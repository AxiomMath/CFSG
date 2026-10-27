module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauLinAlg
import CFSG.RankThree.GF2n.Stroth80.Sec115Root

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

omit [(Q.subgroupOf M).Normal] in
theorem exists_lagrangian_img_inf_QB_of_card_eq (hc : Ctx M Q Z B) (hw : Width Q Z 3)
    (hD4 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ 4)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) :
    ∃ W : Submodule K M₀.E, (∀ e, e ∈ M₀.img (Q ⊓ QB B) ↔ e ∈ W) ∧
      Module.finrank K W = 3 ∧ (∀ w ∈ W, M₀.Qf w = 0) ∧
      ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W := by
  have hKgt1 : 1 < Nat.card K := by
    rw [hD.card]
    have := hc.hyp.q4
    omega
  have hdim : Module.finrank K M₀.E = 2 * 3 := hD.finrank_E hw hKgt1
  have hK2 : (2 : K) = 0 := by
    obtain ⟨x, -, hZ, -⟩ := hc.hyp.cp
    have : CharP K 2 := charP_two_of_globalModelData hD hZ
    exact CharP.cast_eq_zero K 2
  have hDcard : Nat.card ↥(Q ⊓ QB B) = Nat.card K ^ (3 + 1) := by
    rw [hD4, hD.card]
  have hVD : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hDc : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hc.inf_QB_elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨W, hW, hdimW, horth⟩ :=
    Stroth57D.lagrangian_img M₀ hD.reg hK2 hD.card hdim (n := 3)
      (inf_le_left : Q ⊓ QB B ≤ Q) hVD hDc hDcard
  refine ⟨W, hW, hdimW, ?_, ?_⟩
  · intro w hw
    exact (Tim79.QuadModel.isElemAbelian_iff (M₀ := M₀) hD.reg
      (inf_le_left : Q ⊓ QB B ≤ Q)).mp hc.inf_QB_elemAbelian w ((hW w).mpr hw)
  · intro v hv
    rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [M₀.B_comm w v, hv w hw, neg_zero]

theorem Ctx.Xbar_inf_bar_LB_eq_bot_of_le_normalizer (hc : Ctx M Q Z B)
    (hX : Xbar M Q Z B ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q))) :
    Xbar M Q Z B ⊓ bar M Q (LB M Q B) = ⊥ :=
  eq_bot_of_isPGroup_of_subnormal inf_le_left
    (fun _ hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hX hx⟩)
    hc.Xbar_normal hc.pCore_two_Mbar (hc.isPGroup_bar_LB.to_le inf_le_right)

theorem Ctx.exists_Xbar_act_not_mem_line_of_not_le (hc : Ctx M Q Z B)
    (hnot : ¬ Xbar M Q Z B ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)))
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (y : G), y ∈ Q → M₀.π ((m : G) * y * (m : G)⁻¹) = φ m (M₀.π y))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    ∃ g : ↥(H0 M Z), (QuotientGroup.mk (⟨(g : G), g.2.1⟩ : ↥M) : Mbar M Q) ∈ Xbar M Q Z B ∧
      ∀ c : K, φ g b ≠ c • b := by
  by_contra hcon
  push Not at hcon
  refine hnot fun y hy => ?_
  obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.mp (hc.Xbar_le_bar_H0 hy)
  rw [Subgroup.mem_subgroupOf] at hm
  let g : ↥(H0 M Z) := ⟨(m : G), hm⟩
  have hgM : (g : G) ∈ M := g.2.1
  have hgm : (QuotientGroup.mk (⟨(g : G), hgM⟩ : ↥M) : Mbar M Q) = y := by
    rw [← hmk]
    rfl
  rw [← hgm]
  obtain ⟨c, hc'⟩ := hcon g (hgm ▸ hy)
  exact Ctx.mk_mem_normalizer_bar_LB_of_fix_line hc hB hgM
    (T := (φ g : M₀.E →ₗ[K] M₀.E)) (hφπ g) (μ := c) hc'

omit [Finite G] [(Q.subgroupOf M).Normal] in
private theorem exists_act_ne_of_not_mem_Q {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {u : ↥(H0 M Z)} (huQ : (u : G) ∉ Q) :
    ∃ v, (φ u : M₀.E →ₗ[K] M₀.E) v ≠ v := by
  by_contra h
  push Not at h
  refine huQ ((hφker u).mp ?_)
  ext e
  simpa using h e

theorem Ctx.finrank_range_act_eq_two_of_mem_centralizer_Xbar_of_card (hc : Ctx M Q Z B)
    (hw : Width Q Z 3) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hD4 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ 4)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (y : G), y ∈ Q → M₀.π ((m : G) * y * (m : G)⁻¹) = φ m (M₀.π y))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e)
    {u : G} (hu : u ∈ LB M Q B) (huQ : u ∉ Q)
    (huX : (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    Module.finrank K
        (LinearMap.range ((φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E) - 1)) = 2 ∧
      ∀ v ∈ LinearMap.range ((φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E) - 1),
        M₀.Qf v = 0 := by
  obtain ⟨x, -, hZ, -⟩ := hc.hyp.cp
  have : CharP K 2 := charP_two_of_globalModelData hD hZ
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB hD
  obtain ⟨W, hW, hW3, hWs, hWo⟩ := exists_lagrangian_img_inf_QB_of_card_eq hc hw hD4 hD
  obtain ⟨hbW, hTb, hTW⟩ := hc.act_flag_of_mem_LB hD hφπ hB hW hu
  have hnot : ¬ Xbar M Q Z B ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
    intro hX
    obtain ⟨a, haL, hA⟩ := ha2
    have h1 : (QuotientGroup.mk (⟨a, hc.LB_le_M haL⟩ : ↥M) : Mbar M Q) ∈
        Xbar M Q Z B ⊓ bar M Q (LB M Q B) :=
      ⟨Subgroup.subset_closure (hc.mk_mem_Ebar haL hA),
        Subgroup.mem_map.mpr ⟨⟨a, hc.LB_le_M haL⟩, Subgroup.mem_subgroupOf.mpr haL, rfl⟩⟩
    rw [hc.Xbar_inf_bar_LB_eq_bot_of_le_normalizer hX, Subgroup.mem_bot] at h1
    exact hA.2.1 (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  obtain ⟨g, hgX, hgb⟩ := hc.exists_Xbar_act_not_mem_line_of_not_le hnot hφπ hB
  have hcomm : (QuotientGroup.mk (⟨u, (hc.LB_le_H0 hu).1⟩ : ↥M) : Mbar M Q) *
      (QuotientGroup.mk (⟨(g : G), g.2.1⟩ : ↥M) : Mbar M Q) =
      (QuotientGroup.mk (⟨(g : G), g.2.1⟩ : ↥M) : Mbar M Q) *
      (QuotientGroup.mk (⟨u, (hc.LB_le_H0 hu).1⟩ : ↥M) : Mbar M Q) :=
    (Subgroup.mem_centralizer_iff.mp huX _ hgX).symm
  exact Tim79.QuadModel.finrank_range_eq_two_and_singular_of_flag M₀
    (fun e => hφiso ⟨u, hc.LB_le_H0 hu⟩ e)
    (fun e => hc.act_sq_eq_of_mem_LB hφker hu e)
    hWs hWo hW3 hb0 hbW hTb hTW (exists_act_ne_of_not_mem_Q hφker (u := ⟨u, _⟩) huQ)
    (fun e => hφiso g e) (fun e => (act_comm_of_mk_comm hφker hcomm e).symm) hgb

theorem Ctx.isA2_of_mem_centralizer_Xbar_of_card (hc : Ctx M Q Z B) (hw : Width Q Z 3)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) (hD4 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ 4)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (y : G), y ∈ Q → M₀.π ((m : G) * y * (m : G)⁻¹) = φ m (M₀.π y))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e)
    {u : G} (hu : u ∈ LB M Q B) (huQ : u ∉ Q)
    (huX : (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    IsA2 Q Z u := by
  have hflag := hc.finrank_range_act_eq_two_of_mem_centralizer_Xbar_of_card hw ha2 hD4 hD hφπ
    hφker hφiso hu huQ huX
  have hK : 1 < Nat.card K := by
    rw [hD.card]
    have := hc.hyp.q4
    omega
  exact (isA2_iff M₀ hD.reg hD.card hK (φ ⟨u, hc.LB_le_H0 hu⟩)
    (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hu)).1 (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hu)).2
    (fun x hx => hφπ ⟨u, hc.LB_le_H0 hu⟩ x hx)).mpr
    ⟨huQ, hc.sq_mem_Q_of_mem_LB hu, hflag.1, hflag.2⟩

theorem Ctx.not_isA2_of_mem_centralizer_Xbar (hc : Ctx M Q Z B) {u : G} (hu : u ∈ LB M Q B)
    (huX : (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    ¬ IsA2 Q Z u := by
  intro hA
  have hE := hc.mk_mem_Ebar hu hA
  refine hc.not_mem_center_Xbar_of_mem_Ebar (d := ⟨_, Subgroup.subset_closure hE⟩) hE ?_
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp huX (y : Mbar M Q) y.2

theorem Ctx.inf_centralizer_Xbar_eq_bot_of_card_sq (hc : Ctx M Q Z B) (hw : Width Q Z 3)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hL : Nat.card (bar M Q (LB M Q B)) = Nat.card Z ^ 2) :
    bar M Q (LB M Q B) ⊓ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) = ⊥ := by
  have hD4 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ 4 :=
    (card_bar_LB_eq_sq_iff hc hw (by norm_num)).mp hL
  obtain ⟨k, γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp hD
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hxL
  have hu : (m : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hm
  by_contra hx1
  have huQ : (m : G) ∉ Q := fun h =>
    hx1 ((QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_subgroupOf.mpr h))
  exact hc.not_isA2_of_mem_centralizer_Xbar hu hxC
    (hc.isA2_of_mem_centralizer_Xbar_of_card hw ha2 hD4 hD hφπ hφker hφiso hu huQ hxC)

end CFSG.RankThree.GF2n.Stroth80
