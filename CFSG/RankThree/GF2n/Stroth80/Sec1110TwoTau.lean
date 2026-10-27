module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauLinAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

private theorem act_ne_one_of_mem_LB_not_mem_Q [Finite G]
    (hc : Ctx M Q Z B) {K : Type} [Field K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {u : G} (hu : u ∈ LB M Q B) (huQ : u ∉ Q) :
    (φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E) ≠ 1 := by
  intro h1
  have h2 : φ ⟨u, hc.LB_le_H0 hu⟩ = 1 := by
    ext e
    simpa using LinearMap.congr_fun h1 e
  exact huQ ((hφker _).mp h2)

private theorem exists_act_ne_of_mem_LB_not_mem_Q [Finite G]
    (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {u : G} (hu : u ∈ LB M Q B) (huQ : u ∉ Q) :
    ∃ v, (φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E) v ≠ v := by
  have hTne := act_ne_one_of_mem_LB_not_mem_Q hc hφker hu huQ
  by_contra h
  exact hTne (LinearMap.ext fun v => by
    have hv : (φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E) v = v := by
      by_contra hne
      exact (not_exists.mp h) v hne
    simpa using hv)

private theorem act_commutes_of_mem_centralizer_Xbar [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {u : G} (hu : u ∈ LB M Q B)
    (huX : (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    {g : ↥(H0 M Z)}
    (hgX : (QuotientGroup.mk (⟨(g : G), g.2.1⟩ : ↥M) : Mbar M Q) ∈ Xbar M Q Z B)
    (e : M₀.E) :
    (φ g : M₀.E →ₗ[K] M₀.E) ((φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E) e) =
      (φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E)
        ((φ g : M₀.E →ₗ[K] M₀.E) e) := by
  have hcomm : (QuotientGroup.mk (⟨u, (hc.LB_le_H0 hu).1⟩ : ↥M) : Mbar M Q) *
      (QuotientGroup.mk (⟨(g : G), g.2.1⟩ : ↥M) : Mbar M Q) =
      (QuotientGroup.mk (⟨(g : G), g.2.1⟩ : ↥M) : Mbar M Q) *
      (QuotientGroup.mk (⟨u, (hc.LB_le_H0 hu).1⟩ : ↥M) : Mbar M Q) :=
    (Subgroup.mem_centralizer_iff.mp huX _ hgX).symm
  exact (act_comm_of_mk_comm hφker hcomm e).symm

theorem Ctx.finrank_range_act_eq_two_of_mem_centralizer_Xbar [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥)
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
  classical
  haveI : CharP K 2 := charP_two_of_globalModelData hD hZ
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB hD
  obtain ⟨W, hW, hW3, hWs, hWo⟩ :=
    exists_lagrangian_img_inf_QB_of_lieModel hc hw hn hx hZ hLm2 hcenter hD
  obtain ⟨hbW, hTb, hTW⟩ := hc.act_flag_of_mem_LB hD hφπ hB hW hu
  obtain ⟨g, hgX, hgb⟩ := hc.exists_Xbar_act_not_mem_line hx hLm2 hcenter hφπ hB
  have hT1 := exists_act_ne_of_mem_LB_not_mem_Q hc hφker hu huQ
  have hST : ∀ e, (φ g : M₀.E →ₗ[K] M₀.E)
      ((φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E) e) =
      (φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E)
        ((φ g : M₀.E →ₗ[K] M₀.E) e) :=
    fun e => act_commutes_of_mem_centralizer_Xbar hc hφker hu huX hgX e
  exact Tim79.QuadModel.finrank_range_eq_two_and_singular_of_flag M₀
    (fun e => hφiso ⟨u, hc.LB_le_H0 hu⟩ e)
    (fun e => hc.act_sq_eq_of_mem_LB hφker hu e)
    hWs hWo hW3 hb0 hbW hTb hTW hT1 (fun e => hφiso g e) hST hgb

theorem Ctx.isA2_of_mem_centralizer_Xbar [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {u : G} (hu : u ∈ LB M Q B) (huQ : u ∉ Q)
    (huX : (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    IsA2 Q Z u := by
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp hD
  have hflag := Ctx.finrank_range_act_eq_two_of_mem_centralizer_Xbar hc hw hn hx hZ hLm2
    hcenter hD hφπ hφker hφiso hu huQ huX
  have hK : 1 < Nat.card K := by
    rw [hD.card, hZ]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have ha : ∀ x ∈ Q, u * x * u⁻¹ ∈ Q :=
    (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hu)).1
  have ha' : ∀ x ∈ Q, u⁻¹ * x * u ∈ Q :=
    (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hu)).2
  exact (isA2_iff M₀ hD.reg hD.card hK (φ ⟨u, hc.LB_le_H0 hu⟩) ha ha'
    (fun x hx => hφπ ⟨u, hc.LB_le_H0 hu⟩ x hx)).mpr
    ⟨huQ, hc.sq_mem_Q_of_mem_LB hu, hflag.1, hflag.2⟩

theorem false_of_xbar_psl_two [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) : False := by
  obtain ⟨u, hu, huQ, huX⟩ := exists_mem_LB_mk_mem_centralizer_Xbar hc hw hn hZ hLm2 hcenter
  have hA : IsA2 Q Z u :=
    Ctx.isA2_of_mem_centralizer_Xbar hc hw hn hx hZ hLm2 hcenter hD hu huQ huX
  have hE : (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B :=
    hc.mk_mem_Ebar hu hA
  have hX : (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈ Xbar M Q Z B :=
    Subgroup.subset_closure hE
  have hz : (⟨QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M), hX⟩ : ↥(Xbar M Q Z B)) ∈
      Subgroup.center ↥(Xbar M Q Z B) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp huX (y : Mbar M Q) y.2
  have hz1 : (⟨QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M), hX⟩ : ↥(Xbar M Q Z B)) = 1 :=
    Subgroup.mem_bot.mp (hcenter ▸ hz)
  have hq : (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) = 1 := by
    simpa using congrArg Subtype.val hz1
  exact huQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (⟨u, hc.LB_le_M hu⟩ : ↥M)).mp hq))

end CFSG.RankThree.GF2n.Stroth80
