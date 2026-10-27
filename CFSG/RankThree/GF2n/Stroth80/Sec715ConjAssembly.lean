module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjFrameCtx
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjAdj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

private theorem range_opm_conj_sec715 {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (T S : E ≃ₗ[K] E) :
    LinearMap.range (opm (T * S * T⁻¹)) = (LinearMap.range (opm S)).map (T : E →ₗ[K] E) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    refine Submodule.mem_map.mpr ⟨opm S (T.symm x), LinearMap.mem_range.mpr ⟨T.symm x, rfl⟩, ?_⟩
    simp [opm_apply]
  · intro hy
    obtain ⟨w, hw, hTw⟩ := Submodule.mem_map.mp hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
    refine LinearMap.mem_range.mpr ⟨T u, ?_⟩
    rw [← hTw]
    simp [opm_apply]

namespace Sec715Frame

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X} {Tt : X → Submodule K E}

theorem Tt_eq_map (F : Sec715Frame φ V L Nb Rb Tt) (h : X) {a : X} (ha : a ∈ V) (ha1 : a ≠ 1) :
    Tt h = (Tt 1).map ((φ h : E ≃ₗ[K] E) : E →ₗ[K] E) := by
  have h1 : Tt 1 = LinearMap.range (opm (φ a)) := by
    simpa using (F.Tt_range 1 a ha ha1).symm
  have h2 : Tt h = LinearMap.range (opm (φ (h * a * h⁻¹))) := (F.Tt_range h a ha ha1).symm
  rw [h2, h1, map_mul, map_mul, map_inv, range_opm_conj_sec715]

theorem eq_one_of_mem_conj_Nb (F : Sec715Frame φ V L Nb Rb Tt) {h : X}
    (hL : ∀ a ∈ V, h * a * h⁻¹ ∈ L) (hout : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb) {a : X} (ha : a ∈ V)
    (haN : h⁻¹ * a * h ∈ Nb) : a = 1 := by
  by_contra ha1
  apply hout
  intro b hb
  by_cases hb1 : b = 1
  · subst hb1
    simpa using Nb.one_mem
  have hfix : (Tt h).map (opm (φ a)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    rw [F.Tt_eq_map h ha ha1] at hu
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
    have h1 := F.Nb_fixes _ haN u' hu'
    have e : a = h * (h⁻¹ * a * h) * h⁻¹ := by group
    have h2 : φ a (φ h u') = φ h u' := by
      conv_lhs => rw [e]
      rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, phi_inv_apply_phi, h1]
    simp [opm_apply, h2]
  have hcomm := F.comm_conj_of_le_L hL
  have hsame : (Tt 1).map (opm (φ (h * b * h⁻¹))) = ⊥ := by
    rw [F.map_opm_eq hcomm ha ha1 hb hb1, hfix]
  refine F.Rb_fix_Nb _ (F.L_le_Rb (hL b hb)) fun w hw => ?_
  have hmem : opm (φ (h * b * h⁻¹)) w ∈ (Tt 1).map (opm (φ (h * b * h⁻¹))) :=
    Submodule.mem_map_of_mem hw
  rw [hsame, Submodule.mem_bot, opm_apply, sub_eq_zero] at hmem
  exact hmem

end Sec715Frame

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.sec715Conj_of_kappa (h34 : Stroth34Statement) (hZt : Sec7ZtStatement)
    (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hCN : Sec7CommNStatement) (h710 : Stroth710Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t))) (hC : CentTwoInV hc t Z0)
    (hsq : ∀ x ∈ hc.CN t, x * x ∈ Z0)
    (hκ : ∀ h : ↥(bar M Q (H0 M Z)),
      (∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z))) →
      (¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        h * a * h⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) →
      ∀ b ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), b ≠ 1 →
        (∀ x ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
          ∃ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
            ⁅h * b * h⁻¹, x⁆ * z⁻¹ ∈
              conjSubgroup h ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))) ∧
        Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ^ 2 *
            Nat.card ↥(Subgroup.centralizer ({h * b * h⁻¹} : Set ↥(bar M Q (H0 M Z))) ⊓
              (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) <
          Nat.card ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))) :
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  obtain ⟨m, γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ₀, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hM
  obtain ⟨φ, -, hφmk⟩ := exists_barAct hQH hHM φ₀ hφker
  have hφπ' : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z))
      (x : G), x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x) := by
    intro y hy x hx
    have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hy
    rw [hφmk y hy hyH]
    exact hφπ ⟨(y : G), hyH⟩ x hx
  obtain ⟨Tt, F⟩ := Ctx.sec715Frame h34 hZt hZcard hZc hZV hc hs hZ0 M₀ φ hφπ'
  obtain ⟨g, hgM, hgL, hgne⟩ := h710 G M Q Z B hc n t hs Z0 hZ0
  by_cases hgN : conjSubgroup g Z0 ≤ hc.CN t
  · exact ⟨g, hgM, hgN, hgne⟩
  obtain ⟨h₀, hh₀H, hh₀⟩ := hc.exists_H0_conj hs hZ0 hZt hZcard hN2 hTI hC hgM
  rw [hh₀] at hgL hgN hgne
  have hmem : ∀ {S : Subgroup G}, Q ≤ S → ∀ (x : ↥(bar M Q (H0 M Z))) (y : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) →
        (x ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)) ↔ (y : G) ∈ S) := by
    intro S hQS x y hy
    rw [Subgroup.mem_subgroupOf, ← hy]
    exact mk_mem_bar_iff_sec4 hQS y
  have hrep : ∀ x : ↥(bar M Q (H0 M Z)), ∃ y : ↥M,
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) :=
    fun x => QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
  have hh₀M : h₀ ∈ M := hHM hh₀H
  have hh₀bar : QuotientGroup.mk' (Q.subgroupOf M) ⟨h₀, hh₀M⟩ ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH _).mpr hh₀H
  set h : ↥(bar M Q (H0 M Z)) := ⟨_, hh₀bar⟩ with hh
  have hconjmk : ∀ (a : ↥(bar M Q (H0 M Z))) (z : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) z = (a : Mbar M Q) →
      QuotientGroup.mk' (Q.subgroupOf M) (⟨h₀, hh₀M⟩ * z * ⟨h₀, hh₀M⟩⁻¹) =
        ((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q) := by
    intro a z hz
    simp only [map_mul, map_inv, hz, Subgroup.coe_mul, Subgroup.coe_inv, hh]
  have hL : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) := by
    intro a ha
    obtain ⟨z, hz⟩ := hrep a
    have hzZ : (z : G) ∈ Z0 := (hmem hQZ0 a z hz).mp ha
    refine (hmem hQL _ _ (hconjmk a z hz)).mpr ?_
    apply hgL
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hzZ
  have hout : ¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
    intro hall
    apply hgN
    intro x hx
    obtain ⟨z, hzZ, rfl⟩ : ∃ z ∈ Z0, h₀ * z * h₀⁻¹ = x :=
      ⟨h₀⁻¹ * x * h₀, mem_conjSubgroup.mp hx, by group⟩
    have hzM : z ∈ M := hZ0M hzZ
    have hzbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzM⟩ ∈ bar M Q (H0 M Z) :=
      (mk_mem_bar_iff_sec4 hQH _).mpr (hZ0.le.trans hRH hzZ)
    have haV : (⟨_, hzbar⟩ : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
      (hmem hQZ0 _ ⟨z, hzM⟩ rfl).mpr hzZ
    exact (hmem hQN _ _ (hconjmk _ ⟨z, hzM⟩ rfl)).mp (hall _ haV)
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hZ0M hsZ0
  have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH _).mpr (hZ0.le.trans hRH hsZ0)
  set b₀ : ↥(bar M Q (H0 M Z)) := ⟨_, hsbar⟩ with hb₀
  have hb₀V : b₀ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := (hmem hQZ0 _ _ rfl).mpr hsZ0
  have hb₀1 : b₀ ≠ 1 := fun h1 => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)))
  obtain ⟨hκ1, hκ2⟩ := hκ h hL hout b₀ hb₀V hb₀1
  set y := h * b₀ * h⁻¹ with hy
  set Vh := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) with hVh
  set Lh := (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) with hLh
  set Nh := (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) with hNh
  set Rh := (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) with hRh
  have hyL : y ∈ Lh := hL b₀ hb₀V
  have hVc : ∀ z ∈ Vh, ∀ x ∈ Nh, z * x = x * z := by
    intro z hz x hx
    obtain ⟨z₀, hz₀⟩ := hrep z
    have hz₀Z : (z₀ : G) ∈ Z0 := (hmem hQZ0 z z₀ hz₀).mp hz
    apply Subtype.ext
    show (z : Mbar M Q) * x = x * z
    rw [← hz₀]
    exact endg_comm_centre hZ0 (hc.Rt_le_M t) hz₀Z
      (bar_mono' hNR (Subgroup.mem_subgroupOf.mp hx))
  have hVsq : ∀ z ∈ Vh, z * z = 1 := by
    intro z hz
    apply Subtype.ext
    have := sq_eq_one_bar hc hs hZc hZ0 (z : Mbar M Q) (Subgroup.mem_subgroupOf.mp hz)
    simpa [pow_two] using this
  have hNc : ∀ a ∈ Nh, ∀ b ∈ Nh, ⁅a, b⁆ ∈ Vh := by
    intro a ha b hb
    obtain ⟨x, hx⟩ := hrep a
    obtain ⟨w, hw⟩ := hrep b
    have hxN : (x : G) ∈ hc.CN t := (hmem hQN a x hx).mp ha
    have hwN : (w : G) ∈ hc.CN t := (hmem hQN b w hw).mp hb
    have hcomm : ⁅(x : G), (w : G)⁆ ∈ Z0 :=
      hCN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hxN hwN)
    rw [Subgroup.mem_subgroupOf]
    show ⁅(a : Mbar M Q), (b : Mbar M Q)⁆ ∈ bar M Q Z0
    rw [← hx, ← hw, ← map_commutatorElement]
    have hxw : ((⁅x, w⁆ : ↥M) : G) = ⁅(x : G), (w : G)⁆ := by
      simp [commutatorElement_def]
    exact (mk_mem_bar_iff_sec4 hQZ0 ⁅x, w⁆).mpr (hxw ▸ hcomm)
  have hNsq : ∀ a ∈ Nh, a * a ∈ Vh := by
    intro a ha
    obtain ⟨x, hx⟩ := hrep a
    have hxN : (x : G) ∈ hc.CN t := (hmem hQN a x hx).mp ha
    refine (hmem hQZ0 (a * a) (x * x) ?_).mpr (by simpa using hsq _ hxN)
    simp only [map_mul, hx, Subgroup.coe_mul]
  have hyLc : ∀ x ∈ Nh, ⁅y, x⁆ ∈ Lh := by
    intro x hx
    rw [commutatorElement_def]
    have h1 : x * y⁻¹ * x⁻¹ ∈ Lh := F.Nb_norm_L x hx _ (Lh.inv_mem hyL)
    have e : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
    rw [e]
    exact Lh.mul_mem hyL h1
  have hyN : ∀ x ∈ Nh, ⁅y, x⁆ ∈ Nh := by
    intro x hx
    rw [commutatorElement_def]
    exact Nh.mul_mem (F.Nb_normal y (F.L_le_Rb hyL) x hx) (Nh.inv_mem hx)
  have hyV : ∀ z ∈ Vh, y * z = z * y := fun z hz => F.L_comm y hyL z (F.V_le_L hz)
  set Ker := Lh ⊓ conjSubgroup h Nh with hKer
  have hKerV : ∀ z ∈ Vh, z ∈ Ker → z = 1 := by
    intro z hz hzK
    exact F.eq_one_of_mem_conj_Nb hL hout hz (mem_conjSubgroup.mp hzK.2)
  have hK₂ : ∀ x ∈ Nh, ∃ z ∈ Vh, ⁅y, x⁆ * z⁻¹ ∈ Ker := by
    intro x hx
    obtain ⟨z, hz, hzK⟩ := hκ1 x hx
    exact ⟨z, hz, Lh.mul_mem (hyLc x hx) (Lh.inv_mem (F.V_le_L hz)), hzK⟩
  obtain ⟨x, hx, hxy, hxK⟩ := exists_comm_mem_of_card_lt (N := Nh) (V := Vh) (L := Lh)
    (K₂ := Nh) (Ker := Ker) (y := y) F.V_le_Nb F.V_le_L hVc hVsq hNc hNsq F.L_comm hyLc hyN hyV
    hKerV le_rfl (fun c hc _ => hc) hK₂ hκ2
  have hnc : ¬ ∀ a ∈ Vh, x * (h * a * h⁻¹) = (h * a * h⁻¹) * x := fun hall =>
    hxy (hall b₀ hb₀V).symm
  have hcN : h⁻¹ * ⁅x, h * b₀ * h⁻¹⁆ * h ∈ Nh := by
    have h1 : ⁅x, y⁆ ∈ conjSubgroup h Nh := by
      rw [← commutatorElement_inv]
      exact (conjSubgroup h Nh).inv_mem hxK.2
    exact mem_conjSubgroup.mp h1
  obtain ⟨hmN, hmV⟩ := F.exists_conj_le_Nb hL hout hx hnc hb₀V hb₀1 hcN
  obtain ⟨m₀, hm₀⟩ := hrep (h⁻¹ * x * h)
  refine ⟨m₀, m₀.2, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hzZ, rfl⟩ : ∃ z ∈ Z0, (m₀ : G) * z * (m₀ : G)⁻¹ = w :=
      ⟨(m₀ : G)⁻¹ * w * m₀, mem_conjSubgroup.mp hw, by group⟩
    have hzM : z ∈ M := hZ0M hzZ
    have hzbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzM⟩ ∈ bar M Q (H0 M Z) :=
      (mk_mem_bar_iff_sec4 hQH _).mpr (hZ0.le.trans hRH hzZ)
    have haV : (⟨_, hzbar⟩ : ↥(bar M Q (H0 M Z))) ∈ Vh := (hmem hQZ0 _ ⟨z, hzM⟩ rfl).mpr hzZ
    have h1 := hmN _ haV
    refine (hmem hQN _ (m₀ * ⟨z, hzM⟩ * m₀⁻¹) ?_).mp h1
    simp only [map_mul, map_inv, hm₀, Subgroup.coe_mul, Subgroup.coe_inv]
  · intro heq
    apply hmV
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨z, hz⟩ := hrep a
    have hzZ : (z : G) ∈ Z0 := (hmem hQZ0 a z hz).mp ha
    have h1 : (m₀ : G) * z * (m₀ : G)⁻¹ ∈ Z0 := by
      rw [← heq, mem_conjSubgroup]
      simpa [mul_assoc] using hzZ
    show (h⁻¹ * x * h) * a * (h⁻¹ * x * h)⁻¹ ∈ Vh
    refine (hmem hQZ0 _ (m₀ * z * m₀⁻¹) ?_).mpr h1
    simp only [map_mul, map_inv, hm₀, hz, Subgroup.coe_mul, Subgroup.coe_inv]

end CFSG.RankThree.GF2n.Stroth80
