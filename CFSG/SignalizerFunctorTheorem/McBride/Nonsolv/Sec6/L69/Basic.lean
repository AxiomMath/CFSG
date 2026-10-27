module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Geom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Conj
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Khat

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L69

variable {Γ : Type*} [Group Γ]

theorem mem_centralizer_of_mem_centralizer_of_inf_centralizer_eq_bot {H K : Subgroup Γ} {a : Γ}
    (ha : a ∈ Subgroup.normalizer (H : Set Γ)) (hKn : H ≤ Subgroup.normalizer (K : Set Γ))
    (hC : H ⊓ Subgroup.centralizer (K : Set Γ) = ⊥)
    (haK : a ∈ Subgroup.centralizer (K : Set Γ)) : a ∈ Subgroup.centralizer (H : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hax : a * x * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp ha x).mp hx
  have hw : a * x * a⁻¹ * x⁻¹ ∈ H ⊓ Subgroup.centralizer (K : Set Γ) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem hax (inv_mem hx), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk2 : x⁻¹ * k * x ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hKn (inv_mem hx)) k).mp hk
      simpa using this
    have e1 : Commute a⁻¹ (x⁻¹ * k * x) :=
      (Commute.inv_left ((Subgroup.mem_centralizer_iff.mp haK _ hk2).symm))
    have e2 : a * k = k * a := (Subgroup.mem_centralizer_iff.mp haK k hk).symm
    calc k * (a * x * a⁻¹ * x⁻¹)
        = (k * a) * x * a⁻¹ * x⁻¹ := by group
      _ = (a * k) * x * a⁻¹ * x⁻¹ := by rw [e2]
      _ = a * x * (x⁻¹ * k * x) * a⁻¹ * x⁻¹ := by group
      _ = a * x * (a⁻¹ * (x⁻¹ * k * x)) * x⁻¹ := by rw [e1.eq]; group
      _ = (a * x * a⁻¹ * x⁻¹) * k := by group
  rw [hC, Subgroup.mem_bot] at hw
  calc x * a = (a * x * a⁻¹ * x⁻¹)⁻¹ * (a * x) := by group
    _ = a * x := by rw [hw]; simp

variable [Finite Γ]

theorem mem_centralizer_kOf_of_forall {H : Subgroup Γ} (hsol : sol H = ⊥) {v : Γ}
    (hv : ∀ L ∈ lcal H, v ∈ Subgroup.centralizer (L : Set Γ)) :
    v ∈ Subgroup.centralizer (kOf H : Set Γ) := by
  have hK := (isDirectProduct_lcal_kOf hsol).sSup_eq
  have h1 : kOf H ≤ Subgroup.centralizer ({v} : Set Γ) := by
    rw [← hK]
    refine sSup_le fun L hL x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hv L hL) x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hk)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L69

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

open L69

theorem kSetting_thetaOf (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : KSetting p A (thetaOf θ B) :=
  ⟨h.prime, h.elemAbelian, h.isFunctor.normalizes_thetaOf hBA, h.hypB_thetaOf hBA hB⟩

theorem kDown_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : kDown (thetaOf θ B) A = ⊥ :=
  h.theorem_6_6_b (h.thetaOf_mem_msig hBA hB) (thetaOf_anti hBA)

theorem sol_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : sol (thetaOf θ B) = ⊥ :=
  sol_eq_bot_of_kDown_eq_bot (h.kDown_thetaOf hBA hB)

theorem comm_of_mem_A (h : Counterexample p A θ) {a c : G} (ha : a ∈ A) (hc : c ∈ A) :
    a * c = c * a :=
  comm_of_mem_of_isMulCommutative h.elemAbelian.1 ha hc

theorem thetaOf_inf_centralizer (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : thetaOf θ B ⊓ Subgroup.centralizer (A : Set G) = thetaOf θ A := by
  apply le_antisymm
  · obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
    have hb1' : b ≠ 1 := fun h' => hb1 (Subtype.ext h')
    rw [← h.isFunctor.inf_centralizer_self (hBA hb) hb1']
    exact inf_le_inf_right _ (thetaOf_le_apply hb hb1')
  · exact le_inf (thetaOf_anti hBA) (h.isFunctor.thetaOf_le_centralizer le_rfl)

theorem fitting_smear_eq
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) {J : Subgroup G} (hJ : J ∈ lcal (thetaOf θ B)) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear J A) =
      CFSG.inSubgroup CFSG.generalizedFitting (thetaOf θ A) := by
  obtain ⟨-, hlcal, -⟩ := theorem_5_15_f (h.kSetting_thetaOf hBA hB) (h.kDown_thetaOf hBA hB)
    (B := A) le_rfl
  rw [h.thetaOf_inf_centralizer hBA hB] at hlcal
  have hD := T515f.lcal_eq_singleton_of_isSimpleGroup h.lemma_6_8.1 h.lemma_6_8.2
  have hmem : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ∈ lcal (thetaOf θ A) := by
    rw [hlcal]
    exact ⟨J, hJ, rfl⟩
  rw [hD] at hmem
  exact hmem

theorem lcal_thetaOf_nonempty
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : (lcal (thetaOf θ B)).Nonempty := by
  obtain ⟨-, hlcal, -⟩ := theorem_5_15_f (h.kSetting_thetaOf hBA hB) (h.kDown_thetaOf hBA hB)
    (B := A) le_rfl
  rw [h.thetaOf_inf_centralizer hBA hB] at hlcal
  have hD := T515f.lcal_eq_singleton_of_isSimpleGroup h.lemma_6_8.1 h.lemma_6_8.2
  have hmem : CFSG.inSubgroup CFSG.generalizedFitting (thetaOf θ A) ∈ lcal (thetaOf θ A) := by
    rw [hD]
    rfl
  rw [hlcal] at hmem
  obtain ⟨J, hJ, -⟩ := hmem
  exact ⟨J, hJ⟩

theorem exists_conj_eq_of_mem_lcal
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) {J J' : Subgroup G} (hJ : J ∈ lcal (thetaOf θ B))
    (hJ' : J' ∈ lcal (thetaOf θ B)) :
    ∃ a ∈ A, J' = J.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨-, -, hfib⟩ := theorem_5_15_f (h.kSetting_thetaOf hBA hB) (h.kDown_thetaOf hBA hB)
    (B := A) le_rfl
  exact (hfib J hJ J' hJ').mp ((h.fitting_smear_eq hBA hB hJ).trans
    (h.fitting_smear_eq hBA hB hJ').symm)

theorem inf_normalizer_eq_of_mem_lcal
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) {L L' : Subgroup G} (hL : L ∈ lcal (thetaOf θ B))
    (hL' : L' ∈ lcal (thetaOf θ B)) :
    A ⊓ Subgroup.normalizer (L : Set G) = A ⊓ Subgroup.normalizer (L' : Set G) := by
  have key : ∀ L L' : Subgroup G, L ∈ lcal (thetaOf θ B) → L' ∈ lcal (thetaOf θ B) →
      A ⊓ Subgroup.normalizer (L : Set G) ≤ A ⊓ Subgroup.normalizer (L' : Set G) := by
    intro L L' hL hL' v hv
    obtain ⟨c, hcA, rfl⟩ := h.exists_conj_eq_of_mem_lcal hBA hB hL hL'
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hv).1,
      mem_normalizer_map_conj (Subgroup.mem_inf.mp hv).2
        (h.comm_of_mem_A (Subgroup.mem_inf.mp hv).1 hcA)⟩
  exact le_antisymm (key L L' hL hL') (key L' L hL' hL)

theorem inf_centralizer_eq_of_mem_lcal
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) {L L' : Subgroup G} (hL : L ∈ lcal (thetaOf θ B))
    (hL' : L' ∈ lcal (thetaOf θ B)) :
    A ⊓ Subgroup.centralizer (L : Set G) = A ⊓ Subgroup.centralizer (L' : Set G) := by
  have key : ∀ L L' : Subgroup G, L ∈ lcal (thetaOf θ B) → L' ∈ lcal (thetaOf θ B) →
      A ⊓ Subgroup.centralizer (L : Set G) ≤ A ⊓ Subgroup.centralizer (L' : Set G) := by
    intro L L' hL hL' v hv
    obtain ⟨c, hcA, rfl⟩ := h.exists_conj_eq_of_mem_lcal hBA hB hL hL'
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hv).1,
      mem_centralizer_map_conj (Subgroup.mem_inf.mp hv).2
        (h.comm_of_mem_A (Subgroup.mem_inf.mp hv).1 hcA)⟩
  exact le_antisymm (key L L' hL hL') (key L' L hL' hL)

theorem bC_eq_inf_centralizer
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : bC A θ B = A ⊓ Subgroup.centralizer (thetaOf θ B : Set G) := by
  have hsol := h.sol_thetaOf hBA hB
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, haK⟩ := Subgroup.mem_inf.mp ha
    exact Subgroup.mem_inf.mpr ⟨haA,
      mem_centralizer_of_mem_centralizer_of_inf_centralizer_eq_bot
        (h.isFunctor.normalizes_thetaOf hBA haA) (le_normalizer_kOf _)
        (centralizer_kOf_eq_bot hsol) haK⟩
  · exact inf_le_inf_left A
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (kOf_le _)))

theorem bC_eq_inf_centralizer_of_mem_lcal
    (h : Counterexample p A θ) {B : Subgroup G}
    (hBA : B ≤ A) (hB : B ≠ ⊥) {L : Subgroup G} (hL : L ∈ lcal (thetaOf θ B)) :
    bC A θ B = A ⊓ Subgroup.centralizer (L : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left A
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (L511.le_kOf_of_mem_lcal hL)))
  · intro a ha
    obtain ⟨haA, -⟩ := Subgroup.mem_inf.mp ha
    refine Subgroup.mem_inf.mpr ⟨haA, mem_centralizer_kOf_of_forall (h.sol_thetaOf hBA hB)
      fun L' hL' => ?_⟩
    have := h.inf_centralizer_eq_of_mem_lcal hBA hB hL hL'
    exact (Subgroup.mem_inf.mp (this ▸ ha)).2

theorem bN_eq_inf_normalizer
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) {L : Subgroup G} (hL : L ∈ lcal (thetaOf θ B)) :
    bN A θ B = A ⊓ Subgroup.normalizer (L : Set G) := by
  ext a
  unfold bN
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_right fun haA => ?_
  rw [mem_khat_sup_iff h.elemAbelian.1 (h.isFunctor.normalizes_thetaOf hBA) (h.sol_thetaOf hBA hB)
    ⟨L, hL⟩ (Subgroup.mem_sup_right haA)]
  constructor
  · exact fun hall => hall L hL
  · intro haL L' hL'
    have := h.inf_normalizer_eq_of_mem_lcal hBA hB hL hL'
    exact (Subgroup.mem_inf.mp (this ▸ Subgroup.mem_inf.mpr ⟨haA, haL⟩)).2

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
