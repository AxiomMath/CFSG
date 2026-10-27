module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Lines

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

theorem lcal_kOf_eq_of_sol_eq_bot {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (hsol : sol X = ⊥) : lcal (kOf X) = lcal X := by
  have hss : IsSemisimple (kOf X) := isSemisimple_kOf hsol
  rw [hss.lcal_eq, simpleComponents_kOf hsol]

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem diagSetting_kOf_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) :
    DiagSetting p A (kOf (thetaOf θ B)) ∧
      ∀ J ∈ lcal (kOf (thetaOf θ B)), bN A θ B = A ⊓ Subgroup.normalizer (J : Set G) := by
  have hsol := h.sol_thetaOf hBA hB
  have hl := lcal_kOf_eq_of_sol_eq_bot hsol
  refine ⟨⟨h.prime, h.elemAbelian,
    le_normalizer_kOf_of_le_normalizer (h.isFunctor.normalizes_thetaOf hBA), ?_, ?_, ?_⟩,
    fun J hJ => ?_⟩
  · rw [hl]
    exact isDirectProduct_lcal_kOf hsol
  · rw [hl]
    exact h.lcal_thetaOf_nonempty hBA hB
  · intro J hJ J' hJ'
    rw [hl] at hJ hJ'
    exact h.exists_conj_eq_of_mem_lcal hBA hB hJ hJ'
  · rw [hl] at hJ
    exact h.bN_eq_inf_normalizer hBA hB hJ

theorem diagSetting_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) (hk : kOf (thetaOf θ B) = thetaOf θ B) :
    DiagSetting p A (thetaOf θ B) ∧
      ∀ J ∈ lcal (thetaOf θ B), bN A θ B = A ⊓ Subgroup.normalizer (J : Set G) := by
  have hsol := h.sol_thetaOf hBA hB
  refine ⟨⟨h.prime, h.elemAbelian, h.isFunctor.normalizes_thetaOf hBA, ?_,
    h.lcal_thetaOf_nonempty hBA hB,
    fun J hJ J' hJ' => h.exists_conj_eq_of_mem_lcal hBA hB hJ hJ'⟩,
    fun J hJ => h.bN_eq_inf_normalizer hBA hB hJ⟩
  have := isDirectProduct_lcal_kOf hsol
  rwa [hk] at this

theorem diagSetting_apply
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) {x : G} (hx : x ∈ A) (hxE : x ∉ E) :
    DiagSetting p A (θ x) ∧
      ∀ J ∈ lcal (θ x), Subgroup.zpowers x ⊔ E = A ⊓ Subgroup.normalizer (J : Set G) := by
  have hx1 : x ≠ 1 := fun h1 => hxE (h1 ▸ E.one_mem)
  have hz : thetaOf θ (Subgroup.zpowers x) = θ x := h.isFunctor.thetaOf_zpowers hx hx1
  have hzne : Subgroup.zpowers x ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
  have hbN : bN A θ (Subgroup.zpowers x) = Subgroup.zpowers x ⊔ E :=
    core.bN_eq _ (h.zpowers_mem_E1 hx hx1)
  obtain ⟨hD, hN⟩ := h.diagSetting_thetaOf (Subgroup.zpowers_le.mpr hx) hzne
    (core.kOf_eq x hx hxE)
  rw [hz] at hD hN
  exact ⟨hD, fun J hJ => hbN ▸ hN J hJ⟩

theorem diagSetting_kOf_E
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) :
    DiagSetting p A (kOf (thetaOf θ E)) ∧
      ∀ J ∈ lcal (kOf (thetaOf θ E)), E = A ⊓ Subgroup.normalizer (J : Set G) := by
  obtain ⟨hD, hN⟩ := h.diagSetting_kOf_thetaOf core.mem.1 (h.ne_bot_of_mem_E1 core.mem)
  have hbN : bN A θ E = E := by rw [core.bN_eq E core.mem, sup_idem]
  exact ⟨hD, fun J hJ => hbN ▸ hN J hJ⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
