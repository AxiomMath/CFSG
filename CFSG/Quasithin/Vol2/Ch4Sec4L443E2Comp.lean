module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch4Sec4Inputs

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem pCore_le_oddCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pCore p H ≤ CFSG.oddCore H := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_sSup ⟨inferInstance, ?_⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := H)).exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

theorem le_inf_centralizer_of_centralizes {V : Subgroup H}
    (hF : CFSG.fittingSubgroup H ≤ Subgroup.centralizer (V : Set H))
    (hE : CFSG.layer H ≤ Subgroup.centralizer (V : Set H)) :
    V ≤ CFSG.generalizedFitting H ⊓
      Subgroup.centralizer (CFSG.generalizedFitting H : Set H) := by
  have hC : V ≤ Subgroup.centralizer (CFSG.generalizedFitting H : Set H) :=
    Subgroup.le_centralizer_iff.mp (sup_le hF hE)
  exact le_inf (hC.trans (CFSG.centralizer_generalizedFitting_le H)) hC

theorem le_pCoreOf_top_of_le_of_comm {V N : Subgroup H} (hV : IsPGroup 2 V) (hN : N.Normal)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hVN : V ≤ N) :
    V ≤ pCoreOf 2 (⊤ : Subgroup H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNV : N ≤ Subgroup.normalizer (V : Set H) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm x hx y (hVN hy), mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hcomm x hx (x * y * x⁻¹) (hVN hy)
      have e : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [h1]
          _ = x * y * x⁻¹ := by group
      rw [e]
      exact hy
  have h1 : V ≤ pCoreOf 2 N := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVN hNV hV
  refine h1.trans (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top ?_
    (pCoreOf_isPGroup 2 N))
  have hNN : (⊤ : Subgroup H) ≤ Subgroup.normalizer (N : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
  exact hNN.trans (normalizer_le_normalizer_pCoreOf 2 N)

theorem exists_isComponent_commutator_ne_bot {V : Subgroup H} (hV : IsPGroup 2 V)
    (hV1 : V ≠ ⊥) (hO2 : pCoreOf 2 (⊤ : Subgroup H) = ⊥)
    (hO : V ≤ Subgroup.centralizer (CFSG.oddCore H : Set H)) :
    ∃ K : Subgroup H, CFSG.IsComponent K ∧ ⁅K, V⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  have hE : CFSG.layer H ≤ Subgroup.centralizer (V : Set H) := by
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hne K hK
  have hF : CFSG.fittingSubgroup H ≤ Subgroup.centralizer (V : Set H) := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp2 : p.1.1 = 2
    · have h2 : CFSG.pCore p.1.1 H ≤ pCoreOf 2 (⊤ : Subgroup H) := by
        rw [hp2]
        exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
          (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance])
          (CFSG.pCore_isPGroup (p := 2) (G := H))
      rw [hO2] at h2
      exact h2.trans bot_le
    · have hle := pCore_le_oddCore (H := H) (Nat.prime_of_mem_primeFactors p.1.2) hp2
      exact hle.trans (Subgroup.le_centralizer_iff.mp hO)
  have hVZ := le_inf_centralizer_of_centralizes hF hE
  have hN : (CFSG.generalizedFitting H ⊓
      Subgroup.centralizer (CFSG.generalizedFitting H : Set H)).Normal := by
    have := (CFSG.LocalCores.generalized_fitting_characteristic (G := H)).2
    infer_instance
  have hcomm : ∀ x ∈ CFSG.generalizedFitting H ⊓
      Subgroup.centralizer (CFSG.generalizedFitting H : Set H), ∀ y ∈ CFSG.generalizedFitting H ⊓
      Subgroup.centralizer (CFSG.generalizedFitting H : Set H), x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hy.2 x hx.1)
  have h := le_pCoreOf_top_of_le_of_comm hV hN hcomm hVZ
  rw [hO2] at h
  exact hV1 (le_bot_iff.mp h)

end CFSG.Quasithin.H13.Ch4.E443
