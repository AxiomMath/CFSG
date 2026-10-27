module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Cent

public section

namespace CFSG.Quasithin.H13.Sec53F.TriD4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

include hσ3 in
theorem centerOf_perfectCore_P0_form (hK4 : 4 ≤ Nat.card K) {x : GL}
    (hx : x ∈ centerOf (perfectCore (P0 σ))) : ∃ f : trialityFixedField K τ₀, x = ox₆ σ f := by
  obtain ⟨hxP, hxC⟩ := hx
  have hxC' : x ∈ Subgroup.centralizer (Q0 σ : Set GL) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (Q0_le_perfectCore σ hσ3 hK4)) hxC
  have hxQ : x ∈ Q0 σ :=
    (library_facts σ fa0 singleton_ne_univ_fa0).2.2.2 ⟨perfectCore_le _ hxP, hxC'⟩
  exact center_Q0_form σ hσ3 hxQ hxC'

include hσ3 in
theorem centerOf_perfectCore_P1_form (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀)) {x : GL}
    (hx : x ∈ centerOf (perfectCore (P1 σ))) : ∃ f : trialityFixedField K τ₀, x = ox₆ σ f := by
  obtain ⟨hxP, hxC⟩ := hx
  have hxC' : x ∈ Subgroup.centralizer (Q1 σ : Set GL) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (Q1_le_perfectCore σ hσ3 hk4)) hxC
  have hxQ : x ∈ Q1 σ :=
    (library_facts σ fa1 singleton_ne_univ_fa1).2.2.2 ⟨perfectCore_le _ hxP, hxC'⟩
  obtain ⟨e, f, rfl⟩ := center_Q1_form σ hσ3 hxQ hxC'
  have hx2 : ox₂ σ 1 ∈ perfectCore (P1 σ) :=
    posUnipotent_le_perfectCore_P1 σ hσ3 hk4 ((ox_data σ hσ3).2.1.2.1 1)
  have hcomm : ox₂ σ 1 * (ox₅ σ e * ox₆ σ f) = (ox₅ σ e * ox₆ σ f) * ox₂ σ 1 :=
    Subgroup.mem_centralizer_iff.1 hxC (ox₂ σ 1) hx2
  have h1 : ⁅ox₅ σ e * ox₆ σ f, ox₂ σ 1⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm
  have e1 : ox₅ σ e * ox₆ σ f = 1 * ox₅ σ e * ox₆ σ f := by rw [one_mul]
  have hinv : ⁅ox₅ σ e, ox₂ σ 1⁆ = (ox₆ σ (1 * e))⁻¹ := by
    rw [← commutatorElement_inv, rel25 σ hσ3]
  rw [e1, comm_sandwich (Commute.one_left _) (comm26 σ hσ3 1 f).symm (Commute.one_left _),
    hinv] at h1
  have h2 : ox₆ σ (1 * e) = 1 := inv_eq_one.1 h1
  have he : e = 0 := by
    have := ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
    exact (one_mul e).symm.trans this
  exact ⟨f, by rw [he, ox₅_zero σ hσ3, one_mul]⟩

include hσ3 in
theorem exists_torus_conj_ox₆ (f f' : trialityFixedField K τ₀) (hf : f ≠ 0) (hf' : f' ≠ 0) :
    ∃ m ∈ graphFixedRootTorus TwistTag.D4 K τ₀, m * ox₆ σ f * m⁻¹ = ox₆ σ f' := by
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  set b : (trialityFixedField K τ₀)ˣ := Units.mk0 (f' / f) (div_ne_zero hf' hf) with hb
  refine ⟨trialityTorusHom σ (1, b), Subgroup.mem_inf.2
    ⟨trialityTorusHom_mem_graphFixedTorus hσ3' (1, b),
      trialityTorusHom_mem_graphFixedRootGroup hσ3' (1, b)⟩, ?_⟩
  rw [torus_b_ox₆ σ hσ3 b f]
  congr 2
  exact div_mul_cancel₀ f' hf

include hσ3 in
theorem trans_of_forms {N Z : Subgroup GL} (hN : graphFixedRootTorus TwistTag.D4 K τ₀ ≤ N)
    (hZ : ∀ x ∈ Z, ∃ f : trialityFixedField K τ₀, x = ox₆ σ f) :
    ∀ a ∈ Z, ∀ a' ∈ Z, a ≠ 1 → a' ≠ 1 → ∃ m ∈ N, m * a * m⁻¹ = a' := by
  intro a ha a' ha' h1 h1'
  obtain ⟨f, rfl⟩ := hZ a ha
  obtain ⟨f', rfl⟩ := hZ a' ha'
  have hf : f ≠ 0 := fun h => h1 (by rw [h, ox₆_zero σ hσ3])
  have hf' : f' ≠ 0 := fun h => h1' (by rw [h, ox₆_zero σ hσ3])
  obtain ⟨m, hm, hmx⟩ := exists_torus_conj_ox₆ σ hσ3 f f' hf hf'
  exact ⟨m, hN hm, hmx⟩

include hσ3 in
theorem trans_P0 (hK4 : 4 ≤ Nat.card K) :
    ∀ a ∈ centerOf (perfectCore (P0 σ)), ∀ a' ∈ centerOf (perfectCore (P0 σ)), a ≠ 1 → a' ≠ 1 →
      ∃ m ∈ P0 σ, m * a * m⁻¹ = a' :=
  trans_of_forms σ hσ3 (fun _ hm => graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
    (graphFixedRootTorus_le_graphFixedRootBorel hm))
    (fun _ hx => centerOf_perfectCore_P0_form σ hσ3 hK4 hx)

include hσ3 in
theorem trans_P1 (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀)) :
    ∀ a ∈ centerOf (perfectCore (P1 σ)), ∀ a' ∈ centerOf (perfectCore (P1 σ)), a ≠ 1 → a' ≠ 1 →
      ∃ m ∈ P1 σ, m * a * m⁻¹ = a' :=
  trans_of_forms σ hσ3 (fun _ hm => graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
    (graphFixedRootTorus_le_graphFixedRootBorel hm))
    (fun _ hx => centerOf_perfectCore_P1_form σ hσ3 hk4 hx)

end CFSG.Quasithin.H13.Sec53F.TriD4
