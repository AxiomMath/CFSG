module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqSpec
import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4D0
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructNorm

public section

namespace CFSG.Quasithin.H13.F431.D4q.NFq

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Steinberg.TwistedD4


set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK in
theorem charP_two_of_std : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    (k := 3 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])

include hK hσq in
theorem sigma_cube : ∀ c, σ (σ (σ c)) = c := fun c => by
  have h := sigma_three_of_card (σ := σ.toRingHom) hK hσq c
  exact h

include hf hK hσq in
theorem card_d4k : Nat.card (d4k K σ) = 2 ^ f := by
  have hσE3 : σ ^ 3 = 1 := RingEquiv.ext fun c => sigma_cube σ hK hσq c
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσE3
  have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by rw [pow_one]; exact hσq c
  have hc := card_orbitField_D4_orientation Nat.prime_two hf hK (Or.inl rfl) hσ'
    (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)
  rw [show (TwistTag.D4.orbit (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)).card = 1 by
    decide, pow_one, hL2] at hc
  exact hc

include hf hK hσq in
theorem card_Zg : Nat.card (d4Zz K σ) = 2 ^ f := by
  have := charP_two_of_std hf hK
  have hσ := sigma_cube σ hK hσq
  rw [← card_d4k σ hf hK hσq]
  have hinj : Function.Injective
      (fun g : d4k K σ => (⟨vmk σ 0 g, (mem_Zg_iff σ hσ).2 ⟨g, rfl⟩⟩ : d4Zz K σ)) := by
    intro g g' h
    have h2 := congrArg Subtype.val h
    simp only at h2
    have h' : vmk σ 0 g = vmk σ 0 g' := h2
    exact (vmk_inj σ h').2
  have hsurj : Function.Surjective
      (fun g : d4k K σ => (⟨vmk σ 0 g, (mem_Zg_iff σ hσ).2 ⟨g, rfl⟩⟩ : d4Zz K σ)) := by
    rintro ⟨g, hg⟩
    obtain ⟨f', rfl⟩ := (mem_Zg_iff σ hσ).1 hg
    exact ⟨f', rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

include hf hK hσq in
theorem card_Qg : Nat.card (d4Vr K σ) = (2 ^ f) ^ 9 := by
  have := charP_two_of_std hf hK
  have hσ := sigma_cube σ hK hσq
  have hk := card_d4k σ hf hK hσq
  have hinj : Function.Injective
      (fun p : Vc σ × d4k K σ => (⟨vmk σ p.1 p.2, vmk_mem σ hσ p.1 p.2⟩ : d4Vr K σ)) := by
    intro p p' h
    have h2 := congrArg Subtype.val h
    simp only at h2
    have h' : vmk σ p.1 p.2 = vmk σ p'.1 p'.2 := h2
    obtain ⟨h1, h2⟩ := vmk_inj σ h'
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective
      (fun p : Vc σ × d4k K σ => (⟨vmk σ p.1 p.2, vmk_mem σ hσ p.1 p.2⟩ : d4Vr K σ)) := by
    rintro ⟨g, hg⟩
    obtain ⟨x, f', rfl⟩ := exists_vmk σ hσ hg
    exact ⟨(x, f'), rfl⟩
  have h1 : Nat.card (Vc σ × d4k K σ) = Nat.card (d4Vr K σ) :=
    Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  rw [← h1, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, hk, hK]
  ring

include hf hK hσq in
theorem card_U : Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) = (2 ^ f) ^ 12 := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by rw [pow_one]; exact hσq c
  exact (triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K hK 1 (Or.inl rfl)
    σ.toRingHom hσ').2.2

end CFSG.Quasithin.H13.F431.D4q.NFq
