module

public import CFSG.LocalAnalysis.StandardType.GGTDModelU
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel
public import CFSG.LocalAnalysis.StandardType.GGTDLabels
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTorusTorData_unitary_six_three_odd
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) L' ψ A)
    (hodd : Odd (Nat.card ψ.ker)) :
    GGTorusTorData (2 ^ 1 + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) L' A := by
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hTB
  obtain ⟨φ, hM, hdiag⟩ := USixTwo.exists_diagModel_odd hK hψ hker hperf hodd hAe hAI
    (by simpa using hr)
  exact ggTorusTorData_of_model_U hK Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    hM hAe hsc hdiag

theorem ggTorusTorW_unitary_six_three_two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGTorusTorW 3 4 (2 ^ 1 + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5)
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) := by
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hTB
  have hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker) := fun a ha =>
    U63TB.mem_presZ_of_ker hker fun z hz => U63TB.preserves_ker (hAI a ha) hz
  have hTB₁ : GGTorusTBGroup 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.psi1 hker) (U63TB.redSub hker hAle).range := by
    refine ⟨U63TB.psi1_surjective hker hψ, U63TB.psi1_ker_central hker,
      U63TB.commutator_quot hker hperf, U63TB.isElemAbelian_range_redSub hker hAle hAe,
      U63TB.redSub_hAI hker hAle hAI, ?_, ?_, U63TB.selfCent_quot hker hAe hAle hsc⟩
    · rw [U63TB.card_range_redSub hker hAle hperf]
      exact hr
    · rw [U63TB.card_range_redSub hker hAle hperf]
      exact h3
  exact ggTorusTorData_descent_two hker hperf hAe hAle
    (ggTorusTorData_unitary_six_three_odd hK hTB₁ (U63TB.odd_card_ker_psi1 hker))

end CFSG.StandardType

end
