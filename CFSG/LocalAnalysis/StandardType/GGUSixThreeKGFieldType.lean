module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldStruct
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldCase

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n : ℕ}

theorem perLineOn_of_fieldType [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : Nat.card A = 27) {M : GL (Fin 6) K}
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {l : Kˣ}
    (hMu : M ∈ primeFormUnitary hKd (idGram K 6))
    (hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l) (hl : ∀ c : Kˣ, c ^ 3 ≠ l)
    (hMA : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ ∈ TypeA.inducedSub ψ A) :
    PerLineOn A := by
  have hAb : CFSG.Open.IsElemAbelian 3 (TypeA.inducedSub ψ A) :=
    TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ x ∈ TypeA.inducedSub ψ A, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K 6)) (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hcardAb : Nat.card (TypeA.inducedSub ψ A) = 27 := by
    rw [TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)]
    exact hcard
  obtain ⟨X, Z, hXN, hZN, ζ, hXu, hZu, hXA, hZA, hX3, hZ3, hζ, hXM, hXZ, hMZ, hZs⟩ :=
    exists_fieldStruct hKd hK hpq hAb hAbI hcardAb hMN hMu hM3 hl hMA
  exact perLineOn_of_fieldTriple hKd hpq hperfSU hcov' hψ hker hperf hA hAI hcard hXN hMN hZN hXu
    hMu hZu hX3 hZ3 hM3 hl hζ hXM hXZ hMZ hZs hXA hMA hZA

end CFSG.StandardType.UnitSixThreeKG

end
