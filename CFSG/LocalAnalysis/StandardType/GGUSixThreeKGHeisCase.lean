module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGShapeDiag
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGShapes

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n : ℕ}

theorem perLineOn_of_heisTriple [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : Nat.card A = 27) {x y z : GL (Fin 6) K}
    (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hzN : z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hxu : x ∈ primeFormUnitary hKd (idGram K 6)) (hyu : y ∈ primeFormUnitary hKd (idGram K 6))
    (hzu : z ∈ primeFormUnitary hKd (idGram K 6)) {ζ : Kˣ}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hζ : IsPrimitiveRoot ζ 3)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hzs : z ∉ LargeEvenScalars (Fin 6) K)
    (hxA : TableB.projConj (unitarySU 2 n K 6) ⟨x, hxN⟩ ∈ TypeA.inducedSub ψ A)
    (hyA : TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩ ∈ TypeA.inducedSub ψ A)
    (hzA : TableB.projConj (unitarySU 2 n K 6) ⟨z, hzN⟩ ∈ TypeA.inducedSub ψ A) :
    PerLineOn A := by
  have hAbcard : Nat.card (TypeA.inducedSub ψ A) = 27 := by
    rw [TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)]
    exact hcard
  intro a₀ ha₀ ha₀1 hcyc
  exfalso
  obtain ⟨x₀, -, hx₀⟩ := hAI a₀ ha₀
  have hx₀Ab : x₀ ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a₀, ha₀, hx₀⟩
  obtain ⟨i, j, k, hM, hi, hj, hk, hx₀eq⟩ := Line63.H5.exists_mono_of_card hKd hpq hAbcard hxN hyN
    hzN hζ hxA hyA hzA hxy hxz hyz hz3 hzs x₀ hx₀Ab
  have hc : ∀ l, TableB.projConj (unitarySU 2 n K 6) ⟨x ^ i * y ^ j * z ^ k, hM⟩ (ψ l) =
      ψ (a₀ l) := fun l => by rw [← hx₀eq]; exact hx₀ l
  by_cases hij : i ≠ 0 ∨ j ≠ 0
  · exact not_ggFixCompCyclic_of_shapeBad hKd hpq hψ hker hM
      (shapeBad_of_mono hKd hpq hxu hyu hzu hx3 hz3 hζ hxy hxz hyz (Or.inr hy3) hij hi hj k) hc
      hcyc
  · push Not at hij
    obtain ⟨rfl, rfl⟩ := hij
    by_cases hk0 : k = 0
    · subst hk0
      have h1 : ∀ l, ψ (a₀ l) = ψ l := fun l => by
        rw [← hc l]
        have e : (⟨x ^ 0 * y ^ 0 * z ^ 0, hM⟩ : Subgroup.normalizer
            (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = 1 := by
          apply Subtype.ext
          simp
        rw [e, map_one]
        rfl
      exact ha₀1 (TypeA.mulAut_eq_of_forall ψ hker hperf (a := a₀) (b := 1) h1)
    · have hzk : z ^ k ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
        pow_mem hzN k
      have e : (⟨x ^ 0 * y ^ 0 * z ^ k, hM⟩ : Subgroup.normalizer
          (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = ⟨z ^ k, hzk⟩ := by
        apply Subtype.ext
        simp
      rw [e] at hc
      exact not_ggFixCompCyclic_of_shapeBad hKd hpq hψ hker hzk
        (shapeBad_of_central_pow hKd hpq hxu hzu hx3 hz3 hζ hxy hxz hyz hzs hk hk0) hc hcyc

end CFSG.StandardType.UnitSixThreeKG

end
