module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n : ℕ}

theorem perLineOn_of_frame [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) {P : GL (Fin 6) K}
    (hP : P ∈ primeFormUnitary hKd (idGram K 6))
    (hframe : ∀ a ∈ A, ∃ (M : GL (Fin 6) K) (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
      ∀ l, TableB.projConj (unitarySU 2 n K 6) ⟨M, gu_subset_normalizer hKd hM⟩ (ψ l) =
        ψ (a l)) :
    PerLineOn A := by
  obtain ⟨φ, hφs, hφker, hφa, -⟩ := exists_model hKd hψ hker hperf hperfSU hP hcov'
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  haveI : Finite (MulAut L') := Finite.of_injective (fun φ : MulAut L' => (φ : L' → L'))
    DFunLike.coe_injective
  have hPN := LineU.primeForm_mem_normalizer hKd hP
  have hdiag : ∀ a ∈ A, ∃ t : Fin 6 → K, LineU.ActsDiagU φ a t := by
    intro a ha
    obtain ⟨M, hM, hdiagM, hc⟩ := hframe a ha
    have hMN := gu_subset_normalizer hKd hM
    have hDN : P⁻¹ * M * P ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
    have hdiag' : ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        diagonal (Matrix.diag ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
      ((Matrix.isDiag_iff_diagonal_diag _).mp hdiagM).symm
    exact ⟨Matrix.diag ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K),
      P⁻¹ * M * P, hDN, hdiag', hφa a M (P⁻¹ * M * P) hMN hDN rfl hc⟩
  intro a₀ ha₀ ha₀1 _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf a₀ = 3 := orderOf_eq_prime (hAp a₀ ha₀) ha₀1
  have hΛp : Nat.card (Subgroup.zpowers a₀) = 3 := by rw [Nat.card_zpowers, hord]
  have hΛA : Subgroup.zpowers a₀ ≤ A := Subgroup.zpowers_le.mpr ha₀
  obtain ⟨σ, e, heΛ, hmv⟩ := LineU.moved_of_diag hKd (by norm_num) hφs hφker Nat.prime_three hAp
    hdiag hΛA hΛp
  refine ⟨φ (LineU.permSU hKd σ),
    LineU.weyl_W_prop hKd (by norm_num) hφker hAp hdiag _ ⟨σ, rfl⟩, fun hmem => hmv ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp heΛ
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hmem k

end CFSG.StandardType.UnitSixThreeKG

end
