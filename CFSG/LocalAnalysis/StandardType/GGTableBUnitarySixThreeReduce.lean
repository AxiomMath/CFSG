module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeHeis
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwo

public section

namespace CFSG.StandardType

namespace TableBU63

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  TableBUD TableBUE TableBUR TableBUDT

@[expose] def FieldTypeEndNodeInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    ∀ Ab : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))),
      IsElemAbelian 3 Ab →
      (∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) →
      ∀ (M : GL (Fin 6) K)
        (hMN : M ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin 6) K (2 ^ n) : Set (GL (Fin 6) K)))
        (l : Kˣ),
        ((M : Matrix (Fin 6) (Fin 6) K).map (· ^ 2 ^ n))ᵀ * (M : Matrix (Fin 6) (Fin 6) K) = 1 →
        M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l → (∀ c : Kˣ, c ^ 3 ≠ l) →
        TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n)) ⟨M, hMN⟩ ∈ Ab →
        ∃ a ∈ Ab, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
          ∀ a' ∈ Ab, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

theorem ggEndNodeAdmUnitarySixThreeInput_of_fieldType
    (hF : FieldTypeEndNodeInput) :
    GGEndNodeAdmUnitarySixThreeInput := by
  intro n K _ _ hK hpq L' _ _ ψ hψ hker hperf A hA hAI h27 h81 hadm hnofr
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num at hpq
    · exact hn
  have h := TableBU.unitaryFieldData_of_card hK hn
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hN := gu_subset_normalizer (d := 6) h
  have hind : ∀ a ∈ A, ∃ φ : MulAut (LargeEvenProj (unitarySU 2 n K 6)),
      ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hcardAb := TypeA.card_inducedSub hψ hker hperf hind
  have hAbab : IsElemAbelian 3 Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ φ ∈ Ab, φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
    rintro φ ⟨a, ha, hφ⟩
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
    rwa [TypeA.induced_unique ψ hψ hφ hφ']
  obtain ⟨U, hU1, hU2, hAU⟩ := admissible_alpha hK hn (by norm_num) hdq hp3 hpq ψ hψ hker
    (by simpa using h81) hadm
  have hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K 6)) = ⊥ :=
    center_proj_eq_bot hK (by norm_num) hdq
  have hkc := ker_eq_center_of_surjective hψ hker hZ
  set ι := indAut ψ hψ hkc with hι
  have hU1' : U.map ι ≠ ⊥ := fun hbot =>
    hU1 ((Subgroup.map_eq_bot_iff_of_injective U (indAut_injective ψ hψ hkc hperf)).mp hbot)
  have hU2' : IsPGroup 2 (U.map ι) := hU2.map _
  have hAU' : Ab ≤ Subgroup.normalizer (↑(U.map ι)) := by
    rintro φ ⟨a, ha, hφ⟩
    have e : φ = ι a := TypeA.induced_unique ψ hψ hφ (indAut_apply ψ hψ hkc a)
    rw [e]
    exact Subgroup.le_normalizer_map ι ⟨a, hAU ha, rfl⟩
  have hnofrR : ¬ ∃ P ∈ primeFormUnitary h (idGram K 6), ∀ a ∈ Ab, ∃ (M : GL (Fin 6) K)
      (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K 6) ⟨M, gu_subset_normalizer h hM⟩ := by
    rintro ⟨P, hP, hframe⟩
    apply hnofr
    refine ⟨P, ?_, fun a ha => ?_⟩
    · have h1 := mem_primeFormUnitary.mp hP
      simp only [idGram, Units.val_one, Matrix.mul_one] at h1
      exact h1
    · obtain ⟨φ, hφ⟩ := hind a ha
      obtain ⟨M, hM, hdiag, hφM⟩ := hframe φ ⟨a, ha, hφ⟩
      refine ⟨φ, ⟨M, ⟨hM, hdiag⟩, ?_⟩, hφ⟩
      intro g g' hgg'
      rw [hφM]
      exact projConj_graph _ g g' hgg'
  rcases fieldType_or_heis h hK hpq hAbab hAbI (hcardAb ▸ h27) hnofrR with
    ⟨M, hMN, l, hMu, hM3, hl, hMA⟩ | ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA, hx3,
      hz3, hζ3, hζ1, hxy, hxz, hyz, hzs⟩
  ·
    have hMu' : ((M : Matrix (Fin 6) (Fin 6) K).map (· ^ 2 ^ n))ᵀ *
        (M : Matrix (Fin 6) (Fin 6) K) = 1 := by
      have h1 := mem_primeFormUnitary.mp hMu
      simp only [idGram, Units.val_one, Matrix.mul_one] at h1
      exact h1
    exact endNode_of_induced hψ hker hperf hind
      (hF n K hK hpq Ab hAbab hAbI M hMN l hMu' hM3 hl hMA)
  ·
    exact (not_normalizes_twoSubgroup h hK hpq hU1' hU2' hxu hyu hzu hxN hyN hzN (hAU' hxA)
      (hAU' hyA) (hAU' hzA) hx3 hz3 hζ3 hζ1 hxy hxz hyz hzs).elim

end TableBU63

end CFSG.StandardType
