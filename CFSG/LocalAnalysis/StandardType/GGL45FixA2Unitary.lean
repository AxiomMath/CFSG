module

public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Mark
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Centre
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Rank
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniField
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniFix
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniSolv
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem gffa2_unitary_clauseB {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) (X : Type) [Group X] [Finite X]
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
    (hX : commutator X = ⊤) (ψ : MulAut X)
    (hind : ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n))),
      ∃ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
          (LargeEvenGUSet (Fin 3) K (2 ^ n)),
        orderOf f = 3 ∧ LargeEvenInduces θ (fun k k' => k' = ψ k) (u * f * u⁻¹))
    (Q : Subgroup X) (hQ : IsComponentOf Q (ggAutFixedSubgroup ψ))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center X)) :
    Subgroup.center Q = ⊥ ∧ LargeEvenMarking Q fun lab' _ _ _ _ _ => GGLabelA2 lab' := by
  have hZ' : Subgroup.center X = ⊥ :=
    gffa2_center_eq_bot_of_card_dvd
      (gffa2_card_center_dvd_unitary ⟨hX⟩ hn hK θ) hZ
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    unitaryFieldData_of_card (by omega) hK
  obtain ⟨σ, hσ, ⟨E⟩⟩ := gffa2_unitary_fixed_equiv h θ hZ' ψ hind
  obtain ⟨m, hm, -, -⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_card_fixedField_of_orderOf_eq_three h hσ
  have hmodd : Odd m := gffa2_odd_of_unitary h3 hm
  have hcases : m = 1 ∨ 3 ≤ m := by
    obtain ⟨k, hk⟩ := hmodd
    rcases k with _ | k
    · left; omega
    · right; omega
  rcases hcases with hm1' | hm3
  · subst hm1'
    have hn3 : n = 3 := by omega
    clear σ hσ E
    subst hn3
    obtain ⟨σ', hσ', ⟨E'⟩⟩ := gffa2_unitary_fixed_equiv h θ hZ' ψ hind
    have hsolv3 := gffa2_unitary_solvable h hσ'
    have hsolv : Group.IsSolvable ↥(ggAutFixedSubgroup ψ) := by
      haveI := hsolv3
      exact Group.isSolvable_of_isSolvable_injective (f := E'.toMonoidHom) E'.injective
    exact (gffa2_false_of_solvable hsolv hQ).elim
  · obtain ⟨K₀, hFieldK₀, hFinK₀, hK₀, ⟨T₀⟩⟩ :=
      gffa2_unitary_derived_equiv h hσ hm (by omega)
    obtain ⟨E'⟩ := gffa2_commutator_equiv E
    let T := E'.trans T₀
    obtain ⟨hs, hnab⟩ := gffa2_unitary_simple_nonab (by omega : 2 ≤ m) hK₀
    obtain ⟨Qe⟩ := gffa2_component_equiv T hs hQ
    obtain ⟨hlab, hA2⟩ := gffa2_label_unitary hmodd hm3
    have hdatum : LargeEvenRawDatum ⟨.twA, 2, m⟩ fun R₀ _ _ _ =>
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥Q ≃* R₀) := by
      dsimp only [LargeEvenRawDatum]
      exact ⟨K₀, hFieldK₀, hFinK₀, hK₀, hs, hnab, ⟨Qe⟩⟩
    exact gffa2_marking hlab hA2 hdatum

theorem gffa2_unitary_kgraw {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    GGL45FieldFixKGRaw 3 ⟨.twA, 2, n⟩ (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))) := by
  refine ⟨fun _ _ A hA => gffa2_rank_unitary hn hK A hA, ?_⟩
  intro X _ _ θ hX ψ _ hind Q hQ
  refine ⟨?_, ?_⟩
  · intro htor
    exact absurd htor (by rintro (h | h | h | h) <;> cases h)
  · intro _ _ hZ
    exact gffa2_unitary_clauseB hn hK h3 X θ hX ψ hind Q hQ hZ

end CFSG.StandardType
