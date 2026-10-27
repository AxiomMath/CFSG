module

public import CFSG.RankThree.GF2n.Item310
public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOneLie
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def OutSolvableRankTwoStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .G2 0 2 m) ∨
      (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .trialityD4 0 2 m)) →
    (∃ a b : X, a * b ≠ b * a) →
    ∀ P : Subgroup (MulAut X), commutator ↥P = ⊤ →
      P ≤ (MulAut.conj : X →* MulAut X).range

@[expose] def OutSolvableUnitarySixStatement : Prop :=
  ∀ (q : ℕ), (∃ f : ℕ, 1 ≤ f ∧ q = 2 ^ f) → ∀ (X : Type) [Group X] [Finite X], IsPSUModel 6 q X →
    ∀ P : Subgroup (MulAut X), commutator ↥P = ⊤ →
      P ≤ (MulAut.conj : X →* MulAut X).range

theorem exists_noncomm_of_psu_six_model {Q : Type} [Group Q] {f : ℕ}
    (h : StatedClassicalModel Q .PSU 6 2 f) : ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ((6 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h'
    have := congrArg Prod.fst h'
    simp at this
  obtain ⟨hqs, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
    (f := f) hK (by norm_num) hne
  obtain ⟨a, b, hab⟩ := hqs.2.2
  let φ : (StatedSU 6 (2 ^ f) K ⧸ Subgroup.center (StatedSU 6 (2 ^ f) K)) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans e.symm
  exact ⟨φ a, φ b, fun h' => hab (φ.injective (by rw [map_mul, map_mul]; exact h'))⟩

theorem statedClassicalModel_psu_six {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (h : IsPSUModel 6 (2 ^ f) X) : StatedClassicalModel X .PSU 6 2 f := by
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := h
  refine ⟨⟨Nat.prime_two, hf, by norm_num, ?_⟩, K, hK, hKf, hcard, ⟨e⟩⟩
  intro h'
  have := congrArg Prod.fst h'
  simp at this

section Certs

theorem perfect_action_inner_of_catalog (X : Type) [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hcat : CFSG.Assembly.InCatalog X)
    (P : Subgroup (MulAut X)) (hP : commutator ↥P = ⊤) :
    P ≤ (MulAut.conj : X →* MulAut X).range := by
  have hsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds X hnonab hcat
  haveI : Group.IsPerfect P := Group.isPerfect_def.mpr hP
  intro x hx
  obtain ⟨g, hg⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    P.subtype (⟨x, hx⟩ : P)
  exact MonoidHom.mem_range.mpr ⟨g, hg.symm⟩

theorem outSolvableUnitarySix_holds : OutSolvableUnitarySixStatement := by
  intro q hq X _ _ hX P hP
  obtain ⟨f, hf, rfl⟩ := hq
  have hmodel := statedClassicalModel_psu_six hf hX
  haveI hsimp : IsSimpleGroup X :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 6 2 f hmodel).2
  exact perfect_action_inner_of_catalog X (exists_noncomm_of_psu_six_model hmodel)
    (CFSG.ClassicalModels.statedClassicalModel_PSU_inCatalog X 6 2 f hmodel) P hP

theorem outSolvableAlpha_of_rankTwo (h : OutSolvableRankTwoStatement) :
    OutSolvableAlphaStatement := by
  intro X _ _ hX hnonab P hP
  rcases hX with hG2 | hU3 | hD4 | hJ2
  · exact h X (Or.inl hG2) hnonab P hP
  · haveI hsimp : IsSimpleGroup X :=
      (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 3 1 hU3).2
    exact perfect_action_inner_of_catalog X hnonab
      (CFSG.ClassicalModels.statedClassicalModel_PSU_inCatalog X 3 3 1 hU3) P hP
  · exact h X (Or.inr hD4) hnonab P hP
  · obtain ⟨φ⟩ := hJ2
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
      CFSG.Sporadic.J2.isSimpleGroup_J2
    haveI hsimp : IsSimpleGroup X := φ.isSimpleGroup
    exact perfect_action_inner_of_catalog X hnonab (sporadicBridge_J2 X ⟨φ⟩) P hP

end Certs

end CFSG.RankThree.GF2n.Stroth80
