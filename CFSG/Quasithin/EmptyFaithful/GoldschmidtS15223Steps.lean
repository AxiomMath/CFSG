module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Main
public import CFSG.Quasithin.EmptyFaithful.S153DC27
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def L3NotInMc15223 [Finite G] (T Mc M H : Subgroup G)
    (B₀ : Subgroup (MulAut (V154 T Mc M))) (I : Subgroup G) : Prop :=
  ∀ X R : Subgroup G, X ∈ cComp I → CharTwo X → CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) →
    ¬ X ≤ M ⊓ I → oTwoUpper H ≤ Subgroup.normalizer (X : Set G) →
    R ≤ sOf152 T Mc M B₀ → R ≤ Subgroup.normalizer (X : Set G) →
    C27Concl I R (M ⊓ I) X (omegaOneCenterOf (pCoreOf 2 (X ⊔ R))) →
    SBc17.C27SL3 I R (M ⊓ I) X (omegaOneCenterOf (pCoreOf 2 (X ⊔ R))) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ∧
      Nonempty (↥(autOn X (omegaOneCenterOf (pCoreOf 2 (X ⊔ R)))) ≃*
        ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) →
    ¬ X ≤ Mc

@[expose] def Reduction15223P2 : Prop :=
  Reduction15223P1 → ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G),
    Setting152 T Mc M → ∀ H : Subgroup G, IsHStar T M H →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → CharTwo I →
          (∀ X : Subgroup G, ¬ IsChiBlock2 I X) ∧ L3NotInMc15223 T Mc M H B₀ I

@[expose] def Reduction15223P3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → CharTwo I → Concl15218i Mc M I →
        ∃ (r : ℕ) (L : Fin r → Subgroup G), (∀ i, IsChiBlock2 I (L i)) ∧
          ∀ h ∈ I, ∃ m ∈ Mc ⊓ I, ∃ x : Fin r → G, (∀ i, x i ∈ L i) ∧
            h = m * (List.ofFn x).prod

@[expose] def Reduction15223P4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → CharTwo I →
        (∀ X : Subgroup G, ¬ IsChiBlock2 I X) → L3NotInMc15223 T Mc M H B₀ I →
          Concl15218ii T Mc M H B₀ I → False

namespace S15223

theorem stageLemma15223_of_steps (h5 : StageLemma15205) (h159 : StageLemma1519)
    (h8 : StageLemma15208) (h11 : StageLemma15211) (h12 : He12.StageLemma15212W)
    (h13 : StageLemma15213) (h14 : StageLemma15214) (hN : StageNotation15209)
    (h16 : StageLemma15216) (h17 : StageLemma15217) (h18 : StageLemma15218)
    (hP2 : Reduction15223P2) (hP3 : Reduction15223P3) (hP4 : Reduction15223P4) :
    StageLemma15223 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI hchar
  have hP1 : Reduction15223P1 :=
    reduction15223P1_of (fun _ _ _ _ hX => S152O4.om4_facts hX) h5 h159 h8 h11 h12 h13 h14 hN h16
      h17
  obtain ⟨hno, hnot⟩ := hP2 hP1 G T Mc M hs H hH B₀ hB₀ I hI hchar
  rcases (h18 G T Mc M hs H hH B₀ hB₀ I hI.1).cases with hi | hii
  · obtain ⟨r, L, hL, hall⟩ := hP3 G T Mc M hs H hH B₀ hB₀ I hI hchar hi
    refine hI.1.not_le fun h hh => ?_
    obtain ⟨m, hm, x, hx, rfl⟩ := hall h hh
    cases r with
    | zero => simpa using (Subgroup.mem_inf.mp hm).1
    | succ r => exact absurd (hL 0) (hno _)
  · exact hP4 G T Mc M hs H hH B₀ hB₀ I hI hchar hno hnot hii

end S15223

end CFSG.Quasithin
