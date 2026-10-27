module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofRed
public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item224KFactsProof

theorem outTwoCyclic_of_isCyclic_outer {X : Type*} [Group X]
    (h : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :
    OutTwoCyclic X := by
  intro P _ hPI
  refine isCyclic_of_injective
    ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)).comp
      P.subtype) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro p hp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hp
  have : (p : MulAut X) ∈ P ⊓ (MulAut.conj : X →* MulAut X).range := ⟨p.2, hp⟩
  rw [hPI, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (Subtype.ext this)

theorem outTwoCyclic_projSp {n : ℕ} (hn : 0 < n) :
    OutTwoCyclic (projSp 2 (GaloisField 2 n)) := by
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n hn.ne']
  obtain ⟨hcyc, -⟩ := CFSG.QuasithinUnique.Lin2.sp4OutCyclic (GaloisField 2 n) n hcard hn
  exact outTwoCyclic_of_mulEquiv
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 n))).symm
    (outTwoCyclic_of_isCyclic_outer hcyc)

theorem autEllipticTorus_of_borelTits_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hO : OutTwoCyclic X) (hBT : AutTorusBorelTits X) : AutEllipticTorus X := by
  intro E hE hE9 hinner hfix T hT hT1 hTE
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · obtain ⟨x, -, hxZ, -⟩ := hfix
      exact absurd (h ▸ Subgroup.mem_top x) hxZ
  exact autElliptic_of_oddFixedBorelTits hZ hO (hBT E hE hE9 hinner hfix T hT hT1 hTE)

end Item224KFactsProof

open Item224KFactsProof

@[expose] def KS224Sp4BorelTits : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 0 < n → Even n →
    Nonempty (X ≃* projSp 2 (GaloisField 2 n)) → AutTorusBorelTits X

@[expose] def KS224U4BorelTits : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 0 < n → Even n →
    Nonempty (X ≃* projSU 4 2 n) → AutTorusBorelTits X

@[expose] def KS224U4OutTwoCyclic : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 0 < n → Even n →
    Nonempty (X ≃* projSU 4 2 n) → OutTwoCyclic X

@[expose] def KS224U5BorelTits : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSU 5 2 2) → AutTorusBorelTits X

@[expose] def KS224U5OutTwoCyclic : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSU 5 2 2) → OutTwoCyclic X

theorem ks224Sp4_of_borelTits (hBT : KS224Sp4BorelTits) : KS224Sp4 := by
  intro X _ _ n hn he hX
  obtain ⟨e⟩ := hX
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := he
    omega
  have := isSimpleGroup_projSp_two hn2
  have : IsSimpleGroup X := e.isSimpleGroup
  exact autEllipticTorus_of_borelTits_simple
    (outTwoCyclic_of_mulEquiv e (outTwoCyclic_projSp hn)) (hBT X n hn he ⟨e⟩)

theorem ks224U4_of (hBT : KS224U4BorelTits) (hO : KS224U4OutTwoCyclic) : KS224U4 := by
  intro X _ _ n hn he hX
  obtain ⟨e⟩ := hX
  have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl hn
  have : IsSimpleGroup X := e.isSimpleGroup
  exact autEllipticTorus_of_borelTits_simple (hO X n hn he ⟨e⟩) (hBT X n hn he ⟨e⟩)

theorem ks224U5_of (hBT : KS224U5BorelTits) (hO : KS224U5OutTwoCyclic) : KS224U5 := by
  intro X _ _ hX
  obtain ⟨e⟩ := hX
  have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
  have : IsSimpleGroup X := e.isSimpleGroup
  exact autEllipticTorus_of_borelTits_simple (hO X ⟨e⟩) (hBT X ⟨e⟩)

end CFSG.RankThree.PartTwo.Sec21
