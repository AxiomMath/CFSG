module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Main
public import CFSG.RankThree.PartTwo.Sec19.SimsC198List

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def MainConcl (X : Type) [Group X] (𝒟 : Subgroup (MulAut (X ⧸ Subgroup.center X))) :
    Prop :=
  (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    Nonempty (X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)) ∧
  ∃ φ ∈ 𝒟, φ ∉ (MulAut.conj : X ⧸ Subgroup.center X →* MulAut (X ⧸ Subgroup.center X)).range

@[expose] def CaseHolds (A : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], RankHyp X →
    ∀ (c : X ⧸ Subgroup.center X) (L : Subgroup (X ⧸ Subgroup.center X))
      (𝒟 : Subgroup (MulAut (X ⧸ Subgroup.center X))),
      AutDatum (X ⧸ Subgroup.center X) c L 𝒟 → A (X ⧸ Subgroup.center X) → MainConcl X 𝒟

@[expose] def Alt42One (G : Type) [Group G] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ Nonempty (G ≃* projSL 2 (GaloisField p e))

@[expose] def Alt42Two (G : Type) [Group G] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
    (Nonempty (G ≃* projSL 3 (GaloisField p e)) ∨ Nonempty (G ≃* projSU 3 p e))

@[expose] def Alt42Three (G : Type) [Group G] : Prop :=
  ∃ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group)

@[expose] def Alt42Four (G : Type) [Group G] : Prop :=
  ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoGTwo G q) ∨
      Nonempty (G ≃* projSp 2 (GaloisField p 1)) ∨
      Nonempty (G ≃* projSL 4 (GaloisField p 1)) ∨ Nonempty (G ≃* projSU 4 p 1))

@[expose] def Alt42Five (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ n ≤ 12 ∧ Nonempty (G ≃* alternatingGroup (Fin n))

@[expose] def Alt42Six (G : Type) [Group G] : Prop :=
  ∃ s ∈ sporadics42, Nonempty (G ≃* Spor s)

@[expose] def Alt42Seven (G : Type) [Group G] : Prop :=
  IsChevTwoRankTwo G

@[expose] def Alt42Eight (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 5 2 1) ∨
    Nonempty (G ≃* projSL 6 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 6 2 1) ∨
    Nonempty (G ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 1)) ∨
    Nonempty (G ≃* projSp 4 (GaloisField 2 1)) ∨
    Nonempty (G ≃* projOmegaPlus 4 (GaloisField 2 1)) ∨
    (∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (G ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) ∨
    Nonempty (G ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 2)) ∨
    Nonempty (G ≃* projSU 5 2 2) ∨ Nonempty (G ≃* projSU 5 2 3) ∨
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)

@[expose] def Alt42Nine (G : Type) [Group G] : Prop :=
  (∃ e : ℕ, 1 ≤ e ∧ e ≤ 3 ∧
      (Nonempty (G ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (G ≃* projSU 3 3 e))) ∨
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) ∨
    Nonempty (G ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (G ≃* projSU 4 3 1)

theorem list42_alts {G : Type} [Group G] (h : Census.List42 G) :
    Alt42One G ∨ Alt42Two G ∨ Alt42Three G ∨ Alt42Four G ∨ Alt42Five G ∨ Alt42Six G ∨
      Alt42Seven G ∨ Alt42Eight G ∨ Alt42Nine G :=
  h

theorem mainCensus_of_cases
    (h1 : CaseHolds Alt42One) (h2 : CaseHolds Alt42Two) (h3 : CaseHolds Alt42Three)
    (h4 : CaseHolds Alt42Four) (h5 : CaseHolds Alt42Five) (h6 : CaseHolds Alt42Six)
    (h7 : CaseHolds Alt42Seven) (h8 : CaseHolds Alt42Eight) (h9 : CaseHolds Alt42Nine) :
    MainCensus := by
  intro X _ _ hX c L 𝒟 hD
  rcases list42_alts (list42_of_rankHyp hX) with h | h | h | h | h | h | h | h | h
  · exact h1 X hX c L 𝒟 hD h
  · exact h2 X hX c L 𝒟 hD h
  · exact h3 X hX c L 𝒟 hD h
  · exact h4 X hX c L 𝒟 hD h
  · exact h5 X hX c L 𝒟 hD h
  · exact h6 X hX c L 𝒟 hD h
  · exact h7 X hX c L 𝒟 hD h
  · exact h8 X hX c L 𝒟 hD h
  · exact h9 X hX c L 𝒟 hD h

end CFSG.RankThree.PartTwo.Sec19.SimsC198
