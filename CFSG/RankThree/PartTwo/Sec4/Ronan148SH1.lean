module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRows

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def Row427 (S : Type) [Group S] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G, Late.IsE27 A →
    partTwoE G = partTwoF G → aschbacherSolvableCore 3 G = ⊥ → ∀ L : Subgroup G, IsComponent L →
    Nonempty (L ⧸ Subgroup.center L ≃* S) →
    ∀ d ∈ A, d ≠ 1 →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
    ¬ L ≤ Subgroup.centralizer {d} →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {d} : Subgroup G), IsComponent K →
      (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 5)) ∨
        (d ∈ K.map (L ⊓ Subgroup.centralizer {d}).subtype ∧
          IsExtOf (K ⧸ CFSG.pCore 2 K) Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3)))) →
      False

@[expose] def RowOf427 (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → Row427 S

structure K427Rows : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → RowOf427 (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf427 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf427 (projSU 3 p e)
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf427 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf427 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf427 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf427 (projSU 4 p 1)
  five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowOf427 (alternatingGroup (Fin n))
  six : ∀ s ∈ sporadics42, RowOf427 (Spor s)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowOf427 (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowOf427 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowOf427 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowOf427 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowOf427 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowOf427 (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowOf427 (projSU 5 2 1)
  eight_SL6 : RowOf427 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowOf427 (projSU 6 2 1)
  eight_SL7 : RowOf427 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowOf427 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowOf427 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowOf427 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowOf427 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowOf427 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowOf427 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowOf427 (projSU 5 2 2)
  eight_SU5_8 : RowOf427 (projSU 5 2 3)
  eight_F4 : RowOf427 (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOf427 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOf427 (projSU 3 3 e)
  nine_G2 : RowOf427 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowOf427 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowOf427 (projSU 4 3 1)

namespace K427Rows

variable {S : Type} [Group S] [Finite S]

theorem row_of_list42 (R : K427Rows) (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : Census.List42 S) : Row427 S := by
  rcases h with ⟨p, e, hp, h2, he, hf⟩ | ⟨p, e, hp, h3, he, he2, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p, hp, h3, ⟨q, hqp, hqe, hq, hf⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ |
    ⟨s, hsp, hf⟩ | h7 | h8 | h9
  · exact R.one p e h2 he S hs hna hf
  · exact R.two_SL p e h3 he he2 S hs hna hf
  · exact R.two_SU p e h3 he he2 S hs hna hf
  · exact R.three hr S hs hna hf
  · exact R.four_G2 p h3 q hqp hqe hq S hs hna hf
  · exact R.four_Sp p h3 S hs hna hf
  · exact R.four_SL p h3 S hs hna hf
  · exact R.four_SU p h3 S hs hna hf
  · exact R.five n hn5 hn12 S hs hna hf
  · exact R.six s hsp S hs hna hf
  · rcases h7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hq, hf⟩ |
      ⟨q, hq, hq2, hf⟩ | ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    · exact R.seven_SL2 n hn S hs hna hf
    · exact R.seven_SL3 n hn S hs hna hf
    · exact R.seven_SU3 n hn S hs hna hf
    · exact R.seven_Sp4 n hn S hs hna hf
    · exact R.seven_SU4 n hn S hs hna hf
    · exact R.seven_G2 q hq2 hq S hs hna hf
    · exact R.seven_D4 q hq hq2 S hs hna hf
    · exact R.seven_Sz m hm S hs hna hf
    · exact R.seven_F4 m hm S hs hna hf
    · exact R.seven_Tits ht S hs hna hf
  · rcases h8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf |
      hf | hf | hf | hf
    · exact R.eight_SL5 S hs hna hf
    · exact R.eight_SU5 S hs hna hf
    · exact R.eight_SL6 S hs hna hf
    · exact R.eight_SU6 S hs hna hf
    · exact R.eight_SL7 S hs hna hf
    · exact R.eight_Sp6 S hs hna hf
    · exact R.eight_Sp8 S hs hna hf
    · exact R.eight_OmegaPlus S hs hna hf
    · exact R.eight_OmegaMinus b c hbc S hs hna hf
    · exact R.eight_SL4 S hs hna hf
    · exact R.eight_Sp6_4 S hs hna hf
    · exact R.eight_SU5_4 S hs hna hf
    · exact R.eight_SU5_8 S hs hna hf
    · exact R.eight_F4 S hs hna hf
  · rcases h9 with ⟨e, he, he3, hf | hf⟩ | hf | hf | hf
    · exact R.nine_SL3 e he he3 S hs hna hf
    · exact R.nine_SU3 e he he3 S hs hna hf
    · exact R.nine_G2 S hs hna hf
    · exact R.nine_SL4 S hs hna hf
    · exact R.nine_SU4 S hs hna hf

end K427Rows

section Main

theorem item4_27_of_rows (R : K427Rows) : Item4_27 := by
  intro G _ _ hG A hA hEF hθ L hL d hdA hd1 hN K hK htype
  by_cases hLd : L ≤ Subgroup.centralizer {d}
  · exact eq_of_le_centralizer hL hLd hK rfl
  · exfalso
    have hq : IsQuasisimple L := hL.1
    have hlist := RonanK432.list42_quotient_center hq (sectionFourHyp_subgroup hG L)
    exact R.row_of_list42 hq.2.1 hq.2.2 hlist G hG A hA hEF hθ L hL ⟨MulEquiv.refl _⟩ d hdA hd1
      hN hLd K hK htype

end Main

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
