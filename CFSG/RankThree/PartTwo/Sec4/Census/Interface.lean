module

public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex
  localRank)

@[expose] def List42 (G : Type) [Group G] : Prop :=
    (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
      Nonempty (G ≃* projSL 2 (GaloisField p e))) ∨
    (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (Nonempty (G ≃* projSL 3 (GaloisField p e)) ∨ Nonempty (G ≃* projSU 3 p e))) ∨
    (∃ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group)) ∨
    (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoGTwo G q) ∨
        Nonempty (G ≃* projSp 2 (GaloisField p 1)) ∨
        Nonempty (G ≃* projSL 4 (GaloisField p 1)) ∨ Nonempty (G ≃* projSU 4 p 1))) ∨
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 12 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    (∃ s ∈ sporadics42, Nonempty (G ≃* Spor s)) ∨
    IsChevTwoRankTwo G ∨
    (Nonempty (G ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 5 2 1) ∨
      Nonempty (G ≃* projSL 6 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 6 2 1) ∨
      Nonempty (G ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 1)) ∨
      Nonempty (G ≃* projSp 4 (GaloisField 2 1)) ∨
      Nonempty (G ≃* projOmegaPlus 4 (GaloisField 2 1)) ∨
      (∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) ∨
      Nonempty (G ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 2)) ∨
      Nonempty (G ≃* projSU 5 2 2) ∨ Nonempty (G ≃* projSU 5 2 3) ∨
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)) ∨
    ((∃ e : ℕ, 1 ≤ e ∧ e ≤ 3 ∧
        (Nonempty (G ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (G ≃* projSU 3 3 e))) ∨
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) ∨
      Nonempty (G ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (G ≃* projSU 4 3 1))

theorem item4_2_iff : Item4_2 ↔ ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
    IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → List42 G :=
  Iff.rfl

namespace List42

variable {G : Type} [Group G]

theorem one (p e : ℕ) [Fact p.Prime] (hp : p ≠ 2) (he : 1 ≤ e)
    (f : G ≃* projSL 2 (GaloisField p e)) : List42 G :=
  Or.inl ⟨p, e, inferInstance, hp, he, ⟨f⟩⟩

theorem two_SL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (f : G ≃* projSL 3 (GaloisField p e)) : List42 G :=
  Or.inr (Or.inl ⟨p, e, inferInstance, hp, he, he2, Or.inl ⟨f⟩⟩)

theorem two_SU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (f : G ≃* projSU 3 p e) : List42 G :=
  Or.inr (Or.inl ⟨p, e, inferInstance, hp, he, he2, Or.inr ⟨f⟩⟩)

theorem three (hr : (TauCeti.LieTypeIndex.reeG2 1).Valid)
    (f : G ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group) : List42 G :=
  Or.inr (Or.inr (Or.inl ⟨hr, ⟨f⟩⟩))

theorem four_G2 {q : TauCeti.PrimePower} (hq : 3 < q.p) (hf : q.exponent = 1)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (f : G ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : List42 G :=
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  Or.inr (Or.inr (Or.inr (Or.inl ⟨q.p, inferInstance, hq, Or.inl ⟨q, rfl, hf, hv, ⟨f⟩⟩⟩)))

theorem four_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) (f : G ≃* projSp 2 (GaloisField p 1)) :
    List42 G :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨p, inferInstance, hp, Or.inr (Or.inl ⟨f⟩)⟩)))

theorem four_SL (p : ℕ) [Fact p.Prime] (hp : 3 < p) (f : G ≃* projSL 4 (GaloisField p 1)) :
    List42 G :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨p, inferInstance, hp, Or.inr (Or.inr (Or.inl ⟨f⟩))⟩)))

theorem four_SU (p : ℕ) [Fact p.Prime] (hp : 3 < p) (f : G ≃* projSU 4 p 1) : List42 G :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨p, inferInstance, hp, Or.inr (Or.inr (Or.inr ⟨f⟩))⟩)))

theorem five {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) (f : G ≃* alternatingGroup (Fin n)) :
    List42 G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn5, hn, ⟨f⟩⟩))))

theorem six {s : TauCeti.SporadicName} (hs : s ∈ sporadics42) (f : G ≃* Spor s) : List42 G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, ⟨f⟩⟩)))))

theorem seven (h : IsChevTwoRankTwo G) : List42 G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem eight (h : Nonempty (G ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 5 2 1) ∨
      Nonempty (G ≃* projSL 6 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 6 2 1) ∨
      Nonempty (G ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 1)) ∨
      Nonempty (G ≃* projSp 4 (GaloisField 2 1)) ∨
      Nonempty (G ≃* projOmegaPlus 4 (GaloisField 2 1)) ∨
      (∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) ∨
      Nonempty (G ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 2)) ∨
      Nonempty (G ≃* projSU 5 2 2) ∨ Nonempty (G ≃* projSU 5 2 3) ∨
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)) : List42 G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem nine (h : (∃ e : ℕ, 1 ≤ e ∧ e ≤ 3 ∧
        (Nonempty (G ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (G ≃* projSU 3 3 e))) ∨
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) ∨
      Nonempty (G ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (G ≃* projSU 4 3 1)) : List42 G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

theorem eight_SL52 (f : G ≃* projSL 5 (GaloisField 2 1)) : List42 G := eight (Or.inl ⟨f⟩)

theorem eight_SU52 (f : G ≃* projSU 5 2 1) : List42 G := eight (Or.inr (Or.inl ⟨f⟩))

theorem eight_SL62 (f : G ≃* projSL 6 (GaloisField 2 1)) : List42 G :=
  eight (Or.inr (Or.inr (Or.inl ⟨f⟩)))

theorem eight_SU62 (f : G ≃* projSU 6 2 1) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inl ⟨f⟩))))

theorem eight_SL72 (f : G ≃* projSL 7 (GaloisField 2 1)) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f⟩)))))

theorem eight_Sp62 (f : G ≃* projSp 3 (GaloisField 2 1)) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f⟩))))))

theorem eight_Sp82 (f : G ≃* projSp 4 (GaloisField 2 1)) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f⟩)))))))

theorem eight_OmegaPlus (f : G ≃* projOmegaPlus 4 (GaloisField 2 1)) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f⟩))))))))

theorem eight_OmegaMinus {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    (f : G ≃* projOmegaMinus 3 (GaloisField 2 1) b c) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨b, c, hbc, ⟨f⟩⟩)))))))))

theorem eight_SL44 (f : G ≃* projSL 4 (GaloisField 2 2)) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨f⟩))))))))))

theorem eight_Sp64 (f : G ≃* projSp 3 (GaloisField 2 2)) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨f⟩)))))))))))

theorem eight_SU54 (f : G ≃* projSU 5 2 2) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl ⟨f⟩))))))))))))

theorem eight_SU58 (f : G ≃* projSU 5 2 3) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl ⟨f⟩)))))))))))))

theorem eight_F42 (f : G ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) : List42 G :=
  eight (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr ⟨f⟩)))))))))))))

theorem nine_SL3 {e : ℕ} (he : 1 ≤ e) (he3 : e ≤ 3) (f : G ≃* projSL 3 (GaloisField 3 e)) :
    List42 G :=
  nine (Or.inl ⟨e, he, he3, Or.inl ⟨f⟩⟩)

theorem nine_SU3 {e : ℕ} (he : 1 ≤ e) (he3 : e ≤ 3) (f : G ≃* projSU 3 3 e) : List42 G :=
  nine (Or.inl ⟨e, he, he3, Or.inr ⟨f⟩⟩)

theorem nine_G23 (f : G ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) : List42 G :=
  nine (Or.inr (Or.inl ⟨f⟩))

theorem nine_SL43 (f : G ≃* projSL 4 (GaloisField 3 1)) : List42 G :=
  nine (Or.inr (Or.inr (Or.inl ⟨f⟩)))

theorem nine_SU43 (f : G ≃* projSU 4 3 1) : List42 G := nine (Or.inr (Or.inr (Or.inr ⟨f⟩)))

end List42

namespace SectionFourHyp

variable {G : Type} [Group G] [Finite G]

theorem twoLocalOddRank_le (hG : SectionFourHyp G) : CFSG.twoLocalOddRank G ≤ 3 := by
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact hG.evenRank_le

theorem false_of_four_le_twoLocalOddRank (hG : SectionFourHyp G)
    (h : 4 ≤ CFSG.twoLocalOddRank G) : False := by
  have := twoLocalOddRank_le hG
  omega

theorem false_of_three_le_localRank (hG : SectionFourHyp G) {H : Type} [Group H] (e : G ≃* H)
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (h : ∀ [Finite H], 3 ≤ localRank r H) : False := by
  have : Finite H := Finite.of_equiv G e.toEquiv
  have hlt := hG.localRank_lt r hr hr3
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr] at hlt
  have h3 : 3 ≤ localRank r H := h
  omega

end SectionFourHyp

end CFSG.RankThree.PartTwo.Sec4.Census
