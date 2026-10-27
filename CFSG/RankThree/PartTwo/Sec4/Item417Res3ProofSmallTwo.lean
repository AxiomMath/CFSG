module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofChevTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


namespace Res417Three

@[expose] def K417CenterSmallTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → SectionFourHyp Y →
    (Nonempty (Y ⧸ Subgroup.center Y ≃* projSL 5 (GaloisField 2 1)) ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* projSp 3 (GaloisField 2 1)) ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* projSU 5 2 2)) →
    ∀ r : ℕ, r.Prime → 3 < r → ¬ r ∣ Nat.card (Subgroup.center Y)

@[expose] def K417DatumSmallTwo : Prop :=
  (∀ D : Subgroup (projSL 5 (GaloisField 2 1)), IsDatum417 (projSL 5 (GaloisField 2 1)) D →
    Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 4)) ∧
  (∀ D : Subgroup (projSU 5 2 2), IsDatum417 (projSU 5 2 2) D →
    Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 4)) ∧
  (∀ D : Subgroup (projSp 3 (GaloisField 2 1)), IsDatum417 (projSp 3 (GaloisField 2 1)) D →
    Nat.card D = 27 ∧
      Nonempty (autIn ⊤ D ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

end Res417Three

open Res417Three

section Certs


theorem item417OutSmallTwo_of (hC : K417CenterSmallTwo) (hD : K417DatumSmallTwo) :
    Item417OutSmallTwo := by
  intro G _ _ L A E c m hconf hX
  have eC := hconf.centerEquiv
  have hm3 := three_le_of_isQuad hconf.2.2.2.2.1
  have hθ : aschbacherSolvableCore 3 L = ⊥ := by
    refine theta_eq_bot_of_two_three hconf.2.1 hconf.2.2.1 fun r hr hr3 =>
      hC L hconf.2.2.1.1 (sectionFourHyp_subgroup hconf.1 L) ?_ r hr hr3
    rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact Or.inl ⟨eC.trans φ⟩
    · exact Or.inr (Or.inl ⟨eC.trans φ⟩)
    · exact Or.inr (Or.inr ⟨eC.trans φ⟩)
  set eL : L ≃* L ⧸ aschbacherSolvableCore 3 L := (Res417.thetaQuotEquivOfEqBot hθ).symm
  rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · obtain ⟨hdat, hcD, ⟨eA⟩⟩ := hconf.datum (eL.trans φ)
    obtain ⟨h9, ⟨q⟩⟩ := hD.1 _ hdat
    have hm := eq_of_card_datum (k := 2) hm3 hcD (h9.trans (by norm_num))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hm, Or.inr (Or.inr (Or.inr ⟨eL.trans φ⟩)), ⟨eA.trans q⟩⟩))))))))))
  · obtain ⟨hdat, hcD, ⟨eA⟩⟩ := hconf.datum (eL.trans φ)
    obtain ⟨h27, ⟨q⟩⟩ := hD.2.2 _ hdat
    have hm := eq_of_card_datum (k := 3) hm3 hcD (h27.trans (by norm_num))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨hm, ⟨eL.trans φ⟩, ⟨eA.trans q⟩⟩)))))))))))
  · obtain ⟨hdat, hcD, ⟨eA⟩⟩ := hconf.datum (eL.trans φ)
    obtain ⟨h9, ⟨q⟩⟩ := hD.2.1 _ hdat
    have hm := eq_of_card_datum (k := 2) hm3 hcD (h9.trans (by norm_num))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hm, Or.inr (Or.inl ⟨eL.trans φ⟩), ⟨eA.trans q⟩⟩))))))))))

end Certs

end CFSG.RankThree.PartTwo.Sec4
