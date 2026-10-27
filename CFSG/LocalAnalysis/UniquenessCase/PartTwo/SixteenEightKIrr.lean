module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Row
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowA7Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowG2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowL32
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowL34
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowL5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowM22
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowOmegaMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowOmegaPlus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowSp6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowTripleA6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRowU43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_card_ne_pow_zero {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 0) :
    False := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
  rw [hK] at h1
  norm_num at h1

theorem s16k_false_of_irr_nat (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L))
    (hfam : (∃ n : ℕ,
        (IsSLn ↥(lBar V₀ V hV L) n 1 ∧ BinaryNaturalSL (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 1) ∨
        (IsSpn ↥(lBar V₀ V hV L) n 1 ∧ NatSpn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
          (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 1) ∨
        (IsOmegaPlus ↥(lBar V₀ V hV L) n 1 ∧ NatOmegaPlus (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 1) ∨
        (IsOmegaMinus ↥(lBar V₀ V hV L) n 1 ∧ NatOmegaMinus (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 1) ∨
        (IsSUn ↥(lBar V₀ V hV L) n 1 ∧ NatSUn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
          (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 1)) ∨
      (∃ n : ℕ, UC22.IsAlt ↥(lBar V₀ V hV L) n ∧ AlternatingNatural (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n)) :
    False := by
  have hrow := h.toRowCtx hq
  rcases hfam with ⟨n, hn⟩ | ⟨n, hA, hN⟩
  · rcases hn with ⟨hSL, hN⟩ | ⟨hSp, hN⟩ | ⟨hΩ, hN⟩ | ⟨hΩ, hN⟩ | ⟨hSU, hN⟩
    · exact s16k_false_of_binaryNaturalSL hrow hGA (Or.inl rfl) hSL hN
    · exact s16k_false_of_natSp hrow hGA (Or.inl rfl) hSp hN
    · exact s16k_false_of_natOmegaPlus hrow hGA (Or.inl rfl) (Or.inr rfl) hΩ hN
    · exact s16k_false_of_natOmegaMinus hrow hGA (Or.inl rfl) hΩ hN
    · exact s16k_false_of_natSUn hrow hGA hSU hN
  · exact s16k_false_of_altNatural hrow hGA hA hN

theorem s16k_false_of_irr (h : S16kBase D V₀ V L hV) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hRI : S16kRowInputs) (hG2 : S16kG2IsU33)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L))
    (hirr : commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L)) {m : ℕ} (hm3 : m ≤ 3)
    (h135 : Conc4_135 (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) m) : False := by
  have hrow := h.toRowCtx hq
  rcases h135 with ⟨n, hn⟩ | ⟨n, hn⟩ | hg2 | htri | ⟨hu, hm⟩ | ⟨n, hA, hN⟩ | ha7 | ⟨hS, hm⟩ |
    ⟨hS, hm⟩ | ⟨hS, hm⟩ | ⟨hS, hm⟩ | ⟨hS, hm⟩
  · rcases Nat.lt_or_ge m 3 with hlt | hge
    · have hm12 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hn with ⟨hSL, hN⟩ | ⟨hSp, hN⟩ | ⟨hΩ, hN⟩ | ⟨hΩ, hN⟩
      · rcases hm12 with rfl | hm1 | hm2
        · obtain ⟨K, hF, hFin, hK, -⟩ := hSL
          exact s16k_card_ne_pow_zero hK
        · exact s16k_false_of_binaryNaturalSL hrow hGA (Or.inl hm1) hSL hN
        · exact s16k_false_of_binaryNaturalSL hrow hGA (Or.inr hm2) hSL hN
      · rcases hm12 with rfl | hm1 | hm2
        · obtain ⟨-, K, hF, hFin, hK, -⟩ := hN
          exact s16k_card_ne_pow_zero hK
        · exact s16k_false_of_natSp hrow hGA (Or.inl hm1) hSp hN
        · exact s16k_false_of_natSp hrow hGA (Or.inr hm2) hSp hN
      · rcases hm12 with rfl | hm1 | hm2
        · obtain ⟨-, K, hF, hFin, hK, -⟩ := hN
          exact s16k_card_ne_pow_zero hK
        · exact s16k_false_of_natOmegaPlus hrow hGA (Or.inl hm1) (Or.inr hm1) hΩ hN
        · by_cases h4 : n = 4
          · subst h4
            subst hm2
            exact C163.not_isQuasisimple_of_isOmegaPlus_four (by norm_num) hΩ hq
          · exact s16k_false_of_natOmegaPlus hrow hGA (Or.inr hm2) (Or.inl h4) hΩ hN
      · rcases hm12 with rfl | hm1 | hm2
        · obtain ⟨-, K, hF, hFin, b, c, hK, -⟩ := hN
          exact s16k_card_ne_pow_zero hK
        · exact s16k_false_of_natOmegaMinus hrow hGA (Or.inl hm1) hΩ hN
        · exact s16k_false_of_natOmegaMinus hrow hGA (Or.inr hm2) hΩ hN
    · have hm3' : m = 3 := le_antisymm hm3 hge
      subst hm3'
      have h4 := hrow.natural_eight_eq_omegaPlus_four hGA ⟨n, hn⟩
      exact C163.not_isQuasisimple_of_isOmegaPlus_four (by norm_num) h4.1 hq
  · exact s16k_false_of_irr_nat h hGA hq (Or.inl ⟨n, hn⟩)
  · exact s16k_false_of_g2 hG2 hrow hg2
  · exact s16k_false_of_tripleA6 hrow htri
  · exact s16k_false_of_u43 hrow hRI.hU43 hirr hu hm
  · exact s16k_false_of_irr_nat h hGA hq (Or.inr ⟨n, hA, hN⟩)
  · exact s16k_false_of_a7four hrow ha7
  · exact s16k_false_of_sp6 hrow hGA hRI.hSpC hRI.hSpF hRI.hSpSt hirr hS hm
  · exact s16k_false_of_l5 hrow hRI.hI2 hirr hS hm
  · exact s16k_false_of_m22 hrow hRI.hI2 hRI.hOutM22 hirr hS hm
  · exact s16k_false_of_l34 hrow hirr hS hm
  · exact s16k_false_of_l32 hrow hirr hS hm

theorem s16k_concl163_of_irr (h : S16kBase D V₀ V L hV) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hRI : S16kRowInputs) (hG2 : S16kG2IsU33) {t : MulAut (Vtil V₀ V hV)}
    (ht : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hirr : commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L))
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (h135 : Conc4_135 (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))
      (E3.mQuot (commSub (commSub ⊤ (lBar V₀ V hV L)) (Subgroup.zpowers t) ⊔
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))) :
    Concl163 D V₀ V hV L :=
  (s16k_false_of_irr h hGA hRI hG2 hcomp.2.2 hirr
    ((s16k_mQuot_le_rk V₀ V hV _ _ t).trans ht) h135).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
