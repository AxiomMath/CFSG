module

public import CFSG.Quasithin.Vol2.Ch10SecA1011OneSec
public import CFSG.Quasithin.Background.InternalSecRealB
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB45
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem case_two_of_alt
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (h116 : ASInputs.AS_I_1_6_one)
    (hyp : Ch10.Hyp10 G T L I) (hUI : fsuUL T L I = I) [hUab : IsMulCommutative ↥(fsuUL T L I)]
    (halt : AlternatingNatural (lSec T L I) ⊤ ⊥ 5) :
    Ch10.Case10_1_1Two T L I ∧ Ch10.cV1 T L I = ⊥ := by
  have h := oneSec_of h37 h38 h322 hshape hyp hUI
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  have hcomm := commutator_fsuUL_eq h37 h38 hyp hUI
  have hUel : IsElemAbelian 2 (fsuUL T L I) :=
    ⟨hUab, fun u hu => (isec_of_one h37 h38 h322 hyp hUI).elem u hu⟩
  obtain ⟨π, hR⟩ := id halt
  have := h.simple
  have : Nontrivial ↥(lSec T L I) := IsSimpleGroup.toNontrivial
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 5) (by norm_num)) π hR.1
  obtain ⟨eL⟩ := h.equiv
  have hmod := InternalSec.alternatingNatural_of_autSec h.stab h.faithful halt
  have hmod' := hmod
  rw [cV1_eq h37 h38 hyp] at hmod'
  have h1 := h116 G L (fsuUL T L I) hLU hUel hcomm.symm ⟨hUab, hmod'⟩
  have hC : Ch10.cV1 T L I = ⊥ := by
    rw [cV1_eq h37 h38 hyp, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm, h1]
  rw [hC] at hmod
  exact ⟨⟨⟨eL.symm.trans e.symm⟩, hUab, hmod⟩, hC⟩

theorem cases_of_b42Out
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (h116 : ASInputs.AS_I_1_6_one)
    (hyp : Ch10.Hyp10 G T L I) (hUI : fsuUL T L I = I) [hUab : IsMulCommutative ↥(fsuUL T L I)]
    (hout : (∃ n, 2 ≤ n ∧ BinaryNaturalSL (lSec T L I) ⊤ ⊥ 2 n) ∨
      BinaryNaturalSL (lSec T L I) ⊤ ⊥ 3 1 ∨ AlternatingNatural (lSec T L I) ⊤ ⊥ 5) :
    (∃ n, Ch10.Case10_1_1One T L I n) ∨ (Ch10.Case10_1_1Two T L I ∧ Ch10.cV1 T L I = ⊥) ∨
      Ch10.Case10_1_1Three T L I := by
  have h := oneSec_of h37 h38 h322 hshape hyp hUI
  obtain ⟨eA⟩ := h.equivL
  rcases hout with ⟨n, hn, hnat⟩ | hnat | halt
  · obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := InternalSec.BinaryNaturalSL.equiv_of_autSec h.stab h.faithful hnat
    exact Or.inl ⟨n, by omega, ⟨F, inferInstance, inferInstance, hFc,
      ⟨eA.symm.trans (e.symm.trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm)⟩⟩, hUab,
      InternalSec.binaryNaturalSL_of_autSec h.stab h.faithful hnat⟩
  · obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := InternalSec.BinaryNaturalSL.equiv_of_autSec h.stab h.faithful hnat
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
      rw [← Nat.card_congr eA.toEquiv, ← Nat.card_congr e.toEquiv, card_statedSL,
        card_SL_three_pow hFc]
      norm_num
    exact Or.inr (Or.inr ⟨equiv_SL_three_of_card h.shapeL hc, hUab,
      InternalSec.binaryNaturalSL_of_autSec h.stab h.faithful hnat⟩)
  · exact Or.inr (Or.inl (case_two_of_alt h37 h38 h322 hshape h116 hyp hUI halt))

theorem cases_of_one
    (hF : Facts10_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h45 : AsB45) (h116 : ASInputs.AS_I_1_6_one) (h16 : ASInputs.AS_I_1_6)
    (hyp : Ch10.Hyp10 G T L I) (hUI : fsuUL T L I = I) :
    (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I ∨ Ch10.Case10_1_1Three T L I ∨
      (∃ n, Ch10.Case10_1_1Four T L I n ∧ Ch10.cV1 T L I = ⊥) ∨ Case10_1_1SevenWeak T L I := by
  obtain ⟨-, -, -, -, -, ⟨hUab, -⟩, -⟩ := hyp.three
  have h := oneSec_of h37 h38 h322 hshape hyp hUI
  have := h.simple
  obtain ⟨eA⟩ := h.equivL
  obtain ⟨eL⟩ := h.equiv
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  have hcomm := commutator_fsuUL_eq h37 h38 hyp hUI
  have helem := (isec_of_one h37 h38 h322 hyp hUI).elem'
  rcases h45 _ h.sq _ _ h.b4 (qhatOf_ySec_le h37 h38 h322 hyp hUI) with
    ⟨-, ⟨A, hA⟩, hall⟩ | ⟨-, ht⟩ | h3
  · have := cases_of_b42Out h37 h38 h322 hshape h116 hyp hUI
      (b42_of_isShapeGroup hF h.sq h.b4 hA (hall A hA) h.shape)
    tauto
  · rcases table_of_isShapeGroup hF h.b4 ht h.shape with ⟨m, hm, horth⟩ | ⟨f, hsz⟩
    · rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · have hm1 : m = 1 := by omega
        subst hm1
        exact Or.inr (Or.inl (case_two_of_alt h37 h38 h322 hshape h116 hyp hUI
          (hF.orthA5 _ _ _ _ horth)).1)
      ·
        obtain ⟨K, _, _, _, hKc, π, hR⟩ := id horth
        have e := MulEquiv.ofBijective π ⟨hR.injective_of_faithful (twistTensor_faithful m), hR.1⟩
        have hmod := InternalSec.binaryOrthogonalFour_of_autSec h.stab h.faithful horth
        have hfix := (h16 ↥(fsuUL T L I) helem (autOn L (fsuUL T L I)) 0).1
          (InternalSec.commV_autOn_eq_top hLU hcomm)
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, rfl, by
            rw [fixV_autOn_fsuUL h37 h38 hyp]
            exact hmod⟩))))
        rw [fixV_autOn_fsuUL h37 h38 hyp] at hfix
        have hC : Ch10.cV1 T L I = ⊥ := by
          rw [← Subgroup.card_le_one_iff_eq_bot]
          simpa using hfix
        rw [hC] at hmod
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, ⟨by omega, ⟨K, inferInstance, inferInstance, hKc,
          ⟨eL.symm.trans (e.symm.trans
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm)⟩⟩,
          hUab, hmod⟩, hC⟩)))
    ·
      obtain ⟨a, F, _, _, ha, hfa, hFc, ⟨e⟩⟩ :=
        InternalSec.BinaryNaturalSz.equiv_of_autSec h.stab h.faithful hsz
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f, ⟨rfl, a, ha, F, inferInstance, inferInstance, hfa,
        hFc, ⟨eA.symm.trans e.symm⟩⟩, hUab,
        InternalSec.binaryNaturalSz_of_autSec h.stab h.faithful hsz⟩)))
  · exact (not_part3_of_isShapeGroup hF h3 h.shape).elim

end CFSG.Quasithin.Vol2.Ch10.SecA
