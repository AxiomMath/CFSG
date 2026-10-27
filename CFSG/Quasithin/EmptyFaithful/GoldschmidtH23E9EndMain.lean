module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Five2cD
public import CFSG.Quasithin.EmptyFaithful.S151ZR
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9EndDef
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9EndAux

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.H23P4
open scoped Pointwise commutatorElement

theorem lemma15123FiveInputC_of_rows
    (rows : P4Rows) (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) : Lemma15123FiveInputC := by
  rintro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 h21 h5
    ⟨Y, hYM, hYJ, hY5, hSY, hVY, hYV, hSV, hVS, hfac⟩
  obtain ⟨hNL, hLV⟩ := h19.seven L hL.comp hL.quasi hL.not_le
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := fun y hy =>
    hNL (Subgroup.mem_sup_left (mem_oTwoUpper_of_odd ⟨(hYM hy).1, (hYM hy).2⟩
      (odd_orderOf_of_isPGroup_five hY5 y hy)))
  have hVN : V₂ ≤ Subgroup.normalizer (L : Set G) := fun v hv => hNL (Subgroup.mem_sup_right hv)
  have hfd : FiveData L (s1516 T Z₁) Y V₂ :=
    ⟨hC.setting.sylow.2.1, h20.1, hY5, hYN, hSY, hVN, hLV, hVY⟩
  rcases dichotomy_of_isL1519 hL h19.one with hchar | hcomp
  ·
    obtain ⟨hJ, hcases⟩ := h20.2.2.1 hchar
    rcases hcases with hA | hB | hC2
    · exact (not_caseTwoA_15122 hL h21 hchar hA).elim
    ·
      rcases hB.1 hL.comp with h7 | h3 | h6 | hg
      · obtain ⟨hsh, α, hα⟩ := h7
        exact hfd.false_of_block hsh hL.quasi
          (RowOK.quot_of_surjective α hα.1 (CFSG.pCore 2 ↥L) hα.2.1 rows.alt7)
          (by rw [index_altBlock hα, card_altHeart_seven]) (Or.inr (Or.inr rfl))
      · obtain ⟨hsh, hmat⟩ := h3
        obtain ⟨α, hαs, hαk, -⟩ := id hmat
        exact hfd.false_of_block hsh hL.quasi
          (RowOK.quot_of_surjective α hαs (CFSG.pCore 2 ↥L) hαk rows.sl32)
          (by rw [index_matrixBlock hmat, Nat.card_fun]; simp) (Or.inl rfl)
      · obtain ⟨hsh, α, hα⟩ := h6
        exact hfd.false_of_block hsh hL.quasi
          (RowOK.quot_of_surjective α hα.1 (CFSG.pCore 2 ↥L) hα.2.1 rows.alt6)
          (by rw [index_altBlock hα, card_altHeart_six]) (Or.inr (Or.inl rfl))
      · obtain ⟨hsh, hpsu, hidx, hnatural⟩ := hg
        exact hfd.false_of_block hsh hL.quasi (rows.psu33 hpsu) hidx (Or.inr (Or.inr rfl))
    ·
      have hrow : RowOK (↥L ⧸ CFSG.pCore 2 ↥L) := by
        rcases hC2.1 with h | h
        · exact rows.psl4 h
        · exact rows.psl5 h
      have h20' : Lemma15120Concl T Mc M Z₁ L :=
        ⟨h20.1, h20.2.1, fun _ => ⟨hJ, Or.inr (Or.inr hC2)⟩,
          fun hcomp => (not_charTwo_of_isComponentOf hchar hcomp).elim⟩
      have c : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h20', h21⟩
      have h3 := input15122L45Block'_holds h118 h126 h37 h38 G T Mc M Z₁ Z₂ V₁ V₂ L c hchar hC2
      exact (five2c_false_of_factor c h3 hYN (hfd.le_cMod hrow) hfac).elim
  ·
    have hq : CFSG.IsQuasisimple ↥L :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hcomp.2.2
    obtain ⟨-, hcases⟩ := h20.2.2.2 hcomp
    obtain ⟨hnA, hnB⟩ := noBorel_of_h21 hL h21 hcomp
    rcases hcases with hA | hB | hC3 | hD | hE | hA6 | hA7
    · exact (hnA hA).elim
    · exact (hnB hB).elim
    ·
      rcases hC3 with h | h | h
      · exact hfd.false_of_component hq (RowOK.quot_pCore hq (rows.psu33 h))
      · exact hfd.false_of_tits hq (rows.tits h) hVS
          (fun s hs v hv => (Subgroup.mem_normalizer_iff.1 (hSV hs) v).1 hv)
          (fun y hy v hv => (Subgroup.mem_normalizer_iff.1 (hYV hy) v).1 hv)
          (((hC.setting.ranks_six ⟨5, Or.inr rfl, h5⟩).2.1).le.trans (by norm_num))
      · exact hfd.false_of_component hq (RowOK.quot_pCore hq (rows.d4 h))
    ·
      rcases hD with h | h | h | h | h | h | h | h | h
      · exact hfd.false_of_component hq (rows.m11 h)
      · exact hfd.false_of_component hq (rows.m12 h)
      · exact hfd.false_of_component hq (rows.m22 h)
      · exact hfd.false_of_component hq (rows.m23 h)
      · exact hfd.false_of_component hq (rows.m24 h)
      · exact hfd.false_of_component hq (rows.j2 h)
      · exact hfd.false_of_component hq (rows.hs h)
      · exact hfd.false_of_component hq (rows.he h)
      · exact hfd.false_of_component hq (rows.ru h)
    ·
      rcases hE with h | h
      · exact hfd.false_of_component hq (RowOK.quot_pCore hq (rows.psl4 h))
      · exact hfd.false_of_component hq (RowOK.quot_pCore hq (rows.psl5 h))
    ·
      obtain ⟨e⟩ := hA6
      exact hfd.false_of_component hq
        (RowOK.quot_pCore hq (RowOK.of_mulEquiv e.symm rows.alt6))
    ·
      obtain ⟨e⟩ := hA7
      exact hfd.false_of_component hq
        (RowOK.quot_pCore hq (RowOK.of_mulEquiv e.symm rows.alt7))

end CFSG.Quasithin.E9
