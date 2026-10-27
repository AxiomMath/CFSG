module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Five
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Wire
public import CFSG.Quasithin.EmptyFaithful.S151U1
public import CFSG.Quasithin.EmptyFaithful.LRedNoBorel
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Card
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Rows

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Five2cTrivial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L Y : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Setting1516Extra T Mc M Z₁ → Ce15Six T Mc M 5 → CharTwo L →
    Case15120TwoC Mc Z₁ L →
    ⁅L, thompsonJ (s1516 T Z₁)⁆ = L → Y ≤ M ⊓ g1_1516 Z₁ →
    Y ≤ Subgroup.normalizer (thompsonJ T : Set G) → IsPGroup 5 Y →
    ((s1516 T Z₁ : Set G) * (Y : Set G) = (Y : Set G) * (s1516 T Z₁ : Set G)) →
    ⁅V₂, Y⁆ = V₂ → Y ≤ Subgroup.normalizer (L : Set G) → Y ≤ SBc17.cMod L → ⁅L, Y⁆ = ⊥

end CFSG.Quasithin

namespace CFSG.Quasithin.H23P4

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

theorem odd_orderOf_of_isPGroup_five {G : Type} [Group G] {Y : Subgroup G} (hY : IsPGroup 5 Y) :
    ∀ y ∈ Y, Odd (orderOf y) := by
  intro y hy
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hY) ⟨y, hy⟩
  have h1 : orderOf y = 5 ^ k := by
    rw [← Subgroup.orderOf_coe (⟨y, hy⟩ : ↥Y)] at hk
    exact hk
  rw [h1]
  exact Odd.pow (by decide)

theorem lemma15123FiveInputV_of_rows (rows : P4Rows) (h2c : Five2cTrivial) :
    Lemma15123FiveInputV := by
  rintro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 h21 h5 hX
    ⟨Y, hYM, hYJ, hY5, hSY, hVY, hYV, hSV, hVS⟩
  have c : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h20, h21⟩
  obtain ⟨hNL, hLV⟩ := h19.seven L hL.comp hL.quasi hL.not_le
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := fun y hy =>
    hNL (Subgroup.mem_sup_left (mem_oTwoUpper_of_odd ⟨(hYM hy).1, (hYM hy).2⟩
      (odd_orderOf_of_isPGroup_five hY5 y hy)))
  have hVN : V₂ ≤ Subgroup.normalizer (L : Set G) := fun v hv => hNL (Subgroup.mem_sup_right hv)
  have hfd : FiveData L (s1516 T Z₁) Y V₂ :=
    ⟨hC.setting.sylow.2.1, h20.sylow, hY5, hYN, hSY, hVN, hLV, hVY⟩
  rcases input15122Dichotomy_holds G T Mc M Z₁ Z₂ V₁ V₂ L c with hchar | hcomp
  ·
    obtain ⟨hJ, hcases⟩ := h20.two hchar
    rcases hcases with hA | hB | hC2
    · exact (not_caseTwoA_15122 hL h21 hchar hA).elim
    ·
      rcases hB.2.1 hL.comp with h7 | h3 | h6 | hg
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
      exact hfd.false_of_comm (h2c G T Mc M Z₁ Z₂ V₁ V₂ L Y c hX h5 hchar hC2 hJ hYM hYJ hY5 hSY
        hVY hYN (hfd.le_cMod hrow))
  ·
    have hq : CFSG.IsQuasisimple ↥L :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hcomp.2.2
    obtain ⟨-, hcases⟩ := h20.three hcomp
    obtain ⟨hnA, hnB⟩ := input15122NoBorel_proved G T Mc M Z₁ Z₂ V₁ V₂ L c hcomp
    rcases hcases with hA | hB | hC3 | hD | hE
    · exact (hnA hA).elim
    · exact (hnB hB).elim
    ·
      rcases hC3.1 with h | h | h
      · exact hfd.false_of_component hq (RowOK.quot_pCore hq (rows.psu33 h))
      · exact hfd.false_of_tits hq (rows.tits h) hVS
          (fun s hs v hv => (Subgroup.mem_normalizer_iff.1 (hSV hs) v).1 hv)
          (fun y hy v hv => (Subgroup.mem_normalizer_iff.1 (hYV hy) v).1 hv)
          (((hC.setting.ranks_six ⟨5, Or.inr rfl, h5⟩).2.1).le.trans (by norm_num))
      · exact hfd.false_of_component hq (RowOK.quot_pCore hq (rows.d4 h))
    ·
      rcases hD.1 with h | h | h | h | h | h | h | h | h
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
      rcases hE.1 with h | h
      · exact hfd.false_of_component hq (RowOK.quot_pCore hq (rows.psl4 h))
      · exact hfd.false_of_component hq (RowOK.quot_pCore hq (rows.psl5 h))

end CFSG.Quasithin.H23P4
