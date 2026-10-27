module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Inst
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Fin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Blk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Glue
public import CFSG.Quasithin.EmptyFaithful.T1521SA5Two
public import CFSG.Quasithin.EmptyFaithful.T1521SA5Blk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamL3Four
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamSp4Four

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.H23P4
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_five (horb : A3Orbits G) {X S L Y : Subgroup G} (hStd : Std1521 X S L)
    (hYX : Y ≤ X) (hY5 : IsPGroup 5 ↥Y) : Y ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hXS, hcase⟩ := horb X S L hStd.sqtk hStd.sylow hStd.comp
  exact le_normalizer_of_orbits hXS (hcase.imp id fun h => by
    obtain ⟨t, htS, -, hset, -⟩ := h
    exact ⟨t, htS, hset⟩) hYX (exists_odd_pow_eq_one_of_isPGroup (Or.inr rfl) hY5)

theorem exc5_of_rowOK_component (horb : A3Orbits G) {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hq : CFSG.IsQuasisimple ↥L) (hrow : RowOK (↥L ⧸ CFSG.pCore 2 ↥L)) : Exc5 X S L := by
  intro Y hYX _ _ hY5 hSY
  exact comm_eq_bot_of_component hq (le_cMod_of_rowOK hStd.sylow.2.1 hStd.sylowL hY5
    (le_normalizer_of_five horb hStd hYX hY5) hSY hrow)

theorem exc5_of_rowOK_block (horb : A3Orbits G) {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hL : IsShort2 L) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hrow : RowOK (↥L ⧸ CFSG.pCore 2 ↥L)) {d : ℕ}
    (hd : ((blockZ L).subgroupOf (blockU L)).index = 2 ^ d) (hd' : d = 3 ∨ d = 4 ∨ d = 6) :
    Exc5 X S L := by
  intro Y hYX _ _ hY5 hSY
  have hYN := le_normalizer_of_five horb hStd hYX hY5
  exact comm_eq_bot_of_block hL hq hd hd' hY5 hYN
    (le_cMod_of_rowOK hStd.sylow.2.1 hStd.sylowL hY5 hYN hSY hrow)

theorem card_dvd_factorial_index_of_simple {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    {U : Subgroup Γ} (hU : U ≠ ⊤) : Nat.card Γ ∣ U.index.factorial := by
  have h1 := Subgroup.index_normalCore_dvd_factorial_index U
  have h2 : U.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ Subgroup.normalCore_le U)) hU
  rwa [h2, Subgroup.index_bot] at h1

theorem card_eq_relIndex_mul_card {Γ : Type*} [Group Γ] {A B : Subgroup Γ} (h : A ≤ B) :
    Nat.card B = A.relIndex B * Nat.card A := by
  have := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_of_le_left h] at this
  exact this.symm

theorem noFiveIndex_alternating_five : NoFiveIndex ↥(alternatingGroup (Fin 5)) := by
  intro S₀ U hS hle b hb
  by_contra hb0
  have hcard : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [isSylowTwoOf_top_iff] at hS
  obtain ⟨hS2, hodd⟩ := hS
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hmul := Subgroup.card_mul_index S₀
  rw [hcard, hk] at hmul
  have hk5 : k ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 0 < S₀.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    nlinarith
  have hS4 : Nat.card S₀ = 4 := by
    interval_cases k <;> omega
  have hU := card_eq_relIndex_mul_card hle
  rw [hb, hS4] at hU
  have hUi := Subgroup.card_mul_index U
  rw [hU, hcard] at hUi
  have hb1 : b = 1 := by
    by_contra hne
    have h25 : 5 ^ 2 ∣ 5 ^ b := pow_dvd_pow 5 (by omega)
    have h60 : 5 ^ b ∣ 60 := ⟨4 * U.index, by rw [← hUi]; ring⟩
    have := h25.trans h60
    norm_num at this
  subst hb1
  have hidx : U.index = 3 := by
    norm_num at hUi
    omega
  have hUtop : U ≠ ⊤ := fun h => by rw [h, Subgroup.index_top] at hidx; omega
  have := card_dvd_factorial_index_of_simple hUtop
  rw [hcard, hidx] at this
  norm_num at this

theorem out5Pow_alternating_five : CFSG.Quasithin.H23Out.Out5Pow ↥(alternatingGroup (Fin 5)) :=
  CFSG.Quasithin.H23Out.Out5Pow.of_noFiveOut
    (CFSG.Quasithin.H23Out.NoFiveOut.of_card_outer_le_four
      ((Nat.le_of_dvd (by norm_num)
        (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (Or.inl rfl)).2).trans
        (by norm_num)))

theorem rowOK_alternating_five : RowOK ↥(alternatingGroup (Fin 5)) where
  center := alternatingGroup.center_eq_bot (by simp)
  out := out5Pow_alternating_five
  idx := noFiveIndex_alternating_five

theorem rowOK_of_isPSL_two_two_two {X : Type} [Group X] (h : IsPSL 2 2 2 X) : RowOK X := by
  obtain ⟨e⟩ := nonempty_equiv_alt5_of_isPSL_two_two_two h
  exact RowOK.of_mulEquiv e.symm rowOK_alternating_five

omit [Finite G] in
theorem isQuasisimple_of_isComponentOf {X L : Subgroup G} (hc : IsComponentOf L X) :
    CFSG.IsQuasisimple ↥L :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥L).1 hc.2.2

theorem exc5_of_isPSL_two_two_two (horb : A3Orbits G) {X S L : Subgroup G}
    (hStd : Std1521 X S L) (hc : IsComponentOf L X) (hL : IsPSL 2 2 2 ↥L) : Exc5 X S L :=
  exc5_of_rowOK_component horb hStd (isQuasisimple_of_isComponentOf hc)
    (RowOK.quot_pCore (isQuasisimple_of_isComponentOf hc) (rowOK_of_isPSL_two_two_two hL))

theorem exc5_of_isPSL_three_two_two (horb : A3Orbits G) {X S L : Subgroup G}
    (hStd : Std1521 X S L) (hc : IsComponentOf L X) (hL : IsPSL 3 2 2 ↥L) : Exc5 X S L :=
  exc5_of_rowOK_component horb hStd (isQuasisimple_of_isComponentOf hc)
    (RowOK.quot_pCore (isQuasisimple_of_isComponentOf hc) (rowOK_of_isPSL_three_two_two hL))

theorem exc5_of_isPSL_three_two_two_quot (horb : A3Orbits G) {X S L : Subgroup G}
    (hStd : Std1521 X S L) (hc : IsComponentOf L X)
    (hL : IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) : Exc5 X S L :=
  exc5_of_rowOK_component horb hStd (isQuasisimple_of_isComponentOf hc)
    (rowOK_of_isPSL_three_two_two hL)

theorem exc5_of_isPSp4_two_two (horb : A3Orbits G) {X S L : Subgroup G}
    (hStd : Std1521 X S L) (hc : IsComponentOf L X) (hL : IsPSp4 2 2 ↥L) : Exc5 X S L :=
  exc5_of_rowOK_component horb hStd (isQuasisimple_of_isComponentOf hc)
    (RowOK.quot_pCore (isQuasisimple_of_isComponentOf hc) (rowOK_of_isPSp4_two_two hL))

theorem rowOK_of_equiv_sl2_four {Q : Type} [Group Q] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) : RowOK Q := by
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega : 1 ≤ 2) (by simpa using hF)
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [CFSG.Quasithin.SL2Model.card_SL2, hF]
    norm_num
  obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 F hF hSL
  exact RowOK.of_mulEquiv (e.trans e5).symm rowOK_alternating_five

omit [Finite G] in
theorem index_blockZ_of_isLin2Type {L : Subgroup G} {n : ℕ} (h : IsLin2Type L n) :
    ((blockZ L).subgroupOf (blockU L)).index = 2 ^ (2 * n) := by
  obtain ⟨F, _, _, hF, α, hα, hαk, β, hβ, hβk, -⟩ := h
  rw [← hβk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hβ, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF,
    Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, ← pow_mul, mul_comm]

theorem exc5_of_isLin2Type_two (horb : A3Orbits G) {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hL : IsShort2 L) (h2 : IsLin2Type L 2) : Exc5 X S L := by
  have hd := index_blockZ_of_isLin2Type h2
  obtain ⟨F, _, _, hF, α, hα, hαk, -⟩ := h2
  have hF4 : Nat.card F = 4 := by
    rw [Nat.card_eq_fintype_card, hF]
    norm_num
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
    have hF4' : Nat.card F = 4 := hF4
    have : Finite F := Nat.finite_of_card_ne_zero (by omega)
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.SL2Model.card_SL2, hF4']
    norm_num
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    hL.2.2.2.1.resolve_right (by rw [hcard]; norm_num)
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  exact exc5_of_rowOK_block horb hStd hL hq (rowOK_of_equiv_sl2_four hF4 e) hd (Or.inr (Or.inl rfl))

theorem exc5_of_isAltType_five (horb : A3Orbits G) {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hth : ⁅L, thompsonJ S⁆ = L) (hblk : IsBlock2 X L) (h5 : IsAltType L 5) : Exc5 X S L :=
  fun Y hYX hYJ hYC hY5 hSY =>
    exc1521_blockA5_of_orbits horb hStd hth hblk h5 5 Y (Or.inr rfl) hYX hYJ hYC hY5 hSY

end CFSG.Quasithin.E9
