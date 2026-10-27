module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowBalance
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CSeitzRest

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

theorem gf2_cases (x : GaloisField 2 1) : x = 0 ∨ x = 1 := by
  set e := GaloisField.equivZmodP 2 with he
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h (e x) with h0 | h1
  · left
    rw [← e.symm_apply_apply x, h0, map_zero]
  · right
    rw [← e.symm_apply_apply x, h1, map_one]

theorem eq_one_of_irreducible_gf2 {b c : GaloisField 2 1}
    (h : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  have h11 : (1 : GaloisField 2 1) + 1 = 0 := by
    have := CharP.cast_eq_zero (GaloisField 2 1) 2
    rw [Nat.cast_ofNat] at this
    rw [← this]
    norm_num
  have hc : c = 1 := by
    rcases gf2_cases c with hc | hc
    · exact absurd (by rw [hc]; ring) (h 0)
    · exact hc
  have hb : b = 1 := by
    rcases gf2_cases b with hb | hb
    · exfalso
      apply h 1
      rw [hb, hc]
      simpa using h11
    · exact hb
  exact ⟨hb, hc⟩

section Certs

theorem rowSOf148_projSL_of_crossChar {r p e : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) (hp3 : p ≠ 3)
    (hv : (TauCeti.LieTypeIndex.A r ⟨p, e, hp.out, he⟩).Valid) :
    RowSOf148 (projSL (r + 1) (GaloisField p e)) := by
  haveI : Fact (Nat.Prime (⟨p, e, hp.out, he⟩ : TauCeti.PrimePower).p) := hp
  exact rowSOf148_of_crossChar ⟨.A r ⟨p, e, hp.out, he⟩, hv⟩
    (CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL r ⟨p, e, hp.out, he⟩ hv).symm
    (by rw [TauCeti.LieTypeIndex.characteristic_A]; exact hp3)

theorem rowSOf148_projSU_of_crossChar {r p e : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) (hp3 : p ≠ 3)
    (hv : (TauCeti.LieTypeIndex.twistedA r ⟨p, e, hp.out, he⟩).Valid) :
    RowSOf148 (projSU (r + 1) p e) := by
  haveI : Fact (Nat.Prime (⟨p, e, hp.out, he⟩ : TauCeti.PrimePower).p) := hp
  exact rowSOf148_of_crossChar ⟨.twistedA r ⟨p, e, hp.out, he⟩, hv⟩
    (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU r ⟨p, e, hp.out, he⟩ hv).symm
    (by rw [TauCeti.LieTypeIndex.characteristic_twistedA]; exact hp3)

theorem rowSOf148_projSp_two_even {e : ℕ} (he : 1 ≤ e)
    (hv : (TauCeti.LieTypeIndex.B 2 ⟨2, e, Nat.prime_two, he⟩).Valid) :
    RowSOf148 (projSp 2 (GaloisField 2 e)) := by
  haveI : Fact (Nat.Prime (⟨2, e, Nat.prime_two, he⟩ : TauCeti.PrimePower).p) :=
    ⟨Nat.prime_two⟩
  exact rowSOf148_of_crossChar ⟨.B 2 ⟨2, e, Nat.prime_two, he⟩, hv⟩
    (CFSG.RankThree.PartTwo.Sec4.Census.typeB2GroupEquivProjSp ⟨2, e, Nat.prime_two, he⟩ hv).symm
    (by rw [TauCeti.LieTypeIndex.characteristic_B]; norm_num)

theorem rowSOf148_projSp_even {r e : ℕ} (hr : 3 ≤ r) (he : 1 ≤ e)
    (hv : (TauCeti.LieTypeIndex.B r ⟨2, e, Nat.prime_two, he⟩).Valid) :
    RowSOf148 (projSp r (GaloisField 2 e)) := by
  haveI : Fact (Nat.Prime (⟨2, e, Nat.prime_two, he⟩ : TauCeti.PrimePower).p) :=
    ⟨Nat.prime_two⟩
  exact rowSOf148_of_crossChar ⟨.B r ⟨2, e, Nat.prime_two, he⟩, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivProjSp r
      ⟨2, e, Nat.prime_two, he⟩ hv rfl hr).symm
    (by rw [TauCeti.LieTypeIndex.characteristic_B]; norm_num)

theorem seitz82Rest_holds : Seitz82Rest where
  four_SL p _ hp hp3 := by
    refine rowSOf148_projSL_of_crossChar (r := 3) le_rfl (by omega) ?_
    simp [TauCeti.PrimePower.card_def]
    omega
  four_SU p _ hp hp3 := by
    refine rowSOf148_projSU_of_crossChar (r := 3) le_rfl (by omega) ?_
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp
  seven_SL3 n hn h3 := by
    have h8 : 8 ≤ 2 ^ n := by
      obtain ⟨k, rfl⟩ := h3
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine rowSOf148_projSL_of_crossChar (r := 2) hn (by norm_num) ?_
    simp [TauCeti.PrimePower.card_def]
    omega
  seven_SU3 n hn h3 := by
    have h8 : 8 ≤ 2 ^ n := by
      obtain ⟨k, rfl⟩ := h3
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine rowSOf148_projSU_of_crossChar (r := 2) hn (by norm_num) ?_
    simp [TauCeti.PrimePower.card_def]
    omega
  seven_Sp4 n hn h3 := by
    have h8 : 8 ≤ 2 ^ n := by
      obtain ⟨k, rfl⟩ := h3
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine rowSOf148_projSp_two_even hn ?_
    simp [TauCeti.PrimePower.card_def]
    omega
  seven_SU4 n hn := by
    refine rowSOf148_projSU_of_crossChar (r := 3) hn (by norm_num) ?_
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp
  seven_G2 q hq2 _ hq := rowSOf148_of_crossChar ⟨.G2 q, hq⟩ (MulEquiv.refl _)
    (by rw [TauCeti.LieTypeIndex.characteristic_G2, hq2]; norm_num)
  seven_D4 q hq hq2 := rowSOf148_of_crossChar ⟨.trialityD4 q, hq⟩ (MulEquiv.refl _)
    (by rw [TauCeti.LieTypeIndex.characteristic_trialityD4, hq2]; norm_num)
  seven_F4 m hm := rowSOf148_of_crossChar ⟨.reeF4 m, hm⟩ (MulEquiv.refl _)
    (by rw [TauCeti.LieTypeIndex.characteristic_reeF4]; norm_num)
  eight_SU5 := rowSOf148_projSU_of_crossChar (r := 4) (e := 1) le_rfl (by norm_num) (by simp)
  eight_SL6 := rowSOf148_projSL_of_crossChar (r := 5) (e := 1) le_rfl (by norm_num) (by simp)
  eight_SU6 := rowSOf148_projSU_of_crossChar (r := 5) (e := 1) le_rfl (by norm_num) (by simp)
  eight_SL7 := rowSOf148_projSL_of_crossChar (r := 6) (e := 1) le_rfl (by norm_num) (by simp)
  eight_Sp6 := rowSOf148_projSp_even (r := 3) (e := 1) le_rfl le_rfl (by simp)
  eight_Sp8 := rowSOf148_projSp_even (r := 4) (e := 1) (by norm_num) le_rfl (by simp)
  eight_OmegaPlus := by
    haveI : Fact (Nat.Prime (⟨2, 1, Nat.prime_two, Nat.one_pos⟩ : TauCeti.PrimePower).p) :=
      ⟨Nat.prime_two⟩
    have hv : (TauCeti.LieTypeIndex.D 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by simp
    exact rowSOf148_of_crossChar ⟨.D 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩, hv⟩
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivProjOmegaPlus 4
        ⟨2, 1, Nat.prime_two, Nat.one_pos⟩ hv rfl).symm
      (by rw [TauCeti.LieTypeIndex.characteristic_D]; norm_num)
  eight_OmegaMinus b c hbc := by
    have hv : (TauCeti.LieTypeIndex.twistedD 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by simp
    obtain ⟨b', c', hbc', ⟨g⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.bridgeOmega8MinusTwo ⟨2, 1, Nat.prime_two, Nat.one_pos⟩ hv rfl rfl
    obtain ⟨hb, hc⟩ := eq_one_of_irreducible_gf2 hbc
    obtain ⟨hb', hc'⟩ := eq_one_of_irreducible_gf2 hbc'
    subst hb hc
    rw [hb', hc'] at g
    exact rowSOf148_of_crossChar ⟨.twistedD 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩, hv⟩ g.symm
      (by rw [TauCeti.LieTypeIndex.characteristic_twistedD]; norm_num)
  eight_SL4 := rowSOf148_projSL_of_crossChar (r := 3) (e := 2) (by norm_num) (by norm_num)
    (by simp)
  eight_Sp6_4 := rowSOf148_projSp_even (r := 3) (e := 2) le_rfl (by norm_num) (by simp)
  eight_SU5_4 := rowSOf148_projSU_of_crossChar (r := 4) (e := 2) (by norm_num) (by norm_num)
    (by simp)
  eight_SU5_8 := rowSOf148_projSU_of_crossChar (r := 4) (e := 3) (by norm_num) (by norm_num)
    (by simp)
  eight_F4 := rowSOf148_of_crossChar CFSG.Assembly.RankThreeEven.f4TwoIndex (MulEquiv.refl _)
    (by simp [CFSG.Assembly.RankThreeEven.f4TwoIndex, CFSG.Assembly.RankThreeEven.primePowerTwo])

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
