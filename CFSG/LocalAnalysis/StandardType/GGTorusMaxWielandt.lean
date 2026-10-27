module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_12_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_13_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_14_d
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_e
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_6_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.theorem_11_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_c_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_3_a_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_5_b
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

public section

namespace CFSG.StandardType.FrameRoute

open Multiplicative

section Pair

variable {A : Type} [Group A] {m : ℕ}

@[expose] noncomputable def tmPair (φ : A ≃* Multiplicative (Fin m → ZMod 3))
    (c : Fin m → ZMod 3) : A →* Multiplicative (ZMod 3) where
  toFun a := ofAdd (∑ k, c k * toAdd (φ a) k)
  map_one' := by simp
  map_mul' a b := by
    rw [← ofAdd_add, map_mul, toAdd_mul]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[expose] noncomputable def tmKer (φ : A ≃* Multiplicative (Fin m → ZMod 3))
    (c : Fin m → ZMod 3) : Subgroup A :=
  (tmPair φ c).ker

theorem mem_tmKer (φ : A ≃* Multiplicative (Fin m → ZMod 3)) (c : Fin m → ZMod 3) (a : A) :
    a ∈ tmKer φ c ↔ ∑ k, c k * toAdd (φ a) k = 0 := by
  rw [tmKer, MonoidHom.mem_ker]
  exact ofAdd_eq_one

end Pair

section Count

variable {m : ℕ}

private noncomputable def tmDot (s : Fin m → ZMod 3) : (Fin m → ZMod 3) →+ ZMod 3 where
  toFun c := ∑ k, c k * s k
  map_zero' := by simp
  map_add' c c' := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem tmDot_card_ker {s : Fin m → ZMod 3} (hs : s ≠ 0) :
    Nat.card {c : Fin m → ZMod 3 // ∑ k, c k * s k = 0} = 3 ^ (m - 1) := by
  classical
  obtain ⟨k₀, hk₀⟩ : ∃ k, s k ≠ 0 := by
    by_contra h
    exact hs (funext fun k => by_contra fun hk => h ⟨k, hk⟩)
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => by subst h; exact k₀.elim0
  have hsurj : Function.Surjective (tmDot s) := fun t => by
    refine ⟨(Pi.single k₀ (t * (s k₀)⁻¹) : Fin m → ZMod 3), ?_⟩
    change ∑ k, (Pi.single k₀ (t * (s k₀)⁻¹) : Fin m → ZMod 3) k * s k = t
    rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_mul])
      (fun h => (h (Finset.mem_univ _)).elim), Pi.single_eq_same, mul_assoc,
      inv_mul_cancel₀ hk₀, mul_one]
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective hsurj
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at hcard
  have h1 : Nat.card {c : Fin m → ZMod 3 // ∑ k, c k * s k = 0} = Nat.card (tmDot s).ker := rfl
  rw [h1]
  have h3 : 3 ^ m = 3 ^ (m - 1) * 3 := by rw [← pow_succ, Nat.sub_add_cancel hm]
  omega

end Count

section Wielandt

variable {A J : Type} [Group A] [Finite A] [Group J] [Finite J] [MulDistribMulAction A J] {m : ℕ}

variable (J) in
@[expose] noncomputable def tmFixCard (B : Subgroup A) : ℕ :=
  letI : MulDistribMulAction B J := MulDistribMulAction.compHom J B.subtype
  Nat.card (fixedPointSubgroup B J)

theorem tmKer_zero (φ : A ≃* Multiplicative (Fin m → ZMod 3)) : tmKer φ 0 = ⊤ := by
  ext a
  simp [mem_tmKer]

theorem tmKer_card (φ : A ≃* Multiplicative (Fin m → ZMod 3)) {c : Fin m → ZMod 3} (hc : c ≠ 0) :
    Nat.card (tmKer φ c) = 3 ^ (m - 1) := by
  rw [← tmDot_card_ker hc]
  refine Nat.card_congr ((Equiv.subtypeEquiv (φ.toEquiv.trans Multiplicative.toAdd) fun a => ?_))
  rw [mem_tmKer]
  change (∑ k, c k * toAdd (φ a) k = 0) ↔ ∑ k, toAdd (φ a) k * c k = 0
  simp only [mul_comm]

theorem tmFixCard_bot : tmFixCard J (⊥ : Subgroup A) = Nat.card J := by
  letI : MulDistribMulAction (⊥ : Subgroup A) J :=
    MulDistribMulAction.compHom J (⊥ : Subgroup A).subtype
  have h : fixedPointSubgroup (⊥ : Subgroup A) J = ⊤ := by
    ext x
    simp only [fixedPointSubgroup, FixedPoints.mem_subgroup, Subgroup.mem_top, iff_true]
    rintro ⟨b, hb⟩
    rw [Subgroup.mem_bot] at hb
    subst hb
    exact one_smul A x
  rw [tmFixCard, h, Subgroup.card_top]

open Classical in
private theorem tmKer_count (φ : A ≃* Multiplicative (Fin m → ZMod 3)) (hm : 1 ≤ m) (a : A) :
    (∑ c : Fin m → ZMod 3, if a ∈ tmKer φ c then 1 else 0) =
      if a = 1 then 2 * 3 ^ (m - 1) + 3 ^ (m - 1) else 3 ^ (m - 1) := by
  classical
  rw [Finset.sum_boole, Nat.cast_id]
  have h3 : 3 ^ m = 2 * 3 ^ (m - 1) + 3 ^ (m - 1) := by
    rw [← add_one_mul, show 2 + 1 = 3 from rfl, ← pow_succ', Nat.sub_add_cancel hm]
  by_cases ha : a = 1
  · subst ha
    rw [if_pos rfl, ← h3, Finset.filter_true_of_mem fun c _ => (tmKer φ c).one_mem,
      Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · rw [if_neg ha]
    have hs : toAdd (φ a) ≠ 0 := fun h =>
      ha (φ.injective (by rw [map_one]; exact toAdd_eq_zero.mp h))
    rw [← tmDot_card_ker hs, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext c
    simp [mem_tmKer]

theorem tmWielandt_card_sq (φ : A ≃* Multiplicative (Fin m → ZMod 3)) (hm : 1 ≤ m)
    (hcop : Nat.Coprime (Nat.card J) (Nat.card A)) (hsolv : Group.IsSolvable J)
    (hfix : tmFixCard J (⊤ : Subgroup A) = 1) :
    Nat.card J ^ 2 = ∏ c ∈ Finset.univ.filter (fun c : Fin m → ZMod 3 => c ≠ 0),
      tmFixCard J (tmKer φ c) := by
  classical
  let B : Option (Option (Fin m → ZMod 3)) → Subgroup A
    | none => ⊥
    | some none => ⊤
    | some (some c) => tmKer φ c
  let mc : Option (Option (Fin m → ZMod 3)) → ℕ
    | some (some _) => 1
    | _ => 0
  let nc : Option (Option (Fin m → ZMod 3)) → ℕ
    | none => 2 * 3 ^ (m - 1)
    | some none => 3 ^ (m - 1)
    | some (some _) => 0
  have hcoeff : ∀ a : A, (∑ i, if a ∈ B i then mc i else 0) = ∑ i, if a ∈ B i then nc i else 0 := by
    intro a
    simp only [Fintype.sum_option, B, mc, nc, ite_self, zero_add, Subgroup.mem_top, if_true,
      Subgroup.mem_bot, Finset.sum_const_zero, add_zero]
    rw [tmKer_count φ hm a]
    by_cases ha : a = 1 <;> simp [ha]
  have hW := CFSG.Wielandt.fixedPointSubgroup_product_card_eq_of_coeff_sum_eq hcop hsolv B mc nc
    hcoeff
  change (∏ i, tmFixCard J (B i) ^ (mc i * Nat.card (B i))) =
    ∏ i, tmFixCard J (B i) ^ (nc i * Nat.card (B i)) at hW
  simp only [Fintype.prod_option, B, mc, nc, zero_mul, pow_zero, one_mul, Finset.prod_const_one,
    mul_one, hfix, one_pow, tmFixCard_bot, Subgroup.card_bot] at hW
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun c : Fin m → ZMod 3 => c ≠ 0)] at hW
  have hzero : (Finset.univ.filter fun c : Fin m → ZMod 3 => ¬ c ≠ 0) = {0} := by
    ext c
    simp
  rw [hzero, Finset.prod_singleton, tmKer_zero, hfix, one_pow, mul_one] at hW
  rw [Finset.prod_congr rfl fun c hc => by
    rw [tmKer_card φ (Finset.mem_filter.mp hc).2], Finset.prod_pow] at hW
  have hpos : 3 ^ (m - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : (∏ c ∈ Finset.univ.filter (fun c : Fin m → ZMod 3 => c ≠ 0),
      tmFixCard J (tmKer φ c)) ^ 3 ^ (m - 1) = (Nat.card J ^ 2) ^ 3 ^ (m - 1) := by
    rw [hW, ← pow_mul]
  exact (Nat.pow_left_injective hpos h2).symm

theorem tmFixCard_ker_ge_four (φ : A ≃* Multiplicative (Fin m → ZMod 3)) (hm : 1 ≤ m)
    (hcop : Nat.Coprime (Nat.card J) (Nat.card A)) (hfix : tmFixCard J (⊤ : Subgroup A) = 1)
    {c : Fin m → ZMod 3} (h1 : tmFixCard J (tmKer φ c) ≠ 1) : 4 ≤ tmFixCard J (tmKer φ c) := by
  classical
  letI : MulDistribMulAction (tmKer φ c) J := MulDistribMulAction.compHom J (tmKer φ c).subtype
  letI : MulDistribMulAction (⊤ : Subgroup A) J :=
    MulDistribMulAction.compHom J (⊤ : Subgroup A).subtype
  set C := fixedPointSubgroup (tmKer φ c) J with hC
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => φ.injective (by
    rw [map_mul, map_mul, mul_comm])
  have hcardA : Nat.card A = 3 ^ m := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have h3J : ¬ 3 ∣ Nat.card J := fun h => by
    have h3A : 3 ∣ Nat.card A := hcardA ▸ dvd_pow_self 3 (by omega)
    have h31 := Nat.dvd_gcd h h3A
    rw [Nat.Coprime.gcd_eq_one hcop] at h31
    omega
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hne1 : Nat.card C ≠ 1 := h1
  have hne3 : Nat.card C ≠ 3 := fun h => h3J (h ▸ Subgroup.card_subgroup_dvd_card C)
  have hne2 : Nat.card C ≠ 2 := by
    intro h2
    obtain ⟨x, hxC, hx1⟩ : ∃ x ∈ C, x ≠ 1 := by
      by_contra hno
      push Not at hno
      have : C = ⊥ := (Subgroup.eq_bot_iff_forall C).mpr hno
      rw [this, Subgroup.card_bot] at h2
      omega
    have hinv : ∀ a : A, a • x ∈ C := fun a => by
      rw [hC, fixedPointSubgroup, FixedPoints.mem_subgroup] at hxC ⊢
      intro k
      change (k : A) • a • x = a • x
      rw [smul_smul, hcomm, ← smul_smul]
      exact congrArg (a • ·) (hxC k)
    have hfixA : ∀ a : A, a • x = x := by
      intro a
      by_contra hax
      have hax1 : a • x ≠ 1 := fun h => hx1 (by
        have h' := congrArg (fun y => a⁻¹ • y) h
        simpa using h')
      have hsub : ({1, x, a • x} : Set J) ⊆ C := by
        intro y hy
        rcases hy with rfl | rfl | rfl
        · exact C.one_mem
        · exact hxC
        · exact hinv a
      have h3 : ({1, x, a • x} : Set J).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by
            rintro (h | h)
            · exact hx1 h.symm
            · exact hax1 h.symm) (Set.toFinite _), Set.ncard_pair (Ne.symm hax)]
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [h3, ← Nat.card_coe_set_eq] at hle
      change 3 ≤ Nat.card C at hle
      omega
    have hxA : x ∈ fixedPointSubgroup (⊤ : Subgroup A) J := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      exact fun b => hfixA b
    have htop : fixedPointSubgroup (⊤ : Subgroup A) J = ⊥ := by
      rw [← Subgroup.card_eq_one]
      exact hfix
    rw [htop, Subgroup.mem_bot] at hxA
    exact hx1 hxA
  change 4 ≤ Nat.card C
  omega

theorem tmWielandt_four_pow_le (φ : A ≃* Multiplicative (Fin m → ZMod 3)) (hm : 1 ≤ m)
    (hcop : Nat.Coprime (Nat.card J) (Nat.card A)) (hsolv : Group.IsSolvable J)
    (hfix : tmFixCard J (⊤ : Subgroup A) = 1) :
    4 ^ (Finset.univ.filter fun c : Fin m → ZMod 3 =>
      c ≠ 0 ∧ tmFixCard J (tmKer φ c) ≠ 1).card ≤ Nat.card J ^ 2 := by
  classical
  rw [tmWielandt_card_sq φ hm hcop hsolv hfix]
  calc 4 ^ (Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧ tmFixCard J (tmKer φ c) ≠ 1).card
      ≤ ∏ c ∈ Finset.univ.filter (fun c : Fin m → ZMod 3 => c ≠ 0 ∧ tmFixCard J (tmKer φ c) ≠ 1),
          tmFixCard J (tmKer φ c) :=
        Finset.pow_card_le_prod _ _ _ fun c hc =>
          tmFixCard_ker_ge_four φ hm hcop hfix (Finset.mem_filter.mp hc).2.2
    _ ≤ ∏ c ∈ Finset.univ.filter (fun c : Fin m → ZMod 3 => c ≠ 0), tmFixCard J (tmKer φ c) :=
        Finset.prod_le_prod_of_subset_of_one_le' (fun c hc => by
          simp only [Finset.mem_filter] at hc ⊢; exact ⟨hc.1, hc.2.1⟩)
          fun c _ _ => Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')

end Wielandt

end CFSG.StandardType.FrameRoute

end
