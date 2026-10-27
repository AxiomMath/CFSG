module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.RankThree.PartTwo.KFacts.KS12Moves
import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Equiv

theorem pow_three_eq_one_of_center_card_three {X Y : Type*} [Group X] [Group Y]
    (hZ : Nat.card (Subgroup.center X) = 3) (e : X ⧸ Subgroup.center X ≃* Y)
    (hY : ∀ s : Y, (∃ k : ℕ, s ^ 3 ^ k = 1) → s ^ 3 = 1 ∧ ∃ g : Y, g * s * g⁻¹ = s⁻¹)
    (x : X) (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) : x ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hx
  set s := e (x : X ⧸ Subgroup.center X) with hs
  have hsk : s ^ 3 ^ k = 1 := by
    rw [hs, ← map_pow, ← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one, map_one]
  obtain ⟨hs3, g, hg⟩ := hY s ⟨k, hsk⟩
  have hx3Z : x ^ 3 ∈ Subgroup.center X := by
    have h1 : ((x ^ 3 : X) : X ⧸ Subgroup.center X) = 1 := by
      apply e.injective
      rw [map_one, QuotientGroup.mk_pow, map_pow, ← hs, hs3]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (e.symm g)
  have hconj : ((g' * x * g'⁻¹ : X) : X ⧸ Subgroup.center X) =
      ((x⁻¹ : X) : X ⧸ Subgroup.center X) := by
    apply e.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hg', MulEquiv.apply_symm_apply, ← hs, hg, QuotientGroup.mk_inv, map_inv, ← hs]
  have hz : x * (g' * x * g'⁻¹) ∈ Subgroup.center X := by
    have h1 := QuotientGroup.eq.mp hconj.symm
    rwa [inv_inv] at h1
  set z := x * (g' * x * g'⁻¹) with hzdef
  have hz3 : z ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center X))
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hgx : g' * x * g'⁻¹ = x⁻¹ * z := by rw [hzdef]; group
  have h1 : g' * x ^ 3 * g'⁻¹ = x ^ 3 := by
    rw [Subgroup.mem_center_iff.mp hx3Z g', mul_inv_cancel_right]
  have h2 : g' * x ^ 3 * g'⁻¹ = (x ^ 3)⁻¹ := by
    have hcz : Commute x⁻¹ z := Subgroup.mem_center_iff.mp hz x⁻¹
    rw [← conj_pow, hgx, hcz.mul_pow, hz3, mul_one, inv_pow]
  have h6 : x ^ 6 = 1 := by
    have h3 : x ^ 3 = (x ^ 3)⁻¹ := h1.symm.trans h2
    have : x ^ 3 * x ^ 3 = 1 := by
      calc x ^ 3 * x ^ 3 = x ^ 3 * (x ^ 3)⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel _
    rw [← pow_add] at this
    exact this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hj6 : 3 ^ j ∣ 6 := hj ▸ orderOf_dvd_of_pow_eq_one h6
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega)).trans hj6
    norm_num at this
  have hd : orderOf x ∣ 3 := by
    rw [hj]
    exact (pow_dvd_pow 3 hj1).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp hd

theorem exists_inv_conj_of_elemNine {Y : Type*} [Group Y] [Finite Y] {E : Subgroup Y}
    (hE : Nat.card E = 9) (hfac : (Nat.card Y).factorization 3 = 2) {t : Y}
    (ht : ∀ u ∈ E, t * u * t⁻¹ = u⁻¹) (s : Y) (hs : ∃ k : ℕ, s ^ 3 ^ k = 1) :
    ∃ g : Y, g * s * g⁻¹ = s⁻¹ := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hQ : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨h, hh⟩ := KS14.exists_conj_mem_of_card_nine hE hfac hQ
  have hu := ht _ (hh s (Subgroup.mem_zpowers s))
  refine ⟨h * t * h⁻¹, ?_⟩
  calc h * t * h⁻¹ * s * (h * t * h⁻¹)⁻¹ = h * (t * (h⁻¹ * s * h) * t⁻¹) * h⁻¹ := by group
    _ = s⁻¹ := by rw [hu]; group

@[expose] def tSix : Perm (Fin 6) := K412.swSix 1 2 * K412.swSix 4 5

theorem tSix_spec : Perm.sign tSix = 1 ∧
    ∀ i j : Fin 3, tSix * K412.sixF i j * tSix⁻¹ = (K412.sixF i j)⁻¹ := by
  decide +kernel

theorem factorization_alternating_seven :
    (Nat.card (alternatingGroup (Fin 7))).factorization 3 = 2 := by
  rw [KS14.card_alternatingGroup_five_seven_ten.2.1, show (2520 : ℕ) = 3 ^ 2 * 280 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
      Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem alternatingGroup_six_threeElements (s : alternatingGroup (Fin 6))
    (hs : ∃ k : ℕ, s ^ 3 ^ k = 1) : s ^ 3 = 1 ∧ ∃ g, g * s * g⁻¹ = s⁻¹ := by
  set E := K412.eSix.subgroupOf (alternatingGroup (Fin 6)) with hEdef
  have hE : Nat.card E = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe K412.eSix_le_alternatingGroup).toEquiv,
      K412.card_eSix]
  have hfac := Sec4.Item434Alt.factorization_alternating_six
  refine ⟨KS14.pow_three_eq_one_of_elemNine hE hfac (fun u hu => ?_) s hs, ?_⟩
  · obtain ⟨i, j, hij⟩ := Subgroup.mem_subgroupOf.mp hu
    exact Subtype.ext (by rw [Subgroup.coe_pow, hij, K412.sixF_pow_three, Subgroup.coe_one])
  · refine exists_inv_conj_of_elemNine (t := ⟨tSix, tSix_spec.1⟩) hE hfac (fun u hu => ?_) s hs
    obtain ⟨i, j, hij⟩ := Subgroup.mem_subgroupOf.mp hu
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hij]
      exact tSix_spec.2 i j)

theorem alternatingGroup_seven_threeElements (s : alternatingGroup (Fin 7))
    (hs : ∃ k : ℕ, s ^ 3 ^ k = 1) : s ^ 3 = 1 ∧ ∃ g, g * s * g⁻¹ = s⁻¹ := by
  refine ⟨(KS14.a7_facts _ ⟨MulEquiv.refl _⟩).2.2.2.1 s hs, ?_⟩
  refine exists_inv_conj_of_elemNine (t := ⟨KP2.tInv, KP2.tInv_mem_alternatingGroup⟩)
    KS14.card_eNine_subgroupOf factorization_alternating_seven (fun u hu => ?_) s hs
  exact Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    exact KP2.tInv_conj_eq_inv (Subgroup.mem_subgroupOf.mp hu))

theorem m22_threeElements
    (s : Blueprint.NativeSporadic.M22) (hs : ∃ k : ℕ, s ^ 3 ^ k = 1) :
    s ^ 3 = 1 ∧ ∃ g, g * s * g⁻¹ = s⁻¹ := by
  have hs3 := (KS14.m22_ks18Facts _ ⟨MulEquiv.refl _⟩).2.2.2.1 s hs
  refine ⟨hs3, ?_⟩
  by_cases hs1 : s = 1
  · exact ⟨1, by rw [hs1]; group⟩
  have ho : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have ho' : orderOf s⁻¹ = 3 := by rw [orderOf_inv, ho]
  obtain ⟨c, hc⟩ := isConj_iff.mp (KP4.m22_isConj_of_orderOf ⟨MulEquiv.refl _⟩ ho ho')
  exact ⟨c, hc⟩

theorem pow_three_eq_one_of_isTripleCover
    {X : Type*} [Group X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X Blueprint.NativeSporadic.M22)
    (x : X) (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) : x ^ 3 = 1 := by
  rcases hX with ⟨hZ, ⟨e⟩⟩ | ⟨hZ, ⟨e⟩⟩ | ⟨hZ, ⟨e⟩⟩
  · exact pow_three_eq_one_of_center_card_three hZ e alternatingGroup_six_threeElements x hx
  · exact pow_three_eq_one_of_center_card_three hZ e alternatingGroup_seven_threeElements x hx
  · exact pow_three_eq_one_of_center_card_three hZ e m22_threeElements x hx

theorem orderOf_ne_nine_of_isTripleCover
    {X : Type*} [Group X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X Blueprint.NativeSporadic.M22)
    (v : X) : orderOf v ≠ 9 := by
  intro hv
  have h9 : v ^ 3 ^ 2 = 1 := by rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hv, pow_orderOf_eq_one]
  have h3 := pow_three_eq_one_of_isTripleCover hX v ⟨2, h9⟩
  have h1 := orderOf_dvd_of_pow_eq_one h3
  rw [hv] at h1
  norm_num at h1

theorem exists_card_eq_of_isTripleCover {X : Type*} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X Blueprint.NativeSporadic.M22) :
    ∃ m : ℕ, ¬ 3 ∣ m ∧ Nat.card X = 27 * m := by
  rcases hX with h | h | h
  · refine ⟨40, by norm_num, ?_⟩
    rw [card_of_isTripleCover h, K412.card_alternating_six_seven.1]
  · refine ⟨280, by norm_num, ?_⟩
    rw [card_of_isTripleCover h, K412.card_alternating_six_seven.2]
  · refine ⟨49280, by norm_num, ?_⟩
    rw [card_of_isTripleCover h, KS14.card_nativeM22]

end CFSG.RankThree.PartTwo.KFacts
