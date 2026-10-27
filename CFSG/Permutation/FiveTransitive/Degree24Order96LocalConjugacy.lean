module

public import CFSG.Permutation.FiveTransitive.Degree24PrimeSupportIncidence

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem eq_one_or_eq_or_eq_inv_of_card_eq_three
    (T : Type) [Group T] [Fintype T]
    (hTcard : Nat.card T = 3)
    (v : T) (hvOrder : orderOf v = 3)
    (w : T) :
    w = 1 ∨ w = v ∨ w = v⁻¹ := by
  classical
  have hvNe : v ≠ 1 := by
    intro hv
    rw [hv, orderOf_one] at hvOrder
    norm_num at hvOrder
  have hvInvNe : v⁻¹ ≠ 1 := by
    simpa only [inv_ne_one] using hvNe
  have hvNeInv : v ≠ v⁻¹ := by
    intro hv
    have hvSquare : v ^ 2 = 1 := by
      calc
        v ^ 2 = v * v := pow_two v
        _ = v⁻¹ * v := congrArg (fun z => z * v) hv
        _ = 1 := inv_mul_cancel v
    have hOrderDvd : orderOf v ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hvSquare
    rw [hvOrder] at hOrderDvd
    norm_num at hOrderDvd
  let A : Finset T := {1, v, v⁻¹}
  have hAcard : A.card = 3 := by
    have honeNeV : 1 ≠ v := hvNe.symm
    have honeNeInv : 1 ≠ v⁻¹ := hvInvNe.symm
    change ({1, v, v⁻¹} : Finset T).card = 3
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · norm_num
      · simpa only [Finset.mem_singleton] using hvNeInv
    · simp only [Finset.mem_insert, Finset.mem_singleton,
        not_or]
      exact ⟨honeNeV, honeNeInv⟩
  have hUnivCard :
      (Finset.univ : Finset T).card = 3 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      hTcard]
  have hAeq : A = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.subset_univ A
    · rw [hAcard, hUnivCard]
  have hwA : w ∈ A := by
    rw [hAeq]
    exact Finset.mem_univ w
  simpa only [A, Finset.mem_insert,
    Finset.mem_singleton, or_false] using hwA

theorem order96_orderThree_elements_conjugate_or_inverse
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (s : Set X)
    (hHcard : Nat.card (fixingSubgroup P s) = 96)
    (u v : fixingSubgroup P s)
    (hu : orderOf u = 3) (hv : orderOf v = 3) :
    (∃ q : fixingSubgroup P s,
        q * u * q⁻¹ = v) ∨
      (∃ q : fixingSubgroup P s,
        q * u * q⁻¹ = v⁻¹) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let Ru : Subgroup H := Subgroup.zpowers u
  let Rv : Subgroup H := Subgroup.zpowers v
  have hRuCard : Nat.card Ru = 3 := by
    rw [Nat.card_zpowers, hu]
  have hRvCard : Nat.card Rv = 3 := by
    rw [Nat.card_zpowers, hv]
  have hRuP : IsPGroup 3 Ru := by
    apply IsPGroup.of_card (n := 1)
    rw [hRuCard]
    norm_num
  have hRvP : IsPGroup 3 Rv := by
    apply IsPGroup.of_card (n := 1)
    rw [hRvCard]
    norm_num
  obtain ⟨S, hRuS⟩ := hRuP.exists_le_sylow
  obtain ⟨T, hRvT⟩ := hRvP.exists_le_sylow
  have hScard : Nat.card S = 3 :=
    sylow_card_eq_prime_of_card_eq_prime_mul
      H 3 32 (by norm_num) (by norm_num)
        (by simpa only [H] using hHcard) S
  have hTcard : Nat.card T = 3 :=
    sylow_card_eq_prime_of_card_eq_prime_mul
      H 3 32 (by norm_num) (by norm_num)
        (by simpa only [H] using hHcard) T
  have hRuS' : Ru = (S : Subgroup H) := by
    apply Subgroup.eq_of_le_of_card_ge hRuS
    rw [hRuCard, hScard]
  have hRvT' : Rv = (T : Subgroup H) := by
    apply Subgroup.eq_of_le_of_card_ge hRvT
    rw [hRvCard, hTcard]
  obtain ⟨q, hq⟩ := exists_smul_eq H S T
  let uqH : H := MulAut.conj q u
  have huqT : uqH ∈ (T : Subgroup H) := by
    rw [← hq]
    refine ⟨u, ?_, rfl⟩
    rw [← hRuS']
    exact Subgroup.mem_zpowers u
  let uq : T := ⟨uqH, huqT⟩
  have huqNe : uq ≠ 1 := by
    intro huqOne
    have huqHOne : uqH = 1 :=
      congrArg Subtype.val huqOne
    have huOne : u = 1 := by
      apply (MulAut.conj q).injective
      simpa only [map_one, uqH] using huqHOne
    rw [huOne, orderOf_one] at hu
    norm_num at hu
  let vT : T :=
    ⟨v, by
      have hvRv : v ∈ Rv :=
        Subgroup.mem_zpowers v
      rw [hRvT'] at hvRv
      exact hvRv⟩
  have hvTOrder : orderOf vT = 3 := by
    calc
      orderOf vT = orderOf (vT : H) :=
        (Subgroup.orderOf_coe vT).symm
      _ = orderOf v := by
        rfl
      _ = 3 := hv
  rcases
      eq_one_or_eq_or_eq_inv_of_card_eq_three
        T hTcard vT hvTOrder uq with
    huqOne | huqEq | huqEq
  · exact (huqNe huqOne).elim
  · left
    refine ⟨q, ?_⟩
    exact congrArg Subtype.val huqEq
  · right
    refine ⟨q, ?_⟩
    exact congrArg Subtype.val huqEq

end FiveTransitive.Degree24

end CFSG
