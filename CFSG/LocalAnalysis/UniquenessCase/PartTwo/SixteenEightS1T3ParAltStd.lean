module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParAltSyl
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Equiv Nat

private theorem s16t3_alt_four_mul_div_add_mod (n : ℕ) :
    4 * (n / 4) + n % 4 = n :=
  Nat.div_add_mod n 4

private theorem s16t3_alt_eq_four_mul_div_add_mod (n : ℕ) :
    n = 4 * (n / 4) + n % 4 :=
  (s16t3_alt_four_mul_div_add_mod n).symm

private theorem s16t3_alt_div_mul_add_mod (n : ℕ) :
    n / 4 * 4 + n % 4 = n := by
  rw [Nat.mul_comm]
  exact s16t3_alt_four_mul_div_add_mod n

private def s16t3_alt_f (n : ℕ) (i : Fin n) : Fin (n / 4 + 1) :=
  ⟨(i : ℕ) / 4, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt i.isLt))⟩

private theorem s16t3_alt_mem_N0_iff (n : ℕ) (σ : Perm (Fin n)) :
    σ ∈ s16t3AltN0 n ↔ ∀ i, s16t3_alt_f n (σ i) = s16t3_alt_f n i := by
  rw [show σ ∈ s16t3AltN0 n ↔
      ∀ i, ((σ i : Fin n) : ℕ) / 4 = ((i : Fin n) : ℕ) / 4 from Iff.rfl]
  constructor
  · intro h i
    exact Fin.ext (h i)
  · intro h i
    exact congrArg Fin.val (h i)

private def s16t3_alt_fibreFour (n : ℕ) (b : Fin (n / 4)) :
    {a : Fin n // s16t3_alt_f n a = Fin.castSucc b} ≃ Fin 4 where
  toFun a := ⟨((a : Fin n) : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩
  invFun j :=
    ⟨⟨4 * (b : ℕ) + (j : ℕ), by
        have hb : (b : ℕ) + 1 ≤ n / 4 := Nat.succ_le_of_lt b.isLt
        have h4 : 4 * ((b : ℕ) + 1) ≤ 4 * (n / 4) := Nat.mul_le_mul_left 4 hb
        have hle : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
        have : 4 * (b : ℕ) + (j : ℕ) < 4 * ((b : ℕ) + 1) := by omega
        omega⟩,
      by
        apply Fin.ext
        simp only [s16t3_alt_f, Fin.val_castSucc]
        rw [Nat.mul_add_div (by norm_num : 0 < 4), Nat.div_eq_of_lt j.isLt,
          Nat.add_zero]⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have ha : ((a : Fin n) : ℕ) / 4 = b := by
      have := congrArg Fin.val a.2
      simpa [s16t3_alt_f, Fin.val_castSucc] using this
    have h := Nat.div_add_mod ((a : Fin n) : ℕ) 4
    rw [ha] at h
    simp only [Fin.val_mk]
    omega
  right_inv j := by
    apply Fin.ext
    simp only [Fin.val_mk]
    rw [show 4 * (b : ℕ) + (j : ℕ) = (j : ℕ) + 4 * (b : ℕ) by omega,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt j.isLt

private def s16t3_alt_fibreLast (n : ℕ) :
    {a : Fin n // s16t3_alt_f n a = Fin.last (n / 4)} ≃ Fin (n % 4) where
  toFun a :=
    ⟨((a : Fin n) : ℕ) - 4 * (n / 4), by
      have ha : ((a : Fin n) : ℕ) / 4 = n / 4 := by
        have := congrArg Fin.val a.2
        simpa [s16t3_alt_f, Fin.val_last] using this
      have h := Nat.div_add_mod ((a : Fin n) : ℕ) 4
      rw [ha] at h
      have hone : ((a : Fin n) : ℕ) = 4 * (n / 4) + ((a : Fin n) : ℕ) % 4 := h.symm
      have hn : n = 4 * (n / 4) + n % 4 := s16t3_alt_eq_four_mul_div_add_mod n
      have : ((a : Fin n) : ℕ) % 4 < n % 4 := by omega
      omega⟩
  invFun j :=
    ⟨⟨4 * (n / 4) + (j : ℕ), by
        have hn : n = 4 * (n / 4) + n % 4 := s16t3_alt_eq_four_mul_div_add_mod n
        have hj : (j : ℕ) < n % 4 := j.isLt
        omega⟩,
      by
        apply Fin.ext
        simp only [s16t3_alt_f, Fin.val_last]
        rw [Nat.mul_add_div (by norm_num : 0 < 4),
          Nat.div_eq_of_lt (lt_of_lt_of_le j.isLt
            (Nat.le_of_lt (Nat.mod_lt n (by norm_num)))), Nat.add_zero]⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have ha : ((a : Fin n) : ℕ) / 4 = n / 4 := by
      have := congrArg Fin.val a.2
      simpa [s16t3_alt_f, Fin.val_last] using this
    have h := Nat.div_add_mod ((a : Fin n) : ℕ) 4
    rw [ha] at h
    have hone : ((a : Fin n) : ℕ) = 4 * (n / 4) + ((a : Fin n) : ℕ) % 4 := h.symm
    simp only [Fin.val_mk]
    omega
  right_inv j := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

private theorem s16t3_alt_fibre_card_four (n : ℕ) (b : Fin (n / 4)) :
    Fintype.card {a : Fin n // s16t3_alt_f n a = Fin.castSucc b} = 4 :=
  (Fintype.card_congr (s16t3_alt_fibreFour n b)).trans (Fintype.card_fin 4)

private theorem s16t3_alt_fibre_card_last (n : ℕ) :
    Fintype.card {a : Fin n // s16t3_alt_f n a = Fin.last (n / 4)} = n % 4 :=
  (Fintype.card_congr (s16t3_alt_fibreLast n)).trans (Fintype.card_fin (n % 4))

private theorem s16t3_alt_prod_fibre (n : ℕ) :
    (∏ i : Fin (n / 4 + 1), (Fintype.card {a : Fin n // s16t3_alt_f n a = i})!)
      = 24 ^ (n / 4) * (n % 4)! := by
  rw [Fin.prod_univ_castSucc]
  have hfirst : (∏ i : Fin (n / 4),
        (Fintype.card {a : Fin n // s16t3_alt_f n a = Fin.castSucc i})!)
      = ∏ _i : Fin (n / 4), (24 : ℕ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [s16t3_alt_fibre_card_four]
    decide
  rw [hfirst, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    s16t3_alt_fibre_card_last]

private theorem s16t3_alt_N0_card (n : ℕ) :
    Nat.card ↥(s16t3AltN0 n) = 24 ^ (n / 4) * (n % 4)! := by
  have hiff : ∀ g : Perm (Fin n),
      g ∈ s16t3AltN0 n ↔ s16t3_alt_f n ∘ g = s16t3_alt_f n := by
    intro g
    rw [s16t3_alt_mem_N0_iff]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  calc Nat.card ↥(s16t3AltN0 n)
      = Nat.card {g : Perm (Fin n) // s16t3_alt_f n ∘ g = s16t3_alt_f n} :=
        Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ = Fintype.card {g : Perm (Fin n) // s16t3_alt_f n ∘ g = s16t3_alt_f n} :=
        Nat.card_eq_fintype_card
    _ = 24 ^ (n / 4) * (n % 4)! := by
        rw [DomMulAct.stabilizer_card (s16t3_alt_f n)]
        exact s16t3_alt_prod_fibre n

private theorem s16t3_alt_succ_div_four (n : ℕ) :
    (n + 1) / 4 = n / 4 + if n % 4 = 3 then 1 else 0 := by
  have hn : n + 1 = 4 * (n / 4) + (n % 4 + 1) := by
    have := Nat.div_add_mod n 4
    omega
  rw [hn, Nat.mul_add_div (by norm_num : 0 < 4)]
  congr 1
  have hr : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 4 <;> simp [h]

private theorem s16t3_alt_ordCompl_factorial (r : ℕ) (hr : r < 4) :
    ordCompl[2] (Nat.factorial r) = 3 ^ (if r = 3 then 1 else 0) := by
  interval_cases r
  · rw [show Nat.factorial 0 = 1 by decide,
      Nat.factorization_eq_zero_of_lt (by norm_num : 1 < 2), pow_zero,
      Nat.div_one, if_neg (by norm_num)]
    norm_num
  · rw [show Nat.factorial 1 = 1 by decide,
      Nat.factorization_eq_zero_of_lt (by norm_num : 1 < 2), pow_zero,
      Nat.div_one, if_neg (by norm_num)]
    norm_num
  · rw [show Nat.factorial 2 = 2 by decide, if_neg (by norm_num)]
    simpa using Nat.ordCompl_self_pow (p := 2) (k := 1) Nat.prime_two
  · rw [show Nat.factorial 3 = 6 by decide, show (6 : ℕ) = 2 ^ 1 * 3 by norm_num,
      Nat.ordCompl_pow_mul_of_not_dvd 1 Nat.prime_two (by norm_num), if_pos rfl]
    norm_num

private theorem s16t3_alt_ordCompl_N0 (n : ℕ) :
    ordCompl[2] (Nat.card ↥(s16t3AltN0 n)) = 3 ^ ((n + 1) / 4) := by
  rw [s16t3_alt_N0_card, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, mul_pow,
    show (2 ^ 3 : ℕ) ^ (n / 4) = 2 ^ (3 * (n / 4)) by rw [pow_mul]]
  rw [Nat.ordCompl_mul]
  have h1 : ordCompl[2] (2 ^ (3 * (n / 4)) * 3 ^ (n / 4)) = 3 ^ (n / 4) :=
    Nat.ordCompl_pow_mul_of_not_dvd (3 * (n / 4)) Nat.prime_two (by
      intro h
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h) (by norm_num))
  rw [h1, s16t3_alt_ordCompl_factorial (n % 4) (Nat.mod_lt n (by norm_num)),
    ← pow_add, s16t3_alt_succ_div_four]

private theorem s16t3_alt_N0_eq_ordProj_mul_three_pow (n : ℕ) :
    Nat.card ↥(s16t3AltN0 n)
      = ordProj[2] (Nat.card ↥(s16t3AltN0 n)) * 3 ^ ((n + 1) / 4) := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (Nat.card ↥(s16t3AltN0 n)) 2]
  rw [s16t3_alt_ordCompl_N0 n]

private theorem s16t3_alt_card_sup_mul_card_inf (n : ℕ) (Y : Subgroup (Perm (Fin n)))
    (hYN : Y ≤ Subgroup.normalizer (s16t3AltN0 n : Set (Perm (Fin n)))) :
    Nat.card ↥(s16t3AltN0 n ⊔ Y) * Nat.card ↥(s16t3AltN0 n ⊓ Y)
      = Nat.card ↥(s16t3AltN0 n) * Nat.card ↥Y := by
  let N0 := s16t3AltN0 n
  let Q := N0 ⊔ Y
  have hN0Q : N0 ≤ Q := le_sup_left
  have hYQ : Y ≤ Q := le_sup_right
  have hQnorm : Q ≤ Subgroup.normalizer (N0 : Set (Perm (Fin n))) :=
    sup_le Subgroup.le_normalizer hYN
  have hNnormal : (N0.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN0Q).mpr hQnorm
  have hsup : N0.subgroupOf Q ⊔ Y.subgroupOf Q = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hN0Q hYQ]
    exact Subgroup.subgroupOf_self Q
  have hrel : Y.relIndex Q = Y.relIndex N0 := by
    haveI : (N0.subgroupOf Q).Normal := hNnormal
    have h := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal
      (N0.subgroupOf Q) (Y.subgroupOf Q)
    rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hN0Q] at h
    exact h
  have hQrel : Y.relIndex Q * Nat.card ↥Y = Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card (H := Y) (K := Q)
    rwa [inf_eq_left.mpr hYQ] at this
  have hN0rel : Y.relIndex N0 * Nat.card ↥(N0 ⊓ Y) = Nat.card ↥N0 := by
    have := Subgroup.relIndex_mul_card (H := Y) (K := N0)
    rw [inf_comm] at this
    exact this
  calc Nat.card ↥Q * Nat.card ↥(N0 ⊓ Y)
      = (Y.relIndex Q * Nat.card ↥Y) * Nat.card ↥(N0 ⊓ Y) := by rw [← hQrel]
    _ = (Y.relIndex N0 * Nat.card ↥Y) * Nat.card ↥(N0 ⊓ Y) := by rw [hrel]
    _ = (Y.relIndex N0 * Nat.card ↥(N0 ⊓ Y)) * Nat.card ↥Y := by ring
    _ = Nat.card ↥N0 * Nat.card ↥Y := by rw [hN0rel]

private theorem s16t3_alt_inf_N0_Y_card (n : ℕ) (Y : Subgroup (Perm (Fin n)))
    (hY : CFSG.ABGLocalTools.IsSylowOf 2 Y ⊤)
    (hYN : Y ≤ Subgroup.normalizer (s16t3AltN0 n : Set (Perm (Fin n)))) :
    Nat.card ↥(s16t3AltN0 n ⊓ Y) = ordProj[2] (Nat.card ↥(s16t3AltN0 n)) := by
  let N0 := s16t3AltN0 n
  have hQnorm : N0 ⊔ Y ≤ Subgroup.normalizer (N0 : Set (Perm (Fin n))) :=
    sup_le Subgroup.le_normalizer hYN
  have hYsyl : CFSG.ABGLocalTools.IsSylowOf 2 Y (N0 ⊔ Y) :=
    hY.of_le le_sup_right le_top
  have hinf : CFSG.ABGLocalTools.IsSylowOf 2 (Y ⊓ N0) N0 :=
    hYsyl.inf_of_le_normalizer le_sup_left hQnorm
  have h := hinf.card_eq
  rw [inf_comm] at h
  exact h

private theorem s16t3_alt_two_mul_card_parab (n : ℕ) (hn : 1 < n)
    (Y : Subgroup (Perm (Fin n)))
    (hYN : Y ≤ Subgroup.normalizer (s16t3AltN0 n : Set (Perm (Fin n)))) :
    2 * Nat.card ↥((s16t3AltN0 n ⊔ Y) ⊓ alternatingGroup (Fin n))
      = Nat.card ↥(s16t3AltN0 n ⊔ Y) := by
  haveI : NeZero n := ⟨by omega⟩
  let N0 := s16t3AltN0 n
  let A := alternatingGroup (Fin n)
  let Q := N0 ⊔ Y
  have h01 : (0 : Fin n) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_one'] at this
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at this
    omega
  have hswapN0 : Equiv.swap (0 : Fin n) 1 ∈ N0 := by
    change ∀ i : Fin n,
      (((Equiv.swap (0 : Fin n) 1) i : Fin n) : ℕ) / 4 = (i : ℕ) / 4
    intro i
    rw [Equiv.swap_apply_def]
    split_ifs with h0 h1
    · rw [h0, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < n)]
    · rw [h1, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < n)]
    · rfl
  let β : ↥Q →* ℤˣ := Equiv.Perm.sign.comp Q.subtype
  have hker : β.ker = A.subgroupOf Q := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, A, β]
    exact Equiv.Perm.mem_alternatingGroup.symm
  have hrange : β.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, by simp⟩
    · refine ⟨⟨Equiv.swap (0 : Fin n) 1, Subgroup.mem_sup_left hswapN0⟩, ?_⟩
      exact Equiv.Perm.sign_swap h01
  have hcard := Subgroup.card_ker_mul_card_range β
  rw [hker, hrange] at hcard
  have htop : Nat.card ↥(⊤ : Subgroup ℤˣ) = 2 := by
    rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hkerP : Nat.card ↥(A.subgroupOf Q) = Nat.card ↥(Q ⊓ A) := by
    have h1 : A.subgroupOf Q = (A ⊓ Q).subgroupOf Q := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, x.2, and_true]
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm]
  rw [htop, hkerP] at hcard
  rw [mul_comm] at hcard
  exact hcard

private theorem s16t3_alt_support_cycleOf_card_le_four (n : ℕ) (p : Perm (Fin n))
    (hp : p ∈ s16t3AltN0 n) (i : Fin n) :
    (p.cycleOf i).support.card ≤ 4 := by
  by_cases hpi : p i = i
  · rw [(Equiv.Perm.cycleOf_eq_one_iff p).mpr hpi]
    simp
  · have hfib : ∀ m : ℕ, (((p ^ m) i : Fin n) : ℕ) / 4 = (i : ℕ) / 4 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [show p ^ (m + 1) = p * p ^ m from pow_succ' p m, Equiv.Perm.mul_apply]
        exact (hp ((p ^ m) i)).trans ih
    have hmem : ∀ a ∈ (p.cycleOf i).support, (a : ℕ) / 4 = (i : ℕ) / 4 := by
      intro a ha
      have hsa : Equiv.Perm.SameCycle p i a :=
        (Equiv.Perm.mem_support_cycleOf_iff' hpi).mp ha
      obtain ⟨m, hm⟩ := hsa.exists_nat_pow_eq
      rw [← hm]
      exact hfib m
    have hinj : Set.InjOn (fun a : Fin n => (a : ℕ) % 4)
        ((p.cycleOf i).support : Set (Fin n)) := by
      intro a ha b hb hab
      have ha4 := hmem a ha
      have hb4 := hmem b hb
      have hab' : (a : ℕ) % 4 = (b : ℕ) % 4 := hab
      have h1 := Nat.div_add_mod (a : ℕ) 4
      have h2 := Nat.div_add_mod (b : ℕ) 4
      apply Fin.ext
      omega
    calc (p.cycleOf i).support.card
        = ((p.cycleOf i).support.image (fun a : Fin n => (a : ℕ) % 4)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range 4).card := Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_image] at hx
          obtain ⟨a, _, rfl⟩ := hx
          exact Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
      _ = 4 := Finset.card_range 4

private theorem s16t3_alt_pow_three_of_mem_N0 (n : ℕ) (p : Perm (Fin n))
    (hp : p ∈ s16t3AltN0 n) (k : ℕ) (hpk : p ^ 3 ^ k = 1) : p ^ 3 = 1 := by
  have hord : orderOf p ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hpk
  apply Equiv.ext
  intro i
  have hc_dvd3 : orderOf (p.cycleOf i) ∣ 3 ^ k :=
    (Equiv.Perm.orderOf_cycleOf_dvd_orderOf p i).trans hord
  have hc_le : orderOf (p.cycleOf i) ≤ 4 := by
    by_cases hpi : p i = i
    · rw [(Equiv.Perm.cycleOf_eq_one_iff p).mpr hpi]
      simp
    · rw [(Equiv.Perm.isCycle_cycleOf p hpi).orderOf]
      exact s16t3_alt_support_cycleOf_card_le_four n p hp i
  have hc3 : orderOf (p.cycleOf i) ∣ 3 := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hc_dvd3
    have hle : 3 ^ m ≤ 4 := by rw [← hm]; exact hc_le
    have hm1 : m ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ m := not_le.1 h
      have h3 : 3 ^ 2 ≤ 3 ^ m := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 3) h2
      norm_num at h3
      omega
    rw [hm]
    simpa using pow_dvd_pow 3 hm1
  have hpow : (p.cycleOf i) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hc3
  rw [← Equiv.Perm.cycleOf_pow_apply_self p i 3, hpow]

private theorem s16t3_eq_one_of_isPGroup_two_of_pow_three {H : Type*} [Group H] [Finite H]
    (hH : IsPGroup 2 H) {x : H} {k : ℕ} (hx : x ^ 3 ^ k = 1) : x = 1 := by
  obtain ⟨m, hm⟩ := hH x
  have h2 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  have h3 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hx
  have hcop : Nat.Coprime (3 ^ k) (2 ^ m) :=
    Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num))
  have hone : orderOf x = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h2)
  exact orderOf_eq_one_iff.mp hone

private theorem s16t3_alt_pow_three_of_mem_sup (n : ℕ) (Y : Subgroup (Perm (Fin n)))
    (hY : CFSG.ABGLocalTools.IsSylowOf 2 Y ⊤)
    (hYN : Y ≤ Subgroup.normalizer (s16t3AltN0 n : Set (Perm (Fin n))))
    {p : Perm (Fin n)} (hp : p ∈ s16t3AltN0 n ⊔ Y)
    {k : ℕ} (hpk : p ^ 3 ^ k = 1) : p ^ 3 = 1 := by
  have hN0Q : s16t3AltN0 n ≤ s16t3AltN0 n ⊔ Y := le_sup_left
  have hYQ : Y ≤ s16t3AltN0 n ⊔ Y := le_sup_right
  have hQnorm : s16t3AltN0 n ⊔ Y
      ≤ Subgroup.normalizer (s16t3AltN0 n : Set (Perm (Fin n))) :=
    sup_le Subgroup.le_normalizer hYN
  have hNnormal : ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN0Q).mpr hQnorm
  have hsup : (s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y)
      ⊔ Y.subgroupOf (s16t3AltN0 n ⊔ Y) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hN0Q hYQ]
    exact Subgroup.subgroupOf_self (s16t3AltN0 n ⊔ Y)
  haveI : ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y)).Normal := hNnormal
  let psi := (QuotientGroup.mk' ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y))).comp
    (Subgroup.inclusion hYQ)
  have hφsurj : Function.Surjective psi := by
    intro x
    obtain ⟨q, hq⟩ :=
      QuotientGroup.mk'_surjective ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y)) x
    rw [← hq]
    have hqmem : q ∈ (s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y)
        ⊔ Y.subgroupOf (s16t3AltN0 n ⊔ Y) := by rw [hsup]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Subgroup.mem_sup_of_normal_left
        (s := (s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y))
        (t := Y.subgroupOf (s16t3AltN0 n ⊔ Y))).mp hqmem
    have hbY : (b : Perm (Fin n)) ∈ Y := Subgroup.mem_subgroupOf.mp hb
    refine ⟨⟨(b : Perm (Fin n)), hbY⟩, ?_⟩
    change (QuotientGroup.mk' ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y)))
        (Subgroup.inclusion hYQ ⟨(b : Perm (Fin n)), hbY⟩)
      = (QuotientGroup.mk' ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y))) q
    rw [← hab, map_mul]
    have hker : (QuotientGroup.mk' ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y))) a = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact ha
    rw [hker, one_mul]
    rw [show Subgroup.inclusion hYQ ⟨(b : Perm (Fin n)), hbY⟩ = b from Subtype.ext rfl]
  have hH2 := hY.isPGroup.of_surjective psi hφsurj
  have hx : (QuotientGroup.mk' ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y))
      ⟨p, hp⟩) ^ 3 ^ k = 1 := by
    have hone : (⟨p, hp⟩ : ↥(s16t3AltN0 n ⊔ Y)) ^ 3 ^ k = 1 := Subtype.ext hpk
    rw [← map_pow, hone, map_one]
  have hx1 := s16t3_eq_one_of_isPGroup_two_of_pow_three hH2 hx
  have hpN0 : p ∈ s16t3AltN0 n := by
    have hmem : (⟨p, hp⟩ : ↥(s16t3AltN0 n ⊔ Y)) ∈
        (QuotientGroup.mk' ((s16t3AltN0 n).subgroupOf (s16t3AltN0 n ⊔ Y))).ker :=
      MonoidHom.mem_ker.mpr hx1
    rwa [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hmem
  exact s16t3_alt_pow_three_of_mem_N0 n p hpN0 k hpk

theorem s16t3_alt_std (n : ℕ) :
    ∃ Y P : Subgroup (Equiv.Perm (Fin n)), CFSG.ABGLocalTools.IsSylowOf 2 Y ⊤ ∧
      P ≤ alternatingGroup (Fin n) ∧ (∀ y ∈ Y, ∀ p ∈ P, y * p * y⁻¹ ∈ P) ∧
      Y ⊓ alternatingGroup (Fin n) ≤ P ∧
      Nat.card ↥P = 3 ^ ((n + 1) / 4) *
        2 ^ (Nat.card ↥(alternatingGroup (Fin n))).factorization 2 ∧
      ∀ p ∈ P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 := by
  by_cases hn : n ≤ 1
  · haveI hfin : Subsingleton (Fin n) :=
      ⟨fun a b => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
    haveI huniq : Unique (Perm (Fin n)) := Equiv.permUnique
    have hA : Nat.card ↥(alternatingGroup (Fin n)) = 1 := Nat.card_unique
    have hdiv : (n + 1) / 4 = 0 := Nat.div_eq_of_lt (by omega)
    have hPerm : Nat.card ↥(⊤ : Subgroup (Perm (Fin n))) = 1 := by
      rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
      interval_cases n <;> rfl
    refine ⟨⊥, ⊥, ?_, bot_le, ?_, ?_, ?_, ?_⟩
    · refine CFSG.ABGLocalTools.isSylowOf_of_card (p := 2) bot_le ?_
      rw [Subgroup.card_bot, hPerm]
      norm_num
    · intro y hy p hp
      rw [Subgroup.mem_bot] at hy
      subst hy
      simpa using hp
    · exact inf_le_left
    · rw [Subgroup.card_bot, hA, hdiv]
      norm_num
    · intro p hp k hpk
      rw [Subgroup.mem_bot] at hp
      subst hp
      simp
  · have hn' : 1 < n := not_le.1 hn
    haveI : NeZero n := ⟨by omega⟩
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨Y, hY, hYN⟩ := s16t3_alt_sylow_normalizing n
    refine ⟨Y, (s16t3AltN0 n ⊔ Y) ⊓ alternatingGroup (Fin n), hY, inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro y hy p hp
      refine ⟨?_, ?_⟩
      · exact (s16t3AltN0 n ⊔ Y).mul_mem
          ((s16t3AltN0 n ⊔ Y).mul_mem (Subgroup.mem_sup_right hy) hp.1)
          ((s16t3AltN0 n ⊔ Y).inv_mem (Subgroup.mem_sup_right hy))
      · have hpA : Equiv.Perm.sign p = 1 := Equiv.Perm.mem_alternatingGroup.mp hp.2
        change Equiv.Perm.sign (y * p * y⁻¹) = 1
        rw [map_mul, map_mul, map_inv, hpA]
        group
    · intro x hx
      exact ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
    · have hQcard : Nat.card ↥(s16t3AltN0 n ⊔ Y)
          = 3 ^ ((n + 1) / 4) * Nat.card ↥Y := by
        have hprod := s16t3_alt_card_sup_mul_card_inf n Y hYN
        have hinf := s16t3_alt_inf_N0_Y_card n Y hY hYN
        have hN0 := s16t3_alt_N0_eq_ordProj_mul_three_pow n
        have hpos : 0 < ordProj[2] (Nat.card ↥(s16t3AltN0 n)) := Nat.ordProj_pos _ _
        refine Nat.eq_of_mul_eq_mul_right hpos ?_
        rw [← hinf, hprod, hN0, hinf]
        ring
      have hPcard : 2 * Nat.card ↥((s16t3AltN0 n ⊔ Y) ⊓ alternatingGroup (Fin n))
          = Nat.card ↥(s16t3AltN0 n ⊔ Y) := s16t3_alt_two_mul_card_parab n hn' Y hYN
      have hYcard : Nat.card ↥Y
          = 2 ^ (Nat.card ↥(⊤ : Subgroup (Perm (Fin n)))).factorization 2 := hY.card_eq
      have hPermA : Nat.card ↥(⊤ : Subgroup (Perm (Fin n)))
          = 2 * Nat.card ↥(alternatingGroup (Fin n)) := by
        rw [Subgroup.card_top]
        exact (two_mul_nat_card_alternatingGroup (α := Fin n)).symm
      have hfac : (Nat.card ↥(⊤ : Subgroup (Perm (Fin n)))).factorization 2
          = (Nat.card ↥(alternatingGroup (Fin n))).factorization 2 + 1 := by
        rw [hPermA, Nat.factorization_mul (by norm_num) (Nat.card_pos.ne'),
          Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two, add_comm]
      have hmain : 2 * Nat.card ↥((s16t3AltN0 n ⊔ Y) ⊓ alternatingGroup (Fin n))
          = 2 * (3 ^ ((n + 1) / 4)
              * 2 ^ (Nat.card ↥(alternatingGroup (Fin n))).factorization 2) := by
        rw [hPcard, hQcard, hYcard, hfac, pow_add, pow_one]
        ring_nf
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hmain
    · intro p hp k hpk
      exact s16t3_alt_pow_three_of_mem_sup n Y hY hYN hp.1 hpk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
