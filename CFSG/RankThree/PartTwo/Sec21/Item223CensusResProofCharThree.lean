module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOrders
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofGTwoThree
public import CFSG.RankThree.PartTwo.Sec4.Item413Classical
public import CFSG.RankThree.PartTwo.Sec4.Item426RestInner
public import CFSG.LieType.Multipliers.U43Field

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.LieType.Multipliers.U43 (F9)
open Matrix

namespace Item223CensusResProof

theorem cyc7_eq {R : Type*} [Semiring R] (t : R) :
    cyc7 t = 1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6 := by
  simp [cyc7, Finset.sum_range_succ]

theorem cyc7_ne_zero_F9 : ∀ t : F9, cyc7 t ≠ 0 := by
  intro t
  rw [cyc7_eq]
  revert t
  decide

theorem cycRem_eq {K : Type*} [CommRing K] (a b : K) :
    cycRem a b = remSeq a b 0 + remSeq a b 1 + remSeq a b 2 + remSeq a b 3 + remSeq a b 4 +
      remSeq a b 5 + remSeq a b 6 := by
  simp [cycRem, Finset.sum_range_succ]

theorem cycRem_ne_zero_F9 : ∀ a b : F9, cycRem a b ≠ 0 := by
  intro a b
  rw [cycRem_eq]
  revert a b
  decide

theorem remSeq_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (a b : K) (k : ℕ) :
    remSeq (f a) (f b) k = ((f (remSeq a b k).1), f (remSeq a b k).2) := by
  induction k with
  | zero => simp [remSeq]
  | succ k ih => simp [remSeq, ih]

theorem cycRem_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (a b : K) :
    cycRem (f a) (f b) = (f (cycRem a b).1, f (cycRem a b).2) := by
  simp only [cycRem, remSeq_map]
  refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum, map_sum]

theorem cyc7_ne_zero_of_card {K : Type*} [Field K] [Fintype K] (hK : Fintype.card K = 9) :
    ∀ t : K, cyc7 t ≠ 0 := by
  let e : F9 ≃+* K := FiniteField.ringEquivOfCardEq (by rw [hK]; rfl)
  intro t h
  apply cyc7_ne_zero_F9 (e.symm t)
  apply e.injective
  rw [map_zero, ← h, cyc7, cyc7, map_sum]
  simp

theorem cycRem_ne_zero_of_card {K : Type*} [Field K] [Fintype K] (hK : Fintype.card K = 9) :
    ∀ a b : K, cycRem a b ≠ 0 := by
  let e : F9 ≃+* K := FiniteField.ringEquivOfCardEq (by rw [hK]; rfl)
  intro a b h
  apply cycRem_ne_zero_F9 (e.symm a) (e.symm b)
  have h1 := cycRem_map e.toRingHom (e.symm a) (e.symm b)
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    at h1
  rw [h] at h1
  refine Prod.ext (e.injective ?_) (e.injective ?_)
  · rw [Prod.fst_zero, map_zero]
    exact (congrArg Prod.fst h1).symm
  · rw [Prod.snd_zero, map_zero]
    exact (congrArg Prod.snd h1).symm

theorem matrix_eq_zero_of_commute_cyc7 {K : Type*} [Field K] {n : ℕ} (hn : n ≤ 4)
    (h7 : (7 : K) ≠ 0) (hP1 : ∀ t : K, cyc7 t ≠ 0) (hP2 : ∀ a b : K, cycRem a b ≠ 0)
    {c N : Matrix (Fin n) (Fin n) K} (hc7 : c ^ 7 = 1) (hc1 : c ≠ 1) (hNc : N * c = c * N)
    (hN3 : N ^ 3 = 0) : N = 0 := by
  have h := eq_zero_of_commute_cyc7 (V := Fin n → K)
    (by rw [Module.finrank_fin_fun]; exact hn) h7 hP1 hP2
    (c := Matrix.toLinAlgEquiv' c) (N := Matrix.toLinAlgEquiv' N)
    (by rw [← map_pow, hc7, map_one])
    (fun h => hc1 (Matrix.toLinAlgEquiv'.injective (by rw [h, map_one])))
    (by rw [← map_mul, hNc, map_mul]) (by rw [← map_pow, hN3, map_zero])
  exact Matrix.toLinAlgEquiv'.injective (by rw [h, map_zero])

theorem pow_seven_or_pow_three_of_card_nine {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 9) [CharP K 3] {n : ℕ} [NeZero n] (hn : n ≤ 4) {B : GL (Fin n) K}
    (h21 : B ^ 21 = 1) : B ^ 7 = 1 ∨ B ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  by_contra hne
  push Not at hne
  obtain ⟨h7', h3'⟩ := hne
  have h7 : (7 : K) ≠ 0 := by
    intro h
    have h1 : ((7 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K 3] at h1
    norm_num at h1
  set c : Matrix (Fin n) (Fin n) K := ((B ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set M : Matrix (Fin n) (Fin n) K := ((B ^ 7 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hc7 : c ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, h21, Units.val_one]
  have hc1 : c ≠ 1 := fun h => h3' (Units.ext h)
  have hMc : M * c = c * M := by
    rw [← Units.val_mul, ← Units.val_mul, ← pow_add, ← pow_add, add_comm]
  have hN3 : (M - 1) ^ 3 = 0 := by
    rw [sub_pow_char_of_commute 3 (Commute.one_right M), one_pow, ← Units.val_pow_eq_pow_val,
      ← pow_mul, h21, Units.val_one, sub_self]
  have hNc : (M - 1) * c = c * (M - 1) := by
    rw [sub_mul, mul_sub, hMc, one_mul, mul_one]
  have h0 := matrix_eq_zero_of_commute_cyc7 hn h7 (cyc7_ne_zero_of_card hK)
    (cycRem_ne_zero_of_card hK) hc7 hc1 hNc hN3
  exact h7' (Units.ext (sub_eq_zero.mp h0))

theorem fintype_card_galoisField_three_two [Fintype (GaloisField 3 2)] :
    Fintype.card (GaloisField 3 2) = 9 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
  norm_num

theorem eq_one_of_pow_three_eq_one {K : Type*} [Field K] [CharP K 3] {x : K}
    (h : x ^ 3 = 1) : x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (x - 1) ^ 3 = 0 := by rw [sub_pow_char, one_pow, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1)

theorem eq_three_of_dvd {N b m : ℕ} (hN0 : 0 < N) (hb : N < 2 ^ b - 1)
    (hcheck : ∀ m < b, 1 < m → Odd m → m ≠ 3 → ¬ 3 * (2 ^ m - 1) ∣ N) (hm1 : 1 < m)
    (hmo : Odd m) (h : 3 * (2 ^ m - 1) ∣ N) : m = 3 := by
  by_contra hm3
  by_cases hmb : m < b
  · exact hcheck m hmb hm1 hmo hm3 h
  · have h1 : 2 ^ b ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := Nat.le_of_dvd hN0 ((Dvd.intro_left 3 rfl).trans h)
    omega

theorem card_projSL_three_nine_dvd : Nat.card (projSL 3 (GaloisField 3 2)) ∣ 42456960 := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have h1 := Sec4.card_projSL_dvd 3 (GaloisField 3 2)
  rw [Matrix.card_SL_field, fintype_card_galoisField_three_two] at h1
  norm_num [Fin.prod_univ_succ] at h1
  exact h1

theorem noOrderMersenne223_L39 : NoOrderMersenne223 (projSL 3 (GaloisField 3 2)) := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s m hm1 hmo hs
  have hdvd : 3 * (2 ^ m - 1) ∣ 42456960 :=
    hs ▸ (orderOf_dvd_natCard s).trans card_projSL_three_nine_dvd
  obtain rfl := eq_three_of_dvd (b := 27) (by norm_num) (by norm_num) (by decide) hm1 hmo hdvd
  norm_num at hs
  obtain ⟨A, hA, hAs⟩ := s.2
  have hdet : Matrix.GeneralLinearGroup.det A = 1 := MonoidHom.mem_ker.mp hA
  have hmk : ∀ k : ℕ, s ^ k = 1 ↔ A ^ k ∈ Subgroup.center (GL (Fin 3) (GaloisField 3 2)) := by
    intro k
    rw [← OneMemClass.coe_eq_one, Subgroup.coe_pow, ← hAs, ← map_pow,
      Matrix.ProjGenLinGroup.mk_eq_one]
  have h21 : A ^ 21 = 1 := by
    have hc := (hmk 21).mp (hs ▸ pow_orderOf_eq_one s)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨l, hl⟩ := hc
    have hl3 : l ^ 3 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hl
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow, hdet, one_pow] at h1
      exact h1
    have hl1 : l = 1 := Units.ext (eq_one_of_pow_three_eq_one (by
      rw [← Units.val_pow_eq_pow_val, hl3, Units.val_one]))
    rw [← hl, hl1, map_one]
  have hcent : ∀ k : ℕ, A ^ k = 1 → s ^ k = 1 := fun k h =>
    (hmk k).mpr (h ▸ Subgroup.one_mem _)
  rcases pow_seven_or_pow_three_of_card_nine fintype_card_galoisField_three_two (by norm_num)
    h21 with h | h
  · have := orderOf_dvd_of_pow_eq_one (hcent 7 h)
    rw [hs] at this
    norm_num at this
  · have := orderOf_dvd_of_pow_eq_one (hcent 3 h)
    rw [hs] at this
    norm_num at this

theorem fintype_card_galoisField_three_two_mul_one [Fintype (GaloisField 3 (2 * 1))] :
    Fintype.card (GaloisField 3 (2 * 1)) = 9 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 3 (2 * 1) (by norm_num)]
  norm_num

theorem noOrderMersenne223_U43 : NoOrderMersenne223 (projSU 4 3 1) := by
  have : Fintype (GaloisField 3 (2 * 1)) := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s m hm1 hmo hs
  have hdvd : 3 * (2 ^ m - 1) ∣ 3265920 := by
    rw [← hs, ← Sec4.Item426Rest.card_projSU_four_three]
    exact orderOf_dvd_natCard s
  obtain rfl := eq_three_of_dvd (b := 23) (by norm_num) (by norm_num) (by decide) hm1 hmo hdvd
  norm_num at hs
  obtain ⟨A, hA, hAs⟩ := s.2
  have hdet : (A : Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1))).det = 1 :=
    Sec4.det_of_mem_closure_su _ hA
  have hmk : ∀ k : ℕ, s ^ k = 1 ↔
      A ^ k ∈ Subgroup.center (GL (Fin 4) (GaloisField 3 (2 * 1))) := by
    intro k
    rw [← OneMemClass.coe_eq_one, Subgroup.coe_pow, ← hAs, ← map_pow,
      Matrix.ProjGenLinGroup.mk_eq_one]
  have h84 : (A ^ 4) ^ 21 = 1 := by
    have hc := (hmk 21).mp (hs ▸ pow_orderOf_eq_one s)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨l, hl⟩ := hc
    have hl4 : l ^ 4 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hl
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow] at h1
      have h2 : Matrix.GeneralLinearGroup.det A = 1 :=
        Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one])
      rw [h2, one_pow] at h1
      exact h1
    rw [← pow_mul, show 4 * 21 = 21 * 4 from rfl, pow_mul, ← hl, ← map_pow, hl4, map_one]
  have hcent : ∀ k : ℕ, (A ^ 4) ^ k = 1 → s ^ (4 * k) = 1 := fun k h =>
    (hmk (4 * k)).mpr (by rw [pow_mul, h]; exact Subgroup.one_mem _)
  rcases pow_seven_or_pow_three_of_card_nine fintype_card_galoisField_three_two_mul_one le_rfl
    h84 with h | h
  · have := orderOf_dvd_of_pow_eq_one (hcent 7 h)
    rw [hs] at this
    norm_num at this
  · have := orderOf_dvd_of_pow_eq_one (hcent 3 h)
    rw [hs] at this
    norm_num at this

theorem noOrderMersenne223_G2_three {X : Type} [Group X]
    (hX : Blueprint.ChevalleyExceptionalModel X .G2 3 1) : NoOrderMersenne223 X := by
  intro s m hm1 hmo hs
  have hdvd : 3 * (2 ^ m - 1) ∣ 4245696 :=
    hs ▸ (orderOf_dvd_natCard s).trans (Sec4.Item426Rest.card_dvd_of_G2_three hX)
  obtain rfl := eq_three_of_dvd (b := 24) (by norm_num) (by norm_num) (by decide) hm1 hmo hdvd
  exact orderOf_ne_twentyOne_of_G2_three hX s (by rw [hs]; norm_num)

end Item223CensusResProof

open Item223CensusResProof

theorem census223CharThreeOrders_holds :
    Census223CharThreeOrders :=
  ⟨noOrderMersenne223_L39, fun _ _ hX => noOrderMersenne223_G2_three hX, noOrderMersenne223_U43⟩

end CFSG.RankThree.PartTwo.Sec21
