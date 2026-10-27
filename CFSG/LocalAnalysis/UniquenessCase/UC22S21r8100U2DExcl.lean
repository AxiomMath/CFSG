module

public import CFSG.RankThree.PartTwo.KFacts.KP10LinearTwo
public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.SubgroupLists (dickson_gl_two upperGL coe_upperGL mem_statedSL_iff)
open CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

theorem gl2Excl_not_sq_dvd {p c : ℕ} (hp : 3 ≤ p) (hc : c = 12 ∨ c = 24 ∨ c = 60) :
    ¬ p * p ∣ c := by
  intro h
  have hc60 : p * p ≤ 60 := by
    rcases hc with rfl | rfl | rfl <;> exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
  have hp7 : p ≤ 7 := by nlinarith
  interval_cases p <;> rcases hc with rfl | rfl | rfl <;> norm_num at h

theorem gl2Excl_index_eq_one {n N c p : ℕ} (hc : c = 12 ∨ c = 24 ∨ c = 60) (hp : 3 ≤ p)
    (hnN : n * N = c) (hdvd : 2 * p ∣ N) (hne : N ≠ 2 * p) (hmod : n ≡ 1 [MOD p]) : n = 1 := by
  obtain ⟨m, rfl⟩ := hdvd
  have hc0 : 0 < c := by omega
  have hc60 : c ≤ 60 := by omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero, mul_zero] at hnN
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (mul_one _)
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hnN
    omega
  have hm : 2 ≤ m := by omega
  have h12 : 12 ≤ 2 * p * m := by nlinarith
  have hn : n * 12 ≤ n * (2 * p * m) := Nat.mul_le_mul_left n h12
  have hpm : 2 * p * 2 ≤ 2 * p * m := Nat.mul_le_mul_left _ hm
  have hle : 2 * p * m ≤ n * (2 * p * m) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hn0)
  have hn5 : n ≤ 5 := by omega
  have hp15 : p ≤ 15 := by omega
  unfold Nat.ModEq at hmod
  interval_cases n <;> interval_cases p <;> omega

theorem gl2Excl_mem_of_index_dvd_two {X : Type*} [Group X] {C : Subgroup X} (hC : C.index ∣ 2)
    {p : ℕ} (hp : Odd p) {x : X} (hx : x ^ p = 1) : x ∈ C := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hC with h | h
  · rw [index_eq_one.1 h]
    exact mem_top x
  · obtain ⟨k, rfl⟩ := hp
    have hx' : x = (x ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hx, one_mul]
    rw [hx']
    exact pow_mem (sq_mem_of_index_two h x) _

theorem gl2Excl_false_of_index_dvd_two {X : Type*} [Group X] {p : ℕ} {Y : Subgroup X}
    (hY : IsStronglyPEmbedded p Y) (h : Y.index ∣ 2) : False := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h | h
  · exact hY.1 (index_eq_one.1 h)
  · have := normal_of_index_eq_two h
    exact hY.not_dvd_card_of_normal_le le_rfl hY.2.1

theorem gl2Excl_normal_zpowers {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hQ : Nat.card Q = 12 ∨ Nat.card Q = 24 ∨ Nat.card Q = 60) {a b c : Q}
    (ha : orderOf a = 2) (hb : orderOf b = p) (hab : Commute a b) (hcb : c * b * c⁻¹ = b⁻¹) :
    (zpowers b).Normal := by
  have hp := (Fact.out : p.Prime)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hPc : Nat.card (zpowers b) = p := by rw [Nat.card_zpowers, hb]
  have hPp : IsPGroup p (zpowers b) := IsPGroup.of_card (n := 1) (by rw [hPc, pow_one])
  have hidx : ¬ p ∣ (zpowers b).index := by
    rintro ⟨k, hk⟩
    refine gl2Excl_not_sq_dvd hp3 hQ ⟨k, ?_⟩
    rw [← (zpowers b).card_mul_index, hPc, hk, mul_assoc]
  set N := normalizer ((zpowers b : Subgroup Q) : Set Q) with hN
  have hmod : N.index ≡ 1 [MOD p] := by
    have h := card_sylow_modEq_one p Q
    rw [(hPp.toSylow hidx).card_eq_index_normalizer] at h
    exact h
  have hx : orderOf (a * b) = 2 * p := by
    rw [hab.orderOf_mul_eq_mul_orderOf_of_coprime (by
      rw [ha, hb]
      exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)), ha, hb]
  have hxb : Commute (a * b) b := hab.mul_left (Commute.refl b)
  have hxN : zpowers (a * b) ≤ N :=
    zpowers_le.2 (CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers b
      (mem_centralizer_singleton_iff.2 hxb.eq))
  have hcN : c ∈ N := by
    refine mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [← conj_zpow, hcb]
    exact zpow_mem (inv_mem (mem_zpowers b)) k
  have hcx : c ∉ zpowers (a * b) := by
    intro hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    rw [(hxb.zpow_left k).eq, mul_inv_cancel_right] at hcb
    have h2 : b ^ 2 = 1 := by
      calc b ^ 2 = b⁻¹ * b := by rw [sq, ← hcb]
        _ = 1 := inv_mul_cancel b
    have h := orderOf_dvd_of_pow_eq_one h2
    rw [hb] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have h2p : 2 * p ∣ Nat.card N := by
    rw [← hx, ← Nat.card_zpowers]
    exact card_dvd_of_le hxN
  have hne : Nat.card N ≠ 2 * p := by
    intro h
    have heq : zpowers (a * b) = N :=
      eq_of_le_of_card_ge hxN (le_of_eq (by rw [h, Nat.card_zpowers, hx]))
    exact hcx (heq ▸ hcN)
  have hidxN : N.index * Nat.card N = Nat.card Q := by
    rw [mul_comm]
    exact N.card_mul_index
  exact normalizer_eq_top_iff.1 (index_eq_one.1 (gl2Excl_index_eq_one hQ hp3 hidxN h2p hne hmod))

section Matrices

variable {K : Type*} [CommRing K]

theorem gl2Excl_mem_center_of_diagonal {g : GL (Fin 2) K} {α : Fin 2 → K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = diagonal α) (h : α 0 = α 1) :
    g ∈ center (GL (Fin 2) K) :=
  GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨α 0, by
    rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]⟩

theorem gl2Excl_eq_of_diagonal_mem_center {g : GL (Fin 2) K} {α : Fin 2 → K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = diagonal α) (hc : g ∈ center (GL (Fin 2) K)) :
    α 0 = α 1 := by
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hc
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  rw [hg] at h0 h1
  simp only [scalar_apply, diagonal_apply_eq] at h0 h1
  exact h0.symm.trans h1

theorem gl2Excl_entry_eq_zero_of_mem_center {z : GL (Fin 2) K}
    (hz : z ∈ center (GL (Fin 2) K)) : (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  rw [← hc]
  simp

theorem gl2Excl_mulVec_mem_span {g : Matrix (Fin 2) (Fin 2) K} (hg : g 1 0 = 0) :
    g *ᵥ Pi.single 0 1 ∈ Submodule.span K {(Pi.single 0 1 : Fin 2 → K)} :=
  Submodule.mem_span_singleton.2 ⟨g 0 0, by
    rw [mulVec_single_one]
    ext i
    fin_cases i <;> simp [hg]⟩

theorem gl2Excl_conj_antidiag {s y : GL (Fin 2) K} {α : Fin 2 → K}
    (hs0 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = 0) (hs1 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)
    (hα : (y : Matrix (Fin 2) (Fin 2) K) = diagonal α) :
    ((s * y * s⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = diagonal ![α 1, α 0] := by
  have hsy : (s : Matrix (Fin 2) (Fin 2) K) * diagonal α =
      diagonal ![α 1, α 0] * (s : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    rw [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [hs0, hs1, mul_comm]
  rw [Units.val_mul, Units.val_mul, hα, hsy, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

theorem gl2Excl_commute_of_diagonal {g h : GL (Fin 2) K} {α β : Fin 2 → K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = diagonal α)
    (hh : (h : Matrix (Fin 2) (Fin 2) K) = diagonal β) : Commute g h :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, hg, hh, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _)

end Matrices

section GLTwo

variable {r : ℕ} [Fact r.Prime]

theorem gl2Excl_eq_of_normal_sylow {W : Subgroup (GL (Fin 2) (ZMod r))} (P : Sylow r W)
    (hPn : (P : Subgroup W).Normal) (hPc : Nat.card P = r) {p : ℕ} [Fact p.Prime] (hpr : p ≠ r)
    {s y : GL (Fin 2) (ZMod r)} (hsW : s ∈ W) (hyW : y ∈ W)
    (hs0 : (s : Matrix (Fin 2) (Fin 2) (ZMod r)) 0 0 = 0)
    (hs1 : (s : Matrix (Fin 2) (Fin 2) (ZMod r)) 1 1 = 0) (hyp : y ^ p = 1) {α : Fin 2 → ZMod r}
    (hα : (y : Matrix (Fin 2) (Fin 2) (ZMod r)) = diagonal α) : α 0 = α 1 := by
  obtain ⟨q, hq, hqe⟩ := mem_map.1 (KP10.commutator_le_of_normal_sylow P hPn hPc
    (commutator_mem_commutator hsW hyW))
  have hqr : q ^ r = 1 := by
    have h := pow_card_eq_one' (G := (P : Subgroup W)) (x := ⟨q, hq⟩)
    rw [hPc] at h
    exact congrArg Subtype.val h
  have hr : ⁅s, y⁆ ^ r = 1 := by
    rw [← hqe]
    exact congrArg Subtype.val hqr
  have hz := gl2Excl_conj_antidiag hs0 hs1 hα
  have hzy : Commute (s * y * s⁻¹) y := gl2Excl_commute_of_diagonal hz hα
  have hp : ⁅s, y⁆ ^ p = 1 := by
    rw [commutatorElement_def, hzy.inv_right.mul_pow, conj_pow, hyp, mul_one, mul_inv_cancel,
      one_mul, inv_pow, hyp, inv_one]
  have h1 : ⁅s, y⁆ = 1 := by
    have h := pow_gcd_eq_one.2 ⟨hp, hr⟩
    rwa [((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : r.Prime)).2 hpr).gcd_eq_one,
      pow_one] at h
  rw [commutatorElement_def, mul_inv_eq_one] at h1
  have h3 := congrArg (fun g : GL (Fin 2) (ZMod r) => (g : Matrix (Fin 2) (Fin 2) (ZMod r)) 0 0) h1
  simp only [hz, hα, diagonal_apply_eq] at h3
  simpa using h3.symm

theorem gl2Excl (r p : ℕ) [Fact r.Prime] [Fact p.Prime]
    (hr2 : r ≠ 2) (hp2 : p ≠ 2) (W H : Subgroup (GL (Fin 2) (ZMod r))) (hHW : H ≤ W)
    (hemb : IsStronglyPEmbedded p (H.subgroupOf W)) (hrH : ¬ r ∣ Nat.card H)
    (hstab : ∀ g ∈ W, (g : Matrix (Fin 2) (Fin 2) (ZMod r)) *ᵥ Pi.single 0 1 ∈
      Submodule.span (ZMod r) {(Pi.single 0 1 : Fin 2 → ZMod r)} → g ∈ H)
    (t : GL (Fin 2) (ZMod r)) (htH : t ∈ H)
    (ht : (t : Matrix (Fin 2) (Fin 2) (ZMod r)) = diagonal ![-1, 1])
    (s : GL (Fin 2) (ZMod r)) (hsH : s ∈ H) (hs0 : (s : Matrix (Fin 2) (Fin 2) (ZMod r)) 0 0 = 0)
    (hs1 : (s : Matrix (Fin 2) (Fin 2) (ZMod r)) 1 1 = 0)
    (y : GL (Fin 2) (ZMod r)) (hyH : y ∈ H) (hyp : y ^ p = 1) (hy1 : y ≠ 1) (α : Fin 2 → ZMod r)
    (hα : (y : Matrix (Fin 2) (Fin 2) (ZMod r)) = diagonal α) : False := by
  classical
  have hp := (Fact.out : p.Prime)
  have hr := (Fact.out : r.Prime)
  have hyW := hHW hyH
  set y' : W := ⟨y, hyW⟩ with hy'
  have hy'1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hy'p : y' ^ p = 1 := Subtype.ext hyp
  have hy'Y : y' ∈ H.subgroupOf W := mem_subgroupOf.2 hyH
  have hcent := hemb.centralizer_le hy'1 hy'p hy'Y
  have hpH : p ∣ Nat.card H := by
    have h := orderOf_dvd_natCard (⟨y, hyH⟩ : H)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hyp hy1] at h
  have hpr : p ≠ r := fun h => hrH (h ▸ hpH)
  by_cases hsc : α 0 = α 1
  · have hyc := gl2Excl_mem_center_of_diagonal hα hsc
    refine hemb.1 (eq_top_iff.2 fun w _ => hcent (mem_centralizer_singleton_iff.2 ?_))
    exact Subtype.ext (mem_center_iff.1 hyc (w : GL (Fin 2) (ZMod r)))
  by_cases hrW : r ∣ Nat.card W
  · rcases dickson_gl_two W hrW with ⟨P, hPn, hPc⟩ | hSL
    · exact hsc (gl2Excl_eq_of_normal_sylow P hPn hPc hpr (hHW hsH) hyW hs0 hs1 hyp hα)
    ·
      have hu : upperGL (1 : ZMod r) ∈ H := by
        refine hstab _ (hSL ((mem_statedSL_iff _).2 ?_)) (gl2Excl_mulVec_mem_span ?_)
        · rw [coe_upperGL, det_fin_two_of]
          ring
        · simp [coe_upperGL]
      have h := orderOf_dvd_natCard (⟨_, hu⟩ : H)
      rw [Subgroup.orderOf_mk, KP10.orderOf_upperGL_one] at h
      exact hrH h
  rcases KP10.exists_comm_of_not_dvd W hrW with ⟨C, hC, hCi⟩ | hW
  ·
    have hy'C := gl2Excl_mem_of_index_dvd_two hCi (hp.odd_of_ne_two hp2) hy'p
    have hCY : C ≤ H.subgroupOf W := fun c hc =>
      hcent (mem_centralizer_singleton_iff.2 (hC c hc y' hy'C))
    exact gl2Excl_false_of_index_dvd_two hemb ((index_dvd_of_le hCY).trans hCi)
  have : Finite (ProjGenLinGroup (Fin 2) (ZMod r)) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have : Fact (2 < r) := ⟨by have := hr.two_le; omega⟩
  set π := ProjGenLinGroup.mk.subgroupMap W with hπ
  have hπ1 : ∀ w : W, π w = 1 ↔ (w : GL (Fin 2) (ZMod r)) ∈ center (GL (Fin 2) (ZMod r)) :=
    fun w => by
      rw [← ProjGenLinGroup.mk_eq_one, Subtype.ext_iff]
      exact Iff.rfl
  set t' : W := ⟨t, hHW htH⟩ with ht'
  set s' : W := ⟨s, hHW hsH⟩ with hs'
  have hta : orderOf (π t') = 2 := by
    refine orderOf_eq_prime ?_ fun h => ZMod.neg_one_ne_one
      (gl2Excl_eq_of_diagonal_mem_center ht ((hπ1 t').1 h))
    have ht2 : t ^ 2 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, ht, diagonal_pow, Units.val_one, ← diagonal_one]
      congr 1
      funext i
      fin_cases i
      exacts [neg_one_sq, one_pow 2])
    rw [← map_pow, show t' ^ 2 = 1 from Subtype.ext ht2, map_one]
  have hyb : orderOf (π y') = p := by
    refine orderOf_eq_prime (by rw [← map_pow, hy'p, map_one]) fun h => hsc ?_
    exact gl2Excl_eq_of_diagonal_mem_center hα ((hπ1 y').1 h)
  have hty : Commute (π t') (π y') :=
    (show Commute t' y' from Subtype.ext (gl2Excl_commute_of_diagonal ht hα).eq).map π
  have hsy : π s' * π y' * (π s')⁻¹ = (π y')⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_inv, ← map_mul π, ← map_mul π, ← map_mul π, hπ1]
    refine gl2Excl_mem_center_of_diagonal (α := fun i => ![α 1, α 0] i * α i) ?_
      (by simp [mul_comm])
    change ((s * y * s⁻¹ * y : GL (Fin 2) (ZMod r)) : Matrix (Fin 2) (Fin 2) (ZMod r)) = _
    rw [Units.val_mul, gl2Excl_conj_antidiag hs0 hs1 hα, hα, diagonal_mul_diagonal]
  have hN := gl2Excl_normal_zpowers hp2 hW hta hyb hty hsy
  have hSY : (zpowers (π y')).comap π ≤ H.subgroupOf W := by
    intro w hw
    rw [mem_comap] at hw
    obtain ⟨k, hk⟩ : ∃ k : ℕ, π y' ^ k = π w :=
      (isOfFinOrder_of_finite (π y')).mem_powers_iff_mem_zpowers.2 hw
    have hk' : ProjGenLinGroup.mk (y ^ k) = ProjGenLinGroup.mk (w : GL (Fin 2) (ZMod r)) := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    obtain ⟨z, hz, hzw⟩ := ProjGenLinGroup.mk_eq_mk_iff'.1 hk'
    refine mem_subgroupOf.2 (hstab _ w.2 (gl2Excl_mulVec_mem_span ?_))
    rw [← hzw, Units.val_mul, Units.val_pow_eq_pow_val, hα, diagonal_pow, diagonal_mul,
      gl2Excl_entry_eq_zero_of_mem_center hz, mul_zero]
  have hy'S : y' ∈ (zpowers (π y')).comap π := mem_zpowers _
  have hpS : p ∣ Nat.card ((zpowers (π y')).comap π) := by
    have h := orderOf_dvd_natCard (⟨y', hy'S⟩ : (zpowers (π y')).comap π)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hy'p hy'1] at h
  have := hN.comap π
  exact hemb.not_dvd_card_of_normal_le hSY hpS

end GLTwo

end CFSG.LocalAnalysis.UniquenessCase.UC22
