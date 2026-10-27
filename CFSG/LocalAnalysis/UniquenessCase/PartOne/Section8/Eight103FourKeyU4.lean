module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyAbstract
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyU4Lang
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyU4Syl3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyU4Out
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyU4Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K]

private lemma exists_rootsOfUnity_orderOf_eq_prime (h : UnitaryFieldData 2 f K) {p : ℕ}
    (hp : p.Prime) (hpf : p ∣ 2 ^ f + 1) :
    ∃ l : rootsOfUnity (2 ^ f + 1) K, orderOf l = p := by
  have hKfin : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
  have hcard : Nat.card (rootsOfUnity (2 ^ f + 1) K) = 2 ^ f + 1 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hK]
    refine Nat.gcd_eq_right ?_
    refine ⟨2 ^ f - 1, ?_⟩
    have h := sq_tsub_sq (2 ^ f) 1
    rw [one_pow] at h
    exact h
  have hdvd : p ∣ Nat.card (rootsOfUnity (2 ^ f + 1) K) := by
    rw [hcard]
    exact hpf
  exact exists_prime_orderOf_dvd_card' (G := rootsOfUnity (2 ^ f + 1) K) p hdvd

private lemma pow_two_pow_eq_self_of_orderOf {p m : ℕ} {l : rootsOfUnity (2 ^ f + 1) K}
    (hl : orderOf l = p) (h2m : 2 ^ m ≡ 1 [MOD p]) :
    (l : Kˣ) ^ 2 ^ m = (l : Kˣ) := by
  have h1m : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' h1m).mp h2m.symm
  have h2meq : 2 ^ m = p * t + 1 := by
    rw [← Nat.sub_add_cancel h1m, ht]
  have hlp : l ^ p = 1 := by
    rw [← hl]
    exact pow_orderOf_eq_one l
  have hvalp : (l : Kˣ) ^ p = 1 := by
    have h := congrArg (fun x : rootsOfUnity (2 ^ f + 1) K => (x : Kˣ)) hlp
    simpa using h
  rw [h2meq, pow_add, pow_one, pow_mul, hvalp, one_pow, one_mul]

private lemma field_pow_two_pow_eq_self {p m : ℕ} {l : rootsOfUnity (2 ^ f + 1) K}
    (hl : orderOf l = p) (h2m : 2 ^ m ≡ 1 [MOD p]) :
    ((l : Kˣ) : K) ^ 2 ^ m = ((l : Kˣ) : K) := by
  rw [← Units.val_pow_eq_pow_val, pow_two_pow_eq_self_of_orderOf (f := f) (K := K) hl h2m]

private lemma orderOf_two_zmod_dvd_m {p a m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpf : p ∣ 2 ^ f + 1) (h2f : 2 * f = p ^ a * m) :
    orderOf (2 : ZMod p) ∣ m := by
  have : Fact p.Prime := ⟨hp⟩
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpeq : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left hp.ne_one
    exact hp2 hpeq
  have hord_dvd_2f : orderOf (2 : ZMod p) ∣ 2 * f := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have h0 : ((2 : ZMod p) ^ f + 1) = 0 := by
      have h : (((2 : ℕ) ^ f + 1 : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact hpf
      simpa using h
    have hneg : (2 : ZMod p) ^ f = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      exact h0
    rw [show 2 * f = f * 2 by ring, pow_mul, hneg]
    exact neg_one_sq
  have hord_dvd_pm1 : orderOf (2 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one h2ne0
  have hcop : Nat.Coprime (orderOf (2 : ZMod p)) (p ^ a) := by
    have hcop_p : Nat.Coprime (p - 1) (p ^ a) := by
      rcases Nat.eq_zero_or_pos a with ha0 | ha
      · rw [ha0, pow_zero]
        exact Nat.coprime_one_right _
      · rw [Nat.coprime_pow_right_iff ha]
        rw [Nat.coprime_self_sub_left hp.one_le]
        simp
    exact Nat.Coprime.of_dvd_left hord_dvd_pm1 hcop_p
  have h := hord_dvd_2f
  rw [h2f] at h
  exact hcop.dvd_of_dvd_mul_left h

private lemma uFieldAut_mem_u4TorusSylow (h : UnitaryFieldData 2 f K) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {p : ℕ}
    {s : StatedProj (StatedSU 4 (2 ^ f) K)}
    (hs : s ∈ u4TorusSylow (f := f) (K := K) p) :
    uFieldAut h (n := 4) (by norm_num) σ s ∈ u4TorusSylow (f := f) (K := K) p := by
  rw [u4TorusSylow] at hs ⊢
  obtain ⟨d, hdP, rfl⟩ := Subgroup.mem_map.mp hs
  rw [uFieldAut_u4TorusHom h hσ]
  refine Subgroup.mem_map_of_mem _ ?_
  have hd := hdP
  change (powMonoidHom (p ^ (2 ^ f + 1).factorization p)) d = 1 at hd
  rw [powMonoidHom_apply] at hd
  change (powMonoidHom (p ^ (2 ^ f + 1).factorization p)) (d ^ 2) = 1
  rw [powMonoidHom_apply]
  rw [← pow_mul, mul_comm, pow_mul, hd, one_pow]

private lemma pow_uFieldAut_mem_u4TorusSylow (h : UnitaryFieldData 2 f K) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {p : ℕ} (j : ℕ)
    {s : StatedProj (StatedSU 4 (2 ^ f) K)}
    (hs : s ∈ u4TorusSylow (f := f) (K := K) p) :
    (uFieldAut h (n := 4) (by norm_num) σ ^ j) s ∈ u4TorusSylow (f := f) (K := K) p := by
  induction j with
  | zero => simpa using hs
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply]
      exact uFieldAut_mem_u4TorusSylow h hσ ih

private lemma vec_pow_of_pow_eq_one {p : ℕ} {l : rootsOfUnity (2 ^ f + 1) K} (hlp : l ^ p = 1) :
    (![l, l, l⁻¹] : Fin 3 → rootsOfUnity (2 ^ f + 1) K) ^ p = 1 := by
  funext i
  fin_cases i <;> simp [Pi.pow_apply, hlp]

theorem u45KeyDvdConcl_statedSU_four (h : UnitaryFieldData 2 f K) (hf : Even f)
    (hX : UC22.IsU4 (StatedProj (StatedSU 4 (2 ^ f) K)) f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hpf : p ∣ 2 ^ f + 1) :
    U45KeyDvdConcl (StatedProj (StatedSU 4 (2 ^ f) K)) p := by
  classical
  have hKfin : Finite K := h.finite
  have hXfin : Finite (StatedProj (StatedSU 4 (2 ^ f) K)) := inferInstance
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_eq_sq h
  have hf1 : 1 ≤ f := h.one_le
  obtain ⟨a, m, hm, h2f⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : 2 * f ≠ 0) p hp.ne_one
  obtain ⟨l, hl⟩ := exists_rootsOfUnity_orderOf_eq_prime (K := K) h hp hpf
  have hl1 : l ≠ 1 := by
    intro hlt
    rw [hlt, orderOf_one] at hl
    exact hp.ne_one hl.symm
  have hlp : l ^ p = 1 := by
    rw [← hl]
    exact pow_orderOf_eq_one l
  have h2m : (2 : ZMod p) ^ m = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (orderOf_two_zmod_dvd_m (f := f) hp hp2 hpf h2f)
  have hmod : 2 ^ m ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact h2m
  have hlm : ((l : Kˣ) : K) ^ 2 ^ m = ((l : Kˣ) : K) :=
    field_pow_two_pow_eq_self (f := f) (K := K) hl hmod
  let t₀ : StatedProj (StatedSU 4 (2 ^ f) K) := u4TorusHom ![l, l, l⁻¹]
  have hvecp : (![l, l, l⁻¹] : Fin 3 → rootsOfUnity (2 ^ f + 1) K) ^ p = 1 :=
    vec_pow_of_pow_eq_one (f := f) (K := K) hlp
  have ht₀pow : t₀ ^ p = 1 := by
    change u4TorusHom ![l, l, l⁻¹] ^ p = 1
    rw [← map_pow, hvecp, map_one]
  have ht₀P : t₀ ∈ u4TorusSylow (f := f) (K := K) p := by
    rw [u4TorusSylow]
    refine Subgroup.mem_map_of_mem _ ?_
    change (powMonoidHom (p ^ (2 ^ f + 1).factorization p)) ![l, l, l⁻¹] = 1
    rw [powMonoidHom_apply]
    obtain ⟨v', hv'⟩ := Nat.exists_eq_succ_of_ne_zero
      (show (2 ^ f + 1).factorization p ≠ 0 from
        (Nat.Prime.factorization_pos_of_dvd hp (by positivity) hpf).ne')
    rw [hv', pow_succ', pow_mul, hvecp, one_pow]
  have ht₀ : t₀ ≠ 1 := by
    intro h1
    have h1' : u4TorusHom ![l, l, l⁻¹] = 1 := h1
    have hvec : (![l, l, l⁻¹] : Fin 3 → rootsOfUnity (2 ^ f + 1) K) = 1 :=
      u4TorusHom_injective h.one_le (by simpa using h1')
    have hl1' : l = 1 := by
      have := congrFun hvec 0
      simpa using this
    exact hl1 hl1'
  set Φ : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) :=
    uFieldAut h (n := 4) (by norm_num) σ with hΦdef
  have hΦ : ∀ α : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)),
      ∃ y : StatedProj (StatedSU 4 (2 ^ f) K), ∃ j : ℕ,
        α = MulAut.conj y * Φ ^ j := by
    intro α
    obtain ⟨y, j, hα⟩ := exists_conj_mul_uFieldAut_pow h hσ α
    exact ⟨y, j, hα⟩
  have hΦinn : ∀ k : ℕ, Φ ^ k ∈
      (MulAut.conj : StatedProj (StatedSU 4 (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU 4 (2 ^ f) K))).range → Φ ^ k = 1 := by
    intro k hk
    exact uFieldAut_pow_eq_one_of_mem_range h hX hσ hk
  have hP₀ : IsPGroup p (u4TorusSylow (f := f) (K := K) p) := isPGroup_u4TorusSylow hp
  have hP₀i : ¬ p ∣ (u4TorusSylow (f := f) (K := K) p).index :=
    not_dvd_index_u4TorusSylow h hf hp hpf
  have hP₀c : ∀ x ∈ u4TorusSylow (f := f) (K := K) p,
      ∀ y ∈ u4TorusSylow (f := f) (K := K) p, x * y = y * x := by
    intro x hx y hy
    rw [u4TorusSylow] at hx hy
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hΦP : ∀ s ∈ u4TorusSylow (f := f) (K := K) p,
      (Φ ^ m) s ∈ u4TorusSylow (f := f) (K := K) p := by
    intro s hs
    exact pow_uFieldAut_mem_u4TorusSylow h hσ m hs
  have hΦm : Φ ^ (p ^ a * m) = 1 := by
    rw [hΦdef, ← h2f]
    exact uFieldAut_pow_two_mul_eq_one h hσ
  have hΩ : ∀ E : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K)),
      E ≤ u4TorusSylow (f := f) (K := K) p → IsElemAbelian p E → Nat.card E ≤ p ^ 3 :=
    fun E hE hEel => card_le_of_le_u4TorusSylow h hp hE hEel
  have ht₀E : ∀ E : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K)),
      E ≤ u4TorusSylow (f := f) (K := K) p → IsElemAbelian p E → Nat.card E = p ^ 3 →
      t₀ ∈ E :=
    fun E hE hEel hcard =>
      mem_of_le_u4TorusSylow_of_card h hp hE hEel hcard ht₀P ht₀pow
  have hH1 : ∀ x ∈ u4TorusSylow (f := f) (K := K) p, ∀ k : ℕ, (Φ ^ m) ^ k ≠ 1 →
      (MulAut.conj x * (Φ ^ m) ^ k) ^ p = 1 →
      ∃ y ∈ u4TorusSylow (f := f) (K := K) p,
        MulAut.conj y * (MulAut.conj x * (Φ ^ m) ^ k) * (MulAut.conj y)⁻¹ =
          (Φ ^ m) ^ k := by
    intro x hxP k hk hkp
    have hk' : uFieldAut h (n := 4) (by norm_num) σ ^ (m * k) ≠ 1 := by
      rw [← hΦdef, pow_mul]
      exact hk
    have hkp' : (MulAut.conj x * uFieldAut h (n := 4) (by norm_num) σ ^ (m * k)) ^ p = 1 := by
      rw [← hΦdef, pow_mul]
      exact hkp
    obtain ⟨y, hyP, hyconj⟩ :=
      exists_conj_eq_uFieldAut_pow h hX hσ hp hp2 hpf hk' hxP hkp'
    refine ⟨y, hyP, ?_⟩
    rw [← pow_mul]
    simpa only [hΦdef] using hyconj
  have hm3 : 3 ^ (Nat.card Kˣ).factorization 3 ∣ 2 ^ m - 1 :=
    three_pow_factorization_dvd_two_pow_sub_one h hp hp2 hp3 h2f
  obtain ⟨S₃, hS₃, hS₃i, ht₀S, hΦS⟩ :=
    exists_sylow_three_u4_commute_fieldAut h hf hσ hm3 l hl1 hlm
  refine u45KeyDvdConcl_of_torus (X := StatedProj (StatedSU 4 (2 ^ f) K)) (p := p)
    (conj_injective_of_isU4 hX) hΦ hΦinn hm hΦm hP₀ hP₀i hP₀c hΦP hΩ ht₀ ht₀E hH1
    hS₃ hS₃i ht₀S hΦS

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
