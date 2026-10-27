module

public import CFSG.Quasithin.Background.G64C512Ext

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type*} [CommGroup V] [Finite V]

theorem pow_twelve_of_transvections (hV2 : ∀ v : V, v ^ 2 = 1) {x y : MulAut V}
    (hx : Nat.card (commV (Subgroup.zpowers x)) = 2)
    (hy : Nat.card (commV (Subgroup.zpowers y)) = 2) : (x * y) ^ 12 = 1 := by
  classical
  set W := commV (Subgroup.zpowers x) ⊔ commV (Subgroup.zpowers y) with hW
  set z := x * y with hz
  have hW4 : Nat.card W ≤ 4 := by
    have := card_sup_le (commV (Subgroup.zpowers x)) (commV (Subgroup.zpowers y))
    rw [hx, hy] at this
    exact this
  have hzv : ∀ v : V, z v * v⁻¹ ∈ W := by
    intro v
    have h1 : x (y v) * (y v)⁻¹ ∈ W :=
      Subgroup.mem_sup_left (G6.mem_commV_of_mem (Subgroup.mem_zpowers x) (y v))
    have h2 : y v * v⁻¹ ∈ W :=
      Subgroup.mem_sup_right (G6.mem_commV_of_mem (Subgroup.mem_zpowers y) v)
    have : z v * v⁻¹ = (x (y v) * (y v)⁻¹) * (y v * v⁻¹) := by
      rw [hz, MulAut.mul_apply]
      group
    rw [this]
    exact W.mul_mem h1 h2
  have hzW : ∀ w ∈ W, z w ∈ W := by
    intro w hw
    have : z w = (z w * w⁻¹) * w := by group
    rw [this]
    exact W.mul_mem (hzv w) hw
  have hzkv : ∀ (k : ℕ) (v : V), (z ^ k) v * v⁻¹ ∈ W := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have : (z ^ (k + 1)) v * v⁻¹ = (z ((z ^ k) v) * ((z ^ k) v)⁻¹) * ((z ^ k) v * v⁻¹) := by
        rw [pow_succ', MulAut.mul_apply]
        group
      rw [this]
      exact W.mul_mem (hzv _) (ih v)
  have hzkW : ∀ (k : ℕ), ∀ w ∈ W, (z ^ k) w ∈ W := by
    intro k w hw
    have : (z ^ k) w = ((z ^ k) w * w⁻¹) * w := by group
    rw [this]
    exact W.mul_mem (hzkv k w) hw
  have hW6 : ∀ w ∈ W, (z ^ 6) w = w := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, map_one]
    have horb : ∃ d : ℕ, (d = 1 ∨ d = 2 ∨ d = 3) ∧ (z ^ d) w = w := by
      by_contra hcon
      push Not at hcon
      have h1 := hcon 1 (Or.inl rfl)
      have h2 := hcon 2 (Or.inr (Or.inl rfl))
      have h3 := hcon 3 (Or.inr (Or.inr rfl))
      have hne : ∀ i j : ℕ, i < j → j ≤ 3 → (z ^ i) w ≠ (z ^ j) w := by
        intro i j hij hj e
        have hd : (z ^ (j - i)) w = w := by
          have : z ^ j = z ^ i * z ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij.le]
          rw [this, MulAut.mul_apply] at e
          exact ((z ^ i).injective e).symm
        have hji : j - i = 1 ∨ j - i = 2 ∨ j - i = 3 := by omega
        rcases hji with e1 | e1 | e1 <;> rw [e1] at hd
        · exact h1 hd
        · exact h2 hd
        · exact h3 hd
      have hT : ({(z ^ 0) w, (z ^ 1) w, (z ^ 2) w, (z ^ 3) w} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]
          exact hne 2 3 (by norm_num) le_rfl
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hne 1 2 (by norm_num) (by norm_num), hne 1 3 (by norm_num) le_rfl⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hne 0 1 (by norm_num) (by norm_num), hne 0 2 (by norm_num) (by norm_num),
            hne 0 3 (by norm_num) le_rfl⟩
      have : Fintype V := Fintype.ofFinite V
      have hsub : ({(z ^ 0) w, (z ^ 1) w, (z ^ 2) w, (z ^ 3) w} : Finset V) ⊆
          (Finset.univ.filter fun u : V => u ∈ W ∧ u ≠ 1) := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hmem : ∀ k : ℕ, (z ^ k) w ∈ W ∧ (z ^ k) w ≠ 1 := fun k =>
          ⟨hzkW k w hw, fun h => hw1 (by simpa using congrArg (z ^ k).symm h)⟩
        rcases hu with h | h | h | h <;> rw [h] <;> exact hmem _
      have hle := Finset.card_le_card hsub
      rw [hT] at hle
      have hW' : (Finset.univ.filter fun u : V => u ∈ W ∧ u ≠ 1).card + 1 ≤ Nat.card W := by
        have hins : (Finset.univ.filter fun u : V => u ∈ W) =
            insert 1 (Finset.univ.filter fun u : V => u ∈ W ∧ u ≠ 1) := by
          ext u
          by_cases hu : u = 1 <;> simp [hu, W.one_mem]
        have hcW : Nat.card W = (Finset.univ.filter fun u : V => u ∈ W).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        rw [hcW, hins, Finset.card_insert_of_notMem (by simp)]
      omega
    obtain ⟨d, hd, hzd⟩ := horb
    have hpow : ∀ m : ℕ, (z ^ (d * m)) w = w := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.mul_succ, pow_add, MulAut.mul_apply, hzd, ih]
    rcases hd with rfl | rfl | rfl
    · simpa using hpow 6
    · simpa using hpow 3
    · simpa using hpow 2
  ext v
  have h6 := hzkv 6 v
  set w₁ := (z ^ 6) v * v⁻¹ with hw₁
  have hv : (z ^ 6) v = w₁ * v := by rw [hw₁]; group
  rw [MulAut.one_apply, show (12 : ℕ) = 6 + 6 from rfl, pow_add, MulAut.mul_apply, hv, map_mul,
    hW6 w₁ h6, hv, ← mul_assoc, ← sq, hV2, one_mul]

theorem cycleType_of_even_involution {n : ℕ} (hn : n ≤ 7) {σ : Perm (Fin n)} (hσ2 : σ ^ 2 = 1)
    (hσ1 : σ ≠ 1) (hsign : sign σ = 1) : σ.cycleType = {2, 2} := by
  have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have hmem : ∀ m ∈ σ.cycleType, m = 2 := by
    intro m hm
    have h2 := two_le_of_mem_cycleType hm
    have hd : m ∣ 2 := hord ▸ dvd_of_mem_cycleType hm
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.2 ⟨rfl, hmem⟩
  set c := Multiset.card σ.cycleType with hc
  have hsum : σ.cycleType.sum = 2 * c := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : 2 * c ≤ 7 := by
    rw [← hsum, sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simpa using hn)
  have hne : c ≠ 0 := by
    intro h0
    apply hσ1
    rw [← cycleType_eq_zero, hrep, h0]
    rfl
  have heven : Even (σ.cycleType.sum + c) := by
    have := sign_of_cycleType σ
    rw [hsign] at this
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at this
    exact absurd this (by decide)
  rw [hsum] at heven
  have hc2 : c = 2 := by
    rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
    · omega
    · exfalso
      rw [hk] at heven
      obtain ⟨m, hm⟩ := heven
      omega
  rw [hrep, hc2]
  rfl

theorem exists_conj_pow_twelve_ne_one {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) {σ : Perm (Fin n)}
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (hsign : sign σ = 1) :
    ∃ τ : Perm (Fin n), sign τ = 1 ∧ (σ * (τ * σ * τ⁻¹)) ^ 12 ≠ 1 := by
  have hn5 : 5 ≤ n := by omega
  have hn7 : n ≤ 7 := by omega
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  set i3 : Fin n := ⟨3, by omega⟩
  set i4 : Fin n := ⟨4, by omega⟩
  set σ₀ := swap i0 i1 * swap i2 i3 with hσ₀
  set g₀ := swap i1 i2 * swap i3 i4 with hg₀
  have hnd : [i0, i1, i2, i3].Nodup := by
    simp [i0, i1, i2, i3, Fin.ext_iff]
  have hct : σ.cycleType = σ₀.cycleType := by
    rw [cycleType_of_even_involution hn7 hσ2 hσ1 hsign, cycleType_swap_mul_swap_of_nodup hnd]
  obtain ⟨ρ, hρ⟩ := (isConj_iff.1 (isConj_iff_cycleType_eq.2 hct.symm))
  refine ⟨ρ * g₀ * ρ⁻¹, ?_, ?_⟩
  · rw [sign.map_mul, sign.map_mul, sign.map_inv, hg₀, sign.map_mul,
      sign_swap (by simp [i1, i2, Fin.ext_iff]), sign_swap (by simp [i3, i4, Fin.ext_iff])]
    simp [mul_comm]
  · rw [← hρ]
    have : ρ * σ₀ * ρ⁻¹ * (ρ * g₀ * ρ⁻¹ * (ρ * σ₀ * ρ⁻¹) * (ρ * g₀ * ρ⁻¹)⁻¹) =
        ρ * (σ₀ * (g₀ * σ₀ * g₀⁻¹)) * ρ⁻¹ := by group
    rw [this, conj_pow]
    intro h
    have h' : (σ₀ * (g₀ * σ₀ * g₀⁻¹)) ^ 12 = 1 := by
      have := congrArg (fun x => ρ⁻¹ * x * ρ) h
      simpa [mul_assoc] using this
    have hval := congrArg (fun f : Perm (Fin n) => f i0) h'
    simp only [Perm.one_apply] at hval
    rcases hn with rfl | rfl | rfl <;>
      simp [hσ₀, hg₀, i0, i1, i2, i3, i4, pow_succ, Perm.mul_apply, swap_apply_def] at hval

theorem false_of_alt_transvection (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7) (e : ↥(alternatingGroup (Fin n)) ≃* ↥L) {a : MulAut V}
    (haL : a ∈ L) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) : False := by
  set γ := e.symm ⟨a, haL⟩ with hγ
  have hγa : ((e γ : ↥L) : MulAut V) = a := by rw [hγ, MulEquiv.apply_symm_apply]
  set σ : Perm (Fin n) := (γ : Perm (Fin n)) with hσ
  have hγ2 : γ ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, hγa, ha2]; rfl)
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσ, ← Subgroup.coe_pow, hγ2]
    rfl
  have hσ1 : σ ≠ 1 := by
    intro h1
    have : γ = 1 := Subtype.ext h1
    apply ha1
    rw [← hγa, this, map_one]
    rfl
  have hsign : sign σ = 1 := (Equiv.Perm.mem_alternatingGroup).1 γ.2
  obtain ⟨τ, hτ, hne⟩ := exists_conj_pow_twelve_ne_one hn hσ2 hσ1 hsign
  set τ' : ↥(alternatingGroup (Fin n)) := ⟨τ, (Equiv.Perm.mem_alternatingGroup).2 hτ⟩
  set b : MulAut V := ((e (τ' * γ * τ'⁻¹) : ↥L) : MulAut V) with hb
  have hb' : b = ((e τ' : ↥L) : MulAut V) * a * ((e τ' : ↥L) : MulAut V)⁻¹ := by
    rw [hb, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hγa]
  have hbtr : Nat.card (commV (Subgroup.zpowers b)) = 2 := by
    rw [hb', G6.card_commV_zpowers_conj, htr]
  have h12 := pow_twelve_of_transvections hV2 htr hbtr
  apply hne
  have : (γ * (τ' * γ * τ'⁻¹)) ^ 12 = 1 := by
    apply e.injective
    rw [map_one, map_pow, map_mul]
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, Subgroup.coe_mul, hγa]
    exact h12
  have := congrArg (fun x : ↥(alternatingGroup (Fin n)) => (x : Perm (Fin n))) this
  simpa [σ, τ'] using this

end CFSG.Quasithin.G64
