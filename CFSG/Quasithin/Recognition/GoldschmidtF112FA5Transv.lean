module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin

namespace FA5

section Aut

variable {V : Type*} [Group V]

@[expose] def fixSub (σ : MulAut V) : Subgroup V where
  carrier := {v | σ v = v}
  mul_mem' := by
    intro a b ha hb
    change σ (a * b) = a * b
    rw [map_mul, (ha : σ a = a), (hb : σ b = b)]
  one_mem' := by
    change σ 1 = 1
    exact map_one σ
  inv_mem' := by
    intro a ha
    change σ a⁻¹ = a⁻¹
    rw [map_inv, (ha : σ a = a)]

theorem mem_fixSub {σ : MulAut V} {v : V} : v ∈ fixSub σ ↔ σ v = v := Iff.rfl

theorem fixSub_conj (α σ : MulAut V) :
    fixSub (α * σ * α⁻¹) = (fixSub σ).map α.toMonoidHom := by
  ext v
  rw [Subgroup.mem_map_equiv]
  change α (σ (α.symm v)) = v ↔ σ (α.symm v) = α.symm v
  constructor
  · intro h
    simpa using congrArg α.symm h
  · intro h
    rw [h]
    simp

theorem index_fixSub_conj (α σ : MulAut V) :
    (fixSub (α * σ * α⁻¹)).index = (fixSub σ).index := by
  rw [fixSub_conj]
  exact Subgroup.index_map_equiv _ α

variable [Finite V]

theorem eq_one_of_fix_index_le_four (hV2 : ∀ a : V, a * a = 1) {K : Subgroup V}
    (hK : K.index ≤ 4) {x : MulAut V} (hxK : ∀ k ∈ K, x k = k) (hx5 : x ^ 5 = 1) : x = 1 := by
  have hpow : ∀ (n : ℕ), ∀ k ∈ K, (x ^ n) k = k := by
    intro n k hk
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hxK k hk, ih]
  have hinj : ∀ (n : ℕ) (a b : V), (x ^ n) a = (x ^ n) b → a = b :=
    fun n a b h => (x ^ n).injective h
  have hmexists : ∀ e : ℕ, 0 < e → e < 5 → ∃ m : ℕ, e * m % 5 = 1 := by
    intro e he0 he5
    interval_cases e
    · exact ⟨1, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨4, by norm_num⟩
  ext v
  show x v = v
  have : Fintype V := Fintype.ofFinite V
  have : DecidableEq (V ⧸ K) := Classical.decEq _
  have : Fintype (V ⧸ K) := Fintype.ofFinite _
  have hcard : Fintype.card (V ⧸ K) < Fintype.card (Fin 5) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    have : Nat.card (V ⧸ K) = K.index := (Subgroup.index_eq_card K).symm
    omega
  obtain ⟨i, j, hij, hEq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j : Fin 5 => (QuotientGroup.mk ((x ^ (j : ℕ)) v) : V ⧸ K)) hcard
  have aux : ∀ i j : ℕ, i < j → j < 5 →
      (QuotientGroup.mk ((x ^ i) v) : V ⧸ K) = QuotientGroup.mk ((x ^ j) v) →
      ∃ e : ℕ, 0 < e ∧ e < 5 ∧ v⁻¹ * (x ^ e) v ∈ K := by
    intro i j hlt hj h
    refine ⟨j - i, by omega, by omega, ?_⟩
    have h1 : ((x ^ i) v)⁻¹ * (x ^ j) v ∈ K := QuotientGroup.eq.mp h
    have hj' : x ^ j = x ^ i * x ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    have h2 : ((x ^ i) v)⁻¹ * (x ^ j) v = (x ^ i) (v⁻¹ * (x ^ (j - i)) v) := by
      rw [hj', MulAut.mul_apply, map_mul, map_inv]
    rw [h2] at h1
    have h3 := hpow i _ h1
    have h4 : (x ^ i) (v⁻¹ * (x ^ (j - i)) v) = v⁻¹ * (x ^ (j - i)) v := hinj i _ _ h3
    rwa [h4] at h1
  have key : ∃ e : ℕ, 0 < e ∧ e < 5 ∧ v⁻¹ * (x ^ e) v ∈ K := by
    have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hij' with h | h
    · exact aux i j h j.isLt hEq
    · exact aux j i h i.isLt hEq.symm
  obtain ⟨e, he0, he5, hw0⟩ := key
  obtain ⟨m, hm⟩ := hmexists e he0 he5
  obtain ⟨w, hwdef⟩ : ∃ w : V, w = v⁻¹ * (x ^ e) v := ⟨_, rfl⟩
  have hw : w ∈ K := hwdef ▸ hw0
  have hxe : (x ^ e) v = v * w := by rw [hwdef]; group
  have hmul : ∀ m : ℕ, (x ^ (e * m)) v = v * w ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, pow_add, MulAut.mul_apply, hxe, map_mul, ih, hpow _ _ hw, pow_succ,
        mul_assoc]
  have hxpow : x ^ (e * m) = x := by
    have : e * m = 5 * (e * m / 5) + 1 := by omega
    rw [this, pow_add, pow_mul, hx5, one_pow, one_mul, pow_one]
  obtain ⟨k, hk⟩ : ∃ k : V, k = w ^ m := ⟨_, rfl⟩
  have hkK : k ∈ K := hk ▸ K.pow_mem hw m
  have hxv : x v = v * k := by
    have := hmul m
    rwa [hxpow, ← hk] at this
  have hn : ∀ n : ℕ, (x ^ n) v = v * k ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, hxv, map_mul, ih, hpow n k hkK, pow_succ, mul_assoc]
  have h5 := hn 5
  rw [hx5] at h5
  have hk5 : k ^ 5 = 1 := by
    have : v * k ^ 5 = v * 1 := by
      rw [mul_one]
      exact h5.symm
    exact mul_left_cancel this
  have hk1 : k = 1 := by
    have h2 : k ^ 5 = k := by
      have hkk := hV2 k
      calc k ^ 5 = (k * k) * (k * k) * k := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = k := by rw [hkk]; simp
    rw [← h2]
    exact hk5
  rw [hxv, hk1, mul_one]

theorem eq_one_of_transvections (hV2 : ∀ a : V, a * a = 1) {σ τ : MulAut V}
    (hσ : (fixSub σ).index ≤ 2) (hτ : (fixSub τ).index ≤ 2)
    (h5 : (σ * τ) ^ 5 = 1) : σ * τ = 1 := by
  refine eq_one_of_fix_index_le_four hV2 (K := fixSub σ ⊓ fixSub τ) ?_ ?_ h5
  · calc (fixSub σ ⊓ fixSub τ).index ≤ (fixSub σ).index * (fixSub τ).index :=
          Subgroup.index_inf_le
      _ ≤ 2 * 2 := Nat.mul_le_mul hσ hτ
      _ = 4 := by norm_num
  · intro k hk
    rw [MulAut.mul_apply, mem_fixSub.mp hk.2, mem_fixSub.mp hk.1]

theorem eq_one_of_inverted_transvection (hV2 : ∀ a : V, a * a = 1) {ξ ζ : MulAut V}
    (hξ5 : ξ ^ 5 = 1) (hζ2 : ζ ^ 2 = 1)
    (hinv : ζ * ξ * ζ⁻¹ = ξ⁻¹) (hidx : (fixSub ζ).index ≤ 2) : ξ = 1 := by
  have hτ : (fixSub (ξ * ζ * ξ⁻¹)).index ≤ 2 := by
    rw [index_fixSub_conj]
    exact hidx
  have hprod : ζ * (ξ * ζ * ξ⁻¹) = ξ⁻¹ * ξ⁻¹ := by
    calc ζ * (ξ * ζ * ξ⁻¹) = (ζ * ξ * ζ⁻¹) * (ζ ^ 2) * ξ⁻¹ := by group
      _ = ξ⁻¹ * ξ⁻¹ := by rw [hinv, hζ2]; group
  have h5 : (ζ * (ξ * ζ * ξ⁻¹)) ^ 5 = 1 := by
    rw [hprod]
    calc (ξ⁻¹ * ξ⁻¹) ^ 5 = (ξ ^ 5)⁻¹ * (ξ ^ 5)⁻¹ := by group
      _ = 1 := by rw [hξ5]; simp
  have h1 : ζ * (ξ * ζ * ξ⁻¹) = 1 := eq_one_of_transvections hV2 hidx hτ h5
  rw [hprod] at h1
  calc ξ = (ξ ^ 5) * (ξ⁻¹ * ξ⁻¹) * (ξ⁻¹ * ξ⁻¹) := by group
    _ = 1 := by rw [h1, hξ5]; simp

omit [Finite V] in
theorem exists_involution_conj_order_five :
    ∀ a : alternatingGroup (Fin 5), a ≠ 1 → a ^ 2 = 1 →
      ∃ g : alternatingGroup (Fin 5), (a * (g * a * g⁻¹)) ^ 5 = 1 ∧ a * (g * a * g⁻¹) ≠ 1 := by
  decide +kernel

theorem alt5_trivial_of_transvection (hV2 : ∀ a : V, a * a = 1)
    {ρ : alternatingGroup (Fin 5) →* MulAut V}
    {a : alternatingGroup (Fin 5)} (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hidx : (fixSub (ρ a)).index ≤ 2) (g : alternatingGroup (Fin 5)) : ρ g = 1 := by
  obtain ⟨c, hc5, hc1⟩ := exists_involution_conj_order_five a ha1 ha2
  have hτ : (fixSub (ρ (c * a * c⁻¹))).index ≤ 2 := by
    rw [map_mul, map_mul, map_inv, index_fixSub_conj]
    exact hidx
  have h5 : (ρ a * ρ (c * a * c⁻¹)) ^ 5 = 1 := by
    rw [← map_mul, ← map_pow, hc5, map_one]
  have h1 : ρ a * ρ (c * a * c⁻¹) = 1 := eq_one_of_transvections hV2 hidx hτ h5
  have hu : (a * (c * a * c⁻¹)) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact h1
  have hne : ρ.ker ≠ ⊥ := fun h => hc1 (by simpa [h] using hu)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have htop : ρ.ker = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker).resolve_left hne
  have : g ∈ ρ.ker := htop ▸ Subgroup.mem_top g
  exact MonoidHom.mem_ker.mp this

end Aut

end FA5

end CFSG.Quasithin
