module

public import CFSG.Quasithin.Background.SmithB45U3Irr

public section

namespace CFSG.Quasithin.B45U3

open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SmithCurtis
open scoped MatrixGroups Matrix

@[expose] def wtJ (s : ℕ) (a b : Fin s → Bool) : ℕ := mBits a + 2 ^ s * mBits b

variable {s : ℕ}

theorem exists_mBits_eq {m : ℕ} (hm : m < 2 ^ s) : ∃ a : Fin s → Bool, mBits a = m := by
  classical
  let f : (Fin s → Bool) → Fin (2 ^ s) := fun a => ⟨mBits a, mBits_lt a⟩
  have hf : Function.Injective f := fun a a' h => mBits_injective (congrArg Fin.val h)
  have hcard : Fintype.card (Fin s → Bool) = Fintype.card (Fin (2 ^ s)) := by simp
  obtain ⟨a, ha⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩).2 ⟨m, hm⟩
  exact ⟨a, congrArg Fin.val ha⟩

theorem exists_wtJ_eq {e : ℕ} (he : e < (2 ^ s) ^ 2) : ∃ a b : Fin s → Bool, wtJ s a b = e := by
  have hq : 0 < 2 ^ s := by positivity
  obtain ⟨a, ha⟩ := exists_mBits_eq (Nat.mod_lt e hq)
  obtain ⟨b, hb⟩ := exists_mBits_eq (s := s) (m := e / 2 ^ s)
    (Nat.div_lt_of_lt_mul (by rw [← sq]; exact he))
  exact ⟨a, b, by rw [wtJ, ha, hb, Nat.mod_add_div]⟩

theorem wtJ_zeros : wtJ s (zeros s) (zeros s) = 0 := by
  simp [wtJ, mBits_zeros]

theorem wtJ_ones : wtJ s (ones s) (ones s) = (2 ^ s) ^ 2 - 1 := by
  rw [wtJ, mBits_ones]
  have hq : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  zify [hq, Nat.one_le_pow 2 (2 ^ s) (by positivity)]
  ring

theorem eq_zeros_of_wtJ {a b : Fin s → Bool} (h : wtJ s a b = 0) : a = zeros s ∧ b = zeros s := by
  have h' := h
  unfold wtJ at h'
  have hq : 0 < 2 ^ s := by positivity
  have hb : mBits b = 0 := by
    rcases Nat.eq_zero_or_pos (mBits b) with h0 | h0
    · exact h0
    · nlinarith
  rw [hb, mul_zero, add_zero] at h'
  exact ⟨mBits_eq_zero h', mBits_eq_zero hb⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable (k : Type) [Field k] [Algebra K k] [CharP k 2]

omit [CharP K 2] [CharP k 2] in
theorem exists_exponent (c : Kˣ → k) (hmul : ∀ r r', c (r * r') = c r * c r') (hone : c 1 = 1) :
    ∃ e < Nat.card Kˣ, ∀ r : Kˣ, c r = algebraMap K k (r : K) ^ e := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hN : 0 < Nat.card Kˣ := Nat.card_pos
  have hprim : IsPrimitiveRoot (algebraMap K k (g : K)) (Nat.card Kˣ) := by
    have h1 : IsPrimitiveRoot (g : K) (Nat.card Kˣ) := by
      rw [← hord, ← orderOf_units]
      exact IsPrimitiveRoot.orderOf _
    exact h1.map_of_injective (algebraMap K k).injective
  have hpow : ∀ (r : Kˣ) (n : ℕ), c (r ^ n) = c r ^ n := by
    intro r n
    induction n with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcN : c g ^ Nat.card Kˣ = 1 := by rw [← hpow, pow_card_eq_one', hone]
  obtain ⟨e, heN, he⟩ := hprim.eq_pow_of_pow_eq_one hcN
  refine ⟨e, heN, fun r => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, g ^ j = r :=
    (mem_powers_iff_mem_zpowers.mpr (hg r))
  rw [hpow, ← he, ← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, map_pow]

variable {s : ℕ}

theorem TJ_isCurtisType (hK : Nat.card K = (2 ^ s) ^ 2) (a b : Fin s → Bool)
    (χ : suJ K s → k) (hχ : ∀ r : Kˣ, χ (hJ hK r) = algebraMap K k (r : K) ^ wtJ s a b) :
    ∃ μ : Fin 1 → k, (datumJ hK).IsCurtisType (matRep (TJ (K := K) k a b)) (hw k a b) χ μ := by
  have hfix : hw k a b ∈ (datumJ hK).fixU (matRep (TJ (K := K) k a b)) := by
    intro u hu
    obtain ⟨x, y, z, hxyz⟩ := mem_upperUni.mp (mem_UJ.mp hu)
    rw [matRep_apply, TJ_apply, hxyz]
    exact tensorRep_up3_fixed k a b x y z
  have hT : ∀ i : Fin 1, ∃ c : k,
      (datumJ hK).heckeT (matRep (TJ (K := K) k a b)) i (hw k a b) = c • hw k a b := by
    intro i
    have h1 := (datumJ hK).heckeT_mem_fixU (matRep (TJ (K := K) k a b)) i hfix
    have h2 : (datumJ hK).heckeT (matRep (TJ (K := K) k a b)) i (hw k a b) ∈
        fixedSub (matRep (TJ (K := K) k a b)) (UJ K s) := h1
    rw [(TJ_fixed_irreducible k hK a b).1, Submodule.mem_span_singleton] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, hc.symm⟩
  choose μ hμ using hT
  refine ⟨μ, hfix, hw_ne_zero k a b, fun h hh => ?_, hμ⟩
  obtain ⟨r, rfl⟩ := hh
  rw [matRep_apply, TJ_hJ_hw k hK, hχ]
  rfl

omit [CharP k 2] in
theorem repEquiv_apply {G V W : Type*} [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    (φ : ρ.Equiv σ) (g : G) (v : V) : φ (ρ g v) = σ g (φ v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v

omit [CharP k 2] in
theorem nonempty_equiv_of_iso {G V W : Type*} [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    (β : V ≃ₗ[k] W) (hβ : ∀ g v, β (ρ g v) = σ g (β v)) : Nonempty (ρ.Equiv σ) :=
  ⟨Representation.Equiv.mk β fun g => LinearMap.ext fun v => hβ g v⟩

theorem exists_TJ_equiv (hK : Nat.card K = (2 ^ s) ^ 2) {V : Type*} [AddCommGroup V]
    [Module k V] (σ : Representation k (suJ K s) V) (hσ : σ.IsIrreducible) :
    ∃ a b : Fin s → Bool, Nonempty ((matRep (TJ (K := K) k a b)).Equiv σ) := by
  classical
  have hρ : IsSimpleRep σ := (isIrreducible_iff σ).mp hσ
  obtain ⟨y, χ, μ, ht⟩ := (datumJ hK).exists_isCurtisType (splitOver_HJ hK k) hρ
  have hmul : ∀ r r' : Kˣ, χ (hJ hK (r * r')) = χ (hJ hK r) * χ (hJ hK r') := fun r r' => by
    rw [map_mul]
    exact ht.chi_mul ⟨r, rfl⟩ ⟨r', rfl⟩
  have hone : χ (hJ hK 1) = 1 := by rw [map_one]; exact ht.chi_one
  have hU : Nat.card Kˣ = (2 ^ s) ^ 2 - 1 := by rw [Nat.card_units, hK]
  obtain ⟨e, he, hce⟩ := exists_exponent k (fun r => χ (hJ hK r)) hmul hone
  rw [hU] at he
  have hTirr : ∀ a b : Fin s → Bool, IsSimpleRep (matRep (TJ (K := K) k a b)) := fun a b =>
    (isIrreducible_iff _).mp (TJ_fixed_irreducible k hK a b).2
  by_cases hc : ∀ r : Kˣ, χ (hJ hK r) = 1
  ·
    obtain ⟨μ₀, ht₀⟩ := TJ_isCurtisType k hK (zeros s) (zeros s) χ fun r => by
      rw [hc r, wtJ_zeros, pow_zero]
    obtain ⟨μ₁, ht₁⟩ := TJ_isCurtisType k hK (ones s) (ones s) χ fun r => by
      rw [hc r, wtJ_ones, ← map_pow, ← Units.val_pow_eq_pow_val, units_pow_sq_sub_one hK r,
        Units.val_one, map_one]
    have hne : μ₀ 0 ≠ μ₁ 0 := by
      intro h
      have hμ : μ₀ = μ₁ := funext fun i => by rw [Subsingleton.elim i 0]; exact h
      subst hμ
      obtain ⟨β, -⟩ := (datumJ hK).iso_of_isCurtisType (hTirr _ _) (hTirr _ _) ht₀ ht₁
      have h1 := β.finrank_eq
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
        card_TIdx_ones] at h1
      have h2 : Fintype.card (TIdx s (zeros s) (zeros s)) = 1 := by
        rw [card_TIdx]
        simp [zeros, locDim]
      rw [h2] at h1
      have hs := one_le_s hK
      have : 1 < 8 ^ s := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    have hμ : μ 0 = μ₀ 0 ∨ μ 0 = μ₁ 0 := by
      rcases ht.mu_eq 0 with h | h <;> rcases ht₀.mu_eq 0 with h0 | h0 <;>
        rcases ht₁.mu_eq 0 with h1 | h1
      all_goals first
        | exact Or.inl (h.trans h0.symm)
        | exact Or.inr (h.trans h1.symm)
        | exact absurd (h0.trans h1.symm) hne
    rcases hμ with h | h
    · have hμ : μ = μ₀ := funext fun i => by rw [Subsingleton.elim i 0]; exact h
      subst hμ
      obtain ⟨β, hβ⟩ := (datumJ hK).iso_of_isCurtisType (hTirr _ _) hρ ht₀ ht
      exact ⟨zeros s, zeros s, nonempty_equiv_of_iso k β hβ⟩
    · have hμ : μ = μ₁ := funext fun i => by rw [Subsingleton.elim i 0]; exact h
      subst hμ
      obtain ⟨β, hβ⟩ := (datumJ hK).iso_of_isCurtisType (hTirr _ _) hρ ht₁ ht
      exact ⟨ones s, ones s, nonempty_equiv_of_iso k β hβ⟩
  ·
    push Not at hc
    have hd := d'Scalar_eq_zero hK χ hmul (by rw [← map_one (hJ hK)]; exact hone) hc
    obtain ⟨a, b, hab⟩ := exists_wtJ_eq (s := s) (he.trans (Nat.sub_lt (by positivity) one_pos))
    obtain ⟨μ', ht'⟩ := TJ_isCurtisType k hK a b χ fun r => by rw [hce r, hab]
    have hμ : μ = μ' := funext fun i => by
      rcases ht.mu_eq i with h | h <;> rcases ht'.mu_eq i with h' | h'
      · rw [h, h']
      · rw [h, h', hd]
      · rw [h, h', hd]
      · rw [h, h']
    subst hμ
    obtain ⟨β, hβ⟩ := (datumJ hK).iso_of_isCurtisType (hTirr _ _) hρ ht' ht
    exact ⟨a, b, nonempty_equiv_of_iso k β hβ⟩

end CFSG.Quasithin.B45U3
