module

public import CFSG.RankThree.PartOne.HESS.SL2Swap
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.NF7J

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS

section SL2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sl2_nofix_core (ζ : Kˣ)
    (α : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hαinj : Function.Injective α) (n : ℕ) (hα : α (hmat ζ) = hmat ζ ^ n)
    (hU : ∀ M ∈ Uplus K, α M ∈ Uplus K) :
    ∃ k : ℕ, ((ζ : K) ^ 2) ^ n = ((ζ : K) ^ 2) ^ 2 ^ k := by
  have hαx : ∀ c : K, α (xp c) = xp (e2 (α (xp c)) 0 1) := fun c =>
    eq_xp_of_mem_Uplus (hU _ (xp_mem c))
  let β : K → K := fun c => e2 (α (xp c)) 0 1
  have hβ : ∀ c, α (xp c) = xp (β c) := hαx
  have hβadd : ∀ a b, β (a + b) = β a + β b := by
    intro a b
    have h1 : xp (β (a + b)) = xp (β a + β b) := by
      rw [← hβ, ← xp_mul, map_mul, hβ, hβ, xp_mul]
    exact xp_injective h1
  have hβ1 : β 1 ≠ 0 := by
    intro h
    have h1 : α (xp 1) = α 1 := by rw [hβ, h, xp_zero, map_one]
    have h2 : xp (1 : K) = 1 := hαinj h1
    have h3 : (1 : K) = 0 := xp_injective (h2.trans xp_zero.symm)
    exact one_ne_zero h3
  have hβmul : ∀ c, β ((ζ : K) ^ 2 * c) = ((ζ : K) ^ 2) ^ n * β c := by
    intro c
    have h1 := congrArg α (conj_hmat_xp ζ c)
    rw [map_mul, map_mul, map_inv, hα, hβ, hβ, hmat_pow, conj_hmat_xp] at h1
    have h2 := xp_injective h1
    rw [Units.val_pow_eq_pow_val] at h2
    rw [← h2]
    congr 1
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hβpow : ∀ (j : ℕ) (c : K),
      β (((ζ : K) ^ 2) ^ j * c) = ((((ζ : K) ^ 2) ^ n)) ^ j * β c := by
    intro j
    induction j with
    | zero => intro c; simp
    | succ j ih =>
      intro c
      have : ((ζ : K) ^ 2) ^ (j + 1) * c = (ζ : K) ^ 2 * (((ζ : K) ^ 2) ^ j * c) := by ring
      rw [this, hβmul, ih, pow_succ]
      ring
  exact exists_frob_pow_of_additive_twist ((ζ : K) ^ 2) (((ζ : K) ^ 2) ^ n)
    (AddMonoidHom.mk' β hβadd) hβ1 hβpow

end SL2

theorem no_two_pow_add_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ f - 1)
    (hodd : 2 ^ f % 3 = 2) (k : ℕ) : ¬ p ∣ 1 + 2 ^ k := by
  intro h
  have hp1 : 1 < p := hp.one_lt
  exact no_neg_pow_two_cube hp hp2 hdvd hodd (n := 1) (k := k) (by simpa using Nat.mod_eq_of_lt hp1)
    (Nat.mod_eq_zero_of_dvd h)

section Rule

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p f : ℕ}

theorem sl2_swap_rule_one (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (α : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hαinj : Function.Injective α) {n : ℕ} (hn : n % p = 1) (hα : α (hmat ζ) = hmat ζ ^ n) :
    ¬ ∀ M ∈ Uplus K, α M ∈ Uminus K := by
  intro hU
  obtain ⟨k, hk⟩ := sl2_no_swap_core ζ α hαinj n hα hU
  have hζk := zeta_pow_of_inv_pow_eq hk
  have hζk' : ζ ^ (2 * (n + 2 ^ k)) = 1 := by
    apply Units.ext
    simpa using hζk
  have hdvd' : p ∣ 2 * (n + 2 ^ k) := hζ.eq_orderOf ▸ orderOf_dvd_of_pow_eq_one hζk'
  have hdvd'' : p ∣ n + 2 ^ k := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd' with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
    · exact h
  have h1 : p ∣ 1 + 2 ^ k := by
    have hp1 : 1 < p := hp.one_lt
    have hn' : n ≡ 1 [MOD p] := by
      show n % p = 1 % p
      rw [hn, Nat.mod_eq_of_lt hp1]
    exact (Nat.ModEq.dvd_iff (Nat.ModEq.add_right (2 ^ k) hn') (dvd_refl p)).1 hdvd''
  exact no_two_pow_add_one hp hp2 hdvd hodd k h1

theorem sl2_swap_rule_neg (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (α : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hαinj : Function.Injective α) {n : ℕ} (hn : (n + 1) % p = 0) (hα : α (hmat ζ) = hmat ζ ^ n) :
    ¬ ∀ M ∈ Uplus K, α M ∈ Uplus K := by
  intro hU
  obtain ⟨k, hk⟩ := sl2_nofix_core ζ α hαinj n hα hU
  have hk' : ζ ^ (2 * n) = ζ ^ (2 * 2 ^ k) := by
    apply Units.ext
    simpa [pow_mul] using hk
  have hmod : 2 * n ≡ 2 * 2 ^ k [MOD p] := by
    have := (pow_eq_pow_iff_modEq (x := ζ)).1 hk'
    rwa [← hζ.eq_orderOf] at this
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hmod' : n ≡ 2 ^ k [MOD p] := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.gcd_comm] using hcop) hmod
  have h1 : p ∣ 1 + 2 ^ k := by
    have h3 : p ∣ n + 1 := Nat.dvd_of_mod_eq_zero hn
    have h4 : p ∣ 2 ^ k + 1 := (Nat.ModEq.dvd_iff (Nat.ModEq.add_right 1 hmod') (dvd_refl p)).1 h3
    rwa [add_comm] at h4
  exact no_two_pow_add_one hp hp2 hdvd hodd k h1

end Rule

theorem exists_endo_of_conj {G S : Type*} [Group G] [Group S] (φ : S →* G) (hφ : Function.Injective φ)
    (w : G) (hw : ∀ M : S, ∃ M' : S, φ M' = w * φ M * w⁻¹) :
    ∃ α : S →* S, Function.Injective α ∧ ∀ M, φ (α M) = w * φ M * w⁻¹ := by
  choose α hα using hw
  have hmul : ∀ M N, α (M * N) = α M * α N := by
    intro M N
    apply hφ
    rw [hα, map_mul, map_mul, hα, hα]
    group
  refine ⟨MonoidHom.mk' α hmul, ?_, hα⟩
  intro M N h
  apply hφ
  have h1 : φ (α M) = φ (α N) := congrArg φ h
  rw [hα, hα] at h1
  exact mul_left_cancel (mul_right_cancel h1)


section Frame

variable {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {p f : ℕ}

theorem frame_cases (φ : Matrix.SpecialLinearGroup (Fin 2) K →* G) (hφ : Function.Injective φ) {ζ : Kˣ}
    (hζ2 : ζ ^ 2 ≠ 1) {S : Subgroup G} (hS : S ≤ φ.range) (hsq : ∀ s ∈ S, s * s = 1)
    (hcard : Nat.card S = Nat.card K) (hb : ∀ s ∈ S, φ (hmat ζ) * s * (φ (hmat ζ))⁻¹ ∈ S) :
    S = (Uplus K).map φ ∨ S = (Uminus K).map φ := by
  set W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := S.comap φ with hW
  have hSW : W.map φ = S := by
    rw [hW, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hS
  have hWsq : ∀ M ∈ W, M * M = 1 := by
    intro M hM
    apply hφ
    rw [map_mul, map_one]
    exact hsq _ hM
  have hWn : ∀ M ∈ W, hmat ζ * M * (hmat ζ)⁻¹ ∈ W := by
    intro M hM
    have := hb (φ M) hM
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact this
  have hcardW : Nat.card W = Nat.card K := by
    rw [← hcard, ← hSW, Subgroup.card_map_of_injective hφ]
  rcases sl2_two_group_cases hζ2 hWsq hWn with h | h
  · left
    have : W = Uplus K := Subgroup.eq_of_le_of_card_ge h (by rw [card_Uplus, hcardW])
    rw [← hSW, this]
  · right
    have : W = Uminus K := Subgroup.eq_of_le_of_card_ge h (by rw [card_Uminus, hcardW])
    rw [← hSW, this]

theorem frame_rule (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2)
    (φ : Matrix.SpecialLinearGroup (Fin 2) K →* G) (hφ : Function.Injective φ) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) (w : G) (hw : ∀ M, ∃ M', φ M' = w * φ M * w⁻¹) {n : ℕ}
    (hn : w * φ (hmat ζ) * w⁻¹ = φ (hmat ζ) ^ n)
    (hcase : conjBy w ((Uplus K).map φ) = (Uplus K).map φ ∨
      conjBy w ((Uplus K).map φ) = (Uminus K).map φ) :
    (n % p = 1 → conjBy w ((Uplus K).map φ) = (Uplus K).map φ) ∧
      ((n + 1) % p = 0 → conjBy w ((Uplus K).map φ) = (Uminus K).map φ) := by
  obtain ⟨α, hαinj, hα⟩ := exists_endo_of_conj φ hφ w hw
  have hαh : α (hmat ζ) = hmat ζ ^ n := by
    apply hφ
    rw [hα, hn, map_pow]
  have hconj : ∀ M, φ (α M) = w * φ M * w⁻¹ := hα
  have hmem : ∀ M ∈ Uplus K, w * φ M * w⁻¹ ∈ conjBy w ((Uplus K).map φ) := fun M hM =>
    Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom (Subgroup.mem_map_of_mem φ hM)
  constructor
  · intro hn1
    rcases hcase with h | h
    · exact h
    · exfalso
      apply sl2_swap_rule_one hp hp2 hdvd hodd hζ α hαinj hn1 hαh
      intro M hM
      have h1 := hmem M hM
      rw [h] at h1
      obtain ⟨N, hN, hNe⟩ := h1
      have : α M = N := hφ (by rw [hconj, hNe])
      rw [this]
      exact hN
  · intro hn1
    rcases hcase with h | h
    · exfalso
      apply sl2_swap_rule_neg hp hp2 hdvd hodd hζ α hαinj hn1 hαh
      intro M hM
      have h1 := hmem M hM
      rw [h] at h1
      obtain ⟨N, hN, hNe⟩ := h1
      have : α M = N := hφ (by rw [hconj, hNe])
      rw [this]
      exact hN
    · exact h

end Frame

end CFSG.RankThree.PartOne.NF7J
