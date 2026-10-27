module

public import CFSG.Quasithin.Background.RonanD39Block

public section

namespace CFSG.Quasithin.RonanD39

open scoped Pointwise
open CFSG.Quasithin.Z391 CFSG.QuasithinUnique

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem exists_fixed_ne_one_of_isPGroup [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {B : Subgroup Γ}
    (hB : IsPGroup 2 ↥B) {M : Subgroup Q} (hM : ∀ b ∈ B, ∀ m ∈ M, b • m ∈ M) (hne : M ≠ ⊥) :
    ∃ m ∈ M, m ≠ 1 ∧ ∀ b ∈ B, b • m = m := by
  let _ : MulAction ↥B ↥M :=
    { smul := fun b m => ⟨(b : Γ) • (m : Q), hM b b.2 m m.2⟩
      one_smul := fun m => Subtype.ext (one_smul Γ (m : Q))
      mul_smul := fun a b m => Subtype.ext (mul_smul (a : Γ) (b : Γ) (m : Q)) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM2 : IsPGroup 2 ↥M := (isPGroup_two_of_sq_eq_one hQ).to_subgroup M
  have hdvd : 2 ∣ Nat.card ↥M := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hM2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have h1 : (1 : ↥M) ∈ MulAction.fixedPoints ↥B ↥M := fun b =>
    Subtype.ext (smul_one (b : Γ))
  obtain ⟨m, hm, hne1⟩ := hB.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥M hdvd h1
  refine ⟨m, m.2, fun h => hne1 (Subtype.ext h.symm), fun b hb => ?_⟩
  exact congrArg Subtype.val (hm ⟨b, hb⟩)

theorem block_ineq {q : ℚ} {m a₁ d : ℕ} (hq1 : q ≤ 1) (hd : q * m + 1 ≤ d) (ha : a₁ ≤ m) :
    (2 : ℚ) ^ (m - a₁) * q * m ≤ q * a₁ + ((2 : ℚ) ^ (m - a₁) - 1) * d := by
  set j := m - a₁ with hj
  have hJ : (j : ℚ) + 1 ≤ (2 : ℚ) ^ j := by
    have := Nat.lt_two_pow_self (n := j)
    exact_mod_cast this
  have hX1 : (1 : ℚ) ≤ (2 : ℚ) ^ j := one_le_pow₀ (by norm_num)
  have e1 : ((2 : ℚ) ^ j - 1) * (q * m + 1) ≤ ((2 : ℚ) ^ j - 1) * d :=
    mul_le_mul_of_nonneg_left hd (by linarith)
  have e2 : (a₁ : ℚ) = m - j := by
    rw [hj, Nat.cast_sub ha]
    ring
  have e3 : q * j ≤ j := by
    have : (0 : ℚ) ≤ (1 - q) * j := mul_nonneg (by linarith) (Nat.cast_nonneg j)
    linarith
  rw [e2]
  nlinarith

theorem count_from [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ T A : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hT : IsSylowTwoOf T ⊤) (hAT : A ≤ T)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) (hVT : ∀ t ∈ T, t • V = V)
    (hgen : (⨆ g : Γ, g • V) = ⊤) {q : ℚ} (hq1 : q ≤ 1) (hd : q * rk ↥A + 1 ≤ rk ↥V)
    (hqB : ∀ (g : Γ) (A₁ : Subgroup Γ), A₁ ≤ A → A₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ T →
      q * rk ↥A₁ ≤ nB (A₁.map (MulAut.conj g⁻¹).toMonoidHom) V) :
    ∀ (n : ℕ) (P : Subgroup Q), rk Q - rk ↥P ≤ n → XMod.IsInv ↥Λ P → XMod.IsInv ↥A P →
      ∃ k : ℕ, LChain Λ (rk ↥V) P ⊤ k ∧ (k : ℚ) * q * rk ↥A ≤ nS A P ⊤ := by
  intro n
  induction n with
  | zero =>
    intro P hP hPΛ hPA
    have hPt : P = ⊤ := by
      have h1 : rk Q ≤ rk ↥P := by omega
      refine eq_of_le_of_rk_le hQ le_top ?_
      rwa [rk_top]
    subst hPt
    exact ⟨0, LChain.refl ⊤, by simp⟩
  | succ n ih =>
    intro P hP hPΛ hPA
    by_cases hPt : P = ⊤
    · subst hPt
      exact ⟨0, LChain.refl ⊤, by simp⟩
    obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Γ, ¬ g₀ • V ≤ P := by
      by_contra hcon
      push Not at hcon
      apply hPt
      rw [eq_top_iff, ← hgen]
      exact iSup_le hcon
    obtain ⟨P', g, A₁, hPP', hP'Λ, hP'A, hch, hA₁A, hBT, hcnt⟩ :=
      block_step hQ hΛ hT hAT hAc hA2 hV hVT hPΛ hPA hg₀
    have hrkP' : rk ↥P < rk ↥P' := by
      by_contra h
      exact hPP'.ne (eq_of_le_of_rk_le hQ hPP'.le (by omega))
    have hrkQ : rk ↥P' ≤ rk Q := by
      have := rk_mono (le_top : P' ≤ ⊤)
      rwa [rk_top] at this
    obtain ⟨k', hch', hcnt'⟩ := ih P' (by omega) hP'Λ hP'A
    refine ⟨2 ^ (rk ↥A - rk ↥A₁) + k', hch.trans hch', ?_⟩
    have h1 := nS_add_le hPP'.le le_top hP'A (B := A)
    have h3 := hqB g A₁ hA₁A hBT
    have hrkB : rk ↥(A₁.map (MulAut.conj g⁻¹).toMonoidHom) = rk ↥A₁ := rk_map_conj A₁ g⁻¹
    have hle : rk ↥A₁ ≤ rk ↥A := rk_mono hA₁A
    have hkey := block_ineq hq1 hd hle
    have h1' : (nS A P P' : ℚ) + (nS A P' ⊤ : ℚ) ≤ (nS A P ⊤ : ℚ) := by exact_mod_cast h1
    have hpow : 1 ≤ 2 ^ (rk ↥A - rk ↥A₁) := Nat.one_le_two_pow
    have h2' : (nB (A₁.map (MulAut.conj g⁻¹).toMonoidHom) V : ℚ) +
        ((2 : ℚ) ^ (rk ↥A - rk ↥A₁) - 1) * rk ↥V ≤ (nS A P P' : ℚ) := by
      have : ((2 ^ (rk ↥A - rk ↥A₁) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (rk ↥A - rk ↥A₁) - 1 := by
        rw [Nat.cast_sub hpow]
        push_cast
        ring
      rw [← this]
      exact_mod_cast hcnt
    push_cast
    nlinarith

theorem chief_count [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ T A : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hT : IsSylowTwoOf T ⊤) (hAT : A ≤ T)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA1 : A ≠ ⊥)
    {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) (hVT : ∀ t ∈ T, t • V = V)
    (hgen : (⨆ g : Γ, g • V) = ⊤) (hne : V ≠ ⊤) (hAQ : nB A (⊤ : Subgroup Q) ≤ 2 * rk ↥A)
    {q : ℚ}
    (hqB : ∀ (g : Γ) (A₁ : Subgroup Γ), A₁ ≤ A → A₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ T →
      q * rk ↥A₁ ≤ nB (A₁.map (MulAut.conj g⁻¹).toMonoidHom) V) :
    ∃ k : ℕ, LChain Λ (rk ↥V) (⊥ : Subgroup Q) ⊤ k ∧ (k : ℚ) * q ≤ 2 := by
  have hAp : IsPGroup 2 ↥A :=
    isPGroup_two_of_sq_eq_one fun x : ↥A => Subtype.ext (by simpa using hA2 _ x.2)
  have hrkA : 0 < rk ↥A := by
    by_contra h0
    have : rk ↥A = 0 := by omega
    exact hA1 ((rk_eq_zero_iff_of_isPGroup hAp).1 this)
  have hm : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrkA
  have hA1map : A.map (MulAut.conj (1 : Γ)⁻¹).toMonoidHom = A := by
    ext x
    rw [mem_conjMap]
    simp
  have hqA : q * rk ↥A ≤ nB A V := by
    have := hqB 1 A le_rfl (by rw [hA1map]; exact hAT)
    rwa [hA1map] at this
  have hAQ' : (nB A (⊤ : Subgroup Q) : ℚ) ≤ 2 * (rk ↥A : ℚ) := by exact_mod_cast hAQ
  have hq1 : q ≤ 1 := by
    obtain ⟨g, A₁, B, hA₁A, hBdef, hBT, hcount⟩ :=
      mackey_count hQ hΛ hT hAT hAc hA2 hV hVT hgen hne
    have h1 : q * rk ↥A₁ ≤ nB B V := by
      have := hqB g A₁ hA₁A (hBdef ▸ hBT)
      rwa [← hBdef] at this
    have hle : rk ↥A₁ ≤ rk ↥A := rk_mono hA₁A
    have hcount' : (nB A V : ℚ) + (nB B V : ℚ) + (rk ↥A : ℚ) ≤
        (nB A (⊤ : Subgroup Q) : ℚ) + (rk ↥A₁ : ℚ) := by
      have : nB A V + nB B V + rk ↥A ≤ nB A (⊤ : Subgroup Q) + rk ↥A₁ := by omega
      exact_mod_cast this
    have ha₁ : (0 : ℚ) ≤ (rk ↥A₁ : ℚ) := Nat.cast_nonneg _
    by_contra hcon
    have hcon' : 1 < q := not_le.1 hcon
    nlinarith [mul_pos (sub_pos.2 hcon') (add_pos_of_pos_of_nonneg hm ha₁)]
  have hd : q * rk ↥A + 1 ≤ rk ↥V := by
    have hAV : ∀ a ∈ A, ∀ v ∈ V, a • v ∈ V := by
      intro a ha v hv
      have h1 := Subgroup.smul_mem_pointwise_smul v a V hv
      rwa [hVT a (hAT ha)] at h1
    obtain ⟨v, hv, hv1, hvA⟩ := exists_fixed_ne_one_of_isPGroup hQ hAp hAV hV.2.1.ne'
    have hF : V ⊓ XMod.fixed ↥A (⊤ : Subgroup Q) ≠ ⊥ := by
      intro h
      have : v ∈ V ⊓ XMod.fixed ↥A (⊤ : Subgroup Q) :=
        ⟨hv, XMod.mem_fixed.2 ⟨trivial, fun a => hvA a a.2⟩⟩
      rw [h, Subgroup.mem_bot] at this
      exact hv1 this
    have hrkF : 1 ≤ rk ↥(V ⊓ XMod.fixed ↥A (⊤ : Subgroup Q)) := by
      by_contra h0
      have : rk ↥(V ⊓ XMod.fixed ↥A (⊤ : Subgroup Q)) = 0 := by omega
      exact hF ((rk_eq_zero_iff hQ).1 this)
    have hFV : rk ↥(V ⊓ XMod.fixed ↥A (⊤ : Subgroup Q)) ≤ rk ↥V := rk_mono inf_le_left
    have hn : nB A V + 1 ≤ rk ↥V := by
      unfold nB
      omega
    have : (nB A V : ℚ) + 1 ≤ (rk ↥V : ℚ) := by exact_mod_cast hn
    linarith
  obtain ⟨k, hch, hk⟩ := count_from hQ hΛ hT hAT hAc hA2 hV hVT hgen hq1 hd hqB (rk Q) ⊥
    (Nat.sub_le _ _) XMod.isInv_bot XMod.isInv_bot
  rw [nS_bot] at hk
  refine ⟨k, hch, ?_⟩
  have : (k : ℚ) * q * rk ↥A ≤ 2 * rk ↥A := hk.trans hAQ'
  nlinarith

end CFSG.Quasithin.RonanD39
