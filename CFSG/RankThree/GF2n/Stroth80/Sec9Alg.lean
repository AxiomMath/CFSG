module

public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

open scoped commutatorElement

theorem sec9_sup_eq_of_card {G : Type} [Group G] [Finite G]
    {V W X₁ X₂ C : Subgroup G} {q n : ℕ}
    (hVW : V ≤ W) (hX₁ : X₁ ≤ W) (hX₂ : X₂ ≤ W)
    (hVc : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v)
    (hC : ∀ a ∈ W, ∀ b ∈ W, ⁅a, b⁆ ∈ C) (hCV : C ≤ V) (hCX₁ : C ≤ X₁) (hCX₂ : C ≤ X₂)
    (hq : 2 ≤ q) (hn : 3 ≤ n)
    (hW : Nat.card ↥W = q ^ (2 * n - 3)) (hV : Nat.card ↥V = q ^ 5)
    (hX₁c : Nat.card ↥X₁ = q ^ n) (hX₂c : Nat.card ↥X₂ = q ^ n)
    (hI : Nat.card ↥(X₁ ⊓ X₂) ≤ q ^ 3)
    (hVX₁ : Nat.card ↥(V ⊓ X₁) = q ^ 4) (hVX₂ : Nat.card ↥(V ⊓ X₂) = q ^ 4) :
    X₁ ⊔ X₂ = W := by
  have hq0 : 0 < q := by omega
  have hqpos : ∀ k : ℕ, 0 < q ^ k := fun k => pow_pos hq0 k
  have hconj : ∀ a b : G, a * b * a⁻¹ = ⁅a, b⁆ * b := by
    intro a b
    rw [commutatorElement_def]
    group
  have hnormW : ∀ A B : Subgroup G, B ≤ W → A ≤ W → C ≤ A →
      B ≤ Subgroup.normalizer (A : Set G) := by
    intro A B hBW hAW hCA x hx
    have hfwd : ∀ y ∈ B, ∀ h ∈ A, y * h * y⁻¹ ∈ A := by
      intro y hy h hh
      rw [hconj y h]
      exact A.mul_mem (hCA (hC y (hBW hy) h (hAW hh))) hh
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hfwd x hx h
    · intro hh
      have h1 := hfwd x⁻¹ (B.inv_mem hx) (x * h * x⁻¹) hh
      have h2 : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rwa [h2] at h1
  have hprod1 := card_sup_mul_card_inf_of_le_normalizer (hnormW X₁ X₂ hX₂ hX₁ hCX₁)
  rw [hX₁c, hX₂c] at hprod1
  have hpow1 : q ^ (2 * n - 3) * q ^ 3 = q ^ n * q ^ n := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hsup_ge : q ^ (2 * n - 3) ≤ Nat.card ↥(X₁ ⊔ X₂) := by
    refine Nat.le_of_mul_le_mul_right ?_ (hqpos 3)
    calc q ^ (2 * n - 3) * q ^ 3 = q ^ n * q ^ n := hpow1
      _ = Nat.card ↥(X₁ ⊔ X₂) * Nat.card ↥(X₁ ⊓ X₂) := hprod1.symm
      _ ≤ Nat.card ↥(X₁ ⊔ X₂) * q ^ 3 := Nat.mul_le_mul (le_refl _) hI
  exact Subgroup.eq_of_le_of_card_ge (sup_le hX₁ hX₂) (by rw [hW]; exact hsup_ge)

theorem sec9_exists_mul_of_card {G : Type} [Group G] [Finite G]
    {V W X₁ X₂ C : Subgroup G} {q n : ℕ}
    (hVW : V ≤ W) (hX₁ : X₁ ≤ W) (hX₂ : X₂ ≤ W)
    (hVc : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v)
    (hC : ∀ a ∈ W, ∀ b ∈ W, ⁅a, b⁆ ∈ C) (hCV : C ≤ V) (hCX₁ : C ≤ X₁) (hCX₂ : C ≤ X₂)
    (hq : 2 ≤ q) (hn : 3 ≤ n)
    (hW : Nat.card ↥W = q ^ (2 * n - 3)) (hV : Nat.card ↥V = q ^ 5)
    (hX₁c : Nat.card ↥X₁ = q ^ n) (hX₂c : Nat.card ↥X₂ = q ^ n)
    (hI : Nat.card ↥(X₁ ⊓ X₂) ≤ q ^ 3)
    (hVX₁ : Nat.card ↥(V ⊓ X₁) = q ^ 4) (hVX₂ : Nat.card ↥(V ⊓ X₂) = q ^ 4) :
    ∀ w ∈ W, ∃ x₁ ∈ X₁, ∃ x₂ ∈ X₂, w = x₁ * x₂ := by
  have hsup := sec9_sup_eq_of_card hVW hX₁ hX₂ hVc hC hCV hCX₁ hCX₂ hq hn hW hV hX₁c hX₂c hI
    hVX₁ hVX₂
  have hconj : ∀ a b : G, a * b * a⁻¹ = ⁅a, b⁆ * b := by
    intro a b
    rw [commutatorElement_def]
    group
  have hXN : X₂ ≤ Subgroup.normalizer (X₁ : Set G) := by
    intro x hx
    have hfwd : ∀ y ∈ X₂, ∀ h ∈ X₁, y * h * y⁻¹ ∈ X₁ := by
      intro y hy h hh
      rw [hconj y h]
      exact X₁.mul_mem (hCX₁ (hC y (hX₂ hy) h (hX₁ hh))) hh
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hfwd x hx h
    · intro hh
      have h1 := hfwd x⁻¹ (X₂.inv_mem hx) (x * h * x⁻¹) hh
      have h2 : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rwa [h2] at h1
  intro w hw
  have hwS : w ∈ X₁ ⊔ X₂ := by
    rw [hsup]
    exact hw
  have hwM : w ∈ ((X₁ ⊔ X₂ : Subgroup G) : Set G) := hwS
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X₁ X₂ hXN] at hwM
  obtain ⟨x₁, hx₁, x₂, hx₂, hprod⟩ := Set.mem_mul.1 hwM
  exact ⟨x₁, hx₁, x₂, hx₂, hprod.symm⟩

theorem sec9_directSum_of_card {G : Type} [Group G] [Finite G]
    {V W X₁ X₂ C : Subgroup G} {q n : ℕ}
    (hVW : V ≤ W) (hX₁ : X₁ ≤ W) (hX₂ : X₂ ≤ W)
    (hVc : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v)
    (hC : ∀ a ∈ W, ∀ b ∈ W, ⁅a, b⁆ ∈ C) (hCV : C ≤ V) (hCX₁ : C ≤ X₁) (hCX₂ : C ≤ X₂)
    (hq : 2 ≤ q) (hn : 3 ≤ n)
    (hW : Nat.card ↥W = q ^ (2 * n - 3)) (hV : Nat.card ↥V = q ^ 5)
    (hX₁c : Nat.card ↥X₁ = q ^ n) (hX₂c : Nat.card ↥X₂ = q ^ n)
    (hI : Nat.card ↥(X₁ ⊓ X₂) ≤ q ^ 3)
    (hVX₁ : Nat.card ↥(V ⊓ X₁) = q ^ 4) (hVX₂ : Nat.card ↥(V ⊓ X₂) = q ^ 4) :
    V ≤ X₁ ⊔ V ∧ X₁ ⊔ V ≤ W ∧ V ≤ X₂ ⊔ V ∧ X₂ ⊔ V ≤ W ∧
      (X₁ ⊔ V) ⊔ (X₂ ⊔ V) = W ∧ (X₁ ⊔ V) ⊓ (X₂ ⊔ V) = V := by
  have hq0 : 0 < q := by omega
  have hqpos : ∀ k : ℕ, 0 < q ^ k := fun k => pow_pos hq0 k
  have hconj : ∀ a b : G, a * b * a⁻¹ = ⁅a, b⁆ * b := by
    intro a b
    rw [commutatorElement_def]
    group
  have hnormW : ∀ A B : Subgroup G, B ≤ W → A ≤ W → C ≤ A →
      B ≤ Subgroup.normalizer (A : Set G) := by
    intro A B hBW hAW hCA x hx
    have hfwd : ∀ y ∈ B, ∀ h ∈ A, y * h * y⁻¹ ∈ A := by
      intro y hy h hh
      rw [hconj y h]
      exact A.mul_mem (hCA (hC y (hBW hy) h (hAW hh))) hh
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hfwd x hx h
    · intro hh
      have h1 := hfwd x⁻¹ (B.inv_mem hx) (x * h * x⁻¹) hh
      have h2 : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rwa [h2] at h1
  have hVN : ∀ A : Subgroup G, A ≤ W → V ≤ Subgroup.normalizer (A : Set G) := by
    intro A hAW v hv
    have hcen : ∀ h ∈ W, v * h * v⁻¹ = h := by
      intro h hh
      rw [hVc v hv h hh]
      group
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcen h (hAW hh)]
      exact hh
    · intro hh
      have hhW : h ∈ W := by
        have e : h = v⁻¹ * (v * h * v⁻¹) * v := by group
        rw [e]
        exact W.mul_mem (W.mul_mem (W.inv_mem (hVW hv)) (hAW hh)) (hVW hv)
      rw [hcen h hhW] at hh
      exact hh
  have hA1card : Nat.card ↥(X₁ ⊔ V) = q ^ (n + 1) := by
    have h := card_sup_mul_card_inf_of_le_normalizer (hVN X₁ hX₁)
    rw [inf_comm X₁ V, hVX₁, hX₁c, hV] at h
    apply Nat.eq_of_mul_eq_mul_right (hqpos 4)
    rw [h]
    ring
  have hA2card : Nat.card ↥(X₂ ⊔ V) = q ^ (n + 1) := by
    have h := card_sup_mul_card_inf_of_le_normalizer (hVN X₂ hX₂)
    rw [inf_comm X₂ V, hVX₂, hX₂c, hV] at h
    apply Nat.eq_of_mul_eq_mul_right (hqpos 4)
    rw [h]
    ring
  have hsupW : X₁ ⊔ X₂ = W :=
    sec9_sup_eq_of_card hVW hX₁ hX₂ hVc hC hCV hCX₁ hCX₂ hq hn hW hV hX₁c hX₂c hI hVX₁ hVX₂
  have hA1W : X₁ ⊔ V ≤ W := sup_le hX₁ hVW
  have hA2W : X₂ ⊔ V ≤ W := sup_le hX₂ hVW
  have hCA1 : C ≤ X₁ ⊔ V := hCV.trans le_sup_right
  have hprod2 := card_sup_mul_card_inf_of_le_normalizer
    (hnormW (X₁ ⊔ V) (X₂ ⊔ V) hA2W hA1W hCA1)
  have hsup12 : (X₁ ⊔ V) ⊔ (X₂ ⊔ V) = W := by
    refine le_antisymm (sup_le hA1W hA2W) ?_
    rw [← hsupW]
    exact sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right)
  have hpow2 : q ^ (n + 1) * q ^ (n + 1) = q ^ (2 * n - 3) * q ^ 5 := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hsup12, hW, hA1card, hA2card] at hprod2
  have hInfcard : Nat.card ↥((X₁ ⊔ V) ⊓ (X₂ ⊔ V)) = q ^ 5 := by
    apply Nat.eq_of_mul_eq_mul_left (hqpos (2 * n - 3))
    rw [hprod2, hpow2]
  have hVle : V ≤ (X₁ ⊔ V) ⊓ (X₂ ⊔ V) := le_inf le_sup_right le_sup_right
  have hcardK : Nat.card ↥((X₁ ⊔ V) ⊓ (X₂ ⊔ V)) ≤ Nat.card ↥V :=
    le_of_eq (by rw [hInfcard, hV])
  have hInf : (X₁ ⊔ V) ⊓ (X₂ ⊔ V) = V :=
    (Subgroup.eq_of_le_of_card_ge hVle hcardK).symm
  exact ⟨le_sup_right, hA1W, le_sup_right, hA2W, hsup12, hInf⟩

open scoped commutatorElement

theorem sec9_comm_le_of_prod {G : Type} [Group G]
    {N L₁ L₂ W X₁ X₂ V : Subgroup G}
    (hN : ∀ s ∈ N, ∃ a ∈ L₁ ⊓ N, ∃ b ∈ L₂ ⊓ N, s = a * b)
    (hW : ∀ w ∈ W, ∃ x₁ ∈ X₁, ∃ x₂ ∈ X₂, w = x₁ * x₂)
    (hX₁ : X₁ ≤ W) (hX₂ : X₂ ≤ W)
    (hVc : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v)
    (hNV : ∀ s ∈ N, ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (h11 : ∀ s ∈ L₁ ⊓ N, ∀ x ∈ X₁, ⁅s, x⁆ ∈ V) (h12 : ∀ s ∈ L₁ ⊓ N, ∀ x ∈ X₂, ⁅s, x⁆ ∈ V)
    (h21 : ∀ s ∈ L₂ ⊓ N, ∀ x ∈ X₁, ⁅s, x⁆ ∈ V) (h22 : ∀ s ∈ L₂ ⊓ N, ∀ x ∈ X₂, ⁅s, x⁆ ∈ V) :
    ∀ s ∈ N, ∀ w ∈ W, ⁅s, w⁆ ∈ V := by
  have key : ∀ a : G, ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂,
      ⁅a, x₁⁆ ∈ V → ⁅a, x₂⁆ ∈ V → ⁅a, x₁ * x₂⁆ ∈ V := by
    intro a x₁ hx₁ x₂ _ h1 h2
    have hcomm : ⁅a, x₂⁆ * x₁ = x₁ * ⁅a, x₂⁆ := hVc _ h2 x₁ (hX₁ hx₁)
    have hconj : x₁ * ⁅a, x₂⁆ * x₁⁻¹ = ⁅a, x₂⁆ := by
      rw [← hcomm, mul_inv_cancel_right]
    have e : ⁅a, x₁ * x₂⁆ = ⁅a, x₁⁆ * (x₁ * ⁅a, x₂⁆ * x₁⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, hconj]
    exact V.mul_mem h1 h2
  have keyW : ∀ a : G, (∀ x ∈ X₁, ⁅a, x⁆ ∈ V) → (∀ x ∈ X₂, ⁅a, x⁆ ∈ V) →
      ∀ w ∈ W, ⁅a, w⁆ ∈ V := by
    intro a h1 h2 w hw
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hW w hw
    exact key a x₁ hx₁ x₂ hx₂ (h1 x₁ hx₁) (h2 x₂ hx₂)
  have hL₁ : ∀ a ∈ L₁ ⊓ N, ∀ w ∈ W, ⁅a, w⁆ ∈ V :=
    fun a ha => keyW a (h11 a ha) (h12 a ha)
  have hL₂ : ∀ a ∈ L₂ ⊓ N, ∀ w ∈ W, ⁅a, w⁆ ∈ V :=
    fun a ha => keyW a (h21 a ha) (h22 a ha)
  intro s hs w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hN s hs
  have haN : a ∈ N := (Subgroup.mem_inf.mp ha).2
  have e : ⁅a * b, w⁆ = a * ⁅b, w⁆ * a⁻¹ * ⁅a, w⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem (hNV a haN _ (hL₂ b hb w hw)) (hL₁ a ha w hw)

theorem sec9_not_isPGroup_omegaPlusFour {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    ¬ IsPGroup 2 ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 2 K)) := by
  intro hP
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  have h16 : 16 ≤ Nat.card K ^ 2 := by nlinarith
  have hSLpos : Nat.card (CFSG.Open.StatedSL 2 K) ≠ 0 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_two K]
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hSLfin : Finite ↥(CFSG.Open.StatedSL 2 K) := Nat.finite_of_card_ne_zero hSLpos
  have hOmFin : Finite ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 2 K)) :=
    Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two K] at hn
  have hdvd : Nat.card K * (Nat.card K ^ 2 - 1) ∣ 2 ^ n := by
    rw [← hn]
    exact dvd_mul_right _ _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hqdvd : Nat.card K ∣ 2 ^ m := by
    rw [← hm]
    exact dvd_mul_right _ _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hqdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hi
    omega
  obtain ⟨c, hc⟩ : 2 ∣ Nat.card K := by
    rw [hi]
    exact dvd_pow_self 2 hi0
  have hr : Nat.card K ^ 2 - 1 ∣ 2 ^ m := Dvd.intro_left _ hm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hr
  have hq2 : Nat.card K ^ 2 = 4 * c ^ 2 := by
    rw [hc]
    ring
  cases j with
  | zero =>
    rw [pow_zero] at hj
    omega
  | succ j =>
    rw [pow_succ (2 : ℕ) j] at hj
    omega

theorem sec9_quot_equiv_map {G S : Type} [Group G] [Group S] {R N R₀ : Subgroup G}
    (hNR₀ : N ≤ R₀) (hR₀R : R₀ ≤ R) (ψ : ↥R →* S) (hker : ψ.ker = N.subgroupOf R)
    [hN : (N.subgroupOf R₀).Normal] :
    Nonempty ((↥R₀ ⧸ N.subgroupOf R₀) ≃* ↥((R₀.subgroupOf R).map ψ)) := by
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : ↥R₀ →* S, ∀ x : ↥R₀, ψ' x = ψ (Subgroup.inclusion hR₀R x) :=
    ⟨ψ.comp (Subgroup.inclusion hR₀R), fun _ => rfl⟩
  have hrange : ψ'.range = (R₀.subgroupOf R).map ψ := by
    ext s
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hR₀R x, x.2, (hψ' x).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hy⟩, hψ' _⟩
  have hker' : N.subgroupOf R₀ = ψ'.ker := by
    ext x
    rw [MonoidHom.mem_ker, hψ', ← MonoidHom.mem_ker, hker]
    exact Iff.rfl
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker').trans
    (QuotientGroup.quotientKerEquivRange ψ')).trans (MulEquiv.subgroupCongr hrange)⟩

open scoped commutatorElement

theorem sec9_exists_comm_ne_one {S : Type} [Group S] [IsSimpleGroup S]
    (h : ∃ a b : S, a * b ≠ b * a) {a : S} (ha : a ≠ 1) : ∃ s : S, ⁅s, a⁆ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hmem : a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hcon g
    rw [commutatorElement_def] at h1
    have h2 : g * a * g⁻¹ = a := by
      have := mul_inv_eq_one.mp h1
      simpa [mul_assoc] using this
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h2]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hmem
    exact ha hmem
  · obtain ⟨x, y, hxy⟩ := h
    have hx : x ∈ Subgroup.center S := by rw [ht]; exact Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)

theorem sec9_normal_sub_prod {S₁ S₂ : Type} [Group S₁] [Group S₂] [IsSimpleGroup S₁]
    [IsSimpleGroup S₂] (h₁ : ∃ a b : S₁, a * b ≠ b * a) (h₂ : ∃ a b : S₂, a * b ≠ b * a)
    (H : Subgroup (S₁ × S₂)) [H.Normal] (hbot : H ≠ ⊥) (htop : H ≠ ⊤) :
    Nonempty (↥H ≃* S₁) ∨ Nonempty (↥H ≃* S₂) := by
  let K₁ : Subgroup S₁ := H.comap (MonoidHom.inl S₁ S₂)
  let K₂ : Subgroup S₂ := H.comap (MonoidHom.inr S₁ S₂)
  have hmem₁ : ∀ c : S₁, c ∈ K₁ ↔ ((c, 1) : S₁ × S₂) ∈ H := fun c => Iff.rfl
  have hmem₂ : ∀ c : S₂, c ∈ K₂ ↔ ((1, c) : S₁ × S₂) ∈ H := fun c => Iff.rfl
  haveI hK₁ : K₁.Normal := ⟨fun c hc s => by
    rw [hmem₁] at hc ⊢
    have h1 := Subgroup.Normal.conj_mem inferInstance _ hc ((s, 1) : S₁ × S₂)
    simpa using h1⟩
  haveI hK₂ : K₂.Normal := ⟨fun c hc s => by
    rw [hmem₂] at hc ⊢
    have h1 := Subgroup.Normal.conj_mem inferInstance _ hc ((1, s) : S₁ × S₂)
    simpa using h1⟩
  have hP₁ : ∀ a : S₁, ∀ b : S₂, ((a, b) : S₁ × S₂) ∈ H → a ≠ 1 → K₁ = ⊤ := by
    intro a b hab ha1
    obtain ⟨s, hs⟩ := sec9_exists_comm_ne_one h₁ ha1
    have h1 : ((s, 1) : S₁ × S₂) * (a, b) * ((s, 1) : S₁ × S₂)⁻¹ * (a, b)⁻¹ ∈ H :=
      H.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hab _) (H.inv_mem hab)
    have e : ((s, 1) : S₁ × S₂) * (a, b) * ((s, 1) : S₁ × S₂)⁻¹ * (a, b)⁻¹ = (⁅s, a⁆, 1) := by
      refine Prod.ext ?_ ?_
      · simp [commutatorElement_def]
      · simp
    rw [e] at h1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K₁ with hb | ht
    · exfalso
      have : ⁅s, a⁆ ∈ K₁ := h1
      rw [hb, Subgroup.mem_bot] at this
      exact hs this
    · exact ht
  have hP₂ : ∀ a : S₁, ∀ b : S₂, ((a, b) : S₁ × S₂) ∈ H → b ≠ 1 → K₂ = ⊤ := by
    intro a b hab hb1
    obtain ⟨s, hs⟩ := sec9_exists_comm_ne_one h₂ hb1
    have h1 : ((1, s) : S₁ × S₂) * (a, b) * ((1, s) : S₁ × S₂)⁻¹ * (a, b)⁻¹ ∈ H :=
      H.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hab _) (H.inv_mem hab)
    have e : ((1, s) : S₁ × S₂) * (a, b) * ((1, s) : S₁ × S₂)⁻¹ * (a, b)⁻¹ = (1, ⁅s, b⁆) := by
      refine Prod.ext ?_ ?_
      · simp
      · simp [commutatorElement_def]
    rw [e] at h1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K₂ with hb | ht
    · exfalso
      have : ⁅s, b⁆ ∈ K₂ := h1
      rw [hb, Subgroup.mem_bot] at this
      exact hs this
    · exact ht
  have hex : ∃ a : S₁, ∃ b : S₂, ((a, b) : S₁ × S₂) ∈ H ∧ (a ≠ 1 ∨ b ≠ 1) := by
    by_contra hcon
    push Not at hcon
    apply hbot
    rw [eq_bot_iff]
    rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := hcon a b hab
    rw [Subgroup.mem_bot]
    simp [ha, hb]
  by_cases hA : ∃ a : S₁, ∃ b : S₂, ((a, b) : S₁ × S₂) ∈ H ∧ a ≠ 1
  · obtain ⟨a, b, hab, ha⟩ := hA
    have hK₁top := hP₁ a b hab ha
    by_cases hB : ∃ a : S₁, ∃ b : S₂, ((a, b) : S₁ × S₂) ∈ H ∧ b ≠ 1
    · obtain ⟨a', b', hab', hb'⟩ := hB
      have hK₂top := hP₂ a' b' hab' hb'
      exfalso
      apply htop
      rw [eq_top_iff]
      rintro ⟨c, d⟩ -
      have h1 : ((c, 1) : S₁ × S₂) ∈ H := by
        rw [← hmem₁, hK₁top]; exact Subgroup.mem_top c
      have h2 : ((1, d) : S₁ × S₂) ∈ H := by
        rw [← hmem₂, hK₂top]; exact Subgroup.mem_top d
      simpa using H.mul_mem h1 h2
    · push Not at hB
      left
      refine ⟨MulEquiv.ofBijective ((MonoidHom.fst S₁ S₂).comp H.subtype) ⟨?_, ?_⟩⟩
      · intro x y hxy
        have hx2 : x.1.2 = 1 := hB x.1.1 x.1.2 (by simpa using x.2)
        have hy2 : y.1.2 = 1 := hB y.1.1 y.1.2 (by simpa using y.2)
        exact Subtype.ext (Prod.ext hxy (by rw [hx2, hy2]))
      · intro c
        have : ((c, 1) : S₁ × S₂) ∈ H := by
          rw [← hmem₁, hK₁top]; exact Subgroup.mem_top c
        exact ⟨⟨(c, 1), this⟩, rfl⟩
  · push Not at hA
    obtain ⟨a, b, hab, hne⟩ := hex
    have hb : b ≠ 1 := by
      rcases hne with h | h
      · exact absurd (hA a b hab) h
      · exact h
    have hK₂top := hP₂ a b hab hb
    right
    refine ⟨MulEquiv.ofBijective ((MonoidHom.snd S₁ S₂).comp H.subtype) ⟨?_, ?_⟩⟩
    · intro x y hxy
      have hx1 : x.1.1 = 1 := hA x.1.1 x.1.2 (by simpa using x.2)
      have hy1 : y.1.1 = 1 := hA y.1.1 y.1.2 (by simpa using y.2)
      exact Subtype.ext (Prod.ext (by rw [hx1, hy1]) hxy)
    · intro c
      have : ((1, c) : S₁ × S₂) ∈ H := by
        rw [← hmem₂, hK₂top]; exact Subgroup.mem_top c
      exact ⟨⟨(1, c), this⟩, rfl⟩

end CFSG.RankThree.GF2n.Stroth80
