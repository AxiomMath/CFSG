module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.Quasithin.A4

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin

theorem eq_one_of_odd_conj {Γ : Type*} [Group Γ] {a d β : Γ} {m j : ℕ} (hm : Odd m)
    (ham : a ^ m = 1) (had : a * d * a⁻¹ = β * d) (haβ : a * β * a⁻¹ = β)
    (hβ : β ^ 2 ^ j = 1) : β = 1 := by
  have hk : ∀ k : ℕ, a ^ k * d * (a ^ k)⁻¹ = β ^ k * d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : a ^ (k + 1) * d * (a ^ (k + 1))⁻¹ = a * (a ^ k * d * (a ^ k)⁻¹) * a⁻¹ := by
        group
      have h2 : a * β ^ k * a⁻¹ = β ^ k := by
        rw [← conj_pow, haβ]
      calc a ^ (k + 1) * d * (a ^ (k + 1))⁻¹ = a * (β ^ k * d) * a⁻¹ := by rw [h1, ih]
        _ = (a * β ^ k * a⁻¹) * (a * d * a⁻¹) := by group
        _ = β ^ (k + 1) * d := by rw [h2, had, pow_succ]; group
  have h3 : β ^ m = 1 := by
    have := hk m
    rw [ham] at this
    simpa using this.symm
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
  have h4 : orderOf β = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hβ) (orderOf_dvd_of_pow_eq_one h3)
  exact orderOf_eq_one_iff.mp h4

variable {G : Type*} [Group G]

theorem card_lt_of_lt [Finite G] {H K : Subgroup G} (h : H < K) : Nat.card H < Nat.card K :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le)
    fun heq => h.ne (Subgroup.eq_of_le_of_card_ge h.le heq.ge)

theorem commutator_mem_of_series {N B D : Subgroup G} {a : G} (ha : Odd (orderOf a))
    (haN : a ∈ Subgroup.normalizer (N : Set G)) (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hBD : B ≤ D) (hD : ∀ d ∈ D, ∃ j : ℕ, d ^ 2 ^ j ∈ N)
    (h5 : ∀ d ∈ D, a * d * a⁻¹ * d⁻¹ ∈ B) (h6 : ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ N) :
    ∀ d ∈ D, a * d * a⁻¹ * d⁻¹ ∈ N := by
  intro d hd
  set β := a * d * a⁻¹ * d⁻¹ with hβdef
  have hβB : β ∈ B := h5 d hd
  have hβD : β ∈ D := hBD hβB
  have hnormN : (N.subgroupOf (Subgroup.normalizer (N : Set G))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  let π := QuotientGroup.mk' (N.subgroupOf (Subgroup.normalizer (N : Set G)))
  let α : Subgroup.normalizer (N : Set G) := ⟨a, haN⟩
  let δ : Subgroup.normalizer (N : Set G) := ⟨d, hDN hd⟩
  let γ : Subgroup.normalizer (N : Set G) := ⟨β, hDN hβD⟩
  have hker : ∀ x : Subgroup.normalizer (N : Set G), π x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have h1 : α * δ * α⁻¹ = γ * δ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, α, δ, γ, hβdef]
    group
  have h1' : π α * π δ * (π α)⁻¹ = π γ * π δ := by
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul]
  have h2 : π α * π γ * (π α)⁻¹ = π γ := by
    have : π (α * γ * α⁻¹ * γ⁻¹) = 1 := by
      rw [hker]
      exact h6 β hβB
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at this
  obtain ⟨j, hj⟩ := hD β hβD
  have h3 : (π γ) ^ 2 ^ j = 1 := by
    rw [← map_pow, hker]
    exact hj
  have h4 : (π α) ^ orderOf a = 1 := by
    rw [← map_pow]
    have : α ^ orderOf a = 1 := Subtype.ext (by simp [α, pow_orderOf_eq_one])
    rw [this, map_one]
  have h5 := eq_one_of_odd_conj ha h4 h1' h2 h3
  exact (hker γ).mp h5

theorem commutator_le_of_oTwoUpper {A N B D : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hBD : B ≤ D) (hD : ∀ d ∈ D, ∃ j : ℕ, d ^ 2 ^ j ∈ N) (h5 : ⁅A, D⁆ ≤ B) (h6 : ⁅A, B⁆ ≤ N) :
    ⁅oTwoUpper A, D⁆ ≤ N := by
  refine Subgroup.commutator_le.mpr fun x hx d hd => ?_
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    exact commutator_mem_of_series hx.2 (hAN hx.1) hDN hBD hD
      (fun d hd => Subgroup.commutator_le.mp h5 x hx.1 d hd)
      (fun b hb => Subgroup.commutator_le.mp h6 x hx.1 b hb) d hd
  | one =>
    show 1 * d * 1⁻¹ * d⁻¹ ∈ N
    simp
  | mul x y hx hy ihx ihy =>
    have hxN : x ∈ Subgroup.normalizer (N : Set G) := hAN (oTwoUpper_le A hx)
    have h1 : x * y * d * (x * y)⁻¹ * d⁻¹ =
        (x * (y * d * y⁻¹ * d⁻¹) * x⁻¹) * (x * d * x⁻¹ * d⁻¹) := by group
    show x * y * d * (x * y)⁻¹ * d⁻¹ ∈ N
    rw [h1]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN _).mp ihy) ihx
  | inv x hx ih =>
    have hxN : x ∈ Subgroup.normalizer (N : Set G) := hAN (oTwoUpper_le A hx)
    have h1 : x⁻¹ * d * (x⁻¹)⁻¹ * d⁻¹ = x⁻¹ * (x * d * x⁻¹ * d⁻¹)⁻¹ * x := by group
    show x⁻¹ * d * (x⁻¹)⁻¹ * d⁻¹ ∈ N
    rw [h1]
    exact (Subgroup.mem_normalizer_iff''.mp hxN _).mp (N.inv_mem ih)

theorem exists_pow_mem_sup_of_pow_mem {D N : Subgroup G}
    (hDN : D ≤ Subgroup.normalizer (N : Set G)) (hD : ∀ d ∈ D, ∃ j : ℕ, d ^ 2 ^ j ∈ N) :
    ∀ x ∈ D ⊔ N, ∃ j : ℕ, x ^ 2 ^ j ∈ N := by
  intro x hx
  have hx' : x ∈ (↑(D ⊔ N) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D N hDN] at hx'
  obtain ⟨d, hd, n, hn, rfl⟩ := hx'
  obtain ⟨j, hj⟩ := hD d hd
  have hdn : d * n = (d * n * d⁻¹) * d := by group
  have hmem : d * n * d⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hDN hd) n).mp hn
  obtain ⟨x', hx', h⟩ := exists_pow_mul_eq hmem (hDN hd) (2 ^ j)
  refine ⟨j, ?_⟩
  show (d * n) ^ 2 ^ j ∈ N
  rw [hdn, h]
  exact N.mul_mem hx' hj

section Finite

variable [Finite G]

theorem exists_chief_factor {X N D : Subgroup G} (hO : pCoreOf 2 X ≤ N)
    (hND : N < D) (hDX : D ≤ X) (hXD : X ≤ Subgroup.normalizer (D : Set G))
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ N) :
    ∃ B : Subgroup G, N ≤ B ∧ IsTwoChiefFactorOutsideO2 X D B := by
  obtain ⟨B, hNB, hB⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => N ≤ B ∧ B < D ∧ X ≤ Subgroup.normalizer (B : Set G))
    (a := N) ⟨le_rfl, hND, hXN⟩
  refine ⟨B, hNB, hO.trans hNB, hB.1.2.1, hDX, hXD, hB.1.2.2, ?_, fun a ha => ?_⟩
  · intro C hBC hCD hXC
    have := hB.2 ⟨hNB.trans hBC.le, hCD, hXC⟩ hBC.le
    exact absurd this (not_le_of_gt hBC)
  · obtain ⟨k, hk⟩ := hD a ha
    exact ⟨k, hNB hk⟩

theorem commutator_le_of_chief_central {X N D : Subgroup G} (hX : X = oTwoUpper X)
    (hchief : NoncentralTwoChiefFactorsInO2 X) (hO : pCoreOf 2 X ≤ N)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hNX : N ≤ X) (hDX : D ≤ X)
    (hXD : X ≤ Subgroup.normalizer (D : Set G)) (hDN : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ N) :
    ⁅D, X⁆ ≤ N := by
  have hDN' : D ≤ Subgroup.normalizer (N : Set G) := hDX.trans hXN
  have hD' : ∀ d ∈ D ⊔ N, ∃ k : ℕ, d ^ 2 ^ k ∈ N := exists_pow_mem_sup_of_pow_mem hDN' hDN
  have key : ∀ (n : ℕ) (D' : Subgroup G), Nat.card D' = n → N ≤ D' → D' ≤ X →
      X ≤ Subgroup.normalizer (D' : Set G) → (∀ d ∈ D', ∃ k : ℕ, d ^ 2 ^ k ∈ N) → ⁅D', X⁆ ≤ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro D' hn hND' hD'X hXD' hD'N
      rcases eq_or_lt_of_le hND' with h | h
      · rw [← h]
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp hXN
      · obtain ⟨B, hNB, hB⟩ := exists_chief_factor hO h hD'X hXD' hXN hD'N
        have hDB : ⁅D', X⁆ ≤ B := hchief D' B hB
        have hBlt : B < D' := hB.2.1
        have hcard : Nat.card B < n := hn ▸ card_lt_of_lt hBlt
        have hBX : ⁅B, X⁆ ≤ N :=
          ih _ hcard B rfl hNB (hBlt.le.trans hD'X) hB.2.2.2.2.1 (fun b hb => hD'N b (hBlt.le hb))
        have := commutator_le_of_oTwoUpper (A := X) (N := N) (B := B) (D := D')
          hXN (hD'X.trans hXN) hBlt.le hD'N
          (by rw [Subgroup.commutator_comm]; exact hDB)
          (by rw [Subgroup.commutator_comm]; exact hBX)
        rw [← hX, Subgroup.commutator_comm] at this
        exact this
  have h1 := key _ (D ⊔ N) rfl le_sup_right (sup_le hDX hNX)
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hXD hx, hXN hx⟩) hD'
  exact (Subgroup.commutator_mono le_sup_left le_rfl).trans h1

theorem thompson_axb {V A B : Subgroup G} (hV : IsPGroup 2 V) (hA : A = oTwoUpper A)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hB : ∀ b ∈ B, ∃ k : ℕ, b ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G))
    (hAB : ⁅A, B⁆ ≤ Subgroup.centralizer (V : Set G))
    (hfix : A ≤ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G)) :
    A ≤ Subgroup.centralizer (V : Set G) := by
  have hodd : ∀ a ∈ A, Odd (orderOf a) → a ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha hao
    have hzA : Subgroup.zpowers a ≤ Subgroup.normalizer (V : Set G) :=
      (Subgroup.zpowers_le.mpr ha).trans hAV
    let α : Subgroup.zpowers a →* MulAut V :=
      V.normalizerMonoidHom.comp (Subgroup.inclusion hzA)
    let β₀ : B →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hBV)
    have hα : ∀ (a' : Subgroup.zpowers a) (v : V), ((α a' v : V) : G) = a' * v * (a' : G)⁻¹ :=
      fun a' v => rfl
    have hβ₀ : ∀ (b : B) (v : V), ((β₀ b v : V) : G) = b * v * (b : G)⁻¹ := fun b v => rfl
    have : Finite β₀.range := (Set.finite_range β₀).to_subtype
    have hBp : IsPGroup 2 β₀.range := by
      rintro ⟨g, b, rfl⟩
      obtain ⟨k, hk⟩ := hB b b.2
      refine ⟨k, Subtype.ext ?_⟩
      show (β₀ b) ^ 2 ^ k = 1
      rw [← map_pow]
      exact normalizerMonoidHom_eq_one_iff.mpr hk
    have hcomm : ∀ (a' : Subgroup.zpowers a) (b' : β₀.range),
        α a' * β₀.range.subtype b' = β₀.range.subtype b' * α a' := by
      rintro a' ⟨b', b, rfl⟩
      show α a' * β₀ b = β₀ b * α a'
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      have ha'A : (a' : G) ∈ A := (Subgroup.zpowers_le.mpr ha) a'.2
      have hc : (a' : G) * b * (a' : G)⁻¹ * (b : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        hAB (Subgroup.commutator_mem_commutator ha'A b.2)
      have hcw := Subgroup.mem_centralizer_iff.mp hc ((β₀ b (α a' v) : V) : G)
        (β₀ b (α a' v)).2
      rw [MulAut.mul_apply, MulAut.mul_apply]
      simp only [hα, hβ₀] at hcw ⊢
      calc (a' : G) * ((b : G) * v * (b : G)⁻¹) * (a' : G)⁻¹
          = ((a' : G) * b * (a' : G)⁻¹ * (b : G)⁻¹) * ((b : G) * ((a' : G) * v * (a' : G)⁻¹) * (b : G)⁻¹) *
            ((a' : G) * b * (a' : G)⁻¹ * (b : G)⁻¹)⁻¹ := by group
        _ = (b : G) * ((a' : G) * v * (a' : G)⁻¹) * (b : G)⁻¹ := by
            have hcw' : ((a' : G) * b * (a' : G)⁻¹ * (b : G)⁻¹) * ((b : G) * ((a' : G) * v * (a' : G)⁻¹) * (b : G)⁻¹) =
                ((b : G) * ((a' : G) * v * (a' : G)⁻¹) * (b : G)⁻¹) * ((a' : G) * b * (a' : G)⁻¹ * (b : G)⁻¹) := hcw.symm
            rw [hcw']
            group
    have hfix' : ∀ (a' : Subgroup.zpowers a) (r : V),
        (∀ b' : β₀.range, β₀.range.subtype b' r = r) → α a' r = r := by
      intro a' r hr
      have hrB : (r : G) ∈ Subgroup.centralizer (B : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have := congrArg Subtype.val (hr ⟨β₀ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩⟩)
        rw [show (β₀.range.subtype ⟨β₀ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩⟩ : MulAut V) = β₀ ⟨h, hh⟩ from rfl,
          hβ₀] at this
        calc h * (r : G) = h * r * h⁻¹ * h := by group
          _ = r * h := by rw [this]
      have hrmem : (r : G) ∈ (V ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := ⟨r.2, hrB⟩
      have ha'A : (a' : G) ∈ A := (Subgroup.zpowers_le.mpr ha) a'.2
      have h1 := Subgroup.mem_centralizer_iff.mp (hfix ha'A) (r : G) hrmem
      apply Subtype.ext
      rw [hα]
      calc (a' : G) * r * (a' : G)⁻¹ = (r : G) * a' * (a' : G)⁻¹ := by rw [h1]
        _ = r := by group
    have hcard : ¬ 2 ∣ Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers]
      exact fun h => (Nat.not_even_iff_odd.mpr hao) (even_iff_two_dvd.mpr h)
    have key := CFSG.GroupTheory.thompson_A_times_B (p := 2) hV hcard hBp α β₀.range.subtype
      hcomm hfix' ⟨a, Subgroup.mem_zpowers a⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := congrArg (fun f : MulAut V => ((f ⟨v, hv⟩ : V) : G)) key
    simp only [MulAut.one_apply] at this
    rw [hα] at this
    show v * a = a * v
    calc v * a = (a * v * a⁻¹) * a := by rw [this]
      _ = a * v := by group
  calc A = oTwoUpper A := hA
    _ ≤ Subgroup.centralizer (V : Set G) :=
      (Subgroup.closure_le _).mpr fun x hx => hodd x hx.1 hx.2

end Finite

end CFSG.Quasithin.A4
