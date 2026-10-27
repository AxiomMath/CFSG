module

public import CFSG.Quasithin.Background.F9Dual
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open scoped Pointwise

variable {G : Type} [Group G]

section Helpers

theorem isPGroup_closure_pair_of_pow {a b : G} (ha : a * a = 1) (hb : b * b = 1) {k : ℕ}
    (hk : (a * b) ^ 2 ^ k = 1) : IsPGroup 2 (Subgroup.closure ({a, b} : Set G)) := by
  set y := a * b with hy
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hay : ∀ i : ℤ, a * y ^ i * a⁻¹ = y ^ (-i) := by
    intro i
    have h1 : a * y * a⁻¹ = y⁻¹ := by
      rw [hy, mul_inv_rev, hai, hbi]
      calc a * (a * b) * a = (a * a) * b * a := by group
        _ = b * a := by rw [ha, one_mul]
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1, inv_zpow', zpow_neg]
  let D : Set G := {g | ∃ i : ℤ, g = y ^ i ∨ g = a * y ^ i}
  have hDmul : ∀ g ∈ D, ∀ g' ∈ D, g * g' ∈ D := by
    rintro g ⟨i, rfl | rfl⟩ g' ⟨j, rfl | rfl⟩
    · exact ⟨i + j, Or.inl (zpow_add y i j).symm⟩
    · refine ⟨-i + j, Or.inr ?_⟩
      calc y ^ i * (a * y ^ j) = a * (a⁻¹ * y ^ i * a) * y ^ j := by group
        _ = a * y ^ (-i) * y ^ j := by
          rw [show a⁻¹ * y ^ i * a = a * y ^ i * a⁻¹ by rw [hai]]
          rw [hay]
        _ = a * y ^ (-i + j) := by rw [zpow_add]; group
    · exact ⟨i + j, Or.inr (by rw [zpow_add]; group)⟩
    · refine ⟨-i + j, Or.inl ?_⟩
      calc a * y ^ i * (a * y ^ j) = (a * y ^ i * a⁻¹) * y ^ j := by rw [hai]; group
        _ = y ^ (-i + j) := by rw [hay, zpow_add]
  have hsq : ∀ i : ℤ, a * y ^ i * (a * y ^ i) = 1 := by
    intro i
    calc a * y ^ i * (a * y ^ i) = (a * y ^ i * a⁻¹) * y ^ i := by rw [hai]; group
      _ = 1 := by rw [hay, zpow_neg, inv_mul_cancel]
  have hDinv : ∀ g ∈ D, g⁻¹ ∈ D := by
    rintro g ⟨i, rfl | rfl⟩
    · exact ⟨-i, Or.inl (zpow_neg y i).symm⟩
    · exact ⟨i, Or.inr (inv_eq_of_mul_eq_one_right (hsq i))⟩
  have hmem : ∀ g ∈ Subgroup.closure ({a, b} : Set G), g ∈ D := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨0, Or.inr (by rw [zpow_zero, mul_one])⟩
      · exact ⟨1, Or.inr (by rw [zpow_one, hy, ← mul_assoc, ha, one_mul])⟩
    | one => exact ⟨0, Or.inl (zpow_zero y).symm⟩
    | mul x z _ _ hx hz => exact hDmul x hx z hz
    | inv x _ hx => exact hDinv x hx
  intro g
  obtain ⟨i, hi | hi⟩ := hmem g g.2
  · refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hk, one_zpow]
    rfl
  · refine ⟨1, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, hi, pow_one, pow_two, OneMemClass.coe_one]
    exact hsq i

theorem exists_pow_odd_of_not_isPGroup [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hn : ¬ IsPGroup 2 (Subgroup.closure ({a, b} : Set G))) :
    ∃ k : ℕ, Odd (orderOf ((a * b) ^ 2 ^ k)) ∧ orderOf ((a * b) ^ 2 ^ k) ≠ 1 := by
  have h0 : orderOf (a * b) ≠ 0 := (orderOf_pos (a * b)).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd h0
  have hord : orderOf ((a * b) ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hkm]; exact Dvd.intro m rfl), hkm]
    exact Nat.mul_div_cancel_left m (by positivity)
  refine ⟨k, hord ▸ hm, fun h1 => hn (isPGroup_closure_pair_of_pow ha hb (k := k) ?_)⟩
  rw [hord] at h1
  rw [← orderOf_dvd_iff_pow_eq_one, hkm, h1, mul_one]

theorem not_two_pow_of_odd {g : G} (hodd : Odd (orderOf g)) (h1 : orderOf g ≠ 1) (k : ℕ) :
    g ^ 2 ^ k ≠ 1 := by
  intro hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · exact h1 (by rw [hj, h0, pow_zero])
  · rw [hj] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hpos.ne'⟩)

omit [Group G] in
theorem exists_pow_eq_one_of_mem {G : Type} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {g : G} (hg : g ∈ P) : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem card_sup_mul_card_inf' [Finite G] {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem mem_normalizer_of_conjSub_le {g : G} {X : Subgroup G} (h1 : conjSub g X ≤ X)
    (h2 : conjSub g⁻¹ X ≤ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 (mul_mem_conjSub hx)
  · intro hx
    have := h2 (mul_mem_conjSub (g := g⁻¹) hx)
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem mem_or_mul_inv_mem_of_index_two {V₁ V₂ : Subgroup G}
    (hidx : V₁.relIndex V₂ = 2) {a : G} (ha : a ∈ V₂) (ha1 : a ∉ V₁) {e : G} (he : e ∈ V₂) :
    e ∈ V₁ ∨ e * a⁻¹ ∈ V₁ := by
  by_cases he1 : e ∈ V₁
  · exact Or.inl he1
  · right
    have h := (Subgroup.mul_mem_iff_of_index_two (H := V₁.subgroupOf V₂) hidx
      (a := (⟨e, he⟩ : V₂)) (b := (⟨a, ha⟩ : V₂)⁻¹)).2
      (iff_of_false (by rw [Subgroup.mem_subgroupOf]; exact he1)
        (by rw [Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]; exact ha1))
    rw [Subgroup.mem_subgroupOf] at h
    exact h


theorem card_mul_relIndex' {A B : Subgroup G} (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  have := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.2 h] at this
  rw [mul_comm]
  exact this

theorem mem_open_pCore_of_mem_pCore {p : ℕ} {x : G} (hx : x ∈ CFSG.pCore p G) :
    x ∈ CFSG.Open.pCore p G := by
  have hle : CFSG.pCore p G ≤ CFSG.Open.pCore p G := le_rfl
  exact hle hx

theorem orderOf_conj' (l g : G) : orderOf (l * g * l⁻¹) = orderOf g := by
  have := orderOf_injective (MulAut.conj l).toMonoidHom (MulAut.conj l).injective g
  simpa [MulAut.conj_apply] using this

theorem sup_eq_closure_union (A B : Subgroup G) : A ⊔ B = Subgroup.closure ((A : Set G) ∪ B) := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]


theorem acts_trivially_of_gens {A X₁ X₂ Y₁ Y₂ : Subgroup G}
    (hXY : X₁ ⊔ X₂ ≤ Subgroup.centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G))
    (hYX : Y₁ ⊔ Y₂ ≤ X₁ ⊔ X₂)
    (hA1 : ∀ y ∈ A, ∀ x ∈ X₁, y * x * y⁻¹ * x⁻¹ ∈ Y₁ ⊔ Y₂)
    (hA2 : ∀ y ∈ A, ∀ x ∈ X₂, y * x * y⁻¹ * x⁻¹ ∈ Y₁ ⊔ Y₂)
    (hA3 : ∀ y ∈ A, ∀ x ∈ Y₁, y * x * y⁻¹ * x⁻¹ ∈ Y₁ ⊔ Y₂)
    (hA4 : ∀ y ∈ A, ∀ x ∈ Y₂, y * x * y⁻¹ * x⁻¹ ∈ Y₁ ⊔ Y₂) :
    ∀ y ∈ A, y ∈ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) ∧
      y ∈ Subgroup.normalizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) ∧
      ∀ x ∈ X₁ ⊔ X₂, y * x * y⁻¹ * x⁻¹ ∈ Y₁ ⊔ Y₂ := by
  have hconj : ∀ {y : G} {Z Z' W : Subgroup G}, Z ≤ Z' → W ≤ Z' →
      (∀ x ∈ Z, y * x * y⁻¹ * x⁻¹ ∈ W) → conjSub y Z ≤ Z' := by
    intro y Z Z' W hZ hW h b hb
    rw [mem_conjSub] at hb
    have h2 := h _ hb
    have e : b = (y * (y⁻¹ * b * y) * y⁻¹ * (y⁻¹ * b * y)⁻¹) * (y⁻¹ * b * y) := by group
    rw [e]
    exact Z'.mul_mem (hW h2) (hZ hb)
  intro y hy
  have hyi : y⁻¹ ∈ A := A.inv_mem hy
  refine ⟨mem_normalizer_of_conjSub_le ?_ ?_, mem_normalizer_of_conjSub_le ?_ ?_, fun x hx => ?_⟩
  · rw [conjSub_sup]
    exact sup_le (hconj le_sup_left hYX (hA1 y hy)) (hconj le_sup_right hYX (hA2 y hy))
  · rw [conjSub_sup]
    exact sup_le (hconj le_sup_left hYX (hA1 _ hyi)) (hconj le_sup_right hYX (hA2 _ hyi))
  · rw [conjSub_sup]
    exact sup_le (hconj le_sup_left le_rfl (hA3 y hy)) (hconj le_sup_right le_rfl (hA4 y hy))
  · rw [conjSub_sup]
    exact sup_le (hconj le_sup_left le_rfl (hA3 _ hyi)) (hconj le_sup_right le_rfl (hA4 _ hyi))
  · rw [sup_eq_closure_union] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hA1 y hy x hx
      · exact hA2 y hy x hx
    | one => simp
    | mul a b ha hb iha ihb =>
      have haX : a ∈ X₁ ⊔ X₂ := by rw [sup_eq_closure_union]; exact ha
      have hc := Subgroup.mem_centralizer_iff.1 (hXY haX) _ ihb
      have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
          (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
      rw [e, show a * (y * b * y⁻¹ * b⁻¹) * a⁻¹ = y * b * y⁻¹ * b⁻¹ by
        rw [← hc]; group]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      have haX : a ∈ X₁ ⊔ X₂ := by rw [sup_eq_closure_union]; exact ha
      have hc := Subgroup.mem_centralizer_iff.1 (hXY haX) _ (Subgroup.inv_mem _ iha)
      have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
      rw [e, show a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a = (y * a * y⁻¹ * a⁻¹)⁻¹ by
        rw [show a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a =
          a⁻¹ * ((y * a * y⁻¹ * a⁻¹)⁻¹ * a) by group, hc]; group]
      exact Subgroup.inv_mem _ iha

theorem acts_trivially_sup {A B X Y : Subgroup G}
    (hA : ∀ y ∈ A, y ∈ Subgroup.normalizer (X : Set G) ∧ y ∈ Subgroup.normalizer (Y : Set G) ∧
      ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ Y)
    (hB : ∀ y ∈ B, y ∈ Subgroup.normalizer (X : Set G) ∧ y ∈ Subgroup.normalizer (Y : Set G) ∧
      ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ Y) :
    ∀ y ∈ A ⊔ B, y ∈ Subgroup.normalizer (X : Set G) ∧ y ∈ Subgroup.normalizer (Y : Set G) ∧
      ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ Y := by
  intro y hy
  rw [sup_eq_closure_union] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hA y hy
    · exact hB y hy
  | one => exact ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun x _ => by simp⟩
  | mul a b _ _ iha ihb =>
    refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, Subgroup.mul_mem _ iha.2.1 ihb.2.1, fun x hx => ?_⟩
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 iha.2.1 _).1 (ihb.2.2 x hx))
      (iha.2.2 x hx)
  | inv a _ iha =>
    refine ⟨Subgroup.inv_mem _ iha.1, Subgroup.inv_mem _ iha.2.1, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ iha.1) x).1 hx
    have h2 := iha.2.2 _ hx'
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ =
        (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * x * a⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h2

end Helpers

variable [Finite G]

structure HullHyp (T V L V₁ V₂ V₃ V₅ H : Subgroup G) (l₁ l₂ : G) : Prop where
  f91 : HypF91 T V L V₁ V₃ H
  le12 : V₁ ≤ V₂
  le23 : V₂ ≤ V₃
  le35 : V₃ ≤ V₅
  le5 : V₅ ≤ V
  card2 : Nat.card V₂ = 4
  card3 : Nat.card V₃ = 8
  card5 : Nat.card V₅ = 32
  card : Nat.card V = 64
  l₁H : l₁ ∈ H
  l₂H : l₂ ∈ H
  l₁V : l₁ ∈ Subgroup.normalizer (V : Set G)
  l₂V : l₂ ∈ Subgroup.normalizer (V : Set G)
  l₁V₃ : l₁ ∈ Subgroup.normalizer (V₃ : Set G)
  wa : ∀ n ∈ T, (∀ c ∈ V₃, c * n * c⁻¹ * n⁻¹ ∈ V₁) → n ^ 2 ∈ Subgroup.centralizer (V : Set G) →
    n * (l₁ * n * l₁⁻¹) * n⁻¹ * (l₁ * n * l₁⁻¹)⁻¹ ∈ Subgroup.centralizer (V : Set G) →
    n * (l₂ * n * l₂⁻¹) * n⁻¹ * (l₂ * n * l₂⁻¹)⁻¹ ∈ Subgroup.centralizer (V : Set G) →
    n ∈ Subgroup.centralizer (V₃ : Set G) ∧ (∀ v ∈ V, v * n * v⁻¹ * n⁻¹ ∈ V₃) ∧
      (n ∉ Subgroup.centralizer (V : Set G) → ∃ v ∈ V, v * n * v⁻¹ * n⁻¹ ∉ V₁)
  wb : ∀ n ∈ T, (∀ c ∈ V₃, c * n * c⁻¹ * n⁻¹ ∈ V₁) → n ∉ Subgroup.centralizer (V₃ : Set G) →
    ∃ w ∈ V₅, w * n * w⁻¹ * n⁻¹ ∈ V₃ ∧ w * n * w⁻¹ * n⁻¹ ∉ V₁
  wc : ∀ n ∈ Subgroup.normalizer (V : Set G), n ∈ Subgroup.centralizer (V₃ : Set G) →
    ∀ v ∈ V, v * n * v⁻¹ * n⁻¹ ∈ V₃
  wd : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ → l₁ ∈ Subgroup.normalizer (X : Set G) → X = V₁ ∨ X = V₃
  we : ∀ X : Subgroup G, V₃ ≤ X → X ≤ V → l₁ ∈ Subgroup.normalizer (X : Set G) →
    l₂ ∈ Subgroup.normalizer (X : Set G) → X = V₃ ∨ X = V₅ ∨ X = V
  wf : ∀ c ∈ V₃, c ∉ V₁ → ∃ l ∈ H, l ∈ Subgroup.normalizer (V : Set G) ∧ l * c * l⁻¹ ∈ V₂
  wg : ∃ l ∈ Subgroup.normalizer (V₂ : Set G), l ∈ Subgroup.normalizer (V : Set G) ∧
    ∃ w ∈ V₅, l * w * l⁻¹ ∉ V₅
  s1317 : ∀ g ∈ H, ⁅V, conjSub g V⁆ ≤ V ⊓ conjSub g V → ⁅V, conjSub g V⁆ = ⊥
  s13314 : ¬ pCoreOf 2 H ≤ Subgroup.centralizer (V₂ : Set G)
  s13315 : pCoreOf 2 H ⊓ Subgroup.centralizer (V₂ : Set G) ≤
    pCoreOf 2 (Subgroup.normalizer (V₂ : Set G))
  cod : ∀ F : Subgroup G, F ≤ V → F.relIndex V ≤ 8 →
    Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (V : Set G)

namespace HullHyp

variable {T V L V₁ V₂ V₃ V₅ H : Subgroup G} {l₁ l₂ : G}
variable (h : HullHyp T V L V₁ V₂ V₃ V₅ H l₁ l₂)
include h

omit [Finite G] in
theorem elemAbelian : IsElemAbelian 2 V := h.f91.elemAbelian

omit [Finite G] in
theorem V_le_H : V ≤ H := h.f91.V_le_H

omit [Finite G] in
theorem T_le_H : T ≤ H := h.f91.T_le_H

omit [Finite G] in
theorem T_le_normalizer : T ≤ Subgroup.normalizer (V : Set G) := h.f91.T_normalizes_V

theorem pCoreOf_le_T : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le h.f91.sylow_H

omit [Finite G] in
theorem V₁_le_V : V₁ ≤ V := h.f91.V₁_le_V

omit [Finite G] in
theorem V₃_le_V : V₃ ≤ V := h.le35.trans h.le5

omit [Finite G] in
theorem V_le_centralizer : V ≤ Subgroup.centralizer (V : Set G) := fun _ hv =>
  Subgroup.mem_centralizer_iff.2 fun _ hw => isElemAbelian_comm h.elemAbelian hw hv

omit [Finite G] in
theorem V₁_le_centralizer : V₁ ≤ Subgroup.centralizer (V : Set G) :=
  h.V₁_le_V.trans h.V_le_centralizer

theorem U_le_pCoreOf : conjClosure V₃ H ≤ pCoreOf 2 H := h.f91.conjClosure_Vp_le_pCoreOf

omit [Finite G] in
theorem conj_V₁ {k c : G} (hk : k ∈ H) (hc : c ∈ V₁) : k * c * k⁻¹ = c :=
  h.f91.conj_eq_of_mem_V₁ hk hc

omit [Finite G] in
theorem V₁_le_conjSub {g : G} (hg : g ∈ H) {X : Subgroup G} (hX : V₁ ≤ X) : V₁ ≤ conjSub g X := by
  intro c hc
  rw [mem_conjSub]
  rw [show g⁻¹ * c * g = c by
    have := h.conj_V₁ (H.inv_mem hg) hc
    rwa [inv_inv] at this]
  exact hX hc

omit [Finite G] h in
theorem conjSub_pCoreOf {g : G} (hg : g ∈ H) : conjSub g (pCoreOf 2 H) = pCoreOf 2 H :=
  conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hg)

theorem U_facts {u : G} (hu : u ∈ conjClosure V₃ H) :
    u ∈ Subgroup.centralizer (V₃ : Set G) ∧ (∀ v ∈ V, v * u * v⁻¹ * u⁻¹ ∈ V₃) ∧
      (u ∉ Subgroup.centralizer (V : Set G) → ∃ v ∈ V, v * u * v⁻¹ * u⁻¹ ∉ V₁) := by
  have huQ := h.U_le_pCoreOf hu
  have hcomm := h.f91.commutator_conjClosure_le
  refine h.wa u (h.pCoreOf_le_T huQ) (fun c hc => hcomm c (le_conjClosure V₃ H hc) u huQ)
    (h.V₁_le_centralizer (h.f91.sq_mem_conjClosure u hu)) ?_ ?_
  · have hlu : l₁ * u * l₁⁻¹ ∈ conjClosure V₃ H :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V₃ H h.l₁H) u).1 hu
    exact h.V₁_le_centralizer (hcomm u hu _ (h.U_le_pCoreOf hlu))
  · have hlu : l₂ * u * l₂⁻¹ ∈ conjClosure V₃ H :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V₃ H h.l₂H) u).1 hu
    exact h.V₁_le_centralizer (hcomm u hu _ (h.U_le_pCoreOf hlu))

theorem U_le_centralizer_V₃ : conjClosure V₃ H ≤ Subgroup.centralizer (V₃ : Set G) :=
  fun _ hu => (h.U_facts hu).1

theorem V₃_le_centralizer_U : V₃ ≤ Subgroup.centralizer (conjClosure V₃ H : Set G) :=
  fun c hc => Subgroup.mem_centralizer_iff.2 fun _ hu =>
    (Subgroup.mem_centralizer_iff.1 (h.U_le_centralizer_V₃ hu) c hc).symm

theorem U_elemAbelian : IsElemAbelian 2 (conjClosure V₃ H) := by
  refine HypF91.isElemAbelian_conjClosure_of_forall h.f91.elemAbelian_Vp fun k hk c hc => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyU : y ∈ conjClosure V₃ H := by
    rw [SetLike.mem_coe, mem_conjSub] at hy
    have := mem_conjClosure (Z := V₃) hk hy
    rwa [show k * (k⁻¹ * y * k) * k⁻¹ = y by group] at this
  exact (Subgroup.mem_centralizer_iff.1 (h.U_le_centralizer_V₃ hyU) c hc).symm

theorem not_V_le_centralizer_U (hab : ¬ IsElemAbelian 2 (conjClosure V H)) :
    ¬ V ≤ H ⊓ Subgroup.centralizer (conjClosure V₃ H : Set G) := by
  intro hVU
  apply hab
  have hVQ : V ≤ pCoreOf 2 H := h.f91.le_pCoreOf_iff_le_centralizer.2 hVU
  refine HypF91.isElemAbelian_conjClosure_of_forall h.elemAbelian fun k hk => ?_
  have h1 := h.f91.commutator_conjSub_le_of_le_pCoreOf hVQ hk
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (h.s1317 k hk h1)

omit [Finite G] in
theorem V₃_inf_centralizer_Q :
    V₃ ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) = V₁ := by
  have hV₁C : V₁ ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.2 fun q hq => by
      have := h.conj_V₁ (pCoreOf_le 2 H hq) hc
      calc q * c = q * c * q⁻¹ * q := by group
        _ = c * q := by rw [this]
  have hl : l₁ ∈ Subgroup.normalizer
      ((V₃ ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf h.l₁V₃
      (normalizer_le_normalizer_centralizer _ (le_normalizer_pCoreOf 2 H h.l₁H))
  rcases h.wd _ (le_inf (h.le12.trans h.le23) hV₁C) inf_le_left hl with h1 | h1
  · exact h1
  · exfalso
    apply h.s13314
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hc' : c ∈ V₃ ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      rw [h1]
      exact h.le23 hc
    exact (Subgroup.mem_centralizer_iff.1 hc'.2 q hq).symm

theorem not_V_inf_Q_le (hVU : ¬ V ≤ H ⊓ Subgroup.centralizer (conjClosure V₃ H : Set G)) :
    ¬ V ⊓ pCoreOf 2 H ≤ Subgroup.centralizer (conjClosure V₃ H : Set G) := by
  intro hQC
  set Q := pCoreOf 2 H with hQ
  set U := conjClosure V₃ H with hU
  have hex : ∃ u₀ ∈ U, u₀ ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hne
    push Not at hne
    exact hVU fun v hv => ⟨h.V_le_H hv, Subgroup.mem_centralizer_iff.2 fun u hu =>
      (Subgroup.mem_centralizer_iff.1 (hne u hu) v hv).symm⟩
  obtain ⟨u₀, hu₀, hu₀C⟩ := hex
  obtain ⟨v, hv, hvu⟩ := (h.U_facts hu₀).2.2 hu₀C
  set c := v * u₀ * v⁻¹ * u₀⁻¹ with hc
  have hcV₃ : c ∈ V₃ := (h.U_facts hu₀).2.1 v hv
  have hvH : v ∈ H := h.V_le_H hv
  have hcQ : c ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH : x ∈ H := pCoreOf_le 2 H hx
    have hxv : ∀ y ∈ Q, y⁻¹ * (v⁻¹ * y * v) ∈ Subgroup.centralizer (U : Set G) := by
      intro y hy
      apply hQC
      refine ⟨?_, ?_⟩
      · have h1 : y⁻¹ * v⁻¹ * y ∈ V :=
          (Subgroup.mem_normalizer_iff.1 (h.T_le_normalizer (h.pCoreOf_le_T (Q.inv_mem hy)))
            v⁻¹).1 (V.inv_mem hv) |> fun h' => by simpa [mul_assoc] using h'
        rw [show y⁻¹ * (v⁻¹ * y * v) = (y⁻¹ * v⁻¹ * y) * v by group]
        exact V.mul_mem h1 hv
      · have h1 : v⁻¹ * y * v ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (H.inv_mem hvH)) y).1 hy
          rwa [inv_inv] at this
        exact Q.mul_mem (Q.inv_mem hy) h1
    have hu₀H : u₀ ∈ H := pCoreOf_le 2 H (h.U_le_pCoreOf hu₀)
    have hvu₀ : v * u₀ * v⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V₃ H hvH) u₀).1 hu₀
    have hcU : c ∈ U := U.mul_mem hvu₀ (U.inv_mem hu₀)
    have e1 := h.f91.commutator_mul_right hx hvu₀ (U.inv_mem hu₀)
    have hy : v⁻¹ * x * v ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (H.inv_mem hvH)) x).1 hx
      rwa [inv_inv] at this
    have e2 := h.f91.commutator_conj hvH hy hu₀
    rw [show v * (v⁻¹ * x * v) * v⁻¹ = x by group] at e2
    have hq := hxv x hx
    set q := x⁻¹ * (v⁻¹ * x * v) with hqdef
    have hqQ : q ∈ Q := Q.mul_mem (Q.inv_mem hx) hy
    have e3 := h.f91.commutator_mul_left hx hqQ hu₀
    rw [show x * q = v⁻¹ * x * v by rw [hqdef]; group] at e3
    have hq1 : q * u₀ * q⁻¹ * u₀⁻¹ = 1 := by
      rw [(Subgroup.mem_centralizer_iff.1 hq u₀ hu₀).symm]
      group
    rw [hq1, mul_one] at e3
    have e4 := h.f91.commutator_mul_right hx hu₀ (U.inv_mem hu₀)
    rw [mul_inv_cancel, show x * 1 * x⁻¹ * (1 : G)⁻¹ = 1 by group] at e4
    have key : x * c * x⁻¹ * c⁻¹ = 1 := by
      rw [hc, e1, e2, e3, ← e4]
    calc x * c = x * c * x⁻¹ * c⁻¹ * c * x := by group
      _ = c * x := by rw [key]; group
  apply hvu
  rw [← h.V₃_inf_centralizer_Q]
  exact ⟨hcV₃, hcQ⟩

theorem V_inf_Q_eq (hVU : ¬ V ≤ H ⊓ Subgroup.centralizer (conjClosure V₃ H : Set G)) :
    V ⊓ pCoreOf 2 H = V₅ := by
  set Q := pCoreOf 2 H with hQ
  set U := conjClosure V₃ H with hU
  have hl : ∀ {l : G}, l ∈ H → l ∈ Subgroup.normalizer (V : Set G) →
      l ∈ Subgroup.normalizer ((V ⊓ Q : Subgroup G) : Set G) ∧
        l ∈ Subgroup.normalizer ((V ⊓ (Q ⊓ Subgroup.centralizer (U : Set G)) : Subgroup G) :
          Set G) := by
    intro l hlH hlV
    have hlQ : l ∈ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H hlH
    have hlC : l ∈ Subgroup.normalizer ((Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) :=
      normalizer_le_normalizer_centralizer _ (le_normalizer_conjClosure V₃ H hlH)
    exact ⟨mem_normalizer_inf hlV hlQ, mem_normalizer_inf hlV (mem_normalizer_inf hlQ hlC)⟩
  have hV₃Q : V₃ ≤ V ⊓ (Q ⊓ Subgroup.centralizer (U : Set G)) :=
    le_inf h.V₃_le_V (le_inf ((le_conjClosure V₃ H).trans h.U_le_pCoreOf) h.V₃_le_centralizer_U)
  have h2 := h.we _ (hV₃Q.trans (inf_le_inf_left _ inf_le_left)) inf_le_left
    (hl h.l₁H h.l₁V).1 (hl h.l₂H h.l₂V).1
  have hne : V ⊓ Q ≠ V := by
    intro he
    apply hVU
    have hVQ : V ≤ Q := by rw [← he]; exact inf_le_right
    exact h.f91.le_pCoreOf_iff_le_centralizer.1 hVQ
  have hne' : V ⊓ (Q ⊓ Subgroup.centralizer (U : Set G)) ≠ V ⊓ Q := by
    intro he
    apply h.not_V_inf_Q_le hVU
    rw [← he]
    exact inf_le_right.trans inf_le_right
  rcases h2 with h2 | h2 | h2
  · exact absurd (le_antisymm (inf_le_inf_left _ inf_le_left) ((le_of_eq h2).trans hV₃Q)) hne'
  · exact h2
  · exact absurd h2 hne

theorem V_le_pCoreOf_normalizer
    (hVU : ¬ V ≤ H ⊓ Subgroup.centralizer (conjClosure V₃ H : Set G)) :
    V ≤ pCoreOf 2 (Subgroup.normalizer (V₂ : Set G)) := by
  set R := pCoreOf 2 (Subgroup.normalizer (V₂ : Set G)) with hR
  have hV₂V : V₂ ≤ V := h.le23.trans h.V₃_le_V
  have hV₅Q : V₅ ≤ pCoreOf 2 H := by
    rw [← h.V_inf_Q_eq hVU]
    exact inf_le_right
  have hV₅C : V₅ ≤ Subgroup.centralizer (V₂ : Set G) := fun w hw =>
    Subgroup.mem_centralizer_iff.2 fun c hc =>
      isElemAbelian_comm h.elemAbelian (hV₂V hc) (h.le5 hw)
  have hV₅R : V₅ ≤ R := fun w hw => h.s13315 ⟨hV₅Q hw, hV₅C hw⟩
  obtain ⟨l, hl₂, hlV, w, hw, hlw⟩ := h.wg
  have hlwV : l * w * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hlV w).1 (h.le5 hw)
  have hlwR : l * w * l⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hl₂) w).1 (hV₅R hw)
  have hidx : V₅.relIndex V = 2 := by
    have := card_mul_relIndex' h.le5
    rw [h.card5, h.card] at this
    omega
  intro v hv
  rcases mem_or_mul_inv_mem_of_index_two hidx hlwV hlw hv with h1 | h1
  · exact hV₅R h1
  · have := R.mul_mem (hV₅R h1) hlwR
    rwa [inv_mul_cancel_right] at this

theorem exists_odd (hVU : ¬ V ≤ H ⊓ Subgroup.centralizer (conjClosure V₃ H : Set G)) :
    ∃ g ∈ H, Odd (orderOf g) ∧ orderOf g ≠ 1 ∧ g ∈ V ⊔ conjSub g⁻¹ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVQ : ¬ V ≤ pCoreOf 2 H := fun hle =>
    hVU (h.f91.le_pCoreOf_iff_le_centralizer.1 hle)
  obtain ⟨v₁, hv₁, hv₁Q⟩ := Set.not_subset.1 hVQ
  have hv₁H : v₁ ∈ H := h.V_le_H hv₁
  have hv₁2 : v₁ * v₁ = 1 := by
    rw [← pow_two]
    exact isElemAbelian_pow_eq_one h.elemAbelian hv₁
  set x : H := ⟨v₁, hv₁H⟩ with hx
  have hx2 : x * x = 1 := Subtype.ext hv₁2
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hk, pow_one, pow_two, ← zpow_add, ← two_mul, zpow_mul,
      show x ^ (2 : ℤ) = 1 by rw [zpow_two, hx2], one_zpow]
    rfl
  have hnot : ¬ ∀ g : H, IsPGroup 2 (Subgroup.closure ({x, g * x * g⁻¹} : Set H)) := by
    intro hall
    apply hv₁Q
    exact ⟨x, mem_open_pCore_of_mem_pCore (CFSG.BaerSuzuki.baer_suzuki x hxp hall), rfl⟩
  push Not at hnot
  obtain ⟨g, hg⟩ := hnot
  have hw2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
  obtain ⟨k, hodd, h1⟩ := exists_pow_odd_of_not_isPGroup hx2 hw2 hg
  set b : G := (g : G) * v₁ * (g : G)⁻¹ with hb
  set y : G := (v₁ * b) ^ 2 ^ k with hy
  have hyH : ((x * (g * x * g⁻¹)) ^ 2 ^ k : H) = y := by
    simp [hy, hb, hx]
  have hyo : orderOf y = orderOf ((x * (g * x * g⁻¹)) ^ 2 ^ k) := by
    rw [← hyH, Subgroup.orderOf_coe]
  have hyHm : y ∈ H := hyH ▸ ((x * (g * x * g⁻¹)) ^ 2 ^ k).2
  have hv₁i : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv₁2
  have hb2 : b * b = 1 := by
    calc b * b = (g : G) * (v₁ * v₁) * (g : G)⁻¹ := by rw [hb]; group
      _ = 1 := by rw [hv₁2, mul_one, mul_inv_cancel]
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hinv : v₁ * y * v₁⁻¹ = y⁻¹ := by
    have h2 : v₁ * (v₁ * b) * v₁⁻¹ = (v₁ * b)⁻¹ := by
      rw [mul_inv_rev, hbi, hv₁i, ← mul_assoc, hv₁2, one_mul]
    rw [hy, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, h2, inv_pow]
  have hinv' : v₁ * y⁻¹ * v₁⁻¹ = y := by
    rw [show v₁ * y⁻¹ * v₁⁻¹ = (v₁ * y * v₁⁻¹)⁻¹ by group, hinv, inv_inv]
  refine ⟨y, hyHm, hyo ▸ hodd, hyo ▸ h1, ?_⟩
  have hsq : v₁ * (y⁻¹ * v₁ * y⁻¹⁻¹) = y ^ 2 := by
    rw [inv_inv, pow_two]
    calc v₁ * (y⁻¹ * v₁ * y) = (v₁ * y⁻¹ * v₁⁻¹) * y := by rw [hv₁i]; group
      _ = y * y := by rw [hinv']
  have hy2 : y ^ 2 ∈ V ⊔ conjSub y⁻¹ V := by
    rw [← hsq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv₁)
      (Subgroup.mem_sup_right (mul_mem_conjSub hv₁))
  obtain ⟨j, hj⟩ := (hyo ▸ hodd : Odd (orderOf y))
  have hye : y = (y ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have := Subgroup.pow_mem _ hy2 (j + 1)
  rwa [← hye] at this

theorem key (hVU : ¬ V ≤ H ⊓ Subgroup.centralizer (conjClosure V₃ H : Set G)) {g : G}
    (hg : g ∈ H) (hodd : Odd (orderOf g)) (h1 : orderOf g ≠ 1)
    (hgI : g ∈ V ⊔ conjSub g⁻¹ V) :
    ∀ x ∈ conjSub g⁻¹ V₅, ∀ c ∈ V₃, c * x = x * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, c, hc, hcx⟩ := hcon
  set Q := pCoreOf 2 H with hQ
  have hV₅Q : V₅ ≤ Q := by
    rw [← h.V_inf_Q_eq hVU]
    exact inf_le_right
  have hQg : conjSub g⁻¹ Q = Q := conjSub_pCoreOf (H.inv_mem hg)
  have hxQ : x ∈ Q := by
    have := conjSub_mono g⁻¹ hV₅Q hx
    rwa [hQg] at this
  have hxT : x ∈ T := h.pCoreOf_le_T hxQ
  have hxC : x ∉ Subgroup.centralizer (V₃ : Set G) := fun hxC =>
    hcx (Subgroup.mem_centralizer_iff.1 hxC c hc)
  obtain ⟨w, hw, hdV₃, hdV₁⟩ := h.wb x hxT
    (fun c hc => h.f91.commutator_conjClosure_le c (le_conjClosure V₃ H hc) x hxQ) hxC
  set d := w * x * w⁻¹ * x⁻¹ with hd
  have hdV : d ∈ V := by
    have h2 : x * w⁻¹ * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (h.T_le_normalizer hxT) w⁻¹).1 (V.inv_mem (h.le5 hw))
    rw [hd, show w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) by group]
    exact V.mul_mem (h.le5 hw) h2
  have hQN : Q ≤ Subgroup.normalizer (conjSub g⁻¹ V : Set G) := by
    have := conjSub_le_normalizer (g := g⁻¹) (h.pCoreOf_le_T.trans h.T_le_normalizer)
    rwa [hQg] at this
  have hxVg : x ∈ conjSub g⁻¹ V := conjSub_mono g⁻¹ h.le5 hx
  have hdVg : d ∈ conjSub g⁻¹ V := by
    have h2 : w * x * w⁻¹ ∈ conjSub g⁻¹ V :=
      (Subgroup.mem_normalizer_iff.1 (hQN (hV₅Q hw)) x).1 hxVg
    exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hxVg)
  obtain ⟨l, hlH, hlV, hld⟩ := h.wf d hdV₃ hdV₁
  set g' := l * g * l⁻¹ with hg'
  have hg'H : g' ∈ H := H.mul_mem (H.mul_mem hlH hg) (H.inv_mem hlH)
  have hconj : conjSub g'⁻¹ V = conjSub l (conjSub g⁻¹ V) := by
    rw [show g'⁻¹ = l * (g⁻¹ * l⁻¹) by rw [hg']; group, conjSub_mul, conjSub_mul,
      conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ hlV)]
  have hld1 : l * d * l⁻¹ ∉ V₁ := by
    intro h2
    apply hdV₁
    have h3 := h.conj_V₁ (H.inv_mem hlH) h2
    rw [inv_inv, show l⁻¹ * (l * d * l⁻¹) * l = d by group] at h3
    rw [h3]
    exact h2
  have hV₁V' : V₁ ≤ V ⊓ conjSub g'⁻¹ V :=
    le_inf h.V₁_le_V (h.V₁_le_conjSub (H.inv_mem hg'H) h.V₁_le_V)
  have hldV' : l * d * l⁻¹ ∈ V ⊓ conjSub g'⁻¹ V := by
    refine ⟨(Subgroup.mem_normalizer_iff.1 hlV d).1 hdV, ?_⟩
    rw [hconj]
    exact mul_mem_conjSub hdVg
  have hidx12 : V₁.relIndex V₂ = 2 := by
    have := card_mul_relIndex' h.le12
    rw [h.f91.card_V₁, h.card2] at this
    omega
  have hV₂ : V₂ ≤ V ⊓ conjSub g'⁻¹ V := by
    intro e he
    rcases mem_or_mul_inv_mem_of_index_two hidx12 hld hld1 he with h2 | h2
    · exact hV₁V' h2
    · have := Subgroup.mul_mem _ (hV₁V' h2) hldV'
      rwa [inv_mul_cancel_right] at this
  have hI' : V ⊔ conjSub g'⁻¹ V ≤ Subgroup.centralizer (V₂ : Set G) := by
    refine sup_le (fun v hv => Subgroup.mem_centralizer_iff.2 fun e he =>
      isElemAbelian_comm h.elemAbelian ((hV₂ he).1) hv) (fun v hv =>
      Subgroup.mem_centralizer_iff.2 fun e he =>
        isElemAbelian_comm (isElemAbelian_conjSub h.elemAbelian) ((hV₂ he).2) hv)
  have hg'I : g' ∈ V ⊔ conjSub g'⁻¹ V := by
    have := mul_mem_conjSub (g := l) hgI
    rwa [conjSub_sup, conjSub_eq_of_mem_normalizer hlV, ← hconj] at this
  have hg'N : g' ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hI' hg'I)
  have hVR := h.V_le_pCoreOf_normalizer hVU
  have hVgR : conjSub g'⁻¹ V ≤ pCoreOf 2 (Subgroup.normalizer (V₂ : Set G)) := by
    have := conjSub_mono g'⁻¹ hVR
    rwa [conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 _ (Subgroup.inv_mem _ hg'N))]
      at this
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem (pCoreOf_isPGroup 2 _) ((sup_le hVR hVgR) hg'I)
  have hord : orderOf g' = orderOf g := orderOf_conj' l g
  exact not_two_pow_of_odd (hord ▸ hodd) (hord ▸ h1) k hk

theorem le_normalizer_conj (hVU : ¬ V ≤ H ⊓ Subgroup.centralizer (conjClosure V₃ H : Set G))
    {g : G} (hg : g ∈ H) (hodd : Odd (orderOf g)) (h1 : orderOf g ≠ 1)
    (hgI : g ∈ V ⊔ conjSub g⁻¹ V) :
    V ≤ Subgroup.normalizer (conjSub g⁻¹ V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQ
  have hV₅Q : V₅ ≤ Q := by
    rw [← h.V_inf_Q_eq hVU]
    exact inf_le_right
  have hV : IsElemAbelian 2 V := h.elemAbelian
  have hVg : IsElemAbelian 2 (conjSub g⁻¹ V) := isElemAbelian_conjSub hV
  have hk1 := h.key hVU hg hodd h1 hgI
  have hgI' : g⁻¹ ∈ V ⊔ conjSub g⁻¹⁻¹ V := by
    rw [inv_inv]
    have := mul_mem_conjSub (g := g) (Subgroup.inv_mem _ hgI)
    rwa [show g * g⁻¹ * g⁻¹ = g⁻¹ by group, conjSub_sup, conjSub_inv_conjSub, sup_comm] at this
  have hk2 := h.key hVU (H.inv_mem hg) (by rwa [orderOf_inv]) (by rwa [orderOf_inv]) hgI'
  rw [inv_inv] at hk2
  have hk2' : ∀ x ∈ V₅, ∀ c ∈ conjSub g⁻¹ V₃, c * x = x * c := by
    intro x hx c hc
    rw [mem_conjSub, inv_inv] at hc
    have := hk2 (g * x * g⁻¹) (mul_mem_conjSub hx) _ hc
    calc c * x = g⁻¹ * ((g * c * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * c * g⁻¹)) * g := by rw [this]
      _ = x * c := by group
  have hQg : ∀ k ∈ H, conjSub k V₅ ≤ Q := fun k hk => by
    have := conjSub_mono k hV₅Q
    rwa [conjSub_pCoreOf hk] at this
  have hb1 : ∀ v ∈ V, ∀ x ∈ conjSub g⁻¹ V₅, v * x * v⁻¹ * x⁻¹ ∈ V₃ := by
    intro v hv x hx
    have hxQ := hQg g⁻¹ (H.inv_mem hg) hx
    exact h.wc x (h.T_le_normalizer (h.pCoreOf_le_T hxQ))
      (Subgroup.mem_centralizer_iff.2 fun c hc => hk1 x hx c hc) v hv
  have hb2 : ∀ u ∈ conjSub g⁻¹ V, ∀ x ∈ V₅, u * x * u⁻¹ * x⁻¹ ∈ conjSub g⁻¹ V₃ := by
    intro u hu x hx
    have hx' : g * x * g⁻¹ ∈ conjSub g V₅ := mul_mem_conjSub hx
    have hxQ := hQg g hg hx'
    have hu' : g * u * g⁻¹ ∈ V := by
      rw [mem_conjSub, inv_inv] at hu
      exact hu
    have h2 := h.wc _ (h.T_le_normalizer (h.pCoreOf_le_T hxQ))
      (Subgroup.mem_centralizer_iff.2 fun c hc => hk2 _ hx' c hc) _ hu'
    rw [mem_conjSub, inv_inv]
    convert h2 using 1
    group
  set X := V₅ ⊔ conjSub g⁻¹ V₅ with hX
  set Y := V₃ ⊔ conjSub g⁻¹ V₃ with hY
  have hXY : X ≤ Subgroup.centralizer (Y : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (fun c hc => Subgroup.mem_centralizer_iff.2 fun x hx =>
        isElemAbelian_comm hV (h.le5 hx) (h.V₃_le_V hc))
        (fun c hc => Subgroup.mem_centralizer_iff.2 fun x hx => (hk2' x hx c hc).symm)
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (fun c hc => Subgroup.mem_centralizer_iff.2 fun x hx => (hk1 x hx c hc).symm)
        (fun c hc => Subgroup.mem_centralizer_iff.2 fun x hx =>
          isElemAbelian_comm hVg (conjSub_mono _ h.le5 hx) (conjSub_mono _ h.V₃_le_V hc))
  have hYX : Y ≤ X :=
    sup_le (h.le35.trans le_sup_left) ((conjSub_mono _ h.le35).trans le_sup_right)
  have htriv : ∀ {B : Subgroup G}, IsElemAbelian 2 B → ∀ y ∈ B, ∀ x ∈ B,
      y * x * y⁻¹ * x⁻¹ ∈ Y := by
    intro B hB y hy x hx
    rw [show y * x * y⁻¹ * x⁻¹ = 1 by rw [isElemAbelian_comm hB hy hx]; group]
    exact Y.one_mem
  have hAV := acts_trivially_of_gens (A := V) hXY hYX
    (fun y hy x hx => htriv hV y hy x (h.le5 hx))
    (fun y hy x hx => Subgroup.mem_sup_left (hb1 y hy x hx))
    (fun y hy x hx => htriv hV y hy x (h.V₃_le_V hx))
    (fun y hy x hx => Subgroup.mem_sup_left (hb1 y hy x (conjSub_mono _ h.le35 hx)))
  have hAVg := acts_trivially_of_gens (A := conjSub g⁻¹ V) hXY hYX
    (fun y hy x hx => Subgroup.mem_sup_right (hb2 y hy x hx))
    (fun y hy x hx => htriv hVg y hy x (conjSub_mono _ h.le5 hx))
    (fun y hy x hx => Subgroup.mem_sup_right (hb2 y hy x (h.le35 hx)))
    (fun y hy x hx => htriv hVg y hy x (conjSub_mono _ h.V₃_le_V hx))
  obtain ⟨-, -, hgX⟩ := acts_trivially_sup hAV hAVg g⁻¹ (Subgroup.inv_mem _ hgI)
  set A := conjSub g⁻¹ V ⊓ Subgroup.centralizer (V : Set G) with hA
  have hV₃gN : conjSub g⁻¹ V₃ ≤ Subgroup.normalizer (V₃ : Set G) := fun c' hc' =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun c hc =>
      hk1 c' (conjSub_mono _ h.le35 hc') c hc)
  have hYm : (Y : Set G) = (V₃ : Set G) * (conjSub g⁻¹ V₃ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left V₃ (conjSub g⁻¹ V₃) hV₃gN
  have hV₅A : conjSub g⁻¹ V₅ ≤ conjSub g⁻¹ V₃ ⊔ A := by
    intro b hb
    have hx : g * b * g⁻¹ ∈ V₅ := by
      rw [mem_conjSub, inv_inv] at hb
      exact hb
    have h2 := hgX _ (Subgroup.mem_sup_left hx)
    rw [show g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b by group] at h2
    have h3 : b * (g * b * g⁻¹)⁻¹ ∈ (V₃ : Set G) * (conjSub g⁻¹ V₃ : Set G) := by
      rw [← hYm]
      exact h2
    obtain ⟨c, hc, c', hc', hcc⟩ := h3
    have hcc' : c * c' = b * (g * b * g⁻¹)⁻¹ := hcc
    have hcomm : c * c' = c' * c := hk1 c' (conjSub_mono _ h.le35 hc') c hc
    have hbe : c'⁻¹ * b = c * (g * b * g⁻¹) := by
      have e1 : b = c * c' * (g * b * g⁻¹) := by rw [hcc']; group
      calc c'⁻¹ * b = c'⁻¹ * (c * c' * (g * b * g⁻¹)) := by rw [← e1]
        _ = c'⁻¹ * (c' * c) * (g * b * g⁻¹) := by rw [hcomm]; group
        _ = c * (g * b * g⁻¹) := by group
    have hb' : c'⁻¹ * b ∈ A := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (conjSub_mono _ h.V₃_le_V hc'))
        (conjSub_mono _ h.le5 hb), ?_⟩
      rw [hbe]
      exact h.V_le_centralizer (V.mul_mem (h.V₃_le_V hc) (h.le5 hx))
    rw [show b = c' * (c'⁻¹ * b) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right hb')
  have hcc : ∀ X : Subgroup G, Nat.card (conjSub g⁻¹ X) = Nat.card X := fun X =>
    Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
  have hcV₃ : Nat.card (conjSub g⁻¹ V₃) = 8 := by rw [hcc, h.card3]
  have hcV₅ : Nat.card (conjSub g⁻¹ V₅) = 32 := by rw [hcc, h.card5]
  have hcV : Nat.card (conjSub g⁻¹ V) = 64 := by rw [hcc, h.card]
  have hV₁I : V₁ ≤ conjSub g⁻¹ V₃ ⊓ A :=
    le_inf (h.V₁_le_conjSub (H.inv_mem hg) (h.le12.trans h.le23))
      (le_inf (h.V₁_le_conjSub (H.inv_mem hg) h.V₁_le_V) h.V₁_le_centralizer)
  have hI2 : 2 ≤ Nat.card (conjSub g⁻¹ V₃ ⊓ A : Subgroup G) :=
    h.f91.card_V₁ ▸ Subgroup.card_le_of_le hV₁I
  have hnorm : conjSub g⁻¹ V₃ ≤ Subgroup.normalizer (A : Set G) := fun c' hc' =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha =>
      isElemAbelian_comm hVg ha.1 (conjSub_mono _ h.V₃_le_V hc'))
  have hprod := card_sup_mul_card_inf' hnorm
  have hle := Subgroup.card_le_of_le hV₅A
  rw [hcV₃] at hprod
  rw [hcV₅] at hle
  have hA8 : 8 ≤ Nat.card A := by nlinarith
  have hidx : A.relIndex (conjSub g⁻¹ V) ≤ 8 := by
    have := card_mul_relIndex' (inf_le_left : A ≤ conjSub g⁻¹ V)
    rw [hcV] at this
    nlinarith
  set F := conjSub g A with hF
  have hFV : F ≤ V := by
    have := conjSub_mono g (inf_le_left : A ≤ conjSub g⁻¹ V)
    rwa [conjSub_inv_conjSub] at this
  have hFidx : F.relIndex V ≤ 8 := by
    have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A
      (conjSub g⁻¹ V) (MulAut.conj g).injective
    have e : (conjSub g⁻¹ V).map (MulAut.conj g).toMonoidHom = V := conjSub_inv_conjSub g V
    rw [e] at this
    rw [hF]
    exact this ▸ hidx
  have hcod := h.cod F hFV hFidx
  have hAF : A = conjSub g⁻¹ F := by rw [hF, conjSub_conjSub_inv]
  have h3 : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (conjSub g⁻¹ V : Set G) := by
    rw [hAF, conjSub_centralizer, conjSub_normalizer]
    exact conjSub_mono _ hcod
  intro v hv
  exact h3 (Subgroup.mem_centralizer_iff.2 fun a ha =>
    (Subgroup.mem_centralizer_iff.1 ha.2 v hv).symm)

theorem isElemAbelian : IsElemAbelian 2 (conjClosure V H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hab
  have hVU := h.not_V_le_centralizer_U hab
  obtain ⟨g, hg, hodd, h1, hgI⟩ := h.exists_odd hVU
  have hN := h.le_normalizer_conj hVU hg hodd h1 hgI
  have hP : IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_of_isElemAbelian h.elemAbelian)
      (isPGroup_conjSub (isPGroup_of_isElemAbelian h.elemAbelian)) hN
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hP hgI
  exact not_two_pow_of_odd hodd h1 k hk

end HullHyp

end CFSG.Quasithin.H13.U3
