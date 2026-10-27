module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Block

public section

namespace CFSG.Quasithin.S14110

open CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G]

structure A4Data (X W : Subgroup G) (c : G) : Prop where
  le : W ≤ X
  card_W : Nat.card W = 4
  sq_eq_one : ∀ w ∈ W, w ^ 2 = 1
  comm : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u
  mem_X : c ∈ X
  order_c : orderOf c = 3
  mem_normalizer : c ∈ normalizer (W : Set G)
  fpf : ∀ w ∈ W, w ≠ 1 → c * w * c⁻¹ ≠ w
  eq_sup : X = W ⊔ zpowers c
  card_X : Nat.card X = 12
  center : ∀ g ∈ X, (∀ l ∈ X, g * l = l * g) → g = 1

theorem A4Data.of_isShort2 {G : Type} [Group G] [Finite G] {L : Subgroup G} (hs : IsShort2 L)
    (ha : IsAltType L 3) : ∃ c, A4Data L (blockU L) c := by
  obtain ⟨-, hcard4, hsq, hcomm, hcard12, hcen, c, hcL, hc3, hcn, hfp, hLeq⟩ :=
    hs.alt3_structure ha
  exact ⟨c, ⟨le_sup_left.trans hLeq.ge, hcard4, hsq, hcomm, hcL, hc3, hcn, hfp, hLeq, hcard12,
    hcen⟩⟩

namespace A4Data

variable {X W : Subgroup G} {c : G} (h : A4Data X W c)
include h

theorem c_pow_three : c ^ 3 = 1 := h.order_c ▸ pow_orderOf_eq_one c

theorem conj_mem {u : G} (hu : u ∈ W) : c * u * c⁻¹ ∈ W :=
  (mem_normalizer_iff.1 h.mem_normalizer u).1 hu

theorem finite_W : Finite W :=
  Nat.finite_of_card_ne_zero (by rw [h.card_W]; norm_num)

theorem le_normalizer : X ≤ normalizer (W : Set G) := by
  rw [h.eq_sup]
  exact sup_le (fun w hw => Subgroup.le_normalizer hw) (zpowers_le.2 h.mem_normalizer)

theorem mem_decomp {x : G} (hx : x ∈ X) : ∃ w ∈ W, ∃ k : ℤ, x = w * c ^ k := by
  have h1 : x ∈ ((W ⊔ zpowers c : Subgroup G) : Set G) := by rw [← h.eq_sup]; exact hx
  rw [coe_mul_of_right_le_normalizer_left W (zpowers c) (zpowers_le.2 h.mem_normalizer)] at h1
  obtain ⟨w, hw, y, hy, rfl⟩ := h1
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  exact ⟨w, hw, k, rfl⟩

theorem zpow_c_eq_one_of_mem {k : ℤ} (hk : c ^ k ∈ W) : c ^ k = 1 := by
  have h2 : (c ^ k) ^ 2 = 1 := h.sq_eq_one _ hk
  have h3 : (c ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast (c ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.c_pow_three,
      one_zpow]
  calc c ^ k = (c ^ k) ^ 3 * ((c ^ k) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3]; simp

theorem mem_W_of_sq_eq_one {x : G} (hx : x ∈ X) (hx2 : x ^ 2 = 1) : x ∈ W := by
  obtain ⟨w, hw, k, rfl⟩ := h.mem_decomp hx
  have hk : c ^ k ∈ normalizer (W : Set G) := zpow_mem h.mem_normalizer k
  have hconj : c ^ k * w * (c ^ k)⁻¹ ∈ W := (mem_normalizer_iff.1 hk w).1 hw
  have h1 : c ^ (2 * k) = (w * (c ^ k * w * (c ^ k)⁻¹))⁻¹ := by
    have : (w * c ^ k) ^ 2 = w * (c ^ k * w * (c ^ k)⁻¹) * c ^ (2 * k) := by
      rw [pow_two]; group
    rw [this] at hx2
    exact eq_inv_of_mul_eq_one_right hx2
  have h2 : c ^ (2 * k) ∈ W := by
    rw [h1]; exact W.inv_mem (W.mul_mem hw hconj)
  have h3 : c ^ (2 * k) = 1 := h.zpow_c_eq_one_of_mem h2
  have h4 : c ^ k = 1 := by
    have h5 : c ^ (3 * k) = 1 := by
      rw [zpow_mul]
      have : c ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact h.c_pow_three
      rw [this, one_zpow]
    calc c ^ k = c ^ (3 * k) * (c ^ (2 * k))⁻¹ := by rw [← zpow_neg, ← zpow_add]; congr 1; ring
      _ = 1 := by rw [h5, h3]; simp
  rw [h4, mul_one]; exact hw

theorem exists_mul_conj_inv_eq {w₁ : G} (hw₁ : w₁ ∈ W) :
    ∃ w₀ ∈ W, w₀ * (c * w₀⁻¹ * c⁻¹) = w₁ := by
  classical
  have hWfin : Finite W := h.finite_W
  let _ : CommGroup W := { (inferInstance : Group W) with
    mul_comm := fun a b => Subtype.ext (h.comm a a.2 b b.2) }
  let ψ : W →* W :=
    (((MulAut.conj c).toMonoidHom.comp W.subtype).codRestrict W (fun a => h.conj_mem a.2))
  let φ : W →* W := MonoidHom.id W * ψ⁻¹
  have hφ : ∀ a : W, ((φ a : W) : G) = a * (c * a⁻¹ * c⁻¹) := fun a => by
    change (a : G) * ((ψ a)⁻¹ : W) = _
    simp [ψ, MulAut.conj_apply, mul_assoc]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : G) * (c * a⁻¹ * c⁻¹) = 1 := by rw [← hφ a, ha]; rfl
    by_contra hne
    have hne' : (a : G) ≠ 1 := fun h' => hne (Subtype.ext h')
    apply h.fpf a a.2 hne'
    have h2 : c * (a : G)⁻¹ * c⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    calc c * (a : G) * c⁻¹ = (c * (a : G)⁻¹ * c⁻¹)⁻¹ := by group
      _ = a := by rw [h2, inv_inv]
  obtain ⟨⟨w₀, hw₀⟩, hw⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨w₁, hw₁⟩
  refine ⟨w₀, hw₀, ?_⟩
  have := hφ ⟨w₀, hw₀⟩
  rw [hw] at this
  exact this.symm

theorem exists_ne_one_mem_W : ∃ u ∈ W, u ≠ 1 := by
  have hWfin : Finite W := h.finite_W
  have : 1 < Nat.card W := by rw [h.card_W]; norm_num
  have hnt : Nontrivial W := (Finite.one_lt_card_iff_nontrivial (α := W)).1 this
  obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : W)
  exact ⟨u, hu, fun h' => hu1 (Subtype.ext h')⟩

theorem zpow_c_eq_one_of_centralizes {j : ℤ} (hj : ∀ u ∈ W, c ^ j * u * (c ^ j)⁻¹ = u) :
    c ^ j = 1 := by
  have hmod : c ^ (j % 3) = c ^ j := by
    have := zpow_mod_orderOf c j
    rw [h.order_c] at this
    simpa using this
  obtain ⟨u, hu, hu1⟩ := h.exists_ne_one_mem_W
  have hc3 : c ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact h.c_pow_three
  have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [← hmod, h0]; simp
  · exfalso
    rw [← hmod, h1] at hj
    have := hj u hu
    simp only [zpow_one] at this
    exact h.fpf u hu hu1 this
  · exfalso
    rw [← hmod, h2] at hj
    apply h.fpf u hu hu1
    have h3 := hj u hu
    calc c * u * c⁻¹ = c * (c ^ (2 : ℤ) * u * (c ^ (2 : ℤ))⁻¹) * c⁻¹ := by rw [h3]
      _ = c ^ (3 : ℤ) * u * (c ^ (3 : ℤ))⁻¹ := by group
      _ = u := by rw [hc3]; simp

theorem exists_mul_mem_centralizer {g : G} (hg : g ∈ normalizer (X : Set G))
    (hgW : g ∈ centralizer (W : Set G)) : ∃ w ∈ W, w⁻¹ * g ∈ centralizer (X : Set G) := by
  have hc' : g * c * g⁻¹ ∈ X := (mem_normalizer_iff.1 hg c).1 h.mem_X
  obtain ⟨w₁, hw₁, k, hk⟩ := h.mem_decomp hc'
  have hgu : ∀ u ∈ W, g * u * g⁻¹ = u := fun u hu => by
    have := mem_centralizer_iff.1 hgW u hu
    calc g * u * g⁻¹ = (u * g) * g⁻¹ := by rw [this]
      _ = u := by group
  have hgu' : ∀ u ∈ W, g⁻¹ * u * g = u := fun u hu => by
    have := mem_centralizer_iff.1 hgW u hu
    calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
      _ = g⁻¹ * (g * u) := by rw [this]
      _ = u := by group
  have hact : ∀ u ∈ W, (g * c * g⁻¹) * u * (g * c * g⁻¹)⁻¹ = c * u * c⁻¹ := by
    intro u hu
    calc g * c * g⁻¹ * u * (g * c * g⁻¹)⁻¹ = g * c * (g⁻¹ * u * g) * c⁻¹ * g⁻¹ := by group
      _ = g * c * u * c⁻¹ * g⁻¹ := by rw [hgu' u hu]
      _ = g * (c * u * c⁻¹) * g⁻¹ := by group
      _ = c * u * c⁻¹ := hgu _ (h.conj_mem hu)
  have hckW : ∀ u ∈ W, c ^ k * u * (c ^ k)⁻¹ ∈ W := fun u hu =>
    (mem_normalizer_iff.1 (zpow_mem h.mem_normalizer k) u).1 hu
  have hact' : ∀ u ∈ W, c ^ k * u * (c ^ k)⁻¹ = c * u * c⁻¹ := by
    intro u hu
    have h1 := hact u hu
    rw [hk] at h1
    have h2 : w₁ * c ^ k * u * (w₁ * c ^ k)⁻¹ = w₁ * (c ^ k * u * (c ^ k)⁻¹) * w₁⁻¹ := by group
    have h3 : w₁ * (c ^ k * u * (c ^ k)⁻¹) = (c ^ k * u * (c ^ k)⁻¹) * w₁ :=
      h.comm _ hw₁ _ (hckW u hu)
    rw [h2, h3] at h1
    calc c ^ k * u * (c ^ k)⁻¹ = c ^ k * u * (c ^ k)⁻¹ * w₁ * w₁⁻¹ := by group
      _ = c * u * c⁻¹ := h1
  have hk1 : c ^ (k - 1) = 1 := by
    apply h.zpow_c_eq_one_of_centralizes
    intro u hu
    calc c ^ (k - 1) * u * (c ^ (k - 1))⁻¹ = c⁻¹ * (c ^ k * u * (c ^ k)⁻¹) * c := by group
      _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [hact' u hu]
      _ = u := by group
  have hck : c ^ k = c := by
    calc c ^ k = c ^ (k - 1) * c := by group
      _ = c := by rw [hk1, one_mul]
  rw [hck] at hk
  obtain ⟨w, hw, hwc⟩ := h.exists_mul_conj_inv_eq hw₁
  refine ⟨w, hw, ?_⟩
  have hwcomm : w ∈ centralizer (W : Set G) := by
    rw [mem_centralizer_iff]; intro u hu; exact h.comm u hu w hw
  have hwc' : w * c * w⁻¹ = w₁ * c := by
    calc w * c * w⁻¹ = (w * (c * w⁻¹ * c⁻¹)) * c := by group
      _ = w₁ * c := by rw [hwc]
  have h0W : ∀ u ∈ W, (w⁻¹ * g) * u * (w⁻¹ * g)⁻¹ = u := by
    intro u hu
    have h1 : w⁻¹ * (g * u * g⁻¹) * w = (w⁻¹ * g) * u * (w⁻¹ * g)⁻¹ := by group
    rw [hgu u hu] at h1
    rw [← h1]
    have := h.comm u hu w hw
    calc w⁻¹ * u * w = w⁻¹ * (u * w) := by group
      _ = w⁻¹ * (w * u) := by rw [this]
      _ = u := by group
  have h0c : (w⁻¹ * g) * c * (w⁻¹ * g)⁻¹ = c := by
    calc (w⁻¹ * g) * c * (w⁻¹ * g)⁻¹ = w⁻¹ * (g * c * g⁻¹) * w := by group
      _ = w⁻¹ * (w₁ * c) * w := by rw [hk]
      _ = w⁻¹ * (w * c * w⁻¹) * w := by rw [hwc']
      _ = c := by group
  have hcent : X ≤ centralizer ({w⁻¹ * g} : Set G) := by
    rw [h.eq_sup]
    refine sup_le (fun u hu => ?_) (zpowers_le.2 ?_)
    · rw [mem_centralizer_singleton_iff]
      have := h0W u hu
      calc u * (w⁻¹ * g) = ((w⁻¹ * g) * u * (w⁻¹ * g)⁻¹) * (w⁻¹ * g) := by rw [this]
        _ = w⁻¹ * g * u := by group
    · rw [mem_centralizer_singleton_iff]
      calc c * (w⁻¹ * g) = ((w⁻¹ * g) * c * (w⁻¹ * g)⁻¹) * (w⁻¹ * g) := by rw [h0c]
        _ = w⁻¹ * g * c := by group
  rw [mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.1 (hcent hx)

end A4Data

end CFSG.Quasithin.S14110
