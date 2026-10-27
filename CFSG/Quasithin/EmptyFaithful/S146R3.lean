module

public import CFSG.Quasithin.Background.F9Section
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section V4

variable {Γ : Type*} [Group Γ]

theorem v4_mem_four {W : Subgroup Γ} (hW : Nat.card W = 4) (hexp : ∀ y ∈ W, y * y = 1) {w y : Γ}
    (hw : w ∈ W) (hy : y ∈ W) (hw1 : w ≠ 1) (hy1 : y ≠ 1) (hyw : y ≠ w) :
    ∀ z ∈ W, z = 1 ∨ z = w ∨ z = y ∨ z = w * y := by
  intro z hz
  by_contra hcon
  push Not at hcon
  obtain ⟨hz1, hzw, hzy, hzwy⟩ := hcon
  have hwy : w * y ∈ W := W.mul_mem hw hy
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have hfin : (W : Set Γ).Finite := Set.toFinite _
  have hwy1 : w * y ≠ 1 := fun h => hyw (by
    have := hexp w hw
    calc y = w⁻¹ * (w * y) := by group
      _ = w⁻¹ := by rw [h, mul_one]
      _ = w := by
        rw [inv_eq_iff_mul_eq_one]
        exact this)
  have hwyw : w * y ≠ w := fun h => hy1 (by simpa using h)
  have hwyy : w * y ≠ y := fun h => hw1 (by simpa using h)
  have c1 : ({1} : Set Γ).ncard = 1 := Set.ncard_singleton _
  have c2 : (insert w ({1} : Set Γ)).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem (by simpa using hw1), c1]
  have c3 : (insert y (insert w ({1} : Set Γ))).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hyw, hy1]), c2]
  have c4 : (insert (w * y) (insert y (insert w ({1} : Set Γ)))).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hwyy, hwyw, hwy1]), c3]
  have c5 : (insert z (insert (w * y) (insert y (insert w ({1} : Set Γ))))).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hzwy, hzy, hzw, hz1]), c4]
  have hsub : (insert z (insert (w * y) (insert y (insert w ({1} : Set Γ))))) ⊆ (W : Set Γ) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact hwy
    · exact hy
    · exact hw
    · exact W.one_mem
  have := Set.ncard_le_ncard hsub hfin
  rw [c5, ← Nat.card_coe_set_eq] at this
  have e : Nat.card (W : Set Γ) = Nat.card W := rfl
  omega

theorem v4_centralizes {W : Subgroup Γ} (hW : Nat.card W = 4) (hexp : ∀ y ∈ W, y * y = 1) {x : Γ}
    (hx : x ∈ Subgroup.normalizer (W : Set Γ)) (h3 : x ^ 3 = 1) {w : Γ} (hw : w ∈ W) (hw1 : w ≠ 1)
    (hxw : x * w * x⁻¹ = w) : ∀ y ∈ W, x * y * x⁻¹ = y := by
  intro y hy
  by_cases hy1 : y = 1
  · subst hy1; simp
  by_cases hyw : y = w
  · subst hyw; exact hxw
  have hb : x * y * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  rcases v4_mem_four hW hexp hw hy hw1 hy1 hyw _ hb with h | h | h | h
  · exact absurd (by simpa using h) hy1
  · exact absurd (by
      have : x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * w * x := by rw [h]
      have e1 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      have e2 : x⁻¹ * w * x = w := by
        calc x⁻¹ * w * x = x⁻¹ * (x * w * x⁻¹) * x := by rw [hxw]
          _ = w := by group
      rw [e1, e2] at this
      exact this) hyw
  · exact h
  · exfalso
    have hw2 : w * w = 1 := hexp w hw
    have hx3 : x * (x * x) = 1 := by
      calc x * (x * x) = x ^ 3 := (pow_three x).symm
        _ = 1 := h3
    have hinv : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right hx3
    have h2 : x * (x * y * x⁻¹) * x⁻¹ = y := by
      rw [h]
      calc x * (w * y) * x⁻¹ = (x * w * x⁻¹) * (x * y * x⁻¹) := by group
        _ = w * (w * y) := by rw [hxw, h]
        _ = (w * w) * y := by group
        _ = y := by rw [hw2, one_mul]
    have h2' : x * x * y = y * (x * x) := by
      have : x * x * y * (x * x)⁻¹ = y := by
        calc x * x * y * (x * x)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by group
          _ = y := h2
      exact mul_inv_eq_iff_eq_mul.mp this
    have h4 : x * y * x⁻¹ = y := by
      calc x * y * x⁻¹ = x * (y * (x * x)) := by rw [hinv]; group
        _ = x * (x * x * y) := by rw [h2']
        _ = x * (x * x) * y := by group
        _ = y := by rw [hx3, one_mul]
    exact hw1 (by simpa using (show w * y = y by rw [← h, h4]))

theorem v4_eq_of_invariant {W E : Subgroup Γ} (hW : Nat.card W = 4) (hexp : ∀ y ∈ W, y * y = 1)
    (hEW : E ≤ W) {x : Γ} (hx : x ∈ Subgroup.normalizer (W : Set Γ)) (h3 : x ^ 3 = 1)
    (hxE : ∀ a ∈ E, x * a * x⁻¹ ∈ E) (hnc : ∃ y ∈ W, x * y * x⁻¹ ≠ y) (hE : E ≠ ⊥) : E = W := by
  obtain ⟨⟨a, haE⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hbE : x * a * x⁻¹ ∈ E := hxE a haE
  have hba : x * a * x⁻¹ ≠ a := by
    intro hxa
    obtain ⟨y, hyW, hy⟩ := hnc
    exact hy (v4_centralizes hW hexp hx h3 (hEW haE) ha1' hxa y hyW)
  have hb1 : x * a * x⁻¹ ≠ 1 := fun h => ha1' (by simpa using h)
  have hfin : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have : Finite E := Finite.of_injective (Subgroup.inclusion hEW) (Subgroup.inclusion_injective hEW)
  have hEfin : (E : Set Γ).Finite := Set.toFinite _
  have h3card : ({1, a, x * a * x⁻¹} : Set Γ).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, a, x * a * x⁻¹, ha1'.symm, hb1.symm, hba.symm, rfl⟩
  have hsub : ({1, a, x * a * x⁻¹} : Set Γ) ⊆ (E : Set Γ) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact E.one_mem
    · exact haE
    · exact hbE
  have hle := Set.ncard_le_ncard hsub hEfin
  rw [h3card, ← Nat.card_coe_set_eq] at hle
  have hdvd : Nat.card E ∣ Nat.card W := Subgroup.card_dvd_of_le hEW
  have e : Nat.card (E : Set Γ) = Nat.card E := rfl
  rw [e] at hle
  rw [hW, show (4 : ℕ) = 2 ^ 2 by norm_num] at hdvd
  obtain ⟨i, hi, hiE⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have : Nat.card E = 4 := by
    interval_cases i <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hEW (by omega)

end V4

section Transfer

variable {G : Type} [Group G]

structure Sec4 (Z U₁ : Subgroup G) (x : G) : Prop where
  le : Z ≤ U₁
  norm : U₁ ≤ Subgroup.normalizer (Z : Set G)
  sq : ∀ a ∈ U₁, a ^ 2 ∈ Z
  card : Z.relIndex U₁ = 4
  xU : x ∈ Subgroup.normalizer (U₁ : Set G)
  xZ : x ∈ Subgroup.normalizer (Z : Set G)
  x3 : x ^ 3 ∈ Z
  nc : ∃ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∉ Z

namespace Sec4

variable {Z U₁ : Subgroup G} {x : G}

theorem card_tilde (h : Sec4 Z U₁ x) : Nat.card (tildeOf Z U₁) = 4 := by
  have h1 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (le_refl Z) h.le h.norm
  have h2 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left, h.card] at h1
  exact h1

theorem exp_tilde (h : Sec4 Z U₁ x) : ∀ y ∈ tildeOf Z U₁, y * y = 1 := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hy
  rw [← map_mul]
  exact secMk_eq_one_iff.mpr (by simpa [pow_two] using h.sq _ hu)

theorem mem_normalizer_tilde (h : Sec4 Z U₁ x) :
    secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ ∈
      Subgroup.normalizer (tildeOf Z U₁ : Set (SecQuot (Subgroup.normalizer (Z : Set G)) Z)) :=
  secMk_mem_normalizer_secImg (a := ⟨x, h.xZ⟩) h.xU

theorem pow_three_tilde (h : Sec4 Z U₁ x) :
    secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ ^ 3 = 1 := by
  rw [← map_pow, secMk_eq_one_iff]
  simpa using h.x3

theorem fixed_mem (h : Sec4 Z U₁ x) {a : G} (ha : a ∈ U₁) (hxa : x * a * x⁻¹ * a⁻¹ ∈ Z) : a ∈ Z := by
  by_contra haZ
  have hW := h.card_tilde
  have hw1 : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ ≠ 1 := fun h1 =>
    haZ (secMk_eq_one_iff.mp h1)
  have hwW : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ ∈ tildeOf Z U₁ :=
    secMk_mem_secImg (x := ⟨a, h.norm ha⟩) ha
  have hcomm := secMk_comm_of_commutator_mem (A := Subgroup.normalizer (Z : Set G)) (K := Z)
    (x := ⟨x, h.xZ⟩) (y := ⟨a, h.norm ha⟩) hxa
  have hxw : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ *
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ *
        (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩)⁻¹ =
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ := by
    rw [hcomm]; group
  have hall := v4_centralizes hW h.exp_tilde h.mem_normalizer_tilde h.pow_three_tilde hwW hw1 hxw
  obtain ⟨y, hy, hyc⟩ := h.nc
  apply hyc
  have hyW : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨y, h.norm hy⟩ ∈ tildeOf Z U₁ :=
    secMk_mem_secImg (x := ⟨y, h.norm hy⟩) hy
  have := hall _ hyW
  have hc : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ *
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨y, h.norm hy⟩ =
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨y, h.norm hy⟩ *
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ := by
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (Z : Set G)) (B := Z)
    (x := ⟨x, h.xZ⟩) (y := ⟨y, h.norm hy⟩) hc

theorem eq_of_invariant (h : Sec4 Z U₁ x) {E : Subgroup G} (hZE : Z ≤ E) (hEU : E ≤ U₁)
    (hxE : ∀ a ∈ E, x * a * x⁻¹ ∈ E) (hE : ¬ E ≤ Z) : E = U₁ := by
  have hW := h.card_tilde
  have hEW : secImg (Subgroup.normalizer (Z : Set G)) Z E ≤ tildeOf Z U₁ := secImg_mono hEU
  have hinv : ∀ y ∈ secImg (Subgroup.normalizer (Z : Set G)) Z E,
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ * y *
        (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩)⁻¹ ∈
        secImg (Subgroup.normalizer (Z : Set G)) Z E := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_secImg.mp hy
    have := secMk_mem_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z)
      (x := ⟨x, h.xZ⟩ * e * ⟨x, h.xZ⟩⁻¹) (by simpa using hxE _ he)
    simpa [map_mul, map_inv] using this
  have hne : secImg (Subgroup.normalizer (Z : Set G)) Z E ≠ ⊥ := by
    intro hbot
    apply hE
    intro e he
    have h1 := secMk_mem_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z)
      (x := ⟨e, h.norm (hEU he)⟩) he
    rw [hbot, Subgroup.mem_bot] at h1
    exact secMk_eq_one_iff.mp h1
  have hnc : ∃ y ∈ tildeOf Z U₁, secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ * y *
      (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩)⁻¹ ≠ y := by
    obtain ⟨y, hy, hyc⟩ := h.nc
    refine ⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨y, h.norm hy⟩,
      secMk_mem_secImg (x := ⟨y, h.norm hy⟩) hy, fun heq => hyc ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at heq
    exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (Z : Set G)) (B := Z)
      (x := ⟨x, h.xZ⟩) (y := ⟨y, h.norm hy⟩) heq
  have hEq := v4_eq_of_invariant hW h.exp_tilde hEW h.mem_normalizer_tilde h.pow_three_tilde hinv
    hnc hne
  refine le_antisymm hEU fun a ha => ?_
  have h1 : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ ∈
      secImg (Subgroup.normalizer (Z : Set G)) Z E := by
    rw [hEq]
    exact secMk_mem_secImg (x := ⟨a, h.norm ha⟩) ha
  exact (secMk_mem_secImg_iff hZE (x := ⟨a, h.norm ha⟩)).mp h1

end Sec4

end Transfer

end CFSG.Quasithin
