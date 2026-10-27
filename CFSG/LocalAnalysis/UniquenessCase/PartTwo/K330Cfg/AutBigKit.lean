module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Defs
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def MovesLines {T : Type} [Group T] (X : Subgroup T) (n : T) : Prop :=
  ∀ x ∈ X, x ≠ 1 → n * x * n⁻¹ ≠ x ∧ n * x * n⁻¹ ≠ x⁻¹

private lemma k330c_movesLines_map_conj {T : Type} [Group T] {X : Subgroup T} {n g : T}
    (h : MovesLines X n) :
    MovesLines (X.map (MulAut.conj g).toMonoidHom) (g * n * g⁻¹) := by
  intro x hx hx1
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
  have hx_eq : x = g * y * g⁻¹ := by rw [← hxy]; rfl
  have hy1 : y ≠ 1 := by
    intro h1
    apply hx1
    rw [hx_eq, h1]
    group
  rw [hx_eq]
  constructor
  · intro heq
    exact (h y hy hy1).1 (by
      calc n * y * n⁻¹
          = g⁻¹ * ((g * n * g⁻¹) * (g * y * g⁻¹) * (g * n * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [heq]
        _ = y := by group)
  · intro heq
    exact (h y hy hy1).2 (by
      calc n * y * n⁻¹
          = g⁻¹ * ((g * n * g⁻¹) * (g * y * g⁻¹) * (g * n * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹)⁻¹ * g := by rw [heq]
        _ = y⁻¹ := by group)

private lemma k330c_mem_eq_one_or_eq_or_inv {T : Type} [Group T] {Z : Subgroup T}
    (hZ : Nat.card Z = 3) {x : T} (hx : x ∈ Z) (hx1 : x ≠ 1) :
    ∀ y ∈ Z, y = 1 ∨ y = x ∨ y = x⁻¹ := by
  have hx3 : x ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Z) (x := ⟨x, hx⟩)
    rw [hZ] at h
    simpa using Subtype.ext_iff.mp h
  have hxinv : x⁻¹ = x ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', hx3]
  have horder : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hle : Subgroup.zpowers x ≤ Z := Subgroup.zpowers_le.mpr hx
  have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, horder]
  have hEq : Subgroup.zpowers x = Z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hZ])
  intro y hy
  have hy' : y ∈ Subgroup.zpowers x := hEq ▸ hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
  rw [← hk]
  have hkmod : x ^ k = x ^ (k % (3 : ℤ)) := by
    rw [← zpow_mod_orderOf x k, horder]
    congr 1
  rw [hkmod]
  have hb : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
  rcases hb with h | h | h
  · left; rw [h, zpow_zero]
  · right; left; rw [h, zpow_one]
  · right; right; rw [h, zpow_ofNat, hxinv]

private lemma k330c_not_mem_normalizer_of_movesLines {T : Type} [Group T] {X Z : Subgroup T}
    {n : T} (hZ : Nat.card Z = 3) (hZX : Z ≤ X) (hn : MovesLines X n)
    (hnorm : n ∈ normalizer (Z : Set T)) : False := by
  have hne : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    norm_num at hZ
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hxZ : (x : T) ∈ Z := x.2
  have hx1T : (x : T) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxX : (x : T) ∈ X := hZX hxZ
  have hmem : n * (x : T) * n⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp hnorm (x : T)).mp hxZ
  rcases k330c_mem_eq_one_or_eq_or_inv hZ hxZ hx1T (n * (x : T) * n⁻¹) hmem with h | h | h
  · have hxone : (x : T) = 1 := by
      calc (x : T) = n⁻¹ * (n * (x : T) * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h]
        _ = 1 := by group
    exact hx1T hxone
  · exact (hn (x : T) hxX hx1T).1 h
  · exact (hn (x : T) hxX hx1T).2 h

private lemma k330c_map_conj_mul {T : Type} [Group T] (A : Subgroup T) (a b : T) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private lemma k330c_mem_normalizer_mul_self_of_maps {T : Type} [Group T] {A B : Subgroup T}
    {n : T} (h1 : A.map (MulAut.conj n).toMonoidHom = B)
    (h2 : B.map (MulAut.conj n).toMonoidHom = A) :
    n * n ∈ normalizer (A : Set T) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change A.map (MulAut.conj (n * n)).toMonoidHom = A
  rw [← k330c_map_conj_mul A n n, h1, h2]

private lemma k330c_inv_map_conj_of_map_conj {T : Type} [Group T] {A B : Subgroup T} {n : T}
    (h : A.map (MulAut.conj n).toMonoidHom = B) :
    B.map (MulAut.conj n⁻¹).toMonoidHom = A := by
  have h' : A.map (↑(MulAut.conj n) : T →* T) = B := h
  have h'' := (Subgroup.map_symm_eq_iff_map_eq (H := B) (K := A) (e := MulAut.conj n)).mpr h'
  have hs : ((MulAut.conj n).symm : T →* T) = (MulAut.conj n⁻¹).toMonoidHom := by
    ext x
    simp [MulAut.conj_symm_apply, MulAut.conj_apply]
  rwa [hs] at h''

private lemma k330c_inv_mul_mem_normalizer_of_maps {T : Type} [Group T] {A B : Subgroup T}
    {n₁ n₂ : T} (h₁ : A.map (MulAut.conj n₁).toMonoidHom = B)
    (h₂ : A.map (MulAut.conj n₂).toMonoidHom = B) :
    n₂⁻¹ * n₁ ∈ normalizer (A : Set T) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change A.map (MulAut.conj (n₂⁻¹ * n₁)).toMonoidHom = A
  rw [← k330c_map_conj_mul A n₁ n₂⁻¹, h₁, k330c_inv_map_conj_of_map_conj h₂]

private lemma k330c_not_pair_of_moves {T : Type} [Group T] {X Z₁ Z₂ : Subgroup T} {n : T}
    (hn : MovesLines X n) (hn2 : MovesLines X (n * n)) (hZ₁ : Z₁ ≤ X)
    (hc₁ : Nat.card Z₁ = 3) :
    ¬ ((Z₁.map (MulAut.conj n).toMonoidHom = Z₁ ∧
        Z₂.map (MulAut.conj n).toMonoidHom = Z₂) ∨
       (Z₁.map (MulAut.conj n).toMonoidHom = Z₂ ∧
        Z₂.map (MulAut.conj n).toMonoidHom = Z₁)) := by
  intro h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact k330c_not_mem_normalizer_of_movesLines hc₁ hZ₁ hn
      ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr h1)
  · exact k330c_not_mem_normalizer_of_movesLines hc₁ hZ₁ hn2
      (k330c_mem_normalizer_mul_self_of_maps h1 h2)

theorem automizerBig_of_one {T : Type} [Group T] [Finite T] (X₀ : Subgroup T)
    (hS : IsSylowOf 3 X₀ ⊤) (hE : IsElemAbelian 3 X₀) (h9 : Nat.card X₀ = 9) (n : T)
    (hn : n ∈ normalizer (X₀ : Set T)) (h1 : MovesLines X₀ n) (h2 : MovesLines X₀ (n ^ 2)) :
    AutomizerBig T := by
  intro X hSX _ _ Z₁ Z₂ hZ₁ _ hc₁ _ _
  obtain ⟨k, _, hk⟩ := hSX.exists_mem_conj hS
  set g : T := k⁻¹ with hg
  have hconj : ∀ x : T, x ∈ X₀ ↔ g * x * g⁻¹ ∈ X := by
    intro x
    simpa [hg] using hk x
  have hmemX : ∀ y : T, y ∈ X₀ → g * y * g⁻¹ ∈ X := fun y hy => (hconj y).mp hy
  have hmemX₀ : ∀ z : T, z ∈ X → g⁻¹ * z * g ∈ X₀ := by
    intro z hz
    have hz' : g * (g⁻¹ * z * g) * g⁻¹ ∈ X := by
      convert hz using 1
      group
    exact (hconj (g⁻¹ * z * g)).mpr hz'
  have hX : X = X₀.map (MulAut.conj g).toMonoidHom := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · intro hz
      refine ⟨g⁻¹ * z * g, hmemX₀ z hz, ?_⟩
      change g * (g⁻¹ * z * g) * g⁻¹ = z
      group
    · rintro ⟨y, hy, rfl⟩
      exact hmemX y hy
  have hm₁ : MovesLines X (g * n * g⁻¹) := by
    have h := k330c_movesLines_map_conj (X := X₀) (n := n) (g := g) h1
    rwa [← hX] at h
  have hm₂ : MovesLines X ((g * n * g⁻¹) * (g * n * g⁻¹)) := by
    have h := k330c_movesLines_map_conj (X := X₀) (n := n ^ 2) (g := g) h2
    rw [← hX] at h
    have heq : g * n ^ 2 * g⁻¹ = (g * n * g⁻¹) * (g * n * g⁻¹) := by
      rw [pow_two]
      group
    rwa [heq] at h
  have hmX : g * n * g⁻¹ ∈ normalizer (X : Set T) := by
    have hnorm := Subgroup.map_equiv_normalizer_eq X₀ (MulAut.conj g)
    rw [← hX] at hnorm
    rw [← hnorm]
    exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  refine ⟨g * n * g⁻¹, hmX, ?_⟩
  exact k330c_not_pair_of_moves hm₁ hm₂ hZ₁ hc₁

theorem automizerBig_of_two {T : Type} [Group T] [Finite T] (X₀ : Subgroup T)
    (hS : IsSylowOf 3 X₀ ⊤) (hE : IsElemAbelian 3 X₀) (h9 : Nat.card X₀ = 9) (n₁ n₂ : T)
    (hn₁ : n₁ ∈ normalizer (X₀ : Set T)) (hn₂ : n₂ ∈ normalizer (X₀ : Set T))
    (h1 : MovesLines X₀ n₁) (h2 : MovesLines X₀ n₂) (h3 : MovesLines X₀ (n₂⁻¹ * n₁)) :
    AutomizerBig T := by
  intro X hSX _ _ Z₁ Z₂ hZ₁ _ hc₁ _ _
  obtain ⟨k, _, hk⟩ := hSX.exists_mem_conj hS
  set g : T := k⁻¹ with hg
  have hconj : ∀ x : T, x ∈ X₀ ↔ g * x * g⁻¹ ∈ X := by
    intro x
    simpa [hg] using hk x
  have hmemX : ∀ y : T, y ∈ X₀ → g * y * g⁻¹ ∈ X := fun y hy => (hconj y).mp hy
  have hmemX₀ : ∀ z : T, z ∈ X → g⁻¹ * z * g ∈ X₀ := by
    intro z hz
    have hz' : g * (g⁻¹ * z * g) * g⁻¹ ∈ X := by
      convert hz using 1
      group
    exact (hconj (g⁻¹ * z * g)).mpr hz'
  have hX : X = X₀.map (MulAut.conj g).toMonoidHom := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · intro hz
      refine ⟨g⁻¹ * z * g, hmemX₀ z hz, ?_⟩
      change g * (g⁻¹ * z * g) * g⁻¹ = z
      group
    · rintro ⟨y, hy, rfl⟩
      exact hmemX y hy
  have hm₁ : MovesLines X (g * n₁ * g⁻¹) := by
    have h := k330c_movesLines_map_conj (X := X₀) (n := n₁) (g := g) h1
    rwa [← hX] at h
  have hm₂ : MovesLines X (g * n₂ * g⁻¹) := by
    have h := k330c_movesLines_map_conj (X := X₀) (n := n₂) (g := g) h2
    rwa [← hX] at h
  have hm₃ : MovesLines X ((g * n₂ * g⁻¹)⁻¹ * (g * n₁ * g⁻¹)) := by
    have h := k330c_movesLines_map_conj (X := X₀) (n := n₂⁻¹ * n₁) (g := g) h3
    rw [← hX] at h
    have heq : g * (n₂⁻¹ * n₁) * g⁻¹ = (g * n₂ * g⁻¹)⁻¹ * (g * n₁ * g⁻¹) := by group
    rwa [heq] at h
  have hn₁X : g * n₁ * g⁻¹ ∈ normalizer (X : Set T) := by
    have hnorm := Subgroup.map_equiv_normalizer_eq X₀ (MulAut.conj g)
    rw [← hX] at hnorm
    rw [← hnorm]
    exact Subgroup.mem_map.mpr ⟨n₁, hn₁, rfl⟩
  have hn₂X : g * n₂ * g⁻¹ ∈ normalizer (X : Set T) := by
    have hnorm := Subgroup.map_equiv_normalizer_eq X₀ (MulAut.conj g)
    rw [← hX] at hnorm
    rw [← hnorm]
    exact Subgroup.mem_map.mpr ⟨n₂, hn₂, rfl⟩
  by_contra hcon
  have hP₁ : (Z₁.map (MulAut.conj (g * n₁ * g⁻¹)).toMonoidHom = Z₁ ∧
      Z₂.map (MulAut.conj (g * n₁ * g⁻¹)).toMonoidHom = Z₂) ∨
      (Z₁.map (MulAut.conj (g * n₁ * g⁻¹)).toMonoidHom = Z₂ ∧
      Z₂.map (MulAut.conj (g * n₁ * g⁻¹)).toMonoidHom = Z₁) := by
    by_contra hc
    exact hcon ⟨g * n₁ * g⁻¹, hn₁X, hc⟩
  have hP₂ : (Z₁.map (MulAut.conj (g * n₂ * g⁻¹)).toMonoidHom = Z₁ ∧
      Z₂.map (MulAut.conj (g * n₂ * g⁻¹)).toMonoidHom = Z₂) ∨
      (Z₁.map (MulAut.conj (g * n₂ * g⁻¹)).toMonoidHom = Z₂ ∧
      Z₂.map (MulAut.conj (g * n₂ * g⁻¹)).toMonoidHom = Z₁) := by
    by_contra hc
    exact hcon ⟨g * n₂ * g⁻¹, hn₂X, hc⟩
  have hsw₁ : Z₁.map (MulAut.conj (g * n₁ * g⁻¹)).toMonoidHom = Z₂ ∧
      Z₂.map (MulAut.conj (g * n₁ * g⁻¹)).toMonoidHom = Z₁ := by
    rcases hP₁ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact absurd ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr ha)
        (k330c_not_mem_normalizer_of_movesLines hc₁ hZ₁ hm₁)
    · exact ⟨ha, hb⟩
  have hsw₂ : Z₁.map (MulAut.conj (g * n₂ * g⁻¹)).toMonoidHom = Z₂ ∧
      Z₂.map (MulAut.conj (g * n₂ * g⁻¹)).toMonoidHom = Z₁ := by
    rcases hP₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact absurd ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr ha)
        (k330c_not_mem_normalizer_of_movesLines hc₁ hZ₁ hm₂)
    · exact ⟨ha, hb⟩
  exact k330c_not_mem_normalizer_of_movesLines hc₁ hZ₁ hm₃
    (k330c_inv_mul_mem_normalizer_of_maps hsw₁.1 hsw₂.1)

@[expose] def HasHeis (T : Type) [Group T] : Prop :=
  ∃ a b u v : T, a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
    Nat.card (Subgroup.closure {a, b}) = 9 ∧ u * a * u⁻¹ = b⁻¹ ∧ u * b * u⁻¹ = a ∧
    v * a * v⁻¹ = a ^ 2 * b ^ 2 ∧ v * b * v⁻¹ = a ^ 2 * b

private lemma k330c_eq_one_of_sq_eq_one {T : Type} [Group T] {X : Subgroup T}
    (hcard : Nat.card X = 9) {x : T} (hx : x ∈ X) (hx2 : x ^ 2 = 1) : x = 1 := by
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hx2' : (⟨x, hx⟩ : X) ^ 2 = 1 := Subtype.ext hx2
  have horder : orderOf (⟨x, hx⟩ : X) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2'
  have hdvd : orderOf (⟨x, hx⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
  have hone : orderOf (⟨x, hx⟩ : X) = 1 := by
    have h := Nat.dvd_gcd horder hdvd
    rw [hcard, show Nat.gcd 2 9 = 1 by norm_num, Nat.dvd_one] at h
    exact h
  simpa using Subtype.ext_iff.mp (orderOf_eq_one_iff.mp hone)

private lemma k330c_movesLines_of_sq_inv {T : Type} [Group T] {X : Subgroup T} {m : T}
    (hcard : Nat.card X = 9)
    (hsq : ∀ x ∈ X, m * m * x * (m * m)⁻¹ = x⁻¹) : MovesLines X m := by
  intro x hx hx1
  have key : ∀ h : x * x = 1, False := fun h =>
    hx1 (k330c_eq_one_of_sq_eq_one hcard hx (by rw [pow_two]; exact h))
  constructor
  · intro h
    have h2 : m * m * x * (m * m)⁻¹ = x := by
      calc m * m * x * (m * m)⁻¹ = m * (m * x * m⁻¹) * m⁻¹ := by group
        _ = m * x * m⁻¹ := by conv_lhs => rw [h]
        _ = x := h
    have hxinv : x⁻¹ = x := by rw [← hsq x hx, h2]
    exact key ((congrArg (fun t => x * t) hxinv.symm).trans (mul_inv_cancel x))
  · intro h
    have h2 : m * m * x * (m * m)⁻¹ = x := by
      calc m * m * x * (m * m)⁻¹ = m * (m * x * m⁻¹) * m⁻¹ := by group
        _ = m * x⁻¹ * m⁻¹ := by conv_lhs => rw [h]
        _ = (m * x * m⁻¹)⁻¹ := by group
        _ = x := by rw [h]; group
    have hxinv : x⁻¹ = x := by rw [← hsq x hx, h2]
    exact key ((congrArg (fun t => x * t) hxinv.symm).trans (mul_inv_cancel x))

private lemma k330c_pow_mod_three {T : Type} [Group T] {a : T} (ha : a ^ 3 = 1) (n : ℕ) :
    a ^ n = a ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3]
  rw [pow_add, pow_mul, ha, one_pow, mul_one]

private lemma k330c_sq_mul_eq_one {T : Type} [Group T] {a : T} (ha : a ^ 3 = 1) :
    a ^ 2 * a = 1 := by
  rw [← pow_succ]
  simpa using ha

private lemma k330c_inv_sq_eq_self {T : Type} [Group T] {a : T} (ha : a ^ 3 = 1) :
    (a ^ 2)⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (k330c_sq_mul_eq_one ha)

private lemma k330c_commute_mul_pow {T : Type} [Group T] {a b : T} (h : Commute a b)
    (m n k l : ℕ) :
    (a ^ m * b ^ n) * (a ^ k * b ^ l) = a ^ (m + k) * b ^ (n + l) := by
  have hc : Commute (b ^ n) (a ^ k) := (h.pow_pow k n).symm
  calc (a ^ m * b ^ n) * (a ^ k * b ^ l)
      = a ^ m * (b ^ n * a ^ k) * b ^ l := by group
    _ = a ^ m * (a ^ k * b ^ n) * b ^ l := by rw [hc.eq]
    _ = (a ^ m * a ^ k) * (b ^ n * b ^ l) := by group
    _ = a ^ (m + k) * b ^ (n + l) := by rw [pow_add, pow_add]

private lemma k330c_commute_mul_pow_one {T : Type} [Group T] {a b : T} (h : Commute a b)
    (m n k : ℕ) :
    (a ^ m * b ^ n) * (a ^ k * b) = a ^ (m + k) * b ^ (n + 1) := by
  simpa using k330c_commute_mul_pow h m n k 1

private lemma k330c_commute_mul_pow_ones {T : Type} [Group T] {a b : T} (h : Commute a b)
    (m n : ℕ) :
    (a ^ m * b ^ n) * (a * b) = a ^ (m + 1) * b ^ (n + 1) := by
  simpa using k330c_commute_mul_pow h m n 1 1

private lemma k330c_commute_mul_pow_ab {T : Type} [Group T] {a b : T} (h : Commute a b)
    (m : ℕ) : (a ^ m * b) * (a * b) = a ^ (m + 1) * b ^ 2 := by
  simpa using k330c_commute_mul_pow h m 1 1 1

private lemma k330c_heis_v2a {T : Type} [Group T] {a b : T}
    (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a ^ 2 * b ^ 2) ^ 2 * (a ^ 2 * b) ^ 2 = a⁻¹ := by
  have h1 : (a ^ 2 * b ^ 2) ^ 2 = a ^ 4 * b ^ 4 := by
    rw [(hab.pow_pow 2 2).mul_pow 2, ← pow_mul, ← pow_mul]
  have h2 : (a ^ 2 * b) ^ 2 = a ^ 4 * b ^ 2 := by
    rw [(hab.pow_left 2).mul_pow 2, ← pow_mul]
  rw [h1, h2, k330c_commute_mul_pow hab 4 4 4 2,
    k330c_pow_mod_three ha (4 + 4), k330c_pow_mod_three hb (4 + 2)]
  norm_num
  exact eq_inv_of_mul_eq_one_left (k330c_sq_mul_eq_one ha)

private lemma k330c_heis_v2b {T : Type} [Group T] {a b : T}
    (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a ^ 2 * b ^ 2) ^ 2 * (a ^ 2 * b) = b⁻¹ := by
  have h1 : (a ^ 2 * b ^ 2) ^ 2 = a ^ 4 * b ^ 4 := by
    rw [(hab.pow_pow 2 2).mul_pow 2, ← pow_mul, ← pow_mul]
  rw [h1, k330c_commute_mul_pow_one hab 4 4 2,
    k330c_pow_mod_three ha (4 + 2), k330c_pow_mod_three hb (4 + 1)]
  norm_num
  exact eq_inv_of_mul_eq_one_left (k330c_sq_mul_eq_one hb)

private lemma k330c_heis_w2a {T : Type} [Group T] {a b : T}
    (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a ^ 2 * b) ^ 2 * (a * b) = a⁻¹ := by
  have h1 : (a ^ 2 * b) ^ 2 = a ^ 4 * b ^ 2 := by
    rw [(hab.pow_left 2).mul_pow 2, ← pow_mul]
  rw [h1, k330c_commute_mul_pow_ones hab 4 2,
    k330c_pow_mod_three ha (4 + 1), k330c_pow_mod_three hb (2 + 1)]
  norm_num
  exact eq_inv_of_mul_eq_one_left (k330c_sq_mul_eq_one ha)

private lemma k330c_heis_w2b {T : Type} [Group T] {a b : T}
    (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a ^ 2 * b) * (a * b) = b⁻¹ := by
  rw [k330c_commute_mul_pow_ab hab 2,
    k330c_pow_mod_three ha (2 + 1), k330c_pow_mod_three hb 2]
  norm_num
  exact eq_inv_of_mul_eq_one_left (k330c_sq_mul_eq_one hb)

private lemma k330c_heis_inv_a2b2 {T : Type} [Group T] {a b : T}
    (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a ^ 2 * b ^ 2)⁻¹ = a * b := by
  calc (a ^ 2 * b ^ 2)⁻¹ = (b ^ 2)⁻¹ * (a ^ 2)⁻¹ := by rw [mul_inv_rev]
    _ = b * a := by rw [k330c_inv_sq_eq_self ha, k330c_inv_sq_eq_self hb]
    _ = a * b := hab.eq.symm

private lemma k330c_conj_sq_eq_inv_closure {T : Type} [Group T] {a b w : T}
    (hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set T),
      ∀ y ∈ Subgroup.closure ({a, b} : Set T), x * y = y * x)
    (ha : w * a * w⁻¹ = a⁻¹)
    (hb : w * b * w⁻¹ = b⁻¹) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set T), w * x * w⁻¹ = x⁻¹ := by
  intro x hx
  refine Subgroup.closure_induction (p := fun y _ => w * y * w⁻¹ = y⁻¹) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]; exact ha
    · rw [hy]; exact hb
  · rw [mul_one, inv_one]
    group
  · intro y z hy hz ihy ihz
    calc w * (y * z) * w⁻¹ = (w * y * w⁻¹) * (w * z * w⁻¹) := by group
      _ = y⁻¹ * z⁻¹ := by rw [ihy, ihz]
      _ = (y * z)⁻¹ := by
          rw [mul_inv_rev]
          exact hcomm y⁻¹ (Subgroup.inv_mem _ hy) z⁻¹ (Subgroup.inv_mem _ hz)
  · intro y hy ihy
    have h1 : w * y⁻¹ * w⁻¹ = (w * y * w⁻¹)⁻¹ := by group
    rw [h1, ihy, inv_inv]

private lemma k330c_sq_sq_eq_self {T : Type} [Group T] {X : Subgroup T} {w : T}
    (hw : ∀ x ∈ X, w * x * w⁻¹ = x⁻¹) :
    ∀ x ∈ X, (w * w) * x * (w * w)⁻¹ = x := by
  intro x hx
  calc (w * w) * x * (w * w)⁻¹ = w * (w * x * w⁻¹) * w⁻¹ := by group
    _ = w * x⁻¹ * w⁻¹ := by rw [hw x hx]
    _ = (w * x * w⁻¹)⁻¹ := by group
    _ = (x⁻¹)⁻¹ := by rw [hw x hx]
    _ = x := by rw [inv_inv]

private lemma k330c_inv_mul_eq_cube {T : Type} [Group T] {v y : T}
    (h4 : (v * v) * (v * v) * y * ((v * v) * (v * v))⁻¹ = y) :
    v⁻¹ * y * v = (v * (v * v)) * y * (v * (v * v))⁻¹ := by
  calc v⁻¹ * y * v
      = v⁻¹ * ((v * v) * (v * v) * y * ((v * v) * (v * v))⁻¹) * v := by rw [h4]
    _ = (v * (v * v)) * y * (v * (v * v))⁻¹ := by group

theorem automizerBig_of_heis {T : Type} [Group T] [Finite T] (h : HasHeis T) :
    AutomizerBig T := by
  obtain ⟨a, b, u, v, hab, ha3, hb3, hcard, hua, hub, hva, hvb⟩ := h
  let X₀ : Subgroup T := Subgroup.closure ({a, b} : Set T)
  have hXY : ∀ x ∈ X₀, ∀ y ∈ X₀, x * y = y * x := by
    have hcent : X₀ ≤ Subgroup.centralizer (X₀ : Set T) := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        change a ∈ Subgroup.centralizer (X₀ : Set T)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        refine Subgroup.closure_induction (p := fun y _ => y * a = a * y) ?_ ?_ ?_ ?_ hy
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact rfl
          · exact hab.symm
        · rw [one_mul, mul_one]
        · intro y z hy hz ihy ihz
          rw [mul_assoc, ihz, ← mul_assoc, ihy, mul_assoc]
        · intro y hy ihy
          have h1 : a * y⁻¹ = y⁻¹ * a := by
            calc a * y⁻¹ = y⁻¹ * (y * a) * y⁻¹ := by group
              _ = y⁻¹ * (a * y) * y⁻¹ := by rw [ihy]
              _ = y⁻¹ * a := by group
          exact h1.symm
      · rw [hx]
        change b ∈ Subgroup.centralizer (X₀ : Set T)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        refine Subgroup.closure_induction (p := fun y _ => y * b = b * y) ?_ ?_ ?_ ?_ hy
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact hab
          · exact rfl
        · rw [one_mul, mul_one]
        · intro y z hy hz ihy ihz
          rw [mul_assoc, ihz, ← mul_assoc, ihy, mul_assoc]
        · intro y hy ihy
          have h1 : b * y⁻¹ = y⁻¹ * b := by
            calc b * y⁻¹ = y⁻¹ * (y * b) * y⁻¹ := by group
              _ = y⁻¹ * (b * y) * y⁻¹ := by rw [ihy]
              _ = y⁻¹ * b := by group
          exact h1.symm
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hcent hx)) y hy).symm
  have hcommX0 : IsMulCommutative X₀ := by
    refine IsMulCommutative.of_comm ?_
    intro x y
    exact Subtype.ext (hXY x x.2 y y.2)
  have hpowX0 : ∀ x ∈ X₀, x ^ 3 = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => y ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ha3
      · exact hb3
    · exact one_pow 3
    · intro y z hy hz ihy ihz
      have hc : Commute y z := hXY y hy z hz
      rw [hc.mul_pow 3, ihy, ihz, mul_one]
    · intro y hy ihy
      rw [inv_pow, ihy, inv_one]
  have hEA : IsElemAbelian 3 X₀ := ⟨hcommX0, hpowX0⟩
  have hmem_a : a ∈ X₀ := Subgroup.subset_closure (by simp)
  have hmem_b : b ∈ X₀ := Subgroup.subset_closure (by simp)
  have hu_mem : u ∈ normalizer (X₀ : Set T) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · show X₀.map (MulAut.conj u) ≤ X₀
      rw [show X₀ = Subgroup.closure ({a, b} : Set T) from rfl, MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        change (MulAut.conj u) a ∈ Subgroup.closure ({a, b} : Set T)
        rw [MulAut.conj_apply, hua]
        exact Subgroup.inv_mem _ hmem_b
      · rw [hy]
        change (MulAut.conj u) b ∈ Subgroup.closure ({a, b} : Set T)
        rw [MulAut.conj_apply, hub]
        exact hmem_a
    · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]
  have hv_mem : v ∈ normalizer (X₀ : Set T) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · show X₀.map (MulAut.conj v) ≤ X₀
      rw [show X₀ = Subgroup.closure ({a, b} : Set T) from rfl, MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        change (MulAut.conj v) a ∈ Subgroup.closure ({a, b} : Set T)
        rw [MulAut.conj_apply, hva]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hmem_a 2) (Subgroup.pow_mem _ hmem_b 2)
      · rw [hy]
        change (MulAut.conj v) b ∈ Subgroup.closure ({a, b} : Set T)
        rw [MulAut.conj_apply, hvb]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hmem_a 2) hmem_b
    · rw [Subgroup.card_map_of_injective (MulAut.conj v).injective]
  have hab' : Commute a b := hab
  have hu2a : u * u * a * (u * u)⁻¹ = a⁻¹ := by
    calc u * u * a * (u * u)⁻¹ = u * (u * a * u⁻¹) * u⁻¹ := by group
      _ = u * b⁻¹ * u⁻¹ := by rw [hua]
      _ = (u * b * u⁻¹)⁻¹ := by group
      _ = a⁻¹ := by rw [hub]
  have hu2b : u * u * b * (u * u)⁻¹ = b⁻¹ := by
    calc u * u * b * (u * u)⁻¹ = u * (u * b * u⁻¹) * u⁻¹ := by group
      _ = u * a * u⁻¹ := by rw [hub]
      _ = b⁻¹ := by rw [hua]
  have hv2a : v * v * a * (v * v)⁻¹ = a⁻¹ := by
    calc v * v * a * (v * v)⁻¹ = v * (v * a * v⁻¹) * v⁻¹ := by group
      _ = v * (a ^ 2 * b ^ 2) * v⁻¹ := by rw [hva]
      _ = (v * a * v⁻¹) ^ 2 * (v * b * v⁻¹) ^ 2 := by
        rw [← MulAut.conj_apply, map_mul, map_pow, map_pow, MulAut.conj_apply,
          MulAut.conj_apply]
      _ = (a ^ 2 * b ^ 2) ^ 2 * (a ^ 2 * b) ^ 2 := by rw [hva, hvb]
      _ = a⁻¹ := k330c_heis_v2a hab' ha3 hb3
  have hv2b : v * v * b * (v * v)⁻¹ = b⁻¹ := by
    calc v * v * b * (v * v)⁻¹ = v * (v * b * v⁻¹) * v⁻¹ := by group
      _ = v * (a ^ 2 * b) * v⁻¹ := by rw [hvb]
      _ = (v * a * v⁻¹) ^ 2 * (v * b * v⁻¹) := by
        rw [← MulAut.conj_apply, map_mul, map_pow, MulAut.conj_apply, MulAut.conj_apply]
      _ = (a ^ 2 * b ^ 2) ^ 2 * (a ^ 2 * b) := by rw [hva, hvb]
      _ = b⁻¹ := k330c_heis_v2b hab' ha3 hb3
  have hv2_map : ∀ x ∈ X₀, v * v * x * (v * v)⁻¹ = x⁻¹ :=
    k330c_conj_sq_eq_inv_closure (fun x hx y hy => hXY x hx y hy) hv2a hv2b
  have hv4_map : ∀ x ∈ X₀, (v * v) * (v * v) * x * ((v * v) * (v * v))⁻¹ = x :=
    k330c_sq_sq_eq_self hv2_map
  have hmem_a2b : a ^ 2 * b ∈ X₀ :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hmem_a 2) hmem_b
  have hmem_a2b2 : a ^ 2 * b ^ 2 ∈ X₀ :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hmem_a 2) (Subgroup.pow_mem _ hmem_b 2)
  have hvinv_b : v⁻¹ * b * v = (a ^ 2 * b)⁻¹ := by
    calc v⁻¹ * b * v = (v * (v * v)) * b * (v * (v * v))⁻¹ :=
          k330c_inv_mul_eq_cube (hv4_map b hmem_b)
      _ = v * v * (v * b * v⁻¹) * (v * v)⁻¹ := by group
      _ = v * v * (a ^ 2 * b) * (v * v)⁻¹ := by rw [hvb]
      _ = (a ^ 2 * b)⁻¹ := hv2_map (a ^ 2 * b) hmem_a2b
  have hvinv_a : v⁻¹ * a * v = (a ^ 2 * b ^ 2)⁻¹ := by
    calc v⁻¹ * a * v = (v * (v * v)) * a * (v * (v * v))⁻¹ :=
          k330c_inv_mul_eq_cube (hv4_map a hmem_a)
      _ = v * v * (v * a * v⁻¹) * (v * v)⁻¹ := by group
      _ = v * v * (a ^ 2 * b ^ 2) * (v * v)⁻¹ := by rw [hva]
      _ = (a ^ 2 * b ^ 2)⁻¹ := hv2_map (a ^ 2 * b ^ 2) hmem_a2b2
  have hwa : (v⁻¹ * u) * a * (v⁻¹ * u)⁻¹ = a ^ 2 * b := by
    calc (v⁻¹ * u) * a * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * a * u⁻¹) * v := by group
      _ = v⁻¹ * b⁻¹ * v := by rw [hua]
      _ = (v⁻¹ * b * v)⁻¹ := by group
      _ = ((a ^ 2 * b)⁻¹)⁻¹ := by rw [hvinv_b]
      _ = a ^ 2 * b := by group
  have hwb : (v⁻¹ * u) * b * (v⁻¹ * u)⁻¹ = a * b := by
    calc (v⁻¹ * u) * b * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * b * u⁻¹) * v := by group
      _ = v⁻¹ * a * v := by rw [hub]
      _ = (a ^ 2 * b ^ 2)⁻¹ := hvinv_a
      _ = a * b := k330c_heis_inv_a2b2 hab' ha3 hb3
  have hw2a : (v⁻¹ * u) * (v⁻¹ * u) * a * ((v⁻¹ * u) * (v⁻¹ * u))⁻¹ = a⁻¹ := by
    calc (v⁻¹ * u) * (v⁻¹ * u) * a * ((v⁻¹ * u) * (v⁻¹ * u))⁻¹
        = (v⁻¹ * u) * ((v⁻¹ * u) * a * (v⁻¹ * u)⁻¹) * (v⁻¹ * u)⁻¹ := by group
      _ = (v⁻¹ * u) * (a ^ 2 * b) * (v⁻¹ * u)⁻¹ := by rw [hwa]
      _ = ((v⁻¹ * u) * a * (v⁻¹ * u)⁻¹) ^ 2 * ((v⁻¹ * u) * b * (v⁻¹ * u)⁻¹) := by
        rw [← MulAut.conj_apply, map_mul, map_pow, MulAut.conj_apply, MulAut.conj_apply]
      _ = (a ^ 2 * b) ^ 2 * (a * b) := by rw [hwa, hwb]
      _ = a⁻¹ := k330c_heis_w2a hab' ha3 hb3
  have hw2b : (v⁻¹ * u) * (v⁻¹ * u) * b * ((v⁻¹ * u) * (v⁻¹ * u))⁻¹ = b⁻¹ := by
    calc (v⁻¹ * u) * (v⁻¹ * u) * b * ((v⁻¹ * u) * (v⁻¹ * u))⁻¹
        = (v⁻¹ * u) * ((v⁻¹ * u) * b * (v⁻¹ * u)⁻¹) * (v⁻¹ * u)⁻¹ := by group
      _ = (v⁻¹ * u) * (a * b) * (v⁻¹ * u)⁻¹ := by rw [hwb]
      _ = ((v⁻¹ * u) * a * (v⁻¹ * u)⁻¹) * ((v⁻¹ * u) * b * (v⁻¹ * u)⁻¹) := by
        rw [← MulAut.conj_apply, map_mul, MulAut.conj_apply, MulAut.conj_apply]
      _ = (a ^ 2 * b) * (a * b) := by rw [hwa, hwb]
      _ = b⁻¹ := k330c_heis_w2b hab' ha3 hb3
  have hu2_map : ∀ x ∈ X₀, u * u * x * (u * u)⁻¹ = x⁻¹ :=
    k330c_conj_sq_eq_inv_closure (fun x hx y hy => hXY x hx y hy) hu2a hu2b
  have hw2_map : ∀ x ∈ X₀, (v⁻¹ * u) * (v⁻¹ * u) * x * ((v⁻¹ * u) * (v⁻¹ * u))⁻¹ = x⁻¹ :=
    k330c_conj_sq_eq_inv_closure (fun x hx y hy => hXY x hx y hy) hw2a hw2b
  have hmu : MovesLines X₀ u := k330c_movesLines_of_sq_inv hcard hu2_map
  have hmv : MovesLines X₀ v := k330c_movesLines_of_sq_inv hcard hv2_map
  have hmw : MovesLines X₀ (v⁻¹ * u) := k330c_movesLines_of_sq_inv hcard hw2_map
  intro X hSX hEX h9X Z₁ Z₂ hZ₁ hZ₂ hc₁ hc₂ hne
  have hS0 : IsSylowOf 3 X₀ ⊤ := by
    apply CFSG.ABGLocalTools.isSylowOf_of_card le_top
    rw [hcard, ← hSX.card_eq, h9X]
  exact automizerBig_of_two X₀ hS0 hEA hcard u v hu_mem hv_mem hmu hmv hmw
    X hSX hEX h9X Z₁ Z₂ hZ₁ hZ₂ hc₁ hc₂ hne

private lemma k330c_map_map_conj_comp {J T : Type} [Group J] [Group T] (f : J →* T) (m : J) :
    (MulAut.conj (f m)).toMonoidHom.comp f = f.comp (MulAut.conj m).toMonoidHom := by
  ext x
  simp [MulAut.conj_apply]

private lemma k330c_map_conj_map {J T : Type} [Group J] [Group T] (f : J →* T) (m : J)
    (A : Subgroup J) :
    (A.map (MulAut.conj m).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f m)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, k330c_map_map_conj_comp]

private lemma k330c_map_conj_map_eq {J T : Type} [Group J] [Group T] (f : J →* T) (m : J)
    {A B : Subgroup J} (h : A.map (MulAut.conj m).toMonoidHom = B) :
    (A.map f).map (MulAut.conj (f m)).toMonoidHom = B.map f := by
  rw [← k330c_map_conj_map f m A, h]

private lemma k330c_isSylowOf_map {J T : Type} [Group J] [Finite J] [Group T] [Finite T]
    (e : J ≃* T) {X : Subgroup J} (h : IsSylowOf 3 X ⊤) :
    IsSylowOf 3 (X.map (e : J →* T)) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨_, hP, hdvd⟩ := h
  refine ⟨le_top, hP.map (e : J →* T), ?_⟩
  rw [show (⊤ : Subgroup T) = (⊤ : Subgroup J).map (e : J →* T) by
      rw [Subgroup.map_top_of_surjective _ e.surjective],
    Subgroup.relIndex_map_map_of_injective X ⊤ e.injective]
  exact hdvd

private lemma k330c_isElemAbelian_map {J T : Type} [Group J] [Group T] (e : J ≃* T)
    {X : Subgroup J} (h : IsElemAbelian 3 X) :
    IsElemAbelian 3 (X.map (e : J →* T)) := by
  obtain ⟨hcomm, hpow⟩ := h
  refine ⟨?_, ?_⟩
  · exact (Subgroup.equivMapOfInjective X (e : J →* T) e.injective).surjective.isMulCommutative
      hcomm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hpow y hy, map_one]

theorem automizerBig_of_mulEquiv {J T : Type} [Group J] [Finite J] [Group T] [Finite T]
    (e : J ≃* T) (h : AutomizerBig T) : AutomizerBig J := by
  intro X hS hE h9 Z₁ Z₂ hZ₁ hZ₂ hc₁ hc₂ hne
  have hS' : IsSylowOf 3 (X.map (e : J →* T)) ⊤ := k330c_isSylowOf_map e hS
  have hE' : IsElemAbelian 3 (X.map (e : J →* T)) := k330c_isElemAbelian_map e hE
  have h9' : Nat.card (X.map (e : J →* T)) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, h9]
  have hZ₁' : Z₁.map (e : J →* T) ≤ X.map (e : J →* T) := Subgroup.map_mono hZ₁
  have hZ₂' : Z₂.map (e : J →* T) ≤ X.map (e : J →* T) := Subgroup.map_mono hZ₂
  have hc₁' : Nat.card (Z₁.map (e : J →* T)) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hc₁]
  have hc₂' : Nat.card (Z₂.map (e : J →* T)) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hc₂]
  have hne' : Z₁.map (e : J →* T) ≠ Z₂.map (e : J →* T) :=
    fun hh => hne (Subgroup.map_injective e.injective hh)
  obtain ⟨n', hn', hnp⟩ := h (X.map (e : J →* T)) hS' hE' h9' (Z₁.map (e : J →* T))
    (Z₂.map (e : J →* T)) hZ₁' hZ₂' hc₁' hc₂' hne'
  have hn'map : n' ∈ (normalizer (X : Set J)).map (e : J →* T) := by
    change n' ∈ (normalizer (X : Set J)).map e.toMonoidHom
    rw [Subgroup.map_equiv_normalizer_eq X e]
    exact hn'
  obtain ⟨n, hn, hfn⟩ := Subgroup.mem_map.mp hn'map
  refine ⟨n, hn, ?_⟩
  intro hP
  apply hnp
  rcases hP with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    exact ⟨by simpa [hfn] using k330c_map_conj_map_eq (e : J →* T) n ha,
      by simpa [hfn] using k330c_map_conj_map_eq (e : J →* T) n hb⟩
  · right
    exact ⟨by simpa [hfn] using k330c_map_conj_map_eq (e : J →* T) n ha,
      by simpa [hfn] using k330c_map_conj_map_eq (e : J →* T) n hb⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
