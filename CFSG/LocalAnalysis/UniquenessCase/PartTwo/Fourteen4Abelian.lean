module

public import CFSG.GH74.Uniqueness.Section14Tools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem map_conj_inf_centralizer {V : Subgroup G} {g : G}
    (hg : g ∈ normalizer (V : Set G)) (y : G) :
    (V ⊓ centralizer ({y} : Set G)).map (MulAut.conj g : G →* G) =
      V ⊓ centralizer ({g * y * g⁻¹} : Set G) := by
  have hV : V.map (MulAut.conj g : G →* G) = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  have hC : (centralizer ({y} : Set G)).map (MulAut.conj g : G →* G) =
      centralizer ({g * y * g⁻¹} : Set G) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h : w * y = y * w := hw
      show g * w * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * w * g⁻¹)
      calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
        _ = g * (y * w) * g⁻¹ := by rw [h]
        _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group
    · intro h
      refine ⟨g⁻¹ * z * g, ?_, ?_⟩
      · show g⁻¹ * z * g * y = y * (g⁻¹ * z * g)
        calc g⁻¹ * z * g * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [h]
          _ = y * (g⁻¹ * z * g) := by group
      · show g * (g⁻¹ * z * g) * g⁻¹ = z
        group
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hV, hC]

private theorem card_inf_centralizer_eq {V : Subgroup G} {g y z : G}
    (hg : g ∈ normalizer (V : Set G)) (hz : g * y * g⁻¹ = z) :
    Nat.card ↥(V ⊓ centralizer ({y} : Set G)) = Nat.card ↥(V ⊓ centralizer ({z} : Set G)) := by
  have := map_conj_inf_centralizer hg y
  rw [hz] at this
  rw [← this]
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

private theorem centralizer_inv_singleton (y : G) :
    centralizer ({y⁻¹} : Set G) = centralizer ({y} : Set G) := by
  ext z
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact (Commute.inv_right_iff (a := z) (b := y))

private theorem normalizes_inf_centralizer {V : Subgroup G} {g y : G}
    (hg : g ∈ normalizer (V : Set G)) (hy : g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹) :
    g ∈ normalizer ((V ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, map_conj_inf_centralizer hg]
  rcases hy with h | h
  · rw [h]
  · rw [h, centralizer_inv_singleton]

private theorem eq_bot_of_commute {V X : Subgroup G} {x : G} (hX : X = zpowers x)
    (hC : V ⊓ centralizer (X : Set G) = ⊥) {v : G} (hv : v ∈ V) (hvx : v * x = x * v) :
    v = 1 := by
  have hmem : v ∈ V ⊓ centralizer (X : Set G) := by
    refine ⟨hv, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    subst hX
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((show Commute v x from hvx).zpow_right k).symm.eq
  rw [hC] at hmem
  exact Subgroup.mem_bot.1 hmem

private theorem mem_zpowers_sq {y : G} (hy : y ^ 3 = 1) : y ∈ zpowers (y ^ 2) := by
  refine Subgroup.mem_zpowers_iff.2 ⟨2, ?_⟩
  have : (y ^ 2) ^ (2 : ℤ) = y ^ 3 * y := by group
  rw [this, hy, one_mul]

private theorem zpow_eq_of_pow_three {y : G} (hy : y ^ 3 = 1) (i : ℤ) : y ^ i = y ^ (i % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv i 3]
  have h3 : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy
  rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]

private theorem exists_mem_zpowers {x₁ x₂ : G} (h12 : x₁ * x₂ = x₂ * x₁)
    (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) {x : G} (hx : x ∈ zpowers x₁ ⊔ zpowers x₂)
    (hx1 : x ≠ 1) :
    x₂ ∈ zpowers x ∨ x₁ ∈ zpowers x ∨ x₁ * x₂ ∈ zpowers x ∨ x₁ * x₂⁻¹ ∈ zpowers x := by
  have hc : Commute x₁ x₂ := h12
  have hnorm : zpowers x₂ ≤ normalizer (zpowers x₁ : Set G) := by
    refine (Subgroup.zpowers_le.2 ?_).trans (Subgroup.centralizer_le_normalizer _)
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hc.zpow_left k).eq
  have hxmul : x ∈ (zpowers x₁ : Set G) * (zpowers x₂ : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hxmul
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [zpow_eq_of_pow_three h1 i, zpow_eq_of_pow_three h2 j] at hx1 ⊢
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hx2inv : x₂ ^ 2 = x₂⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact h2
  have hy3 : (x₁ * x₂) ^ 3 = 1 := by rw [hc.mul_pow, h1, h2, one_mul]
  have hy3' : (x₁ * x₂⁻¹) ^ 3 = 1 := by
    rw [hc.inv_right.mul_pow, h1, inv_pow, h2, inv_one, one_mul]
  have hsq : (x₁ * x₂) ^ 2 = x₁ ^ 2 * x₂ ^ 2 := hc.mul_pow 2
  have hsq' : (x₁ * x₂⁻¹) ^ 2 = x₁ ^ 2 * x₂ := by
    rw [hc.inv_right.mul_pow, inv_pow, hx2inv, inv_inv]
  have z2 : ∀ y : G, y ^ (2 : ℤ) = y ^ 2 := fun y => by rw [zpow_two, sq]
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;> rw [hi, hj] at hx1 ⊢ <;>
    simp only [zpow_zero, zpow_one, one_mul, mul_one, z2] at hx1 ⊢
  · exact absurd rfl hx1
  · exact Or.inl (Subgroup.mem_zpowers _)
  · exact Or.inl (mem_zpowers_sq h2)
  · exact Or.inr (Or.inl (Subgroup.mem_zpowers _))
  · exact Or.inr (Or.inr (Or.inl (Subgroup.mem_zpowers _)))
  · rw [hx2inv]; exact Or.inr (Or.inr (Or.inr (Subgroup.mem_zpowers _)))
  · exact Or.inr (Or.inl (mem_zpowers_sq h1))
  · rw [← hsq']; exact Or.inr (Or.inr (Or.inr (mem_zpowers_sq hy3')))
  · rw [← hsq]; exact Or.inr (Or.inr (Or.inl (mem_zpowers_sq hy3)))

private theorem centralizer_singleton_le_of_mem_zpowers {x y : G} (hy : y ∈ zpowers x) :
    centralizer ({x} : Set G) ≤ centralizer ({y} : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_singleton_iff] at hv ⊢
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((show Commute v x from hv).zpow_right k).eq

private theorem card_eq_prime_of_sq {q : ℕ} (hq : q.Prime) {V A B : Subgroup G} (hV : IsPGroup q V)
    (hV1 : V ≠ ⊥) (hVc : Nat.card V ≤ q ^ 3) (hAle : A ≤ V)
    (hcard : Nat.card V = Nat.card A * Nat.card B) (hcardAB : Nat.card A = Nat.card B) :
    Nat.card A = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := q)).1 hV
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := q)).1 (hV.to_le hAle)
  have hk2 : k = m + m := by
    apply Nat.pow_right_injective hq.two_le
    show q ^ k = q ^ (m + m)
    rw [← hk, hcard, ← hcardAB, hm, pow_add]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hV1 (Subgroup.card_eq_one.1 (by simpa using hk))
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hq.one_lt).1 (hk ▸ hVc)
  have : m = 1 := by omega
  rw [hm, this, pow_one]

theorem eq_sup_diagonals {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) {V X₁ X₂ : Subgroup G} {x₁ x₂ : G}
    (hV : IsPGroup q V) (hX₁ : X₁ = zpowers x₁) (hX₂ : X₂ = zpowers x₂)
    (hc₁ : Nat.card X₁ = 3) (hc₂ : Nat.card X₂ = 3)
    (hX : IsElemAbelian 3 (X₁ ⊔ X₂)) (hX12 : Nat.card (X₁ ⊔ X₂ : Subgroup G) = 9)
    (hXV : X₁ ⊔ X₂ ≤ normalizer (V : Set G))
    (hC₁ : V ⊓ centralizer (X₁ : Set G) = ⊥) (hC₂ : V ⊓ centralizer (X₂ : Set G) = ⊥) :
    V = (V ⊓ centralizer ({x₁ * x₂} : Set G)) ⊔ (V ⊓ centralizer ({x₁ * x₂⁻¹} : Set G)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcompl : ¬ 3 ∣ Nat.card V := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hV
    intro h
    rw [hn] at h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three (X₁ ⊔ X₂) V (fun m => Subtype.ext (by simpa using hX.2 m m.2))
    (by rw [hX12]; norm_num) hcompl hXV
  have hx₁X : x₁ ∈ X₁ ⊔ X₂ := Subgroup.mem_sup_left (hX₁ ▸ Subgroup.mem_zpowers x₁)
  have hx₂X : x₂ ∈ X₁ ⊔ X₂ := Subgroup.mem_sup_right (hX₂ ▸ Subgroup.mem_zpowers x₂)
  have hcomm : x₁ * x₂ = x₂ * x₁ :=
    congrArg Subtype.val (hX.1.is_comm.comm (⟨x₁, hx₁X⟩ : ↥(X₁ ⊔ X₂)) ⟨x₂, hx₂X⟩)
  have hx₁3 : x₁ ^ 3 = 1 := hX.2 x₁ hx₁X
  have hx₂3 : x₂ ^ 3 = 1 := hX.2 x₂ hx₂X
  refine le_antisymm (hgen.le.trans (iSup_le fun m => iSup_le fun hm => ?_))
    (sup_le inf_le_left inf_le_left)
  have hm1 : (m : G) ≠ 1 := fun h => hm (Subtype.ext h)
  have hmX : (m : G) ∈ zpowers x₁ ⊔ zpowers x₂ := by rw [← hX₁, ← hX₂]; exact m.2
  rcases exists_mem_zpowers hcomm hx₁3 hx₂3 hmX hm1 with h | h | h | h
  · intro v hv
    have hv' := centralizer_singleton_le_of_mem_zpowers h hv.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hv'
    rw [eq_bot_of_commute hX₂ hC₂ hv.1 hv']
    exact Subgroup.one_mem _
  · intro v hv
    have hv' := centralizer_singleton_le_of_mem_zpowers h hv.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hv'
    rw [eq_bot_of_commute hX₁ hC₁ hv.1 hv']
    exact Subgroup.one_mem _
  · exact (inf_le_inf_left V (centralizer_singleton_le_of_mem_zpowers h)).trans le_sup_left
  · exact (inf_le_inf_left V (centralizer_singleton_le_of_mem_zpowers h)).trans le_sup_right

theorem centralizes_of_inverted {A : Subgroup G} (hA : IsCyclic A) {x n : G} (hx : x ^ 3 = 1)
    (hxA : x ∈ normalizer (A : Set G)) (hnA : n ∈ normalizer (A : Set G))
    (hn : n * x * n⁻¹ = x⁻¹) : ∀ a ∈ A, x * a = a * x := by
  intro a ha
  let φ := A.normalizerMonoidHom
  let u : normalizer (A : Set G) := ⟨x, hxA⟩
  let v : normalizer (A : Set G) := ⟨n, hnA⟩
  have hcomm : ∀ s t : MulAut A, s * t = t * s := fun s t =>
    (IsCyclic.mulAutMulEquiv A).injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have h1 : v * u * v⁻¹ = u⁻¹ := Subtype.ext (by simpa using hn)
  have h2 : φ u * φ u = 1 := by
    have h := congrArg φ h1
    rw [map_mul, map_mul, map_inv, map_inv, hcomm (φ v) (φ u), mul_assoc, mul_inv_cancel,
      mul_one] at h
    nth_rewrite 1 [h]
    exact inv_mul_cancel _
  have h3 : φ u ^ 3 = 1 := by
    rw [← map_pow]
    have : u ^ 3 = 1 := Subtype.ext (by simpa using hx)
    rw [this, map_one]
  have h4 : φ u = 1 := by
    calc φ u = φ u ^ 3 * (φ u * φ u)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  have h5 : ((φ u ⟨a, ha⟩ : A) : G) = a := by rw [h4]; rfl
  have h6 : x * a * x⁻¹ = a := h5
  exact mul_inv_eq_iff_eq_mul.1 h6

theorem abelian_338 {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) {V X₁ X₂ : Subgroup G}
    (hV : IsElemAbelian q V) (hV1 : V ≠ ⊥) (hVc : Nat.card V ≤ q ^ 3)
    (hX₁ : Nat.card X₁ = 3) (hX₂ : Nat.card X₂ = 3)
    (hX : IsElemAbelian 3 (X₁ ⊔ X₂)) (hX12 : Nat.card (X₁ ⊔ X₂ : Subgroup G) = 9)
    (hXV : X₁ ⊔ X₂ ≤ normalizer (V : Set G))
    (hk : ∀ s₁ s₂ : Bool, ∃ n ∈ normalizer (V : Set G),
      (∀ x ∈ X₁, n * x * n⁻¹ = if s₁ then x⁻¹ else x) ∧
      (∀ x ∈ X₂, n * x * n⁻¹ = if s₂ then x⁻¹ else x)) :
    V ⊓ centralizer (X₁ : Set G) ≠ ⊥ ∨ V ⊓ centralizer (X₂ : Set G) ≠ ⊥ := by
  by_contra hcon
  obtain ⟨hC₁, hC₂⟩ := not_or.1 hcon
  replace hC₁ := not_not.1 hC₁
  replace hC₂ := not_not.1 hC₂
  haveI : Fact q.Prime := ⟨hq⟩
  have hcyc : ∀ X : Subgroup G, Nat.card X = 3 → ∃ x, X = zpowers x := by
    intro X hX3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top X).1 (isCyclic_of_prime_card hX3)
    exact ⟨x, hx.symm⟩
  obtain ⟨x₁, hx₁⟩ := hcyc X₁ hX₁
  obtain ⟨x₂, hx₂⟩ := hcyc X₂ hX₂
  have hx₁X : x₁ ∈ X₁ ⊔ X₂ := Subgroup.mem_sup_left (hx₁ ▸ Subgroup.mem_zpowers x₁)
  have hx₂X : x₂ ∈ X₁ ⊔ X₂ := Subgroup.mem_sup_right (hx₂ ▸ Subgroup.mem_zpowers x₂)
  have hcomm : x₁ * x₂ = x₂ * x₁ :=
    congrArg Subtype.val (hX.1.is_comm.comm (⟨x₁, hx₁X⟩ : ↥(X₁ ⊔ X₂)) ⟨x₂, hx₂X⟩)
  have hc : Commute x₁ x₂ := hcomm
  have hx₁3 : x₁ ^ 3 = 1 := hX.2 x₁ hx₁X
  have hx₂3 : x₂ ^ 3 = 1 := hX.2 x₂ hx₂X
  have hVq : IsPGroup q V := fun g => ⟨1, Subtype.ext (by simpa using hV.2 g g.2)⟩
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  have hC₁' : ∀ v ∈ V, v * x₁ = x₁ * v → v = 1 := fun v hv h => eq_bot_of_commute hx₁ hC₁ hv h
  set A : Subgroup G := V ⊓ centralizer ({x₁ * x₂} : Set G) with hA
  set B : Subgroup G := V ⊓ centralizer ({x₁ * x₂⁻¹} : Set G) with hB
  have hVAB : V = A ⊔ B :=
    eq_sup_diagonals hq hq3 hVq hx₁ hx₂ hX₁ hX₂ hX hX12 hXV hC₁ hC₂
  have hAle : A ≤ V := inf_le_left
  have hBle : B ≤ V := inf_le_left
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff_forall]
    intro v hv
    have hvA : Commute v (x₁ * x₂) := Subgroup.mem_centralizer_singleton_iff.1 hv.1.2
    have hvB : Commute v (x₁ * x₂⁻¹) := Subgroup.mem_centralizer_singleton_iff.1 hv.2.2
    have h2 : (x₁ * x₂) * (x₁ * x₂⁻¹) = x₁ ^ 2 := by
      calc (x₁ * x₂) * (x₁ * x₂⁻¹) = x₁ * (x₂ * x₁) * x₂⁻¹ := by group
        _ = x₁ * (x₁ * x₂) * x₂⁻¹ := by rw [hcomm]
        _ = x₁ * x₁ := by group
        _ = x₁ ^ 2 := (sq x₁).symm
    have h4 : x₁ = (x₁ ^ 2) ^ 2 := by
      calc x₁ = x₁ * x₁ ^ 3 := by rw [hx₁3, mul_one]
        _ = (x₁ ^ 2) ^ 2 := by group
    have hv1 : Commute v x₁ := by
      have h := (hvA.mul_right hvB).pow_right 2
      rw [h2, ← h4] at h
      exact h
    exact hC₁' v hv.1.1 hv1.eq
  have hBnA : B ≤ normalizer (A : Set G) := by
    have hVV : V ≤ centralizer (V : Set G) := Subgroup.le_centralizer_iff_isMulCommutative.2 hV.1
    exact hBle.trans (hVV.trans ((Subgroup.centralizer_le hAle).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hcard : Nat.card V = Nat.card A * Nat.card B := by
    have h := CFSG.GH74.Uniqueness.card_sup_mul_card_inf' hBnA
    rw [sup_comm, ← hVAB, hAB, Subgroup.card_bot, mul_one] at h
    exact h
  obtain ⟨n, hnV, hn₁, hn₂⟩ := hk true false
  have hn1 : n * x₁ * n⁻¹ = x₁⁻¹ := by simpa using hn₁ x₁ (hx₁ ▸ Subgroup.mem_zpowers x₁)
  have hn2 : n * x₂ * n⁻¹ = x₂ := by simpa using hn₂ x₂ (hx₂ ▸ Subgroup.mem_zpowers x₂)
  have hcardAB : Nat.card A = Nat.card B := by
    have hz : n * (x₁ * x₂) * n⁻¹ = (x₁ * x₂⁻¹)⁻¹ := by
      calc n * (x₁ * x₂) * n⁻¹ = (n * x₁ * n⁻¹) * (n * x₂ * n⁻¹) := by group
        _ = x₁⁻¹ * x₂ := by rw [hn1, hn2]
        _ = (x₁ * x₂⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv]; exact hc.inv_left.eq
    have h := card_inf_centralizer_eq hnV hz
    rw [centralizer_inv_singleton] at h
    exact h
  have hAq : Nat.card A = q := card_eq_prime_of_sq hq hVq hV1 hVc hAle hcard hcardAB
  have hAcyc : IsCyclic A := isCyclic_of_prime_card hAq
  obtain ⟨n', hn'V, hn'₁, hn'₂⟩ := hk true true
  have hn'1 : n' * x₁ * n'⁻¹ = x₁⁻¹ := by simpa using hn'₁ x₁ (hx₁ ▸ Subgroup.mem_zpowers x₁)
  have hn'2 : n' * x₂ * n'⁻¹ = x₂⁻¹ := by simpa using hn'₂ x₂ (hx₂ ▸ Subgroup.mem_zpowers x₂)
  have hx₁A : x₁ ∈ normalizer (A : Set G) := by
    refine normalizes_inf_centralizer (hXV hx₁X) (Or.inl ?_)
    calc x₁ * (x₁ * x₂) * x₁⁻¹ = x₁ * (x₂ * x₁) * x₁⁻¹ := by rw [hcomm]
      _ = x₁ * x₂ := by group
  have hn'A : n' ∈ normalizer (A : Set G) := by
    refine normalizes_inf_centralizer hn'V (Or.inr ?_)
    calc n' * (x₁ * x₂) * n'⁻¹ = (n' * x₁ * n'⁻¹) * (n' * x₂ * n'⁻¹) := by group
      _ = x₁⁻¹ * x₂⁻¹ := by rw [hn'1, hn'2]
      _ = (x₁ * x₂)⁻¹ := by rw [mul_inv_rev]; exact hc.inv_inv.eq
  have hcent := centralizes_of_inverted hAcyc hx₁3 hx₁A hn'A hn'1
  have hA1 : A = ⊥ := by
    rw [eq_bot_iff_forall]
    intro a ha
    exact hC₁' a (hAle ha) (hcent a ha).symm
  have : Nat.card A = 1 := Subgroup.card_eq_one.2 hA1
  exact hq.one_lt.ne' (hAq ▸ this)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
