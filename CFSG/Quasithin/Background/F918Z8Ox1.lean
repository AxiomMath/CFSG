module

public import CFSG.Quasithin.EmptyFaithful.S146xB2Cmp

public section

namespace CFSG.Quasithin

theorem opx_mem_of_odd_pow_eq_one {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : H.index ≤ 2) {a : G} {n : ℕ} (hn : Odd n) (han : a ^ n = 1) : a ∈ H := by
  have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1]
    exact Subgroup.mem_top a
  · have := Subgroup.normal_of_index_eq_two h2
    have hsq : a ^ 2 ∈ H := by simpa [h2] using H.pow_index_mem a
    obtain ⟨m, rfl⟩ := hn
    have e : a = (a ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, han, one_mul]
    have h := H.pow_mem hsq (m + 1)
    rwa [← e] at h

theorem opx_inner_of_odd_order {N : Type*} [Group N] [Finite N]
    (hZ : ∀ x : N, (∀ y : N, x * y = y * x) → x = 1)
    (hAut : Nat.card (MulAut N) ≤ 2 * Nat.card N) {α : MulAut N} {n : ℕ} (hn : Odd n)
    (hα : α ^ n = 1) : ∃ y : N, ∀ x : N, α x = y * x * y⁻¹ := by
  have hinj : Function.Injective (MulAut.conj : N →* MulAut N) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    refine hZ y fun w => ?_
    have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hy) w
    simpa [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] using h
  have hrange : Nat.card (MulAut.conj : N →* MulAut N).range = Nat.card N :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : (MulAut.conj : N →* MulAut N).range.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (MulAut.conj : N →* MulAut N).range
    rw [hrange] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [h1, mul_comm]
    exact hAut
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (opx_mem_of_odd_pow_eq_one _ hidx hn hα)
  exact ⟨y, fun x => by rw [← hy]; rfl⟩

section Rank

variable {S : Type} [Group S] [Finite S]

theorem opx_three_le_pRank {p : ℕ} (hp : p.Prime) {K₁ K₂ K₃ : Subgroup S}
    (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (h13 : ∀ a ∈ K₁, ∀ b ∈ K₃, a * b = b * a)
    (h23 : ∀ a ∈ K₂, ∀ b ∈ K₃, a * b = b * a)
    (hZ₁ : ∀ x ∈ K₁, (∀ y ∈ K₁, x * y = y * x) → x = 1)
    (hZ₃ : ∀ x ∈ K₃, (∀ y ∈ K₃, x * y = y * x) → x = 1)
    {x₁ x₂ x₃ : S} (hx₁ : x₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (hx₃ : x₃ ∈ K₃)
    (ho₁ : orderOf x₁ = p) (ho₂ : orderOf x₂ = p) (ho₃ : orderOf x₃ = p) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
  classical
  have hcard : ∀ {x : S}, orderOf x = p → Nat.card (Subgroup.zpowers x) = p := fun {x} ho => by
    rw [Nat.card_zpowers, ho]
  have hel : ∀ {x : S}, orderOf x = p → CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) := by
    intro x ho
    refine ⟨inferInstance, fun y hy => ?_⟩
    have hxp : x ^ p = 1 := by rw [← ho]; exact pow_orderOf_eq_one x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  set P₁ := Subgroup.zpowers x₁ with hP₁
  set P₂ := Subgroup.zpowers x₂ with hP₂
  set P₃ := Subgroup.zpowers x₃ with hP₃
  have hP₁K : P₁ ≤ K₁ := Subgroup.zpowers_le.mpr hx₁
  have hP₂K : P₂ ≤ K₂ := Subgroup.zpowers_le.mpr hx₂
  have hP₃K : P₃ ≤ K₃ := Subgroup.zpowers_le.mpr hx₃
  have hc12 : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => h12 a (hP₁K ha) b (hP₂K hb)
  have hP₁₂ : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    rw [Subgroup.mem_bot]
    exact hZ₁ z (hP₁K hz1) (fun y hy => (h12 y hy z (hP₂K hz2)).symm)
  have hE₂ : CFSG.Open.IsElemAbelian p (P₁ ⊔ P₂) :=
    isElemAbelian_sup_of_commute (hel ho₁) (hel ho₂)
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (hc12 a ha b hb).symm)
  have hE₂card : Nat.card (P₁ ⊔ P₂ : Subgroup S) = p ^ 2 := by
    obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P₁ P₂ hc12
    rw [hP₁₂, hcard ho₁, hcard ho₂] at hc
    simpa [sq] using hc
  have hE₂C : P₁ ⊔ P₂ ≤ Subgroup.centralizer (K₃ : Set S) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb => (h13 a (hP₁K ha) b hb).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb => (h23 a (hP₂K ha) b hb).symm
  have hE₂P₃ : (P₁ ⊔ P₂) ⊓ P₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz3⟩
    rw [Subgroup.mem_bot]
    refine hZ₃ z (hP₃K hz3) fun y hy => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hE₂C hz1)) y hy).symm
  have h := le_pRank_of_commute_of_inf_eq_bot' hp (P := P₁ ⊔ P₂) (Q := P₃) (H := ⊤)
    hE₂ (hel ho₃)
    (fun x hx y hy => ((Subgroup.mem_centralizer_iff.mp (hE₂C hx)) y (hP₃K hy)).symm) hE₂P₃
    (a := 2) (b := 1) hE₂card (by rw [hcard ho₃, pow_one]) le_top le_top
  omega

end Rank

theorem opx_core {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2) {K K' : Subgroup S}
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKc : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1)
    (hKc' : ∀ x ∈ K', (∀ y ∈ K', x * y = y * x) → x = 1)
    (hpK : p ∣ Nat.card K) (hpK' : p ∣ Nat.card K')
    (hAut : Nat.card (MulAut ↥K') ≤ 2 * Nat.card ↥K')
    {g : S} (hgp : ∃ k : ℕ, g ^ (p ^ k) = 1)
    (hgK : ∀ x ∈ K, g * x * g⁻¹ = x) (hgK' : ∀ x ∈ K', g * x * g⁻¹ ∈ K') : g ∈ K' := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hgp
  have hgN : g ∈ Subgroup.normalizer (K' : Set S) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hgK' y, fun hy => ?_⟩
    let φ : ↥K' → ↥K' := fun x => ⟨g * x * g⁻¹, hgK' x x.2⟩
    have hφ : Function.Injective φ := fun x z h =>
      Subtype.ext (by simpa [φ] using congrArg Subtype.val h)
    obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hφ ⟨g * y * g⁻¹, hy⟩
    have hxy : (x : S) = y := by simpa [φ] using congrArg Subtype.val hx
    exact hxy ▸ x.2
  obtain ⟨α, hα1, hα2⟩ : ∃ α : MulAut ↥K', (∀ x : ↥K', (α x : S) = g * x * g⁻¹) ∧
      α ^ (p ^ k) = 1 := by
    refine ⟨K'.normalizerMonoidHom ⟨g, hgN⟩, fun x => rfl, ?_⟩
    rw [← map_pow]
    have h1 : (⟨g, hgN⟩ : Subgroup.normalizer (K' : Set S)) ^ (p ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [h1, map_one]
  have hZ : ∀ x : ↥K', (∀ y : ↥K', x * y = y * x) → x = 1 := fun x hx =>
    Subtype.ext (hKc' x x.2 fun y hy => congrArg Subtype.val (hx ⟨y, hy⟩))
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨y, hy⟩ := opx_inner_of_odd_order hZ hAut hodd hα2
  have hy0 : (y : S) ∈ K' := y.2
  have hgy : ∀ x ∈ K', g * x * g⁻¹ = (y : S) * x * (y : S)⁻¹ := fun x hx => by
    have h := congrArg Subtype.val (hy ⟨x, hx⟩)
    rw [hα1] at h
    exact h
  obtain ⟨g', hg'⟩ : ∃ g' : S, g' = (y : S)⁻¹ * g := ⟨_, rfl⟩
  have hg'K' : ∀ x ∈ K', x * g' = g' * x := by
    intro x hx
    have h := hgy x hx
    rw [mul_inv_eq_iff_eq_mul] at h
    rw [hg']
    calc x * ((y : S)⁻¹ * g) = (y : S)⁻¹ * ((y : S) * x * (y : S)⁻¹ * g) := by group
      _ = (y : S)⁻¹ * (g * x) := by rw [h]
      _ = (y : S)⁻¹ * g * x := by rw [mul_assoc]
  have hg'K : ∀ x ∈ K, x * g' = g' * x := by
    intro x hx
    have h1 : g * x = x * g := by
      have h := hgK x hx
      rwa [mul_inv_eq_iff_eq_mul] at h
    have h2 : x * (y : S)⁻¹ = (y : S)⁻¹ * x :=
      (Commute.inv_right (hcomm x hx y hy0 : Commute x y))
    rw [hg']
    calc x * ((y : S)⁻¹ * g) = (x * (y : S)⁻¹) * g := by rw [mul_assoc]
      _ = ((y : S)⁻¹ * x) * g := by rw [h2]
      _ = (y : S)⁻¹ * (x * g) := by rw [mul_assoc]
      _ = (y : S)⁻¹ * (g * x) := by rw [h1]
      _ = (y : S)⁻¹ * g * x := by rw [mul_assoc]
  have hg'ord : g' ^ (p ^ k) = 1 := by
    have hyg' : Commute (y : S) g' := hg'K' y hy0
    have hgeq : g = (y : S) * g' := by rw [hg']; group
    have h1 : (y : S) ^ (p ^ k) * g' ^ (p ^ k) = 1 := by
      rw [← hyg'.mul_pow, ← hgeq]
      exact hk
    have h2 : (y : S) ^ (p ^ k) = 1 := by
      refine hKc' _ (K'.pow_mem hy0 _) fun x hx => ?_
      have hc : Commute (g' ^ (p ^ k)) x := (Commute.pow_left (hg'K' x hx).symm _)
      have h3 : (y : S) ^ (p ^ k) = (g' ^ (p ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h3]
      exact hc.inv_left
    rw [h2, one_mul] at h1
    exact h1
  have hg'1 : g' = 1 := by
    by_contra hne
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hg'ord)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.1 (by simpa using hj))
    have hdvd : p ∣ Nat.card (Subgroup.zpowers g') := by
      rw [Nat.card_zpowers, hj]
      exact dvd_pow_self p hj0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
    obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' p hpK'
    have hZK : Subgroup.zpowers g' ≤ Subgroup.centralizer (K : Set S) :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 hg'K)
    have hZK' : Subgroup.zpowers g' ≤ Subgroup.centralizer (K' : Set S) :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 hg'K')
    have h := opx_three_le_pRank hp (K₁ := K) (K₂ := Subgroup.zpowers g') (K₃ := K')
      (fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hZK hb) a ha) hcomm
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.1 (hZK' ha) b hb).symm)
      hKc hKc' x.2 z.2 x'.2 (by rw [Subgroup.orderOf_coe]; exact hx)
      (by rw [Subgroup.orderOf_coe]; exact hz) (by rw [Subgroup.orderOf_coe]; exact hx')
    omega
  have hyg : (y : S) = g := inv_mul_eq_one.1 (hg'.symm.trans hg'1)
  rw [← hyg]
  exact hy0

end CFSG.Quasithin
