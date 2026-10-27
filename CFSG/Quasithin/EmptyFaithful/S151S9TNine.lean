module

public import CFSG.Quasithin.EmptyFaithful.S151S8C1
public import CFSG.Quasithin.EmptyFaithful.S151S9TCoreP
public import CFSG.Quasithin.EmptyFaithful.S151S9TCoreS

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace NineCore

open CoreP

section Elementary

variable {G : Type*} [Group G]

theorem exists_two_pow_mul_three_pow_of_dvd_nine {n a : ℕ} (h : n ∣ 9 * 2 ^ a) :
    ∃ i j : ℕ, n = 2 ^ i * 3 ^ j := by
  obtain ⟨k₁, k₂, hk₁, hk₂, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk₂
  obtain ⟨j, -, rfl⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp (show k₁ ∣ 3 ^ 2 by simpa using hk₁)
  exact ⟨i, j, mul_comm _ _⟩

theorem eq_one_of_mem_of_orderOf_dvd_three {B : Subgroup G} (hB2 : IsPGroup 2 ↥B) {g : G}
    (hg : g ∈ B) (h3 : orderOf g ∣ 3) : g = 1 := by
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd hg (not_mem_of_orderOf_eq_three hB2 h)

theorem orderOf_dvd_three_of_mem_zpowers [Finite G] {x g : G} (hx3 : orderOf x = 3)
    (hg : g ∈ Subgroup.zpowers x) : orderOf g ∣ 3 := by
  have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers x) hg
  rwa [Nat.card_zpowers, hx3] at this

theorem pow_three_eq_one_of_mem_zpowers [Finite G] {x g : G} (hx3 : orderOf x = 3)
    (hg : g ∈ Subgroup.zpowers x) : g ^ 3 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_three_of_mem_zpowers hx3 hg)

theorem eq_one_of_mem_zpowers_of_mem_zpowers [Finite G] {B Y₁ Y₆ : Subgroup G}
    (hB2 : IsPGroup 2 ↥B) (hinf : Y₁ ⊓ Y₆ = B) {x₁ x₆ : G} (hx₁ : x₁ ∈ Y₁) (hx₆ : x₆ ∈ Y₆)
    (hx₁3 : orderOf x₁ = 3) {g : G} (hg₁ : g ∈ Subgroup.zpowers x₁)
    (hg₆ : g ∈ Subgroup.zpowers x₆) : g = 1 := by
  have hgB : g ∈ B := by
    rw [← hinf]
    exact ⟨Subgroup.zpowers_le.mpr hx₁ hg₁, Subgroup.zpowers_le.mpr hx₆ hg₆⟩
  exact eq_one_of_mem_of_orderOf_dvd_three hB2 hgB (orderOf_dvd_three_of_mem_zpowers hx₁3 hg₁)

theorem commute_of_mem_zpowers {x y u v : G} (h : Commute x y) (hu : u ∈ Subgroup.zpowers x)
    (hv : v ∈ Subgroup.zpowers y) : Commute u v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact h.zpow_zpow k l

theorem zpowers_le_normalizer_zpowers {x y : G} (h : Commute x y) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
  exact (commute_of_mem_zpowers h.symm hz (Subgroup.mem_zpowers x)).eq

theorem exists_mul_of_mem_zpowers_sup {x y : G} (h : Commute x y) {e : G}
    (he : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    ∃ u ∈ Subgroup.zpowers x, ∃ v ∈ Subgroup.zpowers y, u * v = e := by
  have h1 := Subgroup.coe_mul_of_left_le_normalizer_right _ _ (zpowers_le_normalizer_zpowers h)
  have he' : e ∈ (Subgroup.zpowers x : Set G) * (Subgroup.zpowers y : Set G) := by
    rw [← h1]; exact he
  exact Set.mem_mul.mp he'

theorem exists_pow_lt_of_mem_zpowers [Finite G] {x g : G} (hx3 : orderOf x = 3)
    (hg : g ∈ Subgroup.zpowers x) : ∃ a : ℕ, a < 3 ∧ g = x ^ a := by
  classical
  obtain ⟨n, hn, hng⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hg)
  rw [Finset.mem_range, hx3] at hn
  exact ⟨n, hn, hng.symm⟩

theorem exists_pow_mul_pow_of_mem_sup [Finite G] {x y : G} (hx3 : orderOf x = 3)
    (hy3 : orderOf y = 3) (h : Commute x y) {e : G}
    (he : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    ∃ a b : ℕ, a < 3 ∧ b < 3 ∧ e = x ^ a * y ^ b := by
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_zpowers_sup h he
  obtain ⟨a, ha, rfl⟩ := exists_pow_lt_of_mem_zpowers hx3 hu
  obtain ⟨b, hb, rfl⟩ := exists_pow_lt_of_mem_zpowers hy3 hv
  exact ⟨a, b, ha, hb, rfl⟩

theorem pow_three_eq_one_of_mem_zpowers_sup [Finite G] {x y : G} (hx3 : orderOf x = 3)
    (hy3 : orderOf y = 3) (h : Commute x y) {e : G}
    (he : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) : e ^ 3 = 1 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_zpowers_sup h he
  rw [(commute_of_mem_zpowers h hu hv).mul_pow, pow_three_eq_one_of_mem_zpowers hx3 hu,
    pow_three_eq_one_of_mem_zpowers hy3 hv, one_mul]

theorem card_zpowers_sup [Finite G] {x y : G} (hx3 : orderOf x = 3) (hy3 : orderOf y = 3)
    (h : Commute x y) (hxy : ∀ g ∈ Subgroup.zpowers x, g ∈ Subgroup.zpowers y → g = 1) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  have hbot : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun g hg => hxy g hg.1 hg.2
  have h1 := B6.relIndex_inf_eq_relIndex_sup (zpowers_le_normalizer_zpowers h)
  rw [hbot, Subgroup.relIndex_bot_left, Nat.card_zpowers, hy3] at h1
  have h2 := Subgroup.relIndex_mul_card (Subgroup.zpowers x)
    (Subgroup.zpowers x ⊔ Subgroup.zpowers y)
  rw [inf_eq_left.mpr le_sup_left, Nat.card_zpowers, hx3, ← h1] at h2
  omega

theorem zpowers_eq_of_mem_of_pow_three [Finite G] {f e : G} (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1)
    (he : e ∈ Subgroup.zpowers f) (hne : e ≠ 1) :
    Subgroup.zpowers f = Subgroup.zpowers e :=
  zpowers_eq_of_mem_of_ne_one (orderOf_eq_prime hf3 hf1) he hne

theorem exists_mem_four_of_mem_sup [Finite G] {x y : G} (hx3 : orderOf x = 3)
    (hy3 : orderOf y = 3) (h : Commute x y)
    (hxy : ∀ g ∈ Subgroup.zpowers x, g ∈ Subgroup.zpowers y → g = 1) {e : G}
    (he : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) (hne : e ≠ 1) :
    ∃ f ∈ ({x, y, x * y, x * y⁻¹} : Set G), Subgroup.zpowers f = Subgroup.zpowers e := by
  have hx : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hy : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx3; omega
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hy3; omega
  have hy2 : y ^ 2 = y⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hy)
  have hyinv : y⁻¹ ^ 2 = y := by rw [inv_pow, hy2, inv_inv]
  have hxy3 : (x * y) ^ 3 = 1 := by rw [h.mul_pow, hx, hy, one_mul]
  have hxyi3 : (x * y⁻¹) ^ 3 = 1 := by
    rw [h.inv_right.mul_pow, hx, inv_pow, hy, inv_one, one_mul]
  have hxy1 : x * y ≠ 1 := by
    intro h1
    have hxe : x = y⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h2 := hxy x (Subgroup.mem_zpowers x)
      (by rw [hxe]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
    exact hx1 h2
  have hxyi1 : x * y⁻¹ ≠ 1 := by
    intro h1
    have hxe : x = y := mul_inv_eq_one.mp h1
    have h2 := hxy x (Subgroup.mem_zpowers x) (by rw [hxe]; exact Subgroup.mem_zpowers y)
    exact hx1 h2
  have key : ∀ {f e : G}, f ^ 3 = 1 → f ≠ 1 → ∀ k : ℕ, e = f ^ k → e ≠ 1 →
      Subgroup.zpowers f = Subgroup.zpowers e := fun hf3 hf1 k hk hne =>
    zpowers_eq_of_mem_of_pow_three hf3 hf1 (hk ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k) hne
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_pow_mul_pow_of_mem_sup hx3 hy3 h he
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hne
  · exact ⟨y, by simp, key hy hy1 1 (by simp) hne⟩
  · exact ⟨y, by simp, key hy hy1 2 (by simp) hne⟩
  · exact ⟨x, by simp, key hx hx1 1 (by simp) hne⟩
  · exact ⟨x * y, by simp, key hxy3 hxy1 1 (by simp) hne⟩
  · exact ⟨x * y⁻¹, by simp, key hxyi3 hxyi1 1 (by simp [hy2]) hne⟩
  · exact ⟨x, by simp, key hx hx1 2 (by simp) hne⟩
  · exact ⟨x * y⁻¹, by simp, key hxyi3 hxyi1 2 (by rw [h.inv_right.mul_pow, hyinv]; simp) hne⟩
  · exact ⟨x * y, by simp, key hxy3 hxy1 2 (by rw [h.mul_pow]) hne⟩

end Elementary

section Transversal

variable {G : Type*} [Group G] [Finite G]

theorem exists_mul_of_card_eq_mul {B P E : Subgroup G} (hBP : B ≤ P) (hEP : E ≤ P)
    (hEB : ∀ e ∈ E, e ∈ B → e = 1) (hcard : Nat.card ↥P = Nat.card ↥E * Nat.card ↥B)
    {g : G} (hg : g ∈ P) : ∃ e ∈ E, ∃ b ∈ B, g = e * b := by
  classical
  let ψ : ↥E → ↥P ⧸ B.subgroupOf P := fun e => QuotientGroup.mk ⟨e, hEP e.2⟩
  have hinj : Function.Injective ψ := by
    intro e e' h
    have h1 := QuotientGroup.eq.mp h
    have h2 : (e : G)⁻¹ * e' ∈ B := Subgroup.mem_subgroupOf.mp h1
    have h3 : (e : G)⁻¹ * e' ∈ E := E.mul_mem (E.inv_mem e.2) e'.2
    exact Subtype.ext (inv_mul_eq_one.mp (hEB _ h3 h2))
  have hcardP : Nat.card (↥P ⧸ B.subgroupOf P) = Nat.card ↥E := by
    have h1 := Subgroup.index_mul_card (B.subgroupOf P)
    have h2 : Nat.card ↥(B.subgroupOf P) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
    rw [h2, hcard] at h1
    rw [← Subgroup.index_eq_card]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  obtain ⟨⟨e, he⟩, hψ⟩ := (hinj.bijective_of_nat_card_le hcardP.le).2 (QuotientGroup.mk ⟨g, hg⟩)
  have h1 := QuotientGroup.eq.mp hψ
  have h2 : e⁻¹ * g ∈ B := Subgroup.mem_subgroupOf.mp h1
  exact ⟨e, he, e⁻¹ * g, h2, by group⟩

end Transversal

section Residual

variable {G : Type*} [Group G] [Finite G]

theorem pow_three_mem_normalCoreIn_of_inf_eq {B P Y₁ Y₆ : Subgroup G} (hY₁P : Y₁ ≤ P)
    (hY₆P : Y₆ ≤ P) (hinf : Y₁ ⊓ Y₆ = B) (hc₁ : Nat.card ↥P = 3 * Nat.card ↥Y₁)
    (hc₆ : Nat.card ↥P = 3 * Nat.card ↥Y₆) {y : G} (hy : y ∈ oPrimeResidualOf 3 P) :
    y ^ 3 ∈ normalCoreIn B P := by
  rw [oPrimeResidualOf_eq_map] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have h₁ := pow_three_mem_normalCore (index_subgroupOf_eq_three hY₁P hc₁) hy'
  have h₆ := pow_three_mem_normalCore (index_subgroupOf_eq_three hY₆P hc₆) hy'
  refine mem_normalCoreIn_iff.mpr ⟨P.pow_mem y'.2 3, fun g hg => ?_⟩
  rw [← hinf]
  exact ⟨Subgroup.mem_subgroupOf.mp (mem_normalCore_iff.mp h₁ ⟨g, hg⟩),
    Subgroup.mem_subgroupOf.mp (mem_normalCore_iff.mp h₆ ⟨g, hg⟩)⟩

theorem oPrimeResidualOf_sup_eq {B P Y₁ Y₆ : Subgroup G} (hBY₁ : B ≤ Y₁) (hBY₆ : B ≤ Y₆)
    (hY₁P : Y₁ ≤ P) (hY₆P : Y₆ ≤ P) (hsup : Y₁ ⊔ Y₆ = P)
    (hc₁ : Nat.card ↥Y₁ = 3 * Nat.card ↥B) (hc₆ : Nat.card ↥Y₆ = 3 * Nat.card ↥B) {x₁ x₆ : G}
    (hx₁ : x₁ ∈ Y₁) (hx₆ : x₆ ∈ Y₆) (hx₁3 : orderOf x₁ = 3) (hx₆3 : orderOf x₆ = 3)
    (hx₁B : x₁ ∉ B) (hx₆B : x₆ ∉ B) : oPrimeResidualOf 3 P ⊔ B = P := by
  refine le_antisymm (sup_le (oPrimeResidualOf_le_self 3 P) (hBY₁.trans hY₁P)) ?_
  refine hsup.ge.trans (sup_le ?_ ?_)
  · refine (sup_eq_of_card_eq_three_mul hBY₁ (Subgroup.zpowers_le.mpr hx₁) hc₁
      (Subgroup.mem_zpowers x₁) hx₁B).ge.trans (sup_le_sup_right ?_ B)
    exact Subgroup.zpowers_le.mpr
      (mem_oPrimeResidualOf_of_orderOf (hY₁P hx₁) (k := 1) (by simpa using hx₁3))
  · refine (sup_eq_of_card_eq_three_mul hBY₆ (Subgroup.zpowers_le.mpr hx₆) hc₆
      (Subgroup.mem_zpowers x₆) hx₆B).ge.trans (sup_le_sup_right ?_ B)
    exact Subgroup.zpowers_le.mpr
      (mem_oPrimeResidualOf_of_orderOf (hY₆P hx₆) (k := 1) (by simpa using hx₆3))

end Residual

section Lattice

variable {G : Type*} [Group G] [Finite G]

theorem inf_eq_of_lattice {B P Y₁ Y₆ : Subgroup G} (hBY₁ : B ≤ Y₁) (hBY₆ : B ≤ Y₆)
    (hY₁P : Y₁ ≤ P) (hne : Y₁ ≠ Y₆) (hc₁ : Nat.card ↥Y₁ = 3 * Nat.card ↥B)
    (hc₆ : Nat.card ↥Y₆ = 3 * Nat.card ↥B) (hcP : Nat.card ↥P = 9 * Nat.card ↥B)
    (hlat : ∀ K : Subgroup G, B ≤ K → K ≤ P → K = B ∨ K = Y₁ ∨ K = Y₆ ∨ K = P) :
    Y₁ ⊓ Y₆ = B := by
  have hpos : 0 < Nat.card ↥B := Nat.card_pos
  rcases hlat (Y₁ ⊓ Y₆) (le_inf hBY₁ hBY₆) (inf_le_left.trans hY₁P) with h | h | h | h
  · exact h
  · exact absurd (Subgroup.eq_of_le_of_card_ge (h.ge.trans inf_le_right)
      (by rw [hc₁, hc₆])) hne
  · exact absurd (Subgroup.eq_of_le_of_card_ge (h.ge.trans inf_le_left)
      (by rw [hc₁, hc₆])).symm hne
  · have := Subgroup.card_le_of_le (h.ge.trans inf_le_left)
    rw [hcP, hc₁] at this
    omega

theorem mem_normalizer_of_mem_normalizer_other {B P Y₁ Y₆ : Subgroup G} (hBY₁ : B ≤ Y₁)
    (hY₁P : Y₁ ≤ P) (hne : Y₁ ≠ Y₆) (hc₁ : Nat.card ↥Y₁ = 3 * Nat.card ↥B)
    (hcP : Nat.card ↥P = 9 * Nat.card ↥B)
    (hlat : ∀ K : Subgroup G, B ≤ K → K ≤ P → K = B ∨ K = Y₁ ∨ K = Y₆ ∨ K = P) {t : G}
    (htB : t ∈ Subgroup.normalizer (B : Set G)) (htP : t ∈ Subgroup.normalizer (P : Set G))
    (htY₆ : t ∈ Subgroup.normalizer (Y₆ : Set G)) : t ∈ Subgroup.normalizer (Y₁ : Set G) := by
  have hpos : 0 < Nat.card ↥B := Nat.card_pos
  have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  have hB : B ≤ Y₁.map (MulAut.conj t).toMonoidHom := fun b hb =>
    Subgroup.mem_map.mpr ⟨t⁻¹ * b * t, hBY₁
      ((Subgroup.mem_normalizer_iff.mp htB (t⁻¹ * b * t)).mpr (by simpa [mul_assoc] using hb)),
      by show t * (t⁻¹ * b * t) * t⁻¹ = b; group⟩
  have hP : Y₁.map (MulAut.conj t).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp htP y).mp (hY₁P hy)
  have hcard := Subgroup.card_map_of_injective (K := Y₁) hinj
  rcases hlat _ hB hP with h | h | h | h
  · rw [h, hc₁] at hcard
    omega
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  · exact absurd (Subgroup.map_injective hinj
      (h.trans (map_conj_eq_of_mem_normalizer htY₆).symm)) hne
  · rw [h, hcP, hc₁] at hcard
    omega

omit [Finite G] in
theorem eq_or_sup_le_of_le_sup {L S P Y₁ Y₆ : Subgroup G} (hBP : S ⊓ L ≤ P)
    (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hlat : ∀ K : Subgroup G, S ⊓ L ≤ K → K ≤ P →
      K = S ⊓ L ∨ K = Y₁ ∨ K = Y₆ ∨ K = P)
    (hY₁ : ¬ S ≤ Subgroup.normalizer (Y₁ : Set G)) (hY₆ : ¬ S ≤ Subgroup.normalizer (Y₆ : Set G))
    {K : Subgroup G} (hSK : S ≤ K) (hKH : K ≤ P ⊔ S) : K = S ∨ P ⊔ S ≤ K := by
  have hZn : S ≤ Subgroup.normalizer ((K ⊓ P : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hSK hs), hSP hs⟩
  rcases hlat (K ⊓ P) (le_inf (inf_le_left.trans hSK) hBP) inf_le_right with h | h | h | h
  · left
    refine le_antisymm (fun k hk => ?_) hSK
    have hk' : k ∈ (S : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S P hSP, sup_comm]
      exact hKH hk
    obtain ⟨s, hs, p, hp, rfl⟩ := Set.mem_mul.mp hk'
    have hpK : p ∈ K ⊓ P :=
      ⟨by simpa using K.mul_mem (K.inv_mem (hSK hs)) hk, hp⟩
    rw [h] at hpK
    exact S.mul_mem hs hpK.1
  · rw [h] at hZn
    exact absurd hZn hY₁
  · rw [h] at hZn
    exact absurd hZn hY₆
  · exact Or.inr (sup_le (h.ge.trans inf_le_left) hSK)

theorem relIndex_sup_eq_of_card {P S : Subgroup G} {n : ℕ}
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hcard : Nat.card ↥P = n * Nat.card ↥(S ⊓ P)) :
    S.relIndex (P ⊔ S) = n := by
  have h1 : (S ⊓ P).relIndex P = S.relIndex (S ⊔ P) := B6.relIndex_inf_eq_relIndex_sup hSP
  have h2 : (S ⊓ P).relIndex P * Nat.card ↥(S ⊓ P ⊓ P) = Nat.card ↥P :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr inf_le_right] at h2
  have hpos : 0 < Nat.card ↥(S ⊓ P) := Nat.card_pos
  rw [sup_comm, ← h1]
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans hcard)

theorem isMinParabolic_of_isMax {H S : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hSH : S ≤ H)
    (hodd : ¬ 2 ∣ S.relIndex H) (hmax : IsMaxSubgroupIn H S)
    (hnn : ¬ H ≤ Subgroup.normalizer (S : Set G)) : IsMinParabolicOf H H := by
  have hsyl : IsSylowTwoOf S H := ⟨hSH, hS2, hodd⟩
  refine (minParabolic_iff.mp ⟨hsyl, hnn, isUniqueMaxOver_iff.mpr ⟨hmax, le_rfl, ?_⟩⟩).1
  intro N hN hSN
  by_contra hne
  exact hN.1.ne (hmax.2 N (lt_of_le_of_ne hSN (Ne.symm hne)) hN.le)

end Lattice

end NineCore

open CoreP NineCore

theorem idx9_core {G : Type} [Group G] [Finite G] {L S P Y₁ Y₆ : Subgroup G}
    (hS2 : IsPGroup 2 ↥S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hPL : P ≤ L) (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hBY₁ : S ⊓ L ≤ Y₁) (hBY₆ : S ⊓ L ≤ Y₆) (hY₁P : Y₁ ≤ P) (hY₆P : Y₆ ≤ P)
    (hne : Y₁ ≠ Y₆) (hsup : Y₁ ⊔ Y₆ = P)
    (hc₁ : Nat.card ↥Y₁ = 3 * Nat.card ↥(S ⊓ L)) (hc₆ : Nat.card ↥Y₆ = 3 * Nat.card ↥(S ⊓ L))
    (hcP : Nat.card ↥P = 9 * Nat.card ↥(S ⊓ L))
    (hlat : ∀ K : Subgroup G, S ⊓ L ≤ K → K ≤ P → K = S ⊓ L ∨ K = Y₁ ∨ K = Y₆ ∨ K = P)
    (hnN : ¬ Y₁ ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))
    (hswap : ∃ t ∈ S, t ∉ Subgroup.normalizer (Y₁ : Set G))
    {x₁ x₆ : G} (hx₁ : x₁ ∈ Y₁) (hx₆ : x₆ ∈ Y₆) (hx₁3 : orderOf x₁ = 3) (hx₆3 : orderOf x₆ = 3)
    (hcomm : x₁ * x₆ = x₆ * x₁)
    {r : Fin 5 → G}
    (hrE : ∀ i, ∀ a b : Fin 3,
      (x₁ ^ (a : ℕ) * x₆ ^ (b : ℕ))⁻¹ * r i * (x₁ ^ (a : ℕ) * x₆ ^ (b : ℕ)) ∈ S ⊓ L)
    (hinj : ∀ f : G, f ∈ ({x₁, x₆, x₁ * x₆, x₁ * x₆⁻¹} : Set G) →
      Function.Injective fun i => ⁅⁅r i, f⁆, f⁆) :
    CharTwo P ∧ IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
      oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  classical
  have hB2 : IsPGroup 2 ↥(S ⊓ L) := hS2.to_le inf_le_left
  obtain ⟨a, ha⟩ := hB2.exists_card_eq
  have hPcard : Nat.card ↥P = 9 * 2 ^ a := by rw [hcP, ha]
  have hBP : S ⊓ L ≤ P := hBY₁.trans hY₁P
  have hinf : Y₁ ⊓ Y₆ = S ⊓ L := inf_eq_of_lattice hBY₁ hBY₆ hY₁P hne hc₁ hc₆ hcP hlat
  have hx₁B : x₁ ∉ S ⊓ L := not_mem_of_orderOf_eq_three hB2 hx₁3
  have hx₆B : x₆ ∉ S ⊓ L := not_mem_of_orderOf_eq_three hB2 hx₆3
  have hc : Commute x₁ x₆ := hcomm
  have hxy : ∀ g ∈ Subgroup.zpowers x₁, g ∈ Subgroup.zpowers x₆ → g = 1 := fun g hg₁ hg₆ =>
    eq_one_of_mem_zpowers_of_mem_zpowers hB2 hinf hx₁ hx₆ hx₁3 hg₁ hg₆
  have hEP : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆ ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr (hY₁P hx₁)) (Subgroup.zpowers_le.mpr (hY₆P hx₆))
  have hEcard : Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆) = 9 :=
    card_zpowers_sup hx₁3 hx₆3 hc hxy
  have hE3 : IsPGroup 3 ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆) :=
    IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hEsyl : ¬ 3 ∣ ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆).subgroupOf P).index := by
    have h1 := Subgroup.card_mul_index ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆).subgroupOf P)
    have h2 : Nat.card ↥((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆).subgroupOf P) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hEcard]
    rw [h2, hPcard] at h1
    have h3 : ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆).subgroupOf P).index = 2 ^ a := by
      omega
    rw [h3]
    exact not_three_dvd_two_pow a
  have hEB : ∀ e ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆, e ∈ S ⊓ L → e = 1 :=
    fun e he heB => eq_one_of_mem_of_orderOf_dvd_three hB2 heB
      (orderOf_dvd_of_pow_eq_one (pow_three_eq_one_of_mem_zpowers_sup hx₁3 hx₆3 hc he))
  have hPE : ∀ g ∈ P, ∃ e ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆, ∃ b ∈ S ⊓ L,
      g = e * b := fun g hg =>
    exists_mul_of_card_eq_mul hBP hEP hEB (by rw [hcP, hEcard, mul_comm]) hg
  have hKn : P ≤ Subgroup.normalizer (normalCoreIn (S ⊓ L) P : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype fun k hk => conj_mem_normalCoreIn hg hk
  have hK2 : IsPGroup 2 ↥(normalCoreIn (S ⊓ L) P) := hB2.to_le normalCoreIn_le
  have hrK : ∀ i, r i ∈ normalCoreIn (S ⊓ L) P := fun i => by
    have h0 : r i ∈ S ⊓ L := by simpa using hrE i 0 0
    refine mem_normalCoreIn_iff.mpr ⟨hBP h0, fun g hg => ?_⟩
    obtain ⟨e, he, b, hb, hgb⟩ := hPE g⁻¹ (P.inv_mem hg)
    obtain ⟨α, β, hα, hβ, rfl⟩ := exists_pow_mul_pow_of_mem_sup hx₁3 hx₆3 hc he
    have h1 := hrE i ⟨α, hα⟩ ⟨β, hβ⟩
    have h2 : g * r i * g⁻¹ = b⁻¹ * ((x₁ ^ α * x₆ ^ β)⁻¹ * r i * (x₁ ^ α * x₆ ^ β)) * b := by
      have h3 : g * r i * g⁻¹ = (x₁ ^ α * x₆ ^ β * b)⁻¹ * r i * (x₁ ^ α * x₆ ^ β * b) := by
        rw [← hgb]; simp
      rw [h3]; group
    rw [h2]
    exact (S ⊓ L).mul_mem ((S ⊓ L).mul_mem ((S ⊓ L).inv_mem hb) h1) hb
  have hord : ∀ x ∈ P, ∃ i j : ℕ, orderOf x = 2 ^ i * 3 ^ j := fun x hx =>
    exists_two_pow_mul_three_pow_of_dvd_nine (hPcard ▸ Subgroup.orderOf_dvd_natCard P hx)
  have hN1 : ∀ y ∈ oPrimeResidualOf 3 P, ∃ m : ℕ, y ^ 3 ^ m ∈ normalCoreIn (S ⊓ L) P :=
    fun y hy => ⟨1, by
      simpa using pow_three_mem_normalCoreIn_of_inf_eq hY₁P hY₆P hinf (by rw [hcP, hc₁]; ring)
        (by rw [hcP, hc₆]; ring) hy⟩
  have hdat : ∀ e ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₆, e ≠ 1 → ∃ f : G,
      Subgroup.zpowers f = Subgroup.zpowers e ∧ ∃ r' : Fin 5 → G,
        (∀ i, r' i ∈ normalCoreIn (S ⊓ L) P) ∧ Function.Injective fun i => ⁅⁅r' i, f⁆, f⁆ :=
    fun e he hne' => by
      obtain ⟨f, hf, hfe⟩ := exists_mem_four_of_mem_sup hx₁3 hx₆3 hc hxy he hne'
      exact ⟨f, hfe, r, hrK, hinj f hf⟩
  obtain ⟨hchar, hN2, hN3⟩ := core_gen normalCoreIn_le_right hKn hK2 hord hEP hE3 hEsyl hN1 hdat
  have hSinf : S ⊓ P = S ⊓ L := le_antisymm (inf_le_inf_left S hPL) (le_inf inf_le_left hBP)
  have hidx : S.relIndex (P ⊔ S) = 9 :=
    relIndex_sup_eq_of_card hSP (by rw [hSinf]; exact hcP)
  have hnn : ¬ P ⊔ S ≤ Subgroup.normalizer (S : Set G) := fun h =>
    hnN fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h (Subgroup.mem_sup_left (hY₁P hy)), Subgroup.le_normalizer (hPL (hY₁P hy))⟩
  have hY₁S : ¬ S ≤ Subgroup.normalizer (Y₁ : Set G) := fun h => by
    obtain ⟨t, ht, htn⟩ := hswap
    exact htn (h ht)
  have hY₆S : ¬ S ≤ Subgroup.normalizer (Y₆ : Set G) := fun h => by
    obtain ⟨t, ht, htn⟩ := hswap
    exact htn (mem_normalizer_of_mem_normalizer_other hBY₁ hY₁P hne hc₁ hcP hlat
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hSN ht⟩) (hSP ht)
      (h ht))
  have hmax : IsMaxSubgroupIn (P ⊔ S) S := by
    refine ⟨lt_of_le_of_ne le_sup_right fun h => ?_, fun K hSK hKH => ?_⟩
    · rw [← h, Subgroup.relIndex_self] at hidx
      omega
    · rcases eq_or_sup_le_of_le_sup hBP hSP hlat hY₁S hY₆S hSK.le hKH with h | h
      · exact absurd h hSK.ne'
      · exact le_antisymm hKH h
  have hres : twoResidual (P ⊔ S) = oPrimeResidualOf 3 P := twoResidual_sup_eq hS2 hSP hord
  refine ⟨hchar, isMinParabolic_of_isMax hS2 le_sup_right ?_ hmax hnn, ?_,
    oPrimeResidualOf_sup_eq hBY₁ hBY₆ hY₁P hY₆P hsup hc₁ hc₆ hx₁ hx₆ hx₁3 hx₆3 hx₁B hx₆B⟩
  · show ¬ 2 ∣ S.relIndex (P ⊔ S)
    rw [hidx]
    decide
  · unfold NumC126
    rw [hres]
    exact ⟨hN2, hN3⟩

end CFSG.Quasithin.S151S9T
