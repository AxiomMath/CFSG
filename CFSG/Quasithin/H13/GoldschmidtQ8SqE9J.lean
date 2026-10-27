module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Odd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup

variable {G : Type*} [Group G] {A B : Subgroup G}

theorem mem_sup_zpowers_iff {y : G} (hy : y ∈ normalizer (A : Set G)) {x : G} :
    x ∈ A ⊔ zpowers y ↔ ∃ a ∈ A, ∃ c : ℤ, x = a * y ^ c := by
  have h1 := Subgroup.coe_mul_of_right_le_normalizer_left A (zpowers y) (zpowers_le.mpr hy)
  rw [← SetLike.mem_coe, h1, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨c, rfl⟩ := mem_zpowers_iff.mp hb
    exact ⟨a, ha, c, rfl⟩
  · rintro ⟨a, ha, c, rfl⟩
    exact ⟨a, ha, y ^ c, mem_zpowers_iff.mpr ⟨c, rfl⟩, rfl⟩

theorem pow_three_zpow {y : G} (hy3 : orderOf y = 3) (c : ℤ) : (y ^ c) ^ 3 = 1 := by
  have h3 : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]

theorem odd_orderOf_zpow {y : G} (hy3 : orderOf y = 3) (c : ℤ) : Odd (orderOf (y ^ c)) :=
  Odd.of_dvd_nat (n := 3) (by decide) (orderOf_dvd_of_pow_eq_one (pow_three_zpow hy3 c))

namespace Cfg

theorem disjoint_zpowers (h : Cfg A B) {y : G} (hy3 : orderOf y = 3) :
    Disjoint A (zpowers y) := by
  apply Subgroup.disjoint_of_coprime_natCard
  rw [h.card_A, Nat.card_zpowers, hy3]
  norm_num

theorem card_J (h : Cfg A B) {y : G} (hy3 : orderOf y = 3) (hy : y ∈ normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ zpowers y) = 24 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A (zpowers y)
    (zpowers_le.mpr hy) (h.disjoint_zpowers hy3), h.card_A, Nat.card_zpowers, hy3]

theorem mem_A_of_sq_mem (h : Cfg A B) {y : G} (hy3 : orderOf y = 3)
    (hy : y ∈ normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ zpowers y) (hx2 : x * x ∈ A) :
    x ∈ A := by
  obtain ⟨a, ha, c, rfl⟩ := (mem_sup_zpowers_iff hy).mp hx
  have hN : y ^ c ∈ normalizer (A : Set G) := Subgroup.zpow_mem _ hy c
  have ha'' : y ^ c * a * (y ^ c)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hN a).mp ha
  have h2 : (y ^ c) ^ 2 ∈ A := by
    have : (y ^ c) ^ 2 = (a * (y ^ c * a * (y ^ c)⁻¹))⁻¹ * (a * y ^ c * (a * y ^ c)) := by
      rw [pow_two]; group
    rw [this]
    exact A.mul_mem (A.inv_mem (A.mul_mem ha ha'')) hx2
  have h3 : (y ^ c) ^ 2 ∈ zpowers y :=
    Subgroup.pow_mem _ (Subgroup.zpow_mem _ (mem_zpowers y) c) 2
  have h4 : (y ^ c) ^ 2 = 1 := (Subgroup.disjoint_def.mp (h.disjoint_zpowers hy3)) h2 h3
  have h5 : y ^ c = 1 := by
    have h3' := pow_three_zpow hy3 c
    calc y ^ c = (y ^ c) ^ 3 * ((y ^ c) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h4]; group
  rw [h5, mul_one]
  exact ha

theorem J_unique_involution (h : Cfg A B) {y : G} (hy3 : orderOf y = 3)
    (hy : y ∈ normalizer (A : Set G)) {u : G} (hu : u ∈ A ⊔ zpowers y) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : u = h.z := by
  have hA : u ∈ A := h.mem_A_of_sq_mem hy3 hy hu (by rw [hu2]; exact one_mem _)
  obtain ⟨w, rfl⟩ := h.exists_phiA hA
  have key : ∀ w : Q8, w * w = 1 → w ≠ 1 → w = a 2 := by decide +kernel
  have hw : w = a 2 := key w (h.phiA_inj (by rw [map_mul, hu2, map_one]))
    (fun hw => hu1 (by rw [hw, map_one]))
  rw [hw]
  rfl

theorem J_centralizer (h : Cfg A B) {y : G} (hy3 : orderOf y = 3)
    (hy : y ∈ normalizer (A : Set G)) (hyc : ∃ a ∈ A, y * a ≠ a * y) {x : G}
    (hx : x ∈ A ⊔ zpowers y) (hc : ∀ m ∈ A, x * m = m * x) : x = 1 ∨ x = h.z := by
  obtain ⟨a, ha, c, rfl⟩ := (mem_sup_zpowers_iff hy).mp hx
  have hax : ∀ m ∈ A, y ^ c * m * (y ^ c)⁻¹ = m ∨ y ^ c * m * (y ^ c)⁻¹ = m⁻¹ := by
    intro m hm
    have h1 : a * y ^ c * m = m * (a * y ^ c) := hc m hm
    have h2 : y ^ c * m * (y ^ c)⁻¹ = a⁻¹ * m * a := by
      calc y ^ c * m * (y ^ c)⁻¹ = a⁻¹ * (a * y ^ c * m) * (y ^ c)⁻¹ := by group
        _ = a⁻¹ * (m * (a * y ^ c)) * (y ^ c)⁻¹ := by rw [h1]
        _ = a⁻¹ * m * a := by group
    rw [h2]
    simpa using h.inner_axis (A.inv_mem ha) hm
  have hcomm := commute_of_inv_or (odd_orderOf_zpow hy3 c) hax
  have hc1 : y ^ c = 1 := by
    by_contra hne
    obtain ⟨m, hm, hym⟩ := hyc
    apply hym
    have hmod : y ^ (c % 3) = y ^ c := by simpa [hy3] using zpow_mod_orderOf y c
    have h3 : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
    have : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
    rcases this with h0 | h0 | h0
    · exact absurd (by rw [← hmod, h0, zpow_zero]) hne
    · rw [h0, zpow_one] at hmod
      rw [hmod]; exact hcomm m hm
    · rw [h0] at hmod
      have h4 : y = (y ^ c) ^ 2 := by
        rw [← hmod, zpow_ofNat, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, h3, one_mul,
          pow_one]
      rw [h4]
      exact (Commute.pow_left (show Commute (y ^ c) m from hcomm m hm) 2).eq
  rw [hc1, mul_one] at hc ⊢
  obtain ⟨w, rfl⟩ := h.exists_phiA ha
  have hw : ∀ w' : Q8, w * w' = w' * w := fun w' =>
    h.phiA_inj (by rw [map_mul, map_mul]; exact hc (h.phiA w') (h.phiA_mem w'))
  rcases q8_central w hw with rfl | rfl
  · left; rw [map_one]
  · right; rfl

end Cfg

end CFSG.Quasithin.H13.Q8SqE9
