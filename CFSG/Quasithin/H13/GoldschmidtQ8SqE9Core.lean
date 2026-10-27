module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Pair
public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Norm
public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Sl

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) =
      Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem card_sup_mul_card_inf {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

namespace Cfg

variable {A B : Subgroup G}

omit [Finite G] in
theorem card_inf (h : Cfg A B) : Nat.card ↥(A ⊓ B) = 2 := by
  have hzo : orderOf h.z = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact h.z_mul_self) h.z_ne_one
  have : A ⊓ B = zpowers h.z := by
    ext x
    rw [h.mem_inf_iff, mem_zpowers_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, zpow_zero _⟩
      · exact ⟨1, zpow_one _⟩
    · rintro ⟨k, rfl⟩
      have hk := zpow_mod_orderOf h.z k
      rw [hzo] at hk
      have : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases this with h0 | h1
      · left; rw [← hk]; simp [h0]
      · right; rw [← hk]; simp [h1]
  rw [this, Nat.card_zpowers, hzo]

theorem core (hcfg : Cfg A B) {H K Q : Subgroup G} (hQ : A ⊔ B = Q) (hQH : Q ≤ H)
    (hQnorm : ∀ x ∈ H, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hKH : K ≤ H)
    (hKodd : ∀ x ∈ H, Odd (orderOf x) → x ∈ K)
    (hKcard : Nat.card K = 9 * Nat.card ↥(K ⊓ Q))
    (hC : ∀ x ∈ H, (∀ q ∈ Q, x * q = q * x) → x ∈ Q) :
    Q ≤ K ∧ ∃ K₁ K₂ : Subgroup G, K₁ ⊔ K₂ = K ∧ K₁ ⊓ K₂ = A ⊓ B ∧
      K₁ ≤ centralizer (K₂ : Set G) ∧ Nonempty (↥K₁ ≃* SL(2, ZMod 3)) ∧
      Nonempty (↥K₂ ≃* SL(2, ZMod 3)) ∧
      ∀ w ∈ H, (∀ x ∈ K, w * x * w⁻¹ * x ∈ Q) →
        w ∈ normalizer (K₁ : Set G) ∧ w ∈ normalizer (K₂ : Set G) := by
  subst hQ
  have hQ32 : Nat.card ↥(A ⊔ B) = 32 := hcfg.card
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9K : 3 ^ 2 ∣ Nat.card K := by
    rw [hKcard]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨Y₀, hY₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 3 h9K
  set Y : Subgroup G := Y₀.map K.subtype with hY
  have hY9 : Nat.card Y = 9 := by
    rw [hY, Subgroup.card_map_of_injective K.subtype_injective, hY₀]
    norm_num
  have hYK : Y ≤ K := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hYodd : ∀ y ∈ Y, Odd (orderOf y) := by
    intro y hy
    have : orderOf y ∣ 9 := hY9 ▸ Subgroup.orderOf_dvd_natCard Y hy
    exact Odd.of_dvd_nat (by decide) this
  have hYN : ∀ y ∈ Y, y ∈ normalizer (A : Set G) ∧ y ∈ normalizer (B : Set G) := fun y hy =>
    hcfg.mem_normalizers_of_odd (hQnorm y (hKH (hYK hy))) (hYodd y hy)
  have hY1 : ∀ y ∈ Y, (∀ q ∈ A ⊔ B, q * y = y * q) → y = 1 := by
    intro y hy hq
    have hyQ : y ∈ A ⊔ B := hC y (hKH (hYK hy)) fun q hq' => (hq q hq').symm
    have h1 : orderOf y ∣ 9 := hY9 ▸ Subgroup.orderOf_dvd_natCard Y hy
    have h2 : orderOf y ∣ 32 := hQ32 ▸ Subgroup.orderOf_dvd_natCard (A ⊔ B) hyQ
    have h3 : orderOf y ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      simpa using this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  obtain ⟨y₁, hy₁Y, y₂, hy₂Y, hy₁3, hy₂3, hy₁B, hy₂A, hy₁A, hy₂B, hy₁₂⟩ :=
    hcfg.exists_pair hY9 hYN hYodd hY1
  have hy₁N : y₁ ∈ normalizer (A : Set G) := (hYN y₁ hy₁Y).1
  have hy₂N : y₂ ∈ normalizer (B : Set G) := (hYN y₂ hy₂Y).2
  obtain ⟨⟨ψ₁⟩, hA1⟩ := hcfg.J_sl hy₁3 hy₁N hy₁A
  obtain ⟨⟨ψ₂⟩, hB2⟩ := hcfg.symm.J_sl hy₂3 hy₂N hy₂B
  have hJ₁24 := hcfg.card_J hy₁3 hy₁N
  have hJ₂24 := hcfg.symm.card_J hy₂3 hy₂N
  have hAH : A ≤ H := le_sup_left.trans hQH
  have hBH : B ≤ H := le_sup_right.trans hQH
  have hy₁H : y₁ ∈ H := hKH (hYK hy₁Y)
  have hy₂H : y₂ ∈ H := hKH (hYK hy₂Y)
  have hAK : A ≤ K := by
    refine hA1.trans ((Subgroup.closure_le K).mpr ?_)
    rintro u ⟨huJ, hu3⟩
    have hJH : A ⊔ zpowers y₁ ≤ H := sup_le hAH (zpowers_le.mpr hy₁H)
    exact hKodd u (hJH huJ) (by rw [hu3]; decide)
  have hBK : B ≤ K := by
    refine hB2.trans ((Subgroup.closure_le K).mpr ?_)
    rintro u ⟨huJ, hu3⟩
    have hJH : B ⊔ zpowers y₂ ≤ H := sup_le hBH (zpowers_le.mpr hy₂H)
    exact hKodd u (hJH huJ) (by rw [hu3]; decide)
  have hJ₁K : A ⊔ zpowers y₁ ≤ K := sup_le hAK (zpowers_le.mpr (hYK hy₁Y))
  have hJ₂K : B ⊔ zpowers y₂ ≤ K := sup_le hBK (zpowers_le.mpr (hYK hy₂Y))
  have hcomm : A ⊔ zpowers y₁ ≤ centralizer ((B ⊔ zpowers y₂ : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le hcfg.symm.comm (zpowers_le.mpr ?_)
      exact Subgroup.mem_centralizer_iff.mpr fun a ha => (hy₂A a ha).symm
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff]
        refine zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun b hb => (hy₁B b hb).symm)
      · refine zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
        exact (Commute.zpow_left hy₁₂ k).eq
  have hinf : (A ⊔ zpowers y₁) ⊓ (B ⊔ zpowers y₂) = A ⊓ B := by
    apply le_antisymm
    · rintro x ⟨hx1, hx2⟩
      have hxc : ∀ m ∈ A, x * m = m * x := fun m hm => by
        have hx3 := (Subgroup.le_centralizer_iff.mp hcomm) hx2
        exact (Subgroup.mem_centralizer_iff.mp hx3 m (Subgroup.mem_sup_left hm)).symm
      rcases hcfg.J_centralizer hy₁3 hy₁N hy₁A hx1 hxc with rfl | rfl
      · exact one_mem _
      · exact (hcfg.mem_inf_iff _).mpr (Or.inr rfl)
    · exact le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans le_sup_left)
  have hnorm : B ⊔ zpowers y₂ ≤ normalizer ((A ⊔ zpowers y₁ : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _)
  have hcard := card_sup_mul_card_inf hnorm
  rw [hinf, hcfg.card_inf, hJ₁24, hJ₂24] at hcard
  have hsup : Nat.card ↥((A ⊔ zpowers y₁) ⊔ (B ⊔ zpowers y₂)) = 288 := by omega
  have hKle : Nat.card K ≤ 288 := by
    rw [hKcard]
    have : Nat.card ↥(K ⊓ (A ⊔ B)) ≤ 32 := hQ32 ▸ Subgroup.card_le_of_le inf_le_right
    omega
  have hKeq : (A ⊔ zpowers y₁) ⊔ (B ⊔ zpowers y₂) = K :=
    Subgroup.eq_of_le_of_card_ge (sup_le hJ₁K hJ₂K) (by omega)
  refine ⟨sup_le hAK hBK, A ⊔ zpowers y₁, B ⊔ zpowers y₂, hKeq, hinf, hcomm, ⟨ψ₁⟩, ⟨ψ₂⟩, ?_⟩
  intro w hwH hw
  have hwQ : ∀ q ∈ A ⊔ B, w * q * w⁻¹ ∈ A ⊔ B := hQnorm w hwH
  refine ⟨hcfg.mem_normalizer_J hwQ hy₁3 hy₁B hy₁A (hw y₁ (hYK hy₁Y)), ?_⟩
  refine hcfg.symm.mem_normalizer_J (by simpa only [sup_comm] using hwQ) hy₂3 hy₂A hy₂B ?_
  rw [sup_comm]
  exact hw y₂ (hYK hy₂Y)

end Cfg

end CFSG.Quasithin.H13.Q8SqE9
