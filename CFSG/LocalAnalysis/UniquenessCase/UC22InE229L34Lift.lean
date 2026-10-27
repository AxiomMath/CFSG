module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Torus
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5U3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.OrderPrimeConj
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs (isConj_of_natCard_eq_prime_of_sylow_cyclic)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_exists_conj_centralizer {Y X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hXc : Nat.card X = q)
    (hrank : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 Y)) ≤ 1) {T : Subgroup (Bar2 Y)}
    (hT : IsCyclic T) (hqT : q ∣ Nat.card T) :
    ∃ g : Bar2 Y, ∀ τ ∈ T, g * τ * g⁻¹ ∈ centralizer
      (((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) : Set (Bar2 Y)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI := hT
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqT
  have hZc : Nat.card (zpowers (x : Bar2 Y)) = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  obtain ⟨g, hg⟩ := isConj_of_natCard_eq_prime_of_sylow_cyclic
    (fun Q => RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one hq2 hrank Q) hZc
    (uc22ine229_card_map hXY hq hq2 hXc)
  refine ⟨g, fun τ hτ => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [← hg] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hc : (τ : Bar2 Y) * (x : Bar2 Y) ^ k = (x : Bar2 Y) ^ k * τ := by
    letI : CommGroup T := IsCyclic.commGroup
    have h : (⟨τ, hτ⟩ : T) * x = x * ⟨τ, hτ⟩ := mul_comm _ _
    have h' : Commute (τ : Bar2 Y) (x : Bar2 Y) := congrArg Subtype.val h
    exact h'.zpow_right k
  show g * (x : Bar2 Y) ^ k * g⁻¹ * (g * τ * g⁻¹) = g * τ * g⁻¹ * (g * (x : Bar2 Y) ^ k * g⁻¹)
  calc g * (x : Bar2 Y) ^ k * g⁻¹ * (g * τ * g⁻¹) = g * ((x : Bar2 Y) ^ k * τ) * g⁻¹ := by group
    _ = g * (τ * (x : Bar2 Y) ^ k) * g⁻¹ := by rw [hc]
    _ = g * τ * g⁻¹ * (g * (x : Bar2 Y) ^ k * g⁻¹) := by group

theorem uc22ine229_prime_dvd_of_dvd_three_mul {p a c : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpa : p ∣ a) (ha : a ∣ 3 * c) : p ∣ c :=
  ((Nat.Prime.dvd_mul hp).1 (hpa.trans ha)).resolve_left fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega

theorem uc22ine229_mk_mem_center_of_comm {Y : Subgroup G} {ρ : ↥Y}
    (h : ∀ y ∈ Y, (ρ : G) * y * (ρ : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 Y) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ρ ∈ center (Bar2 Y) := by
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ w
  obtain ⟨c, hc, hcy⟩ := h y y.2
  have hcc : c = ρ * y * ρ⁻¹ * y⁻¹ := Subtype.ext hcy
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (ρ * y * ρ⁻¹ * y⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (hcc ▸ hc)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)).symm

theorem uc22ine229_exists_prime_order_normalizer (hT : uc22pwTorusSU3)
    (hgr : GriessAllModelsStatement) {M Y : Subgroup G} (hY : Y ∈ calC M) {n : ℕ} (hn : 2 < n)
    (hX : IsSU3 (Bar2 Y) n) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hqn : q ∣ 2 ^ n - 1)
    {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrn : r ∣ 2 ^ n + 1) : ∃ ρ ∈ Y ⊓ normalizer (X : Set G), orderOf ρ = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq2 : q ≠ 2 := by omega
  have hrank := uc22ine229_pRank_le_one_of_isSU3 hX hq hq2
    (uc22ine229_not_dvd_two_pow_add_one hq hq2 hqn)
    (uc22ine229_not_dvd_card_center hgr hX hq hq2 hqn)
  obtain ⟨T, hTc, -, hTd⟩ := hT (Bar2 Y) hX.1 n hn hX
  have hsq : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [pow_mul', ← uc22pwsu3_sq_sub_one (by omega)]
  have hdvd : (2 ^ n - 1) * (2 ^ n + 1) ∣ 3 * Nat.card T :=
    hsq ▸ hTd.trans (Nat.mul_dvd_mul_left 3 (Subgroup.card_map_dvd T _))
  have hqT := uc22ine229_prime_dvd_of_dvd_three_mul hq (by omega) (Dvd.dvd.mul_right hqn _) hdvd
  have hrT := uc22ine229_prime_dvd_of_dvd_three_mul hr hr3 (Dvd.dvd.mul_left hrn _) hdvd
  obtain ⟨g, hg⟩ := uc22ine229_exists_conj_centralizer hXY hq hq2 hXc hrank hTc hqT
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' r hrT
  have hz := hg τ τ.2
  obtain ⟨y, hyN, hy⟩ := uc22ine229_exists_lift hXY hq hq2
    (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])) (Subgroup.centralizer_le_normalizer _ hz)
  have hzo : orderOf (g * (τ : Bar2 Y) * g⁻¹) = r := by
    rw [show g * (τ : Bar2 Y) * g⁻¹ = (MulAut.conj g).toMonoidHom τ from rfl,
      orderOf_injective _ (MulAut.conj g).injective, Subgroup.orderOf_coe, hτ]
  have hdy : r ∣ orderOf (y : G) := by
    rw [Subgroup.orderOf_coe, ← hzo, ← hy]
    exact orderOf_map_dvd _ _
  exact ⟨(y : G) ^ (orderOf (y : G) / r),
    pow_mem (show (y : G) ∈ Y ⊓ normalizer (X : Set G) from ⟨y.2, hyN⟩) _,
    orderOf_pow_orderOf_div (orderOf_pos _).ne' hdy⟩

theorem uc22ine229_exists_three_noncentral (hT : uc22pwTorusSU3) (hgr : GriessAllModelsStatement)
    {M Y : Subgroup G} (hY : Y ∈ calC M) {n : ℕ} (hn : 2 < n) (hX : IsSU3 (Bar2 Y) n)
    (h9 : 9 ∣ 2 ^ n + 1) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hqn : q ∣ 2 ^ n - 1)
    {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) :
    ∃ ρ ∈ Y ⊓ normalizer (X : Set G), IsPGroup 3 (Subgroup.zpowers ρ) ∧
      ∃ y ∈ Y, ρ * y * ρ⁻¹ * y⁻¹ ∉ pCoreOf 2 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : q ≠ 2 := by omega
  have hrank := uc22ine229_pRank_le_one_of_isSU3 hX hq hq2
    (uc22ine229_not_dvd_two_pow_add_one hq hq2 hqn)
    (uc22ine229_not_dvd_card_center hgr hX hq hq2 hqn)
  obtain ⟨T, hTc, -, hTd⟩ := hT (Bar2 Y) hX.1 n hn hX
  have hsq : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [pow_mul', ← uc22pwsu3_sq_sub_one (by omega)]
  rw [hsq] at hTd
  have hqT := uc22ine229_prime_dvd_of_dvd_three_mul hq (by omega) (Dvd.dvd.mul_right hqn _)
    (hTd.trans (Nat.mul_dvd_mul_left 3 (Subgroup.card_map_dvd T _)))
  have h3 : 3 ∣ Nat.card (T.map (QuotientGroup.mk' (center (Bar2 Y)))) := by
    have h9' := h9.trans ((dvd_mul_left _ _).trans hTd)
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨t, htT, htu⟩ := u.2
  have hu3 : orderOf (QuotientGroup.mk' (center (Bar2 Y)) t) = 3 := by
    rw [htu, Subgroup.orderOf_coe, hu]
  obtain ⟨g, hg⟩ := uc22ine229_exists_conj_centralizer hXY hq hq2 hXc hrank hTc hqT
  obtain ⟨y, hyN, hy⟩ := uc22ine229_exists_lift hXY hq hq2
    (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one]))
    (Subgroup.centralizer_le_normalizer _ (hg t htT))
  obtain ⟨b, m, hm, hordy⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hordy
    exact (orderOf_pos y).ne' hordy
  have hmy : m ∣ orderOf y := by
    rw [hordy]
    exact Dvd.intro_left _ rfl
  have hρo : orderOf (y ^ m) = 3 ^ b := by
    rw [orderOf_pow_of_dvd hm0 hmy, hordy, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  refine ⟨((y ^ m : ↥Y) : G), ⟨(y ^ m).2, pow_mem hyN m⟩,
    IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hρo]), ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : QuotientGroup.mk' (center (Bar2 Y))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (y ^ m)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (uc22ine229_mk_mem_center_of_comm (ρ := y ^ m) hcon)
  rw [map_pow, hy, conj_pow] at h1
  have hs : (QuotientGroup.mk' (center (Bar2 Y)) t) ^ m = 1 := by
    simpa using h1
  exact hm (hu3 ▸ orderOf_dvd_of_pow_eq_one hs)

end CFSG.LocalAnalysis.UniquenessCase.UC22
