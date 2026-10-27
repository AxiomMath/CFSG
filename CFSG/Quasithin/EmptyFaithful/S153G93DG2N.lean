module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.Background.SmithB42G2Nat
public import CFSG.Quasithin.Background.B4L3Inv

public section

namespace CFSG.Quasithin.S153G93D.G2N

open CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

section Fixed

variable {K : Type} [Field K] [CharP K 2] [Finite K] {n : ℕ} {W : Type} [CommGroup W]
  {H : Subgroup (MulAut W)} {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem card_fixV_le_of_mem (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hf : IsCoord (lmG K) H ⊥ π f) {a : MulAut W} (haH : a ∈ H) (ha1 : a ≠ 1)
    (ha2 : a ^ 2 = 1) : Nat.card (fixV (Subgroup.zpowers a)) ≤ Nat.card K ^ 4 := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (two_lt_card hK hn)
  have hA : IsElemAbelian2 (Subgroup.zpowers a) := isElemAbelian2_zpowers ha2
  have hAH : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.mpr haH
  obtain ⟨γ, hγ⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨a, haH⟩
  have hγA : γ ∈ ((Subgroup.zpowers a).subgroupOf H).comap (rhoG hc0 hc1 π) := by
    rw [Subgroup.mem_comap, hγ, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers a
  have hγ2 : γ * γ = 1 := comap_rhoG_mul_self hc0 hc1 hf hA γ hγA
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [map_one] at hγ
    exact ha1 (congrArg Subtype.val hγ).symm
  have hle : (fixSub (((Subgroup.zpowers a).subgroupOf H).comap
      (rhoG hc0 hc1 π))).toAddSubgroup ≤ fixQ γ := fun x hx => mem_fixQ.mpr (hx γ hγA)
  rw [card_fixV_eq_fixSub hc0 hc1 hf hAH]
  exact (AddSubgroup.card_le_of_le hle).trans (card_fixQ_le hγ2 hγ1)

theorem card_fixV_le_of_not_mem [Finite W] (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hf : IsCoord (lmG K) H ⊥ π f) {a : MulAut W}
    (haN : a ∈ Subgroup.normalizer (H : Set (MulAut W))) (haH : a ∉ H) (ha2 : a ^ 2 = 1) :
    Nat.card (fixV (Subgroup.zpowers a)) ≤ Nat.card K ^ 3 := by
  have hA : IsElemAbelian2 (Subgroup.zpowers a) := isElemAbelian2_zpowers ha2
  have hAN : Subgroup.zpowers a ≤ Subgroup.normalizer (H : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr haN
  have hsq := card_fixV_sq_le hK hn hf hAN hA (Subgroup.mem_zpowers a) haH
  have hle : Nat.card (fixV (Subgroup.zpowers a ⊓ H)) ≤ Nat.card W :=
    (Subgroup.card_le_of_le (le_top : fixV (Subgroup.zpowers a ⊓ H) ≤ ⊤)).trans
      (by rw [Subgroup.card_top])
  rw [card_W hf] at hle
  have h6 : Nat.card (fixV (Subgroup.zpowers a)) ^ 2 ≤ (Nat.card K ^ 3) ^ 2 := by
    rw [← pow_mul]
    exact hsq.trans hle
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h6

theorem card_fixV_le_four [Finite W] (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hf : IsCoord (lmG K) H ⊥ π f) {a : MulAut W}
    (haN : a ∈ Subgroup.normalizer (H : Set (MulAut W))) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Nat.card (fixV (Subgroup.zpowers a)) ≤ Nat.card K ^ 4 := by
  by_cases haH : a ∈ H
  · exact card_fixV_le_of_mem hK hn hf haH ha1 ha2
  · refine (card_fixV_le_of_not_mem hK hn hf haN haH ha2).trans ?_
    have hq : 0 < Nat.card K := by
      have := two_lt_card hK hn
      omega
    exact Nat.pow_le_pow_right hq (by norm_num)

theorem sq_le_card_commV [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) (hf : IsCoord (lmG K) H ⊥ π f) {a : MulAut W}
    (haN : a ∈ Subgroup.normalizer (H : Set (MulAut W))) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Nat.card K ^ 2 ≤ Nat.card (commV (Subgroup.zpowers a)) := by
  have hcard := card_commV_mul_card_fixV hW a
  rw [card_W hf] at hcard
  have h4 := card_fixV_le_four hK hn hf haN ha1 ha2
  have hpos : 0 < Nat.card K ^ 4 := by
    have := two_lt_card hK hn
    positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card K ^ 2 * Nat.card K ^ 4 = Nat.card K ^ 6 := by ring
    _ = Nat.card (commV (Subgroup.zpowers a)) * Nat.card (fixV (Subgroup.zpowers a)) := hcard.symm
    _ ≤ Nat.card (commV (Subgroup.zpowers a)) * Nat.card K ^ 4 := Nat.mul_le_mul_left _ h4

end Fixed

theorem mem_normalizer_of_involution {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {a : MulAut W} (haN : ∀ k ∈ L, a * k * a⁻¹ ∈ L) (ha2 : a ^ 2 = 1) :
    a ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => haN k hk, fun hk => ?_⟩
  have h1 := haN _ hk
  have e : a * (a * k * a⁻¹) * a⁻¹ = k := by
    rw [hinv]
    calc a * (a * k * a) * a = (a * a) * k * (a * a) := by group
      _ = k := by rw [haa, one_mul, mul_one]
  rwa [e] at h1

theorem sq_le_card_commV_of_g2Natural {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {n : ℕ} (hn : 2 ≤ n)
    (hL : G2Natural L ⊤ ⊥ n) {a : MulAut W} (haN : ∀ k ∈ L, a * k * a⁻¹ ∈ L) (ha1 : a ≠ 1)
    (ha2 : a ^ 2 = 1) : (2 ^ n) ^ 2 ≤ Nat.card (commV (Subgroup.zpowers a)) := by
  obtain ⟨K, _, _, hK, hreal⟩ := hL
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (two_lt_card hK hn)
  have heq : ⁅quasithinG2 K, quasithinG2 K⁆ = quasithinG2 K :=
    (g2Derived_eq hc0 hc1).trans
      CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup.symm
  have hreal' : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes L ⊤ ⊥ := by
    rw [heq]
    exact hreal
  obtain ⟨π, hπ⟩ := hreal'
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  have h := sq_le_card_commV hW hK hn hf (mem_normalizer_of_involution haN ha2) ha1 ha2
  rwa [hK] at h

theorem oneG2_holds : OneG2 := by
  intro W _ _ G₀ K S a z h hG2
  obtain ⟨n, hn, hK⟩ := hG2
  have h1 := sq_le_card_commV_of_g2Natural h.exp hn hK h.aN h.a1 h.a2
  rw [h.rk] at h1
  have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : (2 ^ 2) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2 2
  omega

end CFSG.Quasithin.S153G93D.G2N
