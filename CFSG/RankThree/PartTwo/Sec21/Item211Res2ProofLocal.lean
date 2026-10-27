module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofIrred
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

structure Config2130 (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G)
    (L : Subgroup G) : Prop where
  pair : Sec21Pair G A E U c L
  not_mem : c ∉ L
  card_eq : Nat.card A = 3 * Nat.card (A ⊓ L : Subgroup G)
  nine_le : 9 ≤ Nat.card (A ⊓ L : Subgroup G)
  irred : ∀ X : Subgroup G, X ≤ A ⊓ L →
    L ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = A ⊓ L
  normal : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G)
  full : ∀ b ∈ A ⊓ L, ∃ w ∈ Subgroup.normalizer (A : Set G),
    (∀ x ∈ A ⊓ L, w * x * w⁻¹ = x) ∧ w * c * w⁻¹ = c * b

structure Choice2130 {G : Type} [Group G] [Finite G] (A E : Subgroup G) (c : G) (L : Subgroup G)
    (b : G) (U₀ Y : Subgroup G) : Prop where
  b_mem : b ∈ A ⊓ L
  b_ne_one : b ≠ 1
  u_mem : U₀ ∈ fourGroupsMinus E
  u_le : U₀ ≤ L
  b_comm : U₀ ≤ Subgroup.centralizer ({b} : Set G)
  y_mem : Y ∈ lZeroStarAt A b
  u_norm : U₀ ≤ Subgroup.normalizer (Y : Set G)
  y_comm_u : ⁅Y, U₀⁆ = Y
  c_norm : c ∈ Subgroup.normalizer (Y : Set G)
  y_comm_c : ⁅Y, Subgroup.zpowers c⁆ = Y
  three_norm : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer ({b} : Set G) →
    S ≤ Subgroup.normalizer (Y : Set G)
  sec_cent : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
    (Subgroup.zpowers b : Set G)

@[expose] def Item2130LocalThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2130 G A E U c L → 27 ≤ Nat.card (A ⊓ L : Subgroup G) → False

@[expose] def Item2130LocalChoice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 →
      ∃ (b : G) (U₀ Y : Subgroup G), Choice2130 A E c L b U₀ Y

@[expose] def Item2130LocalON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      A ≤ Y → False

@[expose] def Item2130LocalTypes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ¬ A ≤ Y ⊔ Subgroup.zpowers b →
        c ∈ Y ∨ (c ∈ Y ⊔ Sec4.thetaQuotCentralizer Y ∧ ¬ A ≤ Y ⊔ Sec4.thetaQuotCentralizer Y)

namespace Item211Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem Config2130.eq_nine_or_le {A E U L : Subgroup G} {c : G} (h : Config2130 G A E U c L) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∨ 27 ≤ Nat.card (A ⊓ L : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := h.pair.mem_S.1.1
  have hB : IsPGroup 3 (A ⊓ L : Subgroup G) := fun g =>
    ⟨1, Subtype.ext (by simpa using hAe.2 _ (Subgroup.mem_inf.mp g.2).1)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
  have h9 := h.nine_le
  rw [hk] at h9 ⊢
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · left
    have h1 : 3 ^ 2 ≤ 3 ^ k := by simpa using h9
    have hk2 : k = 2 := by
      have h2 : 2 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
      omega
    rw [hk2]
    norm_num
  · right
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3

theorem exists_pow_conj_of_isPGroup {B : Subgroup G} {c w b' : G} (hBe : ∀ x ∈ B, x ^ 3 = 1)
    (hb' : b' ∈ B) (hwB : ∀ x ∈ B, w * x * w⁻¹ = x) (hwc : w * c * w⁻¹ = c * b') :
    ∃ k : ℕ, IsPGroup 3 (Subgroup.zpowers (w ^ k)) ∧ w ^ k * c * (w ^ k)⁻¹ = c * b' := by
  have hpow : ∀ j : ℕ, w ^ j * c * (w ^ j)⁻¹ = c * b' ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hb'j : w * b' ^ j * w⁻¹ = b' ^ j := hwB _ (B.pow_mem hb' j)
      calc w ^ (j + 1) * c * (w ^ (j + 1))⁻¹ = w * (w ^ j * c * (w ^ j)⁻¹) * w⁻¹ := by group
        _ = w * (c * b' ^ j) * w⁻¹ := by rw [ih]
        _ = (w * c * w⁻¹) * (w * b' ^ j * w⁻¹) := by group
        _ = c * b' ^ (j + 1) := by rw [hwc, hb'j, pow_succ', mul_assoc]
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' 3 (by norm_num)
  have hcop : m.Coprime (orderOf b') := by
    have h3 : orderOf b' ∣ 3 := orderOf_dvd_of_pow_eq_one (hBe b' hb')
    exact Nat.Coprime.coprime_dvd_right h3
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm
  obtain ⟨k', hk'⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨m * k', ?_, ?_⟩
  · have h1 : (w ^ (m * k')) ^ (3 ^ a) = 1 := by
      rw [← pow_mul, show m * k' * 3 ^ a = (3 ^ a * m) * k' by ring, pow_mul, ← hn,
        pow_orderOf_eq_one, one_pow]
    refine IsPGroup.of_card_dvd_pow (n := a) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one h1
  · rw [hpow, pow_mul, hk']

omit [Finite G] in
theorem pow_conj_eq_of_conj_eq {B : Subgroup G} {w : G} (hwB : ∀ x ∈ B, w * x * w⁻¹ = x)
    (j : ℕ) : ∀ x ∈ B, w ^ j * x * (w ^ j)⁻¹ = x := by
  intro x hx
  induction j with
  | zero => simp
  | succ j ih =>
    calc w ^ (j + 1) * x * (w ^ (j + 1))⁻¹ = w * (w ^ j * x * (w ^ j)⁻¹) * w⁻¹ := by group
      _ = x := by rw [ih, hwB x hx]

theorem Choice2130.exists_conj {A E U L : Subgroup G} {c b : G} {U₀ Y : Subgroup G}
    (hcfg : Config2130 G A E U c L) (hC : Choice2130 A E c L b U₀ Y) {b' : G}
    (hb' : b' ∈ A ⊓ L) :
    ∃ w ∈ Subgroup.normalizer (Y : Set G), (∀ x ∈ A ⊓ L, w * x * w⁻¹ = x) ∧
      w * c * w⁻¹ = c * b' := by
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hBe : ∀ x ∈ A ⊓ L, x ^ 3 = 1 := fun x hx => hAe.2 x hx.1
  obtain ⟨w, -, hwB, hwc⟩ := hcfg.full b' hb'
  obtain ⟨k, hk3, hkc⟩ := exists_pow_conj_of_isPGroup hBe hb' hwB hwc
  have hwkB := pow_conj_eq_of_conj_eq hwB k
  have hle : Subgroup.zpowers (w ^ k) ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hwkB b hC.b_mem
    calc w ^ k * b = w ^ k * b * (w ^ k)⁻¹ * w ^ k := by group
      _ = b * w ^ k := by rw [h1]
  exact ⟨w ^ k, hC.three_norm _ hk3 hle (Subgroup.mem_zpowers _), hwkB, hkc⟩

theorem le_of_forall_conj {A E U L : Subgroup G} {c : G} (hcfg : Config2130 G A E U c L)
    {K : Subgroup G} (hcK : c ∈ K)
    (hK : ∀ b' ∈ A ⊓ L, ∃ w ∈ Subgroup.normalizer (K : Set G), w * c * w⁻¹ = c * b') :
    A ≤ K := by
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Item2130Proof.eq_zpowers_sup hcA inf_le_left (fun h => hcfg.not_mem h.2) hcfg.card_eq
  rw [hAB]
  refine sup_le (Subgroup.zpowers_le.mpr hcK) ?_
  intro b' hb'
  obtain ⟨w, hw, hwc⟩ := hK b' hb'
  have h1 : w * c * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hw c).mp hcK
  have h2 : b' = c⁻¹ * (w * c * w⁻¹) := by rw [hwc]; group
  rw [h2]
  exact K.mul_mem (K.inv_mem hcK) h1

theorem Choice2130.le_of_le_sup {A E U L : Subgroup G} {c b : G} {U₀ Y : Subgroup G}
    (hcfg : Config2130 G A E U c L) (hC : Choice2130 A E c L b U₀ Y)
    (hAY : A ≤ Y ⊔ Subgroup.zpowers b) : A ≤ Y := by
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hYb : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A b hC.y_mem)
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYb hy)
  have hcY' : c ∈ ((Y ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := hAY hcA
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y _ hbN] at hcY'
  obtain ⟨y, hy, z, hz, hyz⟩ := hcY'
  have hzB : z ∈ A ⊓ L := (Subgroup.zpowers_le.mpr hC.b_mem) hz
  have hzc : ∀ y' ∈ Y, z * y' = y' * z := by
    intro y' hy'
    obtain ⟨n, rfl⟩ := hz
    have hc : Commute b y' := (Subgroup.mem_centralizer_singleton_iff.mp (hYb hy')).symm
    exact (Commute.zpow_left hc n).eq
  have hBY : A ⊓ L ≤ Y := by
    intro b' hb'
    obtain ⟨w, hwY, hwB, hwc⟩ := Choice2130.exists_conj hcfg hC hb'
    have hwz : w * z * w⁻¹ = z := hwB z hzB
    have hwy : w * y * w⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hwY y).mp hy
    have hm : y⁻¹ * (w * y * w⁻¹) ∈ Y := Y.mul_mem (Y.inv_mem hy) hwy
    have hcomm := hzc _ hm
    have h1 : w * c * w⁻¹ = (w * y * w⁻¹) * z := by
      rw [← hyz]
      calc w * (y * z) * w⁻¹ = (w * y * w⁻¹) * (w * z * w⁻¹) := by group
        _ = (w * y * w⁻¹) * z := by rw [hwz]
    have h2 : b' = c⁻¹ * (w * c * w⁻¹) := by rw [hwc]; group
    have h3 : b' = y⁻¹ * (w * y * w⁻¹) := by
      rw [h2, h1, ← hyz]
      calc (y * z)⁻¹ * (w * y * w⁻¹ * z) = z⁻¹ * ((y⁻¹ * (w * y * w⁻¹)) * z) := by group
        _ = z⁻¹ * (z * (y⁻¹ * (w * y * w⁻¹))) := by rw [← hcomm]
        _ = y⁻¹ * (w * y * w⁻¹) := by group
    rw [h3]
    exact hm
  have hcY : c ∈ Y := hyz ▸ Y.mul_mem hy (hBY hzB)
  exact le_of_forall_conj hcfg hcY fun b' hb' => by
    obtain ⟨w, hw, -, hwc⟩ := Choice2130.exists_conj hcfg hC hb'
    exact ⟨w, hw, hwc⟩

theorem normalizer_le_normalizer_thetaQuotCentralizer (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((Sec4.thetaQuotCentralizer Y : Subgroup G) : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨x', hx', rfl⟩ := hx
  refine ⟨⟨g, hg⟩ * x' * (⟨g, hg⟩ : Subgroup.normalizer (Y : Set G))⁻¹, ?_, rfl⟩
  exact (MonoidHom.normal_ker _).conj_mem x' hx' ⟨g, hg⟩

end Item211Res2Proof

open Item211Res2Proof

theorem item2130Local_of (h3 : Item2130LocalThree) (hch : Item2130LocalChoice)
    (hON : Item2130LocalON) (hT : Item2130LocalTypes) : Item2130Local := by
  intro G _ _ A E U c L hpair hcL hcard hB9 hirr hWB hfull
  have hcfg : Config2130 G A E U c L := ⟨hpair, hcL, hcard, hB9, hirr, hWB, hfull⟩
  rcases Config2130.eq_nine_or_le hcfg with h9 | h27
  · obtain ⟨b, U₀, Y, hC⟩ := hch G A E U c L hcfg h9
    by_cases hAY : A ≤ Y ⊔ Subgroup.zpowers b
    · exact hON G A E U c L b U₀ Y hcfg h9 hC (Choice2130.le_of_le_sup hcfg hC hAY)
    · rcases hT G A E U c L b U₀ Y hcfg h9 hC hAY with hcY | ⟨hcK, hAK⟩
      ·
        refine hAY ((le_of_forall_conj hcfg hcY fun b' hb' => ?_).trans le_sup_left)
        obtain ⟨w, hw, -, hwc⟩ := Choice2130.exists_conj hcfg hC hb'
        exact ⟨w, hw, hwc⟩
      ·
        refine hAK (le_of_forall_conj hcfg hcK fun b' hb' => ?_)
        obtain ⟨w, hw, -, hwc⟩ := Choice2130.exists_conj hcfg hC hb'
        exact ⟨w, Subgroup.inf_normalizer_le_normalizer_sup _ _
          ⟨hw, normalizer_le_normalizer_thetaQuotCentralizer Y hw⟩, hwc⟩
  · exact h3 G A E U c L hcfg h27

end CFSG.RankThree.PartTwo.Sec21
