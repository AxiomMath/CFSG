module

public import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

section General

variable {G : Type} [Group G] [Finite G]

theorem sup_eq_of_isHall_isSylow {X D S : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D X)
    (hS : IsSylowTwoOf S X) : D ⊔ S = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDX, hDodd, k, hk⟩ := hD
  obtain ⟨hSX, hS2, hSodd⟩ := hS
  have hle : D ⊔ S ≤ X := sup_le hDX hSX
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hS2
  have hX1 : Nat.card X = 2 ^ k * Nat.card D := by
    rw [← hk, ← Subgroup.relIndex_mul_card D X, inf_eq_left.mpr hDX]
  have hcS : Nat.card (S.subgroupOf X) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  have hX2 : Nat.card X = Nat.card S * (S.subgroupOf X).index := by
    rw [← hcS]
    exact (Subgroup.card_mul_index (S.subgroupOf X)).symm
  have hidx : Odd (S.subgroupOf X).index := by
    rcases Nat.even_or_odd (S.subgroupOf X).index with he | ho
    · exact absurd (even_iff_two_dvd.mp he) hSodd
    · exact ho
  have hkS : 2 ^ k ∣ Nat.card S := by
    have h1 : 2 ^ k ∣ Nat.card S * (S.subgroupOf X).index := by
      rw [← hX2, hX1]
      exact dvd_mul_right _ _
    exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hidx)).dvd_of_dvd_mul_right h1
  have hcop : Nat.Coprime (Nat.card D) (Nat.card S) := by
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hDodd)
  have hdvd : Nat.card D * Nat.card S ∣ Nat.card ↥(D ⊔ S) :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
  have hpos : 0 < Nat.card ↥(D ⊔ S) := Nat.card_pos
  apply Subgroup.eq_of_le_of_card_ge hle
  calc Nat.card X = 2 ^ k * Nat.card D := hX1
    _ ≤ Nat.card S * Nat.card D :=
        Nat.mul_le_mul_right _ (Nat.le_of_dvd (Nat.card_pos) hkS)
    _ = Nat.card D * Nat.card S := mul_comm _ _
    _ ≤ Nat.card ↥(D ⊔ S) := Nat.le_of_dvd hpos hdvd

omit [Finite G] in
theorem oTwoUpper_sup_eq_of_isPGroup {B T : Subgroup G} (hT : IsPGroup 2 T)
    (hTB : T ≤ Subgroup.normalizer (B : Set G)) : oTwoUpper (B ⊔ T) = oTwoUpper B := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, hodd⟩
    have hx' : x ∈ ((B : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left B T hTB]
      exact hx
    obtain ⟨b, hb, t, ht, rfl⟩ := hx'
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨b', hb', he⟩ := pow_mul_mem_of_mem_normalizer hb (hTB ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hcop : Nat.Coprime (2 ^ a) (orderOf (b * t)) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
    have hmem : b * t ∈ Subgroup.zpowers ((b * t) ^ 2 ^ a) := A4.mem_zpowers_pow_of_coprime hcop
    have hB : b * t ∈ B := by
      rw [he] at hmem
      exact (Subgroup.zpowers_le.mpr hb') hmem
    exact mem_oTwoUpper_of_odd hB hodd
  · exact oTwoUpper_mono le_sup_left

end General

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem isUniqueM (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) : IsUniqueM (L ⊔ T) M := by
  obtain ⟨⟨-, -, huniq⟩, -⟩ :=
    (h331 G T h.simple h.nonabelian h.qtke h.sylow).2 L h.maximal h.isQuasisimple
  rw [h.conjClosure_eq] at huniq
  have hM : M = Subgroup.normalizer (L : Set G) := huniq M h.maxTwoLocal h.sup_le_M
  refine ⟨⟨h.maxTwoLocal, h.sup_le_M⟩, fun M' hM' => ?_⟩
  rw [huniq M' hM'.1 hM'.2, hM]

theorem not_le_of_isHStar (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) {H : Subgroup G}
    (hH : IsHStar T M H) : ¬ L ≤ H := by
  intro hLH
  have h1 := pCoreOf_sup_eq_bot_of_isUniqueM (h.isUniqueM h331) hH.2.1
  have h2 : (L ⊔ T) ⊔ H = H := sup_eq_right.mpr (sup_le hLH hH.1.1)
  rw [h2] at h1
  exact hH.1.2 h1

theorem inf_le_borel_of_isHStar (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) {H : Subgroup G} (hH : IsHStar T M H) : H ⊓ L ≤ borelL T L := by
  have hRA := h.rankOneAt hR
  have hne : H ⊓ L ≠ L := fun heq =>
    h.not_le_of_isHStar h331 hH (heq.symm.le.trans inf_le_left)
  exact le_inf inf_le_right
    (hRA.unique_max (H ⊓ L) (inf_le_inf_right L hH.1.1) inf_le_right hne)

theorem pCoreOf_inf_eq (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    {H : Subgroup G} (hH : IsHStar T M H) : pCoreOf 2 (H ⊓ L) = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hS le_sup_left h.sup_le_normalizer
  have hTHL : T ⊓ L ≤ H ⊓ L := inf_le_inf_right L hH.1.1
  have hSHL : IsSylowTwoOf (T ⊓ L) (H ⊓ L) := A4.isSylowTwoOf_mono hSL hTHL inf_le_right
  apply le_antisymm (F7.isSylowTwoOf_pCoreOf_le hSHL)
  exact le_pCoreOf_of_le_normalizer 2 hTHL
    ((h.inf_le_borel_of_isHStar h331 hR hH).trans inf_le_right) hSL.2.1

theorem inf_le_normalizer_inf (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) {H : Subgroup G} (hH : IsHStar T M H) :
    H ⊓ M ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have h1 : H ⊓ M ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans Subgroup.le_normalizer) (inf_le_right.trans h.normal)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have h2 := h1.trans (normalizer_le_normalizer_pCoreOf 2 (H ⊓ L))
  rwa [h.pCoreOf_inf_eq h331 hR hH] at h2

theorem inf_le_normalizer_borel (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) {H : Subgroup G} (hH : IsHStar T M H) :
    H ⊓ M ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := by
  have h1 : H ⊓ M ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans h.normal
  have h2 : H ⊓ M ≤ Subgroup.normalizer
      ((Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    (h.inf_le_normalizer_inf h331 hR hH).trans Subgroup.le_normalizer
  exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem lemma_5_1_5_one (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    {H D : Subgroup G} (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    H ⊓ M ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
      H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (D ⊔ T) : Set G) := by
  refine ⟨h.inf_le_normalizer_inf h331 hR hH, ?_⟩
  have hS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hS le_sup_left h.sup_le_normalizer
  have hSB : IsSylowTwoOf (T ⊓ L) (borelL T L) :=
    A4.isSylowTwoOf_mono hSL (inf_le_borel T L) inf_le_left
  have hB : D ⊔ (T ⊓ L) = borelL T L := sup_eq_of_isHall_isSylow hD hSB
  have hDT : D ⊔ T = borelL T L ⊔ T := by
    apply le_antisymm (sup_le_sup_right hD.1 T)
    rw [← hB]
    exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
  rw [hDT, oTwoUpper_sup_eq_of_isPGroup h.sylow.1 h.T_le_normalizer_borel]
  exact (h.inf_le_normalizer_borel h331 hR hH).trans (normalizer_le_normalizer_oTwoUpper _)

end Hyp5_0_1

end CFSG.Quasithin.H13
