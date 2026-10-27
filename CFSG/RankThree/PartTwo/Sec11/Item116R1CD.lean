module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1A
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CompThree
public import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

theorem pCore_inf_le_theta_of_bot (x : G) (y' : CAt x) (hy3 : y' ^ 3 = 1)
    (hbot : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer
      ({(QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt x)) y' : QAt x)} : Set (QAt x))) = ⊥) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({(y' : G)} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt x)) :=
    (solvable_prime_complement_core_characterization (H := CAt x) Nat.prime_three).2.2.1
  rw [inSubgroup_pCore_centralizer_inf x y']
  rintro _ ⟨p, hp, rfl⟩
  have hmap := map_pCore_two_centralizer_le (aschbacherSolvableCore 3 (CAt x)) h3 hy3
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt x))) hp)
  rw [hbot, Subgroup.mem_bot] at hmap
  have hp1 : p ∈ aschbacherSolvableCore 3 (CAt x) :=
    (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 (CAt x)) p).mp hmap
  unfold inSubgroup
  exact Subgroup.mem_map_of_mem _ hp1

open CFSG.Assembly.RankThreeEven (projSL)

section Certified

@[expose] def H1bAtCD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d → IsSurvivingCase L → KFAt L a →
        ∀ v ∈ inSubgroup twoFitting (thetaCent (c * d)),
          c * v * c⁻¹ * v⁻¹ ∈ inSubgroup (CFSG.pCore 2) (thetaCent (c * d))

@[expose] def CensusD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d → IsSurvivingCase L →
      ∀ J : Subgroup (Subgroup.centralizer ({c * d} : Set G) ⧸
          aschbacherSolvableCore 3 (Subgroup.centralizer ({c * d} : Set G))),
        CFSG.IsComponent J → ¬ 3 ∣ Nat.card J

end Certified

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

theorem cd_isKGroup {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} {d : G} (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) : CFSG.IsKGroup (QAt (c * d)) := by
  have hG : TheoremFourHyp G := h.toSec11StdLocal.toHyp81.toPartTwoStanding.toTheoremFourHyp
  have hcd1 : c * d ≠ 1 := by
    intro h1
    apply h.not_mem_zpowers
    have hd' : d = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hd']
    exact inv_mem (Subgroup.mem_zpowers c)
  have hCtop : Subgroup.centralizer ({c * d} : Set G) ≠ ⊤ :=
    CFSG.RankThree.PartTwo.Sec6.centralizer_ne_top_of_ne_one hG hcd1
  exact CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient
    (hG.sectionFourHyp hCtop).kGroup _

theorem cdQuot_of (hD : CensusD) (hL : ThreePrimeComponentsTwoCore) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d : G}
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hR1 : ResidueR1 G A c a d)
    (hS : IsSurvivingCase L) :
    ∀ y ∈ A, y ≠ 1 →
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c * d} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G)) ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c * d} : Set G)) := by
  intro y hyA hy1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcdA : c * d ∈ A := mul_mem h.mem_A h.d_mem
  have hyC : y ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hyA (c * d) hcdA)
  have hy3 : y ^ 3 = 1 := hAe.2 y hyA
  have h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt (c * d))) :=
    (solvable_prime_complement_core_characterization (H := CAt (c * d)) Nat.prime_three).2.2.1
  set y' : CAt (c * d) := ⟨y, hyC⟩ with hy'
  have hy'3 : y' ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hy'1 : y' ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
  have hqy3 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt (c * d))) y' :
      QAt (c * d)) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hy'3, map_one])
      (mk_ne_one_of_pow_three (aschbacherSolvableCore 3 (CAt (c * d))) h3 hy'3 hy'1)
  have hbot := hL (QAt (c * d)) (cd_isKGroup h hT) (aschbacherSolvableCore_quotient_eq_bot (CAt (c * d)))
    (hD G A c L a R Y d h hT hR1 hS) _ hqy3
  exact pCore_inf_le_theta_of_bot (c * d) y' hy'3 hbot

theorem twoStarAtCD_of_pieces (hH : H1bAtCD) (hD : CensusD) (hL : ThreePrimeComponentsTwoCore) :
    ResidueR1TwoStarCD := by
  intro G _ _ A c L a R Y d h hT hR1 hS hKF
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hEA : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  have h27 : Nat.card A = 3 ^ 3 := by rw [h.card_eq]; norm_num
  have hdA := h.d_mem
  have hcA := h.mem_A
  have haA := h.a_mem
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hd1 : d ≠ 1 := fun h1 => h.not_mem_zpowers (h1 ▸ Subgroup.one_mem _)
  have hclle : ∀ H : Subgroup G, c ∈ H → d ∈ H → a ∈ H → A ≤ H := by
    intro H hc hd ha
    rw [← h.closure_eq, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hc
    · exact hd
    · exact ha
  have hcd9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 hcA h.ne_one hdA
    h.not_mem_zpowers
  have haV : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro ha
    have hle := hclle (Subgroup.zpowers c ⊔ Subgroup.zpowers d)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)) ha
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hcd9] at this
    norm_num at this
  have haC : a ∉ Subgroup.zpowers c := fun ha => haV (Subgroup.mem_sup_left ha)
  have hcV9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 hcA h.ne_one haA haC
  have hcdA : c * d ∈ A := mul_mem hcA hdA
  have hcd1 : c * d ≠ 1 := by
    intro h1
    apply h.not_mem_zpowers
    have hd' : d = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hd']
    exact inv_mem (Subgroup.mem_zpowers c)
  have hcd3 : (c * d) ^ 3 = 1 := by
    rw [(Commute.mul_pow (show Commute c d from hcomm c hcA d hdA) 3), hc3, hd3, mul_one]
  have hVA : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr haA)
  have hcdV : c * d ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers a := by
    intro hV
    have hcV : c ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers a :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
    have hdV : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers a := by
      have := mul_mem (inv_mem hcV) hV
      simpa using this
    have hle := hclle (Subgroup.zpowers c ⊔ Subgroup.zpowers a) hcV hdV
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hcV9] at this
    norm_num at this
  have hcnot : c ∉ Subgroup.zpowers (c * d) := by
    intro hc
    have hz := TheoremO.zpowers_eq_of_mem_of_ne_one hcd3 hc h.ne_one
    apply h.not_mem_zpowers
    have hcd : c * d ∈ Subgroup.zpowers c := by rw [hz]; exact Subgroup.mem_zpowers (c * d)
    have := mul_mem (inv_mem (Subgroup.mem_zpowers c)) hcd
    simpa using this
  have hQ := cdQuot_of hD hL h hT hR1 hS
  have hPnorm : ∀ y ∈ A, A ≤ Subgroup.normalizer
      ((inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c * d} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) : Subgroup G) : Set G) := by
    intro y hyA
    refine le_trans ?_ (compJ1_le_normalizer_inSubgroup_pCore 2
      (Subgroup.centralizer ({c * d} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)))
    intro u hu
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hcomm u hu (c * d) hcdA),
        Subgroup.mem_centralizer_singleton_iff.mpr (hcomm u hu y hyA)⟩
  refine TwoStarProof.twoStarConditionAt_of_theta hAe h.card_eq hcdA hcd1
    (V := Subgroup.zpowers c ⊔ Subgroup.zpowers a) (by rw [hcV9]; norm_num) hVA hcdV h.mem_A
    hcnot ?_ ?_ ?_
  · exact hH G A c L a R Y d h hT hR1 hS hKF
  · intro y hyA hyz
    have hy1 : y ≠ 1 := fun h1 => hyz (h1 ▸ Subgroup.one_mem _)
    refine le_trans ?_ (hQ y hyA hy1)
    rw [Subgroup.commutator_le]
    intro p hp α hα
    have hα' : α * p⁻¹ * α⁻¹ ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c * d} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) :=
      (Subgroup.mem_normalizer_iff.mp (hPnorm y hyA hα) p⁻¹).mp (inv_mem hp)
    have : p * (α * p⁻¹ * α⁻¹) = p * α * p⁻¹ * α⁻¹ := by group
    rw [commutatorElement_def, ← this]
    exact mul_mem hp hα'
  · intro u hu
    have haz : a ∉ Subgroup.zpowers (c * d) := by
      intro ha
      apply haV
      have hz : Subgroup.zpowers (c * d) ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
        rw [Subgroup.zpowers_le]
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
      exact hz ha
    exact hQ a haA h.a_ne_one (hu a haA haz)

theorem twoStarAtCD_of_suzuki (hH : H1bAtCD) (hD : CensusD) (hK : SuzukiAutFacts) :
    ResidueR1TwoStarCD :=
  twoStarAtCD_of_pieces hH hD (threePrimeComponentsTwoCore_of hK)

end Certified

end CFSG.RankThree.PartTwo.Sec11
