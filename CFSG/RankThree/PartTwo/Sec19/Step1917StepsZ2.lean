module

import CFSG.RankThree.PartTwo.Sec19.Step1917StepsBasic
import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped Pointwise

@[expose] def Step1917Z2KFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q T : Subgroup G) (z : G),
    Group.IsPerfect L →
    (IsLThreePi (L ⧸ CFSG.pCore 2 L) ∨
      Nonempty (L ⧸ CFSG.pCore 2 L ≃* CFSG.Blueprint.NativeSporadic.M12)) →
    IsPGroup 3 Q → Q ≤ Subgroup.normalizer (L : Set G) → (∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) →
    CFSG.Open.pRank 3 (Q ⊔ L) ≤ 3 →
    IsSylowOf 3 T (Q ⊔ L) → Q ≤ T → z ∈ L → z ∈ T → z ≠ 1 → (∀ t ∈ T, t * z = z * t) →
    ∃ P : Subgroup G, P ≤ Q ⊔ L ∧ IsPGroup 3 P ∧ ∃ hzP : z ∈ P,
      (⟨z, hzP⟩ : P) ∈ Subgroup.upperCentralSeries P 2 ∧ (⟨z, hzP⟩ : P) ∉ Subgroup.center P

@[expose] def Step1917Z2W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → L ≤ M → ∀ d ∈ A ⊓ E, d ∉ Subgroup.zpowers c →
      ∃ P : Subgroup G, P ≤ E ⊔ A ⊔ L ∧ IsPGroup 3 P ∧ ∃ hdP : d ∈ P,
        (⟨d, hdP⟩ : P) ∈ Subgroup.upperCentralSeries P 2 ∧ (⟨d, hdP⟩ : P) ∉ Subgroup.center P

namespace Step1917Steps

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_center_iff_of_mem {P : Subgroup G} {x : G} (hx : x ∈ P) :
    (⟨x, hx⟩ : P) ∈ Subgroup.center P ↔ ∀ p ∈ P, p * x = x * p := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h p hp
    exact congrArg Subtype.val (h ⟨p, hp⟩)
  · intro h p
    exact Subtype.ext (h p p.2)

omit [Finite G] in
theorem mem_upperCentralSeries_two_iff_of_mem {P : Subgroup G} {x : G} (hx : x ∈ P) :
    (⟨x, hx⟩ : P) ∈ Subgroup.upperCentralSeries P 2 ↔
      ∀ p ∈ P, ∀ q ∈ P, q * (x * p * x⁻¹ * p⁻¹) = (x * p * x⁻¹ * p⁻¹) * q := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
    Subgroup.upperCentralSeries_one]
  constructor
  · intro h p hp q hq
    have h1 := (Subgroup.mem_center_iff.mp (h ⟨p, hp⟩)) ⟨q, hq⟩
    exact congrArg Subtype.val h1
  · intro h p
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (h p p.2 q q.2)

theorem exists_of_central {P : Subgroup G} (hP : IsPGroup 3 P) {c : G}
    (hc3 : IsPGroup 3 (Subgroup.zpowers c)) (hcP : ∀ p ∈ P, p * c = c * p) {z : G}
    (hzP : z ∈ P) (hz2 : (⟨z, hzP⟩ : P) ∈ Subgroup.upperCentralSeries P 2)
    (hzZ : (⟨z, hzP⟩ : P) ∉ Subgroup.center P) (hz3 : z ^ 3 = 1) {d : G}
    (hd : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers z) (hdc : d ∉ Subgroup.zpowers c) :
    ∃ hdP : d ∈ P ⊔ Subgroup.zpowers c,
      IsPGroup 3 (P ⊔ Subgroup.zpowers c : Subgroup G) ∧
      (⟨d, hdP⟩ : ↥(P ⊔ Subgroup.zpowers c)) ∈
        Subgroup.upperCentralSeries ↥(P ⊔ Subgroup.zpowers c) 2 ∧
      (⟨d, hdP⟩ : ↥(P ⊔ Subgroup.zpowers c)) ∉ Subgroup.center ↥(P ⊔ Subgroup.zpowers c) := by
  set P' := P ⊔ Subgroup.zpowers c with hP'
  have hcC : P ≤ Subgroup.centralizer ({c} : Set G) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcP p hp)
  have hZc : Subgroup.zpowers c ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcent : ∀ x ∈ P', x * c = c * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (sup_le hcC hZc hx)
  have hPN : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hcC.trans (by
      rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
      exact Subgroup.centralizer_le_normalizer _)
  have hP'3 : IsPGroup 3 P' := hP.to_sup_of_normal_right' hc3 hPN
  have hPP' : P ≤ P' := le_sup_left
  have hcP' : c ∈ P' := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  set Z1 : Subgroup G := (Subgroup.center P').map P'.subtype with hZ1
  set Z2 : Subgroup G := (Subgroup.upperCentralSeries P' 2).map P'.subtype with hZ2
  have hmem1 : ∀ x (hx : x ∈ P'), x ∈ Z1 ↔ (⟨x, hx⟩ : P') ∈ Subgroup.center P' := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨_, h, rfl⟩
  have hmem2 : ∀ x (hx : x ∈ P'), x ∈ Z2 ↔
      (⟨x, hx⟩ : P') ∈ Subgroup.upperCentralSeries P' 2 := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨_, h, rfl⟩
  have hZ12 : Z1 ≤ Z2 := Subgroup.map_mono (by
    have := Subgroup.upperCentralSeries_mono P' (show 1 ≤ 2 by norm_num)
    rwa [Subgroup.upperCentralSeries_one] at this)
  have hcZ1 : c ∈ Z1 :=
    (hmem1 c hcP').mpr ((mem_center_iff_of_mem hcP').mpr fun p hp => hcent p hp)
  have hzP' : z ∈ P' := hPP' hzP
  have hzZ2 : z ∈ Z2 := by
    refine (hmem2 z hzP').mpr ((mem_upperCentralSeries_two_iff_of_mem hzP').mpr ?_)
    intro p hp q hq
    have hp' : p ∈ ((P : Set G) * (Subgroup.zpowers c : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right P _ hPN]
      exact hp
    obtain ⟨p₀, hp₀, y, hy, rfl⟩ := hp'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hck : ∀ x ∈ P', x * c ^ k = c ^ k * x := fun x hx =>
      (Commute.zpow_right (hcent x hx) k).eq
    have e : z * (p₀ * c ^ k) * z⁻¹ * (p₀ * c ^ k)⁻¹ = z * p₀ * z⁻¹ * p₀⁻¹ := by
      have h1 := hck z hzP'
      have h2 := hck z⁻¹ (P'.inv_mem hzP')
      calc z * (p₀ * c ^ k) * z⁻¹ * (p₀ * c ^ k)⁻¹
          = z * p₀ * (c ^ k * z⁻¹) * (c ^ k)⁻¹ * p₀⁻¹ := by group
        _ = z * p₀ * (z⁻¹ * c ^ k) * (c ^ k)⁻¹ * p₀⁻¹ := by rw [h2]
        _ = z * p₀ * z⁻¹ * p₀⁻¹ := by group
    rw [e]
    have hcomP := (mem_upperCentralSeries_two_iff_of_mem hzP).mp hz2 p₀ hp₀
    have hq' : q ∈ ((P : Set G) * (Subgroup.zpowers c : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right P _ hPN]
      exact hq
    obtain ⟨q₀, hq₀, y', hy', rfl⟩ := hq'
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    have hw : z * p₀ * z⁻¹ * p₀⁻¹ ∈ P' :=
      hPP' (P.mul_mem (P.mul_mem (P.mul_mem hzP hp₀) (P.inv_mem hzP)) (P.inv_mem hp₀))
    have h3 := (Commute.zpow_right (hcent _ hw) k').eq
    calc q₀ * c ^ k' * (z * p₀ * z⁻¹ * p₀⁻¹)
        = q₀ * (c ^ k' * (z * p₀ * z⁻¹ * p₀⁻¹)) := by group
      _ = q₀ * ((z * p₀ * z⁻¹ * p₀⁻¹) * c ^ k') := by rw [h3]
      _ = (q₀ * (z * p₀ * z⁻¹ * p₀⁻¹)) * c ^ k' := by group
      _ = ((z * p₀ * z⁻¹ * p₀⁻¹) * q₀) * c ^ k' := by rw [hcomP q₀ hq₀]
      _ = (z * p₀ * z⁻¹ * p₀⁻¹) * (q₀ * c ^ k') := by group
  have hzZ1 : z ∉ Z1 := by
    intro h
    apply hzZ
    rw [mem_center_iff_of_mem]
    intro p hp
    exact ((mem_center_iff_of_mem hzP').mp ((hmem1 z hzP').mp h)) p (hPP' hp)
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    (Subgroup.zpowers_le.mpr hzP).trans hPN
  have hd' : d ∈ ((Subgroup.zpowers c : Set G) * (Subgroup.zpowers z : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN]
    exact hd
  obtain ⟨y, hy, w, hw, hyw⟩ := Set.mem_mul.mp hd'
  subst hyw
  have hyZ1 : y ∈ Z1 := (Subgroup.zpowers_le.mpr hcZ1) hy
  have hwZ2 : w ∈ Z2 := (Subgroup.zpowers_le.mpr hzZ2) hw
  have hdP' : y * w ∈ P' :=
    P'.mul_mem ((Subgroup.zpowers_le.mpr hcP') hy) ((Subgroup.zpowers_le.mpr hzP') hw)
  refine ⟨hdP', hP'3, (hmem2 _ hdP').mp (Z2.mul_mem (hZ12 hyZ1) hwZ2), fun h => ?_⟩
  have hwZ1 : w ∈ Z1 := by
    have := Z1.mul_mem (Z1.inv_mem hyZ1) ((hmem1 _ hdP').mpr h)
    rwa [inv_mul_cancel_left] at this
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hj : z ^ j ≠ 1 := by
    intro h1
    apply hdc
    rw [h1, mul_one]
    exact hy
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 (fun h1 => hj (by rw [h1, one_zpow]))
  have hzj : z ∈ Subgroup.zpowers (z ^ j) := by
    have h3 : (z ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
    have ho : orderOf (z ^ j) = 3 := orderOf_eq_prime h3 hj
    have hle : Subgroup.zpowers (z ^ j) ≤ Subgroup.zpowers z :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩)
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, Nat.card_zpowers, ho, hzo])
    rw [heq]
    exact Subgroup.mem_zpowers z
  exact hzZ1 ((Subgroup.zpowers_le.mpr hwZ1) hzj)

end Step1917Steps

open Step1917Steps in
theorem step1917Z2W_of
    (h1913 : Step1913) (hK : Step1917Z2KFact) : Step1917Z2W := by
  intro G _ _ A c L E M hctx hLM d hdD hdc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  obtain ⟨-, -, hL3⟩ := Step1916Proof2.lBar_facts h1913 hctx
  have hE := Step1916Proof2.isE27_E hctx
  have hA := Step1916Proof2.isE27_A hctx
  have hcA := Step1916Proof2.mem_A hctx
  have hcE := Step1916Proof2.mem_E hctx
  have hc3 := Step1916Proof2.orderOf_eq hctx
  have hcL := Step1916Proof2.not_mem_L hctx
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hctx.mem_lA.1
  set Q := E ⊔ A with hQ
  have hQ3 : IsPGroup 3 Q := hctx.isPGroup_sup
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (Step1916Proof2.le_normalizer_E hctx hL3) hctx.mem_lA.2.1
  have hQnab : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    apply Step1916Proof2.ne_E hctx
    have hAE : A ≤ E := fun a ha => mem_of_le_centralizer hst hctx.partTwoS_eq
      hctx.mem_partTwoT.1 (hA.1.2 a ha) fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
        (h e (le_sup_left (b := A) he) a (le_sup_right (a := E) ha))
    exact Subgroup.eq_of_le_of_card_ge hAE (by rw [hA.2, hE.2])
  have hAM := le_M h1913 hctx
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  have hrank : CFSG.Open.pRank 3 (Q ⊔ L) ≤ 3 := by
    have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three
      (sup_le (sup_le hEM hAM) hLM : Q ⊔ L ≤ M)
    have h2 := Sec18.pRank_le_localRank_of_isTwoLocal Nat.prime_three hctx.mem_scriptM.1.1
    rw [hst.toTheoremFourHyp.localRank_three] at h2
    omega
  set Y := Q ⊔ L with hY
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := sup_le hQN Subgroup.le_normalizer
  obtain ⟨T₀, hQT₀⟩ := (hQ3.comap_subtype (K := Y)).exists_le_sylow
  set T : Subgroup G := (T₀ : Subgroup Y).map Y.subtype with hT
  have hTY : IsSylowOf 3 T Y := ⟨T₀, rfl⟩
  have hQT : Q ≤ T := fun x hx =>
    ⟨⟨x, le_sup_left (b := L) hx⟩, hQT₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTL : IsSylowOf 3 (T ⊓ L) L := hTY.inf_of_le_normalizer le_sup_right hYN
  have hTL1 : T ⊓ L ≠ ⊥ := by
    intro h
    have hcard := hTL.card_eq
    rw [h, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card L).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hL3
    have h3 : 3 ≤ 3 ^ (Nat.card L).factorization 3 :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hpos)
    omega
  obtain ⟨z, hzTL, hz1, hz3, hzT⟩ := Step1916Proof2.exists_mem_of_normal hTY.isPGroup inf_le_left
    (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, hYN (hTY.le ht)⟩) hTL1
  have hC : ∀ X : Subgroup G, X ≤ T → X ≤ Subgroup.centralizer ({z} : Set G) := fun X hXT x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzT x (hXT hx))
  have hzA : z ∈ A := mem_of_le_centralizer hst hctx.partTwoS_eq hctx.mem_partTwoE hz3
    (hC A (le_sup_right.trans hQT))
  have hzE : z ∈ E := mem_of_le_centralizer hst hctx.partTwoS_eq hctx.mem_partTwoT.1 hz3
    (hC E (le_sup_left.trans hQT))
  obtain ⟨P, hPY, hP3, hzP, hz2, hzZ⟩ := hK G L Q T z hLperf (h1913 G A c L E M hctx) hQ3 hQN
    hQnab hrank hTY hQT hzTL.2 hzTL.1 hz1 hzT
  have hcent : ∀ x ∈ E ⊔ A ⊔ L, x * c = c * x := by
    have hle : E ⊔ A ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le (sup_le hctx.le_centralizer (le_centralizer_of_mem hA.1.1 hcA))
        (Sec6.le_centralizer_of_mem_thetaComponentsAt hctx.mem_lA.1)
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hzc : z ∉ Subgroup.zpowers c := by
    intro h
    have hbot := Step1914TriProof.zpowers_inf_eq_bot_of_not_mem hc3 hcL
    have : z ∈ Subgroup.zpowers c ⊓ L := ⟨h, hzTL.2⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hz1 this
  have hD9 : Nat.card (A ⊓ E : Subgroup G) = 9 := step1916D_of h1913 G A c L E M hctx
  have hB : Subgroup.zpowers c ⊔ Subgroup.zpowers z = A ⊓ E := by
    have hBD : Subgroup.zpowers c ⊔ Subgroup.zpowers z ≤ A ⊓ E :=
      sup_le (Subgroup.zpowers_le.mpr ⟨hcA, hcE⟩) (Subgroup.zpowers_le.mpr ⟨hzA, hzE⟩)
    have h9 : 9 ≤ Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers z : Subgroup G) :=
      Step1914TriProof.nine_le_card_of_mem_of_not_mem hE (hBD.trans inf_le_right) hc3
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)) hzc
    exact Subgroup.eq_of_le_of_card_ge hBD (by rw [hD9]; exact h9)
  have hd : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers z := hB ▸ hdD
  have hc3' : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc3, pow_one])
  obtain ⟨hdP', hP'3, hd2, hdZ⟩ := exists_of_central hP3 hc3' (fun p hp => hcent p (hPY hp))
    hzP hz2 hzZ hz3 hd hdc
  exact ⟨P ⊔ Subgroup.zpowers c, sup_le hPY (Subgroup.zpowers_le.mpr
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left hcE))), hP'3, hdP', hd2, hdZ⟩

end CFSG.RankThree.PartTwo.Sec19
