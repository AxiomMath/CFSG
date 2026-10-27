module

public import CFSG.RankThree.PartTwo.Sec18.SylowPlane
public import CFSG.RankThree.PartTwo.Sec18.SylowFiveDelta
import CFSG.RankThree.PartTwo.Sec18.SylowFiveChar
import CFSG.RankThree.PartTwo.Sec18.SylowFiveRank
import CFSG.RankThree.PartTwo.Sec18.SylowFiveAct
import CFSG.RankThree.PartTwo.Sec18.SylowFiveCent
import CFSG.RankThree.PartTwo.Sec18.SylowTop
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open CFSG.Assembly.RankThreeEven (projSL)

namespace SylowFive

variable {G : Type} [Group G] [Finite G]

theorem oThreeWStar_le_autIn {A P : Subgroup G}
    (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G))) :
    Sec13.oThreeWStar A ≤ Sec4.autIn P A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : ((Sec13.oThreeWStar A).subgroupOf (Sec13.wStar A)).Normal := by
    rw [Sec13.oThreeWStar, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    exact CFSG.pCore_normal
  exact SylowTop.le_of_isSylowOf (Subgroup.map_subtype_le _)
    (CFSG.pCore_isPGroup.map _) (Sec13.Holds134.isSylowOf_autIn_wStar hP)

theorem conj_mem_centralizer {B : Subgroup G} {w y : G}
    (hw : w ∈ Subgroup.normalizer (B : Set G)) (hy : y ∈ Subgroup.centralizer (B : Set G)) :
    w * y * w⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro b hb
  have hb' : w⁻¹ * b * w ∈ B := (Subgroup.mem_normalizer_iff.mp hw _).mpr (by
    rw [show w * (w⁻¹ * b * w) * w⁻¹ = b by group]
    exact hb)
  have h := hy _ hb'
  calc b * (w * y * w⁻¹) = w * ((w⁻¹ * b * w) * y) * w⁻¹ := by group
    _ = w * (y * (w⁻¹ * b * w)) * w⁻¹ := by rw [h]
    _ = w * y * w⁻¹ * b := by group

theorem zpowers_eq_of_mem {c z : G} (hc3 : orderOf c = 3) (hz : z ∈ Subgroup.zpowers c)
    (hz1 : z ≠ 1) : Subgroup.zpowers z = Subgroup.zpowers c := by
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc3, pow_orderOf_eq_one,
      one_zpow]
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hc3, orderOf_eq_prime hz3 hz1]

section PlaneQ8

variable {A B K P : Subgroup G} {c : G} (hQ8 : PlaneQ8 A B K c)
  (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G)))
  (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
include hQ8 hP hWB

theorem exists_conj_eq_of_planeQ8
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {b : G} (hb : b ∈ B) : ∃ x ∈ qOf P B, x * c * x⁻¹ = b * c := by
  obtain ⟨w, hw, hwT, hwc⟩ := Sec13.exists_transv_of_irreducible hQ8.isElemAbelian hQ8.mem
    hQ8.eq_sup hQ8.card_plane hQ8.commute hQ8.irreducible hQ8.le_normalizer
    hQ8.le_normalizer_plane hWB hWa hb
  have hO := Sec13.oThreeWStar_eq_transvAxis hQ8.isElemAbelian hQ8.mem hQ8.eq_sup hQ8.not_mem
    hQ8.card_plane hQ8.commute hQ8.irreducible hQ8.le_normalizer hQ8.le_normalizer_plane hWB hWa
  obtain ⟨x, hxN, hxP, hxw⟩ := Sec4.mem_autIn_iff.mp (oThreeWStar_le_autIn hP (hO.ge hwT))
  have hBA : B ≤ A := hQ8.eq_sup ▸ le_sup_right
  have hconj : ∀ a (ha : a ∈ A), x * a * x⁻¹ = w * a * w⁻¹ := fun a ha => by
    have h := congrArg (fun σ : MulAut A => ((σ ⟨a, ha⟩ : A) : G)) hxw
    simpa only [Sec13.normalizerMonoidHom_apply_val] using h
  refine ⟨x, ⟨hxP, Subgroup.mem_centralizer_iff.mpr fun b' hb' => ?_⟩, ?_⟩
  · have h1 : w * b' * w⁻¹ = b' := by
      have h := congrArg Subtype.val (hwT.1 ⟨b', hBA hb'⟩ hb')
      rwa [Sec13.normalizerMonoidHom_apply_val] at h
    have h2 := hconj b' (hBA hb')
    rw [h1] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · rw [hconj c hQ8.mem, hwc]
    exact congrArg Subtype.val (hQ8.isElemAbelian.1.is_comm.comm ⟨c, hQ8.mem⟩ ⟨b, hBA hb⟩)

theorem not_le_normalizer_of_planeQ8 (B₀ : Subgroup G) (hB₀B : B₀ ≤ B) (hB₀3 : Nat.card B₀ = 3) :
    ¬ Subgroup.normalizer ((qOf P B : Subgroup G) : Set G) ≤
      Subgroup.normalizer (B₀ : Set G) := by
  intro hN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := Subgroup.normalizer (A : Set G) with hW
  set C := W ⊓ Subgroup.centralizer (B : Set G) with hC
  have hconjC : ∀ w ∈ W, ∀ y ∈ C, w * y * w⁻¹ ∈ C := fun w hw y hy =>
    ⟨W.mul_mem (W.mul_mem hw hy.1) (W.inv_mem hw), conj_mem_centralizer (hWB hw) hy.2⟩
  have hWC : W ≤ Subgroup.normalizer (C : Set G) := fun w hw =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨hconjC w hw y, fun h => by
      have h' := hconjC w⁻¹ (W.inv_mem hw) _ h
      rwa [show w⁻¹ * (w * y * w⁻¹) * w⁻¹⁻¹ = y by group] at h'⟩
  have hQC : P ⊓ C = qOf P B := by rw [hC, ← inf_assoc, inf_eq_left.mpr hP.le]
  have hQsyl : IsSylowOf 3 (qOf P B) C := by
    rw [← hQC]
    exact hP.inf_of_le_normalizer inf_le_left hWC
  have hKB₀ : K ≤ Subgroup.normalizer (B₀ : Set G) := by
    intro k hk
    have hkW : k ∈ W := hQ8.le_normalizer hk
    set Q' := (qOf P B).map (MulAut.conj k).toMonoidHom with hQ'
    have hmemQ' : ∀ q, q ∈ qOf P B → k * q * k⁻¹ ∈ Q' := fun q hq =>
      Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    have hQ'C : Q' ≤ C := by
      rintro _ ⟨q, hq, rfl⟩
      exact hconjC k hkW q ⟨hP.le hq.1, hq.2⟩
    have hQ'syl : IsSylowOf 3 Q' C := by
      refine isSylowOf_of_card hQ'C ?_
      rw [hQ', Subgroup.card_map_of_injective (MulAut.conj k).injective, hQsyl.card_eq]
    obtain ⟨y, hyC, hy⟩ := hQsyl.exists_mem_conj hQ'syl
    have e : ∀ q : G, y⁻¹ * (k * q * k⁻¹) * y = y⁻¹ * k * q * (y⁻¹ * k)⁻¹ := fun q => by group
    have hyk : y⁻¹ * k ∈ Subgroup.normalizer ((qOf P B : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      constructor
      · intro hq
        rw [← e]
        exact (hy _).mp (hmemQ' q hq)
      · intro hq
        obtain ⟨q', hq', hq'eq⟩ := Subgroup.mem_map.mp ((hy _).mpr (by rwa [e]))
        have hqq : q' = q := by
          have h : k * q' * k⁻¹ = k * q * k⁻¹ := hq'eq
          simpa using h
        rwa [← hqq]
    have hyB₀ : y ∈ Subgroup.normalizer (B₀ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hB₀B hyC.2)
    have h := Subgroup.mul_mem _ hyB₀ (hN hyk)
    rwa [mul_inv_cancel_left] at h
  rcases Sec13.eq_bot_or_eq_of_isIrreducibleOn hQ8.irreducible hB₀B hKB₀ with h | h
  · rw [h, Subgroup.card_bot] at hB₀3
    norm_num at hB₀3
  · rw [h, hQ8.card_plane] at hB₀3
    norm_num at hB₀3

end PlaneQ8

section Certified


variable {A M H : Subgroup G} {c : G}

theorem pow_three_mem_zpowers_of_sec18H (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (hH : Sec18H G A M H c) {t : G} {k : ℕ} (htk : t ^ 3 ^ k = 1)
    (htA : ∀ a ∈ A, t * a = a * t) (ht3 : t ^ 3 ∈ A) : t ^ 3 ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := A ⊓ inSubgroup perfectResidual H with hB
  set Kc := Sec4.thetaQuotCentralizer (lc H c) with hKc
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hcA := (mem_and_commutator_mem_of_sec18H hH).1
  have hAeq : A = Subgroup.zpowers c ⊔ B := eq_zpowers_sup_of_sec18H h1812 h184 hH
  have hB9 := card_inf_of_sec18H h1812 h184 hH
  have hB3 : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 _ x.2.1)⟩
  have hBlc : B ≤ lc H c := (inf_lc_eq h1812 h184 hH).ge.trans inf_le_right
  obtain ⟨eL⟩ := SylowFusion.nonempty_quotient_lc h184 hH
  obtain ⟨hZ, -⟩ := center_eq_bot_and_card_mulAut (commutator_inSubgroup_perfectResidual _) eL
  have htc : t * c = c * t := htA c hcA
  have htN : t ∈ Subgroup.normalizer (lc H c : Set G) := by
    refine normalizer_zpowers_le_normalizer_lc h1842 hH
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_))
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (htc.symm : Commute c t) i).eq
  obtain ⟨e, heB, hte⟩ := exists_mem_thetaQuotCentralizer_of_commute
    (commutator_inSubgroup_perfectResidual _) eL hBlc hB9 hB3 htN (fun e he => htA e he.1) htk
  have ht3K : t ^ 3 ∈ Kc := by
    have hcomm : Commute t e⁻¹ := Commute.inv_right (htA e heB.1)
    have h := Kc.pow_mem hte 3
    rwa [hcomm.mul_pow, inv_pow, hA.1.2 e heB.1, inv_one, mul_one] at h
  have hBK : B ⊓ Kc = ⊥ := by
    have h1 := Sec12.card_inf_le_card_center_of_le_thetaQuotCentralizer (L := lc H c)
      (hB3.to_le inf_le_left) (inf_le_right : B ⊓ Kc ≤ Kc)
    rw [hZ, Subgroup.card_bot] at h1
    have h2 : B ⊓ Kc ⊓ lc H c = ⊥ := Subgroup.eq_bot_of_card_le _ h1
    rwa [inf_eq_left.mpr (inf_le_left.trans hBlc)] at h2
  obtain ⟨i, -, b, hb, hbeq⟩ := Sec13.exists_pow_mul_of_mem hA.1 hcA hAeq ht3
  have hbK : b ∈ Kc := by
    have e : b = (c ^ i)⁻¹ * t ^ 3 := by rw [hbeq]; group
    rw [e]
    exact Kc.mul_mem (Kc.inv_mem (Kc.pow_mem (mem_thetaQuotCentralizer_lc H c) i)) ht3K
  have hb1 : b = 1 := by
    have hmem : b ∈ B ⊓ Kc := ⟨hb, hbK⟩
    rwa [hBK, Subgroup.mem_bot] at hmem
  rw [hbeq, hb1, mul_one]
  exact Subgroup.npow_mem_zpowers c i

theorem pow_three_eq_one_of_sec18H (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (hH : Sec18H G A M H c)
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {t : G} {k : ℕ} (htk : t ^ 3 ^ k = 1) (htA : ∀ a ∈ A, t * a = a * t) (ht3 : t ^ 3 ∈ A) :
    t ^ 3 = 1 := by
  by_contra hne
  have hc3 := orderOf_eq_three_of_sec18H h184 hH
  obtain ⟨w, hw, hwc⟩ := SetLike.not_le_iff_exists.mp hWa
  have hconjA : ∀ a ∈ A, w * a * w⁻¹ ∈ A := fun a ha => (Subgroup.mem_normalizer_iff.mp hw a).mp ha
  have h1 := zpowers_eq_of_mem hc3
    (pow_three_mem_zpowers_of_sec18H h1812 h184 h1842 hH htk htA ht3) hne
  have hsk : (w * t * w⁻¹) ^ 3 ^ k = 1 := by rw [conj_pow, htk, mul_one, mul_inv_cancel]
  have hsA : ∀ a ∈ A, w * t * w⁻¹ * a = a * (w * t * w⁻¹) := by
    intro a ha
    have ha' : w⁻¹ * a * w ∈ A := by
      have h := hconjA _ (A.inv_mem (A.inv_mem ha))
      have h' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) a).mp ha
      rwa [inv_inv] at h'
    have h := htA _ ha'
    calc w * t * w⁻¹ * a = w * (t * (w⁻¹ * a * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * a * w) * t) * w⁻¹ := by rw [h]
      _ = a * (w * t * w⁻¹) := by group
  have hs3 : (w * t * w⁻¹) ^ 3 ∈ A := by rw [conj_pow]; exact hconjA _ ht3
  have h2 := zpowers_eq_of_mem hc3
    (pow_three_mem_zpowers_of_sec18H h1812 h184 h1842 hH hsk hsA hs3)
    (by rw [conj_pow]; intro h; exact hne (by simpa using h))
  apply hwc
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc (Subgroup.zpowers c).map (MulAut.conj w : G →* G)
      = (Subgroup.zpowers (t ^ 3)).map (MulAut.conj w : G →* G) := by rw [h1]
    _ = Subgroup.zpowers ((MulAut.conj w : G →* G) (t ^ 3)) := MonoidHom.map_zpowers _ _
    _ = Subgroup.zpowers c := by rw [← h2, conj_pow]; rfl

theorem mem_of_commute_of_sec18H (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (hH : Sec18H G A M H c)
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {k : ℕ} : ∀ {x : G}, x ^ 3 ^ k = 1 → (∀ a ∈ A, x * a = a * x) → x ∈ A := by
  induction k with
  | zero =>
    intro x hx _
    rw [pow_zero, pow_one] at hx
    rw [hx]
    exact A.one_mem
  | succ k ih =>
    intro x hx hxA
    have hx3k : (x ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, ← pow_succ']; exact hx
    have hx3A : x ^ 3 ∈ A := ih hx3k fun a ha => (Commute.pow_left (hxA a ha : Commute x a) 3).eq
    have hx3 := pow_three_eq_one_of_sec18H h1812 h184 h1842 hH hWa hx hxA hx3A
    exact Item183NMProof.mem_of_commute_of_sec18Std hH.toSec18Std hx3 fun b hb => (hxA b hb).symm

theorem caseTwo_of_sec18H (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2)
    (hH : Sec18H G A M H c) {P : Subgroup G}
    (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G)))
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    CaseTwo P A (A ⊓ inSubgroup perfectResidual H) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 _ x.2)⟩
  have hQ8 := planeQ8_of_sec18H h1812 h184 hH
  exact
    { isPGroup := hP.isPGroup
      isElemAbelian := hA.1
      card_eq := hA.2
      le := inf_le_left
      card_plane := card_inf_of_sec18H h1812 h184 hH
      eq_sup := eq_zpowers_sup_of_sec18H h1812 h184 hH
      not_mem := fun h => not_mem_of_sec18H h184 hH h.2
      le_sylow := SylowTop.le_of_isSylowOf (Subgroup.le_normalizer (H := A)) hA3 hP
      le_normalizer := hP.le
      le_normalizer_plane := hP.le.trans hWB
      mem_of_commute := fun x hx hxA => by
        obtain ⟨k, hk⟩ := hP.isPGroup ⟨x, hx⟩
        exact mem_of_commute_of_sec18H h1812 h184 h1842 hH hWa
          (Subtype.ext_iff.mp hk : x ^ 3 ^ k = 1) hxA
      exists_conj_eq := fun b hb => exists_conj_eq_of_planeQ8 hQ8 hP hWB hWa hb
      card_le := fun E hEP hE => card_le_of_le_normalizer hH.toSec18Std (hEP.trans hP.le) hE
      not_le_normalizer := fun B₀ hB₀ h3 => not_le_normalizer_of_planeQ8 hQ8 hP hWB B₀ hB₀ h3 }

theorem item184_5_of
    (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2) : Item184_5 := by
  intro G _ _ A M H c hH P hP
  by_cases hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  · exact Or.inl ⟨hWc, omegaOne_of_le_normalizer_zpowers h1812 h184 h1842 hH hP hWc⟩
  · obtain ⟨hWB, hrest⟩ := wStar_structure_of_sec18H h1812 h184 h1842 hH
    have horb : (Sec13.orbitIn (Subgroup.normalizer (A : Set G))
        (Subgroup.zpowers c)).ncard = 9 := by
      rcases hrest with h | ⟨-, -, -, -, h⟩
      · exact absurd h hWc
      · exact h
    have hS := caseTwo_of_sec18H h1812 h184 h1842 hH hP hWB hWc
    exact Or.inr ⟨hWB, horb, hS.le_sylow, hS.characteristic, hS.sectional⟩

end Certified

end SylowFive

end CFSG.RankThree.PartTwo.Sec18
