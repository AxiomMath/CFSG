module

public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofTwenty
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.FrobeniusNormalComplement

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

section W

variable {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}

theorem pow_three_eq_one_of_isSylowOf (h415 : Sec4.Item4_15)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {T : Subgroup G} (hT : IsSylowOf 3 T L) {x : G} (hx : x ∈ T) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₀, rfl⟩ := hT
  obtain ⟨y, hy, rfl⟩ := hx
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hinj : Set.InjOn π ((S₀ : Subgroup ↥L) : Set ↥L) :=
    injOn_mk_of_isPGroup Nat.prime_three S₀.isPGroup'
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S₀.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S₀ : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 _ hJ Sb _ rfl _ rfl
  have hexp : Monoid.exponent ↥(Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = 3 :=
    hHeis.2.2
  have hyb : π y ∈ (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
    hSb ▸ Subgroup.mem_map_of_mem π hy
  have h1 : (⟨π y, hyb⟩ : ↥(Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))) ^ 3 = 1 := by
    have h0 := Monoid.pow_exponent_eq_one
      (⟨π y, hyb⟩ : ↥(Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    rwa [hexp] at h0
  have h2 : π (y ^ 3) = π 1 := by
    rw [map_pow, map_one]
    exact congrArg Subtype.val h1
  have h3 : y ^ 3 = 1 := hinj (pow_mem hy 3) (one_mem _) h2
  change ((y : ↥L) : G) ^ 3 = 1
  rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]

theorem Sec17Std.exists_w (h415 : Sec4.Item4_15) (h1715 : Item1715) (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ w : G, w ∈ Subgroup.normalizer (A : Set G) ⊓ L ∧ w ∉ A ∧ orderOf w = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, h9, hAeq⟩ := h.hj_facts h1715 h415 hJ
  have hAL3 : IsPGroup 3 ↥(A ⊓ L) := h.isE27.isPGroup.to_le inf_le_left
  obtain ⟨T, hT, hALT⟩ := Item134SylowBarProof.exists_isSylowOf_le inf_le_right hAL3
  have hT27 : Nat.card T = 27 := by
    obtain ⟨S₀, rfl⟩ := hT
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact card_sylow_eq_27 h415 hJ S₀
  obtain ⟨w, hwT, hwAL⟩ : ∃ w ∈ T, w ∉ A ⊓ L := by
    by_contra hall
    push Not at hall
    have hle := Subgroup.card_le_of_le (show T ≤ A ⊓ L from hall)
    rw [hT27, h9] at hle
    omega
  have hw3 : w ^ 3 = 1 := pow_three_eq_one_of_isSylowOf h415 hJ hT hwT
  have hw1 : w ≠ 1 := fun h1 => hwAL (h1 ▸ one_mem _)
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hwL : w ∈ L := hT.le hwT
  have hTN : T ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    set A' := (A ⊓ L).subgroupOf T with hA'
    have hA'9 : Nat.card A' = 9 := by
      rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALT).toEquiv, h9]
    have hidx : A'.index = 3 := by
      have h' := A'.card_mul_index
      rw [hA'9, hT27] at h'
      omega
    have hnorm : A'.Normal := Subgroup.normal_of_index_eq_minFac_card (by
      rw [hidx, hT27]
      norm_num)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hALT).mp hnorm
  have hwc : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer (h.le_centralizer_c hwL)
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := by
    rw [hAeq]
    exact mem_normalizer_sup hwc (hTN hwT)
  exact ⟨w, Subgroup.mem_inf.mpr ⟨hwA, hwL⟩, fun hmem => hwAL ⟨hmem, hwL⟩, hwo⟩

theorem Sec17Y1.exists_sec17W (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1721 : Item1721)
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) :
    ∃ (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q := by
  obtain ⟨w, hwm, hwA, hwo⟩ :=
    h.toSec17Std.exists_w h415 h1715 (h1721 G A c L Y₀ Y₁ S p P h)
  have hPG : P ∈ scriptQPi A (lB A) ⊤ (piOf p) :=
    ⟨⟨h.mem_qStar_p.prop.1.1, le_top⟩, h.mem_qStar_p.prop.2⟩
  obtain ⟨Q, hPQ, hQ⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf p))) hPG
  exact ⟨w, Q,
    { toSec17Y1 := h
      w_mem := hwm
      w_not_mem := hwA
      orderOf_w := hwo
      le_Q := hPQ
      mem_qStar_G := hQ }⟩

theorem para1722_of (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1721 : Item1721) : Para1722 :=
  fun _ _ _ _ _ _ _ _ _ _ _ h => h.exists_sec17W h415 h1715 h1721

theorem para1722_of_items
    (h1715 : Item1715)
    (h1721 : Item1721) : Para1722 :=
  para1722_of Sec4.Sporadic.rank3II_4_15 h1715 h1721

end W

@[expose] def Claim1722X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P → xA A ⊔ S ∈ scriptY1 A (lB A)

@[expose] def Claim1722T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ∀ T : Subgroup G, IsSylowOf 3 T (Subgroup.centralizer (A : Set G)) →
        T ≤ Subgroup.normalizer ((x1720 A Y₀ S L : Subgroup G) : Set G)

namespace TailProof

open Subgroup

theorem exists_normal_complement {A C : Subgroup G} (hCA : C ≤ centralizer (A : Set G))
    (h3 : ∀ y ∈ C, y ^ 3 = 1 → y ∈ A) :
    ∃ N : Subgroup G, N ≤ C ∧ C ≤ normalizer (N : Set G) ∧ ¬ 3 ∣ Nat.card N ∧
      ∀ y ∈ C, ¬ 3 ∣ orderOf y → y ∈ N := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcrit : ∀ Q : Subgroup C, IsPGroup 3 Q → IsPGroup 3 (normalizer (Q : Set C) ⧸
      (centralizer (Q : Set C)).subgroupOf (normalizer (Q : Set C))) := by
    intro Q hQ g
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨e, m, hm3, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 3 (by norm_num)
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    set y := n ^ (3 ^ e) with hy
    have hyord : orderOf y = m := by
      rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) ⟨m, hord⟩, hord,
        Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
    set yC : C := (y : C) with hyC
    have hyN : yC ∈ normalizer (Q : Set C) := y.2
    have hyN' : zpowers yC ≤ normalizer (Q : Set C) := zpowers_le.mpr hyN
    let _ : MulDistribMulAction (zpowers yC) Q :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (zpowers yC) Q hyN'
    have hsmul : ∀ (a : zpowers yC) (q : Q), (((a • q : Q) : C) : C) =
        (a : C) * (q : C) * (a : C)⁻¹ := fun _ _ => rfl
    have : Fact (IsPGroup 3 Q) := ⟨hQ⟩
    have hcop : Nat.Coprime (Nat.card (zpowers yC)) (Nat.card Q) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hyord]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
    have hE : ∃ _ : Fact (IsPGroup 3 (⊥ : Subgroup Q)), IsElementaryAbelian 3 (⊥ : Subgroup Q) :=
      ⟨⟨IsPGroup.of_card (n := 0) (by simp)⟩,
        { toIsMulCommutative := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
            Subsingleton.elim _ _ }⟩
    have htriv : ActsTrivially (zpowers yC) Q := by
      refine corollary_1_12 (p := 3) (by norm_num) ⊥ hE hcop ?_
      intro g _ hg a
      have hg3 : (((g : C) : G)) ^ 3 = 1 := by
        have : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
        simpa using congrArg (fun z : Q => ((z : C) : G)) this
      have hgA : ((g : C) : G) ∈ A := h3 _ (g : C).2 hg3
      apply Subtype.ext
      apply Subtype.ext
      rw [hsmul]
      have hcomm := mem_centralizer_iff.mp (hCA ((a : C).2)) _ hgA
      change (((a : C) : G) * ((g : C) : G) * ((a : C) : G)⁻¹) = ((g : C) : G)
      rw [← hcomm, mul_inv_cancel_right]
    refine Subgroup.mem_subgroupOf.mpr (mem_centralizer_iff.mpr fun q hq => ?_)
    have h1 := htriv ⟨yC, mem_zpowers yC⟩ ⟨q, hq⟩
    have h2 := congrArg (fun z : Q => (z : C)) h1
    simp only at h2
    rw [hsmul] at h2
    change yC * q * yC⁻¹ = q at h2
    calc q * yC = (yC * q * yC⁻¹) * yC := by rw [h2]
      _ = yC * q := by group
  obtain ⟨N₀, hN₀n, hN₀c, k, hk⟩ := (CFSG.GroupTheory.frobenius_normal_p_complement 3).1.2 hcrit
  refine ⟨N₀.map C.subtype, map_subtype_le _, fun c hc => ?_, ?_, fun y hy hy3 => ?_⟩
  · have h := le_normalizer_map (H := N₀) C.subtype
    rw [normalizer_eq_top_iff.mpr hN₀n, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h hc
  · rw [card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN₀c.symm
  · refine ⟨⟨y, hy⟩, ?_, rfl⟩
    have h1 : orderOf (QuotientGroup.mk' N₀ (⟨y, hy⟩ : C)) ∣ orderOf y := by
      rw [← Subgroup.orderOf_mk y hy]
      exact orderOf_map_dvd _ _
    have h2 : orderOf (QuotientGroup.mk' N₀ (⟨y, hy⟩ : C)) ∣ 3 ^ k := by
      rw [← hk, Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf y) (3 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hy3).symm
    have h3' := CFSG.GroupTheory.FrobeniusNormalComplement.orderOf_eq_one_of_dvd hcop h1 h2
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3'

theorem mem_xA_of_not_three_dvd {A : Subgroup G} (hA : A ∈ partTwoF G) {y : G}
    (hy : y ∈ centralizer (A : Set G)) (hy3 : ¬ 3 ∣ orderOf y) : y ∈ xA A := by
  obtain ⟨N, hNC, hCN, hN3, hN⟩ := exists_normal_complement (A := A) le_rfl
    (fun z hz hz3 => mem_of_mem_partTwoF hA hz3 fun a ha =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz a ha))
  exact le_pPrimeCoreOf hNC hCN ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)
    (hN y hy hy3)

theorem exists_three_part (g : G) : ∃ a ∈ zpowers g, ∃ b ∈ zpowers g,
    g = a * b ∧ (∃ k : ℕ, a ^ (3 ^ k) = 1) ∧ ¬ 3 ∣ orderOf b := by
  obtain ⟨e, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hcop : Nat.Coprime (3 ^ e) m :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
  set n : ℤ := ((3 ^ e : ℕ) : ℤ) with hn'
  set α : ℤ := Nat.gcdA (3 ^ e) m with hα
  set β : ℤ := Nat.gcdB (3 ^ e) m with hβ
  have hbez : n * α + (m : ℤ) * β = 1 := by
    rw [hn', hα, hβ, ← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
  have hg1 : g ^ (n * (m : ℤ)) = 1 := by
    rw [hn', ← Nat.cast_mul, zpow_natCast, ← hn]
    exact pow_orderOf_eq_one g
  refine ⟨g ^ ((m : ℤ) * β), zpow_mem_zpowers _ _, g ^ (n * α), zpow_mem_zpowers _ _, ?_,
    ⟨e, ?_⟩, ?_⟩
  · rw [← zpow_add, add_comm, hbez, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul, ← hn', show (m : ℤ) * β * n = (n * (m : ℤ)) * β by ring,
      zpow_mul, hg1, one_zpow]
  · intro h3
    apply hm3
    have hdvd : orderOf (g ^ (n * α)) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, show n * α * (m : ℤ) = (n * (m : ℤ)) * α by ring,
        zpow_mul, hg1, one_zpow]
    exact h3.trans hdvd

end TailProof

section Item1722

variable {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}

theorem Sec17Y1.item168_at (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L) :
    S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) ∧
      (∀ Y ∈ scriptY1 A (lB A), S ≤ Y → Y ≤ Y₁) ∧
      delta A (lB A) (Subgroup.normalizer (S : Set G)) ≤ Y₁ ∧
      Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) ≤
        Subgroup.normalizer (Y₁ : Set G) := by
  have hs := h.toSec17Std
  have hY₁3 : Y₁ ∈ scriptY3 A (lB A) := h.mem_y1Star.prop.1
  obtain ⟨V, hV, hVY⟩ := HeadProof.exists_omega168_le hs h166 hbot hY₁3 h.not_le_M
  obtain ⟨N, hN, hYN, hNS⟩ := h168 (HeadProof.item168_premise hs) V hV Y₁ hY₁3 hVY
  have hY₁N : Y₁ ≤ N := hYN Y₁ hY₁3 le_rfl
  have hNY : N = Y₁ := le_antisymm (h.mem_y1Star.2 hN.prop hY₁N) hY₁N
  rw [hNY] at hNS
  exact hNS S h.mem_qStar_two

theorem rank3II_17_22_of (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (hX : xA A ⊔ S ∈ scriptY1 A (lB A))
    (hT : ∀ T : Subgroup G, IsSylowOf 3 T (Subgroup.centralizer (A : Set G)) →
      T ≤ Subgroup.normalizer ((x1720 A Y₀ S L : Subgroup G) : Set G))
    (h1720 : S ∈ scriptQPiStar A (lB A) (x1720 A Y₀ S L) (piOf 2) ∧
      TransOn A (lB A) (xA A) (x1720 A Y₀ S L)) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y₁ : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  obtain ⟨-, hSY, -, hWS⟩ := h.item168_at h166 hbot h168
  have hXY : xA A ⊔ S ≤ Y₁ := hSY _ hX le_sup_right
  have hxAN : xA A ≤ Subgroup.normalizer (Y₁ : Set G) :=
    le_sup_left.trans (hXY.trans Subgroup.le_normalizer)
  have h3 : ∀ g ∈ Subgroup.centralizer (A : Set G), (∃ k : ℕ, g ^ (3 ^ k) = 1) →
      g ∈ Subgroup.normalizer (Y₁ : Set G) := by
    intro g hg ⟨k, hk⟩
    have hg3 : IsPGroup 3 (Subgroup.zpowers g) := by
      intro x
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
      refine ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, ← hj, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, hk, one_zpow]
    obtain ⟨T, hTsyl, hgT⟩ :=
      Item134SylowBarProof.exists_isSylowOf_le (Subgroup.zpowers_le.mpr hg) hg3
    have hgX := hT T hTsyl (hgT (Subgroup.mem_zpowers g))
    have hgA : g ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hg
    have hSg : S.map (MulAut.conj g).toMonoidHom ∈
        scriptQPiStar A (lB A) (x1720 A Y₀ S L) (piOf 2) := by
      have := HeadProof.map_conj_mem_scriptQPiStar hgA h1720.1
      rwa [Late.map_conj_eq_of_mem_normalizer hgX] at this
    obtain ⟨y, hy, hyS⟩ := h1720.2 S h1720.1 _ hSg
    have hyC : y ∈ Subgroup.centralizer (A : Set G) :=
      pPrimeCoreOf_le 3 _ (Subgroup.mem_inf.mp hy).1
    have hyA : y ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hyC
    have hygS : y⁻¹ * g ∈ Subgroup.normalizer (S : Set G) :=
      inv_mul_mem_normalizer_of_map_conj_eq hyS.symm
    have hygN : y⁻¹ * g ∈ Subgroup.normalizer (Y₁ : Set G) :=
      hWS (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hyA) hgA, hygS⟩)
    have hyN : y ∈ Subgroup.normalizer (Y₁ : Set G) := hxAN (Subgroup.mem_inf.mp hy).1
    have e : g = y * (y⁻¹ * g) := by group
    rw [e]
    exact mul_mem hyN hygN
  intro g hg
  obtain ⟨a, ha, b, hb, heq, ha3, hb3⟩ := TailProof.exists_three_part g
  have haC : a ∈ Subgroup.centralizer (A : Set G) := (Subgroup.zpowers_le.mpr hg) ha
  have hbC : b ∈ Subgroup.centralizer (A : Set G) := (Subgroup.zpowers_le.mpr hg) hb
  rw [heq]
  exact mul_mem (h3 a haC ha3)
    (hxAN (TailProof.mem_xA_of_not_three_dvd hs.mem_partTwoF hbC hb3))

end Item1722

end CFSG.RankThree.PartTwo.Sec17
