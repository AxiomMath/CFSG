module

public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof176Steps

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_commMod (C : Subgroup G) {c : G} (hcC : c ∈ C) :
    ∃ S : Subgroup G, S ≤ C ∧
      (∀ x ∈ C, x * c * x⁻¹ * c⁻¹ ∈ pPrimeCoreOf 3 C → x ∈ S) ∧
      ∀ x ∈ S, ∀ k : ℤ, ⁅x, c ^ k⁆ ∈ pPrimeCoreOf 3 C := by
  set N := CFSG.pPrimeCore 3 ↥C with hN
  set π := QuotientGroup.mk' N with hπ
  set c' : ↥C := ⟨c, hcC⟩ with hc'
  set S' := (Subgroup.centralizer ({π c'} : Set (↥C ⧸ N))).comap π with hS'
  refine ⟨S'.map C.subtype, Subgroup.map_subtype_le _, fun x hxC hx => ?_, ?_⟩
  · refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, hS', Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have hmem : (⟨x, hxC⟩ : ↥C) * c' * (⟨x, hxC⟩ : ↥C)⁻¹ * c'⁻¹ ∈ N := by
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = (⟨x, hxC⟩ : ↥C) * c' * (⟨x, hxC⟩ : ↥C)⁻¹ * c'⁻¹ := Subtype.ext (by simpa using hyx)
      exact this ▸ hy
    have h1 : π ((⟨x, hxC⟩ : ↥C) * c' * (⟨x, hxC⟩ : ↥C)⁻¹ * c'⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmem
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · rintro _ ⟨x', hx', rfl⟩ k
    have hx'' : π x' ∈ Subgroup.centralizer ({π c'} : Set (↥C ⧸ N)) := hx'
    have hcomm : Commute (π x') (π c') := Subgroup.mem_centralizer_singleton_iff.mp hx''
    have hk : π ⁅x', c' ^ k⁆ = 1 := by
      simp only [commutatorElement_def, map_mul, map_inv, map_zpow]
      rw [(hcomm.zpow_right k).eq]
      group
    have hkN : ⁅x', c' ^ k⁆ ∈ N := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
      exact hk
    refine ⟨⁅x', c' ^ k⁆, hkN, ?_⟩
    simp only [commutatorElement_def, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_zpow]
    rfl

theorem card_closure_pair {x y : G} (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 := by
  have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [show ({x, y} : Set G) = {x} ∪ {y} from rfl, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute x y from hxy) i j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [inf_zpowers_eq_bot hy hyx, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
    hx, hy] at hcard
  rw [hcl, hcard]

theorem commutator_le_pPrimeCoreOf (hbal : Step143Balance) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hΩ : omegaA A = {Subgroup.zpowers c}) {a x : G} (haA : a ∈ A)
    (hac : a ∉ Subgroup.zpowers c) (hxA : x ∈ A) (hx : x ∈ Subgroup.closure {c, a})
    {P : Subgroup G} (hP : P ∈ scriptQ A (lB A))
    (hPa : P ≤ Subgroup.centralizer ({a} : Set G)) :
    ⁅P, Subgroup.zpowers x⁆ ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27'
  have hAmax := h.maximal_isElemAbelian
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ one_mem _)
  have haΩ : Subgroup.zpowers a ∉ omegaA A := by
    rw [hΩ]
    intro hmem
    apply hac
    rw [← Set.mem_singleton_iff.mp hmem]
    exact Subgroup.mem_zpowers a
  set C := Subgroup.centralizer ({a} : Set G) with hC
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hxA⟩ ⟨a, haA⟩))
  obtain ⟨S, -, hSmem, hScomm⟩ := exists_commMod C hxC
  have hNS : pPrimeCoreOf 3 C ≤ S := by
    intro n hn
    refine hSmem n (pPrimeCoreOf_le 3 C hn) ?_
    have hxN : x ∈ Subgroup.normalizer ((pPrimeCoreOf 3 C : Subgroup G) : Set G) :=
      le_normalizer_pPrimeCoreOf 3 C hxC
    have h1 : x * n⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 C :=
      (Subgroup.mem_normalizer_iff.mp hxN n⁻¹).mp (inv_mem hn)
    have : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
    rw [this]
    exact mul_mem hn h1
  have hOS : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ S := by
    intro o ho
    have hoA : o ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ ho
    refine hSmem o (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA) hoA) ?_
    rw [(Subgroup.mem_centralizer_iff.mp hoA x hxA).symm, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hP3 : ¬ 3 ∣ Nat.card P := (isPiSubgroup_piCompl_iff Nat.prime_three P).mp hP.1.2.1
  have hPS : P ≤ S := by
    refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA.1
      (by rw [hA.2]; norm_num) hP.1.2.2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3) fun H hHA hH9 => ?_
    have hH : IsHyperplane A H := ⟨hHA, by rw [hA.2, hH9]; norm_num⟩
    by_cases hxH : x ∈ H
    ·
      intro y hy
      refine hSmem y (hPa hy.1) ?_
      rw [← Subgroup.mem_centralizer_iff.mp hy.2 x hxH, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    by_cases haH : a ∈ H
    ·
      have hcH : c ∉ H := fun hcH => hxH (by
        have hle : Subgroup.closure ({c, a} : Set G) ≤ H := by
          rw [Subgroup.closure_le]
          rintro y (rfl | rfl)
          · exact hcH
          · exact haH
        exact hle hx)
      have hLH : lB A H = ⊥ := Sec14.lB_eq_bot fun b d' Lb hcfg => hcH (by
        have hb : Subgroup.zpowers b = Subgroup.zpowers c := by
          have := hcfg.2.1
          rw [hΩ] at this
          exact this
        rw [hcfg.1]
        exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert b {d'})))
          (hb ▸ Subgroup.mem_zpowers c))
      have h2 := hP.2 H hH
      rw [qBound, hLH, sup_bot_eq] at h2
      exact h2.trans (sup_le ((Sec14.pPrimeCoreOf_centralizer_le_sup hA hAmax hHA
        (Sec14.commutator_pPrimeCoreOf_le hbal h haA ha1 haΩ hH haH)).trans
          (sup_le hNS hOS)) hOS)
    ·
      have hAle := Sec14.le_sup_zpowers_of_not_mem hA hH haA haH
      intro y hy
      have hyA : y ∈ Subgroup.centralizer (A : Set G) :=
        Sec14.mem_centralizer_of_le_sup hAle hy.2 (hPa hy.1)
      refine hSmem y (hPa hy.1) ?_
      rw [← Subgroup.mem_centralizer_iff.mp hyA x hxA, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  rw [Subgroup.commutator_le]
  intro y hy z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact hScomm y (hPS hy) k

end Proof176Steps

end CFSG.RankThree.PartTwo.Sec17
