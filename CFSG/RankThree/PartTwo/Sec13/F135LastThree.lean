module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

theorem sl5_comm_zpow_mem_R {M : Type*} [Group M] (R : Subgroup M) [R.Normal] (k c : M)
    (hkc : k * c * k⁻¹ * c⁻¹ ∈ R) (n : ℤ) : k * c ^ n * k⁻¹ * (c ^ n)⁻¹ ∈ R := by
  have h1 : (QuotientGroup.mk' R) ⁅k, c⁆ = 1 := (QuotientGroup.eq_one_iff ⁅k, c⁆).2 hkc
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  have h2 : Commute (QuotientGroup.mk' R k) (QuotientGroup.mk' R (c ^ n)) := by
    rw [map_zpow]
    exact (show Commute (QuotientGroup.mk' R k) (QuotientGroup.mk' R c) from h1).zpow_right n
  have h3 : (QuotientGroup.mk' R) ⁅k, c ^ n⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h2
  exact (QuotientGroup.eq_one_iff ⁅k, c ^ n⁆).1 h3

theorem sl5_comm_zpow_mem_S {M : Type*} [Group M] (S K : Subgroup M)
    (hKS : ∀ k ∈ K, k ∈ normalizer (S : Set M)) (c : M) (hcS : c ∈ S) (k : M) (hk : k ∈ K)
    (n : ℤ) : k * c ^ n * k⁻¹ * (c ^ n)⁻¹ ∈ S := by
  have hcn : c ^ n ∈ S := zpow_mem hcS n
  have h1 : k * c ^ n * k⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hKS k hk) (c ^ n)).1 hcn
  exact mul_mem h1 (inv_mem hcn)

theorem sl5_isPGroup_map {M : Type*} [Group M] {p : ℕ} {S : Subgroup M} (hS : IsPGroup p S)
    (F : Subgroup S) : IsPGroup p (F.map S.subtype) := by
  intro g
  obtain ⟨f, -, hf⟩ := Subgroup.mem_map.1 g.2
  obtain ⟨k, hk⟩ := hS f
  refine ⟨k, Subtype.ext ?_⟩
  have h := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h ⊢
  rw [← hf]
  exact h

theorem sl5_pRank_map_eq {M : Type*} [Group M] [Finite M] (S : Subgroup M) (F : Subgroup S) :
    CFSG.pRank 3 ↥F = CFSG.pRank 3 ↥(F.map S.subtype) := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥F,
    CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(F.map S.subtype)]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
    (Subgroup.equivMapOfInjective F S.subtype (Subgroup.subtype_injective S))

theorem sl5_fix_comm {M : Type*} [Group M] (K S : Subgroup M)
    (hKS : K ≤ normalizer (S : Set M)) (t : K) :
    ∀ s ∈ fixedSubgroup (conjAction K S hKS t), (t : M) * (s : M) = (s : M) * (t : M) := by
  intro s hs
  have hval := congrArg Subtype.val ((mem_fixedSubgroup _ _).1 hs)
  rw [conjAction_apply] at hval
  calc (t : M) * (s : M) = (t : M) * (s : M) * (t : M)⁻¹ * (t : M) :=
        (inv_mul_cancel_right _ _).symm
    _ = (s : M) * (t : M) := by rw [hval]

theorem sl5_hrank_core {M : Type*} [Group M] [Finite M] (S : Subgroup M) (hS3 : IsPGroup 3 S)
    (x : M) (F : Subgroup S) (hF : ∀ s ∈ F, x * (s : M) = (s : M) * x)
    (hrank3 : ∀ X : Subgroup M, IsPGroup 3 X → X ≤ centralizer ({x} : Set M) →
      CFSG.pRank 3 X ≤ 3) :
    CFSG.pRank 3 ↥F ≤ 3 := by
  have hYc : F.map S.subtype ≤ centralizer ({x} : Set M) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hF s hs
  rw [sl5_pRank_map_eq S F]
  exact hrank3 (F.map S.subtype) (sl5_isPGroup_map hS3 F) hYc

theorem K_centralizes_of_centralizes_sylow {M : Type*} [Group M] (R K S : Subgroup M) [R.Normal] (c : M)
    (hKperf : ⁅K, K⁆ = K) (hKS : ∀ k ∈ K, k ∈ normalizer (S : Set M)) (hcS : c ∈ S)
    (hKc : ∀ k ∈ K, k * c * k⁻¹ * c⁻¹ ∈ R)
    (hKSR : ∀ k ∈ K, ∀ s ∈ S ⊓ R, k * s = s * k) : ∀ k ∈ K, k * c = c * k := by
  have hA : ⁅K, Subgroup.zpowers c⁆ ≤ S ⊓ R := by
    refine Subgroup.commutator_le.2 fun k hk g hg => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact Subgroup.mem_inf.2 ⟨sl5_comm_zpow_mem_S S K hKS c hcS k hk n,
      sl5_comm_zpow_mem_R R k c (hKc k hk) n⟩
  have hB : ⁅⁅K, Subgroup.zpowers c⁆, K⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.2 fun a ha k hk => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hKSR k hk a (hA ha)).symm
  have hzK : ⁅Subgroup.zpowers c, K⁆ = ⁅K, Subgroup.zpowers c⁆ :=
    Subgroup.commutator_comm _ _
  have hC : ⁅⁅Subgroup.zpowers c, K⁆, K⁆ = ⊥ := by
    rw [hzK]
    exact hB
  have hD : ⁅⁅K, K⁆, Subgroup.zpowers c⁆ = ⊥ :=
    CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma hB hC
  rw [hKperf] at hD
  intro k hk
  have hmem : ⁅k, c⁆ ∈ ⁅K, Subgroup.zpowers c⁆ :=
    Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers c)
  rw [hD, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem hrank_of_hrank3 {M : Type*} [Group M] [Finite M] (K S : Subgroup M)
    (hKS : K ≤ normalizer (S : Set M)) (hS3 : IsPGroup 3 S)
    (hrank3 : ∀ t : M, t ≠ 1 → t * t = 1 → ∀ X : Subgroup M, IsPGroup 3 X →
      X ≤ centralizer ({t} : Set M) → CFSG.pRank 3 X ≤ 3) :
    ∀ t : K, t ≠ 1 → t * t = 1 → CFSG.pRank 3 (fixedSubgroup (conjAction K S hKS t)) ≤ 3 := by
  intro t ht1 ht2
  have hx1 : (t : M) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hx2 : (t : M) * (t : M) = 1 := by
    simpa using congrArg Subtype.val ht2
  exact sl5_hrank_core S hS3 (t : M) (fixedSubgroup (conjAction K S hKS t))
    (sl5_fix_comm K S hKS t) (hrank3 (t : M) hx1 hx2)

end CFSG.RankThree.PartTwo.Sec13.F135Last
