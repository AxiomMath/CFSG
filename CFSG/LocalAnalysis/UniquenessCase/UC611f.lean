module

public import CFSG.LocalAnalysis.UniquenessCase.UC611b
public import CFSG.LocalAnalysis.UniquenessCase.UC611c
public import CFSG.LocalAnalysis.UniquenessCase.UC611d
public import CFSG.LocalAnalysis.UniquenessCase.UC611e
public import CFSG.LocalAnalysis.UniquenessCase.UC611a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.GroupTheory.Gorenstein.MaxOrderThompson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

variable {G : Type} [Group G] [Finite G]

theorem r6_11Used_of_sig3_eq_empty {D : Data G} (h : D.sig3 = ∅) : R6_11Used D := fun h3 => by
  rw [h] at h3
  exact absurd h3 (Set.notMem_empty _)

structure Sigma3Std (D : Data G) : Prop where
  exists_clauseC : 3 ∈ D.sig3 → ∃ Q : Subgroup G, IsSylowOf 3 Q D.M ∧ rankThreeClauseC D.M Q

theorem sigma3Std_of_eq (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G) (D : Data G)
    (h : D.sig3 = sigmaThreeOf D.M) : Sigma3Std D where
  exists_clauseC h3 := by
    rw [h] at h3
    obtain ⟨-, hq, Q, hw, hc⟩ := h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨(Q : Subgroup G), uc22p22q_isSylowOf_of_sylow Q (hw.sylow_le hS hq), hc⟩

theorem r6_11Used_of (D : Data G) (hstd : Sigma23Std D) (hs3 : Sigma3Std D) (h61 : R6_1 D) :
    R6_11Used D := by
  intro h3 P hP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpσ : 3 ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inr h3
  obtain ⟨Q₀, hQ₀, hc₀⟩ := hs3.exists_clauseC h3
  have hc := uc611_clauseC_of_sylow hQ₀ hP hc₀
  obtain ⟨hsolv, ⟨e⟩, hΓ, -⟩ := id hc
  have hP3 : IsPGroup 3 ↥P := hP.isPGroup
  have hPM : P ≤ D.M := hP.le
  have h3' : ∀ Y : Subgroup G, Y ≤ thompsonSubgroup P → Y ≠ ⊥ → InU D.M Y := by
    intro Y hY hY0
    by_cases hΓP : rankThreeGamma 1 3 P ≤ D.M
    · exact uc611_inU_of_stronglyEmbedded D hstd hpσ hP hΓP
        ((hY.trans (CFSG.Open.thompsonSubgroup_le_self P)).trans hPM)
        (hP3.to_le (hY.trans (CFSG.Open.thompsonSubgroup_le_self P))) hY0
    · have hC : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ thompsonSubgroup P →
          ¬ centralizer (X : Set G) ≤ D.M := fun X hXP hX3 hXA =>
        uc611_not_centralizer_le D h61 hpσ hP e hΓ hΓP hXP hX3 hXA
      exact uc611_inU_thompson D hstd hpσ hP e hΓ (uc611_stronglyClosed D h61 hpσ hP e hΓ hC) hY hY0
  obtain ⟨y, hyP, hy3, hyJ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_orderOf_eq_three_not_mem_thompsonSubgroup e
  refine ⟨⟨e⟩, ⟨hsolv, hΓ⟩, h3', ?_, ?_⟩
  ·
    intro Q hQ hPQ S hSQ hSc hPS b hb s hs
    have hQ2 : IsPGroup 2 ↥Q := hQ.isPGroup
    have hXP : zpowers y ≤ P := (Subgroup.zpowers_le).2 hyP
    have hX3 : Nat.card ↥(zpowers y) = 3 := by rw [Nat.card_zpowers, hy3]
    have hXA : ¬ zpowers y ≤ thompsonSubgroup P := fun h => hyJ (h (Subgroup.mem_zpowers y))
    obtain ⟨n, -, hn⟩ := uc611_clauseC_at hc hQ hPQ hXP hX3 hXA
    have hfaith := uc611_inf_centralizer_Q D hP3 hPM hQ
    have hnt := uc611_comm_ne_one e hQ2 hPQ hfaith hXP hX3 hXA
    exact uc611_B_centralizes e hQ2 hPQ hSQ hSc hPS hXP hX3 hXA hn hnt b hb s hs
  ·
    intro X Q hXP hX3 hXA hQ hPQ
    have hQ2 : IsPGroup 2 ↥Q := hQ.isPGroup
    obtain ⟨n, hn1, hn⟩ := uc611_clauseC_at hc hQ hPQ hXP hX3 hXA
    have hnt := uc611_comm_ne_one e hQ2 hPQ (uc611_inf_centralizer_Q D hP3 hPM hQ) hXP hX3 hXA
    set Zs : Subgroup G := (Subgroup.center ↥P).map P.subtype with hZs
    have hZcard : Nat.card ↥Zs = 3 := by
      rw [hZs, Subgroup.card_map_of_injective P.subtype_injective]
      exact uc611_card_center e
    haveI : IsCyclic ↥Zs := isCyclic_of_prime_card hZcard
    obtain ⟨⟨z, hzZ⟩, hg⟩ := IsCyclic.exists_generator (α := ↥Zs)
    have hZeq : Zs = zpowers z := by
      ext w
      constructor
      · intro hw
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨w, hw⟩)
        exact Subgroup.mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩
      · intro hw
        exact (Subgroup.zpowers_le (H := Zs)).2 hzZ hw
    have hz3 : z ^ 3 = 1 := by
      have h1 := pow_card_eq_one' (x := (⟨z, hzZ⟩ : ↥Zs))
      rw [hZcard] at h1
      exact congrArg Subtype.val h1
    obtain ⟨c, hcmem, hcz⟩ := hzZ
    have hzP : z ∈ P := hcz ▸ c.2
    have hzcent : ∀ x ∈ P, z * x = x * z := by
      intro x hx
      have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hcmem) ⟨x, hx⟩)
      rw [← hcz]
      exact this.symm
    have hzR : z ∈ normalizer ((Q ⊓ centralizer (X : Set G) : Subgroup G) : Set G) :=
      uc611_mem_normalizer_inf_centralizer hPQ hXP hzP hzcent
    have hnt' : ∃ r ∈ Q ⊓ centralizer (X : Set G), z * r ≠ r * z := by
      obtain ⟨r, hr, z', hz', hne⟩ := hnt
      refine ⟨r, hr, fun hcomm => hne ?_⟩
      rw [hZeq] at hz'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
      exact (Commute.zpow_left (show Commute z r from hcomm) k).eq
    obtain ⟨hA, hB, hC⟩ := uc611_q8cc_action hn hz3 hzR hnt'
    refine ⟨n, hn1, hn, ?_, ?_, ?_⟩
    · rw [hZeq]
      exact hA
    · rw [hZeq, uc611_centralizer_zpowers_eq]
      exact hB
    · rw [hZeq, uc611_centralizer_zpowers_eq]
      exact hC

theorem r6_11Used_dataOfSetup (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G)
    (S : CFSG.LocalAnalysis.RankThreeUC.Setup G) : R6_11Used (dataOfSetup hS S) :=
  r6_11Used_of _ (sigma23Std_ofSetup hS S) (sigma3Std_of_eq hS _ rfl) (r6_1_dataOfSetup hS S)

end CFSG.LocalAnalysis.UniquenessCase.UC6
