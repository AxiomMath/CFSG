module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12
public import CFSG.LocalAnalysis.WeakClosure81.W19Fstar
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

theorem pRank_coe_mono {p : ℕ} (hp : 1 < p) {A B : Subgroup G} (h : A ≤ B) :
    CFSG.pRank p ↥A ≤ CFSG.pRank p ↥B := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact CFSG.SectionRank.pRank_mono hp h

structure Hyp183 (D : Data G) (V₀ V H : Subgroup G) (i : ℕ) : Prop where
  setting : WeakClosureSetting D V₀ V
  ne_bot : V₀ ≠ ⊥
  hyp171 : W3Hyp171 D H
  i_le : i ≤ 1
  normW : normalizer (E3.wClos V i D.T : Set G) ≤ D.M
  notLe : ¬ H ≤ D.M

@[expose] def Concl181 (D : Data G) (V₀ V H : Subgroup G) : Prop :=
  W3Hyp181 D H → MBarGT D.M V₀ V 2 → HasCompFactor H IsCalL1

@[expose] def Concl182 (D : Data G) (V₀ V H : Subgroup G) (i : ℕ) : Prop :=
  W3Hyp182 D H → MBarGT D.M V₀ V (i + 2) → HasCompFactor H IsCalL0

theorem not_concl181_iff {D : Data G} {V₀ V H : Subgroup G} :
    ¬ Concl181 D V₀ V H ↔ W3Hyp181 D H ∧ MBarGT D.M V₀ V 2 ∧ ¬ HasCompFactor H IsCalL1 := by
  unfold Concl181
  tauto

theorem not_concl182_iff {D : Data G} {V₀ V H : Subgroup G} {i : ℕ} :
    ¬ Concl182 D V₀ V H i ↔
      W3Hyp182 D H ∧ MBarGT D.M V₀ V (i + 2) ∧ ¬ HasCompFactor H IsCalL0 := by
  unfold Concl182
  tauto

structure MinCex183 (D : Data G) (V₀ V H : Subgroup G) (i : ℕ) : Prop where
  hyp : Hyp183 D V₀ V H i
  fail : ¬ (Concl181 D V₀ V H ∧ Concl182 D V₀ V H i)
  min : ∀ (H' : Subgroup G) (i' : ℕ), Hyp183 D V₀ V H' i' →
    ¬ (Concl181 D V₀ V H' ∧ Concl182 D V₀ V H' i') → Nat.card H ≤ Nat.card H'

namespace Hyp183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem isSylowIn_T (h : Hyp183 D V₀ V H i) : IsSylowIn 2 D.T H := by
  have hT : IsSylowIn 2 D.T ⊤ := isSylowOf_two_iff_isSylowIn.mp D.sylowG
  exact isSylowIn_of_le_of_le hT h.hyp171.2.1 le_top

theorem T_lt (h : Hyp183 D V₀ V H i) : D.T < H :=
  lt_of_le_of_ne h.hyp171.2.1 fun heq => h.notLe (heq ▸ D.sylowM.le)

theorem pCoreOf_le_T (h : Hyp183 D V₀ V H i) : pCoreOf 2 H ≤ D.T :=
  E1.pCoreOf_two_le_of_isSylowIn h.isSylowIn_T

theorem ne_top (h : Hyp183 D V₀ V H i) : H ≠ ⊤ := by
  intro htop
  have hF := h.hyp171.1
  subst htop
  haveI := D.standing.simple
  have hF' : (CFSG.generalizedFitting ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype =
      pCoreOf 2 (⊤ : Subgroup G) := by
    rw [← hF]
    unfold Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations]
  have hcen : (⊤ : Subgroup G) ⊓ Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup G) : Set G) ≤
      pCoreOf 2 (⊤ : Subgroup G) := by
    rintro y ⟨hyH, hyc⟩
    have hc : (⟨y, hyH⟩ : ↥(⊤ : Subgroup G)) ∈ Subgroup.centralizer
        (CFSG.generalizedFitting ↥(⊤ : Subgroup G) : Set ↥(⊤ : Subgroup G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : (w : G) ∈ pCoreOf 2 (⊤ : Subgroup G) := by
        rw [← hF']
        exact Subgroup.mem_map_of_mem _ hw
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hyc) _ hw')
    have := CFSG.centralizer_generalizedFitting_le ↥(⊤ : Subgroup G) hc
    rw [← hF']
    exact ⟨_, this, rfl⟩
  have hnorm : (pCoreOf 2 (⊤ : Subgroup G)).Normal :=
    ⟨fun n hn g => by
      have hg := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup G)
        (Subgroup.mem_top g)
      have := (Subgroup.mem_normalizer_iff.1 hg n).1 hn
      simpa using this⟩
  obtain ⟨a, b, hab⟩ := D.standing.nonab
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCoreOf 2 (⊤ : Subgroup G)) with hbot | htopp
  · rw [hbot] at hcen
    have hcent : a ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have : x = 1 := by simpa using hx
      rw [this]
      simp
    have ha : a ∈ (⊥ : Subgroup G) := hcen ⟨Subgroup.mem_top a, hcent⟩
    have ha1 : a = 1 := by simpa using ha
    exact hab (by rw [ha1]; simp)
  · have hP : IsPGroup 2 G := by
      have := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup G)
      rw [htopp] at this
      exact (IsPGroup.of_equiv this (Subgroup.topEquiv))
    haveI : Nontrivial G := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    haveI := hP.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · exact absurd hc (Subgroup.nontrivial_iff_ne_bot _ |>.mp this)
    · exact hab (by
        have : a ∈ Subgroup.center G := by rw [hc]; trivial
        exact ((Subgroup.mem_center_iff.mp this) b).symm)

theorem kgroup (h : Hyp183 D V₀ V H i) : CFSG.Open.IsKGroup ↥H :=
  D.standing.kProper.isKGroup H h.ne_top

theorem of_le (h : Hyp183 D V₀ V H i) {X : Subgroup G} (hTX : D.T ≤ X) (hXH : X ≤ H)
    (hXM : ¬ X ≤ D.M) : Hyp183 D V₀ V X i where
  setting := h.setting
  ne_bot := h.ne_bot
  hyp171 := ⟨fstar_eq_pCoreOf_of_le hXH (h.pCoreOf_le_T.trans hTX) h.hyp171.1, hTX,
    fun p hp hp2 hX g => by
      have hH : 3 < CFSG.pRank p ↥H := lt_of_lt_of_le hX (pRank_coe_mono hp.one_lt hXH)
      exact (pRank_coe_mono hp.one_lt (inf_le_inf_right _ hXH)).trans
        (h.hyp171.2.2 p hp hp2 hH g)⟩
  i_le := h.i_le
  normW := h.normW
  notLe := hXM

end Hyp183

theorem W3Hyp181.of_le {D : Data G} {H X : Subgroup G} (h : W3Hyp181 D H) (hXH : X ≤ H) :
    W3Hyp181 D X :=
  ⟨(pRank_coe_mono (p := 3) (by norm_num) hXH).trans h.1, h.2⟩

theorem W3Hyp182.of_le {D : Data G} {H X : Subgroup G} (h : W3Hyp182 D H) (hXH : X ≤ H) :
    W3Hyp182 D X :=
  ⟨(pRank_coe_mono (p := 3) (by norm_num) hXH).trans h.1,
    fun p hp hp2 hX => (pRank_coe_mono hp.one_lt (inf_le_inf_right _ hXH)).trans
      (h.2 p hp hp2 (lt_of_lt_of_le hX (pRank_coe_mono hp.one_lt hXH)))⟩

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem concl_of_lt (h : MinCex183 D V₀ V H i) {X : Subgroup G} (hX : Hyp183 D V₀ V X i)
    (hXH : X < H) : Concl181 D V₀ V X ∧ Concl182 D V₀ V X i := by
  by_contra hfail
  exact absurd (Subgroup.card_lt_of_lt hXH) (not_lt.mpr (h.min X i hX hfail))

end MinCex183

theorem exists_minCex183 {D : Data G} {V₀ V H : Subgroup G} {i : ℕ} (h : Hyp183 D V₀ V H i)
    (hfail : ¬ (Concl181 D V₀ V H ∧ Concl182 D V₀ V H i)) :
    ∃ (H' : Subgroup G) (i' : ℕ), MinCex183 D V₀ V H' i' := by
  classical
  have hex : ∃ n, ∃ (H' : Subgroup G) (i' : ℕ), Hyp183 D V₀ V H' i' ∧
      ¬ (Concl181 D V₀ V H' ∧ Concl182 D V₀ V H' i') ∧ Nat.card H' = n :=
    ⟨_, H, i, h, hfail, rfl⟩
  obtain ⟨H', i', h1, h2, h3⟩ := Nat.find_spec hex
  refine ⟨H', i', h1, h2, fun H'' i'' hh hf => ?_⟩
  rw [h3]
  exact Nat.find_min' hex ⟨H'', i'', hh, hf, rfl⟩

theorem w3Thm183_of_no_minCex (h : ∀ (D : Data G) (V₀ V H : Subgroup G) (i : ℕ),
    ¬ MinCex183 D V₀ V H i) : W3Thm183 G := by
  intro D V₀ V hset hV₀ H hH i hi hN hnot
  by_contra hfail
  have hyp : Hyp183 D V₀ V H i := ⟨hset, hV₀, hH, hi, hN, hnot⟩
  obtain ⟨H', i', hmin⟩ := exists_minCex183 hyp hfail
  exact h D V₀ V H' i' hmin

end CFSG.LocalAnalysis.WeakClosure81

end
