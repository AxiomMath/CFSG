module

public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement
import CFSG.RankThree.PartTwo.Sec18.Item186Two
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_sup {K U V : Subgroup G} (hU : K ≤ Subgroup.normalizer (U : Set G))
    (hV : K ≤ Subgroup.normalizer (V : Set G)) :
    K ≤ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hU hg),
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hV hg)]

@[expose] def scriptX (A M H : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ invariantPiSubgroups ⊤ (A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)) (piCompl 3) ∧
    CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ X}

variable {A M H : Subgroup G} {c : G}

theorem isPiSubgroup_of_le {X Y : Subgroup G} (hX : IsPiSubgroup (piCompl 3) X) (hYX : Y ≤ X) :
    IsPiSubgroup (piCompl 3) Y :=
  fun p hp => hX p (hp.trans (Subgroup.card_dvd_of_le hYX))

theorem le_normalizer_pCoreOf (hH : Sec18H G A M H c) :
    A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) :=
  sup_le (Item186Proof.le_normalizer_pCoreOf_inf hH.toSec18Std hH.mem_scriptH)
    Subgroup.le_normalizer

theorem sup_mem_scriptX (hH : Sec18H G A M H c) {Y : Subgroup G}
    (hY : Y ∈ invariantPiSubgroups ⊤ (A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)) (piCompl 3)) :
    Y ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ∈ scriptX A M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hS
  obtain ⟨-, hY3, hYn⟩ := hY
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := le_sup_right.trans hYn
  refine ⟨⟨le_top, fun p hp => ?_, le_normalizer_sup hYn (le_normalizer_pCoreOf hH)⟩,
    le_sup_right⟩
  have hprod := Sec6.card_sup_mul_card_inf hSY
  rw [sup_comm] at hprod
  have hdvd : (p : ℕ) ∣ Nat.card S * Nat.card Y :=
    hprod ▸ hp.trans (Dvd.intro _ rfl)
  rcases (Nat.Prime.dvd_mul p.2).mp hdvd with h2 | h3
  ·
    have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk] at h2
    have h2' : (p : ℕ) = 2 := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp
      (p.2.dvd_of_dvd_pow h2)
    change (p : ℕ) ≠ 3
    omega
  · exact hY3 p h3

theorem normalizer_le_of_le_normalizer (h186 : Item186H) (hH : Sec18H G A M H c)
    (h187 : Hyp187 A M H c) {C : Subgroup G} (hC : C ≠ ⊥) (hCH : C ≤ H)
    (hHC : H ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  have : IsSimpleGroup G := hH.isSimpleGroup
  obtain ⟨-, -, hN, -⟩ := h186 G A M H c hH h187
  have hne : Subgroup.normalizer (C : Set G) ≠ ⊤ := by
    intro htop
    have hCn : C.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal C with h | h
    · exact hC h
    · exact hH.mem_scriptH.1 (eq_top_iff.mpr (h ▸ hCH))
  obtain ⟨Y, hY, hNY⟩ := (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hne
  have hYmem : Y ∈ scriptN (H : Set G) := ⟨hY, fun h hh => hNY (hHC hh)⟩
  rw [hN, Set.mem_singleton_iff] at hYmem
  exact hYmem ▸ hNY

structure MinCex (A M H : Subgroup G) (c : G) (X : Subgroup G) : Prop where
  sec18H : Sec18H G A M H c
  hyp187 : Hyp187 A M H c
  mem : X ∈ scriptX A M H
  not_le : ¬ X ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G)
  min : ∀ Y ∈ scriptX A M H, Y < X →
    Y ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G)

theorem item187_of_minCex
    (h : ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G) (X : Subgroup G),
      MinCex A M H c X → False) : Item187 := by
  intro G _ _ A M H c hH h187 Y hY
  by_contra hYN
  set N := Subgroup.normalizer (inSubgroup perfectResidual H : Set G) with hN
  set C := {X | X ∈ scriptX A M H ∧ ¬ X ≤ N} with hC
  have hne : (Y ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)) ∈ C :=
    ⟨sup_mem_scriptX hH hY, fun h => hYN (le_sup_left.trans h)⟩
  obtain ⟨X, ⟨hX, hXN⟩, hmin⟩ := WellFounded.has_min wellFounded_lt C ⟨_, hne⟩
  refine h G A M H c X ⟨hH, h187, hX, hXN, fun Z hZ hZX => ?_⟩
  by_contra hZN
  exact hmin Z ⟨hZ, hZN⟩ hZX

namespace MinCex

variable {X : Subgroup G}

theorem pCoreOf_le (hX : MinCex A M H c X) : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ X :=
  hX.mem.2

theorem isPiSubgroup (hX : MinCex A M H c X) : IsPiSubgroup (piCompl 3) X :=
  hX.mem.1.2.1

theorem le_normalizer (hX : MinCex A M H c X) :
    A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (X : Set G) :=
  hX.mem.1.2.2

theorem le_of_sup_ne (hX : MinCex A M H c X) {U : Subgroup G} (hUX : U ≤ X)
    (hU : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (U : Set G))
    (hne : U ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≠ X) :
    U ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  have hmem := sup_mem_scriptX hX.sec18H ⟨le_top, isPiSubgroup_of_le hX.isPiSubgroup hUX, hU⟩
  exact le_sup_left.trans (hX.min _ hmem (lt_of_le_of_ne (sup_le hUX hX.pCoreOf_le) hne))

theorem sup_eq_or_sup_eq (hX : MinCex A M H c X) {U V : Subgroup G} (hUX : U ≤ X)
    (hVX : V ≤ X)
    (hU : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (U : Set G))
    (hV : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (V : Set G))
    (hUV : U ⊔ V = X) :
    U ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) = X ∨ V ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) = X := by
  by_contra hne
  push Not at hne
  exact hX.not_le (hUV ▸ sup_le (hX.le_of_sup_ne hUX hU hne.1) (hX.le_of_sup_ne hVX hV hne.2))

theorem eq_or_eq (hX : MinCex A M H c X) {U V : Subgroup G} (hUX : U ≤ X) (hVX : V ≤ X)
    (hSU : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ U) (hSV : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ V)
    (hU : A ≤ Subgroup.normalizer (U : Set G)) (hV : A ≤ Subgroup.normalizer (V : Set G))
    (hUV : U ⊔ V = X) : U = X ∨ V = X := by
  have hU' : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (U : Set G) :=
    sup_le hU (hSU.trans Subgroup.le_normalizer)
  have hV' : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (V : Set G) :=
    sup_le hV (hSV.trans Subgroup.le_normalizer)
  rcases hX.sup_eq_or_sup_eq hUX hVX hU' hV' hUV with h | h
  · exact Or.inl ((sup_eq_left.mpr hSU).symm.trans h)
  · exact Or.inr ((sup_eq_left.mpr hSV).symm.trans h)

end MinCex

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
