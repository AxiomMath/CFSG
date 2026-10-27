module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenActorTools
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4Noninner
public import CFSG.RankThree.Chevalley.SteinbergCEF4PlaneAssembly
public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace F4Nonsplit

variable {G : Type*} [Group G]

theorem le_commutator_of_isComponentOf {X C : Subgroup G} (hX : IsComponentOf X C) :
    X ≤ ⁅C, C⁆ := by
  have h := congrArg (Subgroup.map X.subtype) hX.2.2.1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  calc X = ⁅X, X⁆ := h.symm
    _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hX.1 hX.1

theorem ne_bot_of_isComponentOf {X C : Subgroup G} (hX : IsComponentOf X C) : X ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot X).1 (CFSG.LocalCores.isQuasisimple_nontrivial
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hX.2.2))

theorem not_isComponentOf_of_commutator_eq_bot {X C : Subgroup G} (h : ⁅C, C⁆ = ⊥) :
    ¬ IsComponentOf X C := fun hX =>
  ne_bot_of_isComponentOf hX (le_bot_iff.mp (h ▸ le_commutator_of_isComponentOf hX))

theorem not_isComponentOf_of_commute {X C : Subgroup G}
    (h : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) : ¬ IsComponentOf X C :=
  not_isComponentOf_of_commutator_eq_bot (Subgroup.commutator_eq_bot_iff_le_centralizer.2
    fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => h b hb a ha)

theorem commutator_le_self (C : Subgroup G) : ⁅C, C⁆ ≤ C :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commutator_subgroupOf_normal (C : Subgroup G) : (⁅C, C⁆.subgroupOf C).Normal := by
  have e : ⁅C, C⁆.subgroupOf C = ⁅(⊤ : Subgroup C), ⊤⁆ := by
    have h1 : ⁅C, C⁆ = Subgroup.map C.subtype ⁅(⊤ : Subgroup C), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map C.subtype, Subgroup.range_subtype]
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [e]
  infer_instance

theorem eq_commutator_of_isComponentOf [Finite G] {X C : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥⁅C, C⁆) (hX : IsComponentOf X C) : X = ⁅C, C⁆ := by
  have hRc : IsComponentOf ⁅C, C⁆ C :=
    ⟨commutator_le_self C, IsSubnormal.step (commutator_le_self C) (commutator_subgroupOf_normal C)
      (IsSubnormal.refl C),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq⟩
  exact CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hX hRc
    (le_commutator_of_isComponentOf hX)

theorem dvd_card_of_isComponentOf_of_quasisimple [Finite G] {p : ℕ} {X C : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥⁅C, C⁆) (hp : p ∣ Nat.card ↥⁅C, C⁆) (hX : IsComponentOf X C) :
    p ∣ Nat.card X := by
  rw [eq_commutator_of_isComponentOf hq hX]
  exact hp

theorem dvd_card_of_isComponentOf_of_map_eq [Finite G] {M : Type*} [Group M] {ι : G →* M}
    {ψ : M →* M} (hι : Function.Injective ι) (hψ : Function.Injective ψ) {C : Subgroup G}
    {D : Subgroup M} (hCD : C.map ι = D.map ψ) (hq : CFSG.IsQuasisimple ↥⁅D, D⁆) {p : ℕ}
    (hp : p ∣ Nat.card ↥⁅D, D⁆) {X : Subgroup G} (hX : IsComponentOf X C) : p ∣ Nat.card X := by
  obtain ⟨hR, hqR, -, -⟩ := CFSG.RankThree.Chevalley.EvenF4Actors.transport_derived hι hψ hCD
  have hcard : Nat.card ↥⁅C, C⁆ = Nat.card ↥⁅D, D⁆ := by
    rw [← Subgroup.card_map_of_injective hι, hR, Subgroup.card_map_of_injective hψ]
  exact dvd_card_of_isComponentOf_of_quasisimple (hqR hq).1 (hcard ▸ hp) hX

theorem isQuasisimple_of_isSimpleGroup {R : Type*} [Group R] (hs : IsSimpleGroup R)
    (hperf : Group.IsPerfect R) (hnc : ∃ a b : R, a * b ≠ b * a) : CFSG.IsQuasisimple R := by
  have := hs
  have hs': IsSimpleGroup (R ⧸ (⊥ : Subgroup R)) := by
    have : Nontrivial (R ⧸ (⊥ : Subgroup R)) :=
      QuotientGroup.quotientBot.symm.injective.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective (QuotientGroup.mk' (⊥ : Subgroup R))
      (QuotientGroup.mk'_surjective _)
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient (⊥ : Subgroup R) bot_le
    hperf hs' ?_
  obtain ⟨x, y, hxy⟩ := hnc
  refine ⟨x, y, fun h => hxy ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_bot,
    inv_mul_eq_one] at h
  exact h

end F4Nonsplit

end CFSG.StandardType
