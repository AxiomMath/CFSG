module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def psi {L E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (L : Set G)) : ↥E →* MulAut (Bar2 L) :=
  (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp (Subgroup.inclusion hE)

@[simp] theorem psi_apply {L E : Subgroup G} (hE : E ≤ Subgroup.normalizer (L : Set G))
    (e : ↥E) :
    psi hE e = CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L (Subgroup.inclusion hE e) :=
  rfl

theorem mem_ker_iff_centralizerBar {L E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (L : Set G)) (e : ↥E) :
    psi hE e = 1 ↔ (e : G) ∈ centralizerBar E L := by
  constructor
  · intro h
    refine mem_centralizerBar_iff.mpr ⟨e.2, ?_⟩
    intro y hy
    have h1 : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
        (Subgroup.inclusion hE e) = 1 := by
      simpa only [psi_apply] using h
    have hfix : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
        (Subgroup.inclusion hE e) (QuotientGroup.mk (⟨y, hy⟩ : ↥L)) =
        QuotientGroup.mk (⟨y, hy⟩ : ↥L) := by
      rw [h1, MulAut.one_apply]
    have hc := (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
      (Subgroup.inclusion hE e) (⟨y, hy⟩ : ↥L)).mp hfix
    rw [commutatorElement_def]
    simpa only [Subgroup.coe_inclusion] using hc
  · intro h
    ext w
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [psi_apply, MulAut.one_apply]
      refine (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
        (Subgroup.inclusion hE e) x).mpr ?_
      simpa only [commutatorElement_def, Subgroup.coe_inclusion] using
        (mem_centralizerBar_iff.mp h).2 (x : G) x.2

theorem ker_eq_centralizerBar_subgroupOf {L E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (L : Set G)) :
    (psi hE).ker = (centralizerBar E L).subgroupOf E := by
  ext e
  rw [MonoidHom.mem_ker, mem_ker_iff_centralizerBar hE e, Subgroup.mem_subgroupOf]

theorem card_centralizerBar_of_card_range {L E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (L : Set G))
    (hEcard : Nat.card E = 9)
    (hRange : Nat.card (psi hE).range = 3) :
    Nat.card (centralizerBar E L) = 3 := by
  have hker : Nat.card (psi hE).ker = Nat.card (centralizerBar E L) := by
    rw [ker_eq_centralizerBar_subgroupOf hE,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centralizerBar_le E L)).toEquiv]
  have h := Subgroup.card_ker_mul_card_range (psi hE)
  rw [hker, hRange, hEcard] at h
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
