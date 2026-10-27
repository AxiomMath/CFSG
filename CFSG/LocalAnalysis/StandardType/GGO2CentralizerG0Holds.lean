module

public import CFSG.LieType.ChevTwo.Main
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVInputs
public import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
public import CFSG.LocalAnalysis.StandardType.GGOuterInvFieldTags

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggChevTwo_pCoreOf_inf_centralizer_eq_bot {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {G₀ : Subgroup X} (hG₀ : IsSimpleGroup ↥G₀)
    (hna : ∃ a b : ↥G₀, a * b ≠ b * a)
    (hC : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo ↥G₀)
    {b : X} (hbN : b ∈ Subgroup.normalizer (G₀ : Set X)) (hbp : b ^ p = 1) :
    pCoreOf 2 (G₀ ⊓ Subgroup.centralizer {b}) = ⊥ := by
  have hAN : Subgroup.zpowers b ≤ Subgroup.normalizer (G₀ : Set X) :=
    (Subgroup.zpowers_le).2 hbN
  let φ : ↥(Subgroup.zpowers b) →* MulAut ↥G₀ :=
    (Subgroup.normalizerMonoidHom (H := G₀)).comp (Subgroup.inclusion hAN)
  have hφ : ∀ (a : ↥(Subgroup.zpowers b)) (g : ↥G₀),
      ((φ a) g : X) = (a : X) * (g : X) * (a : X)⁻¹ :=
    fun a g => Subgroup.normalizerMonoidHom_apply_apply_coe G₀ (Subgroup.inclusion hAN a) g
  haveI : Fact p.Prime := ⟨hp⟩
  have hR : IsPGroup p φ.range :=
    (IsElemAbelian.isPGroup (isElemAbelian_zpowers hbp)).of_surjective φ.rangeRestrict
      φ.rangeRestrict_surjective
  have h0 := CFSG.LieType.ChevTwo.chev2CoreCent_of_leaves ↥G₀ hG₀ hna hC p hp hp2 φ.range hR
  have hmap : (CFSG.LieType.ChevTwo.autCentralizer φ.range).map G₀.subtype =
      G₀ ⊓ Subgroup.centralizer {b} := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, ?_⟩
      have hfix := hh (φ ⟨b, Subgroup.mem_zpowers b⟩) (MonoidHom.mem_range.2 ⟨_, rfl⟩)
      have h1 : b * (h : X) * b⁻¹ = (h : X) := by simpa [hφ] using congrArg Subtype.val hfix
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      calc b * (h : X) = (b * (h : X) * b⁻¹) * b := by group
        _ = (h : X) * b := by rw [h1]
    · rintro ⟨hgG, hgC⟩
      refine ⟨⟨g, hgG⟩, ?_, rfl⟩
      rintro α ⟨a, rfl⟩
      have hgb : b * g = g * b := (Subgroup.mem_centralizer_iff.1 hgC b rfl)
      have hb : b ∈ Subgroup.centralizer {g} :=
        Subgroup.mem_centralizer_iff.2 fun y hy => by
          rw [Set.mem_singleton_iff.1 hy]; exact hgb.symm
      have ha : (a : X) ∈ Subgroup.centralizer {g} := (Subgroup.zpowers_le.2 hb) a.2
      have hag : g * (a : X) = (a : X) * g := Subgroup.mem_centralizer_iff.1 ha g rfl
      apply Subtype.ext
      rw [hφ]
      change (a : X) * g * (a : X)⁻¹ = g
      rw [← hag]
      group
  rw [← hmap, CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 G₀.subtype G₀.subtype_injective, h0,
    Subgroup.map_bot]

theorem ggG0_pCoreOf_two_centralizer_eq_bot {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {b : G}
    (hbN : b ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)) (hbr : b ^ r = 1) :
    pCoreOf 2 (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥ := by
  obtain ⟨hsimp, -, hM⟩ := ggIVFlatData_of_ctx hctx s1
  haveI := hsimp
  have hnc : ∃ a b : ↥(ggG0 p B x L D J), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hbot : commutator ↥(ggG0 p B x L D J) = ⊥ := by
      rw [eq_bot_iff, commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact h a b
    rw [hM.1] at hbot
    exact top_ne_bot hbot
  have hcenter : Subgroup.center ↥(ggG0 p B x L D J) = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥(ggG0 p B x L D J)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have ha : a ∈ Subgroup.center ↥(ggG0 p B x L D J) := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  exact ggChevTwo_pCoreOf_inf_centralizer_eq_bot hr hr2 hsimp hnc
    (isChevTwo_of_largeEvenMarking_of_center_eq_bot hM hcenter) hbN hbr

theorem ggO2CentralizerG0At_holds
    (t : StatedLieTag) : GGO2CentralizerG0At t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b hb _
  exact ggG0_pCoreOf_two_centralizer_eq_bot hctx s1 hctx.prime hctx.ne_two
    (hctx.bstar_le_normalizer hb) (hctx.bstar.2.1.2 b hb)

end CFSG.StandardType
