module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.Quasithin.Background.C124Perf
public import CFSG.GroupTheory.TwoResidualOddOrder
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

@[expose] def W4Lem13_6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y : Subgroup (MulAut W), CFSG.Open.IsKGroup ↥Y →
      (∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥) →
      IsBasicModule Y →
      ∀ t ∈ Y, orderOf t = 2 → rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
        ∃ L : Subgroup (MulAut W), Conc4_136W Y t L

section Shape

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}
  {L : Subgroup (MulAut W)}

private theorem isQuasisimple_of_open {Q : Type*} [Group Q]
    (h : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

private theorem commutator_eq_self_of_open_isQuasisimple {G : Type*} [Group G] {L : Subgroup G}
    (h : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h.1] at h1
  rw [← h1, Subgroup.map_top, Subgroup.range_subtype]

private theorem twoResidual_eq_self_of_odd_card {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (h : Odd (Nat.card L)) : twoResidual L = L :=
  le_antisymm (twoResidual_le L) (CFSG.GroupTheory.le_twoResidual_of_odd_card le_rfl h)

private theorem twoResidual_eq_self_of_perfect' {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (h : ⁅L, L⁆ = L) : twoResidual L = L :=
  CFSG.Quasithin.C124.twoResidual_eq_self_of_perfect' h

private theorem natCard_of_isElemAbelianOfRank {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (Multiplicative.ofAdd (α := Fin n → ZMod p)),
    Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem genFittingFStar_eq_top_of_nilpotent {G : Type*} [Group G]
    [Group.IsNilpotent G] : CFSG.Open.genFittingFStar G = ⊤ := by
  have hfit : CFSG.Open.genFittingFitting G = ⊤ := CFSG.fitting_eq_top_of_nilpotent G
  rw [CFSG.Open.genFittingFStar.eq_sup, hfit, top_sup_eq]

private theorem genFittingFStar_eq_top_of_open_isQuasisimple {G : Type*} [Group G]
    (h : CFSG.Open.IsQuasisimple G) : CFSG.Open.genFittingFStar G = ⊤ := by
  have htop : CFSG.Open.IsComponentOf (⊤ : Subgroup G) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.refl ⊤,
      h.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)⟩
  have hlayer : CFSG.Open.genFittingLayer G = ⊤ := by
    rw [CFSG.Open.genFittingLayer.eq_sSup]
    exact top_le_iff.mp (le_sSup htop)
  rw [CFSG.Open.genFittingFStar.eq_sup, hlayer, sup_top_eq]

private theorem fstar_eq_self_of_genFittingFStar_eq_top {G : Type} [Group G] {L : Subgroup G}
    (h : CFSG.Open.genFittingFStar ↥L = ⊤) : Fstar L = L := by
  rw [Fstar, h, Subgroup.map_top, Subgroup.range_subtype]

private theorem ne_bot_of_isComponentOf {G : Type*} [Group G] {L A : Subgroup G}
    (h : CFSG.Open.IsComponentOf L A) : L ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot L).mp
    (CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_of_open h.2.2))

theorem Conc4_136W.le (h : Conc4_136W A t L) : L ≤ A := by
  rcases h with ⟨-, -, hC1 | ⟨K, hK, g, hg, -, rfl, -⟩ | ⟨hL, -⟩ | ⟨-, -, hL, -⟩⟩
  · obtain ⟨p, hp, hLp, -⟩ := hC1
    exact hLp.trans (Subgroup.map_subtype_le (CFSG.pCore p A))
  · refine sup_le hK.1 ?_
    rintro x ⟨k, hk, rfl⟩
    change (MulAut.conj g) k ∈ A
    rw [MulAut.conj_apply]
    exact A.mul_mem (A.mul_mem hg (hK.1 hk)) (A.inv_mem hg)
  · exact hL.1
  · exact hL.1

theorem Conc4_136W.ne_bot (h : Conc4_136W A t L) : L ≠ ⊥ := by
  rcases h with ⟨-, -, hC1 | ⟨K, hK, -, -, -, rfl, -⟩ | ⟨hL, -⟩ | ⟨-, -, hL, -⟩⟩
  · obtain ⟨p, hp, -, hne, -, -⟩ := hC1
    intro hbot
    exact hne (by rw [hbot, Subgroup.commutator_bot_left])
  · intro hbot
    exact ne_bot_of_isComponentOf hK (le_bot_iff.mp (hbot ▸ le_sup_left))
  · exact ne_bot_of_isComponentOf hL
  · exact ne_bot_of_isComponentOf hL

theorem Conc4_136W.twoResidual_eq (h : Conc4_136W A t L) : twoResidual L = L := by
  rcases h with ⟨-, -, hC1 | ⟨K, hK, g, -, -, rfl, -⟩ | ⟨hL, -⟩ | ⟨-, -, hL, -⟩⟩
  · obtain ⟨p, hp, -, -, -, hcases⟩ := hC1
    exact twoResidual_eq_self_of_odd_card (by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨h12, -⟩ | ⟨hea, -⟩ | ⟨hc, -⟩ |
        ⟨r, m, hpm, -, hea, -⟩ | ⟨hea, -⟩
      · rw [hc.2]; decide
      · rw [hc.2]; decide
      · rw [h12.2.1]; decide
      · rw [natCard_of_isElemAbelianOfRank hea]; decide
      · rw [hc.2]; decide
      · rw [natCard_of_isElemAbelianOfRank hea]
        rcases hpm with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact Odd.pow (by decide)
      · rw [natCard_of_isElemAbelianOfRank hea]; decide)
  · let K' : Subgroup (MulAut W) := K.map (MulAut.conj g).toMonoidHom
    show twoResidual (K ⊔ K') = K ⊔ K'
    have hKperf : ⁅K, K⁆ = K := commutator_eq_self_of_open_isQuasisimple hK.2.2
    have hK'perf : ⁅K', K'⁆ = K' := by
      show ⁅K', K'⁆ = K'
      rw [← Subgroup.map_commutator, hKperf]
    refine twoResidual_eq_self_of_perfect' (le_antisymm (Subgroup.commutator_le_self _) ?_)
    exact sup_le
      (hKperf.symm.le.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
      (hK'perf.symm.le.trans (Subgroup.commutator_mono le_sup_right le_sup_right))
  · exact twoResidual_eq_self_of_perfect' (commutator_eq_self_of_open_isQuasisimple hL.2.2)
  · exact twoResidual_eq_self_of_perfect' (commutator_eq_self_of_open_isQuasisimple hL.2.2)

theorem Conc4_136W.fstar_eq (h : Conc4_136W A t L) : Fstar L = L := by
  rcases h with ⟨-, -, hC1 | ⟨K, hK, g, hg, hne, rfl, -⟩ | ⟨hL, -⟩ | ⟨-, -, hL, -⟩⟩
  · obtain ⟨p, hp, hLp, -⟩ := hC1
    haveI : Fact p.Prime := ⟨hp⟩
    have hcore : IsPGroup p (CFSG.Open.pCoreOf p A) := by
      show IsPGroup p ((CFSG.pCore p A).map A.subtype)
      exact IsPGroup.map (CFSG.pCore_isPGroup (p := p) (G := A)) A.subtype
    haveI : Group.IsNilpotent ↥L := (hcore.to_le hLp).isNilpotent
    exact fstar_eq_self_of_genFittingFStar_eq_top
      (genFittingFStar_eq_top_of_nilpotent (G := ↥L))
  · let K' : Subgroup (MulAut W) := K.map (MulAut.conj g).toMonoidHom
    show Fstar (K ⊔ K') = K ⊔ K'
    have hK'comp : CFSG.Open.IsComponentOf K' A :=
      CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK hg
    have hcomm : ⁅K, K'⁆ = ⊥ :=
      CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hK hK'comp hne
    have hKle : K ≤ Subgroup.normalizer (K : Set (MulAut W)) := Subgroup.le_normalizer
    have hcent : K' ≤ Subgroup.centralizer (K : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((Subgroup.commutator_comm K K').symm.trans hcomm)
    have hK'le : K' ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
      hcent.trans (Subgroup.centralizer_le_normalizer (K : Set (MulAut W)))
    have hKnormal : (K.subgroupOf (K ⊔ K')).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le hKle hK'le)
    have hKsub : CFSG.Open.IsSubnormal K (K ⊔ K') :=
      CFSG.Open.IsSubnormal.step le_sup_left hKnormal (CFSG.Open.IsSubnormal.refl _)
    have hKtop : CFSG.Open.IsComponentOf (K.subgroupOf (K ⊔ K')) ⊤ :=
      (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf le_sup_left).mp
        ⟨le_sup_left, hKsub, hK.2.2⟩
    have hcent' : K ≤ Subgroup.centralizer (K' : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hKle' : K ≤ Subgroup.normalizer (K' : Set (MulAut W)) :=
      hcent'.trans (Subgroup.centralizer_le_normalizer (K' : Set (MulAut W)))
    have hK'le' : K' ≤ Subgroup.normalizer (K' : Set (MulAut W)) := Subgroup.le_normalizer
    have hK'normal : (K'.subgroupOf (K ⊔ K')).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sup_le hKle' hK'le')
    have hK'sub : CFSG.Open.IsSubnormal K' (K ⊔ K') :=
      CFSG.Open.IsSubnormal.step le_sup_right hK'normal (CFSG.Open.IsSubnormal.refl _)
    have hK'top : CFSG.Open.IsComponentOf (K'.subgroupOf (K ⊔ K')) ⊤ :=
      (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf le_sup_right).mp
        ⟨le_sup_right, hK'sub, hK'comp.2.2⟩
    have hsup : K.subgroupOf (K ⊔ K') ⊔ K'.subgroupOf (K ⊔ K') = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hlayer : CFSG.Open.genFittingLayer ↥(K ⊔ K') = ⊤ := by
      rw [CFSG.Open.genFittingLayer.eq_sSup]
      exact top_le_iff.mp
        (le_trans (le_of_eq hsup.symm) (sup_le (le_sSup hKtop) (le_sSup hK'top)))
    have htop : CFSG.Open.genFittingFStar ↥(K ⊔ K') = ⊤ := by
      rw [CFSG.Open.genFittingFStar.eq_sup, hlayer, sup_top_eq]
    exact fstar_eq_self_of_genFittingFStar_eq_top htop
  · exact fstar_eq_self_of_genFittingFStar_eq_top
      (genFittingFStar_eq_top_of_open_isQuasisimple hL.2.2)
  · exact fstar_eq_self_of_genFittingFStar_eq_top
      (genFittingFStar_eq_top_of_open_isQuasisimple hL.2.2)

end Shape

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
