module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Fix
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OPlane
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParC
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ClassicalMinus
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Inputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16NatU
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OChiefModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.Monster.B.TwoA.Co2Inv.Kernel
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnPre

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)

theorem exists_fixed_singular_plane_of_mem_aSet {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : ↥(⊤ : Subgroup W) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hN : NatCoordsOmegaMinusOn H ⊤ (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ)
    {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet (n + 1) H) :
    ∃ U : Submodule F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F),
      Module.finrank F U = 2 ∧ (∀ u ∈ U, StatedQuadMinus 3 F b c u = 0) ∧
      ∀ (e : MulAut W) (he : e ∈ E), ∀ u ∈ U,
        (((ε ⟨e, hE.1 he⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)).mulVec u = u := by
  classical
  haveI : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := n)
      Nat.prime_two hF
  let Q := StatedQuadMinus 3 F b c
  let φ : ↥E →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
    (Subgroup.subtype (StatedOmega Q)).comp
      (ε.toMonoidHom.comp (Subgroup.inclusion hE.1))
  have hφ_apply : ∀ e : ↥E, φ e =
      ((ε (Subgroup.inclusion hE.1 e) : ↥(StatedOmega Q)) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) := fun _ => rfl
  let E' : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) := φ.range
  have hE'2 : IsPGroup 2 E' :=
    hE.2.2.1.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hE'Ω : E' ≤ StatedOmega Q := by
    rintro g ⟨e, rfl⟩
    exact (ε (Subgroup.inclusion hE.1 e)).2
  have hΩ : StatedOmega Q ≤ CFSG.MatrixModel.isometryCore Q := by
    show ⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆ ≤ _
    exact Subgroup.commutator_le_self _
  have hE'O : ∀ g ∈ E', ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v := by
    intro g hg v
    have h :=
      CFSG.ComponentClassification.CatFC.KGHS3.isometryCore_preserves Q (hΩ (hE'Ω hg)) v
    have h' : quadMinus 3 F b c (((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)).mulVec v) = quadMinus 3 F b c v := by
      rw [coe_quadMinus]
      exact h
    simpa [gv] using h'
  obtain ⟨w, v, hw0, hli, hwq, hvq, hpol, hplane⟩ :=
    exists_fixed_plane (F := F) (b := b) (c := c) hirr hF (by omega) hE'O hE'2
  let vW : W := (ψ.symm (Multiplicative.ofAdd v)).1
  have hψv : ψ ⟨vW, Subgroup.mem_top vW⟩ = Multiplicative.ofAdd v := by
    have h : (⟨vW, Subgroup.mem_top vW⟩ : ↥(⊤ : Subgroup W)) =
        ψ.symm (Multiplicative.ofAdd v) := Subtype.ext rfl
    rw [h, MulEquiv.apply_symm_apply]
  have hψ_mul : ∀ e : ↥E,
      ψ ⟨e.1 vW, Subgroup.mem_top (e.1 vW)⟩ = Multiplicative.ofAdd (gv (φ e) v) := by
    intro e
    have h := hN (Subgroup.inclusion hE.1 e) ⟨vW, Subgroup.mem_top vW⟩
    have hto : Multiplicative.toAdd (ψ (⟨vW, Subgroup.mem_top vW⟩ : ↥(⊤ : Subgroup W))) = v := by
      rw [hψv]
      rfl
    rw [hto, ← hφ_apply e] at h
    simpa [gv] using h
  have hsub : (fun x : W => ψ ⟨x, Subgroup.mem_top x⟩) '' (MulAction.orbit ↥E vW) ⊆
      Set.range (fun t : F => Multiplicative.ofAdd (v + t • w)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨t, -, htv⟩ := hplane (φ e) (⟨e, rfl⟩)
    refine ⟨t, ?_⟩
    change Multiplicative.ofAdd (v + t • w) =
      ψ ⟨e.1 vW, Subgroup.mem_top (e.1 vW)⟩
    rw [← htv, ← hψ_mul e]
  have hcard : (MulAction.orbit ↥E vW).ncard ≤ 2 ^ n := by
    have hinj : Function.Injective (fun x : W => ψ ⟨x, Subgroup.mem_top x⟩) := by
      intro x y h
      exact congrArg Subtype.val (ψ.injective h)
    have himg : ((fun x : W => ψ ⟨x, Subgroup.mem_top x⟩) ''
        (MulAction.orbit ↥E vW)).ncard = (MulAction.orbit ↥E vW).ncard :=
      Nat.card_image_of_injective hinj _
    calc (MulAction.orbit ↥E vW).ncard
        = ((fun x : W => ψ ⟨x, Subgroup.mem_top x⟩) ''
            (MulAction.orbit ↥E vW)).ncard := himg.symm
      _ ≤ (Set.range (fun t : F => Multiplicative.ofAdd (v + t • w))).ncard :=
          Nat.card_mono (Set.finite_range _) hsub
      _ ≤ Nat.card F := Finite.card_range_le _
      _ = 2 ^ n := hF
  letI : MulAction ↥E W := MulAction.compHom W E.subtype
  have hstab : (stabAt E vW).subgroupOf E = MulAction.stabilizer ↥E vW := by
    rw [eq_comm]
    ext e
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_stabAt,
      MulAction.compHom_smul_def, MulAut.smul_def]
    exact ⟨fun h => ⟨e.2, h⟩, fun h => h.2⟩
  have hrel : (stabAt E vW).relIndex E ≤ 2 ^ n := by
    rw [Subgroup.relIndex, hstab, MulAction.index_stabilizer]
    exact hcard
  have hE2 : IsPGroup 2 E := hE.2.2.1.isPGroup
  have hm : E3.mQuot E (stabAt E vW) ≤ n := by
    rw [E3.relIndex_eq_two_pow hE2 (stabAt E vW)] at hrel
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hrel
  have hvW : vW ∈ fixV E := by
    by_contra hw
    have hge := le_mQuot_stabAt_of_mem_aSet hE hw
    omega
  have hfixw : ∀ (e : MulAut W) (he : e ∈ E),
      (((ε ⟨e, hE.1 he⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)).mulVec w = w := by
    intro e he
    have h := hplane (φ ⟨e, he⟩) ⟨⟨e, he⟩, rfl⟩
    have hinc : Subgroup.inclusion hE.1 ⟨e, he⟩ = ⟨e, hE.1 he⟩ := rfl
    rw [hφ_apply ⟨e, he⟩, hinc] at h
    simpa [gv] using h.choose_spec.1
  have hfixv : ∀ (e : MulAut W) (he : e ∈ E),
      (((ε ⟨e, hE.1 he⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)).mulVec v = v := by
    intro e he
    have h1 : e vW = vW := hvW e he
    have h := hN ⟨e, hE.1 he⟩ ⟨vW, Subgroup.mem_top vW⟩
    have hto : Multiplicative.toAdd (ψ (⟨vW, Subgroup.mem_top vW⟩ : ↥(⊤ : Subgroup W))) = v := by
      rw [hψv]
      rfl
    rw [h1, hto, hψv] at h
    exact (Multiplicative.ofAdd.injective h).symm
  refine ⟨Submodule.span F ({w, v} : Set (OW F)), finrank_span_pair hli, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, t, rfl⟩ := coeffs_of_mem_span hx
    have h := quad_span_zero hwq hvq hpol s t
    rw [coe_quadMinus] at h
    exact h
  · intro e he x hx
    obtain ⟨s, t, rfl⟩ := coeffs_of_mem_span hx
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hfixw e he, hfixv e he]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
