module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGLatOrth
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsLift
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassList
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.Adapters.TauCetiExceptional.TwistedTransfer
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.SeitzReduction CFSG.TauCetiBridge.Twisted

section InvolutionsTwE6


private theorem ggInvTwE6_exists_model_frobQ {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (ψ : twistedE6Group 2 f →* G)
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ (ψbar : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G)
      (π : twistedE6Group 2 f →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      Function.Injective ψbar ∧ ψbar.range = ψ.range ∧ Function.Surjective π ∧
      π.ker = ψ.ker ∧ (∀ x, ψbar (π x) = ψ x) ∧
      (∀ z, ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((e6IsogenyT (GaloisField 2 (2 * f))
          (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) := by
  obtain ⟨π, hπ, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hπker' : π.ker = ψ.ker :=
    hπker.trans (AutSt.ker_eq_center hker hC).symm
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  let eC : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ≃*
      twistedE6Group 2 f ⧸ ψ.ker :=
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hπker')
  let ψbar : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G :=
    (QuotientGroup.kerLift ψ).comp eC.toMonoidHom
  have hcomp : ∀ x, ψbar (π x) = ψ x := by
    intro x
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π x) =
        (QuotientGroup.mk x : twistedE6Group 2 f ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ψbar, eC, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
      Function.comp_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]
  refine ⟨ψbar, π, (QuotientGroup.kerLift_injective ψ).comp eC.injective, ?_, hπ, hπker',
    hcomp, hπval⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := hπ x
    rw [hcomp]
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨π a, hcomp a⟩

private theorem ggInvTwE6_pi_xFixed {f : ℕ} (hf : 1 ≤ f)
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hπval : ∀ z, ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f))
        (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hfix : rho γ = γ) :
    ((π (xFixed (frobQ 2 f) hγ hfix 1 (map_one _) : twistedE6Group 2 f) :
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) γ 1 := by
  haveI : NeZero (2 * f) := ⟨by omega⟩
  rw [hπval]
  exact E6Pilot.coe_e6Isogeny_xm hγ 1

private theorem ggInvTwE6_pi_xPair {f : ℕ} (hf : 1 ≤ f)
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hπval : ∀ z, ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f))
        (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    (hθ : ∀ c, frobQ 2 f (frobQ 2 f c) = c)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hne : rho γ ≠ γ) :
    ((π (xPair (frobQ 2 f) hθ hγ hne 1 : twistedE6Group 2 f) :
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) γ 1 *
        pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) (rho γ) 1 := by
  haveI : NeZero (2 * f) := ⟨by omega⟩
  have hs : ((twistSign γ : ℤ) : GaloisField 2 (2 * f)) = 1 := by
    rcases twistSign_eq_one_or γ with h | h
    · rw [h, Int.cast_one]
    · rw [h, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  rw [hπval]
  change ((e6Isogeny (GaloisField 2 (2 * f))
      (e6Data_valid.xm _ γ 1 * e6Data_valid.xm _ (rho γ)
        ((twistSign γ : GaloisField 2 (2 * f)) * frobQ 2 f 1)) :
      adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) =
    pinnedX .E6 (GaloisField 2 (2 * f)) γ 1 * pinnedX .E6 (GaloisField 2 (2 * f)) (rho γ) 1
  rw [hs, map_one, one_mul, map_mul, Subgroup.coe_mul, E6Pilot.coe_e6Isogeny_xm hγ 1,
    E6Pilot.coe_e6Isogeny_xm (isRoot_rho hγ) 1]

private theorem ggInvTwE6_hrep {f : ℕ} (hf : 1 ≤ f)
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hπval : ∀ z, ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f))
        (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) :
    ∀ r ∈ twistedE6ClassReps (GaloisField 2 (2 * f)) (frobQ 2 f),
      ∃ Z : Set (Fin (Tag.rank .F4) → ℤ),
        (∃ L ∈ asClassList .twistedE6, Z = {β | List.ofFn β ∈ L}) ∧
        ∃ r' ∈ ⨆ β ∈ Z, twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) β, π r' = r := by
  have hθ : ∀ c, frobQ 2 f (frobQ 2 f c) = c := frobQ_frobQ 2 f hf
  intro r hr
  rcases hr with h | h | h
  ·
    have hγ : IsRoot .E6 e6HighestRoot := isRoot_e6HighestRoot
    have hfix : rho e6HighestRoot = e6HighestRoot := permLattice_e6HighestRoot
    refine ⟨{β : Fin (Tag.rank .F4) → ℤ | List.ofFn β ∈ [[2, 3, 4, 2]]},
      ⟨[[2, 3, 4, 2]], by decide +kernel, rfl⟩, xFixed (frobQ 2 f) hγ hfix 1 (map_one _), ?_, ?_⟩
    · refine Subgroup.mem_iSup_of_mem (proj e6HighestRoot) (Subgroup.mem_iSup_of_mem ?_
        (xFixed_mem (frobQ 2 f) hγ hfix 1 (map_one _)))
      show List.ofFn (proj e6HighestRoot) ∈ [[2, 3, 4, 2]]
      decide +kernel
    · apply Subtype.ext
      rw [ggInvTwE6_pi_xFixed hf hπval hγ hfix, h]
  ·
    obtain ⟨hU, -, -, -, -⟩ := isRoot_twistedE6ClassRoots
    have hρU : rho twistedE6ClassRootU = twistedE6ClassRootU' := permLattice_twistedE6ClassRootU
    have hne : rho twistedE6ClassRootU ≠ twistedE6ClassRootU := by
      rw [hρU]
      intro h
      exact absurd (congrFun h ⟨2, by decide⟩) (by decide +kernel)
    refine ⟨{β : Fin (Tag.rank .F4) → ℤ | List.ofFn β ∈ [[1, 2, 3, 2]]},
      ⟨[[1, 2, 3, 2]], by decide +kernel, rfl⟩, xPair (frobQ 2 f) hθ hU hne 1, ?_, ?_⟩
    · refine Subgroup.mem_iSup_of_mem (proj twistedE6ClassRootU) (Subgroup.mem_iSup_of_mem ?_
        (xPair_mem (frobQ 2 f) hθ hU hne 1))
      show List.ofFn (proj twistedE6ClassRootU) ∈ [[1, 2, 3, 2]]
      decide +kernel
    · apply Subtype.ext
      rw [ggInvTwE6_pi_xPair hf hπval hθ hU hne, h, hρU]
      rfl
  ·
    obtain ⟨-, -, hA, -, hB⟩ := isRoot_twistedE6ClassRoots
    have hρA : rho twistedE6ClassRootA = twistedE6ClassRootA' := permLattice_twistedE6ClassRootA
    have hneA : rho twistedE6ClassRootA ≠ twistedE6ClassRootA := by
      rw [hρA]
      intro h
      exact absurd (congrFun h ⟨0, by decide⟩) (by decide +kernel)
    have hfixB : rho twistedE6ClassRootB = twistedE6ClassRootB := permLattice_twistedE6ClassRootB
    refine ⟨{β : Fin (Tag.rank .F4) → ℤ | List.ofFn β ∈ [[1, 2, 2, 1], [1, 2, 4, 2]]},
      ⟨[[1, 2, 2, 1], [1, 2, 4, 2]], by decide +kernel, rfl⟩,
      xPair (frobQ 2 f) hθ hA hneA 1 * xFixed (frobQ 2 f) hB hfixB 1 (map_one _), ?_, ?_⟩
    · refine mul_mem (Subgroup.mem_iSup_of_mem (proj twistedE6ClassRootA)
        (Subgroup.mem_iSup_of_mem ?_ (xPair_mem (frobQ 2 f) hθ hA hneA 1)))
        (Subgroup.mem_iSup_of_mem (proj twistedE6ClassRootB)
          (Subgroup.mem_iSup_of_mem ?_ (xFixed_mem (frobQ 2 f) hB hfixB 1 (map_one _))))
      · show List.ofFn (proj twistedE6ClassRootA) ∈ [[1, 2, 2, 1], [1, 2, 4, 2]]
        decide +kernel
      · show List.ofFn (proj twistedE6ClassRootB) ∈ [[1, 2, 2, 1], [1, 2, 4, 2]]
        decide +kernel
    · apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, ggInvTwE6_pi_xPair hf hπval hθ hA hneA,
        ggInvTwE6_pi_xFixed hf hπval hB hfixB, h, hρA]
      rfl

theorem ggExcKGInvolutions_twistedE6 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .twistedE6 n f).K →* G) (hset : GGKnownSetting .twistedE6 n f ψ) :
    ∀ s ∈ ψ.range, orderOf s = 2 →
      ∃ g ∈ ψ.range, ∃ Z : Set (Fin (ggU .twistedE6 n f).D.rank → ℤ), ggASClass .twistedE6 n f Z ∧
        g * s * g⁻¹ ∈ ⨆ β ∈ Z, ((ggU .twistedE6 n f).D.rootGroup β).map ψ := by
  intro s hs hs2
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨ψbar, π, hψbar_inj, hψbar_range, hπ_surj, hπ_ker, hcomp, hπval⟩ :=
    ggInvTwE6_exists_model_frobQ hf ψ hker hcent
  let K := GaloisField 2 (2 * f)
  have hK : Nat.card K = (2 ^ f) ^ 2 := CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : K, frobQEquiv hf c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  refine ggExcKGInvolutions_of_factor .twistedE6 n f ψ π ψbar hψbar_inj hπ_surj hcomp
    (twistedE6ClassReps K (frobQ 2 f)) ?_ ?_ hs hs2
  ·
    exact ggInvTwE6_hrep hf hπval
  ·
    intro y hy
    have hy2 : y ^ 2 = 1 := by
      have h := pow_orderOf_eq_one y
      rwa [hy] at h
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hy
      omega
    obtain ⟨a, ha⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction hf hK hσ
      (twistedE6FrameReduction hf hK hσ) hy2 hy1
    exact ⟨a, ha⟩

end InvolutionsTwE6

end CFSG.StandardType
