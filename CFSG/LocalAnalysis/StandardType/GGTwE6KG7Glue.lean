module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreDefs

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.StandardType.SCFourCover

private theorem kg7glue_largeEvenInduces_iff_of_iff {L : Type*} [Group L] {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {rel rel' : L → L → Prop}
    (h : ∀ l l', rel l l' ↔ rel' l l') (φ : MulAut R) :
    LargeEvenInduces θ rel φ ↔ LargeEvenInduces θ rel' φ := by
  constructor
  · intro hφ l l' hl
    exact hφ l l' ((h l l').2 hl)
  · intro hφ l l' hl
    exact hφ l l' ((h l l').1 hl)

private theorem kg7glue_ggMarkingAll_induces_I (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {X : Type*} [Group X] {ι : Type}
    (rel : ι → X → X → Prop) (S : Set ι)
    (h : ∀ s ∈ S, LargeEvenMarking X fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (rel s) φ) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ =>
      ∀ s ∈ S, ∃ φ ∈ I, LargeEvenInduces θ (rel s) φ := by
  intro P hP
  obtain ⟨hX, lab, hlab, hrawP⟩ := hP
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_
    (hraw 3 Nat.prime_three (by norm_num) lab hlab _ (hiso lab hlab _ hrawP))⟩
  rintro R _ I F ⟨⟨⟨hs, hna, θ, hθ⟩, hisoR⟩, hinnR⟩
  obtain ⟨hmul, hinv, hinn, -⟩ := hinnR hs hna
  refine ⟨hs, hna, θ, hθ, fun s hsS => ?_⟩
  obtain ⟨-, labₛ, hlabₛ, hrawₛ⟩ := h s hsS
  obtain ⟨Rₛ, _, Iₛ, Fₛ, ⟨hss, hnas, θₛ, φₛ, hφₛ, hind⟩, hisoₛ⟩ :=
    largeEvenRawDatum_exists (hisoR hs hna labₛ hlabₛ _ hrawₛ)
  have hmem : (MulAut.congr (θ.symm.trans θₛ)).symm φₛ ∈ ggInndiag R I :=
    (hisoₛ hss hnas (θ.symm.trans θₛ) _).2 (by
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure hφₛ))
  refine ⟨_, (ggL45_mem_ggInndiag_iff hmul hinv hinn).1 hmem, ?_⟩
  intro l l' hl
  simp only [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply, hind l l' hl]

theorem ggMarkingAll_autsInduceOn_of_map (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {X R : Type} [Group X] [Group R] {ψ : X →* R}
    (hker : ψ.ker ≤ Subgroup.center X) (A : Subgroup (MulAut X)) (ρ : MulAut X → MulAut R)
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) {J : Subgroup X} (hJ : ⁅J, J⁆ = J)
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    (h : ∀ a ∈ A, LargeEvenMarking ↥(J.map ψ) fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (fun m m' : ↥(J.map ψ) => (m' : R) = ρ a m) φ) :
    GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGAutsInduceOn A J θ' I' := by
  have hXJ : commutator ↥J = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJ)
  have stepA : ∀ a ∈ A, LargeEvenMarking ↥J fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (fun j j' : ↥J => a (j : X) = (j' : X)) φ := by
    intro a ha
    refine largeEvenMarking_centerQuot (centerQuotMap hker hJ) hXJ ?_ (h a ha)
    intro lab R' _ I F θ hθ
    obtain ⟨φ, hφI, hind⟩ := hθ
    refine ⟨φ, hφI, ?_⟩
    have hmap := (largeEvenInduces_map_iff hker (hρ a) hJ (hAJ a ha) θ φ).2 hind
    exact (kg7glue_largeEvenInduces_iff_of_iff ((centerQuotMap hker hJ).trans θ)
      (rel := fun j j' : ↥J => a (j : X) = (j' : X))
      (rel' := fun j j' : ↥J => (j' : X) = a (j : X))
      (fun _ _ => eq_comm) φ).2 hmap
  exact kg7glue_ggMarkingAll_induces_I hraw hiso
    (fun (a : MulAut X) (j j' : ↥J) => a (j : X) = (j' : X))
    (A : Set (MulAut X)) stepA

end CFSG.StandardType.TwE6KG7
