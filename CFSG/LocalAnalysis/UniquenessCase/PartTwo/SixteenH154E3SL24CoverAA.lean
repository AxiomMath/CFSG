module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNA
public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.GH74.KGroups

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_orth3L_eq_map_autSub
    {L : Subgroup (MulAut W)}
    {ψ : ↥(commSub ⊤ L) ≃* Orth3} {π : ↥(StatedSL 2 GF4) →* ↥L}
    (hπ : Function.Surjective π)
    (hact : ∀ (γ : ↥(StatedSL 2 GF4)) (u : W) (hu : u ∈ commSub ⊤ L)
        (hu' : (π γ : MulAut W) u ∈ commSub ⊤ L),
        ψ ⟨(π γ : MulAut W) u, hu'⟩ =
          Multiplicative.ofAdd (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4)
            (Multiplicative.toAdd (ψ ⟨u, hu⟩)))) :
    orth3L = (autSub L (commSub ⊤ L)).map (MulAut.congr ψ).toMonoidHom := by
  let hstab : ∀ γ : ↥(StatedSL 2 GF4), (π γ : MulAut W) ∈ stabSub (commSub ⊤ L) :=
    fun γ => StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := (π γ : MulAut W))
      (by intro u; simp) (Subgroup.le_normalizer (π γ).2)
  have hpoint : ∀ γ : ↥(StatedSL 2 GF4),
      MulAut.congr ψ (resHom (commSub ⊤ L) ⟨π γ, hstab γ⟩) = s16h_orth3AutHom γ := by
    intro γ
    apply MulEquiv.ext
    intro v
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    rw [s16h_orth3AutHom_apply]
    have h1 : resHom (commSub ⊤ L) ⟨π γ, hstab γ⟩ (ψ.symm v) =
        ⟨(π γ : MulAut W) ((ψ.symm v : ↥(commSub ⊤ L)) : W),
          (hstab γ ((ψ.symm v : ↥(commSub ⊤ L)) : W)).2 (ψ.symm v).2⟩ := rfl
    rw [h1, hact γ ((ψ.symm v : ↥(commSub ⊤ L)) : W) (ψ.symm v).2
      ((hstab γ ((ψ.symm v : ↥(commSub ⊤ L)) : W)).2 (ψ.symm v).2)]
    rw [show (⟨((ψ.symm v : ↥(commSub ⊤ L)) : W), (ψ.symm v).2⟩ : ↥(commSub ⊤ L)) =
      ψ.symm v from rfl, MulEquiv.apply_symm_apply]
  rw [s16h_orth3L_eq_range]
  apply le_antisymm
  · rintro _ ⟨γ, rfl⟩
    exact ⟨resHom (commSub ⊤ L) ⟨π γ, hstab γ⟩,
      mem_autSub.mpr ⟨⟨π γ, hstab γ⟩, (π γ).2, rfl⟩, hpoint γ⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨γ, hγ⟩ := hπ ⟨(g : MulAut W), hgL⟩
    have hx : (⟨π γ, hstab γ⟩ : stabSub (commSub ⊤ L)) = g :=
      Subtype.ext (congrArg (fun l : ↥L => (l : MulAut W)) hγ)
    have hg_eq : resHom (commSub ⊤ L) ⟨π γ, hstab γ⟩ = resHom (commSub ⊤ L) g :=
      congrArg (resHom (commSub ⊤ L)) hx
    rw [← hg_eq]
    exact ⟨γ, (hpoint γ).symm⟩

theorem s16h_sl24_cover_resHom_normalizer {L : Subgroup (MulAut W)} {n : MulAut W}
    (hn : n ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hnU : n ∈ stabSub (commSub ⊤ L)) :
    resHom (commSub ⊤ L) ⟨n, hnU⟩ ∈
      Subgroup.normalizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) := by
  have hnorm : (⟨n, hnU⟩ : stabSub (commSub ⊤ L)) ∈
      Subgroup.normalizer (((L.subgroupOf (stabSub (commSub ⊤ L)) :
        Subgroup (stabSub (commSub ⊤ L))) : Set (stabSub (commSub ⊤ L)))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      exact (Subgroup.mem_normalizer_iff.mp hn (h : MulAut W)).mp hh
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      exact (Subgroup.mem_normalizer_iff.mp hn (h : MulAut W)).mpr hh
  exact Subgroup.le_normalizer_map (resHom (commSub ⊤ L)) ⟨⟨n, hnU⟩, hnorm, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
