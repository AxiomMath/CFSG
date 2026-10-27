module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankExclusionPacket
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ActualKernelInclusion
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedPairAmbientPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NeighbourRootActual

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.NeighbourFinal
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups CFSG.StandardType.LieCore
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Open
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.F4Pilot
open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.StandardType.S2MathFi1035Pos
open CFSG.StandardType.F4ExplicitPos.LiteralSetup
open CFSG.StandardType.F4ExplicitPos.RankExclusionFinish
open CFSG.StandardType.F4ExplicitPos.RankExclusionPacket
open CFSG.StandardType.F4ExplicitPos.OddKernelActual
open CFSG.StandardType.F4ExplicitPos.ActualKernelInclusion
open CFSG.StandardType.F4ExplicitPos.CommonPairTransport
open CFSG.StandardType.F4ExplicitPos.JointOrbitSelection
open CFSG.StandardType.F4ExplicitPos.NativePinFinal
open CFSG.StandardType.F4ExplicitPos.ComponentAttach
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.StandardType.F4ExplicitPos.InnerDirect
open CFSG.StandardType.F4ExplicitPos.ActualSetup
open CFSG.StandardType.F4ExplicitPos.BaseChange
open CFSG.StandardType.F4ExplicitPos.C3Range
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem f4_neighbour_actual
    {X : Type} [Group X] [Finite X]
    {n f p : ℕ} {ψ : (ggU .F4 n f).K →* X}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    (Fr : F4Omega f →+* F4Omega f)
    (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (w : WeylGroup .F4) (g0 : ModGL .F4 (F4Omega f))
    (hg0C : g0 ∈ adjointGroup .F4 (F4Omega f))
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr ⟨g0, hg0C⟩ :
        adjointGroup .F4 (F4Omega f)) : ModGL .F4 (F4Omega f)) =
        g0 * canonicalRep (coxeterSystem .F4) (F4Omega f) w)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hRho : FrobRootMap
      (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0) ρ)
    {d : X} (hdD : d ∈ D)
    (hgen : Subgroup.closure ({x, d} : Set X) = D)
    (coord : D → Fin Tag.F4.rank → (F4Omega f)ˣ)
    (hcoord : ∀ d0 : D, ThetaF4 (L := F4Omega f) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 (Subgroup.inclusion (hH_DB hH) d0) =
        rootDiagUnit .F4 (coord d0))
    (hcoord_pow : ∀ (d0 : D) (j : Fin Tag.F4.rank), coord d0 j ^ p = 1)
    (hcoord_torus : ∀ d0 : D, rootDiagUnit .F4 (coord d0) ∈
        (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0).torus)
    (hfix : ∀ b : B₁,
        (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0).step
          (ThetaF4 (L := F4Omega f) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
            (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
            (f4_exists_inner_correction_hH hH) g0 b) =
        ThetaF4 (L := F4Omega f) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
          (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
          (f4_exists_inner_correction_hH hH) g0 b)
    {iJ : KernelComponent (jointChar (coord ⟨x, hH_xD hH⟩) (coord ⟨d, hdD⟩))}
    (hJattach : CFSG.Assembly.IsComponentOf
        ((J.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ (hH_range hH) (hH_ker hH)
          (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0))
        ((langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0).Γ ⊓
          Subgroup.centralizer
            ({rootDiagUnit .F4 (coord ⟨x, hH_xD hH⟩), rootDiagUnit .F4 (coord ⟨d, hdD⟩)} :
              Set (ModGL .F4 (F4Omega f)))))
    (hJorbit : ((J.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ (hH_range hH) (hH_ker hH)
          (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0)) ≤
        rootSpan .F4 (F4Omega f)
          (ratOrbit (fun u => ρ u)
            (componentRoots (jointChar (coord ⟨x, hH_xD hH⟩) (coord ⟨d, hdD⟩)) iJ)))
    {α : Fin Tag.F4.rank → ℤ}
    (hAlpha : α ∈ componentRoots (jointChar (coord ⟨x, hH_xD hH⟩) (coord ⟨d, hdD⟩)) iJ)
    {wD : ModGL .F4 (F4Omega f)}
    (hwD : wD ∈ CFSG.StandardType.F4ExplicitPos.NativePinFinal.Zsub
        (jointChar (coord ⟨x, hH_xD hH⟩) (coord ⟨d, hdD⟩)))
    {R : Subgroup X} (hRJ : R ≤ J)
    (hcard : Nat.card ((R.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ (hH_range hH)
          (hH_ker hH) (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0)) =
        Nat.card (GaloisField 2 f))
    (hRcurve : (R.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ (hH_range hH) (hH_ker hH)
          (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0) ≤
        (rootSubgroup Tag.F4 (F4Omega f) α).map (MulAut.conj wD).toMonoidHom)
    {e : X} (he : e ∈ D) (_he1 : e ≠ 1)
    {K : Subgroup X} (hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({e} : Set X)))
    (hJK : J ≤ K) (hKne : K ≠ J)
    (_hKodd : Odd (Nat.card (Subgroup.center ↥K))) :
    K = G₀ ∨ ∃ β ∈ (ggU .PSp 3 f).D.roots, GGRootVia (ggU .PSp 3 f) K R β := by
  classical
  let : Algebra (ZMod 2) (F4Omega f) := ZMod.algebra (F4Omega f) 2
  let : Algebra.IsAlgebraic (ZMod 2) (F4Omega f) :=
    CFSG.LieType.Chevalley.algebraicClosure_isAlgebraic_zmod 2 (GaloisField 2 f)
  have hf : 1 ≤ f := (F4PosData.ofHyp hH).hf
  let Dlang : LangDatum Tag.F4 (F4Omega f) :=
    langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0
  let Θ : B₁ →* ModGL .F4 (F4Omega f) :=
    ThetaF4 (L := F4Omega f) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
      (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
      (f4_exists_inner_correction_hH hH) g0
  let η : G₀ →* ModGL .F4 (F4Omega f) :=
    etaF4 (L := F4Omega f) ψ G₀ (hH_range hH) (hH_ker hH)
      (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0
  have hη : Function.Injective η :=
    SelectedPairAmbient.etaF4_injective_local (f := f) (Ω := F4Omega f)
      ψ G₀ (hH_range hH) (hH_ker hH)
      (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0
  have hηrange : (η.comp (Subgroup.inclusion hKG)).range = (K.subgroupOf G₀).map η := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  obtain hcentral | ⟨ie, hKorbit, hKabs, hrank, hneD, hne⟩ :=
    CFSG.StandardType.F4ExplicitPos.RankExclusionPacket.neighbor_rank_or_central_selected
      (Ω := F4Omega f) (halg := ‹Algebra.IsAlgebraic (ZMod 2) (F4Omega f)›)
      hH he hKG hKcomp hJK hKne (Fr := Fr) hFr w hg0C hg0 Dlang rfl ρ hRho coord
      hcoord hcoord_pow hcoord_torus hfix
  · exact Or.inl hcentral
  · right
    have hKorbit' : (K.subgroupOf G₀).map η ≤ rootSpan .F4 (F4Omega f)
        (ratOrbit (fun u => ρ u) (componentRoots (rootCharHom (coord ⟨e, he⟩)) ie)) := by
      rw [← hηrange]; exact hKorbit
    have hKabs' : (K.subgroupOf G₀).map η ≤ rootSpan .F4 (F4Omega f)
        (componentRoots (rootCharHom (coord ⟨e, he⟩)) ie) := by
      rw [← hηrange]; exact hKabs
    have hker : kernelRoots (jointChar (coord ⟨x, hH_xD hH⟩) (coord ⟨d, hdD⟩)) ⊆
        kernelRoots (rootCharHom (coord ⟨e, he⟩)) :=
      CFSG.StandardType.F4ExplicitPos.ActualKernelInclusion.kernelRoots_joint_subset_of_closure
        (hH_DB hH) Θ coord hcoord (hH_xD hH) hdD hgen ⟨e, he⟩
    have hkerρ : ∀ γ ∈ kernelRoots (rootCharHom (coord ⟨e, he⟩)),
        ρ γ ∈ kernelRoots (rootCharHom (coord ⟨e, he⟩)) := by
      intro γ hγ
      rw [kernelRoots] at hγ ⊢
      refine ⟨(hRho.isRoot_iff γ).2 hγ.1, ?_⟩
      have h := hRho.rootChar_eq (coord ⟨e, he⟩) (hcoord_torus ⟨e, he⟩) γ hγ.1
      have h1 : rootChar (coord ⟨e, he⟩) γ = 1 := by simpa [rootCharHom] using hγ.2
      rw [h1, one_pow] at h
      simpa [rootCharHom] using h
    have hpOdd : Odd p := (hH_prime hH).odd_of_ne_two (hH_ne_two hH)
    have hstable : (fun γ => ρ γ) '' componentRoots (rootCharHom (coord ⟨e, he⟩)) ie =
        componentRoots (rootCharHom (coord ⟨e, he⟩)) ie :=
      CFSG.StandardType.F4ExplicitPos.OddKernelActual.f4_cyclic_componentRoots_image_eq_of_coord
        (D := Dlang) ρ hRho (coord ⟨e, he⟩) (hcoord_torus ⟨e, he⟩) hpOdd
        (hcoord_pow ⟨e, he⟩) ie
    have horbit1 : componentOrbitLength ρ (componentRoots (rootCharHom (coord ⟨e, he⟩)) ie) = 1 :=
      (OddKernelActual.f4_cyclic_componentOrbitLength_eq_one_of_coord
        (D := Dlang) ρ hRho (coord ⟨e, he⟩) (hcoord_torus ⟨e, he⟩) hpOdd
        (hcoord_pow ⟨e, he⟩) ie).2
    have hp2odd : p % 2 = 1 := Nat.odd_iff.mp hpOdd
    have hpΩ : (p : F4Omega f) ≠ 0 := by
      have : NeZero (p : F4Omega f) := NeZero.of_not_dvd (R := F4Omega f) (p := 2) (n := p)
        (fun h => hH_ne_two hH
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hH_prime hH)).1 h).symm)
      exact NeZero.out
    have hap : rootDiagUnit Tag.F4 (coord ⟨e, he⟩) ^ p = 1 := by
      rw [rootDiagUnit_pow,
        show coord ⟨e, he⟩ ^ p = 1 from funext (fun j => hcoord_pow ⟨e, he⟩ j),
        rootDiagUnit_one]
    obtain ⟨v, Js, hJs, hshapePar, hrank3, hncard⟩ :=
      f4_rank_ge_three_component_is_levi (hH_prime hH) hp2odd hpΩ hap hneD ie hrank
    have hshape : componentRoots (rootCharHom (coord ⟨e, he⟩)) ie =
          (fun γ => v • γ) '' CFSG.SeitzReduction.F4Pilot.b3LeviRoots ∨
        componentRoots (rootCharHom (coord ⟨e, he⟩)) ie =
          (fun γ => v • γ) '' CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet := by
      rcases hJs with hJb | hJc
      · left
        rw [hshapePar, hJb, SelectedLiteral.parabolicRoots_f4LeviB3_eq_b3LeviRoots]
      · right
        rw [hshapePar, hJc, SelectedLiteral.parabolicRoots_f4LeviC3_eq_c3RootSet]
    have hattach : CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map η)
        (Dlang.Γ ⊓ Subgroup.centralizer ({rootDiagUnit Tag.F4 (coord ⟨e, he⟩)} :
          Set (ModGL .F4 (F4Omega f)))) :=
      CFSG.StandardType.F4ExplicitPos.RankExclusionPacket.neighbor_kbar_attachment
        hH he hKG hKcomp (Fr := Fr) hFr w hg0C hg0 Dlang rfl (coord ⟨e, he⟩)
        (hcoord ⟨e, he⟩)
    have hJnonabel : ∃ y ∈ (J.subgroupOf G₀).map η, ∃ z ∈ (J.subgroupOf G₀).map η,
        y * z ≠ z * y := by
      obtain ⟨a, b, hab⟩ :=
        JointOrbitSelection.exists_noncomm_of_isQuasisimple hJattach.2.2
      exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
    have hKle : (J.subgroupOf G₀).map η ≤ (K.subgroupOf G₀).map η :=
      Subgroup.map_mono (Subgroup.comap_mono hJK)
    have hKspanRat : (K.subgroupOf G₀).map η ≤ rootSpan .F4 (F4Omega f)
        (rationalRoots ρ (rootCharHom (coord ⟨e, he⟩)) ie) := by
      rw [CFSG.StandardType.F4ExplicitPos.OddKernelActual.f4_cyclic_rationalRoots_eq_of_coord
        (D := Dlang) ρ hRho (coord ⟨e, he⟩) (hcoord_torus ⟨e, he⟩) hpOdd
        (hcoord_pow ⟨e, he⟩) ie]
      exact hKabs'
    have hsub : componentRoots (jointChar (coord ⟨x, hH_xD hH⟩) (coord ⟨d, hdD⟩)) iJ ⊆
        componentRoots (rootCharHom (coord ⟨e, he⟩)) ie :=
      CommonPairTransport.componentRoots_subset_of_common_selected_joint
        (Ω := F4Omega f) (χD := jointChar (coord ⟨x, hH_xD hH⟩) (coord ⟨d, hdD⟩))
        (χe := rootCharHom (coord ⟨e, he⟩)) iJ ie hker hkerρ hRho.iform_eq
        hJorbit hKle hKspanRat hJnonabel horbit1
    have hAlphaC : α ∈ componentRoots (rootCharHom (coord ⟨e, he⟩)) ie := hsub hAlpha
    have hwD' : wD ∈ CFSG.StandardType.F4ExplicitPos.NativePinFinal.Zsub
        (rootCharHom (coord ⟨e, he⟩)) :=
      (CFSG.StandardType.F4ExplicitPos.NativePinFinal.mem_Zsub_iff _ wD).mpr
        ((sup_le_sup le_rfl (rootSpan_mono hker))
          ((CFSG.StandardType.F4ExplicitPos.NativePinFinal.mem_Zsub_iff _ wD).mp hwD))
    have hq : Dlang.q = 2 ^ f :=
      (SelectedLiteral.langDatumF4_q (K := GaloisField 2 f) (L :=
          F4Omega f) Fr hFr w hg0C hg0).trans
        (CFSG.StandardType.F4ExplicitPos.SelectedLiteral.card_galoisField_two f hf)
    exact CFSG.StandardType.F4ExplicitPos.NeighbourRootActual.ggRootVia_of_actual_rankThree
      (f := f) (hf := hf) (Ω := F4Omega f) G₀ K R hKG (hRJ.trans hJK) η hη Dlang hq ρ hRho
      (coord ⟨e, he⟩) ie hkerρ hstable hrank3 hncard v hshape hattach hKabs' hcard hAlphaC
      hwD' hRcurve

end CFSG.StandardType.F4ExplicitPos.NeighbourFinal

end

end
