module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwAut
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwSK
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwCover
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwDiag
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwAssembly
import CFSG.RankThree.PartOne.KE.CTLangData

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement

theorem rckRetTwE6_holds
    : RCKRetTwE6 := by
  intro τ S a hT p hp hp2 hTp i h hq hquasi hshape
  classical
  obtain ⟨hkind, h6, hn⟩ := hshape
  have hτ := rckA4_tag h6
  have hpL := rckA4_cast_ne_zero hp hp2
  obtain ⟨β, hβroot, hΨβ, hnon, hedge, -⟩ := rckE6_labelled hτ S hp hpL hTp i h6 hn
  have hrank : τ.rank < 2 * compRank (componentRoots (rootCharHom a) i) := by
    rw [h6]
    rcases hτ with rfl | rfl | rfl <;> simp [Tag.rank]
  have himg := rckRet_orbit_one S hT i hrank
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := fun γ hγ =>
    himg ▸ Set.mem_image_of_mem _ hγ
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hstab
  obtain ⟨ι, hι⟩ := rckRet_iota hτ hβroot hnon hedge
  obtain ⟨θ, hθ⟩ := rckE6_comparison hτ hβroot hι
  have hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ := fun γ hγ => by
    rw [← hΨβ] at hγ ⊢
    exact hstab γ hγ
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · have := S.hqpow.1
      rw [hq, h0, pow_zero] at this
      exact absurd this not_isPrimePow_one
    · exact h0
  have hRH : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ RetH τ β := by
    have h0 := rckRet_R_le_H S i hs1
    rw [hΨβ] at h0
    exact h0
  have hout : ¬ twistInner (rootsOfFam β Set.univ) S.ρ := by
    intro hin
    have h1 : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rw [hs1, Function.iterate_one, hΨβ]
      exact hin
    simp [twistKind, h1] at hkind
  have hbij : Set.BijOn S.ρ (rootsOfFam β Set.univ) (rootsOfFam β Set.univ) := by
    refine ⟨hρΨ, S.ρ.injective.injOn, ?_⟩
    intro y hy
    have hy' : y ∈ componentRoots (rootCharHom a) i := hΨβ ▸ hy
    have h2 : y ∈ S.ρ '' componentRoots (rootCharHom a) i := by
      rw [himg]
      exact hy'
    rw [hΨβ] at h2
    exact h2
  obtain ⟨w', hw'⟩ := rckRet_outer_transport hτ hβroot hι hbij (fun γ _ => S.frob.neg_eq γ)
    (fun γ _ δ _ => S.frob.iform_eq γ δ) hout
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g0, hg0, hlangg⟩ :=
    CFSG.RankThree.PartOne.KE.lang_conjugator_twisted (ZMod 2) (ℓ := 2) (f := h) hh GGL w'
  let g1 : ModGL Tag.E6 GGL := g0
  have hg1 : g1 ∈ adjointGroup Tag.E6 GGL := hg0
  have hlangg' : twistHom TwistTag.E6 GGL (ggFrobT h) g1 =
      g1 * canonicalRep (coxeterSystem Tag.E6) GGL w' := hlangg
  have hzh : g1⁻¹ ∈ adjointGroup Tag.E6 GGL := inv_mem hg1
  have hlang : twistHom TwistTag.E6 GGL (ggFrobT h) (g1⁻¹)⁻¹ =
      (g1⁻¹)⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w' := by
    rw [inv_inv]
    exact hlangg'
  obtain ⟨SK, hSKq, hSKg0, hSKn, hSKΦ, hSKρ, -⟩ := rckRet_SK_tw hh hzh hlang
  have hg0eq : SK.D.g0 = g1 := hSKg0.trans (inv_inv g1)
  have hstepEq : ∀ y : ModGL Tag.E6 GGL, SK.D.n * SK.D.Φ y * SK.D.n⁻¹ =
      canonicalRep (coxeterSystem Tag.E6) GGL w' *
        (show ModGL Tag.E6 GGL from twistHom TwistTag.E6 GGL (ggFrobT h) y) *
          (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ := fun y => by
    rw [hSKn, DFunLike.congr_fun hSKΦ y]
    rfl
  have hρ : ∀ γ ∈ rootsOfFam β Set.univ, SK.ρ (ι γ) = ι (S.ρ γ) := fun γ hγ => by
    rw [hSKρ (ι γ) (hι.1.mapsTo hγ)]
    exact hw' γ hγ
  obtain ⟨φ, hφsurj, hφker, hφform⟩ := rckRet_tw_cover hτ S hβroot hΨβ hι hθ hRH hs1 hquasi hh hq
    SK hSKq hSKΦ hρΨ hρ
  have hκφ : (rckRetKappa θ hRH).comp φ =
      (MulAut.conj SK.D.g0⁻¹).toMonoidHom.comp ((rckTw6_iota h).comp (rckTw6_psi h hh)) := by
    refine MonoidHom.ext fun x => ?_
    refine (hφform x).trans ?_
    show _ = SK.D.g0⁻¹ * _ * SK.D.g0⁻¹⁻¹
    rw [inv_inv]
    rfl
  have hrangeΓ : (rckRetKappa θ hRH).range = SK.Γ := by
    have h1 : ((rckRetKappa θ hRH).comp φ).range = (rckRetKappa θ hRH).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφsurj, ← MonoidHom.range_eq_map]
    rw [← h1, hκφ]
    exact rckTw6_cover_range SK h hh hSKΦ
  have hker := rckRet_kappa_ker hθ hRH hrangeΓ (rckRet_tw_SKcent hh SK hSKΦ)
  have hψ : ∀ x, ((rckRetKappa θ hRH).comp φ) x =
      g1⁻¹ * (show ModGL Tag.E6 GGL from rckTw6_iota h (rckTw6_psi h hh x)) * g1⁻¹⁻¹ := by
    intro x
    have h1 := DFunLike.congr_fun hκφ x
    rw [hg0eq] at h1
    exact h1
  have htor : ∀ b ∈ S.D.torus, ∃ t ∈ SK.D.torus,
      (∀ (x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        (hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i),
        rckRetKappa θ hRH ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ = t * rckRetKappa θ hRH x * t⁻¹) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, rckRootVal t (ι γ) = rckRootVal b γ := by
    intro b hb
    have hbT : b ∈ torusGroup τ GGL := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
    refine ⟨rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)), ?_, ?_, ?_⟩
    · show _ ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf SK.D.n SK.D.Φ
      rw [CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
      exact ⟨rootDiagUnit_mem_torusGroup _, (hstepEq _).trans (rckRet_tw_torus_fixed S hι hρΨ hw'
        (fun c => by rw [ggFrobT_apply, hq]) hb)⟩
    · intro x hx
      obtain ⟨hx', h'⟩ := rckRet_theta_torus hι hθ hbT ⟨(x : ModGL τ GGL), hRH x.2⟩
      rw [rckRetKappa_apply, rckRetKappa_apply]
      exact h'
    · intro γ hγ
      exact rckRet_torus_val hι hbT γ (by rw [← hΨβ]; exact hγ)
  obtain ⟨hfinM, hperfM, hsplit, hstd, hade⟩ := rckRet_tw_modelFacts hh
  have hrg : ∀ γ ∈ (ggU .twistedE6 0 h).D.roots,
      IsPGroup 2 ((ggU .twistedE6 0 h).D.rootGroup γ) :=
    fun γ hγ => rootGroup_isPGroup_of_standardReturnAt hstd hγ
  have hZodd := rckRet_tw_center_odd hh φ hφsurj hφker
  have hdiag : ∀ b ∈ S.D.torus, GGPsiInnerDiag (ggU .twistedE6 0 h).D
      ((rationalComponent S.ρ S.Γ (rootCharHom a) i).subtype.comp φ) b := by
    intro b hb
    have hbT : b ∈ torusGroup τ GGL := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
    have hFt : S.D.step b = b := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).2
    obtain ⟨t, htT, hconj, -⟩ := htor b hb
    have htadj : t ∈ adjointGroup Tag.E6 GGL :=
      CFSG.RankThree.PartOne.KE.twistedTorusOf_le_adjointGroup _ _ htT
    have htfix : canonicalRep (coxeterSystem Tag.E6) GGL w' *
        (show ModGL Tag.E6 GGL from twistHom TwistTag.E6 GGL (ggFrobT h) t) *
          (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ = t := by
      have h0 := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 htT).2
      exact (hstepEq t).symm.trans h0
    have hdiagE6 : GGPsiInnerDiag (twistedE6Datum 2 h) ((rckRetKappa θ hRH).comp φ) t :=
      rckRet_innerDiag_TwE6 hh hzh htadj hlang htfix hψ
    refine rckRet_transfer_innerDiag hrg φ (rckRetKappa θ hRH) hker.le hZodd ?_ hconj hdiagE6
    intro r hr
    refine ⟨rckRet_conj_mem_R S i hs1 hbT hFt hr, ?_⟩
    have h1 := rckRet_conj_mem_R S i hs1 (inv_mem hbT) (by rw [map_inv, hFt]) hr
    rwa [inv_inv] at h1
  unfold RCKReturnedCover
  simp only [hs1, mul_one, Function.iterate_one]
  refine ⟨ggU .twistedE6 0 h, φ, Tag.E6, SK, rckRetKappa θ hRH, ι, rfl, hstd, hφsurj, hφker,
    hfinM, hperfM, hsplit, ?_, hdiag, Or.inr (Or.inl rfl), hSKq, hker, hrangeΓ, ?_, ?_, ?_, ?_,
    htor⟩
  · obtain ⟨hβ₀, hlong⟩ := rckRet_tw_longRoot h
    obtain ⟨γ₀, hγ₀, hst1, hst2, hpair1, hpair2⟩ := rckRet_tw_pair hh SK hSKΦ hSKq
    refine ⟨Pi.single (0 : Fin 4) 1, hβ₀, hlong, γ₀, hγ₀, SK.D.g0⁻¹, inv_mem SK.D.g0_mem, hst1,
      hst2, ?_, ?_⟩
    · exact (congrArg (fun f : twistedE6Group 2 h →* ModGL Tag.E6 GGL =>
        ((twistedE6Datum 2 h).rootGroup (Pi.single (0 : Fin 4) 1)).map f) hκφ).trans hpair1
    · exact (congrArg (fun f : twistedE6Group 2 h →* ModGL Tag.E6 GGL =>
        ((twistedE6Datum 2 h).rootGroup (-Pi.single (0 : Fin 4) 1)).map f) hκφ).trans hpair2
  · rw [hΨβ]
    exact hι.1
  · intro γ hγ
    exact hι.2.2.2.1 γ (by rw [← hΨβ]; exact hγ)
  · intro γ hγ δ hδ
    exact hι.2.2.2.2 γ (by rw [← hΨβ]; exact hγ) δ (by rw [← hΨβ]; exact hδ)
  · intro γ hγ
    have hγ' : γ ∈ rootsOfFam β Set.univ := by rw [← hΨβ]; exact hγ
    exact (hρ γ hγ').symm

end CFSG.StandardType.RCKRP

end
