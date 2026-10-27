module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover6Aux2
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankTwE6ThreeHolds
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextRankAux2
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer

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

theorem rckRet_innerDiag_TwE6
    {h : ℕ} (hh : 0 < h) {zh t : ModGL Tag.E6 GGL}
    (hzh : zh ∈ adjointGroup Tag.E6 GGL) (ht : t ∈ adjointGroup Tag.E6 GGL)
    {w' : WeylGroup Tag.E6}
    (hlang : twistHom TwistTag.E6 GGL (ggFrobT h) zh⁻¹ =
      zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w')
    (htfix : canonicalRep (coxeterSystem Tag.E6) GGL w' *
      (show ModGL Tag.E6 GGL from twistHom TwistTag.E6 GGL (ggFrobT h) t) *
        (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ = t)
    {ψ : twistedE6Group 2 h →* ModGL Tag.E6 GGL}
    (hψ : ∀ x, ψ x = zh * (show ModGL Tag.E6 GGL from rckTw6_iota h (rckTw6_psi h hh x)) * zh⁻¹) :
    GGPsiInnerDiag (twistedE6Datum 2 h) ψ t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh1 : 1 ≤ h := hh
  let k := GaloisField 2 (2 * h)
  let θ : k ≃+* k := frobQEquiv hh1
  let ι : k →+* GGL := ggRatEmb (2 * h)
  let zhT : ModGL TwistTag.E6.tag GGL := show ModGL TwistTag.E6.tag GGL from zh
  let tT : ModGL TwistTag.E6.tag GGL := show ModGL TwistTag.E6.tag GGL from t
  let n : ModGL TwistTag.E6.tag GGL :=
    show ModGL TwistTag.E6.tag GGL from canonicalRep (coxeterSystem Tag.E6) GGL w'
  let C₀G : Subgroup (ModGL TwistTag.E6.tag GGL) :=
    graphFixedRootGroup TwistTag.E6 GGL (ggFrobT h)
  let d : ModGL TwistTag.E6.tag GGL := zhT⁻¹ * tT * zhT
  have hzhT : zhT ∈ adjointGroup TwistTag.E6.tag GGL := hzh
  have htT : tT ∈ adjointGroup TwistTag.E6.tag GGL := ht
  have hlangT : twistHom TwistTag.E6 GGL (ggFrobT h) zhT⁻¹ = zhT⁻¹ * n := hlang
  have htfixT : n * (show ModGL TwistTag.E6.tag GGL from
      twistHom TwistTag.E6 GGL (ggFrobT h) t) * n⁻¹ = tT := htfix
  have hFzhT : twistHom TwistTag.E6 GGL (ggFrobT h) zhT = n⁻¹ * zhT := by
    have h := congrArg (fun m : ModGL TwistTag.E6.tag GGL => m⁻¹) hlangT
    simpa only [map_inv, mul_inv_rev, inv_inv] using h
  have htT' : twistHom TwistTag.E6 GGL (ggFrobT h) d = d := by
    show twistHom TwistTag.E6 GGL (ggFrobT h) (zhT⁻¹ * tT * zhT) = zhT⁻¹ * tT * zhT
    calc twistHom TwistTag.E6 GGL (ggFrobT h) (zhT⁻¹ * tT * zhT)
        = twistHom TwistTag.E6 GGL (ggFrobT h) zhT⁻¹ *
            twistHom TwistTag.E6 GGL (ggFrobT h) tT *
            twistHom TwistTag.E6 GGL (ggFrobT h) zhT := by rw [map_mul, map_mul]
      _ = (zhT⁻¹ * n) * twistHom TwistTag.E6 GGL (ggFrobT h) tT * (n⁻¹ * zhT) := by
            rw [hlangT, hFzhT]
      _ = zhT⁻¹ * (n * twistHom TwistTag.E6 GGL (ggFrobT h) tT * n⁻¹) * zhT := by group
      _ = zhT⁻¹ * tT * zhT := by rw [htfixT]
  have hd_fixed : d ∈ twistedFixedGroup TwistTag.E6 GGL (ggFrobT h) := by
    show zhT⁻¹ * tT * zhT ∈ twistedFixedGroup TwistTag.E6 GGL (ggFrobT h)
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzhT) htT) hzhT, htT'⟩
  have hK : Nat.card k = (2 ^ h) ^ 2 := by
    rw [show k = GaloisField 2 (2 * h) from rfl, GaloisField.card 2 (2 * h) (by omega),
      mul_comm 2 h, pow_mul]
  have hσ : ∀ c : k, θ c = c ^ (2 ^ h) := fun c => by
    change frobQ 2 h c = c ^ (2 ^ h)
    exact frobQ_apply 2 h c
  have hFrsurj : Function.Surjective (ggFrobT h) := by
    intro c
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2 ^ h)
      (pow_pos (by norm_num : (0 : ℕ) < 2) h)
    exact ⟨y, by rw [ggFrobT_apply, hy]⟩
  letI : Algebra k GGL := ι.toAlgebra
  haveI : CharP k 2 := inferInstance
  haveI : CharP GGL 2 := inferInstance
  haveI : IsScalarTower (ZMod 2) k GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure k GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := k) }
  have hd_inndiag : d ∈ (twistedE6InndiagGL k θ).map (baseChangeGL (algebraMap k GGL)) :=
    twistedFixedGroup_le_map_inndiag_alg Nat.prime_two hh1 hK θ hσ (ggFrobT h)
      (ggFrobT_apply h) hd_fixed
  obtain ⟨g, hg, hgd⟩ := Subgroup.mem_map.mp hd_inndiag
  have hgd' : baseChangeGL (ggRatEmb (2 * h)) g = d := hgd
  let α : MulAut ↥(graphFixedRootGroup TwistTag.E6 k (frobQ 2 h)) :=
    twistedE6InndiagConj k θ ⟨g, hg⟩
  have hαD : α ∈ LayerSixE.twInndiagAut h := by
    rw [CFSG.StandardType.NoOffTwE6Three.twInndiagAut_eq_range_twistedE6InndiagConj hh1]
    exact ⟨⟨g, hg⟩, rfl⟩
  have hC0map : (twistedE6RootGroup k θ).map (baseChangeGL ι) = C₀G := by
    change (graphFixedRootGroup TwistTag.E6 k θ.toRingHom).map
        (baseChangeGL (ggRatEmb (2 * h))) = graphFixedRootGroup TwistTag.E6 GGL (ggFrobT h)
    exact map_baseChangeGL_graphFixedRootGroup_eq TwistTag.E6 Nat.prime_two hh1 k hK θ.toRingHom
      hσ (ggRatEmb (2 * h)) (ggFrobT_apply h) hFrsurj
  have hπ_surj : Function.Surjective (rckTw6_psi h hh1) := by
    intro y
    obtain ⟨x, hx⟩ := CFSG.LieType.Steinberg.Isogeny.twistedE6Isogeny_surjective 2 h hh1
      ((MulEquiv.subgroupCongr (rckTw6_hRR h hh1)).symm y)
    refine ⟨x, ?_⟩
    show (MulEquiv.subgroupCongr (rckTw6_hRR h hh1))
      (CFSG.LieType.Steinberg.Isogeny.twistedE6Isogeny 2 h hh1 x) = y
    rw [hx, MulEquiv.apply_symm_apply]
  let ψR : Subgroup (ModGL TwistTag.E6.tag GGL) := ψ.range
  have hπval : ∀ z : twistedE6Group 2 h,
      ((rckTw6_psi h hh1 z : ↥(graphFixedRootGroup TwistTag.E6 k (frobQ 2 h))) :
          ModGL TwistTag.E6.tag k) =
        ((CFSG.LieType.Steinberg.Isogeny.e6IsogenyT k (z : e6Data_valid.minGroup k) :
          ↥(adjointGroup TwistTag.E6.tag k)) : ModGL TwistTag.E6.tag k) := by
    intro z
    exact CFSG.LieType.Steinberg.Isogeny.coe_twistedE6Isogeny (p := 2) (f := h) hh1 z
  have hkπ : ψ.ker ≤ (rckTw6_psi h hh1).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h2 : zhT * rckTw6_iota h (rckTw6_psi h hh1 x) * zhT⁻¹ = 1 := by
      have hψx : ψ x = zhT * rckTw6_iota h (rckTw6_psi h hh1 x) * zhT⁻¹ := hψ x
      rw [← hψx, hx]
      rfl
    have h1T : rckTw6_iota h (rckTw6_psi h hh1 x) = 1 := by
      calc rckTw6_iota h (rckTw6_psi h hh1 x)
          = zhT⁻¹ * (zhT * rckTw6_iota h (rckTw6_psi h hh1 x) * zhT⁻¹) * zhT := by group
        _ = zhT⁻¹ * 1 * zhT := by rw [h2]
        _ = 1 := by group
    have hι_inj : Function.Injective (rckTw6_iota h) := by
      intro a b hab
      apply Subtype.ext
      exact baseChangeGL_injective (ggRatEmb (2 * h)) hab
    exact hι_inj (by rw [h1T, map_one])
  have hι_range : (rckTw6_iota h).range = C₀G := by
    rw [show rckTw6_iota h = (baseChangeGL ι).comp
      (twistedE6RootGroup k θ).subtype from rfl]
    exact (MonoidHom.range_comp (baseChangeGL ι) (twistedE6RootGroup k θ).subtype).trans
      (by rw [Subgroup.range_subtype]; exact hC0map)
  have hψ_range : ψR = C₀G.map (MulAut.conj zhT).toMonoidHom := by
    have hψ_eq : (show twistedE6Group 2 h →* ModGL TwistTag.E6.tag GGL from ψ) =
        (MulAut.conj zhT).toMonoidHom.comp ((rckTw6_iota h).comp (rckTw6_psi h hh1)) := by
      refine MonoidHom.ext (fun x => ?_)
      change ψ x = zhT * rckTw6_iota h (rckTw6_psi h hh1 x) * zhT⁻¹
      rw [hψ x]
      rfl
    show ψ.range = C₀G.map (MulAut.conj zhT).toMonoidHom
    calc (show Subgroup (ModGL TwistTag.E6.tag GGL) from ψ.range)
        = ((MulAut.conj zhT).toMonoidHom.comp
            ((rckTw6_iota h).comp (rckTw6_psi h hh1))).range :=
          congrArg MonoidHom.range hψ_eq
      _ = Subgroup.map (MulAut.conj zhT).toMonoidHom
            ((rckTw6_iota h).comp (rckTw6_psi h hh1)).range := MonoidHom.range_comp _ _
      _ = Subgroup.map (MulAut.conj zhT).toMonoidHom
            (Subgroup.map (rckTw6_iota h) (rckTw6_psi h hh1).range) :=
          congrArg (Subgroup.map (MulAut.conj zhT).toMonoidHom)
            (MonoidHom.range_comp (rckTw6_iota h) (rckTw6_psi h hh1))
      _ = Subgroup.map (MulAut.conj zhT).toMonoidHom
            (Subgroup.map (rckTw6_iota h) ⊤) := by
            rw [MonoidHom.range_eq_top.2 hπ_surj]
      _ = Subgroup.map (MulAut.conj zhT).toMonoidHom (rckTw6_iota h).range := by
            rw [Subgroup.map_top]
      _ = C₀G.map (MulAut.conj zhT).toMonoidHom := by rw [hι_range]
  have hdN : d ∈ Subgroup.normalizer (C₀G : Set (ModGL TwistTag.E6.tag GGL)) := by
    have hgN : g ∈ Subgroup.normalizer
        (twistedE6RootGroup k θ : Set (ModGL TwistTag.E6.tag k)) :=
      twistedE6InndiagGL_le_normalizer k θ hg
    rw [← hgd', ← hC0map]
    exact Subgroup.le_normalizer_map (f := baseChangeGL ι) ⟨g, hgN, rfl⟩
  have hcN' : tT ∈ Subgroup.normalizer (ψR : Set (ModGL TwistTag.E6.tag GGL)) := by
    rw [hψ_range]
    have htd : (MulAut.conj zhT).toMonoidHom d = tT := by
      change zhT * d * zhT⁻¹ = tT
      rw [show d = zhT⁻¹ * tT * zhT from rfl]
      group
    rw [← htd]
    exact Subgroup.le_normalizer_map (f := (MulAut.conj zhT).toMonoidHom) ⟨d, hdN, rfl⟩
  have hcN : t ∈ Subgroup.normalizer (ψ.range : Set (ModGL Tag.E6 GGL)) := hcN'
  have hα : LayerSixE.GGInduces (rckTw6_psi h hh1) ψ t α := by
    intro y y' hconj
    have hT : zhT * rckTw6_iota h (rckTw6_psi h hh1 y') * zhT⁻¹ =
        tT * (zhT * rckTw6_iota h (rckTw6_psi h hh1 y) * zhT⁻¹) * tT⁻¹ := by
      have h := hconj
      rw [hψ y', hψ y] at h
      exact h
    have hd_eq : rckTw6_iota h (rckTw6_psi h hh1 y') =
        d * rckTw6_iota h (rckTw6_psi h hh1 y) * d⁻¹ := by
      calc rckTw6_iota h (rckTw6_psi h hh1 y')
          = zhT⁻¹ * (zhT * rckTw6_iota h (rckTw6_psi h hh1 y') * zhT⁻¹) * zhT := by group
        _ = zhT⁻¹ * (tT * (zhT * rckTw6_iota h (rckTw6_psi h hh1 y) * zhT⁻¹) * tT⁻¹) *
              zhT := by rw [hT]
        _ = d * rckTw6_iota h (rckTw6_psi h hh1 y) * d⁻¹ := by
              rw [show d = zhT⁻¹ * tT * zhT from rfl]; group
    have h3 : (rckTw6_psi h hh1 y' : ModGL TwistTag.E6.tag k) =
        g * (rckTw6_psi h hh1 y : ModGL TwistTag.E6.tag k) * g⁻¹ := by
      apply baseChangeGL_injective (ggRatEmb (2 * h))
      rw [map_mul, map_mul, map_inv, hgd']
      exact hd_eq
    have h4 : (rckTw6_psi h hh1 y' : ModGL TwistTag.E6.tag k) =
        (α (rckTw6_psi h hh1 y) : ModGL TwistTag.E6.tag k) := by
      rw [show (α (rckTw6_psi h hh1 y) : ModGL TwistTag.E6.tag k) =
          g * (rckTw6_psi h hh1 y : ModGL TwistTag.E6.tag k) * g⁻¹ from
        twistedE6InndiagConj_apply (K := k) (σ := θ) ⟨g, hg⟩ (rckTw6_psi h hh1 y)]
      exact h3
    exact Subtype.ext h4
  exact LayerSixE.ggPsiInnerDiag_of_induces_twistedE6 (f := h) hh1
    (π := rckTw6_psi h hh1) hπ_surj hπval ψ hkπ hcN hα hαD

end CFSG.StandardType.RCKRP

end
