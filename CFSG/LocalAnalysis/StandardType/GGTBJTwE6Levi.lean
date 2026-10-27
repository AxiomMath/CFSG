module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviComponentAction
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBsCount
public import CFSG.LocalAnalysis.StandardType.GGTBJE6FrameDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviAssemble

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus TableBExc.E6Three


theorem ggTBJ_twE6_levi_side
    {K : Type} [Field K] [Finite K] {n p : ℕ} [Fact p.Prime]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hp5 : 5 < p) (hpq : p ∣ 2 ^ n + 1)
    {G : Type} [Group G] [Finite G] {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (ψ₀ : X →* TwE6Delta.RecipeR K n)
    (hA : GGTorusTBGroup p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)
      X ψ₀ (ggGamma X hN).range)
    (y : MulAut X) (hy : y ∈ (ggGamma X hN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (bX : Bs) (hbX1 : bX ≠ 1) (hbXC : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcount : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨σ, hσ, E, F, ζ, hζ, T, ψ, s, Θ, e, ΘB, t₀, i, v, C,
      hζo, hv, hTinj, hT, hψ, hker, hs, hΘ, he, hΘB, hAut, ht₀, -, -, hΨ,
      hLow, hAnn⟩ := ggTBJ_twE6_bs_levi_model hn hK hp5 hpq hBs hSC hN ψ₀ hA y hy hy1 hJ
  let sf : (Fin Tag.E6.rank → Multiplicative (ZMod p)) →* X := s.comp e.toMonoidHom
  have hsf : ∀ f, ψ (sf f) = T (Multiplicative.ofAdd (fun j => Multiplicative.toAdd (f j))) := by
    intro f
    change ψ (s (e f)) = _
    rw [hs, he]
  have hΘsf : ∀ f c, ((ΘB (f, c) : Bs) : G) = ((sf f : X) : G) * c := hΘB
  let a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := TableBExc.E6Three.zetaVec ζ hζ t₀
  let Ψ : Set (Fin Tag.E6.rank → ℤ) := componentRoots (rootCharHom a) i
  have hAnnCount : ∀ t : ggRootAnn p Ψ, ∀ j ∈ J,
      ((sf (fun k => Multiplicative.ofAdd ((t : Fin Tag.E6.rank → ZMod p) k)) : X) : G) * j =
        j * ((sf (fun k => Multiplicative.ofAdd ((t : Fin Tag.E6.rank → ZMod p) k)) : X) : G) := by
    intro t j hj
    let ft : Fin Tag.E6.rank → Multiplicative (ZMod p) :=
      fun k => Multiplicative.ofAdd ((t : Fin Tag.E6.rank → ZMod p) k)
    have het : e ft = Multiplicative.ofAdd (t : Fin Tag.E6.rank → ZMod p) := by
      rw [he]; rfl
    change ((s (e ft) : X) : G) * j = j * ((s (e ft) : X) : G)
    rw [het]
    have hxJ : (⟨j, hJX hj⟩ : X) ∈ J.subgroupOf X := hj
    have hc := hAnn (t : Fin Tag.E6.rank → ZMod p) t.2 ⟨j, hJX hj⟩ hxJ
    exact congrArg (fun z : X => (z : G)) hc
  have hannDim := FrameBs.finrank_le_two_of_centralizer_count hBs ΘB sf hΘsf hJX
    (ggRootAnn p Ψ) hAnnCount bX hbX1 hbXC hcount
  have h4 : 4 ≤ compRank Ψ := by
    have h := le_compRank_of_finrank_ggRootAnn (τ := Tag.E6) (p := p) Ψ hannDim
    have hr : Tag.E6.rank = 6 := rfl
    omega
  have hprim : IsPrimitiveRoot (ζ : AlgebraicClosure K) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζo)
  have ha : ∀ j, a j ^ p = 1 := by
    intro j
    change (ζ ^ (t₀ j).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra hh
    push Not at hh
    have hat : a = 1 := funext hh
    have hTf : T (Multiplicative.ofAdd t₀) = 1 := by
      apply ggKGTl_conj_injective F
      change ggKGTwY F (T (Multiplicative.ofAdd t₀)) = ggKGTwY F 1
      rw [hT]
      change rootDiagUnit TwistTag.E6.tag a = ggKGTwY F 1
      rw [hat]
      exact (CFSG.LieType.Chevalley.E6_rootDiagUnit_one
        (K := AlgebraicClosure K)).trans (map_one (ggKGTwY F)).symm
    exact ht₀ (congrArg Multiplicative.toAdd (hTinj (hTf.trans (map_one T).symm)))
  have h3 : 3 ≤ compRank Ψ := le_trans (by decide) h4
  obtain ⟨v₁, Sd, hSd, hΨnative⟩ := e6_class_levi hp hp2 hprim a ha ha1 i h3
  have hΨnative' : Ψ = (v₁ • ·) '' parabolicRoots Tag.E6 {j : Fin 6 | j ∉ Sd} := hΨnative
  have hcp : ¬p ∣ Nat.card (Subgroup.center X) :=
    TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3 X ψ₀ hA.1 hA.2.1 hA.2.2.1
  let ρ : WeylGroup Tag.E6 →* MulAut (Fin 6 → Multiplicative (ZMod p)) :=
    adMulAutHom TwistTag.E6.tag p
  have hρinj : Function.Injective ρ := adMulAutHom_injective_of_four_lt (by omega)
  have hρact : ∀ (w : WeylGroup Tag.E6) (f : Fin 6 → Multiplicative (ZMod p)),
      (fun j => Multiplicative.toAdd (ρ w f j)) = adAct .E6 p w (fun j => Multiplicative.toAdd (f j)) := by
    intro w f
    funext j
    change Multiplicative.toAdd (adMulAutHom Tag.E6 p w f j) = _
    exact congrArg Multiplicative.toAdd
      (adMulAutHom_apply (τ := Tag.E6) (p := p) w f j)
  have hW : FrameBs.sectionFrameAut (X.subtype.comp sf) X = ρ.range := by
    rw [FrameBs.sectionFrameAut_subtype_comp sf le_rfl, Subgroup.subgroupOf_self]
    exact sectionFrameAut_eq_adMulAutHom_range_twE6 hK hσ F hv hζ T hTinj hT ψ hψ hker hcp sf hsf
  obtain ⟨V, hAdd, hMod, ι, φ, h, α, f, hlin, hrefl, hpair, hf, hclos, hφ, -⟩ :=
    TypeBDatum.exists_E6_datum_of_sectionFrameAut hp2 hp3 hBs ΘB (X.subtype.comp sf)
      (hAut X le_rfl) ρ hρinj hρact hW
  letI : AddCommGroup V := hAdd
  letI : Module (ZMod p) V := hMod
  have hAnnSect : ∀ x : Fin Tag.E6.rank → ZMod p,
      (∀ γ ∈ Ψ, ∑ j, (γ j : ZMod p) * x j = 0) →
      ∀ z ∈ J.subgroupOf X, sf (fun j => Multiplicative.ofAdd (x j)) * z =
        z * sf (fun j => Multiplicative.ofAdd (x j)) := by
    intro x hx z hz
    change s (e (fun j => Multiplicative.ofAdd (x j))) * z =
      z * s (e (fun j => Multiplicative.ofAdd (x j)))
    rw [he]
    exact hAnn x hx z hz
  have hLowSect : ∀ γ ∈ Ψ, ∃ z ∈ J.subgroupOf X, ggKGTwY F (ψ z) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ) := by
    intro γ hγ
    obtain ⟨r, hr, hrep⟩ := ggKGTwJ_weyl hK hσ F hv (isRoot_of_mem_componentRoots hγ)
    obtain ⟨z, hz, hzψ⟩ := hLow γ hγ r hr
    refine ⟨z, hz, ?_⟩
    rw [hzψ]
    exact hrep
  have hSectJ : FrameBs.sectionFrameAut sf (J.subgroupOf X) =
      (Subgroup.closure (rootReflection '' Ψ)).map ρ :=
    sectionFrameAut_eq_rootReflectionClosure_twE6 (by omega) F hζ T hTinj hT ψ hker hcp
      sf hsf (J.subgroupOf X) Ψ v C hΨ hAnnSect hLowSect
  let χ : WeylGroup Tag.E6 →* MulAut Bs := (TypeBDatum.liftBs ΘB).comp ρ
  let χ' : WeylGroup Tag.E6 →* MulAut Bs := (ggAutomizer X Bs).subtype.comp
    (f.toMonoidHom.comp ggE6Row_coxeterGroupEquiv.symm.toMonoidHom)
  have heSimple : ∀ j : Fin 6, ggE6Row_coxeterGroupEquiv.symm (simple Tag.E6 j) =
      CoxeterMatrix.E₆.simple j := by
    intro j
    apply ggE6Row_coxeterGroupEquiv.injective
    rw [ggE6Row_coxeterGroupEquiv.apply_symm_apply, ggE6Row_coxeterGroupEquiv_simple]
  have hχ : χ = χ' := (coxeterSystem Tag.E6).ext_simple (fun j => by
    change TypeBDatum.liftBs ΘB (ρ (simple Tag.E6 j)) =
      (f (ggE6Row_coxeterGroupEquiv.symm (simple Tag.E6 j)) : MulAut Bs)
    rw [heSimple j]
    exact (hφ j).symm.trans (hf j).symm)
  let u : CoxeterMatrix.E₆.Group := ggE6Row_coxeterGroupEquiv.symm v₁
  have hχv : χ v₁ = (f u : MulAut Bs) := congrArg (fun k : WeylGroup Tag.E6 →* MulAut Bs => k v₁) hχ
  have hχsimple : ∀ j, χ (simple Tag.E6 j) = φ j := fun j => (hφ j).symm
  have hJmap : ggAutomizer J Bs = (Subgroup.closure (rootReflection '' Ψ)).map χ := by
    rw [hAut J hJX, FrameBs.sectionFrameAut_subtype_comp sf hJX, hSectJ]
    exact Subgroup.map_map _ (TypeBDatum.liftBs ΘB) ρ
  have hPar : Subgroup.closure (rootReflection '' Ψ) =
      Subgroup.closure ((fun j => v₁ * simple Tag.E6 j * v₁⁻¹) '' {j : Fin 6 | j ∉ Sd}) := by
    rw [hΨnative']
    have hset : rootReflection '' ((v₁ • ·) '' parabolicRoots Tag.E6 {j : Fin 6 | j ∉ Sd}) =
        {w : WeylGroup Tag.E6 | ∃ γ ∈ (v₁ • ·) '' parabolicRoots Tag.E6 {j : Fin 6 | j ∉ Sd},
          w = rootReflection γ} := by
      ext w
      constructor
      · rintro ⟨γ, hγ, hw⟩
        exact ⟨γ, hγ, hw.symm⟩
      · rintro ⟨γ, hγ, hw⟩
        exact ⟨γ, hγ, hw.symm⟩
    rw [hset]
    exact closure_rootReflection_smul_parabolicRoots v₁ {j : Fin 6 | j ∉ Sd}
  have hJrange : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 6 // j ∉ Sd} => χ (v₁ * simple Tag.E6 j.1 * v₁⁻¹)) := by
    rw [hJmap, hPar, MonoidHom.map_closure, Set.image_image, Set.image_eq_range]
    rfl
  have hgen : ∀ j : {j : Fin 6 // j ∉ Sd}, χ (v₁ * simple Tag.E6 j.1 * v₁⁻¹) =
      (f u : MulAut Bs) * φ j.1 * (f u : MulAut Bs)⁻¹ := by
    intro j
    rw [map_mul, map_mul, map_inv, hχv, hχsimple j.1]
  have hJconj : ggAutomizer J Bs = Subgroup.closure (Set.range
      fun j : {j : Fin 6 // j ∉ Sd} => (f u : MulAut Bs) * φ j.1 * (f u : MulAut Bs)⁻¹) :=
    hJrange.trans (congrArg (fun z : {j : Fin 6 // j ∉ Sd} → MulAut Bs =>
      Subgroup.closure (Set.range z)) (funext hgen))
  have hCeq : Tag.cartan .E6 = CartanMatrix.E₆ := by
    rw [show Tag.cartan .E6 = Tag.cartanE 6 from rfl, cartanE_eq]
  have hpair' : ∀ j k, α j (h k) = (Tag.cartan .E6 j k : ZMod p) := by
    simpa only [hCeq] using hpair
  exact ggE6LeviDatum_of_conj hp2 hlin hrefl hpair' hf hclos u hSd hJconj

end CFSG.StandardType

end
