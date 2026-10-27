module

public import CFSG.LocalAnalysis.StandardType.PhanEClassify
public import CFSG.LocalAnalysis.StandardType.PhanEResSL
public import CFSG.LocalAnalysis.StandardType.PhanEStdBuildingData
public import CFSG.LocalAnalysis.StandardType.PhanEMatchCases
public import CFSG.LocalAnalysis.StandardType.PhanEMatchCasesX
public import CFSG.LocalAnalysis.StandardType.PhanEMatchDiagram
public import CFSG.LocalAnalysis.StandardType.PhanEMatchPath
public import CFSG.LocalAnalysis.StandardType.PhanEMatchLink

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group

theorem phanEResidueModels_of_charts
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {w₀ : W} (F : FrobData D n H w₀)
    (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
    (hsq : ∀ i, n i * n i = 1) (hpanel : StdPanel hct F (nrep hct w₀))
    {Fld : Type} [Field Fld] [Finite Fld] [CharP Fld 2] {f : ℕ}
    (hK : Nat.card Fld = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (M : ChevModel2 D n H Fld) (θ : Fld →+* Fld) (PC : M.PhiCompat F θ)
    (hθ : θ = (sg Fld f : Fld →+* Fld)) (hred : D.divisible = ∅)
    (hsl : ∀ i j : Fin D.rank, i ≠ j →
      coxeterMatrix D.isFiniteType i j = 2 ∨ coxeterMatrix D.isFiniteType i j = 3)
    (charts : ∀ (m : ℕ) (e : Fin m → Fin D.rank), 1 ≤ m → m ≤ 3 → Function.Injective e →
      (∀ k l : Fin m, D.cartan (e k) (e l) =
        if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) →
      ∃ L : Res.SLPath M m, L.e = e) :
    PhanEResidueModels Fld f (coxeterMatrix D.isFiniteType) (stdδ hct)
      (stdFlip F (nrep hct w₀)) := by
  subst hθ
  have hsl' : ∀ i j : Fin D.rank, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1 :=
    cartan_sl_of_coxeter D.isFiniteType hsl
  have hSL : SLDiagram D.cartan := SLDiagram.of_isFiniteType D.isFiniteType hsl'
  intro J a hJ
  obtain ⟨g, v, I, π, t₀, l₀, hIJ, hR, hcore, hπ', ht₀, hl₀, hψ⟩ :=
    Res.exists_frame hct hext F hw₀ hsq hred (Res.phi_rankOne_le F M PC) J a
  have hfr : IsFrame hct F J a g v I t₀ l₀ := ⟨hIJ, hR, hcore, ht₀, hl₀, hψ⟩
  have hw₀sq : w₀ * w₀ = 1 := hw₀.mul_self
  have hπI : ∀ i ∈ I, π i ∈ I := fun i hi => (hπ' i hi).1
  have hππ : ∀ i ∈ I, π (π i) = i := fun i hi => (hπ' i hi).2.1
  have hπw : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1 :=
    fun i hi => (hπ' i hi).2.2
  have hπA : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      (D.cartan (π i) (π j) ≠ 0 ↔ D.cartan i j ≠ 0) :=
    fun i hi j hj hij => adj_iff_pi D.isFiniteType hw₀sq F.hop hπw hi hj hij
  obtain ⟨c, σ, hshape, hrank, hinj, hrange, hadj, hcoreσ, hpermσ⟩ :=
    exists_code_matches_rank hSL hIJ hπI hππ hπA hJ
  refine ⟨c, hrank, ?_⟩
  have hm : Matches D.cartan c σ J I π := ⟨hinj, hrange, hadj, hcoreσ, hpermσ⟩
  rcases hshape with ⟨-, hsh⟩ | ⟨-, hsh⟩
  · cases hsh with
    | path hc =>
        exact residueModel_path hct hext F hw₀ hsq hpanel hK hq PC charts (Or.inl hc) σ hm hfr hπw
    | exch =>
        exact residueModel_exchA1A1 hct hext F hw₀ hsq hpanel hK hq PC charts σ hm hfr hπw
    | nodes ha hb =>
        exact residueModel_prod hct hext F hw₀ hsq hpanel hK hq PC charts (Or.inl ha) hb σ hm hfr
          hπw
  · cases hsh with
    | path hc =>
        exact residueModel_path hct hext F hw₀ hsq hpanel hK hq PC charts (Or.inr hc) σ hm hfr hπw
    | exchPencil =>
        exact residueModel_exchA2A1 hct hext F hw₀ hsq hpanel hK hq PC charts σ hm hfr hπw
    | pathNode ha hb =>
        exact residueModel_prod hct hext F hw₀ hsq hpanel hK hq PC charts (Or.inr ha) hb σ hm hfr
          hπw
    | exchNode hb =>
        exact residueModel_exch3 hct hext F hw₀ hsq hpanel hK hq PC charts hb σ hm hfr hπw
    | nodes3 ha hb hb' =>
        exact residueModel_prod3 hct hext F hw₀ hsq hpanel hK hq PC charts ha hb hb' σ hm hfr hπw

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
