module

public import CFSG.LocalAnalysis.StandardType.PhanEResFrame
public import CFSG.LocalAnalysis.StandardType.PhanEFlagChart
public import CFSG.LocalAnalysis.StandardType.PhanEClassify
public import CFSG.LocalAnalysis.StandardType.PhanEStdBuildingData
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate
public import CFSG.LocalAnalysis.StandardType.PhanELocalProd

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.AGLEmbeddingD2.ParabLevi

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

@[expose] def IsFrame (J : Set (Fin D.rank)) (a : K ⧸ borel D H) (g : K) (v : W)
    (I : Set (Fin D.rank)) (t₀ l₀ : K) : Prop :=
  I ⊆ J ∧
    residue (cs) (stdδ hct) J a = residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H) ∧
    Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a =
      residue (cs) (stdδ hct) I ((g : K) : K ⧸ borel D H) ∧
    t₀ ∈ ⨆ k, H k ∧ l₀ ∈ leviM D I ∧
    ∀ l ∈ leviM D I,
      Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a ((g * l : K) : K ⧸ borel D H) =
        ((g * t₀ * l₀ * (nrep hct v * F.φ l * (nrep hct v)⁻¹) : K) : K ⧸ borel D H)

@[expose] def ChartOf {ι Ω : Type} {Y : ChamberSystem ι Ω} (J : Set (Fin D.rank))
    (a : K ⧸ borel D H)
    (Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
      (residue (cs) (stdδ hct) J a)) Y) (R₀' : Set Ω) (ψ' : Ω → Ω) : Prop :=
  (∀ x : ↥(residue (cs) (stdδ hct) J a),
    (x : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a ↔
      Θ.Φ x ∈ R₀') ∧
  ∀ x x' : ↥(residue (cs) (stdδ hct) J a),
    (x : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a →
    (x' : K ⧸ borel D H) =
      Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a (x : K ⧸ borel D H) →
    Θ.Φ x' = ψ' (Θ.Φ x)

include hext hw₀ hsq in
theorem exists_psiRes (hpanel : StdPanel hct F (nrep hct w₀)) (J : Set (Fin D.rank))
    (a : K ⧸ borel D H) :
    ∃ ψ : ↥(residue (cs) (stdδ hct) J a) → ↥(residue (cs) (stdδ hct) J a),
      (∀ x : ↥(residue (cs) (stdδ hct) J a),
        ((ψ x : ↥(residue (cs) (stdδ hct) J a)) : K ⧸ borel D H) =
          Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a (x : K ⧸ borel D H)) ∧
      (∀ x : ↥(residue (cs) (stdδ hct) J a),
        (x : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a →
        ((ψ x : ↥(residue (cs) (stdδ hct) J a)) : K ⧸ borel D H) ∈
          Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a) ∧
      ∀ x : ↥(residue (cs) (stdδ hct) J a),
        (x : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a →
        ψ (ψ x) = x := by
  have hB : IsWeylDistanceBuilding (cs) (stdδ hct) :=
    (stdBuildingData hct F hext hw₀ hsq hpanel).building
  have hw : ∀ w : W, (cs).length (w * w₀) + (cs).length w = (cs).length w₀ :=
    (stdBuildingData hct F hext hw₀ hsq hpanel).longest
  have ht : Gate.IsFlipInvolution (cs) (stdδ hct) w₀ (stdFlip F (nrep hct w₀)) :=
    Gate.isFlipInvolution_of_isSphericalFlip
      (stdBuildingData hct F hext hw₀ hsq hpanel).flip
  refine ⟨fun x =>
      ⟨Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a (x : K ⧸ borel D H),
        resProj_mem hB J a (stdFlip F (nrep hct w₀) (x : K ⧸ borel D H))⟩,
    fun _ => rfl, fun x hx => Gate.flipPsi_mem hB hw ht hx,
    fun x hx => Subtype.ext (Gate.flipPsi_flipPsi hB hw ht hx)⟩

include hext hw₀ hsq in
theorem phanEResidueModel_of_chartOf (hpanel : StdPanel hct F (nrep hct w₀))
    {Fld : Type} [Field Fld] [Finite Fld] [CharP Fld 2] {f : ℕ}
    (hK : Nat.card Fld = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {J : Set (Fin D.rank)} {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)}
    {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀) (code : PhanCode)
    (Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
      (residue (cs) (stdδ hct) J a)) (code.sys Fld))
    (hΘ : ChartOf hct F J a Θ (code.R0 Fld) (code.psi Fld f hK)) :
    PhanEResidueModel (cs) (stdδ hct) Fld f (stdFlip F (nrep hct w₀)) J a code := by
  obtain ⟨hIJ, -, hcore, -, -, -⟩ := hfr
  have hB : IsWeylDistanceBuilding (cs) (stdδ hct) :=
    (stdBuildingData hct F hext hw₀ hsq hpanel).building
  have hw : ∀ w : W, (cs).length (w * w₀) + (cs).length w = (cs).length w₀ :=
    (stdBuildingData hct F hext hw₀ hsq hpanel).longest
  have ht : Gate.IsFlipInvolution (cs) (stdδ hct) w₀ (stdFlip F (nrep hct w₀)) :=
    Gate.isFlipInvolution_of_isSphericalFlip
      (stdBuildingData hct F hext hw₀ hsq hpanel).flip
  haveI : Finite ((cs).parabolic J) := by
    haveI : Finite W := finite_group D.isFiniteType
    infer_instance
  refine Flag.phanEResidueModel_of_chart hB hw ht hcore hIJ hK hq code Θ ?_ ?_
  · intro c
    rw [← hcore]
    exact hΘ.1 c
  · intro c c' hc hc'
    exact hΘ.2 c c' (by rwa [hcore]) hc'

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
