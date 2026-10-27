module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitClassFunctionInner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResRank1
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Dickson.Sec6.I1431
open CFSG.RankThree.Chevalley
open scoped MatrixGroups



theorem e6IsogenyFixed_nodeHom0_sl2Diag
    {k : Type} [Field k] [Finite k] (θ : k →+* k)
    (t : (fixedField θ)ˣ) :
    CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed θ
        (nodeHom0 θ (sl2Diag (fixedField θ) t)) =
      excresTheta .E6 (fixedField θ) (Pi.single (nd 1) 1) 1
        (sl2Diag (fixedField θ) t) := by
  let K := fixedField θ
  let s : kˣ := Units.map K.subtype.toMonoidHom t
  let a : Fin (Tag.rank .E6) := nd 1
  let β : Fin (Tag.rank .E6) → ℤ := Pi.single a 1
  have hnode : (nodeHom0 θ (sl2Diag K t) : e6Data_valid.minGroup k) =
      e6Data_valid.hm k a s := by
    change e6Rank1 k a (liftSL θ 2 (sl2Diag K t)) = e6Data_valid.hm k a s
    have hdiag : sl2Diag K t = CFSG.ClassicalInvolution.WeakCT.torusHom K t := by
      apply Subtype.ext
      simp [sl2Diag, CFSG.ClassicalInvolution.WeakCT.coe_torusHom]
    have htorus : liftSL θ 2 (sl2Diag K t) = torusHom k s := by
      rw [hdiag]
      exact liftSL_torusHom θ t
    rw [htorus]
    exact e6Rank1_hm (k := k) (a := a) s
  have hL : CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed θ
        (nodeHom0 θ (sl2Diag K t)) =
      (rootDiagUnit .E6 (fun j => s ^ Tag.E6.cartan a j) : ModGL .E6 k) := by
    rw [CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed_apply]
    change ((CFSG.LieType.Steinberg.Isogeny.e6Isogeny k
      (nodeHom0 θ (sl2Diag K t) : e6Data_valid.minGroup k) :
        adjointGroup .E6 k) : ModGL .E6 k) =
      rootDiagUnit .E6 (fun j => s ^ Tag.E6.cartan a j)
    rw [hnode]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_hm_eq a s
  have hR : excresTheta .E6 K β 1 (sl2Diag K t) =
      (rootDiagUnit .E6 (fun j => s ^ Tag.E6.cartan a j) : ModGL .E6 k) := by
    rw [excresTheta_apply, one_mul, inv_one, mul_one]
    rw [baseChangeGL_rootSL2_of_field]
    have hmap : Matrix.SpecialLinearGroup.map K.subtype (sl2Diag K t) = sl2Diag k s := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, sl2Diag, s]
    rw [hmap]
    change (rootSL2 .E6 k (Pi.single a 1) (sl2Diag k s)) =
      rootDiagUnit .E6 (fun j => s ^ Tag.E6.cartan a j)
    have hroot : rootSL2 .E6 k (Pi.single a 1) (sl2Diag k s) =
        simpleRootSL2 .E6 k a (sl2Diag k s) := by
      rw [rootSL2_apply]
      simp [pinnedWeyl, pinnedData_single]
    rw [hroot]
    rw [show sl2Diag k s = HSL s by rfl]
    rw [simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]
  rw [hL, hR]

theorem odd_normalizer_inner_nodeHom0
    {k : Type} [Field k] [Finite k] (θ : k →+* k)
    {g : fixedGroup k θ}
    (hg : g ∈ Subgroup.normalizer ((nodeHom0 θ).range : Set (fixedGroup k θ)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ (nodeHom0 θ).range, ∀ x ∈ (nodeHom0 θ).range,
      g * x * g⁻¹ = r * x * r⁻¹ := by
  let K := fixedField θ
  let ρ : SL2 K →* fixedGroup k θ := nodeHom0 θ
  let χ : fixedGroup k θ → k := fun x => LinearMap.trace k (RootModule TwistTag.E6.tag k)
    (CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed θ x : Module.End k (RootModule TwistTag.E6.tag k))
  have hker : ∀ A : SL2 K, ρ A = 1 → ∃ c : Kˣ, c ^ 2 = 1 ∧
      (A : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
    intro A hA
    have hA1 : A = 1 := rFixed_injective θ (nd 1) rfl (by simpa [ρ] using hA)
    exact ⟨1, by simp, by rw [hA1]; simp⟩
  have hχ : ∀ x y : fixedGroup k θ, χ (y * x * y⁻¹) = χ x := by
    intro x y
    dsimp [χ]
    simp only [map_mul, map_inv, Units.val_mul, LinearMap.trace_conj]
  have hχd : ∀ t : Kˣ, χ (ρ (sl2Diag K t)) =
      K.subtype (((t : K) + (t : K)⁻¹) ^ 2 + (20 : K) * ((t : K) + (t : K)⁻¹)) + 34 := by
    intro t
    change LinearMap.trace k (RootModule TwistTag.E6.tag k)
      (CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed θ (nodeHom0 θ (sl2Diag K t)) :
        Module.End k (RootModule TwistTag.E6.tag k)) = _
    have htorus := e6IsogenyFixed_nodeHom0_sl2Diag θ t
    change CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed θ (nodeHom0 θ (sl2Diag K t)) =
      excresTheta TwistTag.E6.tag K (Pi.single (nd 1) 1) 1 (sl2Diag K t) at htorus
    rw [htorus]
    rw [excres_trace_theta (τ := TwistTag.E6.tag) (Or.inl rfl)]
    change K.subtype (Polynomial.aeval
      (Matrix.trace (sl2Diag K t : Matrix (Fin 2) (Fin 2) K))
      (Polynomial.X ^ 2 + 20 * Polynomial.X + 34)) = _
    simp [sl2Diag, Matrix.trace_fin_two, map_ofNat]
    rfl
  exact excres_normalizer_inner_of_odd (ρ := ρ) hker K.subtype 20 34 χ hχ hχd hgo
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)

theorem odd_normalizer_inner_fundamental_twistedE6_model
    {p : ℕ} [hp : Fact p.Prime] (_hp2 : p ≠ 2) (n e : ℕ)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .twistedE6 n p e)
    {R : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv .twistedE6 n p e hp.out).K}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .twistedE6
      (CFSG.ClassicalInvolution.Generic.modelUniv .twistedE6 n p e hp.out).D)
    {g : (CFSG.ClassicalInvolution.Generic.modelUniv .twistedE6 n p e hp.out).K}
    (hg : g ∈ Subgroup.normalizer
      (R : Set (CFSG.ClassicalInvolution.Generic.modelUniv .twistedE6 n p e hp.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain rfl : n = 0 := hadm.2.2
  let k := GaloisField p (2 * e)
  let θ : k →+* k := frobQ p e
  let R' : Subgroup (fixedGroup k θ) := R
  let g' : fixedGroup k θ := g
  have hR'generic : R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups
      .twistedE6 (twistedDatum k θ) := hR
  have hg' : g' ∈ Subgroup.normalizer (R' : Set (fixedGroup k θ)) := hg
  have hgo' : Odd (orderOf g') := hgo
  change ∃ r ∈ R', ∀ x ∈ R', g' * x * g'⁻¹ = r * x * r⁻¹
  let R0 : Subgroup (fixedGroup k θ) := (nodeHom0 θ).range
  let D := twistedDatum k θ
  let α : Fin D.rank → ℤ := Pi.single (nf 0) 1
  have hlong : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot D α :=
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .twistedE6 0 p e hp.out
      trivial hadm (nf 0) (by show 0 < 2; decide)
  have hR0 : R0 ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups .twistedE6 D := by
    refine ⟨1, α, Or.inl hlong, ?_⟩
    change R0 = CFSG.ClassicalInvolution.Generic.conjSub 1 (D.rootGroup α ⊔ D.rootGroup (-α))
    rw [CFSG.ClassicalInvolution.Generic.conjSub_one]
    exact (rankOne_twistedE6_zero θ).symm
  have hR' : R' ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups .twistedE6 D := by
    rcases hR'generic with ⟨c, γ, hγ, rfl⟩
    refine ⟨c, γ, ?_, rfl⟩
    rcases hγ with hγ | ⟨hG2, _⟩ | ⟨hD4, _⟩
    · exact Or.inl ((CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff
        (D := D) (γ := γ)).mpr ⟨hγ.1, hγ.2⟩)
    · cases hG2
    · cases hD4
  have hsingle : CFSG.ClassicalInvolution.ModelFacts.FundamentalSingleClass .twistedE6 D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass
      .twistedE6 0 p e hp.out trivial hadm (by decide) (by decide)
  obtain ⟨c, hc⟩ := hsingle R0 hR0 R' hR'
  have hR_eq : R' = CFSG.ClassicalInvolution.Generic.conjSub c R0 := hc
  have hg0 : c⁻¹ * g' * c ∈ Subgroup.normalizer (R0 : Set (fixedGroup k θ)) := by
    rw [hR_eq, Subgroup.mem_normalizer_iff] at hg'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : c * x * c⁻¹ ∈ CFSG.ClassicalInvolution.Generic.conjSub c R0 :=
        CFSG.ClassicalInvolution.Generic.conj_mem_conjSub hx
      have h := (hg' _).mp hx'
      rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff] at h
      simpa [mul_assoc] using h
    · intro hx
      have hx' : g' * (c * x * c⁻¹) * g'⁻¹ ∈ CFSG.ClassicalInvolution.Generic.conjSub c R0 := by
        rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff]
        simpa [mul_assoc] using hx
      have h := (hg' _).mpr hx'
      rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff] at h
      simpa [mul_assoc] using h
  have hgo0 : Odd (orderOf (c⁻¹ * g' * c)) := by
    have h : orderOf (c⁻¹ * g' * c) = orderOf g' := by
      simpa [MulAut.conj_apply] using (MulAut.conj c⁻¹).orderOf_eq g'
    rwa [h]
  obtain ⟨r, hr, hinner⟩ := odd_normalizer_inner_nodeHom0 θ hg0 hgo0
  refine ⟨c * r * c⁻¹, hR_eq ▸ CFSG.ClassicalInvolution.Generic.conj_mem_conjSub hr, ?_⟩
  intro x hx
  rw [hR_eq, CFSG.ClassicalInvolution.Generic.mem_conjSub_iff] at hx
  have h := hinner (c⁻¹ * x * c) hx
  calc
    g' * x * g'⁻¹ = c * ((c⁻¹ * g' * c) * (c⁻¹ * x * c) * (c⁻¹ * g' * c)⁻¹) * c⁻¹ := by group
    _ = c * (r * (c⁻¹ * x * c) * r⁻¹) * c⁻¹ := by rw [h]
    _ = (c * r * c⁻¹) * x * (c * r * c⁻¹)⁻¹ := by group

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
