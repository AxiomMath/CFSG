module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.FrameAct
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentPerm
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Data
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.StandardType.NTPlane

section Core

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups commutatorElement

private theorem ntpA2shape_core_split
    {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (Fr : L →+* L)
    (θ : SL(3, L) →* ModGL τ L) (π : Equiv.Perm (Fin 3))
    (hθ : ∀ (a b : Fin 3) (hab : a ≠ b), ∃ β : Lˣ, ∀ c : L,
      θ (Matrix.SpecialLinearGroup.transvection hab c) =
        pinnedX τ L (σ (π a) (π b)) ((β : L) * Fr c)) :
    ∃ B : GL (Fin 3) L, ∀ X : SL(3, L), θ X =
      ψ (slConjugation 3 L B (Matrix.SpecialLinearGroup.map Fr X)) := by
  classical
  choose β hβ using hθ
  choose ε hε using hψ.transv
  let G : Fin 3 → Fin 3 → Lˣ := fun a b =>
    if h : a ≠ b then (ε (π a) (π b) (π.injective.ne h))⁻¹ * β a b h else 1
  have hG : ∀ a b (hab : a ≠ b), G a b =
      (ε (π a) (π b) (π.injective.ne hab))⁻¹ * β a b hab := by
    intro a b hab
    simp only [G, dif_pos hab]
  have hg : ∀ (a b : Fin 3) (hab : a ≠ b) (c : L),
      θ (Matrix.SpecialLinearGroup.transvection hab c) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((G a b : L) * Fr c)) := by
    intro a b hab c
    have h2 := hε (π a) (π b) (π.injective.ne hab) ((G a b : L) * Fr c)
    have hβG : ε (π a) (π b) (π.injective.ne hab) * G a b = β a b hab := by
      rw [hG a b hab]; group
    rw [hβ a b hab c, h2]
    congr 1
    rw [← hβG, Units.val_mul, mul_assoc]
  have hinj : ∀ (a b : Fin 3) (hab : a ≠ b) (e e' : L),
      ψ (Matrix.SpecialLinearGroup.transvection hab e) =
        ψ (Matrix.SpecialLinearGroup.transvection hab e') → e = e' := by
    intro a b hab e e' heq
    have h1 := hε a b hab e
    have h2 := hε a b hab e'
    rw [h1, h2] at heq
    exact mul_left_cancel₀ (Units.ne_zero (ε a b hab))
      (pinnedX_injective τ L (σ a b) heq)
  have hcocycle : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c → G a b * G b c = G a c := by
    intro a b c hab hbc hac
    have h1 : θ ⁅Matrix.SpecialLinearGroup.transvection hab (1 : L),
        Matrix.SpecialLinearGroup.transvection hbc (1 : L)⁆ =
        θ (Matrix.SpecialLinearGroup.transvection hac (1 : L)) := by
      rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) (1 : L),
        mul_one]
    rw [map_commutatorElement, hg a b hab 1, hg b c hbc 1, hg a c hac 1,
      ← map_commutatorElement] at h1
    simp only [map_one, mul_one] at h1
    have hπ := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (π.injective.ne hab) (π.injective.ne hbc) (π.injective.ne hac)
      ((G a b : L)) ((G b c : L))
    rw [hπ] at h1
    have he := hinj (π a) (π c) (π.injective.ne hac)
      ((G a b : L) * (G b c : L)) ((G a c : L)) h1
    exact Units.ext (by rw [Units.val_mul]; exact he)
  have third : ∀ y z : Fin 3, y ≠ z → ∃ x, x ≠ y ∧ x ≠ z := by decide
  have hGinv : ∀ y z (hyz : y ≠ z), G y z * G z y = 1 := by
    intro y z hyz
    obtain ⟨x, hxy, hxz⟩ := third y z hyz
    have h1 := hcocycle x y z hxy hyz hxz
    have h2 := hcocycle x z y hxz hyz.symm hxy
    have h3 : G x y * (G y z * G z y) = G x y * 1 := by
      rw [mul_one, ← mul_assoc, h1, h2]
    exact mul_left_cancel h3
  let d : Fin 3 → Lˣ := fun a => if _ : a ≠ (0 : Fin 3) then G a 0 else 1
  have hd0 : d 0 = 1 := by simp [d]
  have hda : ∀ a (ha : a ≠ (0 : Fin 3)), d a = G a 0 := by
    intro a ha; simp [d, ha]
  have hgd : ∀ a b (hab : a ≠ b), G a b = d a * (d b)⁻¹ := by
    intro a b hab
    by_cases ha0 : a = 0
    · subst ha0
      rw [hd0, one_mul, hda b (Ne.symm hab)]
      exact eq_inv_of_mul_eq_one_left (hGinv 0 b hab)
    · by_cases hb0 : b = 0
      · subst hb0
        rw [hd0, inv_one, mul_one, hda a ha0]
      · rw [hda a ha0, hda b hb0, ← hcocycle a 0 b ha0 (Ne.symm hb0) hab,
          eq_inv_of_mul_eq_one_left (hGinv 0 b (Ne.symm hb0))]
  let P : GL (Fin 3) L := TauCeti.permutationGL π
  let D : GL (Fin 3) L := TauCeti.diagGL d
  let B : GL (Fin 3) L := P * D
  have hconj : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      slConjugation 3 L B (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection (π.injective.ne hij) ((G i j : L) * t) := by
    intro i j hij t
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_slConjugation, TauCeti.toGL_transvection_eq_transvectionUnit,
      TauCeti.toGL_transvection_eq_transvectionUnit]
    change (P * D) * TauCeti.transvectionUnit hij t * (P * D)⁻¹ =
      TauCeti.transvectionUnit (π.injective.ne hij) ((G i j : L) * t)
    have hD : D * TauCeti.transvectionUnit hij t * D⁻¹ =
        TauCeti.transvectionUnit hij ((d i : L) * t * ((d j)⁻¹ : Lˣ)) :=
      TauCeti.diagGL_mul_transvectionUnit_mul_inv (A := L) (N := 3) hij d t
    have hP : P * TauCeti.transvectionUnit hij ((d i : L) * t * ((d j)⁻¹ : Lˣ)) * P⁻¹ =
        TauCeti.transvectionUnit (π.injective.ne hij)
          ((d i : L) * t * ((d j)⁻¹ : Lˣ)) := by
      have hsymm : TauCeti.permutationGL (k := L) π.symm =
          (TauCeti.permutationGL (k := L) π)⁻¹ := by
        rw [← map_inv]
        rfl
      have h := TauCeti.permutationGL_inv_mul_transvectionUnit_mul_permutationGL
        (A := L) (n := Fin 3) π.symm hij ((d i : L) * t * ((d j)⁻¹ : Lˣ))
      rw [hsymm, inv_inv] at h
      simpa only [P] using h
    calc (P * D) * TauCeti.transvectionUnit hij t * (P * D)⁻¹
        = P * (D * TauCeti.transvectionUnit hij t * D⁻¹) * P⁻¹ := by group
      _ = P * TauCeti.transvectionUnit hij ((d i : L) * t * ((d j)⁻¹ : Lˣ)) * P⁻¹ := by
            rw [hD]
      _ = TauCeti.transvectionUnit (π.injective.ne hij)
            ((d i : L) * t * ((d j)⁻¹ : Lˣ)) := hP
      _ = TauCeti.transvectionUnit (π.injective.ne hij) ((G i j : L) * t) := by
            rw [hgd i j hij]
            congr 1
            push_cast
            ring
  refine ⟨B, fun X => ?_⟩
  have heq : θ = (ψ.comp (slConjugation 3 L B).toMonoidHom).comp
      (Matrix.SpecialLinearGroup.map Fr) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    show θ (Matrix.SpecialLinearGroup.transvection hij t) =
      ψ (slConjugation 3 L B (Matrix.SpecialLinearGroup.map Fr
        (Matrix.SpecialLinearGroup.transvection hij t)))
    rw [hg i j hij t, Matrix.SpecialLinearGroup.map_transvection, hconj i j hij (Fr t)]
  exact DFunLike.congr_fun heq X

end Core

section Graph

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm
open scoped MatrixGroups

private theorem ntpA2shape_frame_core
    {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (Fr : L →+* L)
    (θ : SL(3, L) →* ModGL τ L) (π : Equiv.Perm (Fin 3)) (e : Bool)
    (hθ : ∀ (a b : Fin 3) (hab : a ≠ b), ∃ β : Lˣ, ∀ c : L,
      θ (Matrix.SpecialLinearGroup.transvection hab c) =
        pinnedX τ L (if e then σ (π b) (π a) else σ (π a) (π b)) ((β : L) * Fr c)) :
    ∃ B : GL (Fin 3) L, ∀ X : SL(3, L), θ X =
      ψ (slConjugation 3 L B (if e then slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr X)
        else Matrix.SpecialLinearGroup.map Fr X)) := by
  cases e with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hθ ⊢
    exact ntpA2shape_core_split hψ Fr θ π hθ
  | true =>
    simp only [↓reduceIte] at hθ ⊢
    have hδ : ∀ (a b : Fin 3) (hab : a ≠ b) (c : L),
        slGraphAut 3 L (Matrix.SpecialLinearGroup.transvection hab c) =
          Matrix.SpecialLinearGroup.transvection hab.symm (-c) := by
      intro a b hab c
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [toGL_slGraphAut, TauCeti.toGL_transvection_eq_transvectionUnit,
        TauCeti.toGL_transvection_eq_transvectionUnit]
      exact TauCeti.inverseTranspose_transvectionUnit hab c
    obtain ⟨B, hB⟩ := ntpA2shape_core_split hψ Fr (θ.comp (slGraphAut 3 L).toMonoidHom) π (by
      intro a b hab
      obtain ⟨β, hβ⟩ := hθ b a hab.symm
      refine ⟨-β, fun c => ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hδ a b hab c, hβ (-c), map_neg, Units.val_neg]
      congr 1
      ring)
    refine ⟨B, fun X => ?_⟩
    have hδδ : slGraphAut 3 L (slGraphAut 3 L X) = X := (slGraphAut 3 L).left_inv X
    have hmap : Matrix.SpecialLinearGroup.map Fr (slGraphAut 3 L X) =
        slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr X) := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, slGraphAut_matrix, ← map_inv,
        RingHom.mapMatrix_apply, Matrix.transpose_map]
    have h1 := hB (slGraphAut 3 L X)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hδδ] at h1
    rw [h1, hmap]

end Graph

section Pin

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

private theorem ntpA2shape_pinned
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ψ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {κ : ℤ} (hκ : κ ≠ 0) (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    (w : WeylGroup τ) (hmaps : ∀ a b, a ≠ b → w • S.ρ (σ a b) ∈ frameRoots σ)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ S.D.q) :
    ∃ (π : Equiv.Perm (Fin 3)) (e : Bool), ∀ (a b : Fin 3) (hab : a ≠ b), ∃ β : Lˣ, ∀ c : L,
      canonicalRep (coxeterSystem τ) L w *
          S.D.step (ψ (Matrix.SpecialLinearGroup.transvection hab c)) *
          (canonicalRep (coxeterSystem τ) L w)⁻¹ =
        pinnedX τ L (if e then σ (π b) (π a) else σ (π a) (π b)) ((β : L) * Fr c) := by
  classical
  have key : ∀ (a b : Fin 3) (hab : a ≠ b), ∃ β : Lˣ, ∀ c : L,
      canonicalRep (coxeterSystem τ) L w *
          S.D.step (ψ (Matrix.SpecialLinearGroup.transvection hab c)) *
          (canonicalRep (coxeterSystem τ) L w)⁻¹ =
        pinnedX τ L (w • S.ρ (σ a b)) ((β : L) * Fr c) := by
    intro a b hab
    obtain ⟨ε, hε⟩ := hψ.transv a b hab
    obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S (hψ.isRoot a b hab)
    obtain ⟨ν, hν, hνX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w
      ((S.frob.isRoot_iff (σ a b)).2 (hψ.isRoot a b hab))
    have hν0 : ν ≠ 0 := by
      rintro rfl
      simp at hν
    refine ⟨Units.mk0 (ν * μ * (ε : L) ^ S.D.q)
      (mul_ne_zero (mul_ne_zero hν0 hμ0) (pow_ne_zero _ (Units.ne_zero ε))), fun c => ?_⟩
    rw [hε c, hμ, hνX, hFr, Units.val_mk0, mul_pow]
    congr 1
    ring
  rcases hψ.aut_cases le_rfl hκ hnorm (fun γ => w • S.ρ γ) hmaps
      (fun γ => by simp only [S.frob.neg_eq, smul_neg])
      (fun γ δ => by simp only [iform_smul, S.frob.iform_eq]) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · refine ⟨π, false, fun a b hab => ?_⟩
    obtain ⟨β, hβ⟩ := key a b hab
    exact ⟨β, fun c => by rw [hβ c, hπ a b hab]; rfl⟩
  · refine ⟨π, true, fun a b hab => ?_⟩
    obtain ⟨β, hβ⟩ := key a b hab
    exact ⟨β, fun c => by rw [hβ c, hπ a b hab]; rfl⟩

end Pin

section Weyl

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ntpA2shape_exists_not_commute_pinnedX_neg
    {τ : Tag} {K : Type} [Field K]
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ c d : K, pinnedX τ K β c * pinnedX τ K (-β) d ≠
      pinnedX τ K (-β) d * pinnedX τ K β c := by
  obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨ε₁, -, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_single τ i)
  obtain ⟨ε₂, -, hY⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_neg_single τ i)
  refine ⟨ε₁ * 1, ε₂ * 1, fun h => ?_⟩
  refine not_commute_xUnit_yUnit (τ := τ) (K := K) i ?_
  have e1 := hX 1
  have e2 := hY 1
  rw [pinnedX_single] at e1
  rw [pinnedX_neg_single, smul_neg] at e2
  set n := canonicalRep (coxeterSystem τ) K w
  have h' : (n * xUnit τ K i 1 * n⁻¹) * (n * yUnit τ K i 1 * n⁻¹) =
      (n * yUnit τ K i 1 * n⁻¹) * (n * xUnit τ K i 1 * n⁻¹) := by
    rw [e1, e2]
    exact h
  show xUnit τ K i 1 * yUnit τ K i 1 = yUnit τ K i 1 * xUnit τ K i 1
  calc xUnit τ K i 1 * yUnit τ K i 1
      = n⁻¹ * ((n * xUnit τ K i 1 * n⁻¹) * (n * yUnit τ K i 1 * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * yUnit τ K i 1 * n⁻¹) * (n * xUnit τ K i 1 * n⁻¹)) * n := by rw [h']
    _ = yUnit τ K i 1 * xUnit τ K i 1 := by group

private theorem ntpA2shape_eq_of_componentRootSpan_le
    {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {j j' : KernelComponent χ}
    (h : componentRootSpan K χ j ≤ componentRootSpan K χ j') : j = j' := by
  by_contra hne
  obtain ⟨a, ha⟩ := Quotient.exists_rep j
  have hγ : (a : Fin τ.rank → ℤ) ∈ componentRoots χ j := ⟨a.2, ha⟩
  have hneg : -(a : Fin τ.rank → ℤ) ∈ componentRoots χ j :=
    (isRootComponent_componentRoots j).neg_mem _ hγ
  obtain ⟨c, d, hcd⟩ :=
    ntpA2shape_exists_not_commute_pinnedX_neg (K := K) (isRoot_of_mem_componentRoots hγ)
  have hx : pinnedX τ K (a : Fin τ.rank → ℤ) c ∈ componentRootSpan K χ j :=
    pinnedX_mem_rootSpan hγ c
  have hy : pinnedX τ K (-(a : Fin τ.rank → ℤ)) d ∈ componentRootSpan K χ j' :=
    h (pinnedX_mem_rootSpan hneg d)
  exact hcd (commute_of_mem_componentRootSpan hne hx hy).eq

private theorem ntpA2shape_weyl_fix
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i₀ : KernelComponent (rootCharHom a)) {w : WeylGroup τ} (hw : w ∈ rootCharStabilizer a)
    {m : ModGL τ L} (hm : m ∈ toralRootGroup τ L a)
    (hk : ∀ y ∈ componentRootSpan L (rootCharHom a) i₀,
      m * canonicalRep (coxeterSystem τ) L w * S.D.step y *
          (m * canonicalRep (coxeterSystem τ) L w)⁻¹ ∈ componentRootSpan L (rootCharHom a) i₀) :
    (fun γ => w • S.ρ γ) '' componentRoots (rootCharHom a) i₀ =
      componentRoots (rootCharHom a) i₀ := by
  obtain ⟨j', hj'⟩ := outer_exists_image_component S hT i₀
  obtain ⟨j, hj⟩ := exists_weyl_image_component a hw j'
  have himg : (fun γ => w • S.ρ γ) '' componentRoots (rootCharHom a) i₀ =
      componentRoots (rootCharHom a) j := by
    rw [← hj, ← hj', Set.image_image]
  have hstep : (componentRootSpan L (rootCharHom a) i₀).map S.D.step =
      componentRootSpan L (rootCharHom a) j' := by
    change (rootSpan τ L (componentRoots (rootCharHom a) i₀)).map S.D.step =
      rootSpan τ L (componentRoots (rootCharHom a) j')
    rw [map_rootSpan_step S _ (fun α hα => isRoot_of_mem_componentRoots hα), hj']
  have hconj : (componentRootSpan L (rootCharHom a) j').map
      (MulAut.conj (m * canonicalRep (coxeterSystem τ) L w)).toMonoidHom =
        componentRootSpan L (rootCharHom a) j :=
    map_conj_componentRootSpan a hw hm hj
  have hle : componentRootSpan L (rootCharHom a) j ≤ componentRootSpan L (rootCharHom a) i₀ := by
    rw [← hconj, ← hstep, Subgroup.map_map]
    rintro _ ⟨y, hy, rfl⟩
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hk y hy
  rw [himg, ntpA2shape_eq_of_componentRootSpan_le _ hle]

end Weyl

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm
open scoped MatrixGroups

theorem ntpA2_shape
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L)
    (hpair : OrderThreeOutsideConnected S a n) (hker : (rootCharKernel a).ncard = 18)
    (i₀ : KernelComponent (rootCharHom a))
    (φ : SL(3, L) →* ModGL .E6 L) (σφ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
    (hφ : IsSLFrame φ σφ) (hΨ : componentRoots (rootCharHom a) i₀ = frameRoots σφ)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ S.D.q)
    (k : ℕ) (hk : ∀ y ∈ φ.range, n ^ k * S.D.step y * (n ^ k)⁻¹ ∈ φ.range) :
    ∃ (B : GL (Fin 3) L) (e : Bool), ∀ X : SL(3, L),
      n ^ k * S.D.step (φ X) * (n ^ k)⁻¹ =
        φ (slConjugation 3 L B (if e then slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr X)
          else Matrix.SpecialLinearGroup.map Fr X)) := by
  classical
  obtain ⟨-, hT, -, hnM, -, hcomm, -⟩ := hpair
  have hn : n ∈ toralCentralizer Tag.E6 L a :=
    mem_toralCentralizer.2 ⟨(S.D.mem_model.1 hnM).1, by rw [hcomm, mul_inv_cancel_right]⟩
  obtain ⟨w, hw, m, hm, hnk⟩ :=
    exists_mul_canonicalRep_of_mem_toralCentralizer a (Subgroup.pow_mem _ hn k)
  have hrange : φ.range = componentRootSpan L (rootCharHom a) i₀ := by
    rw [hφ.range, ← hΨ]
    rfl
  have hfix := ntpA2shape_weyl_fix S hT i₀ hw hm fun y hy => by
    rw [← hrange] at hy ⊢
    rw [← hnk]
    exact hk y hy
  have hmaps : ∀ x y, x ≠ y → w • S.ρ (σφ x y) ∈ frameRoots σφ := by
    intro x y hxy
    have h1 : w • S.ρ (σφ x y) ∈ (fun γ => w • S.ρ γ) '' componentRoots (rootCharHom a) i₀ :=
      ⟨σφ x y, by rw [hΨ]; exact ⟨x, y, hxy, rfl⟩, rfl⟩
    rwa [hfix, hΨ] at h1
  have hnorm : ∀ x y, x ≠ y →
      CFSG.LieType.Steinberg.Adjoint.iform (σφ x y) (σφ x y) = 2 * 1 := fun x y hxy => by
    rw [mul_one]
    exact CFSG.ClassicalInvolution.ModelFacts.Levi.iform_self_isRoot_E6 (hφ.isRoot x y hxy)
  obtain ⟨π, e, hshape⟩ := ntpA2shape_pinned S hφ one_ne_zero hnorm w hmaps Fr hFr
  let θ : SL(3, L) →* ModGL Tag.E6 L :=
    ((MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L w)).toMonoidHom.comp S.D.step).comp φ
  have hθ : ∀ X, θ X = canonicalRep (coxeterSystem Tag.E6) L w * S.D.step (φ X) *
      (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ := fun X => by
    simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨B', hB'⟩ := ntpA2shape_frame_core hφ Fr θ π e fun x y hxy => by
    obtain ⟨β, hβ⟩ := hshape x y hxy
    exact ⟨β, fun c => (hθ _).trans (hβ c)⟩
  obtain ⟨Bm, hBm⟩ := exists_frameAct_of_mem_toralRootGroup i₀ hφ hΨ hm
  have hBm' : ∀ Y, m * φ Y * m⁻¹ = φ (slConjugation 3 L Bm Y) := fun Y => by
    have h := hBm Y
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact h
  refine ⟨Bm * B', e, fun X => ?_⟩
  have h1 : n ^ k * S.D.step (φ X) * (n ^ k)⁻¹ = m * θ X * m⁻¹ := by
    rw [hθ, hnk]
    group
  rw [h1, hB' X, hBm', map_mul, MulAut.mul_apply]

end CFSG.StandardType.NTPlane

end
