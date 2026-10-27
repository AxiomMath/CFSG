module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.FiniteIndex
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Unbundled
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.SimpleRing.Principal

namespace CFSG
end CFSG
open CFSG

open scoped BigOperators
open Finsupp TensorProduct Module

namespace CFSG.Theory.Representation

open _root_.Representation

attribute [local instance] Fintype.ofFinite

variable {G A V W : Type*}
variable [Group G] [Finite G]
variable [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

noncomputable section

public instance finiteDimensional_coindV
    {H K U : Type*} [Group H] [Group K] [Finite K]
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (φ : H →* K) (ρ : Representation ℂ H U) :
    FiniteDimensional ℂ (Representation.coindV φ ρ) := by
  let _ : FiniteDimensional ℂ (K → U) := inferInstance
  infer_instance

public instance finiteDimensional_ind
    (S : Subgroup G) (ρ : Representation ℂ S A) :
    FiniteDimensional ℂ (Representation.IndV S.subtype ρ) := by
  let _ : FiniteDimensional ℂ (G →₀ ℂ) := inferInstance
  let _ : FiniteDimensional ℂ (TensorProduct ℂ (G →₀ ℂ) A) := inferInstance
  let τ := Representation.tprod ((leftRegular ℂ G).comp S.subtype) ρ
  exact FiniteDimensional.of_surjective (Representation.Coinvariants.mk τ)
    (Representation.Coinvariants.mk_surjective τ)


noncomputable def indToCoindAux
    (S : Subgroup G) (ρ : Representation ℂ S A) (g : G) :
    A →ₗ[ℂ] (G → A) := by
  classical
  exact
    LinearMap.pi fun g₁ =>
      if h : (QuotientGroup.rightRel S).r g₁ g then
        ρ ⟨g₁ * g⁻¹, by
          rcases h with ⟨s, rfl⟩
          exact mul_inv_cancel_right s.1 g ▸ s.2⟩
      else
        0

omit [Finite G] [FiniteDimensional ℂ A] in
@[simp] lemma indToCoindAux_self
    (S : Subgroup G) (ρ : Representation ℂ S A) (g : G) (a : A) :
    indToCoindAux S ρ g a g = a := by
  have hgg : (QuotientGroup.rightRel S).r g g := by
    refine ⟨1, ?_⟩
    simp
  rw [indToCoindAux, LinearMap.pi_apply, dif_pos hgg]
  · have hsub :
        (⟨g * g⁻¹, by
          simp⟩ : S) = 1 := by
      apply Subtype.ext
      simp
    rw [hsub]
    simp

omit [Finite G] [FiniteDimensional ℂ A] in
lemma indToCoindAux_of_not_rel
    (S : Subgroup G) (ρ : Representation ℂ S A)
    (g g₁ : G) (a : A) (h : ¬ (QuotientGroup.rightRel S).r g₁ g) :
    indToCoindAux S ρ g a g₁ = 0 := by
  classical
  rw [indToCoindAux, LinearMap.pi_apply, dif_neg h]
  simp

omit [Finite G] [FiniteDimensional ℂ A] in
@[simp] lemma indToCoindAux_mul_snd
    (S : Subgroup G) (ρ : Representation ℂ S A)
    (g g₁ : G) (a : A) (s : S) :
    indToCoindAux S ρ g a (s * g₁) = ρ s (indToCoindAux S ρ g a g₁) := by
  rcases em ((QuotientGroup.rightRel S).r g₁ g) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s * s₁, mul_assoc ..⟩, dif_pos ⟨s₁, rfl⟩]
    simp [S.smul_def, mul_assoc, ← S.mul_def]
  · rw [indToCoindAux_of_not_rel S ρ _ _ _ h, indToCoindAux_of_not_rel, map_zero]
    exact mt
      (fun ⟨s₁, hs₁⟩ =>
        ⟨s⁻¹ * s₁, by
          change (((s⁻¹ * s₁ : S) : G) * g = g₁)
          calc
            (((s⁻¹ * s₁ : S) : G) * g) = (↑s)⁻¹ * (((s₁ : S) : G) * g) := by
              simp [mul_assoc]
            _ = (↑s)⁻¹ * ((↑s : G) * g₁) := by
              simpa [Subgroup.smul_def] using congrArg (fun z : G => (↑s)⁻¹ * z) hs₁
            _ = g₁ := by simp⟩)
      h

omit [Finite G] [FiniteDimensional ℂ A] in
@[simp] lemma indToCoindAux_mul_fst
    (S : Subgroup G) (ρ : Representation ℂ S A)
    (g₁ g₂ : G) (a : A) (s : S) :
    indToCoindAux S ρ (s * g₁) (ρ s a) g₂ = indToCoindAux S ρ g₁ a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s₁ * s⁻¹, by simp [S.smul_def, smul_eq_mul, mul_assoc]⟩, dif_pos ⟨s₁, rfl⟩,
      ← Module.End.mul_apply, ← map_mul]
    congr
    simp [Subtype.ext_iff, S.smul_def, mul_assoc]
  · rw [indToCoindAux_of_not_rel (S := S) (ρ := ρ) (h := h),
      indToCoindAux_of_not_rel]
    exact mt
      (fun ⟨s₁, hs₁⟩ =>
        ⟨s₁ * s, by
          change (((s₁ * s : S) : G) * g₁ = g₂)
          simpa [Subgroup.smul_def, mul_assoc] using hs₁⟩)
      h

omit [Finite G] [FiniteDimensional ℂ A] in
@[simp] lemma indToCoindAux_snd_mul_inv
    (S : Subgroup G) (ρ : Representation ℂ S A)
    (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux S ρ g₁ a (g₂ * g₃⁻¹) = indToCoindAux S ρ (g₁ * g₃) a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r (g₂ * g₃⁻¹) g₁) with ⟨s, hs⟩ | h
  · simp [S.smul_def, mul_assoc, ← eq_mul_inv_iff_mul_eq.1 hs]
  · rw [indToCoindAux_of_not_rel (S := S) (ρ := ρ) (h := h), indToCoindAux_of_not_rel]
    exact mt
      (fun hs : ∃ s : S, s * (g₁ * g₃) = g₂ =>
        show ∃ t : S, t * g₁ = g₂ * g₃⁻¹ from
          by
            rcases hs with ⟨s, hs⟩
            refine ⟨s, ?_⟩
            simpa [S.smul_def, eq_mul_inv_iff_mul_eq, mul_assoc] using hs)
      h

omit [Finite G] [FiniteDimensional ℂ A] in
@[simp] lemma indToCoindAux_fst_mul_inv
    (S : Subgroup G) (ρ : Representation ℂ S A)
    (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux S ρ (g₁ * g₂⁻¹) a g₃ = indToCoindAux S ρ g₁ a (g₃ * g₂) := by
  simpa using (indToCoindAux_snd_mul_inv S ρ g₁ g₃ g₂⁻¹ a).symm

set_option backward.isDefEq.respectTransparency.types false in
noncomputable abbrev indToCoind
    (S : Subgroup G) (ρ : Representation ℂ S A) :
    Representation.IndV S.subtype ρ →ₗ[ℂ] Representation.coindV S.subtype ρ :=
  Representation.Coinvariants.lift _ (TensorProduct.lift <|
    (linearCombination _ fun g =>
      LinearMap.codRestrict _ (indToCoindAux S ρ g) fun _ _ _ => by simp) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) fun _ => by
        ext x
        simp [LinearMap.codRestrict_apply]

omit [Finite G] [FiniteDimensional ℂ A] in
@[simp] lemma indToCoind_mk
    (S : Subgroup G) (ρ : Representation ℂ S A) (g h : G) (a : A) :
    ((indToCoind S ρ) (Representation.IndV.mk S.subtype ρ g a)).1 h =
      indToCoindAux S ρ g a h := by
  simp [indToCoind, Representation.IndV.mk, LinearMap.comp_apply]
  rfl

@[simps] noncomputable def coindToInd
    (S : Subgroup G) (ρ : Representation ℂ S A) :
    Representation.coindV S.subtype ρ →ₗ[ℂ] Representation.IndV S.subtype ρ where
  toFun f := by
    classical
    let _ : S.FiniteIndex := inferInstance
    let _ := Subgroup.fintypeQuotientOfFiniteIndex (H := S)
    exact
      ∑ g : Quotient (QuotientGroup.rightRel S), Quotient.liftOn g
        (fun g => Representation.IndV.mk S.subtype ρ g (f.1 g))
        fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
          (Submodule.Quotient.eq _).2 <| Representation.Coinvariants.mem_ker_of_eq s
            (MonoidAlgebra.single g₂ 1 ⊗ₜ[ℂ] f.1 g₂) _ <| by
              have := f.2 s g₂
              simp_all
  map_add' _ _ := by
    classical
    let _ : S.FiniteIndex := inferInstance
    let _ := Subgroup.fintypeQuotientOfFiniteIndex (H := S)
    simpa [← Finset.sum_add_distrib, TensorProduct.tmul_add] using
      Finset.sum_congr rfl fun z _ => Quotient.inductionOn z fun _ => by simp
  map_smul' _ _ := by
    classical
    let _ : S.FiniteIndex := inferInstance
    let _ := Subgroup.fintypeQuotientOfFiniteIndex (H := S)
    simpa [Finset.smul_sum] using
      Finset.sum_congr rfl fun z _ => Quotient.inductionOn z fun _ => by simp

omit [FiniteDimensional ℂ A] in
lemma coindToInd_of_support_subset_orbit
    (S : Subgroup G) (ρ : Representation ℂ S A)
    (g : G) (f : Representation.coindV S.subtype ρ)
    (hx : f.1.support ⊆ MulAction.orbit S g) :
    coindToInd S ρ f = Representation.IndV.mk S.subtype ρ g (f.1 g) := by
  classical
  let _ : S.FiniteIndex := inferInstance
  let _ := Subgroup.fintypeQuotientOfFiniteIndex (H := S)
  rw [coindToInd_apply, Finset.sum_eq_single ⟦g⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with
    | h b =>
        have : f.1 b = 0 := by
          simp_all only [Function.support_subset_iff, ne_eq, Quotient.eq]
          contrapose! hx
          exact ⟨b, hx, hb⟩
        simp_all
  · simp

omit [FiniteDimensional ℂ A] in
lemma coindToInd_indToCoind
    (S : Subgroup G) (ρ : Representation ℂ S A) :
    indToCoind S ρ ∘ₗ coindToInd S ρ = LinearMap.id := by
  classical
  let _ : S.FiniteIndex := inferInstance
  let _ := Subgroup.fintypeQuotientOfFiniteIndex (H := S)
  ext g a
  rw [LinearMap.comp_apply, coindToInd_apply, LinearMap.id_apply]
  simp only [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single ⟦a⟧]
  · simp [indToCoind, Representation.IndV.mk, LinearMap.comp_apply]
    simp [LinearMap.codRestrict]
  · intro b _ hb
    induction b using Quotient.inductionOn with
    | h b =>
        simp [indToCoind, Representation.IndV.mk, LinearMap.comp_apply]
        simpa [LinearMap.codRestrict] using
          indToCoindAux_of_not_rel S ρ b a (g.1 b) (mt Quotient.sound hb.symm)
  · simp

omit [FiniteDimensional ℂ A] in
lemma indToCoind_coindToInd
    (S : Subgroup G) (ρ : Representation ℂ S A) :
    coindToInd S ρ ∘ₗ indToCoind S ρ = LinearMap.id := by
  classical
  let _ : S.FiniteIndex := inferInstance
  let _ := Subgroup.fintypeQuotientOfFiniteIndex (H := S)
  ext g a
  simp only [LinearMap.comp_apply, AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.id_apply]
  rw [coindToInd_of_support_subset_orbit S ρ g]
  · simp [indToCoind, Representation.IndV.mk, LinearMap.comp_apply]
    simp [LinearMap.codRestrict]
  · intro x hx
    contrapose! hx
    simp [indToCoind, LinearMap.comp_apply]
    simpa [LinearMap.codRestrict] using indToCoindAux_of_not_rel S ρ g x a hx

public noncomputable def indCoindEquiv
    (S : Subgroup G) (ρ : Representation ℂ S A) :
    (Representation.ind S.subtype ρ).Equiv (Representation.coind S.subtype ρ) := by
  classical
  let f :
      Representation.IntertwiningMap (Representation.ind S.subtype ρ)
        (Representation.coind S.subtype ρ) := by
    refine
      { toLinearMap := indToCoind S ρ
        isIntertwining' := ?_ }
    intro g
    apply Representation.IndV.hom_ext
    intro h
    ext a x
    simp [LinearMap.comp_apply, Representation.coind]
    change indToCoindAux S ρ (h * g⁻¹) a x = indToCoindAux S ρ h a (x * g)
    exact indToCoindAux_fst_mul_inv S ρ h g x a
  refine f.ofBijective ?_
  constructor
  · intro x y hxy
    have hx := congrArg
      (fun T : Representation.IndV S.subtype ρ →ₗ[ℂ] Representation.IndV S.subtype ρ => T x)
      (indToCoind_coindToInd S ρ)
    have hy := congrArg
      (fun T : Representation.IndV S.subtype ρ →ₗ[ℂ] Representation.IndV S.subtype ρ => T y)
      (indToCoind_coindToInd S ρ)
    calc
      x = (coindToInd S ρ) (f x) := by simpa [f, LinearMap.comp_apply] using hx.symm
      _ = (coindToInd S ρ) (f y) := by rw [hxy]
      _ = y := by simpa [f, LinearMap.comp_apply] using hy
  · intro y
    refine ⟨coindToInd S ρ y, ?_⟩
    have hy := congrArg (fun T : Representation.coindV S.subtype ρ →ₗ[ℂ]
        Representation.coindV S.subtype ρ => T y) (coindToInd_indToCoind S ρ)
    simpa [f, LinearMap.comp_apply] using hy

abbrev RightCosets (S : Subgroup G) := Quotient (QuotientGroup.rightRel S)

instance rightCosetsFintype (S : Subgroup G) : Fintype (RightCosets S) := by
  letI : Fintype (G ⧸ S) := Fintype.ofFinite (G ⧸ S)
  exact QuotientGroup.fintypeQuotientRightRel (s := S)

def rightCosetOut (S : Subgroup G) (g : G) : G :=
  Quotient.out (Quotient.mk (QuotientGroup.rightRel S) g)

omit [Finite G] in
theorem rightCosetOut_spec (S : Subgroup G) (g : G) :
    g * (rightCosetOut S g)⁻¹ ∈ S := by
  simpa [rightCosetOut, QuotientGroup.rightRel_apply] using
    (Quotient.mk_out (s := QuotientGroup.rightRel S) g)

omit [Finite G] in
theorem rightCosetOut_eq_of_mk_eq (S : Subgroup G) {g h : G}
    (eq : Quotient.mk (QuotientGroup.rightRel S) g =
      Quotient.mk (QuotientGroup.rightRel S) h) :
    rightCosetOut S g = rightCosetOut S h := by
  exact congrArg Quotient.out eq

omit [Finite G] in
theorem rightCosetOut_out (S : Subgroup G) (q : RightCosets S) :
    rightCosetOut S (Quotient.out q) = Quotient.out q := by
  exact congrArg Quotient.out (Quotient.out_eq q)

def rightCosetCorrection (S : Subgroup G) (g : G) : S :=
  ⟨g * (rightCosetOut S g)⁻¹, rightCosetOut_spec S g⟩

omit [Finite G] in
theorem rightCoset_mk_smul (S : Subgroup G) (s : S) (g : G) :
    Quotient.mk (QuotientGroup.rightRel S) ((s : G) * g) =
      Quotient.mk (QuotientGroup.rightRel S) g := by
  apply Quotient.sound
  change (QuotientGroup.rightRel S).r ((s : G) * g) g
  rw [QuotientGroup.rightRel_apply]
  simp [mul_inv_rev, s.2]

omit [Finite G] in
theorem rightCosetCorrection_smul (S : Subgroup G) (s : S) (g : G) :
    rightCosetCorrection S ((s : G) * g) = s * rightCosetCorrection S g := by
  apply Subtype.ext
  change ((s : G) * g) * (rightCosetOut S ((s : G) * g))⁻¹ =
    (s : G) * (g * (rightCosetOut S g)⁻¹)
  rw [rightCosetOut_eq_of_mk_eq S (rightCoset_mk_smul S s g)]
  simp [mul_assoc]

omit [Finite G] in
theorem subgroupSubtype_correction_mul_out (S : Subgroup G) (g : G) :
    ((rightCosetCorrection S g : S) : G) * rightCosetOut S g = g := by
  simp [rightCosetCorrection, mul_assoc]

omit [Finite G] in
theorem rightCosetCorrection_out (S : Subgroup G) (q : RightCosets S) :
    rightCosetCorrection S (Quotient.out q) = 1 := by
  apply Subtype.ext
  change Quotient.out q * (rightCosetOut S (Quotient.out q))⁻¹ = (1 : G)
  rw [rightCosetOut_out]
  simp

def fixedConjugate (S : Subgroup G) (q : RightCosets S) (g : G)
    (h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q) : S :=
  ⟨Quotient.out q * g * (Quotient.out q)⁻¹, by
    have hrel := Quotient.exact (s := QuotientGroup.rightRel S)
      (h.trans (Quotient.out_eq q).symm)
    change (QuotientGroup.rightRel S).r (Quotient.out q * g) (Quotient.out q) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    simpa [mul_inv_rev, mul_assoc] using (S.inv_mem hrel)⟩

omit [Finite G] in
theorem rightCosetCorrection_fixed (S : Subgroup G) (q : RightCosets S) (g : G)
    (h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q) :
    rightCosetCorrection S (Quotient.out q * g) = fixedConjugate S q g h := by
  apply Subtype.ext
  have hout : rightCosetOut S (Quotient.out q * g) = Quotient.out q := by
    exact congrArg Quotient.out h
  change (Quotient.out q * g) * (rightCosetOut S (Quotient.out q * g))⁻¹ =
    Quotient.out q * g * (Quotient.out q)⁻¹
  rw [hout]

noncomputable def coindVEquivQuotient
    (S : Subgroup G) (ρ : Representation ℂ S A) :
    Representation.coindV S.subtype ρ ≃ₗ[ℂ] (RightCosets S → A) where
  toFun f q := f.1 (Quotient.out q)
  invFun x := by
    refine ⟨fun g => ρ (rightCosetCorrection S g)
      (x (Quotient.mk (QuotientGroup.rightRel S) g)), ?_⟩
    intro s h
    have hq := rightCoset_mk_smul S s h
    have hc := rightCosetCorrection_smul S s h
    simp [hq, hc]
  map_add' f f' := by
    ext q
    rfl
  map_smul' a f := by
    ext q
    rfl
  left_inv f := by
    ext g
    change ρ (rightCosetCorrection S g) (f.1 (rightCosetOut S g)) = f.1 g
    rw [← f.2 (rightCosetCorrection S g) (rightCosetOut S g)]
    simpa using congrArg f.1 (subgroupSubtype_correction_mul_out S g)
  right_inv x := by
    ext q
    change ρ (rightCosetCorrection S (Quotient.out q))
        (x (Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q))) = x q
    rw [rightCosetCorrection_out S q, Quotient.out_eq q]
    simp

def coindCoordinateEnd (S : Subgroup G) (ρ : Representation ℂ S A) (g : G) :
    (RightCosets S → A) →ₗ[ℂ] (RightCosets S → A) :=
  (coindVEquivQuotient S ρ).conj ((Representation.coind S.subtype ρ) g)

omit [Finite G] [FiniteDimensional ℂ A] in
theorem coindCoordinateEnd_apply (S : Subgroup G) (ρ : Representation ℂ S A) (g : G)
    (x : RightCosets S → A) (q : RightCosets S) :
    coindCoordinateEnd S ρ g x q =
      ρ (rightCosetCorrection S (Quotient.out q * g))
        (x (Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g))) := by
  rfl

theorem coindCoordinateEnd_trace_formula
    (S : Subgroup G) [DecidablePred (· ∈ S)] (ρ : Representation ℂ S A) (g : G) :
    LinearMap.trace ℂ (RightCosets S → A) (coindCoordinateEnd S ρ g) =
      ∑ q : RightCosets S,
        if h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q then
          ρ.character (fixedConjugate S q g h)
        else
          0 := by
  classical
  let κ := Module.Free.ChooseBasisIndex ℂ A
  let b : Module.Basis κ ℂ A := Module.Free.chooseBasis ℂ A
  rw [trace_pi_map_perm b
    (fun q : RightCosets S => Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g))
    (fun q : RightCosets S => ρ (rightCosetCorrection S (Quotient.out q * g)))
    (coindCoordinateEnd S ρ g)]
  · refine Finset.sum_congr rfl ?_
    intro q hq
    by_cases h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q
    · simp [h, rightCosetCorrection_fixed S q g h, Representation.character]
    · simp [h]
  · intro x q
    exact coindCoordinateEnd_apply S ρ g x q

theorem coind_character_formula
    (S : Subgroup G) [DecidablePred (· ∈ S)] (ρ : Representation ℂ S A) (g : G) :
    (Representation.coind S.subtype ρ).character g =
      ∑ q : RightCosets S,
        if h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q then
          ρ.character (fixedConjugate S q g h)
        else
          0 := by
  rw [Representation.character, ← coindCoordinateEnd_trace_formula S ρ g]
  exact (LinearMap.trace_conj'
    ((Representation.coind S.subtype ρ) g) (coindVEquivQuotient S ρ)).symm

noncomputable def quotientMkFiberEquivSubgroup
    (S : Subgroup G) (q : RightCosets S) :
    {x : G // Quotient.mk (QuotientGroup.rightRel S) x = q} ≃ S where
  toFun x := by
    refine ⟨x.1 * (Quotient.out q)⁻¹, ?_⟩
    have hrel : (QuotientGroup.rightRel S).r (Quotient.out q) x.1 := by
      exact Quotient.exact ((Quotient.out_eq q).trans x.2.symm)
    simpa [QuotientGroup.rightRel_apply] using hrel
  invFun s := by
    refine ⟨(s : G) * Quotient.out q, ?_⟩
    calc
      Quotient.mk (QuotientGroup.rightRel S) ((s : G) * Quotient.out q) =
          Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q) := by
            apply Quotient.sound
            change (QuotientGroup.rightRel S).r ((s : G) * Quotient.out q) (Quotient.out q)
            rw [QuotientGroup.rightRel_apply]
            simp [mul_inv_rev, s.2]
      _ = q := Quotient.out_eq q
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv s := by
    apply Subtype.ext
    simp [mul_assoc]

omit [Finite G] in
theorem quotientMk_fiber_nat_card (S : Subgroup G) (q : RightCosets S) :
    Nat.card {x : G // Quotient.mk (QuotientGroup.rightRel S) x = q} = Nat.card S := by
  exact Nat.card_congr (quotientMkFiberEquivSubgroup S q)

theorem quotient_sum_lift_rightRel
    (S : Subgroup G) (F : RightCosets S → ℂ) :
    (∑ x : G, F (Quotient.mk (QuotientGroup.rightRel S) x)) =
      (Nat.card S : ℂ) * (∑ q : RightCosets S, F q) := by
  classical
  calc
    (∑ x : G, F (Quotient.mk (QuotientGroup.rightRel S) x)) =
        ∑ q : RightCosets S, ∑ x : {x : G //
          Quotient.mk (QuotientGroup.rightRel S) x = q}, F (Quotient.mk
            (QuotientGroup.rightRel S) (x : G)) := by
      exact (Fintype.sum_fiberwise
        (g := fun x : G => Quotient.mk (QuotientGroup.rightRel S) x)
        (f := fun x : G => F (Quotient.mk (QuotientGroup.rightRel S) x))).symm
    _ = ∑ q : RightCosets S, ∑ _x : {x : G //
          Quotient.mk (QuotientGroup.rightRel S) x = q}, F q := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp [x.2]
    _ = ∑ q : RightCosets S, (Nat.card S : ℂ) * F q := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rw [← quotientMk_fiber_nat_card S q]
      simp
    _ = (Nat.card S : ℂ) * ∑ q : RightCosets S, F q := by
      rw [Finset.mul_sum]

def fiberCorrection (S : Subgroup G) (q : RightCosets S)
    (x : {x : G // Quotient.mk (QuotientGroup.rightRel S) x = q}) : S := by
  refine ⟨x.1 * (Quotient.out q)⁻¹, ?_⟩
  have hrel : (QuotientGroup.rightRel S).r (Quotient.out q) x.1 := by
    exact Quotient.exact ((Quotient.out_eq q).trans x.2.symm)
  simpa [QuotientGroup.rightRel_apply] using hrel

omit [Finite G] in
theorem fiberCorrection_mul_out (S : Subgroup G) (q : RightCosets S)
    (x : {x : G // Quotient.mk (QuotientGroup.rightRel S) x = q}) :
    ((fiberCorrection S q x : S) : G) * Quotient.out q = x.1 := by
  change (x.1 * (Quotient.out q)⁻¹) * Quotient.out q = x.1
  simp [mul_assoc]

omit [Finite G] in
theorem fiberConjugate_eq_raw (S : Subgroup G) (q : RightCosets S)
    (x : {x : G // Quotient.mk (QuotientGroup.rightRel S) x = q}) (g : G) :
    x.1 * g * x.1⁻¹ =
      (fiberCorrection S q x : G) *
        (Quotient.out q * g * (Quotient.out q)⁻¹) *
        (fiberCorrection S q x : G)⁻¹ := by
  rw [← fiberCorrection_mul_out S q x]
  simp [mul_assoc]

omit [Finite G] in
theorem quotient_mk_mul_out_eq_iff
    (S : Subgroup G) (q : RightCosets S) (g : G) :
    Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q ↔
      Quotient.out q * g * (Quotient.out q)⁻¹ ∈ S := by
  constructor
  · intro h
    exact (fixedConjugate S q g h).2
  · intro hq
    calc
      Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) =
          Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q) := by
            apply Quotient.sound
            change (QuotientGroup.rightRel S).r (Quotient.out q * g) (Quotient.out q)
            rw [QuotientGroup.rightRel_apply]
            have hq' : (Quotient.out q * g * (Quotient.out q)⁻¹)⁻¹ ∈ S := S.inv_mem hq
            simpa [mul_inv_rev, mul_assoc] using hq'
      _ = q := Quotient.out_eq q

omit [Finite G] in
theorem quotient_fiber_conjugate_mem_iff
    (S : Subgroup G) (q : RightCosets S) (g : G)
    (x : {x : G // Quotient.mk (QuotientGroup.rightRel S) x = q}) :
    x.1 * g * x.1⁻¹ ∈ S ↔
      Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q := by
  constructor
  · intro hx
    have hmid : Quotient.out q * g * (Quotient.out q)⁻¹ ∈ S := by
      have htmp : (fiberCorrection S q x : G)⁻¹ * (x.1 * g * x.1⁻¹) *
          (fiberCorrection S q x : G) ∈ S := by
        exact S.mul_mem (S.mul_mem (S.inv_mem (fiberCorrection S q x).2) hx)
          (fiberCorrection S q x).2
      simpa [fiberConjugate_eq_raw S q x g, mul_assoc] using htmp
    exact (quotient_mk_mul_out_eq_iff S q g).2 hmid
  · intro hq
    have hmid : Quotient.out q * g * (Quotient.out q)⁻¹ ∈ S :=
      (quotient_mk_mul_out_eq_iff S q g).1 hq
    rw [fiberConjugate_eq_raw S q x g]
    exact S.mul_mem (S.mul_mem (fiberCorrection S q x).2 hmid)
      (S.inv_mem (fiberCorrection S q x).2)

omit [Finite G] [FiniteDimensional ℂ A] in
theorem quotient_fiber_character_term
    (S : Subgroup G) [DecidablePred (· ∈ S)] (ρ : Representation ℂ S A) (g : G)
    (q : RightCosets S)
    (x : {x : G // Quotient.mk (QuotientGroup.rightRel S) x = q}) :
    (if hx : x.1 * g * x.1⁻¹ ∈ S then
      ρ.character ⟨x.1 * g * x.1⁻¹, hx⟩
    else
      0) =
    (if h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q then
      ρ.character (fixedConjugate S q g h)
    else
      0) := by
  have hmemiff := quotient_fiber_conjugate_mem_iff S q g x
  by_cases hfix : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q
  · have hx : x.1 * g * x.1⁻¹ ∈ S := hmemiff.mpr hfix
    simp [hx, hfix]
    have hs :
        (⟨x.1 * g * x.1⁻¹, hx⟩ : S) =
          fiberCorrection S q x * fixedConjugate S q g hfix * (fiberCorrection S q x)⁻¹ := by
      apply Subtype.ext
      simp [fiberConjugate_eq_raw S q x g, fixedConjugate, mul_assoc]
    rw [hs]
    exact Representation.char_conj (ρ := ρ)
      (g := fixedConjugate S q g hfix) (h := fiberCorrection S q x)
  · have hx : ¬ x.1 * g * x.1⁻¹ ∈ S := by
      exact fun hx => hfix (hmemiff.mp hx)
    simp [hfix, hx]

/-- Character formula for induced representations. -/
public theorem induced_character_formula
    (S : Subgroup G) [DecidablePred (· ∈ S)] (ρ : Representation ℂ S A) (g : G) :
    (Representation.ind S.subtype ρ).character g =
      (Nat.card S : ℂ)⁻¹ * ∑ x : G,
        if hx : x * g * x⁻¹ ∈ S then
          ρ.character ⟨x * g * x⁻¹, hx⟩
        else
          0 := by
  classical
  let F : RightCosets S → ℂ := fun q =>
    if h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q then
      ρ.character (fixedConjugate S q g h)
    else
      0
  have hcardS_ne : (Nat.card S : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card S ≠ 0)
  have hindcoind :
      (Representation.ind S.subtype ρ).character =
        (Representation.coind S.subtype ρ).character :=
    Representation.char_iso (indCoindEquiv S ρ)
  have hsum :
      (∑ x : G,
        if hx : x * g * x⁻¹ ∈ S then
          ρ.character ⟨x * g * x⁻¹, hx⟩
        else
          0) =
      ∑ x : G, F (Quotient.mk (QuotientGroup.rightRel S) x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    let q : RightCosets S := Quotient.mk (QuotientGroup.rightRel S) x
    let xq : {x' : G // Quotient.mk (QuotientGroup.rightRel S) x' = q} := ⟨x, rfl⟩
    simpa [F, q, xq] using quotient_fiber_character_term S ρ g q xq
  have hsumF :
      (∑ x : G,
        if hx : x * g * x⁻¹ ∈ S then
          ρ.character ⟨x * g * x⁻¹, hx⟩
        else
          0) =
      (Nat.card S : ℂ) * (∑ q : RightCosets S, F q) := by
    rw [hsum]
    exact quotient_sum_lift_rightRel S F
  calc
    (Representation.ind S.subtype ρ).character g
      = ∑ q : RightCosets S, F q := by
          rw [hindcoind, coind_character_formula S ρ g]
    _ = (Nat.card S : ℂ)⁻¹ * ∑ x : G,
          if hx : x * g * x⁻¹ ∈ S then
            ρ.character ⟨x * g * x⁻¹, hx⟩
          else
            0 := by
      rw [hsumF]
      field_simp [hcardS_ne]

public lemma eigenvalue_pow_eq_one_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ}
    (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    μ ^ n = 1 := by
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  have hvpow : (f ^ n) v = μ ^ n • v := hv.pow_apply n
  have hv_eq : v = μ ^ n • v := by
    simpa [hpow] using hvpow
  have hsmul : (1 - μ ^ n) • v = 0 := by
    rw [sub_smul, one_smul, ← hv_eq, sub_self]
  rcases smul_eq_zero.mp hsmul with hzero | hzero
  · exact (sub_eq_zero.mp hzero).symm
  · exact (hv.2 hzero).elim

lemma eigenvalue_ne_zero_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    μ ≠ 0 := by
  have hμpow : μ ^ n = 1 := eigenvalue_pow_eq_one_of_pow_eq_one hpow hμ
  intro hzero
  rw [hzero] at hμpow
  simp [hn] at hμpow

lemma eigenvalue_unit_mem_rootsOfUnity_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ} [NeZero n]
    (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    (Units.mk0 μ
      (eigenvalue_ne_zero_of_pow_eq_one (n := n) (show n ≠ 0 from NeZero.ne n) hpow hμ) : ℂˣ) ∈
        rootsOfUnity n ℂ := by
  rw [mem_rootsOfUnity]
  ext
  simpa using eigenvalue_pow_eq_one_of_pow_eq_one hpow hμ

lemma complex_star_eigenvalue_eq_inv_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ} [NeZero n]
    (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    star μ = μ⁻¹ := by
  simpa using
    (Complex.conj_rootsOfUnity
      (ζ := Units.mk0 μ
        (eigenvalue_ne_zero_of_pow_eq_one (n := n) (show n ≠ 0 from NeZero.ne n) hpow hμ))
      (n := n) (eigenvalue_unit_mem_rootsOfUnity_of_pow_eq_one (n := n) hpow hμ))

lemma complex_star_eigenvalue_eq_pow_pred_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    star μ = μ ^ (n - 1) := by
  have hn0 : NeZero n := ⟨hn⟩
  rw [@complex_star_eigenvalue_eq_inv_of_pow_eq_one _ _ _ _ _ _ _ hn0 hpow hμ]
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  apply inv_eq_of_mul_eq_one_right
  simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using
    eigenvalue_pow_eq_one_of_pow_eq_one hpow hμ

public lemma eigenspace_iSup_eq_top_over_eigenvalues
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hf : f.IsSemisimple) :
    ⨆ μ : f.Eigenvalues, f.eigenspace (μ : ℂ) = ⊤ := by
  calc
    ⨆ μ : f.Eigenvalues, f.eigenspace (μ : ℂ) = ⨆ μ : ℂ, f.eigenspace μ := by
      apply le_antisymm
      · exact iSup_le fun μ => le_iSup (fun ν : ℂ => f.eigenspace ν) μ
      · refine iSup_le fun μ => ?_
        by_cases hμ : f.HasEigenvalue μ
        · exact le_iSup (fun ν : f.Eigenvalues => f.eigenspace (ν : ℂ)) ⟨μ, hμ⟩
        · have hbot : f.eigenspace μ = ⊥ := by
            by_contra hne
            exact hμ hne
          simp [hbot]
    _ = ⊤ := hf.iSup_eigenspace_eq_top

public lemma end_isSemisimple_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1) :
    f.IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := ((Polynomial.X : Polynomial ℂ) ^ n - 1)) ?_ ?_
  · exact
      ((Polynomial.X_pow_sub_one_separable_iff (F := ℂ) (n := n)).2 (by
        exact_mod_cast hn)).squarefree
  · simp [map_sub, map_pow, Polynomial.aeval_X, hpow]

public lemma trace_restrict_pow_eigenspace_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (μ : f.Eigenvalues) (k : ℕ) :
    LinearMap.trace ℂ (f.eigenspace (μ : ℂ))
      ((f ^ k).restrict
        (Module.End.pow_apply_mem_of_forall_mem k
          (f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
            (Module.End.eigenspace_mem_invtSubmodule f (μ : ℂ))))) =
      (μ : ℂ) ^ k * Module.finrank ℂ (f.eigenspace (μ : ℂ)) := by
  let hμ :
      ∀ x : V, x ∈ f.eigenspace (μ : ℂ) → f x ∈ f.eigenspace (μ : ℂ) :=
    f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
      (Module.End.eigenspace_mem_invtSubmodule f (μ : ℂ))
  have hrestrict :
      ((f ^ k).restrict (Module.End.pow_apply_mem_of_forall_mem k hμ)) =
        ((μ : ℂ) ^ k • LinearMap.id : Module.End ℂ (f.eigenspace (μ : ℂ))) := by
    calc
      ((f ^ k).restrict (Module.End.pow_apply_mem_of_forall_mem k hμ)) = (f.restrict hμ) ^ k := by
        symm
        exact Module.End.pow_restrict k hμ
      _ = (((μ : ℂ) • LinearMap.id : Module.End ℂ (f.eigenspace (μ : ℂ))) ^ k) := by
        rw [Module.End.restrict_eigenspace]
      _ = ((μ : ℂ) ^ k • (LinearMap.id : Module.End ℂ (f.eigenspace (μ : ℂ)))) := by
        simpa using smul_pow (μ : ℂ) (LinearMap.id : Module.End ℂ (f.eigenspace (μ : ℂ))) k
      _ = (μ : ℂ) ^ k • LinearMap.id := by
        simp
  rw [hrestrict]
  simp [LinearMap.trace_id, smul_eq_mul]

public lemma trace_pow_eq_sum_eigenvalues
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {n k : ℕ}
    (hn : n ≠ 0) (hpow : f ^ n = 1) :
    LinearMap.trace ℂ V (f ^ k) =
      ∑ μ : f.Eigenvalues, ((μ : ℂ) ^ k * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
  classical
  let N : f.Eigenvalues → Submodule ℂ V := fun μ => f.eigenspace (μ : ℂ)
  have hsemi : f.IsSemisimple := end_isSemisimple_of_pow_eq_one f hn hpow
  have hindep : iSupIndep N := by
    change iSupIndep (f.eigenspace ∘ (fun μ : f.Eigenvalues => (μ : ℂ)))
    exact f.eigenspaces_iSupIndep.comp Subtype.coe_injective
  have htop : iSup N = ⊤ := by
    simpa [N] using eigenspace_iSup_eq_top_over_eigenvalues (f := f) hsemi
  have hds : DirectSum.IsInternal N :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep htop
  have hmap : ∀ μ : f.Eigenvalues, Set.MapsTo (f ^ k) (N μ) (N μ) := by
    intro μ
    exact Module.End.pow_apply_mem_of_forall_mem k
      (f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
        (Module.End.eigenspace_mem_invtSubmodule f (μ : ℂ)))
  calc
    LinearMap.trace ℂ V (f ^ k) =
      ∑ μ : f.Eigenvalues, LinearMap.trace ℂ (N μ) ((f ^ k).restrict (hmap μ)) := by
        simpa [N] using LinearMap.trace_eq_sum_trace_restrict hds hmap
    _ = ∑ μ : f.Eigenvalues, ((μ : ℂ) ^ k * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
      refine Finset.sum_congr rfl ?_
      intro μ hμ
      simpa [N] using trace_restrict_pow_eigenspace_eq (f := f) μ k


lemma trace_pow_pred_eq_star_trace_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {n : ℕ}
    (hn : n ≠ 0) (hpow : f ^ n = 1) :
    LinearMap.trace ℂ V (f ^ (n - 1)) = star (LinearMap.trace ℂ V f) := by
  classical
  have htrace :
      LinearMap.trace ℂ V f =
        ∑ μ : f.Eigenvalues, ((μ : ℂ) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
    simpa using (trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow)
  have htracePred :
      LinearMap.trace ℂ V (f ^ (n - 1)) =
        ∑ μ : f.Eigenvalues, ((μ : ℂ) ^ (n - 1) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
    simpa using (trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := n - 1) hn hpow)
  rw [htracePred, htrace]
  calc
    ∑ μ : f.Eigenvalues, ((μ : ℂ) ^ (n - 1) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) =
      ∑ μ : f.Eigenvalues, star (((μ : ℂ) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro μ hμ
        rw [star_mul]
        simp [complex_star_eigenvalue_eq_pow_pred_of_pow_eq_one (f := f) (μ := (μ : ℂ)) hn hpow
          μ.property, mul_comm]
    _ = star (∑ μ : f.Eigenvalues, ((μ : ℂ) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) : ℂ) := by
      symm
      simp

public lemma representation_character_inv_eq_star_character
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = star (ρ.character g) := by
  let n := orderOf g
  have hn : n ≠ 0 := Nat.ne_of_gt (orderOf_pos g)
  have hpow : (ρ g) ^ n = 1 := by
    subst n
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  have hginv : g ^ (n - 1) = g⁻¹ := by
    subst n
    have hmul : g ^ (orderOf g - 1) * g = 1 := by
      calc
        g ^ (orderOf g - 1) * g = g ^ ((orderOf g - 1) + 1) := by
          rw [pow_succ]
        _ = g ^ orderOf g := by
          congr 1
          exact Nat.sub_add_cancel (Nat.succ_le_of_lt (orderOf_pos g))
        _ = 1 := pow_orderOf_eq_one g
    exact eq_inv_iff_mul_eq_one.mpr hmul
  calc
    ρ.character g⁻¹ = LinearMap.trace ℂ V (ρ g⁻¹) := rfl
    _ = LinearMap.trace ℂ V ((ρ g) ^ (n - 1)) := by
      rw [← hginv, MonoidHom.map_pow]
    _ = star (LinearMap.trace ℂ V (ρ g)) := by
      simpa using trace_pow_pred_eq_star_trace_of_pow_eq_one (f := ρ g) (n := n) hn hpow
    _ = star (ρ.character g) := rfl


end

end CFSG.Theory.Representation
