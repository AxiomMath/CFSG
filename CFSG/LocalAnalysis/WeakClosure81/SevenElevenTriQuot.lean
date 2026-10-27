module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriRep
public import CFSG.RankThree.FFModules.ChiefFactors

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

open Subgroup

structure TrialityHyp {Γ X : Type} [Group Γ] [Group X] (π : Γ →* X) (𝔇 : Set Γ) (s : X) :
    Prop where
  surj : Function.Surjective π
  ker : IsPGroup 2 π.ker
  sq : s ^ 2 = 1
  gen : Subgroup.normalClosure ({s} : Set X) = ⊤
  image : π '' 𝔇 = {x : X | IsConj s x}
  cent : ∀ r : X, IsConj s r → Subgroup.centralizer ({r} : Set X) =
    Subgroup.closure ({x : X | IsConj s x} ∩ (Subgroup.centralizer ({r} : Set X) : Set X))
  line : ∃ a b t : X, IsConj s a ∧ IsConj s b ∧ IsConj s t ∧ orderOf (a * b) = 3 ∧
    orderOf (t * a) = 3 ∧ orderOf (t * b) = 3 ∧ orderOf (t * (b * a * b⁻¹)) = 3

structure TrialityIdent {Γ X A : Type} [Group Γ] [Group X] [AddCommGroup A] [Module (ZMod 2) A]
    (π : Γ →* X) (𝔇 : Set Γ) (ρ : Γ →* Module.End (ZMod 2) A) : Prop where
  comm : ∀ d ∈ 𝔇, ∀ e ∈ 𝔇, π d * π e = π e * π d → (ρ d - 1) * (ρ e - 1) = 0
  braid : ∀ d ∈ 𝔇, ∀ e ∈ 𝔇, orderOf (π d * π e) = 3 →
    (ρ d - 1) * (ρ e - 1) * (ρ d - 1) = ρ d - 1

open CFSG.RankThree.FFModules

private lemma triaQuot_toRepresentation_coe {Γ A : Type} [Group Γ] [AddCommGroup A]
    [Module (ZMod 2) A] {ρ : Representation (ZMod 2) Γ A} (U' : Subrepresentation ρ)
    (g : Γ) (x : U'.toSubmodule) :
    (((U'.toRepresentation g) x : U'.toSubmodule) : A) = ρ g x.1 :=
  rfl

private lemma triaQuot_factorRep_sub_one_mk {Γ A : Type} [Group Γ] [AddCommGroup A]
    [Module (ZMod 2) A] {ρ : Representation (ZMod 2) Γ A} (U U' : Subrepresentation ρ)
    (g : Γ) (x : U'.toSubmodule) :
    (factorRep U U' g - 1) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((U'.toRepresentation g - 1) x) := by
  rw [LinearMap.sub_apply, Module.End.one_apply, factorRep_mk]
  show (factorSub U U').mkQ (U'.toRepresentation g x) - (factorSub U U').mkQ x =
    (factorSub U U').mkQ ((U'.toRepresentation g - 1) x)
  rw [← map_sub, LinearMap.sub_apply, Module.End.one_apply]

private lemma triaQuot_factorRep_sub_one_mul {Γ A : Type} [Group Γ] [AddCommGroup A]
    [Module (ZMod 2) A] {ρ : Representation (ZMod 2) Γ A} (U U' : Subrepresentation ρ)
    {d e : Γ} (h : (ρ d - 1) * (ρ e - 1) = 0) :
    (factorRep U U' d - 1) * (factorRep U U' e - 1) = 0 := by
  have hres : (U'.toRepresentation d - 1) * (U'.toRepresentation e - 1) = 0 := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    have hx := congrArg (fun f : Module.End (ZMod 2) A => f x.1) h
    simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply, Submodule.coe_sub, Submodule.coe_zero,
      triaQuot_toRepresentation_coe] using hx
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (p := factorSub U U') y
  simp only [Module.End.mul_apply, LinearMap.zero_apply, triaQuot_factorRep_sub_one_mk]
  rw [show (U'.toRepresentation d - 1) ((U'.toRepresentation e - 1) x) = 0 from by
    rw [← Module.End.mul_apply, hres, LinearMap.zero_apply]]
  rfl

private lemma triaQuot_factorRep_sub_one_braid {Γ A : Type} [Group Γ] [AddCommGroup A]
    [Module (ZMod 2) A] {ρ : Representation (ZMod 2) Γ A} (U U' : Subrepresentation ρ)
    {d e : Γ} (h : (ρ d - 1) * (ρ e - 1) * (ρ d - 1) = ρ d - 1) :
    (factorRep U U' d - 1) * (factorRep U U' e - 1) * (factorRep U U' d - 1) =
      factorRep U U' d - 1 := by
  have hres : (U'.toRepresentation d - 1) * (U'.toRepresentation e - 1)
      * (U'.toRepresentation d - 1) = U'.toRepresentation d - 1 := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    have hx := congrArg (fun f : Module.End (ZMod 2) A => f x.1) h
    simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_sub, triaQuot_toRepresentation_coe] using hx
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (p := factorSub U U') y
  simp only [Module.End.mul_apply, triaQuot_factorRep_sub_one_mk]
  rw [show (U'.toRepresentation d - 1) ((U'.toRepresentation e - 1)
      ((U'.toRepresentation d - 1) x)) = (U'.toRepresentation d - 1) x from by
    show ((U'.toRepresentation d - 1) * (U'.toRepresentation e - 1)
      * (U'.toRepresentation d - 1)) x = (U'.toRepresentation d - 1) x
    rw [hres]]

private theorem triality_ident_factorRep {Γ X A : Type} [Group Γ] [Group X] [AddCommGroup A]
    [Module (ZMod 2) A] {π : Γ →* X} {𝔇 : Set Γ} {ρ : Representation (ZMod 2) Γ A}
    (U U' : Subrepresentation ρ) (hI : TrialityIdent π 𝔇 ρ) :
    TrialityIdent π 𝔇 (factorRep U U') := by
  refine ⟨?_, ?_⟩
  · intro d hd e he hde
    exact triaQuot_factorRep_sub_one_mul U U' (hI.comm d hd e he hde)
  · intro d hd e he hde
    exact triaQuot_factorRep_sub_one_braid U U' (hI.braid d hd e he hde)

theorem factorRep_eq_one_of_triality {Γ X A : Type} [Group Γ] [Group X] [AddCommGroup A]
    [Module (ZMod 2) A] [Finite A] {π : Γ →* X} {𝔇 : Set Γ} {s : X}
    (hL : TrialityHyp π 𝔇 s) {ρ : Representation (ZMod 2) Γ A} (hI : TrialityIdent π 𝔇 ρ)
    {U U' : Subrepresentation ρ} (h : U ⋖ U') : ∀ g : Γ, factorRep U U' g = 1 := by
  have hle : π.ker ≤ CFSG.pCore 2 Γ :=
    le_sSup (s := {K : Subgroup Γ | K.Normal ∧ IsPGroup 2 K})
      ⟨MonoidHom.normal_ker π, hL.ker⟩
  have hker : π.ker ≤ (factorRep U U').ker := by
    intro j hj
    show factorRep U U' j = 1
    refine LinearMap.ext fun x => ?_
    simpa using factor_trivial_pCore h (hle hj) x
  let ρX : X →* Module.End (ZMod 2) (U'.toSubmodule ⧸ factorSub U U') :=
    (QuotientGroup.lift π.ker (factorRep U U') hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective π hL.surj).symm.toMonoidHom
  have hρX : ∀ g : Γ, ρX (π g) = factorRep U U' g := by
    intro g
    have he : (QuotientGroup.quotientKerEquivOfSurjective π hL.surj)
        (QuotientGroup.mk g) = π g := by
      show QuotientGroup.kerLift π (QuotientGroup.mk g) = π g
      exact QuotientGroup.kerLift_mk (φ := π) g
    change (QuotientGroup.lift π.ker (factorRep U U') hker)
        ((QuotientGroup.quotientKerEquivOfSurjective π hL.surj).symm (π g)) =
      factorRep U U' g
    rw [show (QuotientGroup.quotientKerEquivOfSurjective π hL.surj).symm (π g) =
        (QuotientGroup.mk g : Γ ⧸ π.ker) from
      by rw [← he, MulEquiv.symm_apply_apply]]
    exact QuotientGroup.lift_mk' π.ker hker g
  have hIq : TrialityIdent π 𝔇 (factorRep U U') := triality_ident_factorRep U U' hI
  have hcomm : ∀ a b : X, IsConj s a → IsConj s b → a * b = b * a →
      (ρX a - 1) * (ρX b - 1) = 0 := by
    intro a b ha hb hab
    have ha' : a ∈ π '' 𝔇 := by rw [hL.image]; exact ha
    obtain ⟨d, hd, hda⟩ := (Set.mem_image π 𝔇 a).mp ha'
    have hb' : b ∈ π '' 𝔇 := by rw [hL.image]; exact hb
    obtain ⟨e, he, heb⟩ := (Set.mem_image π 𝔇 b).mp hb'
    have h1 : ρX a = factorRep U U' d := by rw [← hda, hρX d]
    have h2 : ρX b = factorRep U U' e := by rw [← heb, hρX e]
    rw [h1, h2]
    exact hIq.comm d hd e he (by rw [hda, heb]; exact hab)
  have hbraid : ∀ a b : X, IsConj s a → IsConj s b → orderOf (a * b) = 3 →
      (ρX a - 1) * (ρX b - 1) * (ρX a - 1) = ρX a - 1 := by
    intro a b ha hb hab
    have ha' : a ∈ π '' 𝔇 := by rw [hL.image]; exact ha
    obtain ⟨d, hd, hda⟩ := (Set.mem_image π 𝔇 a).mp ha'
    have hb' : b ∈ π '' 𝔇 := by rw [hL.image]; exact hb
    obtain ⟨e, he, heb⟩ := (Set.mem_image π 𝔇 b).mp hb'
    have h1 : ρX a = factorRep U U' d := by rw [← hda, hρX d]
    have h2 : ρX b = factorRep U U' e := by rw [← heb, hρX e]
    rw [h1, h2]
    exact hIq.braid d hd e he (by rw [hda, heb]; exact hab)
  have htriv : ∀ x : X, ρX x = 1 :=
    triality_rep_trivial ρX s hL.sq hL.gen hL.cent hL.line hcomm hbraid
  intro g
  rw [← hρX g]
  exact htriv (π g)

end CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri
