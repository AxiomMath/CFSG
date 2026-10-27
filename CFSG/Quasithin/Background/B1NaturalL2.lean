module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

public section

namespace CFSG.Quasithin

open Matrix

variable {V : Type*} [CommGroup V]

@[expose] def ActsAsNaturalL2 (H : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ (e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (φ : ↥U ≃* Multiplicative (Fin 2 → ZMod 2)),
    ∀ (h : ↥H) (u : ↥U) (hu : (h : MulAut V) (u : V) ∈ U),
      φ ⟨(h : MulAut V) u, hu⟩ =
        Multiplicative.ofAdd ((e h : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (φ u))

namespace B1

@[expose] def slAut (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    MulAut (Multiplicative (Fin 2 → ZMod 2)) where
  toFun x := Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd x)
  left_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, ofAdd_toAdd]
  right_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' a b := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem slAut_apply (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (x : Multiplicative (Fin 2 → ZMod 2)) :
    slAut g x =
      Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd x) :=
  rfl

@[expose] def slHom : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →*
    MulAut (Multiplicative (Fin 2 → ZMod 2)) where
  toFun := slAut
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    show Multiplicative.ofAdd (((1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
      Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd x) = x
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    show Multiplicative.ofAdd (((g * h : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
      Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd x) =
      Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
        ((h : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd x))
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem mulVec_ext {M N : Matrix (Fin 2) (Fin 2) (ZMod 2)}
    (h : ∀ x : Fin 2 → ZMod 2, M *ᵥ x = N *ᵥ x) : M = N := by
  apply Matrix.ext
  intro i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem slHom_injective : Function.Injective slHom := by
  intro g h hgh
  have key : ∀ x : Fin 2 → ZMod 2, (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ x =
      (h : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ x := by
    intro x
    have := congrArg (fun f : MulAut (Multiplicative (Fin 2 → ZMod 2)) =>
      Multiplicative.toAdd (f (Multiplicative.ofAdd x))) hgh
    simpa [slHom, slAut_apply] using this
  exact Subtype.ext (mulVec_ext key)

@[expose] def linOf (f : MulAut (Multiplicative (Fin 2 → ZMod 2))) :
    (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun x := Multiplicative.toAdd (f (Multiplicative.ofAdd x))
  map_add' a b := by simp only [ofAdd_add, map_mul, toAdd_mul]
  map_smul' c x := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp
    · simp

@[expose] noncomputable def matOf (f : MulAut (Multiplicative (Fin 2 → ZMod 2))) :
    Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  LinearMap.toMatrix' (linOf f)

theorem matOf_mulVec (f : MulAut (Multiplicative (Fin 2 → ZMod 2))) (x : Fin 2 → ZMod 2) :
    matOf f *ᵥ x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := by
  unfold matOf
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem matOf_mul (f g : MulAut (Multiplicative (Fin 2 → ZMod 2))) :
    matOf (f * g) = matOf f * matOf g := by
  refine mulVec_ext fun x => ?_
  rw [← Matrix.mulVec_mulVec, matOf_mulVec, matOf_mulVec, matOf_mulVec]
  simp

theorem matOf_one : matOf (1 : MulAut (Multiplicative (Fin 2 → ZMod 2))) = 1 := by
  refine mulVec_ext fun x => ?_
  rw [matOf_mulVec, Matrix.one_mulVec]
  simp

theorem det_matOf (f : MulAut (Multiplicative (Fin 2 → ZMod 2))) : (matOf f).det = 1 := by
  have h1 : (matOf f).det * (matOf f⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← matOf_mul, mul_inv_cancel, matOf_one, Matrix.det_one]
  revert h1
  generalize (matOf f).det = a
  generalize (matOf f⁻¹).det = b
  revert a b
  decide

theorem slHom_surjective : Function.Surjective slHom := by
  intro f
  let g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨matOf f, det_matOf f⟩
  refine ⟨g, MulEquiv.ext fun x => ?_⟩
  show slAut g x = f x
  rw [slAut_apply]
  have hg : ((g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
      Matrix (Fin 2) (Fin 2) (ZMod 2)) = matOf f := rfl
  rw [hg, matOf_mulVec]
  simp

end B1

theorem actsAsNaturalL2_of_full [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : Nat.card U = 4) (hst : H ≤ stabSub U)
    (hfaith : H ⊓ centSub U = ⊥) (htop : autSub H U = ⊤) : ActsAsNaturalL2 H U := by
  have hKU : IsKleinFour U := by
    have hexp : Monoid.exponent U = 2 := by
      have hdvd : Monoid.exponent U ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun w =>
        Subtype.ext (by simpa using hV w)
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exfalso
        have hsub : Subsingleton U := ⟨fun a b => by
          have ha := Monoid.pow_exponent_eq_one a
          have hb := Monoid.pow_exponent_eq_one b
          rw [h, pow_one] at ha hb
          rw [ha, hb]⟩
        have := Finite.card_le_one_iff_subsingleton.2 hsub
        omega
      · exact h
    exact ⟨hU, hexp⟩
  have hKW : IsKleinFour (Multiplicative (Fin 2 → ZMod 2)) := by
    have : IsAddKleinFour (Fin 2 → ZMod 2) :=
      { card_four := by simp
        exponent_two := by
          rw [AddMonoid.exponent_eq_prime_iff Nat.prime_two]
          intro g hg
          refine addOrderOf_eq_prime ?_ hg
          ext i
          have h2 : (2 : ZMod 2) = 0 := by decide
          simp [h2] }
    infer_instance
  obtain ⟨φ⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥U)
    (G₂ := Multiplicative (Fin 2 → ZMod 2))
  let ρ : ↥H →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hst)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine (Subgroup.eq_bot_iff_forall _).2 fun h hh => ?_
    have hh' : ρ h = 1 := hh
    have hcent : (h : MulAut V) ∈ centSub U := by
      intro u hu
      have := congrArg (fun ψ : MulAut ↥U => ((ψ ⟨u, hu⟩ : U) : V)) hh'
      simpa [ρ, resHom_apply] using this
    have hmem : (h : MulAut V) ∈ H ⊓ centSub U := ⟨h.2, hcent⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hρsurj : Function.Surjective ρ := by
    intro ψ
    have hψ : ψ ∈ autSub H U := by rw [htop]; trivial
    obtain ⟨g, hgH, hgψ⟩ := mem_autSub.1 hψ
    exact ⟨⟨g, hgH⟩, hgψ⟩
  let e0 : ↥H ≃* MulAut ↥U := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  let eSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃*
      MulAut (Multiplicative (Fin 2 → ZMod 2)) :=
    MulEquiv.ofBijective B1.slHom ⟨B1.slHom_injective, B1.slHom_surjective⟩
  let e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    e0.trans ((MulAut.congr φ).trans eSL.symm)
  refine ⟨e, φ, fun h u hu => ?_⟩
  have h1 : B1.slHom (e h) = MulAut.congr φ (ρ h) := by
    have : eSL (e h) = MulAut.congr φ (e0 h) := by
      show eSL (eSL.symm (MulAut.congr φ (e0 h))) = _
      exact eSL.apply_symm_apply _
    exact this
  have h3 : (MulAut.congr φ) (ρ h) (φ u) = φ ⟨(h : MulAut V) u, hu⟩ := by
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  calc φ ⟨(h : MulAut V) u, hu⟩ = (MulAut.congr φ) (ρ h) (φ u) := h3.symm
    _ = B1.slHom (e h) (φ u) := by rw [h1]
    _ = _ := B1.slAut_apply _ _

end CFSG.Quasithin
