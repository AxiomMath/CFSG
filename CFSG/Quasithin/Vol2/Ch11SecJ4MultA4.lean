module

public import CFSG.Quasithin.Vol2.Ch11SecJ4MultA3
public import CFSG.Sporadic.Recognition.J4MultiplierIota
public import CFSG.Sporadic.Bridge.J4Surj

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult

open CFSG.RankThree.PartTwo.Sec4

theorem isPGroup_two_ker_rightHom {N P H Q : Type*} [Group N] [Group P] [Group H] [Group Q]
    {ϕ : P →* MulAut N} (hN : ∀ n : N, n ^ 2 = 1) (e : H ≃* N ⋊[ϕ] P) (f : P →* Q)
    (hf : Function.Injective f) :
    IsPGroup 2 (f.comp (SemidirectProduct.rightHom.comp e.toMonoidHom)).ker := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have hx : f (SemidirectProduct.rightHom (e x)) = 1 := x.2
  have hr : (e x).right = 1 := hf (hx.trans (map_one f).symm)
  have hl : e x = SemidirectProduct.inl (e x).left := by
    ext
    · rfl
    · simp [hr]
  have h2 : e ((x : H) ^ 2) = 1 := by
    rw [map_pow, hl, ← map_pow, hN, map_one]
  show (x : H) ^ 2 ^ 1 = 1
  rw [pow_one]
  exact e.injective (h2.trans (map_one e).symm)

theorem exists_local_of_semidirect {A J S M N P : Type*} [Group A] [Group J] [Group S] [Group M]
    [Group N] [Group P] {ϕ : P →* MulAut N} (θ : N ⋊[ϕ] P →* J) (hθ : Function.Injective θ)
    (e₁ : A ≃* J) (e₂ : A ≃* S) (eM : M ≃* P) (hN : ∀ n : N, n ^ 2 = 1)
    (hi : ¬ 3 ∣ θ.range.index) :
    ∃ (H : Subgroup S) (φ : H →* M), Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧
      ¬ 3 ∣ H.index := by
  let eJ : J ≃* S := e₁.symm.trans e₂
  let H : Subgroup S := θ.range.map (eJ : J →* S)
  let iH : θ.range ≃* H := θ.range.equivMapOfInjective (eJ : J →* S) eJ.injective
  let iS : N ⋊[ϕ] P ≃* θ.range := MonoidHom.ofInjective hθ
  let e : H ≃* N ⋊[ϕ] P := iH.symm.trans iS.symm
  let f : P →* M := eM.symm.toMonoidHom
  refine ⟨H, f.comp (SemidirectProduct.rightHom.comp e.toMonoidHom), ?_,
    isPGroup_two_ker_rightHom hN e f eM.symm.injective, ?_⟩
  · exact eM.symm.surjective.comp (SemidirectProduct.rightHom_surjective.comp e.surjective)
  · rw [Subgroup.index_map_equiv]
    exact hi

theorem sq_eq_one_f2 (n : Multiplicative (Fin 11 → ZMod 2)) : n ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
  generalize Multiplicative.toAdd n i = x
  revert x
  decide

section Certified


theorem factJ4Multiplier_of (hH : J4LocalM24) (hM24 : NoPerfectTripleCoverM24) :
    FactJ4Multiplier := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have e' : CFSG.Blueprint.NativeSporadic.J4 ≃* Spor .J4 := e
  exact factJ4Multiplier_of_mulEquiv e' hH hM24


theorem j4LocalM24 : J4LocalM24 := by
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have e₂' : CFSG.Blueprint.NativeSporadic.J4 ≃* Spor .J4 := e₂
  obtain ⟨eM⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have eM' : CFSG.Blueprint.NativeSporadic.M24 ≃* CFSG.Sporadic.Recognition.J4Multiplier.PM24 :=
    eM
  have hi : ¬ 3 ∣ CFSG.Sporadic.Recognition.J4Multiplier.theta.range.index := by
    rw [CFSG.Sporadic.Recognition.J4Multiplier.theta_index]
    norm_num
  exact exists_local_of_semidirect (A := CFSG.Blueprint.NativeSporadic.J4)
    (J := CFSG.Sporadic.J4.J) (S := Spor .J4) (M := CFSG.Blueprint.NativeSporadic.M24)
    CFSG.Sporadic.Recognition.J4Multiplier.theta
    CFSG.Sporadic.Recognition.J4Multiplier.theta_injective
    (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat) e₂' eM' sq_eq_one_f2 hi

theorem factJ4Multiplier_of_noTripleCover (hM24 : NoPerfectTripleCoverM24) :
    FactJ4Multiplier :=
  factJ4Multiplier_of j4LocalM24 hM24

end Certified

end CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult
