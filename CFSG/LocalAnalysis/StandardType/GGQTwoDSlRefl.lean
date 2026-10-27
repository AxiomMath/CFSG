module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlClass
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlPair

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sl

section Linear

variable {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type} {m : ℕ}

theorem ggLin_e0_eq (e' : Fin m ≃ ι) (e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥A)
    (β : Additive ↥Bs ≃+ DVec m)
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (((ggCoxeterMatrixD m).reindex e').simple (e' t)) : ↥A) :
        MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    {e₀ : (ggCoxeterMatrixD m).Group ≃* dEven m} (he₀ : IsDEquiv m e₀)
    (w : (ggCoxeterMatrixD m).Group) :
    ggLin (p := 3) β ((e0 e' e w : ↥A) : MulAut ↥Bs) =
      ((e₀ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) := by
  have hsimple : ∀ t : Fin m,
      ggLin (p := 3) β (((e (((ggCoxeterMatrixD m).reindex e').simple (e' t)) : ↥A) :
        MulAut ↥Bs)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t) := by
    intro t
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨s, rfl⟩ : ∃ s : ↥Bs, β (Additive.ofMul s) = v :=
      ⟨Additive.toMul (β.symm v), by simp⟩
    rw [ggLin_apply_ofMul]
    exact hβ t s
  let φ₁ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (ggLin (p := 3) β).comp (A.subtype.comp (e0 e' e).toMonoidHom)
  let φ₂ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (dEven m).subtype.comp e₀.toMonoidHom
  have heq : φ₁ = φ₂ := by
    refine (ggCoxeterMatrixD m).toCoxeterSystem.ext_simple fun t => ?_
    show ggLin (p := 3) β (((e0 e' e ((ggCoxeterMatrixD m).simple t) : ↥A)) : MulAut ↥Bs) =
      ((e₀ ((ggCoxeterMatrixD m).simple t) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m)
    rw [e0_simple, hsimple t, he₀ t]
  exact DFunLike.congr_fun heq w

end Linear

end Sl

variable {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
  {M : CoxeterMatrix ι} {m : ℕ}

theorem ggCoxRefl_of_isReflection (e : M.Group ≃* ↥A) (e' : Fin m ≃ ι) (hm : 4 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (β : Additive ↥Bs ≃+ DVec m)
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥A) : MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    {a : MulAut ↥Bs} (haA : a ∈ A) (ha : GGIsReflection 3 a) : a ∈ ggCoxRefl M e := by
  subst hM
  obtain ⟨e₀, he₀⟩ := dEven_equiv hm
  set w : (ggCoxeterMatrixD m).Group := (Sl.e0 e' e).symm ⟨a, haA⟩ with hw
  have hwa : ((Sl.e0 e' e w : ↥A) : MulAut ↥Bs) = a := by
    rw [hw, MulEquiv.apply_symm_apply]
  have hlin := Sl.ggLin_e0_eq e' e β hβ he₀ w
  rw [hwa] at hlin
  obtain ⟨x, f, hfx, hform⟩ := exists_of_ggIsReflection β ha
  have hu : ggLin (p := 3) β a ∈ dEven m := by
    rw [hlin]
    exact (e₀ w).2
  obtain ⟨ε, p, q, hpq, hpq'⟩ := Sl.eq_dTau_of_reflection hu hfx hform
  obtain ⟨u, t, hut⟩ := Sl.exists_conj_simple_of_dTau hm he₀ ε hpq
  have hw' : w = u * (ggCoxeterMatrixD m).simple t * u⁻¹ := by
    apply e₀.injective
    apply Subtype.ext
    rw [← hlin, hpq', hut]
  have hΨ : ((ggCoxeterMatrixD m).reindexGroupEquiv e').symm
      (u * (ggCoxeterMatrixD m).simple t * u⁻¹) =
      ((ggCoxeterMatrixD m).reindexGroupEquiv e').symm u *
        ((ggCoxeterMatrixD m).reindex e').simple (e' t) *
          (((ggCoxeterMatrixD m).reindexGroupEquiv e').symm u)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  refine ⟨((ggCoxeterMatrixD m).reindexGroupEquiv e').symm u, e' t, ?_⟩
  rw [← hwa, hw']
  show ((e (((ggCoxeterMatrixD m).reindexGroupEquiv e').symm
      (u * (ggCoxeterMatrixD m).simple t * u⁻¹)) : ↥A) : MulAut ↥Bs) = _
  rw [hΨ]

end CFSG.StandardType.QTwo

end
