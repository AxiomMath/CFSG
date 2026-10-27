module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobSelected

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Selected

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
  {m : ℕ} {e' : Fin m ≃ ι}

omit [Finite G] in
theorem qtwoD_image_eq (hm : 4 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (β : Additive ↥Bs ≃+ DVec m)
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s))) :
    (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) = dEven m := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  obtain ⟨e0, he0⟩ := dEven_equiv hm
  subst hM
  have hdt : ∀ t : Fin m, ggLin (p := 3) β
      ((e (((ggCoxeterMatrixD m).reindex e').simple (e' t)) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t) := by
    intro t
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨s, rfl⟩ : ∃ s : ↥Bs, v = β (Additive.ofMul s) :=
      ⟨Additive.toMul (β.symm v), by simp⟩
    rw [ggLin_apply_ofMul]
    exact hβ t s
  let Ψ : ((ggCoxeterMatrixD m).reindex e').Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (ggLin (p := 3) β).comp ((ggAutomizerJoin L Bs 𝒦).subtype.comp e.toMonoidHom)
  let Ψ' : ((ggCoxeterMatrixD m).reindex e').Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (dEven m).subtype.comp
      (e0.toMonoidHom.comp (((ggCoxeterMatrixD m).reindexGroupEquiv e').toMonoidHom))
  have hΨ : Ψ = Ψ' := by
    apply PresentedGroup.ext
    intro i
    obtain ⟨t, rfl⟩ := e'.surjective i
    have h1 : Ψ (((ggCoxeterMatrixD m).reindex e').simple (e' t)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t) :=
      hdt t
    have h2 : Ψ' (((ggCoxeterMatrixD m).reindex e').simple (e' t)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t) := by
      change ((e0 (((ggCoxeterMatrixD m).reindexGroupEquiv e')
        (((ggCoxeterMatrixD m).reindex e').simple (e' t))) : dEven m) :
          DVec m ≃ₗ[ZMod 3] DVec m) = _
      rw [CoxeterMatrix.reindexGroupEquiv_apply_simple, Equiv.symm_apply_apply]
      exact he0 t
    exact h1.trans h2.symm
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hmem : ggLin (p := 3) β a ∈ Ψ.range :=
      ⟨e.symm ⟨a, ha⟩, by simp [Ψ]⟩
    rw [hΨ] at hmem
    obtain ⟨w, hw⟩ := hmem
    rw [← hw]
    exact (e0 (((ggCoxeterMatrixD m).reindexGroupEquiv e') w)).2
  · intro hg
    have hmem : g ∈ Ψ'.range := by
      refine ⟨((ggCoxeterMatrixD m).reindexGroupEquiv e').symm (e0.symm ⟨g, hg⟩), ?_⟩
      simp [Ψ']
    rw [← hΨ] at hmem
    obtain ⟨w, hw⟩ := hmem
    exact ⟨((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs), (e w).2, hw⟩

end Selected

end CFSG.StandardType.QTwo

end
