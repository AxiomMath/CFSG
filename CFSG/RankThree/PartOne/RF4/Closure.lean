module

public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


theorem shortFaithful_F4_of_isAlgebraic {L : Type} [Field L] [CharP L 2] [Algebra (ZMod 2) L]
    [Algebra.IsAlgebraic (ZMod 2) L] : ReeTag.F4.ShortFaithful L := by
  intro g hg hfix
  obtain ⟨S, hS⟩ := exists_finset_descent hg
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := ZMod 2) S
  obtain ⟨y, hy, rfl⟩ := hS E hSE
  have hp : ((ReeTag.F4.prime : ℕ) : E) = 0 := by
    apply E.subtype.injective
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero L 2
  have hfixE : ∀ v ∈ ReeTag.F4.shortModule E,
      (y : Module.End E (RootModule ReeTag.F4.tag E)) v = v := by
    intro v hv
    have hle : ReeTag.F4.shortModule E ≤
        LinearMap.eqLocus (y : Module.End E (RootModule ReeTag.F4.tag E)) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨i, hi, rfl⟩ | ⟨α, hα, rfl⟩)
      · have hmem : hVec ReeTag.F4.tag L i ∈ ReeTag.F4.shortModule L :=
          Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩)
        exact (baseChangeGL_fixes_single_iff E.subtype y _).1 (hfix _ hmem)
      · by_cases hr : IsRoot ReeTag.F4.tag α
        · have hmem : rootVec ReeTag.F4.tag L α ∈ ReeTag.F4.shortModule L :=
            Submodule.subset_span (Or.inr ⟨α, hα, rfl⟩)
          have h1 := hfix _ hmem
          simp only [rootVec, hr, dite_true] at h1
          change (y : Module.End E (RootModule ReeTag.F4.tag E)) (rootVec ReeTag.F4.tag E α) =
            rootVec ReeTag.F4.tag E α
          simp only [rootVec, hr, dite_true]
          exact (baseChangeGL_fixes_single_iff E.subtype y _).1 h1
        · change (y : Module.End E (RootModule ReeTag.F4.tag E)) (rootVec ReeTag.F4.tag E α) =
            rootVec ReeTag.F4.tag E α
          simp only [rootVec, hr, dite_false, map_zero]
    exact hle hv
  rw [ReeTag.shortFaithful hp y hy hfixE, map_one]

theorem exists_reeClosureAut {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L] :
    ∃ Φ : MulAut (adjointGroup Tag.F4 L), IsReeExceptional ReeTag.F4 L Φ := by
  classical
  have hCh : CharP L ReeTag.F4.prime := ‹CharP L 2›
  have : PerfectRing L 2 := inferInstance
  have hp : ((ReeTag.F4.prime : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
  have hf := shortFaithful_F4_of_isAlgebraic (L := L)
  set e := ReeTag.F4.exceptionalEndo L hp hf with he
  have hsq : e.comp e = frobeniusTwist Tag.F4 L (frobenius L 2) :=
    ReeTag.exceptionalEndo_comp_self hp hf
  have hFrsurj : Function.Surjective (frobeniusTwist Tag.F4 L (frobenius L 2)) := by
    intro g
    have hmap := map_exactEntrywiseAut (τ := Tag.F4) (frobeniusEquiv L 2)
      (H := adjointGroup Tag.F4 L) (Or.inl rfl)
    have hg : (g : ModGL Tag.F4 L) ∈ (adjointGroup Tag.F4 L).map
        (exactEntrywiseAut Tag.F4 (frobeniusEquiv L 2)).toMonoidHom := by
      rw [hmap]
      exact g.2
    obtain ⟨h, hh, hhg⟩ := hg
    exact ⟨⟨h, hh⟩, Subtype.ext hhg⟩
  have hinj : Function.Injective e := ReeTag.exceptionalEndo_injective hp hf
  have hsurj : Function.Surjective e := by
    intro g
    obtain ⟨h, rfl⟩ := hFrsurj g
    exact ⟨e h, DFunLike.congr_fun hsq h⟩
  refine ⟨MulEquiv.ofBijective e ⟨hinj, hsurj⟩, fun i c => ⟨?_, ?_⟩⟩
  · exact ReeTag.exceptionalEndo_xElement hp hf i c
  · exact ReeTag.exceptionalEndo_yElement hp hf i c

section BaseChange

variable {t : ReeTag} {K L : Type} [Field K] [Field L]

theorem adjointBaseChangeHom_xElement (ι : K →+* L) (i : Fin t.tag.rank) (c : K) :
    adjointBaseChangeHom t.tag ι (xElement i c) = xElement i (ι c) :=
  Subtype.ext (baseChangeGL_xUnit _ i c)

theorem adjointBaseChangeHom_yElement (ι : K →+* L) (i : Fin t.tag.rank) (c : K) :
    adjointBaseChangeHom t.tag ι (yElement i c) = yElement i (ι c) :=
  Subtype.ext (baseChangeGL_yUnit _ i c)

theorem IsReeExceptional.map_baseChange [Finite K] [CharP K t.prime] (ι : K →+* L)
    {Φ : MulAut (adjointGroup t.tag L)} (hΦ : IsReeExceptional t L Φ)
    (u : adjointGroup t.tag K) :
    Φ (adjointBaseChangeHom t.tag ι u) =
      adjointBaseChangeHom t.tag ι (t.finiteExceptionalAut K u) := by
  have h := adjointGroup_hom_ext
    (f := Φ.toMonoidHom.comp (adjointBaseChangeHom t.tag ι))
    (g := (adjointBaseChangeHom t.tag ι).comp (t.finiteExceptionalAut K).toMonoidHom)
    (fun i c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [adjointBaseChangeHom_xElement, (hΦ i _).1, ReeTag.finiteExceptionalAut_xElement,
        adjointBaseChangeHom_xElement, map_pow])
    (fun i c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [adjointBaseChangeHom_yElement, (hΦ i _).2, ReeTag.finiteExceptionalAut_yElement,
        adjointBaseChangeHom_yElement, map_pow])
  exact DFunLike.congr_fun h u

theorem IsReeExceptional.map_baseChange_pow [Finite K] [CharP K t.prime] (ι : K →+* L)
    {Φ : MulAut (adjointGroup t.tag L)} (hΦ : IsReeExceptional t L Φ) (n : ℕ)
    (u : adjointGroup t.tag K) :
    (Φ ^ n) (adjointBaseChangeHom t.tag ι u) =
      adjointBaseChangeHom t.tag ι ((t.finiteExceptionalAut K ^ n) u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, hΦ.map_baseChange ι, pow_succ', MulAut.mul_apply]

end BaseChange

end CFSG.RankThree.PartOne.RF4
