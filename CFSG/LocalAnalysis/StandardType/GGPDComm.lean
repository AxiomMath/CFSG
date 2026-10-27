module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs
public import CFSG.LocalAnalysis.StandardType.GGPDReflInv
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.GroupTheory.SteinbergCECentralOddKernelLift

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped IsMulCommutative

theorem ggPD_comap_commute {K : Type} [Field K] {d : ℕ}
    {A : Subgroup (Matrix.GeneralLinearGroup (Fin d) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))}
    (hA : IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ 4)
    [Fact (Nat.Prime 3)] {Γ : Type} [Fintype Γ] [DecidableEq Γ] {C : Matrix Γ Γ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥A ≃+ V}
    {φ : Γ → MulAut ↥A} {h : Γ → V} {α : Γ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι C φ h α) (hΓ : Fintype.card Γ = 4) :
    ∀ u ∈ A.comap (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))),
      ∀ v ∈ A.comap (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))),
        u * v = v * u := by
  classical
  let S := Matrix.GeneralLinearGroup (Fin d) K ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)
  haveI hAe : CFSG.IsElementaryAbelian 3 A :=
    CFSG.Open.IsElemAbelian.isElementaryAbelian hA
  have hCE : Subgroup.normalizer (A : Set S) ≤ Subgroup.normalizer (A : Set S) := le_rfl
  refine CFSG.RankThree.GroupTheory.commute_of_mem_comap_of_forms
    (π := QuotientGroup.mk'
      (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))) (p := 3) (E := A)
    (C := Subgroup.normalizer (A : Set S))
    (QuotientGroup.mk'_surjective _) ?_ hCE ?_
  · rw [QuotientGroup.ker_mk']
  · intro B hBalt hBinv
    let l : V →ₗ[ZMod 3] Additive A := ι.symm.toAddMonoidHom.toZModLinearMap 3
    set B' : LinearMap.BilinForm (ZMod 3) V := B.comp l l with hB'def
    have hB'alt : B'.IsAlt := by
      intro x
      rw [hB'def, LinearMap.BilinForm.comp_apply]
      exact hBalt (l x)
    have hcardV : Nat.card V = 3 ^ 4 := by
      rw [← Nat.card_congr ι.toEquiv]
      exact hcard
    haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcardV]; norm_num)
    letI : Fintype V := Fintype.ofFinite V
    have hfinrank : Module.finrank (ZMod 3) V = 4 := by
      have hcard3 := Module.card_eq_pow_finrank (K := ZMod 3) (V := V)
      rw [ZMod.card, ← Nat.card_eq_fintype_card] at hcard3
      rw [hcardV] at hcard3
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hcard3).symm
    haveI : Nonempty Γ := Fintype.card_pos_iff.mp (by rw [hΓ]; norm_num)
    have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ :=
      LinearIndependent.span_eq_top_of_card_eq_finrank hD.indep
        (by rw [hΓ, hfinrank])
    have hinv : ∀ i u v,
        B' (u - α i u • h i) (v - α i v • h i) = B' u v := by
      intro i u v
      obtain ⟨g, -, hgnorm, hgact⟩ := hD.mem i
      let c : ↥(Subgroup.normalizer (A : Set S)) := ⟨g, hgnorm⟩
      have hc : ∀ x : A,
          A.normalizerMonoidHom
              (⟨c, hCE c.2⟩ : ↥(Subgroup.normalizer (A : Set S))) x = φ i x := by
        intro x
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact (hgact x).symm
      have hphi : ∀ x y : A,
          B (Additive.ofMul (φ i x)) (Additive.ofMul (φ i y)) =
            B (Additive.ofMul x) (Additive.ofMul y) := by
        intro x y
        have h := hBinv c x y
        rw [hc x, hc y] at h
        exact h
      have hl : ∀ w : V, l (w - α i w • h i) =
          Additive.ofMul (φ i (Additive.toMul (l w))) := by
        intro w
        rw [← hD.lin i w, ggLin_apply]
        simp only [l, AddMonoidHom.coe_toZModLinearMap, AddEquiv.coe_toAddMonoidHom,
          AddEquiv.symm_apply_apply]
      rw [hB'def, LinearMap.BilinForm.comp_apply, LinearMap.BilinForm.comp_apply,
        hl u, hl v]
      exact hphi (Additive.toMul (l u)) (Additive.toMul (l v))
    have h2 : (2 : ZMod 3) ≠ 0 := by
      intro hz
      have hdvd : (3 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff (ZMod 3) 3 2).mp hz
      norm_num at hdvd
    have hdiag : ∀ i, α i (h i) = 2 := by
      intro i
      rw [hD.pair i i, hD.diag i]
      norm_num
    have hB'zero : B' = 0 :=
      ggPD_invariantAlternating_eq_zero h2 h α hdiag hspan B' hB'alt hinv
    have hl_surj : Function.Surjective l := by
      intro x
      refine ⟨ι (Additive.ofMul (Additive.toMul x)), ?_⟩
      simp only [l, AddMonoidHom.coe_toZModLinearMap, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.symm_apply_apply]
      rfl
    have hBzero : B = 0 := by
      ext x y
      obtain ⟨u, rfl⟩ := hl_surj x
      obtain ⟨v, rfl⟩ := hl_surj y
      have h := congrArg (fun B : LinearMap.BilinForm (ZMod 3) V => B u v) hB'zero
      simpa [hB'def, LinearMap.BilinForm.comp_apply] using h
    exact hBzero

end CFSG.StandardType

end
