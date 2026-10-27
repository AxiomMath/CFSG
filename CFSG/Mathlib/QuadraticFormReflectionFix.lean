module

public import CFSG.ClassicalGroups.Orthogonal.Derived
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_vectors_of_reflection_list {Q : QuadraticForm K V} :
    ∀ l : List (TauCeti.QuadraticMap.orthogonalGroup Q),
      (∀ r ∈ l, ∃ (v : V) (_ : Invertible (Q v)),
        TauCeti.QuadraticMap.reflectionOrthogonal Q v = r) →
      ∃ lv : List V, lv.length = l.length ∧ (∀ v ∈ lv, Q v ≠ 0) ∧
        ((l.prod : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) =
          (lv.map (CFSG.ClassicalGroups.Orthogonal.reflect Q)).prod
  | [], _ => ⟨[], rfl, by simp, by simp⟩
  | r :: l, h => by
    obtain ⟨v, hinv, hv⟩ := h r List.mem_cons_self
    obtain ⟨lv, hlen, hQ, hprod⟩ := exists_vectors_of_reflection_list l
      fun r' hr' => h r' (List.mem_cons_of_mem r hr')
    refine ⟨v :: lv, by simp [hlen], fun w hw => ?_, ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact (isUnit_of_invertible (Q w)).ne_zero
      · exact hQ w hw
    · have hr : ((r : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) =
          CFSG.ClassicalGroups.Orthogonal.reflect Q v := by
        rw [← hv, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
        letI : Invertible (Q v) := hinv
        exact (CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection).symm
      rw [List.prod_cons, Subgroup.coe_mul, hprod, hr, List.map_cons, List.prod_cons]

theorem exists_list_reflect_of_fix [FiniteDimensional K V] [NeZero (2 : K)]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (P : Submodule K V) (hP : (Q.restrict P).Nondegenerate)
    (g : V ≃ₗ[K] V) (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ p ∈ P, g p = p) :
    ∃ l : List V,
      (∀ w ∈ l, w ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P ∧ Q w ≠ 0) ∧
      g = (l.map (CFSG.ClassicalGroups.Orthogonal.reflect Q)).prod := by
  classical
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  let W : Submodule K V := LinearMap.BilinForm.orthogonal Q.polarBilin P
  have hW : IsCompl P W := hP.isCompl_orthogonal
  have hWnd : (Q.restrict W).Nondegenerate := hQ.nondegenerate_restrict_orthogonal hP
  let e : ((Q.restrict P).prod (Q.restrict W)).IsometryEquiv Q :=
    IsometryEquiv.prodRestrictOrthogonal Q P hW
  set gO : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨g, hg⟩ with hgO
  set g'O : TauCeti.QuadraticMap.orthogonalGroup ((Q.restrict P).prod (Q.restrict W)) :=
    (TauCeti.QuadraticMap.orthogonalGroupCongr e).symm gO with hg'O
  have hgW : ∀ w : W, g (w : V) ∈ W := by
    intro w
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    calc Q.polarBilin p (g (w : V))
        = Q.polarBilin (g p) (g (w : V)) := by rw [hfix p hp]
      _ = Q.polarBilin p (w : V) := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg p w
      _ = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) p hp
  have hg'app : ∀ m, (g'O : _ ≃ₗ[K] _) m = e.symm ((gO : V ≃ₗ[K] V) (e m)) :=
    fun m => TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply e gO m
  have hsymmP : ∀ p : P, e.symm (p : V) = (p, 0) := fun p => by
    have hp : e (p, 0) = (p : V) := by
      rw [IsometryEquiv.prodRestrictOrthogonal_apply]; simp
    rw [show (p : V) = e (p, 0) from hp.symm]
    exact LinearEquiv.symm_apply_apply (e : (P × W) ≃ₗ[K] V) (p, 0)
  have hmem_range : g'O ∈ (QuadraticMap.orthogonalGroupProd (Q.restrict P) (Q.restrict W)).range := by
    rw [QuadraticMap.mem_range_orthogonalGroupProd_iff]
    constructor
    · intro m₁
      rw [hg'app]
      have h0 : e (m₁, 0) = (m₁ : V) := by
        rw [IsometryEquiv.prodRestrictOrthogonal_apply]; simp
      rw [h0]
      have hmem : (gO : V ≃ₗ[K] V) (m₁ : V) ∈ P := by
        change g (m₁ : V) ∈ P
        rw [hfix m₁ m₁.2]; exact m₁.2
      rw [hsymmP ⟨(gO : V ≃ₗ[K] V) (m₁ : V), hmem⟩]
    · intro m₂
      rw [hg'app]
      have h0 : e (0, m₂) = (m₂ : V) := by
        rw [IsometryEquiv.prodRestrictOrthogonal_apply]; simp
      rw [h0]
      have hsum : ((e.symm ((gO : V ≃ₗ[K] V) (m₂ : V))).1 : V) +
          ((e.symm ((gO : V ≃ₗ[K] V) (m₂ : V))).2 : V) = (gO : V ≃ₗ[K] V) (m₂ : V) := by
        rw [← IsometryEquiv.prodRestrictOrthogonal_apply Q P hW
          (e.symm ((gO : V ≃ₗ[K] V) (m₂ : V)))]
        exact LinearEquiv.apply_symm_apply (e : (P × W) ≃ₗ[K] V) ((gO : V ≃ₗ[K] V) (m₂ : V))
      have hx1 : ((e.symm ((gO : V ≃ₗ[K] V) (m₂ : V))).1 : V) =
          (gO : V ≃ₗ[K] V) (m₂ : V) -
            ((e.symm ((gO : V ≃ₗ[K] V) (m₂ : V))).2 : V) := by
        rw [eq_sub_iff_add_eq]
        exact hsum
      have hmem : ((e.symm ((gO : V ≃ₗ[K] V) (m₂ : V))).1 : V) ∈ W := by
        rw [hx1]
        exact W.sub_mem (hgW m₂) (e.symm ((gO : V ≃ₗ[K] V) (m₂ : V))).2.2
      have hbot : ((e.symm ((gO : V ≃ₗ[K] V) (m₂ : V))).1 : V) ∈ (⊥ : Submodule K V) := by
        rw [← hW.inf_eq_bot]
        exact Submodule.mem_inf.mpr ⟨(e.symm ((gO : V ≃ₗ[K] V) (m₂ : V))).1.2, hmem⟩
      exact Subtype.ext (by simpa using hbot)
  obtain ⟨f, hf⟩ := hmem_range
  have hf1 : f.1 = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun p => ?_)
    have h0 : e (p, 0) = (p : V) := by
      rw [IsometryEquiv.prodRestrictOrthogonal_apply]; simp
    have hfixp : (gO : V ≃ₗ[K] V) (p : V) = (p : V) := by
      change g (p : V) = (p : V); exact hfix p p.2
    have hgapp := hg'app (p, 0)
    rw [h0, hfixp, hsymmP p] at hgapp
    have hfapp : (QuadraticMap.orthogonalGroupProd (Q.restrict P) (Q.restrict W) f :
        (P × W) ≃ₗ[K] (P × W)) ((p, 0) : P × W) = (p, 0) := by
      rw [hf]
      exact hgapp
    rw [QuadraticMap.coe_orthogonalGroupProd, LinearEquiv.prodCongr_apply] at hfapp
    simpa using (Prod.ext_iff.1 hfapp).1
  obtain ⟨l, hlrefl, _, hprod⟩ :=
    TauCeti.QuadraticMap.exists_reflectionOrthogonal_list_prod_eq (Q.restrict W) hWnd f.2
  obtain ⟨lv, _, hQv, hlvprod⟩ := exists_vectors_of_reflection_list l hlrefl
  have hf2 : (f.2 : W ≃ₗ[K] W) =
      (lv.map (CFSG.ClassicalGroups.Orthogonal.reflect (Q.restrict W))).prod := by
    rw [← hprod]
    exact hlvprod
  have hgeq : g = (TauCeti.QuadraticMap.orthogonalGroupCongr e
      (QuadraticMap.orthogonalGroupProd (Q.restrict P) (Q.restrict W) (1, f.2)) :
      V ≃ₗ[K] V) := by
    have h1 : TauCeti.QuadraticMap.orthogonalGroupCongr e
        (QuadraticMap.orthogonalGroupProd (Q.restrict P) (Q.restrict W) f) = gO := by
      rw [hf, MulEquiv.apply_symm_apply]
    rw [show f = (1, f.2) from Prod.ext hf1 rfl] at h1
    rw [h1]
  have hreflect_restrict : ∀ (w c : W),
      CFSG.ClassicalGroups.Orthogonal.reflect Q (w : V) (c : V) =
        (CFSG.ClassicalGroups.Orthogonal.reflect (Q.restrict W) w c : V) := by
    intro w c
    by_cases h : Q (w : V) = 0
    · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero (Q := Q) h,
        CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero (Q := Q.restrict W)
          (show (Q.restrict W) w = 0 from h)]
      rfl
    · have h' : (Q.restrict W) w ≠ 0 := by simpa using h
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply (Q := Q) h,
        CFSG.ClassicalGroups.Orthogonal.reflect_apply (Q := Q.restrict W) h']
      simp only [Submodule.coe_sub, Submodule.coe_smul]
      congr 1
  have hmain : ∀ lv : List W, ∀ (a : V) (_ : a ∈ P) (b : W),
      ((lv.map (fun w : W => CFSG.ClassicalGroups.Orthogonal.reflect Q (w : V))).prod)
          (a + (b : V)) =
        a + (((lv.map (CFSG.ClassicalGroups.Orthogonal.reflect (Q.restrict W))).prod) b : V) := by
    intro lv
    induction lv with
    | nil => intro a ha b; simp
    | cons w lv ih =>
      intro a ha b
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      simp only [LinearEquiv.mul_apply]
      rw [ih a ha b]
      have horth : polar Q (w : V) a = 0 := by
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) a ha
        rw [QuadraticMap.polarBilin_apply_apply] at h
        rw [polar_comm]
        exact h
      rw [map_add, CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (Q := Q) horth,
        hreflect_restrict]
  refine ⟨lv.map (fun w : W => (w : V)), ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact ⟨w.2, by simpa using hQv w hw⟩
  · apply LinearEquiv.ext
    intro y
    have hsum : ((e.symm y).1 : V) + ((e.symm y).2 : V) = y := by
      rw [← IsometryEquiv.prodRestrictOrthogonal_apply Q P hW (e.symm y)]
      exact LinearEquiv.apply_symm_apply (e : (P × W) ≃ₗ[K] V) y
    have hgy : g y = ((e.symm y).1 : V) +
        (((lv.map (CFSG.ClassicalGroups.Orthogonal.reflect (Q.restrict W))).prod)
          (e.symm y).2 : V) := by
      rw [hgeq, TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply,
        QuadraticMap.coe_orthogonalGroupProd]
      change e ((1 : P ≃ₗ[K] P).prodCongr (f.2 : W ≃ₗ[K] W) (e.symm y)) = _
      rw [LinearEquiv.prodCongr_apply]
      change e ((e.symm y).1, (f.2 : W ≃ₗ[K] W) (e.symm y).2) = _
      rw [IsometryEquiv.prodRestrictOrthogonal_apply, hf2]
    rw [hgy, List.map_map]
    conv_rhs => rw [← hsum]
    exact (hmain lv ((e.symm y).1 : V) (e.symm y).1.2 (e.symm y).2).symm

end CFSG
