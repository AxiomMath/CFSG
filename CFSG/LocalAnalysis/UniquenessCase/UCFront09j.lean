module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup

theorem mulAut_comm_of_fpf {W : Type*} [CommGroup W] {α δ : MulAut W} (hδ : δ ^ 3 = 1)
    (hα : α ^ 2 = 1) (hc : Commute α (δ * α * δ⁻¹)) (hfix : ∀ w, δ w = w → w = 1)
    (h2 : ∀ w : W, w * w = 1 → w = 1) : α * δ = δ * α := by
  have hδ3 : ∀ w, δ (δ (δ w)) = w := fun w => by
    simpa [pow_succ, MulAut.mul_apply] using congrArg (fun f : MulAut W => f w) hδ
  have hα2 : ∀ w, α (α w) = w := fun w => by
    simpa [pow_succ, MulAut.mul_apply] using congrArg (fun f : MulAut W => f w) hα
  have hnorm : ∀ w, w * δ w * δ (δ w) = 1 := fun w =>
    hfix _ (by rw [map_mul, map_mul, hδ3]; exact (mul_rotate _ _ _).symm)
  have hinv : ∀ w, δ⁻¹ w = (w * δ w)⁻¹ := fun w => by
    have h := hnorm (δ⁻¹ w)
    simp only [MulAut.apply_inv_self] at h
    exact eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h)
  have hX : ∀ w, α (δ (α w)) * α (δ (α (δ w))) = δ w * δ (α (δ (α w))) := fun w => by
    have h := congrArg (fun f : MulAut W => f w) hc.eq
    simp only [MulAut.mul_apply, hinv, map_inv, map_mul, hα2] at h
    exact inv_injective h
  let Y : W →* W := (α.toMonoidHom.comp (δ.toMonoidHom.comp α.toMonoidHom)) / δ.toMonoidHom
  have hY : ∀ w, Y w = α (δ (α w)) / δ w := fun _ => rfl
  have hY0 : ∀ w, δ (Y w) = Y w * Y (δ w) := fun w => by
    rw [hY, hY, map_div, div_mul_div_comm, hX, mul_div_mul_left_eq_div]
  have hY1 : ∀ w, δ (Y w) = (Y (δ (δ w)))⁻¹ := fun w => by
    rw [hY0]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul Y, ← map_mul Y, hnorm, map_one])
  have hYY : ∀ w, Y w = (Y w)⁻¹ := fun w => by
    have h3 : δ (δ (δ (Y w))) = (Y w)⁻¹ := by
      rw [hY1, map_inv, hY1, inv_inv, hδ3, hY1, hδ3]
    rw [hδ3] at h3
    exact h3
  have hXδ : ∀ w, α (δ (α w)) = δ w := fun w => by
    have h := h2 (Y w) (mul_eq_one_iff_eq_inv.2 (hYY w))
    rwa [hY, div_eq_one] at h
  ext w
  simpa [MulAut.mul_apply, hα2] using hXδ (α w)

theorem map_mul_swap_of_fpf {K W : Type*} [Group K] [CommGroup W] (ρ : K →* MulAut W) {e d : K}
    (hd : d ^ 3 = 1) (he : e ^ 2 = 1) (hc : Commute e (d * e * d⁻¹))
    (hfix : ∀ w, ρ d w = w → w = 1) (h2 : ∀ w : W, w * w = 1 → w = 1) :
    ρ (e * d) = ρ (d * e) := by
  rw [map_mul, map_mul]
  refine mulAut_comm_of_fpf (by rw [← map_pow, hd, map_one]) (by rw [← map_pow, he, map_one])
    ?_ hfix h2
  have h : ρ e * ρ (d * e * d⁻¹) = ρ (d * e * d⁻¹) * ρ e := by rw [← map_mul, ← map_mul, hc.eq]
  rw [map_mul, map_mul, map_inv] at h
  exact h

variable {G : Type*} [Group G]

@[expose] def centGen9 (P X E D : Subgroup G) : Subgroup G :=
  closure {y | y ∈ P ∧ (y ∈ centralizer (E : Set G) ∨
    ∃ x ∈ X, y ∈ centralizer ((D.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G))}

theorem centGen9_le (P X E D : Subgroup G) : centGen9 P X E D ≤ P :=
  (closure_le _).2 fun _ hy => hy.1

theorem inf_centralizer_le_centGen9 (P X E D : Subgroup G) :
    P ⊓ centralizer (E : Set G) ≤ centGen9 P X E D :=
  fun _ hy => subset_closure ⟨hy.1, Or.inl hy.2⟩

theorem inf_centralizer_map_le_centGen9 (P E D : Subgroup G) {X : Subgroup G} {x : G}
    (hx : x ∈ X) :
    P ⊓ centralizer ((D.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ≤
      centGen9 P X E D :=
  fun _ hy => subset_closure ⟨hy.1, Or.inr ⟨x, hx, hy.2⟩⟩

theorem centGen9_mono {P Q : Subgroup G} (X E D : Subgroup G) (h : Q ≤ P) :
    centGen9 Q X E D ≤ centGen9 P X E D :=
  closure_mono fun _ hy => ⟨h hy.1, hy.2⟩

theorem centGen9_le_of {P X E D M : Subgroup G} (hE : P ⊓ centralizer (E : Set G) ≤ M)
    (hD : ∀ x ∈ X,
      P ⊓ centralizer ((D.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ≤ M) :
    centGen9 P X E D ≤ M := by
  refine (closure_le _).2 fun y ⟨hyP, hy⟩ => ?_
  rcases hy with hy | ⟨x, hx, hy⟩
  · exact hE ⟨hyP, hy⟩
  · exact hD x hx ⟨hyP, hy⟩

theorem le_normalizer_centGen9 [Finite G] {P X E D : Subgroup G}
    (hXP : X ≤ normalizer (P : Set G)) (hXE : X ≤ normalizer (E : Set G)) :
    X ≤ normalizer (centGen9 P X E D : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj g).injective).ge
  rw [centGen9, MonoidHom.map_closure]
  refine closure_mono ?_
  rintro _ ⟨y, ⟨hyP, hy⟩, rfl⟩
  show g * y * g⁻¹ ∈ _
  refine ⟨(hXP hg y).1 hyP, ?_⟩
  rcases hy with hy | ⟨x, hx, hy⟩
  · have hE : E.map (MulAut.conj g).toMonoidHom = E := mem_normalizer_iff_map_conj_eq.1 (hXE hg)
    have h : g * y * g⁻¹ ∈
        centralizer ((E.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
      map_centralizer_le_centralizer_image _ _ (mem_map_of_mem _ hy)
    rw [hE] at h
    exact Or.inl h
  · have hD : (D.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        D.map (MulAut.conj (g * x)).toMonoidHom := by
      rw [map_map]
      congr 1
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h : g * y * g⁻¹ ∈ centralizer
        (((D.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom : Subgroup G) :
          Set G) :=
      map_centralizer_le_centralizer_image _ _ (mem_map_of_mem _ hy)
    rw [hD] at h
    exact Or.inr ⟨g * x, X.mul_mem hg hx, h⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
