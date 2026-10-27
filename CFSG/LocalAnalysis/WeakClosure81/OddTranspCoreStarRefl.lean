module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs
import CFSG.Fischer.Classification.Orthogonal3.Refl

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Open Matrix CFSG.Fischer.Classification

section Vectors

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

private theorem nondegOn_perp_three (hf : IsF3Form f) {u v w : Fin m → ZMod 3}
    (hu : f u u = 1) (hv : f v v = 1) (hw : f w w = 1) (huv : f u v = 0) (huw : f u w = 0)
    (hvw : f v w = 0) :
    ∀ y ∈ F3.perpSub f ![u, v, w], y ≠ 0 → ∃ y' ∈ F3.perpSub f ![u, v, w], f y y' ≠ 0 := by
  have hvu : f v u = 0 := by rw [hf.symm]; exact huv
  have hwu : f w u = 0 := by rw [hf.symm]; exact huw
  have hwv : f w v = 0 := by rw [hf.symm]; exact hvw
  refine F3.nondegOn_of_proj hf (fun y => y - f y u • u - f y v • v - f y w • w)
    (fun y => F3.mem_perpSub_three.2 ⟨?_, ?_, ?_⟩) fun x hx y => ?_
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hu, hvu, hwu]
    ring
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, huv, hwv]
    ring
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hw, huw, hvw]
    ring
  · obtain ⟨h1, h2, h3⟩ := F3.mem_perpSub_three.1 hx
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, h1, h2, h3]
    ring

private theorem exists_star_vectors (hf : IsF3Form f) (hm : 5 ≤ m) :
    ∃ v e₁ e₂ e₃ : Fin m → ZMod 3, f v v = 1 ∧ f e₁ e₁ = 1 ∧ f e₂ e₂ = 1 ∧ f e₃ e₃ = 1 ∧
      f e₁ e₂ = 0 ∧ f e₁ e₃ = 0 ∧ f e₂ e₃ = 0 ∧ f v e₁ = 1 ∧ f v e₂ = 1 ∧ f v e₃ = 1 := by
  obtain ⟨e₁, h1⟩ := F3.exists_norm_eq hf (by omega) (c := 1) one_ne_zero
  obtain ⟨e₂, h2, h21⟩ := F3.exists_norm_eq_perp hf (by omega) h1 (c := 1) one_ne_zero
  have h12 : f e₁ e₂ = 0 := by rw [hf.symm]; exact h21
  obtain ⟨e₃, h3, h31, h32⟩ :=
    F3.exists_norm_eq_perp_two hf (by omega) h1 h2 h12 (c := 1) one_ne_zero
  have h13 : f e₁ e₃ = 0 := by rw [hf.symm]; exact h31
  have h23 : f e₂ e₃ = 0 := by rw [hf.symm]; exact h32
  obtain ⟨y, hy, hyy⟩ := F3.exists_mem_norm_eq hf (nondegOn_perp_three hf h1 h2 h3 h12 h13 h23)
    (F3.perpSub_twoDim hf (k := 3) (by omega) ![e₁, e₂, e₃]) (c := 1) one_ne_zero
  obtain ⟨hy1, hy2, hy3⟩ := F3.mem_perpSub_three.1 hy
  have h1y : f e₁ y = 0 := by rw [hf.symm]; exact hy1
  have h2y : f e₂ y = 0 := by rw [hf.symm]; exact hy2
  have h3y : f e₃ y = 0 := by rw [hf.symm]; exact hy3
  refine ⟨e₁ + e₂ + e₃ + y, e₁, e₂, e₃, ?_, h1, h2, h3, h12, h13, h23, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, h1, h2, h3, hyy,
      h12, h13, h23, h21, h31, h32, hy1, hy2, hy3, h1y, h2y, h3y, add_zero, zero_add]
    decide
  · simp only [LinearMap.BilinForm.add_left, h1, h21, h31, hy1, add_zero]
  · simp only [LinearMap.BilinForm.add_left, h12, h2, h32, hy2, add_zero, zero_add]
  · simp only [LinearMap.BilinForm.add_left, h13, h23, h3, hy3, add_zero, zero_add]

theorem exists_reflStar_vectors (hsym : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0) (hm : 5 ≤ m) :
    ∃ v e₁ e₂ e₃ : Fin m → ZMod 3, f v v = 1 ∧ f e₁ e₁ = 1 ∧ f e₂ e₂ = 1 ∧ f e₃ e₃ = 1 ∧
      f e₁ e₂ = 0 ∧ f e₁ e₃ = 0 ∧ f e₂ e₃ = 0 ∧ f v e₁ = 1 ∧ f v e₂ = 1 ∧ f v e₃ = 1 :=
  exists_star_vectors ⟨hsym, hnd⟩ hm

end Vectors

theorem hasCoreStar_of_reflModel {G : Type} [Group G] {t : G}
    (hP : Pair G {x | IsConj t x}) {m : ℕ} (hm : 5 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hsym : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel {x : G | IsConj t x}
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    HasCoreStar G t := by
  have hf : IsF3Form f := ⟨hsym, hnd⟩
  obtain ⟨v, e₁, e₂, e₃, hv, h1, h2, h3, h12, h13, h23, hv1, hv2, hv3⟩ :=
    exists_star_vectors hf hm
  obtain ⟨φ, hφ⟩ := hmod
  let ρ : (Fin m → ZMod 3) → ↥(F3.reflGroup f) := fun u =>
    ⟨F3.refl f u, F3.refl_mem_reflGroup u⟩
  have hρ : ∀ u, ((ρ u : ↥(F3.reflGroup f)) : GL (Fin m) (ZMod 3)) = F3.refl f u := fun _ => rfl
  let g : (Fin m → ZMod 3) → G := fun u => φ.symm (QuotientGroup.mk (ρ u))
  have hgD : ∀ u, f u u = 1 → IsConj t (g u) := fun u hu =>
    (hφ (g u)).mpr ⟨ρ u, F3.refl_mem_reflSet hu, by simp [g]⟩
  have hgmul : ∀ u u', g u * g u' = φ.symm (QuotientGroup.mk (ρ u * ρ u')) := fun u u' => by
    simp only [g, ← map_mul, QuotientGroup.mk_mul]
  have hcomm : ∀ u u', f u u = 1 → f u' u' = 1 → f u u' = 0 → g u * g u' = g u' * g u := by
    intro u u' hu hu' h
    rw [hgmul, hgmul, show ρ u * ρ u' = ρ u' * ρ u from
      Subtype.ext ((F3.refl_commute_iff hf hu hu').2 (Or.inl h))]
  have hinj : ∀ u u', f u u = 1 → f u' u' = 1 → g u = g u' → u' = u ∨ u' = -u := by
    intro u u' hu hu' h
    have hc : (ρ u)⁻¹ * ρ u' ∈ Subgroup.center ↥(F3.reflGroup f) :=
      QuotientGroup.eq.mp (φ.symm.injective h)
    rcases F3.coe_eq_of_mem_center hf (by omega) hc with h2 | h2
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hρ, hρ, inv_mul_eq_one] at h2
      exact (F3.refl_eq_refl_iff hu hu').mp h2
    · exfalso
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hρ, hρ, inv_mul_eq_iff_eq_mul, mul_neg_one] at h2
      exact F3.refl_ne_neg_refl (f := f) (by omega) u u' h2
  have hord : ∀ u u', f u u = 1 → f u' u' = 1 → f u u' ≠ 0 → u' ≠ u → u' ≠ -u →
      orderOf (g u * g u') = 3 := by
    intro u u' hu hu' h hne hne'
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [hgmul, ← map_pow, ← QuotientGroup.mk_pow, show (ρ u * ρ u') ^ 3 = 1 from
        Subtype.ext (by simpa [hρ] using F3.refl_mul_refl_pow_three hf hu hu' h),
        QuotientGroup.mk_one, map_one]
    · have hgu : g u * g u = 1 := CFSG.Fischer.Pair.mul_self hP (hgD u hu)
      have hgu' : g u' = g u := by
        rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hgu]
      rcases hinj u u' hu hu' hgu'.symm with h2 | h2
      exacts [hne h2, hne' h2]
  have hsep : ∀ {a e : Fin m → ZMod 3}, f a e = 0 → f v e = 1 → a ≠ v ∧ a ≠ -v := by
    intro a e ha hve
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, hve] at ha
      exact one_ne_zero ha
    · rw [h, LinearMap.BilinForm.neg_left, hve] at ha
      exact absurd ha (by decide)
  have h21 : f e₂ e₁ = 0 := by rw [hf.symm]; exact h12
  have h31 : f e₃ e₁ = 0 := by rw [hf.symm]; exact h13
  obtain ⟨n1v, n1v'⟩ := hsep h12 hv2
  obtain ⟨n2v, n2v'⟩ := hsep h21 hv1
  obtain ⟨n3v, n3v'⟩ := hsep h31 hv1
  have hne : ∀ {a b : Fin m → ZMod 3}, f a a = 1 → f b b = 1 → f a b = 0 → g a ≠ g b := by
    intro a b ha hb hab h
    rcases hinj a b ha hb h with h' | h'
    · rw [h', ha] at hab
      exact one_ne_zero hab
    · rw [h', LinearMap.BilinForm.neg_right, ha] at hab
      exact absurd hab (by decide)
  exact hasCoreStar_of_center (hgD v hv) (hgD e₁ h1) (hgD e₂ h2) (hgD e₃ h3)
    (hord v e₁ hv h1 (by rw [hv1]; exact one_ne_zero) n1v n1v')
    (hord v e₂ hv h2 (by rw [hv2]; exact one_ne_zero) n2v n2v')
    (hord v e₃ hv h3 (by rw [hv3]; exact one_ne_zero) n3v n3v')
    (hcomm e₁ e₂ h1 h2 h12) (hcomm e₁ e₃ h1 h3 h13) (hcomm e₂ e₃ h2 h3 h23)
    (hne h1 h2 h12) (hne h1 h3 h13) (hne h2 h3 h23)

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
