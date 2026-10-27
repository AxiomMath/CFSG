module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3E9GL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FifteenEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private def s16t_klein_conjAut {H : Type} [Group H] {A B : Subgroup H}
    (hnorm : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (b : ↥B) : MulAut ↥A where
  toFun a := ⟨(b : H) * (a : H) * (b : H)⁻¹, hnorm b b.2 a a.2⟩
  invFun a := ⟨(b : H)⁻¹ * (a : H) * (b : H),
    by simpa using hnorm (b : H)⁻¹ (B.inv_mem b.2) a a.2⟩
  left_inv a := by apply Subtype.ext; group
  right_inv a := by apply Subtype.ext; group
  map_mul' a c := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    group

private theorem s16t_klein_conjAut_coe {H : Type} [Group H] {A B : Subgroup H}
    (hnorm : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (b : ↥B) (a : ↥A) :
    ((s16t_klein_conjAut hnorm b a : ↥A) : H) = (b : H) * (a : H) * (b : H)⁻¹ := rfl

private def s16t_klein_conjHom {H : Type} [Group H] {A B : Subgroup H}
    (hnorm : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) : ↥B →* MulAut ↥A where
  toFun := s16t_klein_conjAut hnorm
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    simp only [MulAut.one_apply, s16t_klein_conjAut_coe, Subgroup.coe_one, one_mul, inv_one,
      mul_one]
  map_mul' b c := by
    apply MulEquiv.ext
    intro a
    rw [MulAut.mul_apply]
    apply Subtype.ext
    simp only [s16t_klein_conjAut_coe, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
    group

private theorem s16t_klein_conjHom_apply {H : Type} [Group H] {A B : Subgroup H}
    (hnorm : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (b : ↥B) (a : ↥A) :
    s16t_klein_conjHom hnorm b a = s16t_klein_conjAut hnorm b a := rfl

private theorem s16t_klein_congr_apply {G K : Type} [Group G] [Group K] (e : G ≃* K)
    (f : MulAut G) (x : G) : (MulAut.congr e) f (e x) = e (f x) := by
  rw [MulAut.congr_apply]
  simp

private theorem s16t_klein_conjHom_injective {H : Type} [Group H] {A B : Subgroup H}
    (hnorm : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    (hcent : ∀ b ∈ B, (∀ a ∈ A, b * a = a * b) → b = 1) :
    Function.Injective (s16t_klein_conjHom hnorm) := by
  refine (injective_iff_map_eq_one (s16t_klein_conjHom hnorm)).mpr ?_
  intro b hb
  apply Subtype.ext
  apply hcent (b : H) b.2
  intro a ha
  have h := congrArg (fun g : MulAut ↥A => ((g ⟨a, ha⟩ : ↥A) : H)) hb
  have h2 : (b : H) * a * (b : H)⁻¹ = a := by
    simpa only [s16t_klein_conjHom_apply, s16t_klein_conjAut_coe, MulAut.one_apply,
      Subtype.coe_mk] using h
  calc (b : H) * a = (b : H) * a * (b : H)⁻¹ * (b : H) := by group
    _ = a * (b : H) := by rw [h2]

theorem s16t_klein_of_selfCentralizing {H : Type} [Group H] [Finite H] {A B : Subgroup H}
    (hA : IsElemAbelianOfRank 3 2 ↥A) (hnorm : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    (hcent : ∀ b ∈ B, (∀ a ∈ A, b * a = a * b) → b = 1)
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card B ≤ 4 ∧ (2 < Nat.card B → ∃ z ∈ B, ∀ a ∈ A, z * a * z⁻¹ = a⁻¹) := by
  classical
  haveI : Finite ↥B := Subtype.finite
  obtain ⟨e⟩ := hA
  let ψ : ↥B →* MulAut ↥A := s16t_klein_conjHom hnorm
  have hψ : Function.Injective ψ := s16t_klein_conjHom_injective hnorm hcent
  let φ : ↥B →* MulAut (Multiplicative (Fin 2 → ZMod 3)) :=
    (MulAut.congr e).toMonoidHom.comp ψ
  have hφ : Function.Injective φ := fun x y hxy => hψ ((MulAut.congr e).injective hxy)
  have hc' : ∀ x y : ↥B, x * y = y * x := by
    intro x y
    apply Subtype.ext
    exact hc (x : H) x.2 (y : H) y.2
  have h2' : ∀ x : ↥B, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    simpa using h2 (x : H) x.2
  refine ⟨s16c167_card_le_four_of_aut_E9 hc' h2' φ hφ, ?_⟩
  intro hgt
  obtain ⟨z, hz⟩ := s16t_exists_inv_of_aut_E9 hc' h2' φ hφ hgt
  refine ⟨(z : H), z.2, ?_⟩
  intro a ha
  have hza : ψ z (⟨a, ha⟩ : ↥A) = (⟨a, ha⟩ : ↥A)⁻¹ := by
    apply e.injective
    rw [map_inv, ← s16t_klein_congr_apply e (ψ z) ⟨a, ha⟩]
    exact hz (e ⟨a, ha⟩)
  have hcoe := congrArg (fun w : ↥A => (w : H)) hza
  simpa [ψ, s16t_klein_conjHom_apply, s16t_klein_conjAut_coe] using hcoe

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
