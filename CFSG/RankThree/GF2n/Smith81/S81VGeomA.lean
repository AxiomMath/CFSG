module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomAup
public import CFSG.RankThree.GF2n.Smith81.S81VGeomAlow

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem exists_normalized_gen_of_mem [Finite F] (hσ : ∀ c, σ (σ c) = c)
    {U : Submodule F (Fin 6 → F)} (hno : ∀ L ≤ U, finrank F L = 2 → ¬ IsTotIso σ L)
    {S : Set (Fin 6 → F)} (hS : ClosedPts σ S) {z : Fin 6 → F} (hzU : z ∈ U) (hz0 : z ≠ 0)
    (hzi : herm σ z z = 0) (hzS : z ∉ S) {x : Fin 6 → F} (hxS : x ∈ S) (hxU : x ∈ U) :
    ∃ y : Fin 6 → F, (y ∈ S ∧ y ∈ U ∧ herm σ z y = 1) ∧
      Submodule.span F {y} = Submodule.span F {x} := by
  have hx0 : x ≠ 0 := (hS.iso x hxS).1
  have hxi : herm σ x x = 0 := (hS.iso x hxS).2
  have hxz : x ∉ Submodule.span F {z} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hx0
      rw [← hc, zero_smul]
    apply hzS
    have hzc : z = c⁻¹ • x := by
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hzc]
    exact hS.smul x hxS c⁻¹ (inv_ne_zero hc0)
  have hcz : herm σ z x ≠ 0 := herm_ne_zero_of_noTI hσ hno hzU hxU hz0 hxz hzi hxi
  refine ⟨(herm σ z x)⁻¹ • x, ⟨hS.smul x hxS (herm σ z x)⁻¹ (inv_ne_zero hcz),
    Submodule.smul_mem U (herm σ z x)⁻¹ hxU, ?_⟩, ?_⟩
  · rw [herm_smul_right, inv_mul_cancel₀ hcz]
  · exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hcz)) x

theorem card_points_le_normalized [Finite F] (hσ : ∀ c, σ (σ c) = c)
    {U : Submodule F (Fin 6 → F)} (hno : ∀ L ≤ U, finrank F L = 2 → ¬ IsTotIso σ L)
    {S : Set (Fin 6 → F)} (hS : ClosedPts σ S) {z : Fin 6 → F} (hzU : z ∈ U) (hz0 : z ≠ 0)
    (hzi : herm σ z z = 0) (hzS : z ∉ S) :
    Nat.card {r : Submodule F (Fin 6 → F) // ∃ x ∈ S, x ∈ U ∧ r = Submodule.span F {x}} ≤
      Nat.card {x : Fin 6 → F // x ∈ S ∧ x ∈ U ∧ herm σ z x = 1} := by
  refine Nat.card_le_card_of_surjective
    (fun y : {x : Fin 6 → F // x ∈ S ∧ x ∈ U ∧ herm σ z x = 1} =>
      (⟨Submodule.span F {y.1}, y.1, y.2.1, y.2.2.1, rfl⟩ :
        {r : Submodule F (Fin 6 → F) // ∃ x ∈ S, x ∈ U ∧ r = Submodule.span F {x}})) ?_
  rintro ⟨r, x, hxS, hxU, rfl⟩
  obtain ⟨y, ⟨hyS, hyU, hyz⟩, hy⟩ :=
    exists_normalized_gen_of_mem hσ hno hS hzU hz0 hzi hzS hxS hxU
  exact ⟨⟨y, hyS, hyU, hyz⟩, Subtype.ext hy⟩

theorem lemmaA [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ) {U : Submodule F (Fin 6 → F)}
    (hU : NonDeg σ U) (h3 : finrank F U = 3) {S : Set (Fin 6 → F)} (hS : ClosedPts σ S)
    {a b c : Fin 6 → F} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (haU : a ∈ U) (hbU : b ∈ U)
    (hcU : c ∈ U) (hind : LinearIndependent F ![a, b, c]) :
    ∀ z ∈ U, z ≠ 0 → herm σ z z = 0 → z ∈ S := by
  intro z hzU hz0 hzi
  by_contra hzS
  have hno : ∀ L ≤ U, finrank F L = 2 → ¬ IsTotIso σ L :=
    fun L hL h2 => noTI_of_nonDeg_three hσ.invol hU h3 hL h2
  have h1 := card_points_ge hσ h3 hno hS ha hb hc haU hbU hcU hind
  have h2 := card_points_le_normalized hσ.invol hno hS hzU hz0 hzi hzS
  have h4 := card_normalized_le hσ.invol hU h3 hS hzU hz0 hzi hzS
  omega

end CFSG.RankThree.GF2n.Smith81.S81V
