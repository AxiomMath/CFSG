module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidLift
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidGram
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernary
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTransport

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) zx5_zmodThreeAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
  {A : Subgroup (U ≃ₗ[ZMod 3] U)}

theorem exists_isometry_of_mulEquiv_R3_diagF3_five_two (hn : 3 ≤ Module.finrank (ZMod 3) U)
    (hirr : AbsIrred 3 A) (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 5 2))
    (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 (diagF3 5 2)) {B : LinearMap.BilinForm (ZMod 3) U}
    (hBs : ∀ x y, B x y = B y x) (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u) :
    ∃ L : (Fin 5 → ZMod 3) ≃ₗ[ZMod 3] U, ∀ x y, B (L x) (L y) = diagF3 5 2 x y := by
  obtain ⟨y, hy, hne, hforest, hspan, hgen⟩ := exists_forest_spanning_diagF3_five_two
  obtain ⟨u, hgram, hlift⟩ := exists_roots_of_forest hn hirr (m := 5) (by norm_num)
    (f := diagF3 5 2) (isF3Form_diagF3 (by decide)) φ hφ hBs hB (k := 6) y hy hne hforest
  let tfun : Fin 6 → ↥A := fun i => (hlift i).choose
  have ht_act : ∀ i x, ((tfun i : ↥A) : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i :=
    fun i => ((hlift i).choose_spec).2.2
  have ht_phi : ∀ i, φ (QuotientGroup.mk (tfun i)) = reflBar (diagF3 5 2) (y i) :=
    fun i => ((hlift i).choose_spec).2.1
  let X : Submodule (ZMod 3) U := Submodule.span (ZMod 3) (Set.range u)
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hmem : u 0 ∈ X := Submodule.subset_span (Set.mem_range_self 0)
    rw [hbot] at hmem
    have hu0 : u 0 = 0 := by simpa using hmem
    have h1 : B (u 0) (u 0) = 1 := by
      rw [hgram]
      exact hy 0
    have hzero : B (0 : U) 0 = 0 := by simp
    rw [hu0] at h1
    rw [hzero] at h1
    exact zero_ne_one h1
  have hXinv : ∀ t ∈ Set.range tfun, ∀ x ∈ X,
      ((t : ↥A) : U ≃ₗ[ZMod 3] U) x ∈ X := by
    rintro t ⟨i, rfl⟩ x hx
    rw [ht_act i x]
    exact Submodule.add_mem X hx
      (Submodule.smul_mem X _ (Submodule.subset_span (Set.mem_range_self (f := u) i)))
  have hqtop : Subgroup.closure
      ((QuotientGroup.mk : ↥A → ↥A ⧸ Subgroup.center ↥A) '' Set.range tfun) = ⊤ := by
    let mkh : ↥A →* ↥A ⧸ Subgroup.center ↥A := QuotientGroup.mk' (Subgroup.center ↥A)
    have hmk : (mkh : ↥A → ↥A ⧸ Subgroup.center ↥A) = QuotientGroup.mk := rfl
    have himage : (φ.toMonoidHom : ↥A ⧸ Subgroup.center ↥A →* R3 (diagF3 5 2)) ''
        (mkh '' Set.range tfun) = Set.range (fun i => reflBar (diagF3 5 2) (y i)) := by
      rw [Set.image_image]
      rw [← Set.range_comp' (fun x => φ.toMonoidHom (mkh x)) tfun]
      congr 1
      funext i
      exact ht_phi i
    have hmap : Subgroup.map (φ.toMonoidHom : ↥A ⧸ Subgroup.center ↥A →* R3 (diagF3 5 2))
        (Subgroup.closure (mkh '' Set.range tfun)) = ⊤ := by
      rw [MonoidHom.map_closure, himage, hgen]
    rw [hmk] at hmap
    refine Subgroup.map_injective (f := (φ.toMonoidHom : _ →* R3 (diagF3 5 2))) φ.injective ?_
    rw [hmap, Subgroup.map_top_of_surjective _ φ.surjective]
  have hX : X = ⊤ := AbsIrred.eq_top_of_closure_mk_image_eq_top hirr hXne hXinv hqtop
  obtain ⟨L, _, hiso⟩ := exists_linearEquiv_of_gram_eq (V := Fin 5 → ZMod 3) (W := U)
    (f := diagF3 5 2) (B := B) (y := y) (u := u) (isF3Form_diagF3 (by decide)).nondeg hBnd
    hspan hX hgram
  exact ⟨L, hiso⟩

end CFSG.StandardType.ZS
