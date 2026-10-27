module

public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Quasithin Matrix Matrix.SpecialLinearGroup
open scoped commutatorElement

theorem exists_commutator_eq_transvection {i j : Fin 3} (hij : i ≠ j) :
    ∃ a b : L3.Γ, ⁅a, b⁆ = transvection hij (1 : ZMod 2) := by
  obtain ⟨k, hik, hkj⟩ : ∃ k : Fin 3, i ≠ k ∧ k ≠ j := by
    revert hij; revert i j; decide
  have := commutatorElement_transvection hik hkj hij (1 : ZMod 2) (1 : ZMod 2)
  rw [mul_one] at this
  exact ⟨_, _, this⟩

theorem hom_eq_one {A : Type*} [CommGroup A] (f : L3.Γ →* A) (γ : L3.Γ) : f γ = 1 := by
  have hc : ∀ a b : L3.Γ, f ⁅a, b⁆ = 1 := fun a b => by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have ht : ∀ (i j : Fin 3) (hij : i ≠ j) (c : ZMod 2), f (transvection hij c) = 1 := by
    intro i j hij c
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [transvection_coeff_zero, map_one]
    · obtain ⟨a, b, hab⟩ := exists_commutator_eq_transvection hij
      rw [← hab]
      exact hc a b
  have hle : (⊤ : Subgroup L3.Γ) ≤ f.ker := by
    rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := Fin 3) (K := ZMod 2), Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact ht t.i t.j t.hij t.c
  exact hle (Subgroup.mem_top γ)

variable {V : Type*} [CommGroup V]

theorem invariant_of_commV_le {G : Subgroup (MulAut V)} {A : Subgroup V} (h : commV G ≤ A) :
    ∀ g ∈ G, ∀ a ∈ A, g a ∈ A := by
  intro g hg a ha
  have e : g a = (g a * a⁻¹) * a := by group
  rw [e]
  exact A.mul_mem (h (Subgroup.subset_closure ⟨g, hg, a, rfl⟩)) ha

section Data

variable {G : Subgroup (MulAut V)} {W₂ W₁ : Subgroup V} (D : L3Data G W₂ W₁)
include D

theorem mem_fixV_of_forall {K : Subgroup V} (hK : K ≤ fixV G) {x : V}
    (hx : ∀ g ∈ G, g x * x⁻¹ ∈ K) : x ∈ fixV G := by
  let f : L3.Γ →* K :=
    { toFun := fun γ => ⟨D.rho γ x * x⁻¹, hx _ (D.rho_mem γ)⟩
      map_one' := by
        apply Subtype.ext
        change D.rho 1 x * x⁻¹ = 1
        rw [map_one, MulAut.one_apply, mul_inv_cancel]
      map_mul' := fun γ δ => by
        apply Subtype.ext
        change D.rho (γ * δ) x * x⁻¹ = (D.rho γ x * x⁻¹) * (D.rho δ x * x⁻¹)
        have h1 : D.rho γ (D.rho δ x * x⁻¹) = D.rho δ x * x⁻¹ :=
          hK (hx _ (D.rho_mem δ)) _ (D.rho_mem γ)
        rw [map_mul, map_inv] at h1
        have e : D.rho γ (D.rho δ x) = D.rho δ x * x⁻¹ * D.rho γ x := by rw [← h1]; group
        rw [map_mul, MulAut.mul_apply, e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel }
  intro g hg
  obtain ⟨γ, rfl⟩ := D.exists_rho hg
  have h := congrArg Subtype.val (hom_eq_one f γ)
  change D.rho γ x * x⁻¹ = 1 at h
  exact mul_inv_eq_one.mp h

theorem commSub_commV : commSub (commV G) G = commV G := by
  apply le_antisymm
  · rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  · set U₂ := commSub (commV G) G with hU₂
    have hle : U₂ ≤ commV G := by
      rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨g, hg, v, rfl⟩
    have hmem : ∀ γ, D.rho γ v * v⁻¹ ∈ commV G := fun γ =>
      Subgroup.subset_closure ⟨D.rho γ, D.rho_mem γ, v, rfl⟩
    let f : L3.Γ →* ↥(commV G) ⧸ U₂.subgroupOf (commV G) :=
      { toFun := fun γ => QuotientGroup.mk ⟨D.rho γ v * v⁻¹, hmem γ⟩
        map_one' := by
          show (QuotientGroup.mk ⟨D.rho 1 v * v⁻¹, hmem 1⟩ :
            ↥(commV G) ⧸ U₂.subgroupOf (commV G)) = QuotientGroup.mk 1
          congr 1
          apply Subtype.ext
          change D.rho 1 v * v⁻¹ = 1
          rw [map_one, MulAut.one_apply, mul_inv_cancel]
        map_mul' := fun γ δ => by
          show (QuotientGroup.mk ⟨D.rho (γ * δ) v * v⁻¹, hmem _⟩ :
            ↥(commV G) ⧸ U₂.subgroupOf (commV G)) =
              QuotientGroup.mk ⟨D.rho γ v * v⁻¹, hmem γ⟩ *
                QuotientGroup.mk ⟨D.rho δ v * v⁻¹, hmem δ⟩
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have hc : D.rho γ (D.rho δ v * v⁻¹) * (D.rho δ v * v⁻¹)⁻¹ ∈ U₂ :=
            Subgroup.subset_closure ⟨D.rho γ, D.rho_mem γ, _, hmem δ, rfl⟩
          convert U₂.inv_mem hc using 1
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, MulAut.mul_apply, map_inv]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel }
    obtain ⟨γ, rfl⟩ := D.exists_rho hg
    have h : (QuotientGroup.mk ⟨D.rho γ v * v⁻¹, hmem γ⟩ :
        ↥(commV G) ⧸ U₂.subgroupOf (commV G)) = QuotientGroup.mk 1 := hom_eq_one f γ
    rw [QuotientGroup.eq, mul_one, inv_mem_iff, Subgroup.mem_subgroupOf] at h
    exact h

end Data

end CFSG.Quasithin.Vol2.Ch10.V1C
