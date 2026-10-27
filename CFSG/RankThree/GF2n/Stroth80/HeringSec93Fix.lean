module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreM
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Head

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalGroups.F2Fixed
open CFSG.Open.StatedAPI
open scoped Matrix

namespace HS9

section Geometry

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_LomGL_plus_two91
    (E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)))
    {u : Fin 2 ⊕ Fin 2 → K} (hu : quadPlus 2 K u = 0) (hu0 : u ≠ 0) :
    Nat.card (E.LomGL u) = Nat.card K ^ 2 := by
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  have hLe := rootGroup_le_elementaryGroup (quadPlus 2 K) u
  have hLom : Nat.card ↥(Lom (quadPlus 2 K) u) = Nat.card ↥(rootGroup (quadPlus 2 K) u) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLe).toEquiv
  have hfin : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
  have h1 : Nat.card ↥((Lom (quadPlus 2 K) u).comap E.equiv.toMonoidHom) =
      Nat.card ↥(Lom (quadPlus 2 K) u) := by
    have h := Subgroup.comap_equiv_eq_map_symm E.equiv (Lom (quadPlus 2 K) u)
    erw [h]
    exact Subgroup.card_map_of_injective (f := E.equiv.symm.toMonoidHom) E.equiv.symm.injective
  unfold ElemMatrixIso.LomGL matrixOf
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h1, hLom,
    card_rootGroup hQ hu hu0, hfin]

theorem card_eq_two_pow91 : ∃ e : ℕ, Nat.card K = 2 ^ e := by
  letI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem exists_singular_fixed91 (h4 : 4 ≤ Nat.card K)
    (E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)))
    {u : Fin 2 ⊕ Fin 2 → K} (hu : quadPlus 2 K u = 0) (hu0 : u ≠ 0)
    {U₀ : Subgroup (GL (Fin 2 ⊕ Fin 2) K)} (hU : U₀ ≤ StatedOmega (StatedQuadPlus 2 K))
    (h2 : IsPGroup 2 U₀) :
    ∃ p : Fin 2 ⊕ Fin 2 → K, p ≠ 0 ∧ quadPlus 2 K p = 0 ∧
      ∀ g ∈ U₀,
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ p = p := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := StatedOmega (StatedQuadPlus 2 K) with hXdef
  have hS₁X : E.LomGL u ≤ X := fun A hA => ((mem_matrixOf_iff).mp hA).1
  let S₁ : Subgroup ↥X := (E.LomGL u).subgroupOf X
  let U₀' : Subgroup ↥X := U₀.subgroupOf X
  have hcardX : Nat.card ↥X = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := card_omegaPlus_four h4
  have hcardS₁ : Nat.card S₁ = Nat.card K ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₁X).toEquiv]
    exact card_LomGL_plus_two91 E hu hu0
  obtain ⟨e, he⟩ := card_eq_two_pow91 (K := K)
  have he1 : 1 ≤ e := by
    by_contra h
    have : e = 0 := by omega
    rw [this, pow_zero] at he
    omega
  have hp1 : IsPGroup 2 S₁ :=
    IsPGroup.of_card (n := 2 * e) (by rw [hcardS₁, he, ← pow_mul, mul_comm])
  have hindex : ¬ 2 ∣ S₁.index := by
    have h := Subgroup.card_mul_index S₁
    rw [hcardX, hcardS₁] at h
    have h' : S₁.index = (Nat.card K ^ 2 - 1) ^ 2 := by
      refine Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := K)) 2) ?_
      rw [h, mul_pow]
    rw [h']
    intro hd
    have hd2 : 2 ∣ Nat.card K ^ 2 - 1 := Nat.prime_two.dvd_of_dvd_pow hd
    have hq2 : 2 ∣ Nat.card K ^ 2 := by
      rw [he, ← pow_mul]
      exact dvd_pow_self 2 (by omega)
    have hpos : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    omega
  let P₁ : Sylow 2 ↥X := hp1.toSylow hindex
  have hU₀' : IsPGroup 2 U₀' :=
    h2.of_injective (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hU).injective
  obtain ⟨P₂, hP₂⟩ := hU₀'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X P₁ P₂
  have hfix : ∀ y : GL (Fin 2 ⊕ Fin 2) K, y ∈ E.LomGL u →
      (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u = u := by
    intro y hy
    obtain ⟨-, w, -, hw⟩ := (Om10.mem_LomGL_iff_eichler E).mp hy
    rw [hw u, eichler_apply_self]
  refine ⟨((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u, ?_, ?_, ?_⟩
  · intro h0
    apply hu0
    have h1 : (((g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    exact h1.symm
  · rw [E.quad_mulVec g.2 u]
    exact hu
  · intro x hxU
    have hxX : x ∈ X := hU hxU
    have hmem : (⟨x, hxX⟩ : ↥X) ∈ (P₂ : Subgroup ↥X) := hP₂ hxU
    rw [← hg] at hmem
    have hmem' : g⁻¹ * ⟨x, hxX⟩ * g ∈ (P₁ : Subgroup ↥X) := by
      have := (Sylow.coe_subgroup_smul (g := g) (P := P₁)) ▸ hmem
      simpa [Subgroup.mem_smul_pointwise_iff_exists, MulAut.smul_def] using
        (Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp this)
    have hS : (g⁻¹ * ⟨x, hxX⟩ * g : ↥X) ∈ S₁ := hmem'
    have hy : (((g⁻¹ * ⟨x, hxX⟩ * g : ↥X) : GL (Fin 2 ⊕ Fin 2) K)) ∈ E.LomGL u :=
      Subgroup.mem_subgroupOf.mp hS
    have hfy := hfix _ hy
    set y : GL (Fin 2 ⊕ Fin 2) K := (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ * x * (g : GL (Fin 2 ⊕ Fin 2) K)
      with hydef
    have hfy' : ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u = u :=
      hfy
    have key : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [← Units.val_mul, ← Units.val_mul, hydef]
      congr 1
      group
    rw [Matrix.mulVec_mulVec, ← key, ← Matrix.mulVec_mulVec, hfy']

theorem exists_nonsingular_perp_value91 {u u' : Fin 2 ⊕ Fin 2 → K}
    (hu : quadPlus 2 K u = 0) (hu' : quadPlus 2 K u' = 0)
    (huu' : polar (quadPlus 2 K) u u' ≠ 0) {c : K} (hc : c ≠ 0) :
    ∃ d : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) u d = 0 ∧ polar (quadPlus 2 K) u' d = 0 ∧
      quadPlus 2 K d = c := by
  obtain ⟨a, ha, ha', hQa⟩ :=
    exists_nonsingular_perp91 (nondegenerate_polarBilin_quadPlus 2 K) hu hu' huu'
  obtain ⟨κ, hκ⟩ := isSquare_of_charTwo' (c / quadPlus 2 K a)
  refine ⟨κ • a, ?_, ?_, ?_⟩
  · rw [polar_smul_right_eq, ha, mul_zero]
  · rw [polar_smul_right_eq, ha', mul_zero]
  · rw [map_smul_eq_sq, _root_.sq, ← hκ]
    field_simp

end Geometry

end HS9

end CFSG.RankThree.GF2n.Stroth80
