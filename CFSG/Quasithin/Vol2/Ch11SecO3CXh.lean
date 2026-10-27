module

public import CFSG.Quasithin.Vol2.Ch11SecO3CXg

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

open CFSG.Quasithin CFSG.Quasithin.H13 Matrix
open CFSG.Quasithin.Vol2.KGNat (IsCoord linModelNat gmapSp spLine spHyp vec4 spJ spB_e0 spB_mat
  v0_ne_zero mat_mulVec_inv mat_inv_mulVec)
open CFSG.Quasithin.Vol2.KGNat.KA (gconj_mulVec_sp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom)
open CFSG.Quasithin.Vol2.Ch11.SecB.K7 (trv trv_zero trv_conj trv_smul bil_comm)
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_centralizer_of_conjV_eq_one {V : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (V : Set G)) (h1 : SecA.conjV V h hh = 1) :
    h ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have e1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h1
  simp only [SecA.conjV_apply_coe, MulAut.one_apply] at e1
  exact (mul_inv_eq_iff_eq_mul.mp e1).symm

theorem conjV_one {V : Subgroup G} (h1 : (1 : G) ∈ Subgroup.normalizer (V : Set G)) :
    SecA.conjV V 1 h1 = 1 := by
  ext v
  simp [SecA.conjV_apply_coe]

section Coord

variable {T L I : Subgroup G} [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K]
  {π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)}

theorem mem_normalizer_of_eigen
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f) {g : StatedSp 2 K}
    {V₁ : Subgroup G} (hV₁V : V₁ ≤ fsuV T I)
    (hV₁ : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup) {h : G}
    (hh : h ∈ Subgroup.normalizer (fsuV T I : Set G)) {δ : StatedSp 2 K}
    (hδ : SecA.conjV (fsuV T I) h hh = ((π δ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {l : K} (hl : mat 2 K δ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) = l • (mat 2 K g *ᵥ vec4 1 0 0 0)) :
    h ∈ Subgroup.normalizer (V₁ : Set G) := by
  rw [← SecA.conjV_mem_stabW_iff hV₁V hh, SecA.mem_stabW, hδ]
  intro u
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, O2.mem_v1_iff hV₁, O2.mem_v1_iff hV₁,
    hf.act4]
  exact smul_iff_of_mulVec_eq (v0_ne_zero g) hl (f u)

theorem mem_conj_iff (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    {g : StatedSp 2 K} {V₁ : Subgroup G}
    (hV₁ : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup) {y : G}
    (hy : y ∈ Subgroup.normalizer (fsuV T I : Set G)) {γ : StatedSp 2 K}
    (hγ : SecA.conjV (fsuV T I) y hy = ((π γ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (w : ↥(fsuV T I)) :
    (w : G) ∈ conjSubgroup V₁ y ↔
      ∃ c : K, f w = c • (mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)) := by
  rw [mem_conjSubgroup_iff, ← SecA.conjV_apply_coe (fsuV T I) hy w, O2.mem_v1_iff hV₁, hγ,
    hf.act4]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have e1 := congrArg (fun v => mat 2 K γ⁻¹ *ᵥ v) hc
    simpa only [mat_inv_mulVec, Matrix.mulVec_smul] using e1
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, Matrix.mulVec_smul, mat_mulVec_inv]⟩

variable [CharP K 2]

theorem bil_ne_zero (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    {g : StatedSp 2 K} {V₁ V₃ : Subgroup G}
    (hV₁ : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup)
    (hV₃ : V₃.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spHyp K)).toAddSubgroup) {y : G}
    (hy : y ∈ Subgroup.normalizer (fsuV T I : Set G)) {γ : StatedSp 2 K}
    (hγ : SecA.conjV (fsuV T I) y hy = ((π γ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hopp : conjSubgroup V₁ y ⊓ V₃ = ⊥) :
    Matrix.toBilin' (spJ K) (mat 2 K g *ᵥ vec4 1 0 0 0)
      (mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)) ≠ 0 := by
  intro h0
  obtain ⟨w, hw⟩ := hf.surj (mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0))
  have h1 : (w : G) ∈ conjSubgroup V₁ y := (mem_conj_iff hf hV₁ hy hγ w).mpr ⟨1, by
    rw [hw, one_smul]⟩
  have h2 : (w : G) ∈ V₃ := (O2.mem_v3_iff hV₃ w).mpr (by rw [hw, bil_comm]; exact h0)
  have h3 : (w : G) ∈ conjSubgroup V₁ y ⊓ V₃ := ⟨h1, h2⟩
  rw [hopp, Subgroup.mem_bot] at h3
  have h4 : w = 1 := Subtype.ext h3
  have h5 : mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) = 0 := by rw [← hw, h4, hf.map_one]
  have h6 := congrArg (fun v => mat 2 K γ *ᵥ v) h5
  simp only [mat_mulVec_inv, Matrix.mulVec_zero] at h6
  exact v0_ne_zero g h6

theorem eq_smul_of_mem_normalizer
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f) {g g' : StatedSp 2 K}
    (hg' : mat 2 K g' *ᵥ vec4 1 0 0 0 = mat 2 K g *ᵥ vec4 1 0 0 0) {V₁ : Subgroup G}
    (hV₁ : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup) {y : G}
    (hy : y ∈ Subgroup.normalizer (fsuV T I : Set G)) {γ : StatedSp 2 K}
    (hγ : SecA.conjV (fsuV T I) y hy = ((π γ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hβ : Matrix.toBilin' (spJ K) (mat 2 K g *ᵥ vec4 1 0 0 0)
      (mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)) ≠ 0)
    {a : Kˣ} (ha : a ≠ 1) {x : G} (hxN : x ∈ Subgroup.normalizer (conjSubgroup V₁ y : Set G))
    (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hxa : SecA.conjV (fsuV T I) x hx =
      ((π (g' * torusHom (Pi.mulSingle 0 a) * g'⁻¹) : ↥(autOn L (fsuV T I))) :
        MulAut ↥(fsuV T I))) :
    mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) =
      Matrix.toBilin' (spJ K) (mat 2 K g *ᵥ vec4 1 0 0 0)
        (mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)) • (mat 2 K g' *ᵥ vec4 0 0 1 0) := by
  set u := mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) with hu
  obtain ⟨w, hw⟩ := hf.surj u
  have h1 : (w : G) ∈ conjSubgroup V₁ y := (mem_conj_iff hf hV₁ hy hγ w).mpr ⟨1, by
    rw [hw, one_smul]⟩
  have h2 : ((SecA.conjV (fsuV T I) x hx w : ↥(fsuV T I)) : G) ∈ conjSubgroup V₁ y := by
    rw [SecA.conjV_apply_coe]
    exact conj_mem_of_mem_normalizer hxN h1
  obtain ⟨μ, hμ⟩ := (mem_conj_iff hf hV₁ hy hγ _).mp h2
  rw [hxa, hf.act4, hw, gconj_mulVec_sp] at hμ
  have h3 := congrArg (fun v => mat 2 K g'⁻¹ *ᵥ v) hμ
  simp only [mat_inv_mulVec, Matrix.mulVec_smul] at h3
  have hv2 : (mat 2 K g'⁻¹ *ᵥ u) (.inr 0) = Matrix.toBilin' (spJ K) (mat 2 K g *ᵥ vec4 1 0 0 0) u
      := by
    rw [← spB_e0 (mat 2 K g'⁻¹ *ᵥ u), ← spB_mat g' (vec4 1 0 0 0) (mat 2 K g'⁻¹ *ᵥ u),
      mat_mulVec_inv, hg']
  have h4 := eq_smul_of_torus ha (hv2 ▸ hβ) h3
  rw [hv2] at h4
  have h5 := congrArg (fun v => mat 2 K g' *ᵥ v) h4
  simp only [mat_mulVec_inv, Matrix.mulVec_smul] at h5
  exact h5

end Coord

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_trv_full {V W : Subgroup G} (ρ : StatedSp 2 K →* MulAut ↥V) {g g' : StatedSp 2 K}
    (hg' : mat 2 K g' *ᵥ vec4 1 0 0 0 = mat 2 K g *ᵥ vec4 1 0 0 0)
    (htrv : ∀ w ∈ W, ∃ hw : w ∈ Subgroup.normalizer (V : Set G), ∃ c : K,
      SecA.conjV V w hw = ρ (trv (mat 2 K g *ᵥ vec4 1 0 0 0) c))
    (hWC : ¬ W ≤ Subgroup.centralizer (V : Set G))
    (hX : ∀ a : Kˣ, ∃ t ∈ Subgroup.normalizer (W : Set G),
      ∃ ht : t ∈ Subgroup.normalizer (V : Set G),
        SecA.conjV V t ht = ρ (g' * torusHom (Pi.mulSingle 0 a) * g'⁻¹)) (c : K) :
    ∃ w ∈ W, ∃ hw : w ∈ Subgroup.normalizer (V : Set G),
      SecA.conjV V w hw = ρ (trv (mat 2 K g *ᵥ vec4 1 0 0 0) c) := by
  obtain ⟨w₀, hw₀, hw₀C⟩ := IsConcreteLE.not_le_iff_exists.mp hWC
  obtain ⟨hw₀V, c₀, hc₀⟩ := htrv w₀ hw₀
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [trv_zero, map_one] at hc₀
    exact hw₀C (mem_centralizer_of_conjV_eq_one hw₀V hc₀)
  by_cases hc : c = 0
  · subst hc
    exact ⟨1, W.one_mem, Subgroup.one_mem _, by rw [trv_zero, map_one, conjV_one]⟩
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (c / c₀)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hr
    exact hr.elim (fun h => hc h) fun h => hc₀0 h
  obtain ⟨t, htW, htV, ht⟩ := hX (Units.mk0 r hr0)
  refine ⟨t * w₀ * t⁻¹, conj_mem_of_mem_normalizer htW hw₀, Subgroup.mul_mem _
    (Subgroup.mul_mem _ htV hw₀V) (Subgroup.inv_mem _ htV), ?_⟩
  rw [conjV_mul3 htV hw₀V (Subgroup.inv_mem _ htV), SecA.conjV_inv _ htV, ht, hc₀, ← map_inv,
    ← map_mul, ← map_mul, trv_conj, gconj_mulVec_sp, ← hg', mat_inv_mulVec, torus_mulVec_e0,
    Matrix.mulVec_smul, Units.val_mk0, trv_smul]
  congr 2
  rw [sq, ← hr, div_mul_cancel₀ c hc₀0]

end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX
