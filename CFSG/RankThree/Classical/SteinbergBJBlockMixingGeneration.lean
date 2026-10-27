module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.RankThree.Classical

open Module

variable {K : Type*} [Field K] {U V : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V]
  [Module K V]

@[expose] def blockUpper (B : V →ₗ[K] U) : (U × V) ≃ₗ[K] (U × V) where
  toFun p := (p.1 + B p.2, p.2)
  invFun p := (p.1 - B p.2, p.2)
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
    abel_nf
  map_smul' c p := by simp
  left_inv p := by simp
  right_inv p := by simp

@[expose] def blockLower (C : U →ₗ[K] V) : (U × V) ≃ₗ[K] (U × V) where
  toFun p := (p.1, p.2 + C p.1)
  invFun p := (p.1, p.2 - C p.1)
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
    abel_nf
  map_smul' c p := by simp
  left_inv p := by simp
  right_inv p := by simp

theorem blockUpper_apply (B : V →ₗ[K] U) (p : U × V) : blockUpper B p = (p.1 + B p.2, p.2) :=
  rfl

theorem blockLower_apply (C : U →ₗ[K] V) (p : U × V) : blockLower C p = (p.1, p.2 + C p.1) :=
  rfl

theorem blockUpper_add (B B' : V →ₗ[K] U) : blockUpper (B + B') = blockUpper B * blockUpper B' := by
  ext p <;> simp [blockUpper_apply, LinearEquiv.mul_apply, add_assoc, add_comm (B p.2)]

theorem blockLower_add (C C' : U →ₗ[K] V) : blockLower (C + C') = blockLower C * blockLower C' := by
  ext p <;> simp [blockLower_apply, LinearEquiv.mul_apply, add_assoc, add_comm (C p.1)]

theorem blockUpper_zero : blockUpper (0 : V →ₗ[K] U) = 1 := by
  ext p <;> simp [blockUpper_apply]

theorem blockLower_zero : blockLower (0 : U →ₗ[K] V) = 1 := by
  ext p <;> simp [blockLower_apply]

theorem blockUpper_neg (B : V →ₗ[K] U) : blockUpper (-B) = (blockUpper B)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← blockUpper_add, neg_add_cancel, blockUpper_zero]

theorem blockLower_neg (C : U →ₗ[K] V) : blockLower (-C) = (blockLower C)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← blockLower_add, neg_add_cancel, blockLower_zero]

theorem conj_left_blockUpper (g : U ≃ₗ[K] U) (D : V →ₗ[K] U) :
    g.prodCongr (LinearEquiv.refl K V) * blockUpper D * (g.prodCongr (LinearEquiv.refl K V))⁻¹ =
      blockUpper ((g : U →ₗ[K] U) ∘ₗ D) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext p <;> simp [blockUpper_apply, LinearEquiv.mul_apply]

theorem conj_right_blockUpper (h : V ≃ₗ[K] V) (D : V →ₗ[K] U) :
    (LinearEquiv.refl K U).prodCongr h * blockUpper D * ((LinearEquiv.refl K U).prodCongr h)⁻¹ =
      blockUpper (D ∘ₗ (h.symm : V →ₗ[K] V)) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext p <;> simp [blockUpper_apply, LinearEquiv.mul_apply]

theorem conj_right_blockLower (h : V ≃ₗ[K] V) (C : U →ₗ[K] V) :
    (LinearEquiv.refl K U).prodCongr h * blockLower C * ((LinearEquiv.refl K U).prodCongr h)⁻¹ =
      blockLower ((h : V →ₗ[K] V) ∘ₗ C) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext p <;> simp [blockLower_apply, LinearEquiv.mul_apply]

theorem conj_left_blockLower (g : U ≃ₗ[K] U) (C : U →ₗ[K] V) :
    g.prodCongr (LinearEquiv.refl K V) * blockLower C * (g.prodCongr (LinearEquiv.refl K V))⁻¹ =
      blockLower (C ∘ₗ (g.symm : U →ₗ[K] U)) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext p <;> simp [blockLower_apply, LinearEquiv.mul_apply]

section RankOne

variable {ι κ : Type*}

@[expose] noncomputable def basisRankOne (bU : Basis ι K U) (bV : Basis κ K V) (k : ι) (l : κ) :
    V →ₗ[K] U :=
  (bV.coord l).smulRight (bU k)

theorem basisRankOne_apply (bU : Basis ι K U) (bV : Basis κ K V) (k : ι) (l : κ) (y : V) :
    basisRankOne bU bV k l y = bV.coord l y • bU k :=
  rfl

theorem smul_basisRankOne_mem_of_ne_bot [Nontrivial ι] [Nontrivial κ] (bU : Basis ι K U)
    (bV : Basis κ K V) (M : AddSubgroup (V →ₗ[K] U))
    (hL : ∀ D ∈ M, ∀ i i' : ι, i ≠ i' → basisRankOne bU bU i i' ∘ₗ D ∈ M)
    (hR : ∀ D ∈ M, ∀ j j' : κ, j ≠ j' → ∀ c : K, c • (D ∘ₗ basisRankOne bV bV j j') ∈ M)
    (hne : M ≠ ⊥) (k : ι) (l : κ) (c : K) : c • basisRankOne bU bV k l ∈ M := by
  obtain ⟨⟨D, hD⟩, hD0'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hne
  have hD0 : D ≠ 0 := fun h0 => hD0' (Subtype.ext h0)
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, D (bV j₀) ≠ 0 := by
    by_contra h
    push Not at h
    exact hD0 (bV.ext fun j => by rw [h j, LinearMap.zero_apply])
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, bU.coord i₀ (D (bV j₀)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hj₀ (bU.ext_elem fun i => by rw [← Basis.coord_apply, h i, map_zero, Finsupp.zero_apply])
  set β := bU.coord i₀ (D (bV j₀)) with hβ
  obtain ⟨i, hi⟩ := exists_ne i₀
  obtain ⟨j', hj'⟩ := exists_ne j₀
  have h1 : ∀ e : K, e • basisRankOne bU bV i j' ∈ M := by
    intro e
    have h := hR _ (hL D hD i i₀ hi) j₀ j' hj'.symm (e / β)
    convert h using 1
    ext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, basisRankOne_apply, map_smul,
      LinearMap.smul_apply, smul_smul, Basis.coord_apply]
    have hβ' : (bU.repr (D (bV j₀))) i₀ = β := rfl
    rw [hβ']
    congr 1
    field_simp
  have h2 : ∀ (k : ι) (e : K), e • basisRankOne bU bV k j' ∈ M := by
    intro k e
    by_cases hk : k = i
    · rw [hk]
      exact h1 e
    · convert hL _ (h1 e) k i hk using 1
      ext y
      simp [basisRankOne_apply, Basis.coord_apply]
  by_cases hl : l = j'
  · rw [hl]
    exact h2 k c
  · convert hR _ (h2 k c) j' l (Ne.symm hl) 1 using 1
    ext y
    simp [basisRankOne_apply, Basis.coord_apply]

end RankOne

section Matrices

variable {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def slAction (b : Basis ι K W) :
    Matrix.SpecialLinearGroup ι K →* (W ≃ₗ[K] W) where
  toFun A := Matrix.toLinearEquiv b A (by rw [A.2]; exact isUnit_one)
  map_one' := LinearEquiv.ext fun x => by
    rw [Matrix.toLinearEquiv_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin_one]
    rfl
  map_mul' A B := LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply, Matrix.toLinearEquiv_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLinearEquiv_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin_mul b b b]
    rfl

theorem slAction_apply (b : Basis ι K W) (A : Matrix.SpecialLinearGroup ι K) (x : W) :
    slAction b A x = Matrix.toLin b b (A : Matrix ι ι K) x :=
  rfl

theorem slAction_transvection_apply (b : Basis ι K W) {i j : ι} (hij : i ≠ j) (c : K) (x : W) :
    slAction b (Matrix.SpecialLinearGroup.transvection hij c) x =
      x + (c * b.coord j x) • b i := by
  rw [slAction_apply, Matrix.SpecialLinearGroup.transvection_coe, map_add, LinearMap.add_apply,
    Matrix.toLin_one, LinearMap.id_apply, Matrix.toLin_apply, Matrix.single_mulVec]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [Function.update_self, Basis.coord_apply]
  · intro k _ hk
    rw [Function.update_of_ne hk, Pi.zero_apply, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem exists_slAction_eq (b : Basis ι K W) {g : W ≃ₗ[K] W} (hg : LinearEquiv.det g = 1) :
    ∃ A : Matrix.SpecialLinearGroup ι K, slAction b A = g := by
  have hdet : (LinearMap.toMatrix b b (g : W →ₗ[K] W)).det = 1 := by
    rw [LinearMap.det_toMatrix, ← LinearEquiv.coe_det, hg, Units.val_one]
  refine ⟨(⟨_, hdet⟩ : Matrix.SpecialLinearGroup ι K), LinearEquiv.ext fun x => ?_⟩
  change Matrix.toLin b b (LinearMap.toMatrix b b (g : W →ₗ[K] W)) x = g x
  rw [Matrix.toLin_toMatrix]
  rfl

theorem mem_of_det_eq_one_of_transvection_mem (b : Basis ι K W) (H : Subgroup (W ≃ₗ[K] W))
    (hH : ∀ (i j : ι) (hij : i ≠ j) (c : K),
      slAction b (Matrix.SpecialLinearGroup.transvection hij c) ∈ H)
    {g : W ≃ₗ[K] W} (hg : LinearEquiv.det g = 1) : g ∈ H := by
  obtain ⟨A, rfl⟩ := exists_slAction_eq b hg
  have hA : A ∈ H.comap (slAction b) := by
    have htop : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct ι K → Matrix.SpecialLinearGroup ι K)) ≤ H.comap (slAction b) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨t, rfl⟩
      exact hH t.i t.j t.hij t.c
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at htop
    exact htop (Subgroup.mem_top A)
  exact hA

end Matrices

section Theorem

variable {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*}

theorem coord_self_ne (b : Basis ι K W) {i i' : ι} (h : i ≠ i') (c : K) :
    (c • b.coord i') (b i) = 0 := by
  rw [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne' h,
    smul_zero]

theorem linearMap_det_transvection {f : Module.Dual K W} {v : W} (hf : f v = 0) :
    LinearMap.det (LinearEquiv.transvection hf : W →ₗ[K] W) = 1 := by
  rw [← LinearEquiv.coe_det, LinearEquiv.transvection.det_eq_one hf, Units.val_one]

theorem linearMap_det_transvection_symm {f : Module.Dual K W} {v : W} (hf : f v = 0) :
    LinearMap.det ((LinearEquiv.transvection hf).symm : W →ₗ[K] W) = 1 := by
  rw [← LinearEquiv.coe_det, LinearEquiv.det_symm, map_inv, LinearEquiv.transvection.det_eq_one hf,
    inv_one, Units.val_one]

end Theorem

theorem special_linear_two_block_mixing_unipotents_generate [FiniteDimensional K U]
    [FiniteDimensional K V] (hU : 2 ≤ Module.finrank K U) (hV : 2 ≤ Module.finrank K V)
    (H : Subgroup ((U × V) ≃ₗ[K] (U × V)))
    (hSL : ∀ h ∈ H, LinearMap.det (h : (U × V) →ₗ[K] (U × V)) = 1)
    (hSLU : ∀ g : U ≃ₗ[K] U, LinearMap.det (g : U →ₗ[K] U) = 1 →
      g.prodCongr (LinearEquiv.refl K V) ∈ H)
    (hSLV : ∀ g : V ≃ₗ[K] V, LinearMap.det (g : V →ₗ[K] V) = 1 →
      (LinearEquiv.refl K U).prodCongr g ∈ H)
    {B : V →ₗ[K] U} (hB : B ≠ 0) (huB : blockUpper B ∈ H)
    {C : U →ₗ[K] V} (hC : C ≠ 0) (hlC : blockLower C ∈ H) :
    ∀ g : (U × V) ≃ₗ[K] (U × V), g ∈ H ↔ LinearMap.det (g : (U × V) →ₗ[K] (U × V)) = 1 := by
  classical
  intro g
  refine ⟨hSL g, fun hg => ?_⟩
  set bU := Module.finBasis K U with hbU
  set bV := Module.finBasis K V with hbV
  have : Nontrivial (Fin (Module.finrank K U)) := Fin.nontrivial_iff_two_le.mpr hU
  have : Nontrivial (Fin (Module.finrank K V)) := Fin.nontrivial_iff_two_le.mpr hV
  let Mup : AddSubgroup (V →ₗ[K] U) :=
    { carrier := {D | blockUpper D ∈ H}
      add_mem' := fun {D E} hD hE => by
        change blockUpper (D + E) ∈ H
        rw [blockUpper_add]
        exact mul_mem hD hE
      zero_mem' := by
        change blockUpper 0 ∈ H
        rw [blockUpper_zero]
        exact one_mem H
      neg_mem' := fun {D} hD => by
        change blockUpper (-D) ∈ H
        rw [blockUpper_neg]
        exact inv_mem hD }
  let Mlow : AddSubgroup (U →ₗ[K] V) :=
    { carrier := {D | blockLower D ∈ H}
      add_mem' := fun {D E} hD hE => by
        change blockLower (D + E) ∈ H
        rw [blockLower_add]
        exact mul_mem hD hE
      zero_mem' := by
        change blockLower 0 ∈ H
        rw [blockLower_zero]
        exact one_mem H
      neg_mem' := fun {D} hD => by
        change blockLower (-D) ∈ H
        rw [blockLower_neg]
        exact inv_mem hD }
  have hmemUp : ∀ D, D ∈ Mup ↔ blockUpper D ∈ H := fun D => Iff.rfl
  have hmemLow : ∀ D, D ∈ Mlow ↔ blockLower D ∈ H := fun D => Iff.rfl
  have hLup : ∀ D ∈ Mup, ∀ i i', i ≠ i' → basisRankOne bU bU i i' ∘ₗ D ∈ Mup := by
    intro D hD i i' hii'
    have hf := coord_self_ne bU hii' 1
    rw [one_smul] at hf
    have ht := hSLU _ (linearMap_det_transvection hf)
    have h1 : blockUpper ((LinearEquiv.transvection hf : U →ₗ[K] U) ∘ₗ D) ∈ H := by
      rw [← conj_left_blockUpper]
      exact mul_mem (mul_mem ht hD) (inv_mem ht)
    have h2 : basisRankOne bU bU i i' ∘ₗ D =
        (LinearEquiv.transvection hf : U →ₗ[K] U) ∘ₗ D + -D := by
      ext y
      simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.transvection.apply, basisRankOne_apply]
      abel
    rw [h2]
    exact Mup.add_mem h1 (Mup.neg_mem hD)
  have hRup : ∀ D ∈ Mup, ∀ j j', j ≠ j' → ∀ c : K, c • (D ∘ₗ basisRankOne bV bV j j') ∈ Mup := by
    intro D hD j j' hjj' c
    have hf := coord_self_ne bV hjj' c
    have ht := hSLV _ (linearMap_det_transvection_symm hf)
    have h1 : blockUpper (D ∘ₗ (LinearEquiv.transvection hf : V →ₗ[K] V)) ∈ H := by
      have := conj_right_blockUpper (LinearEquiv.transvection hf).symm D
      rw [LinearEquiv.symm_symm] at this
      rw [← this]
      exact mul_mem (mul_mem ht hD) (inv_mem ht)
    have h2 : c • (D ∘ₗ basisRankOne bV bV j j') =
        D ∘ₗ (LinearEquiv.transvection hf : V →ₗ[K] V) + -D := by
      ext y
      simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.transvection.apply,
        basisRankOne_apply,
        map_add, map_smul, smul_smul]
      abel
    rw [h2]
    exact Mup.add_mem h1 (Mup.neg_mem hD)
  have hLlow : ∀ D ∈ Mlow, ∀ j j', j ≠ j' → basisRankOne bV bV j j' ∘ₗ D ∈ Mlow := by
    intro D hD j j' hjj'
    have hf := coord_self_ne bV hjj' 1
    rw [one_smul] at hf
    have ht := hSLV _ (linearMap_det_transvection hf)
    have h1 : blockLower ((LinearEquiv.transvection hf : V →ₗ[K] V) ∘ₗ D) ∈ H := by
      rw [← conj_right_blockLower]
      exact mul_mem (mul_mem ht hD) (inv_mem ht)
    have h2 : basisRankOne bV bV j j' ∘ₗ D =
        (LinearEquiv.transvection hf : V →ₗ[K] V) ∘ₗ D + -D := by
      ext y
      simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.transvection.apply, basisRankOne_apply]
      abel
    rw [h2]
    exact Mlow.add_mem h1 (Mlow.neg_mem hD)
  have hRlow : ∀ D ∈ Mlow, ∀ i i', i ≠ i' → ∀ c : K, c • (D ∘ₗ basisRankOne bU bU i i') ∈ Mlow := by
    intro D hD i i' hii' c
    have hf := coord_self_ne bU hii' c
    have ht := hSLU _ (linearMap_det_transvection_symm hf)
    have h1 : blockLower (D ∘ₗ (LinearEquiv.transvection hf : U →ₗ[K] U)) ∈ H := by
      have := conj_left_blockLower (LinearEquiv.transvection hf).symm D
      rw [LinearEquiv.symm_symm] at this
      rw [← this]
      exact mul_mem (mul_mem ht hD) (inv_mem ht)
    have h2 : c • (D ∘ₗ basisRankOne bU bU i i') =
        D ∘ₗ (LinearEquiv.transvection hf : U →ₗ[K] U) + -D := by
      ext y
      simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.transvection.apply,
        basisRankOne_apply,
        map_add, map_smul, smul_smul]
      abel
    rw [h2]
    exact Mlow.add_mem h1 (Mlow.neg_mem hD)
  have hupNe : Mup ≠ ⊥ := fun h => hB (by
    have : B ∈ Mup := huB
    rw [h, AddSubgroup.mem_bot] at this
    exact this)
  have hlowNe : Mlow ≠ ⊥ := fun h => hC (by
    have : C ∈ Mlow := hlC
    rw [h, AddSubgroup.mem_bot] at this
    exact this)
  have hallUp := smul_basisRankOne_mem_of_ne_bot bU bV Mup hLup hRup hupNe
  have hallLow := smul_basisRankOne_mem_of_ne_bot bV bU Mlow hLlow hRlow hlowNe
  set bW := bU.prod bV with hbW
  have hg' : LinearEquiv.det g = 1 := Units.ext (by rw [LinearEquiv.coe_det, hg, Units.val_one])
  refine mem_of_det_eq_one_of_transvection_mem bW H ?_ hg'
  intro i j hij c
  have happ := slAction_transvection_apply bW hij c
  rcases i with i | i <;> rcases j with j | j
  · have hij' : i ≠ j := fun h => hij (congrArg Sum.inl h)
    have hf := coord_self_ne bU hij' c
    have e : slAction bW (Matrix.SpecialLinearGroup.transvection hij c) =
        (LinearEquiv.transvection hf).prodCongr (LinearEquiv.refl K V) := by
      ext p
      · rw [happ]
        simp [hbW, Basis.coord_apply, LinearMap.transvection.apply]
      · rw [happ]
        simp [hbW]
    rw [e]
    exact hSLU _ (linearMap_det_transvection hf)
  · have e : slAction bW (Matrix.SpecialLinearGroup.transvection hij c) =
        blockUpper (c • basisRankOne bU bV i j) := by
      ext p
      · rw [happ]
        simp [hbW, Basis.coord_apply, blockUpper_apply, basisRankOne_apply, smul_smul]
      · rw [happ]
        simp [hbW, blockUpper_apply]
    rw [e]
    exact hallUp i j c
  · have e : slAction bW (Matrix.SpecialLinearGroup.transvection hij c) =
        blockLower (c • basisRankOne bV bU i j) := by
      ext p
      · rw [happ]
        simp [hbW, blockLower_apply]
      · rw [happ]
        simp [hbW, Basis.coord_apply, blockLower_apply, basisRankOne_apply, smul_smul]
    rw [e]
    exact hallLow i j c
  · have hij' : i ≠ j := fun h => hij (congrArg Sum.inr h)
    have hf := coord_self_ne bV hij' c
    have e : slAction bW (Matrix.SpecialLinearGroup.transvection hij c) =
        (LinearEquiv.refl K U).prodCongr (LinearEquiv.transvection hf) := by
      ext p
      · rw [happ]
        simp [hbW]
      · rw [happ]
        simp [hbW, Basis.coord_apply, LinearMap.transvection.apply]
    rw [e]
    exact hSLV _ (linearMap_det_transvection hf)

end CFSG.RankThree.Classical
