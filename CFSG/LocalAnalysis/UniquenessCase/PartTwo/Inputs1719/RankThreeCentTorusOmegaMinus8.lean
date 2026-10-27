module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusOmegaMinus8
public import CFSG.ClassicalGroups.Orthogonal.MinusLeviBlocks
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaOddOrder
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.LieType.SeitzGeneration.OrthAnisoTorus
public import CFSG.LinearAlgebra.CubeRootBlockSymmetric
public import CFSG.RankThree.CentralCover.HigherClassicalFourGroupWitness
public import CFSG.GroupTheory.DisjointSupCard
public import CFSG.GroupTheory.ZpowersSupExponent

public section

open Matrix CFSG.Open
open CFSG.ComponentClassification.UnbalancingLocal.OrthogonalBlocks
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

namespace CFSG.RankThree.CentralCover

theorem embed3GL_le_refl {F : Type} [Field F] (g : GL (Fin 3) F) :
    embed3GL (le_refl 3) g = g := by
  apply Units.ext
  ext i j
  rw [coe_embed3GL, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hsymm : ∀ i : Fin 3, (finSplit3 (le_refl 3)).symm i = Sum.inl i := by
    intro i
    rw [finSplit3, Equiv.symm_trans_apply, Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
    exact Fin.ext rfl
  rw [hsymm i, hsymm j]
  simp [Matrix.fromBlocks]

end CFSG.RankThree.CentralCover

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

private theorem om_tailQ {F : Type} [Field F] {b c : F} (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    (HypForm.tail 3 (Fin 2) (planeNorm b c)).Q v = StatedQuadMinus 4 F b c v := by
  rw [CFSG.RankThree.CentralCover.tail_Q_eq]
  simp only [StatedQuadMinus, planeNorm, Function.comp_apply]
  ring

private theorem om_y_mem {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (Y : GL (Fin 2) F)
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hodd : Odd (orderOf Y)) :
    planeBlockHom 3 Y ∈ StatedOmega (StatedQuadMinus 4 F b c) := by
  refine CFSG.ClassicalGroups.Orthogonal.mem_statedOmega_quadMinus_of_odd b c hirr _ ?_ ?_
  · intro v
    exact planeBlockHom_isometry Y hY v
  · rw [orderOf_planeBlockHom]
    exact hodd

private noncomputable def omY {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (Y : GL (Fin 2) F)
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hodd : Odd (orderOf Y)) : ↥(StatedOmega (StatedQuadMinus 4 F b c)) :=
  ⟨planeBlockHom 3 Y, om_y_mem hirr Y hY hodd⟩

@[simp] private theorem coe_omY {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (Y : GL (Fin 2) F)
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hodd : Odd (orderOf Y)) :
    ((omY hirr Y hY hodd : ↥(StatedOmega (StatedQuadMinus 4 F b c))) :
        GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) = planeBlockHom 3 Y := rfl

private noncomputable def omD1 (F : Type) [Field F] (ζ : Fˣ) : Fin 3 → Fˣ :=
  fun i => if i = 2 then 1 else ζ

private noncomputable def omD2 (F : Type) [Field F] (ζ : Fˣ) : Fin 3 → Fˣ := Pi.mulSingle 2 ζ

private theorem omD1_pow {F : Type} [Field F] {ζ : Fˣ} {r : ℕ} (hζ : ζ ^ r = 1) :
    ∀ j, omD1 F ζ j ^ r = 1 := by
  intro j
  by_cases hj : j = 2
  · simp [omD1, hj]
  · simp only [omD1, if_neg hj]
    exact hζ

private theorem omD2_pow {F : Type} [Field F] {ζ : Fˣ} {r : ℕ} (hζ : ζ ^ r = 1) :
    ∀ j, omD2 F ζ j ^ r = 1 := by
  intro j
  by_cases hj : j = 2
  · subst hj; simpa [omD2] using hζ
  · rw [omD2, Pi.mulSingle_eq_of_ne hj, one_pow]

private theorem omD1_01 {F : Type} [Field F] (ζ : Fˣ) : omD1 F ζ 0 = omD1 F ζ 1 := by
  simp [omD1]

private theorem omD2_01 {F : Type} [Field F] (ζ : Fˣ) : omD2 F ζ 0 = omD2 F ζ 1 := by
  simp [omD2]

private theorem omD2_0 {F : Type} [Field F] (ζ : Fˣ) : omD2 F ζ 0 = 1 := by simp [omD2]

private theorem omD2_1 {F : Type} [Field F] (ζ : Fˣ) : omD2 F ζ 1 = 1 := by simp [omD2]

private theorem omD1_supp {F : Type} [Field F] {ζ : Fˣ} :
    ∀ j : Fin 3, j ≠ 0 → j ≠ 1 → omD1 F ζ j = 1 := by
  intro j _ _
  have h2 : j = 2 := by revert j; decide
  simp [omD1, h2]

private theorem omD2_supp {F : Type} [Field F] {ζ : Fˣ} :
    ∀ j : Fin 3, j ≠ 2 → j ≠ 0 → omD2 F ζ j = 1 := by
  intro j h2 _
  rw [omD2, Pi.mulSingle_eq_of_ne h2]

private noncomputable def omLevi {F : Type} [Field F] (b c : F) :
    SpecialLinearGroup (Fin 2) F →* ↥(StatedOmega (StatedQuadMinus 4 F b c)) :=
  MonoidHom.codRestrict
    (((HypForm.tail 3 (Fin 2) (planeNorm b c)).rho).comp
      ((padGLHom (K := F)).comp (Matrix.SpecialLinearGroup.toGL)))
    (StatedOmega (StatedQuadMinus 4 F b c))
    (fun g => by
      have hmem := CFSG.RankThree.CentralCover.rho_embed3GL_mem_statedOmega
        (HypForm.tail 3 (Fin 2) (planeNorm b c)) (le_refl 3)
        (fun v => om_tailQ v) (g := padGLHom (Matrix.SpecialLinearGroup.toGL g)) (by
          rw [det_padGLHom]
          simp)
      rwa [CFSG.RankThree.CentralCover.embed3GL_le_refl] at hmem)

@[simp] private theorem coe_omLevi {F : Type} [Field F] (b c : F)
    (g : SpecialLinearGroup (Fin 2) F) :
    ((omLevi b c g : ↥(StatedOmega (StatedQuadMinus 4 F b c))) :
        GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
      (HypForm.tail 3 (Fin 2) (planeNorm b c)).rho
        (padGLHom (Matrix.SpecialLinearGroup.toGL g)) := rfl

private theorem omLevi_injective {F : Type} [Field F] (b c : F) :
    Function.Injective (omLevi (b := b) (c := c)) := by
  intro g h hgh
  have h1 : ((omLevi b c g : ↥(StatedOmega (StatedQuadMinus 4 F b c))) :
      GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
      ((omLevi b c h : ↥(StatedOmega (StatedQuadMinus 4 F b c))) :
        GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) := by rw [hgh]
  rw [coe_omLevi, coe_omLevi] at h1
  exact Matrix.SpecialLinearGroup.toGL_injective
    (padGLHom_injective (CFSG.RankThree.CentralCover.HypForm.rho_injective _ h1))

private theorem orderOf_omLevi {F : Type} [Field F] (b c : F)
    (g : SpecialLinearGroup (Fin 2) F) :
    orderOf (omLevi b c g : ↥(StatedOmega (StatedQuadMinus 4 F b c))) = orderOf g :=
  orderOf_injective (omLevi (b := b) (c := c)) (omLevi_injective b c) g

private theorem exists_plane_rotation {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) :
    ∃ Y : GL (Fin 2) F, (∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z) ∧
      orderOf Y = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨α, β, hdet, hrotpow, hrotne⟩ :=
    CFSG.LieType.SeitzGeneration.exists_rotMat_order (b := b) (c := c) hirr hp hp2 hpq
  let Y : GL (Fin 2) F :=
    Matrix.nonsingInvUnit (CFSG.LieType.SeitzGeneration.rotMat b c α β)
      (by rw [CFSG.LieType.SeitzGeneration.det_rotMat, hdet]; exact isUnit_one)
  have hYcoe : (Y : Matrix (Fin 2) (Fin 2) F) = CFSG.LieType.SeitzGeneration.rotMat b c α β :=
    rfl
  have hYpow : Y ^ p = 1 := by
    apply Units.ext
    change (Y : Matrix (Fin 2) (Fin 2) F) ^ p = 1
    rw [hYcoe]
    exact hrotpow
  have hYne : Y ≠ 1 := by
    intro h
    apply hrotne
    have h1 : (Y : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [h]; rfl
    rwa [hYcoe] at h1
  refine ⟨Y, ?_, orderOf_eq_prime hYpow hYne⟩
  intro z
  have h := CFSG.LieType.SeitzGeneration.rotMat_isom (b := b) (c := c) α β hdet z
  simpa [planeNorm, hYcoe] using h

private theorem orderOf_omY {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (Y : GL (Fin 2) F)
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hodd : Odd (orderOf Y)) :
    orderOf (omY hirr Y hY hodd : ↥(StatedOmega (StatedQuadMinus 4 F b c))) =
      orderOf Y := by
  rw [← Subgroup.orderOf_coe (omY hirr Y hY hodd), coe_omY, orderOf_planeBlockHom]

private noncomputable abbrev omG1 {F : Type} [Field F] {b c : F} {r : ℕ} (hr : Odd r)
    (ζ : Fˣ) (hζ : ζ ^ r = 1) : ↥(StatedOmega (StatedQuadMinus 4 F b c)) :=
  minusDiagGL (b := b) (c := c) (n := 4) hr (omD1 F ζ) (omD1_pow hζ)

private noncomputable abbrev omG2 {F : Type} [Field F] {b c : F} {r : ℕ} (hr : Odd r)
    (ζ : Fˣ) (hζ : ζ ^ r = 1) : ↥(StatedOmega (StatedQuadMinus 4 F b c)) :=
  minusDiagGL (b := b) (c := c) (n := 4) hr (omD2 F ζ) (omD2_pow hζ)

private theorem omG1_pow_eq_one {F : Type} [Field F] {b c : F} {r : ℕ} (hr : Odd r) {ζ : Fˣ}
    (hζ : ζ ^ r = 1) : (omG1 (b := b) (c := c) (r := r) hr ζ hζ) ^ r = 1 :=
  minusDiagGL_pow_eq_one (b := b) (c := c) (n := 4) hr (omD1_pow hζ)

private theorem omG2_pow_eq_one {F : Type} [Field F] {b c : F} {r : ℕ} (hr : Odd r) {ζ : Fˣ}
    (hζ : ζ ^ r = 1) : (omG2 (b := b) (c := c) (r := r) hr ζ hζ) ^ r = 1 :=
  minusDiagGL_pow_eq_one (b := b) (c := c) (n := 4) hr (omD2_pow hζ)

private theorem orderOf_omG1 {F : Type} [Field F] {b c : F} {r : ℕ} [Fact r.Prime] (hr : Odd r)
    {ζ : Fˣ} (hζ : ζ ^ r = 1) (hζne : ζ ≠ 1) :
    orderOf (omG1 (b := b) (c := c) (r := r) hr ζ hζ) = r := by
  refine orderOf_eq_prime (omG1_pow_eq_one hr hζ) ?_
  intro h1
  have h2 := coe_minusDiagGL_apply_inl (b := b) (c := c) (n := 4) (r := r) hr (omD1_pow hζ) 0
  dsimp only [omG1] at h1
  rw [h1] at h2
  simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq] at h2
  exact hζne (Units.ext (by simpa [omD1] using h2.symm))

private theorem orderOf_omG2 {F : Type} [Field F] {b c : F} {r : ℕ} [Fact r.Prime] (hr : Odd r)
    {ζ : Fˣ} (hζ : ζ ^ r = 1) (hζne : ζ ≠ 1) :
    orderOf (omG2 (b := b) (c := c) (r := r) hr ζ hζ) = r := by
  refine orderOf_eq_prime (omG2_pow_eq_one hr hζ) ?_
  intro h1
  have h2 := coe_minusDiagGL_apply_inl (b := b) (c := c) (n := 4) (r := r) hr (omD2_pow hζ) 2
  dsimp only [omG2] at h1
  rw [h1] at h2
  simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq] at h2
  exact hζne (Units.ext (by simpa [omD2] using h2.symm))

private theorem commute_minusDiagGL_omLevi {F : Type} [Field F] {b c : F} {r : ℕ} (hr : Odd r)
    {d : Fin 3 → Fˣ} (hd : ∀ j, d j ^ r = 1) (hd01 : d 0 = d 1)
    (g : SpecialLinearGroup (Fin 2) F) :
    Commute (minusDiagGL (b := b) (c := c) (n := 4) hr d hd) (omLevi b c g) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_minusDiagGL, coe_omLevi]
  exact (commute_diagGL_torusEntMinus_rho_padGLHom (qW := planeNorm b c) d hd01
    (Matrix.SpecialLinearGroup.toGL g)).eq

private theorem commute_minusDiagGL_omY {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    {r : ℕ} (hr : Odd r) {d : Fin 3 → Fˣ} (hd : ∀ j, d j ^ r = 1)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (Y : GL (Fin 2) F)
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hodd : Odd (orderOf Y)) :
    Commute (minusDiagGL (b := b) (c := c) (n := 4) hr d hd) (omY hirr Y hY hodd) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_minusDiagGL, coe_omY]
  exact (planeBlockHom_commute_diagGL (m := 3) d Y).eq

private theorem commute_omLevi_omY {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (g : SpecialLinearGroup (Fin 2) F)
    (Y : GL (Fin 2) F)
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hodd : Odd (orderOf Y)) : Commute (omLevi b c g) (omY hirr Y hY hodd) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_omLevi, coe_omY]
  exact (planeBlockHom_commute_rho (planeNorm b c)
    (padGLHom (Matrix.SpecialLinearGroup.toGL g)) Y).eq

private theorem omLevi_sl2W_conj_inv {F : Type} [Field F] (b c : F)
    {g : SpecialLinearGroup (Fin 2) F}
    (hgsym : (g : Matrix (Fin 2) (Fin 2) F)ᵀ = (g : Matrix (Fin 2) (Fin 2) F)) :
    omLevi b c sl2W * omLevi b c g * (omLevi b c sl2W)⁻¹ = (omLevi b c g)⁻¹ := by
  calc omLevi b c sl2W * omLevi b c g * (omLevi b c sl2W)⁻¹
      = omLevi b c (sl2W * g) * omLevi b c sl2W⁻¹ := by rw [← map_mul, ← map_inv]
    _ = omLevi b c (sl2W * g * sl2W⁻¹) := by rw [← map_mul]
    _ = omLevi b c g⁻¹ := by rw [sl2W_conj_eq_inv_of_transpose hgsym]
    _ = (omLevi b c g)⁻¹ := map_inv ..

private theorem commute_minusPairFlip_omY {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {i k : Fin 3} (hik : i ≠ k) (Y : GL (Fin 2) F)
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hodd : Odd (orderOf Y)) :
    Commute (minusPairFlip (b := b) (c := c) (n := 4) hirr i k hik) (omY hirr Y hY hodd) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_minusPairFlip, coe_omY]
  exact (planeBlockHom_commute_permGL_minusFlip (m := 3) i Y).mul_left
    (planeBlockHom_commute_permGL_minusFlip (m := 3) k Y)

private theorem disjoint_zpowers_diag {F : Type} [Field F] {b c : F} {r : ℕ} (hr : Odd r)
    {ζ : Fˣ} (hζ : ζ ^ r = 1) :
    Disjoint (Subgroup.zpowers (minusDiagGL (b := b) (c := c) (n := 4) hr (omD1 F ζ)
        (omD1_pow hζ)))
      (Subgroup.zpowers (minusDiagGL (b := b) (c := c) (n := 4) hr (omD2 F ζ)
        (omD2_pow hζ))) := by
  rw [disjoint_iff_inf_le]
  intro z hz
  rw [Subgroup.mem_inf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff] at hz
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := hz
  have hentry : (ζ : F) ^ k = 1 := by
    have h1 : ((((minusDiagGL (b := b) (c := c) (n := 4) hr (omD1 F ζ) (omD1_pow hζ)) ^ k :
        ↥(StatedOmega (StatedQuadMinus 4 F b c))) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inl 0) =
        ((((minusDiagGL (b := b) (c := c) (n := 4) hr (omD2 F ζ) (omD2_pow hζ)) ^ l :
          ↥(StatedOmega (StatedQuadMinus 4 F b c))) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
          Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inl 0) := by
      rw [hk, hl]
    rw [coe_minusDiagGL_zpow_apply_inl (n := 4) hr (omD1_pow hζ) k 0,
      coe_minusDiagGL_zpow_apply_inl (n := 4) hr (omD2_pow hζ) l 0] at h1
    simpa [omD1, omD2] using h1
  have hζk : ζ ^ k = 1 := Units.ext (by
    rw [Units.val_zpow_eq_zpow_val, Units.val_one]
    exact hentry)
  have hdk : (omD1 F ζ) ^ k = 1 := by
    funext i
    fin_cases i <;> simp [omD1, Pi.pow_apply, hζk]
  rw [← hk, minusDiagGL_zpow_eq_one (b := b) (c := c) (n := 4) hr (omD1_pow hζ) hdk]
  exact Subgroup.mem_bot.mpr rfl

private theorem disjoint_zpowers_omLevi_omY {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (g : SpecialLinearGroup (Fin 2) F)
    (Y : GL (Fin 2) F)
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hodd : Odd (orderOf Y)) :
    Disjoint (Subgroup.zpowers (omLevi b c g)) (Subgroup.zpowers (omY hirr Y hY hodd)) := by
  rw [disjoint_iff_inf_le]
  intro z hz
  rw [Subgroup.mem_inf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff] at hz
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := hz
  have hYl : Y ^ l = 1 := by
    refine eq_one_of_planeBlockHom_eq_rho (m := 3) (qW := planeNorm b c)
      (g := padGLHom (Matrix.SpecialLinearGroup.toGL (g ^ k))) ?_
    have h1 : ((omLevi b c g ^ k : ↥(StatedOmega (StatedQuadMinus 4 F b c))) :
        GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
        ((omY hirr Y hY hodd ^ l : ↥(StatedOmega (StatedQuadMinus 4 F b c))) :
          GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) := by rw [hk, hl]
    rw [Subgroup.coe_zpow, Subgroup.coe_zpow, coe_omLevi, coe_omY] at h1
    simp only [← map_zpow] at h1
    exact h1.symm
  have hy1 : (omY hirr Y hY hodd) ^ l = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_zpow, Subgroup.coe_one, coe_omY, ← map_zpow, hYl, map_one]
  rw [← hl, hy1]
  exact Subgroup.mem_bot.mpr rfl

private theorem commute_odd_insert_omegaMinus8 {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hrodd : Odd r)
    {ζ : Fˣ} (hζ : ζ ^ r = 1) (hζne : ζ ≠ 1) {g : SpecialLinearGroup (Fin 2) F}
    (hgord : orderOf g = p) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {Y : GL (Fin 2) F}
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hYodd : Odd (orderOf Y)) :
    (∀ a ∈ ({omG1 (b := b) (c := c) (r := r) hrodd ζ hζ,
        omG2 (b := b) (c := c) (r := r) hrodd ζ hζ, omLevi b c g,
        omY hirr Y hY hYodd} : Set ↥(StatedOmega (StatedQuadMinus 4 F b c))),
      ∀ t ∈ ({omG1 (b := b) (c := c) (r := r) hrodd ζ hζ,
        omG2 (b := b) (c := c) (r := r) hrodd ζ hζ, omLevi b c g,
        omY hirr Y hY hYodd} : Set ↥(StatedOmega (StatedQuadMinus 4 F b c))), Commute a t) ∧
      ∀ a ∈ ({omG1 (b := b) (c := c) (r := r) hrodd ζ hζ,
        omG2 (b := b) (c := c) (r := r) hrodd ζ hζ, omLevi b c g,
        omY hirr Y hY hYodd} : Set ↥(StatedOmega (StatedQuadMinus 4 F b c))),
        Odd (orderOf a) := by
  have : Fact r.Prime := ⟨hr⟩
  have hord1 : orderOf (omG1 (b := b) (c := c) (r := r) hrodd ζ hζ) = r :=
    orderOf_omG1 hrodd hζ hζne
  have hord2 : orderOf (omG2 (b := b) (c := c) (r := r) hrodd ζ hζ) = r :=
    orderOf_omG2 hrodd hζ hζne
  have hord3 : orderOf (omLevi b c g) = p := (orderOf_omLevi b c g).trans hgord
  have hcomm12 : Commute (omG1 (b := b) (c := c) (r := r) hrodd ζ hζ)
      (omG2 (b := b) (c := c) (r := r) hrodd ζ hζ) :=
    commute_minusDiagGL (b := b) (c := c) (n := 4) hrodd (omD1 F ζ) (omD2 F ζ)
      (omD1_pow hζ) (omD2_pow hζ)
  have hcomm13 : Commute (omG1 (b := b) (c := c) (r := r) hrodd ζ hζ) (omLevi b c g) :=
    commute_minusDiagGL_omLevi (b := b) (c := c) hrodd (omD1_pow hζ) (omD1_01 ζ) g
  have hcomm14 : Commute (omG1 (b := b) (c := c) (r := r) hrodd ζ hζ)
      (omY hirr Y hY hYodd) :=
    commute_minusDiagGL_omY (b := b) (c := c) hrodd (omD1_pow hζ) hirr Y hY hYodd
  have hcomm23 : Commute (omG2 (b := b) (c := c) (r := r) hrodd ζ hζ) (omLevi b c g) :=
    commute_minusDiagGL_omLevi (b := b) (c := c) hrodd (omD2_pow hζ) (omD2_01 ζ) g
  have hcomm24 : Commute (omG2 (b := b) (c := c) (r := r) hrodd ζ hζ)
      (omY hirr Y hY hYodd) :=
    commute_minusDiagGL_omY (b := b) (c := c) hrodd (omD2_pow hζ) hirr Y hY hYodd
  have hcomm34 : Commute (omLevi b c g) (omY hirr Y hY hYodd) :=
    commute_omLevi_omY hirr g Y hY hYodd
  refine ⟨?_, ?_⟩
  · intro a ha t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ht
    rcases ha with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl
    · exact Commute.refl _
    · exact hcomm12
    · exact hcomm13
    · exact hcomm14
    · exact hcomm12.symm
    · exact Commute.refl _
    · exact hcomm23
    · exact hcomm24
    · exact hcomm13.symm
    · exact hcomm23.symm
    · exact Commute.refl _
    · exact hcomm34
    · exact hcomm14.symm
    · exact hcomm24.symm
    · exact hcomm34.symm
    · exact Commute.refl _
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · rw [hord1]; exact hrodd
    · rw [hord2]; exact hrodd
    · rw [hord3]; exact hp.odd_of_ne_two hp2
    · rw [orderOf_omY hirr Y hY hYodd]; exact hYodd

private theorem minusPairFlip_conj_omegaMinus8 {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} {r : ℕ} (hrodd : Odd r) {ζ : Fˣ} (hζ : ζ ^ r = 1)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h01 : (0 : Fin 3) ≠ 1)
    (h20 : (2 : Fin 3) ≠ 0) {Y : GL (Fin 2) F}
    (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hYodd : Odd (orderOf Y)) :
    (minusPairFlip (b := b) (c := c) (n := 4) hirr 0 1 h01 *
        omG1 (b := b) (c := c) (r := r) hrodd ζ hζ *
        (minusPairFlip (b := b) (c := c) (n := 4) hirr 0 1 h01)⁻¹ =
      (omG1 (b := b) (c := c) (r := r) hrodd ζ hζ)⁻¹) ∧
      (minusPairFlip (b := b) (c := c) (n := 4) hirr 0 1 h01 *
        omG2 (b := b) (c := c) (r := r) hrodd ζ hζ *
        (minusPairFlip (b := b) (c := c) (n := 4) hirr 0 1 h01)⁻¹ =
      omG2 (b := b) (c := c) (r := r) hrodd ζ hζ) ∧
      (minusPairFlip (b := b) (c := c) (n := 4) hirr 0 1 h01 * omY hirr Y hY hYodd *
        (minusPairFlip (b := b) (c := c) (n := 4) hirr 0 1 h01)⁻¹ = omY hirr Y hY hYodd) ∧
      (minusPairFlip (b := b) (c := c) (n := 4) hirr 2 0 h20 *
        omG2 (b := b) (c := c) (r := r) hrodd ζ hζ *
        (minusPairFlip (b := b) (c := c) (n := 4) hirr 2 0 h20)⁻¹ =
      (omG2 (b := b) (c := c) (r := r) hrodd ζ hζ)⁻¹) ∧
      (minusPairFlip (b := b) (c := c) (n := 4) hirr 2 0 h20 * omY hirr Y hY hYodd *
        (minusPairFlip (b := b) (c := c) (n := 4) hirr 2 0 h20)⁻¹ = omY hirr Y hY hYodd) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact minusPairFlip_conj_inv (b := b) (c := c) (n := 4) hirr hrodd (omD1 F ζ) (omD1_pow hζ)
      h01 (fun l => congrFun (torusEntMinus_comp_minusFlip_inv (i := 0) (k := 1) h01
        (fun j hj hk => omD1_supp j hj hk)) l)
  · exact minusPairFlip_conj_eq (b := b) (c := c) (n := 4) hirr hrodd (omD2 F ζ) (omD2_pow hζ)
      h01 (fun l => congrFun (torusEntMinus_comp_minusFlip_eq (i := 0) (k := 1) h01
        (omD2_0 ζ) (omD2_1 ζ)) l)
  · have hc := commute_minusPairFlip_omY (b := b) (c := c) hirr h01 Y hY hYodd
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  · exact minusPairFlip_conj_inv (b := b) (c := c) (n := 4) hirr hrodd (omD2 F ζ) (omD2_pow hζ)
      h20 (fun l => congrFun (torusEntMinus_comp_minusFlip_inv (i := 2) (k := 0) h20
        (fun j hj hk => omD2_supp j hj hk)) l)
  · have hc := commute_minusPairFlip_omY (b := b) (c := c) hirr h20 Y hY hYodd
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem inverter_insert_omegaMinus8 {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} {r : ℕ} (hrodd : Odd r) {ζ : Fˣ} (hζ : ζ ^ r = 1)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {g : SpecialLinearGroup (Fin 2) F}
    (hgsym : (g : Matrix (Fin 2) (Fin 2) F)ᵀ = (g : Matrix (Fin 2) (Fin 2) F))
    {Y : GL (Fin 2) F} (hY : ∀ z : Fin 2 → F, planeNorm b c (Y *ᵥ z) = planeNorm b c z)
    (hYodd : Odd (orderOf Y)) :
    ∀ a ∈ ({omG1 (b := b) (c := c) (r := r) hrodd ζ hζ,
        omG2 (b := b) (c := c) (r := r) hrodd ζ hζ, omLevi b c g,
        omY hirr Y hY hYodd} : Set ↥(StatedOmega (StatedQuadMinus 4 F b c))),
      ∀ t ∈ ({omG1 (b := b) (c := c) (r := r) hrodd ζ hζ,
        omG2 (b := b) (c := c) (r := r) hrodd ζ hζ, omLevi b c g,
        omY hirr Y hY hYodd} : Set ↥(StatedOmega (StatedQuadMinus 4 F b c))), a ≠ t →
        (∃ w : ↥(StatedOmega (StatedQuadMinus 4 F b c)),
            w * a * w⁻¹ = a⁻¹ ∧ w * t * w⁻¹ = t) ∨
          (∃ w : ↥(StatedOmega (StatedQuadMinus 4 F b c)),
            w * t * w⁻¹ = t⁻¹ ∧ w * a * w⁻¹ = a) := by
  classical
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  obtain ⟨hflip01_g1, hflip01_g2, hflip01_y, hflip20_g2, hflip20_y⟩ :=
    minusPairFlip_conj_omegaMinus8 (b := b) (c := c) hrodd hζ hirr h01 h20 hY hYodd
  let w01 := minusPairFlip (b := b) (c := c) (n := 4) hirr 0 1 h01
  let w20 := minusPairFlip (b := b) (c := c) (n := 4) hirr 2 0 h20
  let wS := omLevi b c (sl2W : SpecialLinearGroup (Fin 2) F)
  have hSx : wS * omLevi b c g * wS⁻¹ = (omLevi b c g)⁻¹ := omLevi_sl2W_conj_inv b c hgsym
  have hSg1 : wS * omG1 (b := b) (c := c) (r := r) hrodd ζ hζ * wS⁻¹ =
      omG1 (b := b) (c := c) (r := r) hrodd ζ hζ := by
    have hc := (commute_minusDiagGL_omLevi (b := b) (c := c) hrodd (omD1_pow hζ)
      (omD1_01 ζ) (sl2W : SpecialLinearGroup (Fin 2) F)).symm
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hSg2 : wS * omG2 (b := b) (c := c) (r := r) hrodd ζ hζ * wS⁻¹ =
      omG2 (b := b) (c := c) (r := r) hrodd ζ hζ := by
    have hc := (commute_minusDiagGL_omLevi (b := b) (c := c) hrodd (omD2_pow hζ)
      (omD2_01 ζ) (sl2W : SpecialLinearGroup (Fin 2) F)).symm
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hSy : wS * omY hirr Y hY hYodd * wS⁻¹ = omY hirr Y hY hYodd := by
    have hc := commute_omLevi_omY hirr (sl2W : SpecialLinearGroup (Fin 2) F) Y hY hYodd
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  intro a ha t ht hat
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ht
  rcases ha with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl
  · exact absurd rfl hat
  · exact Or.inl ⟨w01, hflip01_g1, hflip01_g2⟩
  · exact Or.inr ⟨wS, hSx, hSg1⟩
  · exact Or.inl ⟨w01, hflip01_g1, hflip01_y⟩
  · exact Or.inr ⟨w01, hflip01_g1, hflip01_g2⟩
  · exact absurd rfl hat
  · exact Or.inr ⟨wS, hSx, hSg2⟩
  · exact Or.inl ⟨w20, hflip20_g2, hflip20_y⟩
  · exact Or.inl ⟨wS, hSx, hSg1⟩
  · exact Or.inl ⟨wS, hSx, hSg2⟩
  · exact absurd rfl hat
  · exact Or.inl ⟨wS, hSx, hSy⟩
  · exact Or.inr ⟨w01, hflip01_g1, hflip01_y⟩
  · exact Or.inr ⟨w20, hflip20_g2, hflip20_y⟩
  · exact Or.inr ⟨wS, hSx, hSy⟩
  · exact absurd rfl hat

private theorem exists_torus_centralizer_omegaMinus8 {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hq3 : Nat.card F % 3 = 2) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ Nat.card F - 1) :
    ∃ (S : Set ↥(StatedOmega (StatedQuadMinus 4 F b c)))
      (D E : Subgroup ↥(StatedOmega (StatedQuadMinus 4 F b c))),
      (∀ s ∈ S, ∀ t ∈ S, Commute s t) ∧ (∀ s ∈ S, Odd (orderOf s)) ∧
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t →
        (∃ w : ↥(StatedOmega (StatedQuadMinus 4 F b c)),
            w * s * w⁻¹ = s⁻¹ ∧ w * t * w⁻¹ = t) ∨
          (∃ w : ↥(StatedOmega (StatedQuadMinus 4 F b c)),
            w * t * w⁻¹ = t⁻¹ ∧ w * s * w⁻¹ = s)) ∧
      D ⊔ E ≤ Subgroup.closure S ∧ (∀ z ∈ D, z ^ r = 1) ∧ (∀ z ∈ E, z ^ p = 1) ∧
      r ^ 2 ≤ Nat.card D ∧ p ^ 2 ≤ Nat.card E := by
  classical
  have hr2 : r ≠ 2 := by omega
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by rwa [Nat.card_units])
  have hζr : ζ ^ r = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζne : ζ ≠ 1 := fun h => by rw [h, orderOf_one] at hζ; omega
  obtain ⟨g, hgsym, hgord⟩ :=
    CFSG.LinearAlgebra.exists_symmetric_sl2_orderOf_eq hp hp2 hpq hq3
  obtain ⟨Y, hYisom, hYord⟩ := exists_plane_rotation (b := b) hirr hp hp2 hpq
  have hYodd : Odd (orderOf Y) := by rw [hYord]; exact hp.odd_of_ne_two hp2
  let g1 := omG1 (b := b) (c := c) (r := r) hrodd ζ hζr
  let g2 := omG2 (b := b) (c := c) (r := r) hrodd ζ hζr
  let x := omLevi b c g
  let y := omY hirr Y hYisom hYodd
  have hord1 : orderOf g1 = r := orderOf_omG1 hrodd hζr hζne
  have hord2 : orderOf g2 = r := orderOf_omG2 hrodd hζr hζne
  have hord3 : orderOf x = p := (orderOf_omLevi b c g).trans hgord
  have hord4 : orderOf y = p := (orderOf_omY hirr Y hYisom hYodd).trans hYord
  have hS := commute_odd_insert_omegaMinus8 (b := b) (c := c) hp hp2 hr hrodd hζr hζne hgord
    hirr hYisom hYodd
  have hinv := inverter_insert_omegaMinus8 (b := b) (c := c) hrodd hζr hirr hgsym hYisom hYodd
  have hcomm12 : Commute g1 g2 := hS.1 g1 (by simp [g1]) g2 (by simp [g2])
  have hcomm34 : Commute x y := hS.1 x (by simp [x]) y (by simp [y])
  have hdisj12 := disjoint_zpowers_diag (b := b) (c := c) hrodd hζr
  have hdisj34 := disjoint_zpowers_omLevi_omY (b := b) (c := c) hirr g Y hYisom hYodd
  have hDr : ∀ z ∈ Subgroup.zpowers g1 ⊔ Subgroup.zpowers g2, z ^ r = 1 := fun z hz =>
    CFSG.GroupTheory.pow_eq_one_of_mem_zpowers_sup hcomm12 (by rw [hord1]) (by rw [hord2]) hz
  have hEp : ∀ z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, z ^ p = 1 := fun z hz =>
    CFSG.GroupTheory.pow_eq_one_of_mem_zpowers_sup hcomm34 (by rw [hord3]) (by rw [hord4]) hz
  have hDcard : r ^ 2 ≤ Nat.card ↥(Subgroup.zpowers g1 ⊔ Subgroup.zpowers g2) := by
    rw [show r ^ 2 = Nat.card (Subgroup.zpowers g1) * Nat.card (Subgroup.zpowers g2) by
      rw [Nat.card_zpowers, Nat.card_zpowers, hord1, hord2, pow_two]]
    exact CFSG.GroupTheory.card_mul_card_le_card_sup_of_disjoint hdisj12
  have hEcard : p ^ 2 ≤ Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
    rw [show p ^ 2 = Nat.card (Subgroup.zpowers x) * Nat.card (Subgroup.zpowers y) by
      rw [Nat.card_zpowers, Nat.card_zpowers, hord3, hord4, pow_two]]
    exact CFSG.GroupTheory.card_mul_card_le_card_sup_of_disjoint hdisj34
  have hDEle : Subgroup.zpowers g1 ⊔ Subgroup.zpowers g2 ⊔
      (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤
      Subgroup.closure ({g1, g2, x, y} : Set ↥(StatedOmega (StatedQuadMinus 4 F b c))) := by
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;>
      rw [Subgroup.zpowers_le] <;> exact Subgroup.subset_closure (by simp)
  exact ⟨{g1, g2, x, y}, Subgroup.zpowers g1 ⊔ Subgroup.zpowers g2,
    Subgroup.zpowers x ⊔ Subgroup.zpowers y, hS.1, hS.2, hinv, hDEle, hDr, hEp, hDcard,
    hEcard⟩

theorem k_RankThreeCentTorus_omegaMinus8 :
    ∀ (K : Type) [Group K] [Finite K] (f p r : ℕ),
      CFSG.Open.StatedLieAdmissible .POmegaMinus 4 2 f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaMinus 4 2 f →
          CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) → Odd f →
            p.Prime → p ≠ 2 → p ∣ 2 ^ f + 1 → r.Prime → 5 ≤ r → r ∣ 2 ^ f - 1 →
              ∃ E : Subgroup K, CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
                2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Subgroup.centralizer (E : Set K))) := by
  intro K _ _ f p r hAdm hK hQ hOddC hf hp hp2 hpdvd hr hr5 hrdvd
  obtain ⟨F, hF, hFin, hFcard, b, c, hirr, φ, hφ, hker⟩ := exists_cover_omegaMinus8 hK
  let := hF
  let := hFin
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hFcard])
  have hpq : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hpdvd
  have hrq : r ∣ Nat.card F - 1 := by rw [hFcard]; exact hrdvd
  have hq3 : Nat.card F % 3 = 2 := by rw [hFcard]; exact CFSG.two_pow_mod_three_of_odd hf
  have hr2 : r ≠ 2 := by omega
  obtain ⟨S, D, E, hScomm, hSodd, hSinv, hDEle, hDr, hEp, hDcard, hEcard⟩ :=
    exists_torus_centralizer_omegaMinus8 (F := F) hirr hp hp2 hpq hq3 hr hr5 hrq
  have hcommS := CFSG.GroupTheory.comap_closure_comm_of_inverters (φ := φ) hφ hker
    hScomm hSodd hSinv
  have hc : ∀ x ∈ (D ⊔ E).comap φ, ∀ y ∈ (D ⊔ E).comap φ, x * y = y * x := fun x hx y hy =>
    hcommS x (Subgroup.comap_mono hDEle hx) y (Subgroup.comap_mono hDEle hy)
  exact CFSG.GroupTheory.exists_elemAbelian_le_pRank_centralizer_of_comap_comm
    (φ := φ) hφ hker hr hr2 hp hp2 hDr hEp hc (a := 2) (b := 2) hDcard hEcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
