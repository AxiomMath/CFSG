module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3Sub
public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification
open scoped commutatorElement

variable {K : Type} [Field K]

abbrev preH (H : Subgroup (projectiveSL 3 K)) : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  H.comap (proj 3 K)

abbrev commH (H : Subgroup (projectiveSL 3 K)) : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  ⁅preH H, preH H⁆

theorem map_commH {H : Subgroup (projectiveSL 3 K)} (hperf : ⁅H, H⁆ = H) :
    (commH H).map (proj 3 K) = H := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 K),
    hperf]

theorem eq_of_mem_commH {H : Subgroup (projectiveSL 3 K)}
    (ψ : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K)
    (hψ : ∀ x ∈ preH H, proj 3 K (ψ x) = proj 3 K x) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ commH H) : ψ g = g := by
  have hc : ∀ x ∈ preH H, ∃ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), ψ x = x * z := by
    intro x hx
    have h := proj_eq_proj_iff.mp (hψ x hx).symm
    rw [scalars_eq_center] at h
    exact ⟨_, h, by group⟩
  have hgen : commH H ≤ MonoidHom.eqLocus ψ (MonoidHom.id _) := by
    rw [commH, Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨z, hz, hxz⟩ := hc x hx
    obtain ⟨w, hw, hyw⟩ := hc y hy
    change ψ ⁅x, y⁆ = ⁅x, y⁆
    rw [map_commutatorElement, hxz, hyw, commutatorElement_def, commutatorElement_def]
    have hz' := Subgroup.mem_center_iff.mp hz
    have hw' := Subgroup.mem_center_iff.mp hw
    have e2 : z * (y * w) * z⁻¹ = y * w := by
      rw [← hz' (y * w)]
      group
    have e3 : w * x⁻¹ * w⁻¹ = x⁻¹ := by
      rw [← hw' x⁻¹]
      group
    calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
        = x * (z * (y * w) * z⁻¹) * x⁻¹ * (y * w)⁻¹ := by group
      _ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by rw [e2]; group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [e3]
  exact hgen hg

theorem liftInv_of_commH_inv {H : Subgroup (projectiveSL 3 K)} (hperf : ⁅H, H⁆ = H)
    {W : Submodule K (Fin 3 → K)}
    (hW : ∀ g ∈ commH H, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) : LiftInv H W := by
  intro x hx w hw
  have hxG : proj 3 K x ∈ (commH H).map (proj 3 K) := by
    rw [map_commH hperf]
    exact hx
  obtain ⟨g, hg, hgx⟩ := hxG
  have hz : g⁻¹ * x ∈ scalars 3 K := proj_eq_proj_iff.mp hgx
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hz
  have hx' : (x : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
    calc (x : Matrix (Fin 3) (Fin 3) K)
        = ((g * (g⁻¹ * x) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [mul_inv_cancel_left]
      _ = (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ * x : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := Matrix.SpecialLinearGroup.coe_mul _ _
      _ = _ := by rw [hc]
  have hsc : (scalar (Fin 3) (c : K)) *ᵥ w = (c : K) • w := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [hx', ← mulVec_mulVec, hsc, mulVec_smul]
  exact W.smul_mem _ (hW g hg w hw)

theorem commH_irred [Finite K] [CharP K 2] {H : Subgroup (projectiveSL 3 K)}
    (hH : HasOrderFourMod H) (hperf : ⁅H, H⁆ = H) (W : Submodule K (Fin 3 → K))
    (hW : ∀ g ∈ commH H, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ :=
  liftInv_eq_bot_or_eq_top hH (liftInv_of_commH_inv hperf hW)

theorem exists_ne_comm {G' : Type*} [Group G'] {H : Subgroup G'} (hH : HasOrderFourMod H)
    (hperf : ⁅H, H⁆ = H) : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  by_contra hne
  push Not at hne
  have hle : H ≤ Subgroup.centralizer (H : Set G') := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hne b hb a ha
  have hbot : H = ⊥ := by
    rw [← hperf]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  obtain ⟨N, -, -, y, hy, -, hy2⟩ := hH
  rw [hbot, Subgroup.mem_bot] at hy
  rw [hy, one_pow] at hy2
  exact hy2 N.one_mem

theorem scalar_of_commute [Finite K] [CharP K 2] {H : Subgroup (projectiveSL 3 K)}
    (hH : HasOrderFourMod H) (hperf : ⁅H, H⁆ = H) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ g ∈ commH H, (g : Matrix (Fin 3) (Fin 3) K) * M = M * (g : Matrix (Fin 3) (Fin 3) K)) :
    ∃ c : K, M = scalar (Fin 3) c := by
  set G' : Subgroup (GL (Fin 3) K) := (commH H).map Matrix.SpecialLinearGroup.toGL with hG'
  have hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep G'.subtype := by
    intro W hW
    refine commH_irred hH hperf W fun g hg w hw => ?_
    have h := hW ⟨Matrix.SpecialLinearGroup.toGL g, g, hg, rfl⟩ w hw
    simpa only [Subgroup.coe_subtype, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h
  rcases CFSG.RankThree.SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hirr with
    h | ⟨hcyc, -⟩
  · refine h M ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hM g hg
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := exists_ne_comm hH hperf
    rw [← map_commH hperf] at ha hb
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨h, hh, rfl⟩ := hb
    apply hab
    have hcomm := (IsCyclic.isMulCommutative (α := G')).is_comm.comm
      ⟨Matrix.SpecialLinearGroup.toGL g, g, hg, rfl⟩ ⟨Matrix.SpecialLinearGroup.toGL h, h, hh, rfl⟩
    have hgh : g * h = h * g := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_mul, map_mul]
      exact congrArg Subtype.val hcomm
    rw [← map_mul, ← map_mul, hgh]

theorem centralizer_eq_bot [Finite K] [CharP K 2] {H : Subgroup (projectiveSL 3 K)}
    (hH : HasOrderFourMod H) (hperf : ⁅H, H⁆ = H) :
    Subgroup.centralizer (H : Set (projectiveSL 3 K)) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨A, rfl⟩ := proj_surjective 3 K c
  have hψ : ∀ x ∈ preH H, proj 3 K ((MulAut.conj A).toMonoidHom x) = proj 3 K x := by
    intro x hx
    have hcx := Subgroup.mem_centralizer_iff.mp hc (proj 3 K x) hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, ← hcx,
      mul_inv_cancel_right]
  have hcomm : ∀ g ∈ commH H, (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
    intro g hg
    have h := eq_of_mem_commH (MulAut.conj A).toMonoidHom hψ hg
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have h' : A * g = g * A := by
      calc A * g = A * g * A⁻¹ * A := by group
        _ = g * A := by rw [h]
    have h'' := congrArg (fun z : SpecialLinearGroup (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) h'
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h''.symm
  obtain ⟨d, hd⟩ := scalar_of_commute hH hperf hcomm
  rw [Subgroup.mem_bot, proj_eq_one_iff, mem_scalars]
  have hdet : d ^ 3 = 1 := by
    have h := A.2
    rw [hd, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hd0 : d ≠ 0 := by
    rintro rfl
    norm_num at hdet
  exact ⟨Units.mk0 d hd0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet,
    Units.val_one]), by rw [hd, Units.val_mk0]⟩

theorem det_eq_zero_of_symm_diag [CharP K 2] {D : Matrix (Fin 3) (Fin 3) K}
    (hsym : ∀ i j, D i j = D j i) (hdiag : ∀ i, D i i = 0) : D.det = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_three, hdiag 0, hdiag 1, hdiag 2, hsym 1 0, hsym 2 0, hsym 2 1]
  linear_combination D 0 1 * D 0 2 * D 1 2 * h2

theorem false_of_transpose_form [Finite K] [CharP K 2] {G : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    {M : Matrix (Fin 3) (Fin 3) K} (hM0 : M.det ≠ 0)
    (hM : ∀ g ∈ G, (g : Matrix (Fin 3) (Fin 3) K)ᵀ * M * (g : Matrix (Fin 3) (Fin 3) K) = M) :
    False := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hinvT : ∀ g : SpecialLinearGroup (Fin 3) K,
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
        (g : Matrix (Fin 3) (Fin 3) K)ᵀ = 1 := by
    intro g
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  set D := M + Mᵀ with hD
  have hDg : ∀ g ∈ G, (g : Matrix (Fin 3) (Fin 3) K)ᵀ * D * (g : Matrix (Fin 3) (Fin 3) K) = D := by
    intro g hg
    have h1 := hM g hg
    have h1t := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at h1t
    rw [hD, Matrix.mul_add, Matrix.add_mul, h1, h1t]
  have hdotT : ∀ (A : Matrix (Fin 3) (Fin 3) K) (u y : Fin 3 → K),
      (A *ᵥ u) ⬝ᵥ y = u ⬝ᵥ (Aᵀ *ᵥ y) := by
    intro A u y
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  by_cases hD0 : D = 0
  ·
    have hMs : Mᵀ = M := by
      have h := hD0
      rw [hD, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h.symm
    have hsym : ∀ i j, M i j = M j i := fun i j => by
      rw [← Matrix.transpose_apply M j i, hMs]
    set q : (Fin 3 → K) → K := fun v => v ⬝ᵥ (M *ᵥ v) with hq
    have hqadd : ∀ u v, q (u + v) = q u + q v := by
      intro u v
      have hs : v ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ v) := by
        rw [show v ⬝ᵥ (M *ᵥ u) = (Mᵀ *ᵥ v) ⬝ᵥ u by rw [hdotT, Matrix.transpose_transpose], hMs,
          dotProduct_comm]
      simp only [hq, mulVec_add, add_dotProduct, dotProduct_add]
      rw [hs]
      linear_combination (u ⬝ᵥ (M *ᵥ v)) * h2
    have hqsmul : ∀ (c : K) v, q (c • v) = c ^ 2 * q v := by
      intro c v
      simp only [hq, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    let W : Submodule K (Fin 3 → K) :=
      { carrier := {v | q v = 0}
        add_mem' := by
          intro u v hu hv
          change q (u + v) = 0
          rw [hqadd]
          change q u = 0 at hu
          change q v = 0 at hv
          rw [hu, hv, add_zero]
        zero_mem' := by
          change q 0 = 0
          simp [hq]
        smul_mem' := by
          intro c v hv
          change q (c • v) = 0
          change q v = 0 at hv
          rw [hqsmul, hv, mul_zero] }
    have hWinv : ∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
      intro g hg w hw
      change q ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = 0
      change q w = 0 at hw
      have : q ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = q w := by
        simp only [hq]
        rw [hdotT, mulVec_mulVec, mulVec_mulVec, hM g hg]
      rw [this, hw]
    rcases hirr W hWinv with hbot | htop
    · by_cases h00 : M 0 0 = 0
      · have hv : (Pi.single 0 1 : Fin 3 → K) ∈ W := by
          change q (Pi.single 0 1) = 0
          simp only [hq, mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply]
          exact h00
        rw [hbot, Submodule.mem_bot] at hv
        exact one_ne_zero (congrFun hv 0 |>.symm.trans (by simp) |>.symm)
      · obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (M 1 1 / M 0 0)
        have hv : (![s, 1, 0] : Fin 3 → K) ∈ W := by
          change q ![s, 1, 0] = 0
          have hss : M 0 0 * (s * s) = M 1 1 := by
            rw [← hs]
            field_simp
          simp only [hq, dotProduct, mulVec, Fin.sum_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, mul_zero, zero_mul, add_zero, mul_one, one_mul,
            zero_add]
          rw [hsym 1 0]
          linear_combination hss + (M 1 1 + M 0 1 * s) * h2
        rw [hbot, Submodule.mem_bot] at hv
        have := congrFun hv 1
        simp at this
    · have hdiag : ∀ i, M i i = 0 := by
        intro i
        have hv : (Pi.single i 1 : Fin 3 → K) ∈ W := by
          rw [htop]
          exact Submodule.mem_top
        change q (Pi.single i 1) = 0 at hv
        simpa only [hq, mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] using hv
      exact hM0 (det_eq_zero_of_symm_diag hsym hdiag)
  ·
    let W : Submodule K (Fin 3 → K) := LinearMap.ker (Matrix.toLin' D)
    have hmemW : ∀ v, v ∈ W ↔ D *ᵥ v = 0 := fun v => by
      change Matrix.toLin' D v = 0 ↔ _
      rw [Matrix.toLin'_apply]
    have hWinv : ∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
      intro g hg w hw
      rw [hmemW] at hw ⊢
      have hDg' : D * (g : Matrix (Fin 3) (Fin 3) K) =
          ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * D := by
        calc D * (g : Matrix (Fin 3) (Fin 3) K)
            = ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
                (g : Matrix (Fin 3) (Fin 3) K)ᵀ * D * (g : Matrix (Fin 3) (Fin 3) K) := by
              rw [hinvT, Matrix.one_mul]
          _ = ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
                ((g : Matrix (Fin 3) (Fin 3) K)ᵀ * D * (g : Matrix (Fin 3) (Fin 3) K)) := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hDg g hg]
      rw [mulVec_mulVec, hDg', ← mulVec_mulVec, hw, mulVec_zero]
    have hsymD : ∀ i j, D i j = D j i := fun i j => by
      simp only [hD, Matrix.add_apply, Matrix.transpose_apply]
      ring
    have hdiagD : ∀ i, D i i = 0 := fun i => by
      simp only [hD, Matrix.add_apply, Matrix.transpose_apply]
      linear_combination M i i * h2
    rcases hirr W hWinv with hbot | htop
    · obtain ⟨v, hv0, hDv⟩ :=
        Matrix.exists_mulVec_eq_zero_iff.mpr (det_eq_zero_of_symm_diag hsymD hdiagD)
      have hv : v ∈ W := (hmemW v).mpr hDv
      rw [hbot, Submodule.mem_bot] at hv
      exact hv0 hv
    · apply hD0
      ext i j
      have hv : (Pi.single j 1 : Fin 3 → K) ∈ W := by
        rw [htop]
        exact Submodule.mem_top
      rw [hmemW, mulVec_single_one] at hv
      simpa [Matrix.col_apply] using congrFun hv i

theorem conj_map_eq_of_fix {H : Subgroup (projectiveSL 3 K)} {A : GL (Fin 3) K} {σ : K ≃+* K}
    (hfix : ∀ h ∈ H, (conjAut 3 K A * fieldAut 3 K σ) h = h) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ commH H) :
    (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map σ *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = g := by
  set ψ : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K :=
    (CatalogueBHigherLinearAction.slConjugation 3 K A).toMonoidHom.comp
      (CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ).toMonoidHom with hψdef
  have hψ : ∀ x ∈ preH H, proj 3 K (ψ x) = proj 3 K x := fun x hx => hfix _ hx
  have h := eq_of_mem_commH ψ hψ hg
  have hc := congrArg (fun z : SpecialLinearGroup (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) h
  simp only [hψdef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hc
  rw [coe_slConjugation] at hc
  exact hc

theorem conj_map_dual_eq_of_fix {H : Subgroup (projectiveSL 3 K)} {A : GL (Fin 3) K}
    {σ : K ≃+* K} (hfix : ∀ h ∈ H, (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) h = h)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ commH H) :
    (A : Matrix (Fin 3) (Fin 3) K) *
      (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ).map σ *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = g := by
  set ψ : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K :=
    (CatalogueBHigherLinearAction.slConjugation 3 K A).toMonoidHom.comp
      ((CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ).toMonoidHom.comp
        (CatalogueBGraphForm.slGraphAut 3 K).toMonoidHom) with hψdef
  have hψ : ∀ x ∈ preH H, proj 3 K (ψ x) = proj 3 K x := fun x hx => hfix _ hx
  have h := eq_of_mem_commH ψ hψ hg
  have hc := congrArg (fun z : SpecialLinearGroup (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) h
  simp only [hψdef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hc
  rw [coe_slConjugation] at hc
  exact hc

theorem map_one_ringAut (M : Matrix (Fin 3) (Fin 3) K) : M.map (1 : K ≃+* K) = M := by
  ext i j
  rfl

theorem det_ne_zero_of_GL (B : GL (Fin 3) K) : (B : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit B)).ne_zero

theorem fieldAut_ne_one_of_fix [Finite K] [CharP K 2] {H : Subgroup (projectiveSL 3 K)}
    (hH : HasOrderFourMod H) (hperf : ⁅H, H⁆ = H) {A : GL (Fin 3) K} {σ : K ≃+* K} {ε : ℕ}
    (hε : ε ≤ 1) (hfix : ∀ h ∈ H, (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) h = h)
    (hne : conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε ≠ 1) : σ ≠ 1 := by
  rintro rfl
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one] at hfix hne
    apply hne
    have hcomm : ∀ g ∈ commH H, (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
      intro g hg
      have h := conj_map_eq_of_fix hfix hg
      rw [map_one_ringAut] at h
      calc (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)
          = (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                (A : Matrix (Fin 3) (Fin 3) K) := by rw [h]
        _ = _ := by rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    obtain ⟨c, hc⟩ := scalar_of_commute hH hperf hcomm
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply det_ne_zero_of_GL A
      rw [hc, map_zero, Matrix.det_zero]
    have hA : A = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
      apply Units.ext
      rw [hc]
      rfl
    rw [hA, conjAut_scalar, map_one, mul_one]
  · rw [pow_one] at hfix hne
    have hform : ∀ g ∈ commH H, (g : Matrix (Fin 3) (Fin 3) K)ᵀ *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro g hg
      have h := conj_map_dual_eq_of_fix hfix hg
      rw [map_one_ringAut] at h
      have hT : (g : Matrix (Fin 3) (Fin 3) K)ᵀ *
          ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
      calc (g : Matrix (Fin 3) (Fin 3) K)ᵀ * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (g : Matrix (Fin 3) (Fin 3) K)
          = (g : Matrix (Fin 3) (Fin 3) K)ᵀ * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((A : Matrix (Fin 3) (Fin 3) K) *
                ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
                  ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by rw [h]
        _ = (g : Matrix (Fin 3) (Fin 3) K)ᵀ *
              (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) *
                ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
                  ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Units.inv_mul, Matrix.mul_one, hT, Matrix.one_mul]
    exact false_of_transpose_form (commH_irred hH hperf) (det_ne_zero_of_GL A⁻¹) hform

theorem even_and_eq_pow_of_sq_eq_one [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {A : GL (Fin 3) K} {σ : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1) (hσ : σ ≠ 1)
    (h2 : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) ^ 2 = 1) :
    Even f ∧ ∀ x, σ x = x ^ 2 ^ (f / 2) := by
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one] at h2
    obtain ⟨hfe, hx, -⟩ := even_linear_field_involution_descent hf hK le_rfl A σ hσ h2
    exact ⟨hfe, hx⟩
  · rw [pow_one] at h2
    obtain ⟨hfe, hx, -⟩ :=
      UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK le_rfl A σ hσ h2
    exact ⟨hfe, hx⟩

theorem exists_mul_eq_conjAut_dualAut {σ : K ≃+* K} (hσσ : σ * σ = 1) (A B : GL (Fin 3) K)
    {ε η : ℕ} (hε : ε ≤ 1) (hη : η ≤ 1) :
    ∃ (C : GL (Fin 3) K) (e : ℕ), e ≤ 1 ∧
      conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε *
          (conjAut 3 K B * fieldAut 3 K σ * dualAut 3 K ^ η) =
        conjAut 3 K C * fieldAut 3 K 1 * dualAut 3 K ^ e := by
  obtain ⟨-, -, -, hδδ, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  have hcf : ∀ C : GL (Fin 3) K, conjAut 3 K A * fieldAut 3 K σ * (conjAut 3 K C * fieldAut 3 K σ) =
      conjAut 3 K (A * Matrix.GeneralLinearGroup.map (σ : K →+* K) C) * fieldAut 3 K 1 := by
    intro C
    rw [conjAut_mul_fieldAut_mul, hσσ]
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl <;>
    rcases (show η = 0 ∨ η = 1 by omega) with rfl | rfl
  · refine ⟨A * Matrix.GeneralLinearGroup.map (σ : K →+* K) B, 0, zero_le_one, ?_⟩
    simp only [pow_zero, mul_one]
    exact hcf B
  · refine ⟨A * Matrix.GeneralLinearGroup.map (σ : K →+* K) B, 1, le_rfl, ?_⟩
    simp only [pow_zero, pow_one, mul_one]
    rw [← mul_assoc, hcf B]
  · refine ⟨A * Matrix.GeneralLinearGroup.map (σ : K →+* K)
      (Matrix.GeneralLinearGroup.inverseTranspose B), 1, le_rfl, ?_⟩
    simp only [pow_zero, pow_one, mul_one]
    rw [← hcf (Matrix.GeneralLinearGroup.inverseTranspose B)]
    calc conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K * (conjAut 3 K B * fieldAut 3 K σ)
        = conjAut 3 K A * fieldAut 3 K σ * (dualAut 3 K * conjAut 3 K B) * fieldAut 3 K σ := by
          simp only [mul_assoc]
      _ = conjAut 3 K A * fieldAut 3 K σ *
            (conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose B) * dualAut 3 K) *
              fieldAut 3 K σ := by rw [dualAut_mul_conjAut]
      _ = conjAut 3 K A * fieldAut 3 K σ *
            conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose B) *
              (dualAut 3 K * fieldAut 3 K σ) := by simp only [mul_assoc]
      _ = _ := by rw [dualAut_mul_fieldAut]; simp only [mul_assoc]
  · refine ⟨A * Matrix.GeneralLinearGroup.map (σ : K →+* K)
      (Matrix.GeneralLinearGroup.inverseTranspose B), 0, zero_le_one, ?_⟩
    simp only [pow_zero, pow_one, mul_one]
    rw [← hcf (Matrix.GeneralLinearGroup.inverseTranspose B)]
    calc conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K * (conjAut 3 K B * fieldAut 3 K σ *
          dualAut 3 K)
        = conjAut 3 K A * fieldAut 3 K σ * (dualAut 3 K * conjAut 3 K B) * fieldAut 3 K σ *
            dualAut 3 K := by simp only [mul_assoc]
      _ = conjAut 3 K A * fieldAut 3 K σ *
            (conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose B) * dualAut 3 K) *
              fieldAut 3 K σ * dualAut 3 K := by rw [dualAut_mul_conjAut]
      _ = conjAut 3 K A * fieldAut 3 K σ *
            conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose B) *
              (dualAut 3 K * fieldAut 3 K σ) * dualAut 3 K := by simp only [mul_assoc]
      _ = conjAut 3 K A * fieldAut 3 K σ *
            conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose B) * fieldAut 3 K σ *
              (dualAut 3 K * dualAut 3 K) := by rw [dualAut_mul_fieldAut]; simp only [mul_assoc]
      _ = _ := by rw [hδδ, mul_one]; simp only [mul_assoc]

theorem eq_of_involution_of_fix [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 1 ≤ f) {H : Subgroup (projectiveSL 3 K)} (hH : HasOrderFourMod H) (hperf : ⁅H, H⁆ = H)
    {α β : MulAut (projectiveSL 3 K)} (hα2 : α ^ 2 = 1) (hβ2 : β ^ 2 = 1) (hα1 : α ≠ 1)
    (hβ1 : β ≠ 1) (hαH : ∀ h ∈ H, α h = h) (hβH : ∀ h ∈ H, β h = h) : α = β := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 α
  obtain ⟨B, τ, η, hη, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 β
  have hσ := fieldAut_ne_one_of_fix hH hperf hε hαH hα1
  have hτ := fieldAut_ne_one_of_fix hH hperf hη hβH hβ1
  obtain ⟨hfe, hσx⟩ := even_and_eq_pow_of_sq_eq_one hK hf hε hσ hα2
  obtain ⟨-, hτx⟩ := even_and_eq_pow_of_sq_eq_one hK hf hη hτ hβ2
  have hστ : σ = τ := RingEquiv.ext fun x => by rw [hσx, hτx]
  subst hστ
  have hσσ : σ * σ = 1 := by
    haveI := Fintype.ofFinite K
    apply RingEquiv.ext
    intro x
    rw [RingAut.mul_apply, hσx, hσx, ← pow_mul, ← pow_add, ← two_mul,
      Nat.mul_div_cancel' hfe.two_dvd, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rfl
  obtain ⟨C, e, he, hCe⟩ := exists_mul_eq_conjAut_dualAut hσσ A B hε hη
  set α := conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε with hαdef
  set β := conjAut 3 K B * fieldAut 3 K σ * dualAut 3 K ^ η with hβdef
  have hγH : ∀ h ∈ H, (conjAut 3 K C * fieldAut 3 K 1 * dualAut 3 K ^ e) h = h := by
    intro h hh
    rw [← hCe, MulAut.mul_apply, hβH h hh, hαH h hh]
  have hγ : α * β = 1 := by
    by_contra hne
    rw [hCe] at hne
    exact fieldAut_ne_one_of_fix hH hperf he hγH hne rfl
  have hββ : β * β = 1 := by rw [← pow_two]; exact hβ2
  calc α = α * β * β := by rw [mul_assoc, hββ, mul_one]
    _ = β := by rw [hγ, one_mul]

end CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3
