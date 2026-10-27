module

public import CFSG.Quasithin.MS93.MSPOff

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

theorem transv_eq_transv_iff [CharP F 2] {x y : V4 F} (hx : x ≠ 0) :
    transv y 1 = transv x 1 ↔ y = x := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨v, hv⟩ := exists_form_eq_one hx
  have h1 := congrArg (fun g : Sp4 F => mat g *ᵥ v) h
  simp only [transv_mulVec, one_mul, hv, one_smul, add_right_inj] at h1
  set l := form F y v with hl
  have hy : y ≠ 0 := by
    rintro rfl
    rw [smul_zero] at h1
    exact hx h1.symm
  rw [← h1, transv_smul_vec] at h
  have hl2 : l ^ 2 * 1 = 1 := transv_injective hy h.symm |>.symm.trans rfl |>.symm
  have hl1 : l = 1 := by
    have h2 : (l - 1) ^ 2 = 0 := by
      have h2z : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hl2 + (1 - l) * h2z
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  rw [← h1, hl1, one_smul]

theorem mulVec_eq_of_commute_transv [CharP F 2] {g : Sp4 F} {x : V4 F} (hx : x ≠ 0)
    (h : g * transv x 1 = transv x 1 * g) : mat g *ᵥ x = x := by
  have : g * transv x 1 * g⁻¹ = transv x 1 := by rw [h, mul_inv_cancel_right]
  rw [transv_conj] at this
  exact (transv_eq_transv_iff hx).1 this

theorem Q₂_comm [CharP F 2] {x y : Sp4 F} (hx : x ∈ Q₂ F) (hy : y ∈ Q₂ F) : x * y = y * x := by
  obtain ⟨hxS, hx0⟩ := mem_Q₂_iff.1 hx
  obtain ⟨hyS, hy0⟩ := mem_Q₂_iff.1 hy
  obtain ⟨a, C, hC, hxC⟩ := exists_of_mem_sylS hxS
  obtain ⟨b, E, hE, hyE⟩ := exists_of_mem_sylS hyS
  have hC11 : C 1 1 = 0 := by rw [← entry_of_mem_sylS hxC, hx0]
  have hE11 : E 1 1 = 0 := by rw [← entry_of_mem_sylS hyE, hy0]
  have hC10 : C 1 0 = C 0 1 := by simpa using congrFun₂ hC 0 1
  have hE10 : E 1 0 = E 0 1 := by simpa using congrFun₂ hE 0 1
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, mat_mul_mulVec, hxC, hyE]
  obtain ⟨p0, p1, p2, p3⟩ := mulVec_blockMat_unitri b E v
  obtain ⟨r0, r1, r2, r3⟩ := mulVec_blockMat_unitri a C v
  obtain ⟨s0, s1, s2, s3⟩ := mulVec_blockMat_unitri a C (blockMat (unitri b) E *ᵥ v)
  obtain ⟨t0, t1, t2, t3⟩ := mulVec_blockMat_unitri b E (blockMat (unitri a) C *ᵥ v)
  refine ext4 ?_ ?_ ?_ ?_
  · rw [s0, t0, p0, p1, p2, p3, r0, r1, r2, r3, hC11, hE11, hC10, hE10]
    grind
  · rw [s1, t1, p1, p2, p3, r1, r2, r3, hC11, hE11, hC10, hE10]
    grind
  · rw [s2, t2, p2, r2]
  · rw [s3, t3, p2, p3, r2, r3]
    grind

theorem Q₂_sq [CharP F 2] {x : Sp4 F} (hx : x ∈ Q₂ F) : x ^ 2 = 1 := by
  obtain ⟨hxS, hx0⟩ := mem_Q₂_iff.1 hx
  obtain ⟨a, C, hC, hxC⟩ := exists_of_mem_sylS hxS
  have hC11 : C 1 1 = 0 := by rw [← entry_of_mem_sylS hxC, hx0]
  have hC10 : C 1 0 = C 0 1 := by simpa using congrFun₂ hC 0 1
  refine ext_mulVec fun v => ?_
  rw [sq, mat_mul_mulVec, mat_one, one_mulVec, hxC]
  obtain ⟨r0, r1, r2, r3⟩ := mulVec_blockMat_unitri a C v
  obtain ⟨s0, s1, s2, s3⟩ := mulVec_blockMat_unitri a C (blockMat (unitri a) C *ᵥ v)
  refine ext4 ?_ ?_ ?_ ?_
  · rw [s0, r0, r1, r2, r3, hC11, hC10]
    grind
  · rw [s1, r1, r2, r3, hC11, hC10]
    grind
  · rw [s2, r2]
  · rw [s3, r2, r3]
    grind

abbrev hp₁ (F : Type) [Field F] : Submodule F (V4 F) := Submodule.span F {e₁ F, f₁ F}

abbrev lev₂ (F : Type) [Field F] : Subgroup (Sp4 F) := fixer (hp₁ F)

abbrev L₂ (F : Type) [Field F] : Subgroup (Sp4 F) := Q₂ F ⊔ lev₂ F

theorem mem_lev₂_iff {g : Sp4 F} :
    g ∈ lev₂ F ↔ mat g *ᵥ e₁ F = e₁ F ∧ mat g *ᵥ f₁ F = f₁ F := by
  refine ⟨fun h => ⟨h _ (Submodule.subset_span (Set.mem_insert _ _)),
    h _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))⟩, fun ⟨h1, h2⟩ v hv => ?_⟩
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  rw [mulVec_add, mulVec_smul, mulVec_smul, h1, h2]

theorem lev₂_le_P₂ : lev₂ F ≤ P₂ F := fun g hg =>
  fixer_le_stab _ (fun v hv => by
    rw [pt₀_eq_span] at hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [mulVec_smul, (mem_lev₂_iff.1 hg).1])

theorem L₂_le_P₂ : L₂ F ≤ P₂ F := sup_le Q₂_le_P₂ lev₂_le_P₂

theorem Q₂_le_L₂ : Q₂ F ≤ L₂ F := le_sup_left

theorem lev₂_le_L₂ : lev₂ F ≤ L₂ F := le_sup_right

theorem Q₂_inf_lev₂ : Q₂ F ⊓ lev₂ F = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgQ, hgL⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hgS, hg0⟩ := mem_Q₂_iff.1 hgQ
  obtain ⟨a, C, hC, hgC⟩ := exists_of_mem_sylS hgS
  have hC11 : C 1 1 = 0 := by rw [← entry_of_mem_sylS hgC, hg0]
  have hC10 : C 1 0 = C 0 1 := by simpa using congrFun₂ hC 0 1
  have hf := (mem_lev₂_iff.1 hgL).2
  rw [hgC] at hf
  obtain ⟨r0, r1, r2, r3⟩ := mulVec_blockMat_unitri a C (f₁ F)
  have ha : a = 0 := by
    have := congrFun hf (.inr 1)
    rw [r3] at this
    simpa using this
  have hc10 : C 1 0 = 0 := by
    have := congrFun hf (.inl 1)
    rw [r1] at this
    simpa using this
  have hc00 : C 0 0 = 0 := by
    have := congrFun hf (.inl 0)
    rw [r0, ha] at this
    simpa using this
  rw [Subgroup.mem_bot]
  refine mat_injective ?_
  rw [hgC, ha, mat_one, unitri_zero]
  have hC0 : C = 0 := by
    rw [eq_sym2 hC, hc00, ← hC10, hc10, hC11]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hC0]
  exact blockMat_one

theorem transv_mem_L₂ {x : V4 F} (hx : x (.inr 0) = 0) (c : F) : transv x c ∈ L₂ F := by
  set x' : V4 F := x - x (.inl 0) • e₁ F with hx'
  have hlev : transv x' c ∈ lev₂ F := mem_lev₂_iff.2 ⟨by
      rw [transv_mulVec, form_apply]
      simp [hx', hx], by
      rw [transv_mulVec, form_apply]
      simp [hx']⟩
  have hQ : transv x c * transv x' (-c) ∈ Q₂ F := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := mem_pt₀.1 hv
      rw [mat_mul_mulVec, transv_mulVec, transv_mulVec]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, hx', h1, h2, h3, hx]
    · have h0 := mem_perp_pt₀.1 hv
      rw [mat_mul_mulVec, transv_mulVec, transv_mulVec]
      refine mem_pt₀.2 ⟨?_, ?_, ?_⟩ <;> simp [form_apply, hx', h0, hx] <;> ring
  have : transv x c = (transv x c * transv x' (-c)) * transv x' c := by
    rw [mul_assoc, transv_mul, neg_add_cancel, transv_zero, mul_one]
  rw [this]
  exact Subgroup.mul_mem_sup hQ hlev

theorem L₂_le_normalizer_Q₂ : L₂ F ≤ Subgroup.normalizer (Q₂ F : Set (Sp4 F)) :=
  L₂_le_P₂.trans P₂_le_normalizer_Q₂

theorem transv_e₁_mem_L₂ (c : F) : transv (e₁ F) c ∈ L₂ F := transv_mem_L₂ (by simp) c

theorem center_L₂ [CharP F 2] : Subgroup.center ↥(L₂ F) = (X₂ F).subgroupOf (L₂ F) := by
  ext ⟨z, hz⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · intro h
    have hc : ∀ x : V4 F, x (.inr 0) = 0 → x ≠ 0 → mat z *ᵥ x = x := fun x hx hx0 =>
      mulVec_eq_of_commute_transv hx0
        (congrArg Subtype.val (h ⟨transv x 1, transv_mem_L₂ hx 1⟩)).symm
    have he₂ : mat z *ᵥ e₂ F = e₂ F := hc _ (by simp) e₂_ne_zero
    have hf₂ : mat z *ᵥ f₂ F = f₂ F := hc _ (by simp) f₂_ne_zero
    have he₁₂ : mat z *ᵥ (e₁ F + e₂ F) = e₁ F + e₂ F := hc _ (by simp) e₁_add_e₂_ne_zero
    have he₁ : mat z *ᵥ e₁ F = e₁ F := by
      rw [mulVec_add, he₂, add_left_inj] at he₁₂
      exact he₁₂
    intro v hv
    have h0 := mem_perp_pt₀.1 hv
    have hv' : v = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F + v (.inr 1) • f₂ F := by
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [h0]
    rw [hv', mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, he₁, he₂, hf₂]
  · intro hzX g
    obtain ⟨c, rfl⟩ := mem_X₂_iff.1 hzX
    refine Subtype.ext ?_
    change (g : Sp4 F) * transv (e₁ F) c = transv (e₁ F) c * g
    have key : L₂ F ≤ Subgroup.centralizer {transv (e₁ F) c} := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Q₂_comm hy (X₂_le_Q₂ (mem_X₂_iff.2 ⟨c, rfl⟩))
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have : y * transv (e₁ F) c * y⁻¹ = transv (e₁ F) c := by
          rw [transv_conj, (mem_lev₂_iff.1 hy).1]
        calc y * transv (e₁ F) c = y * transv (e₁ F) c * y⁻¹ * y := by group
          _ = transv (e₁ F) c * y := by rw [this]
    exact Subgroup.mem_centralizer_singleton_iff.1 (key g.2)

@[expose] def iotaM (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![1, 0; 0, M 0 0] !![0, 0; 0, M 0 1] !![0, 0; 0, M 1 0] !![1, 0; 0, M 1 1]

theorem iotaM_mulVec (M : Matrix (Fin 2) (Fin 2) F) (v : V4 F) :
    iotaM M *ᵥ v = v (.inl 0) • e₁ F + (M 0 0 * v (.inl 1) + M 0 1 * v (.inr 1)) • e₂ F +
      v (.inr 0) • f₁ F + (M 1 0 * v (.inl 1) + M 1 1 * v (.inr 1)) • f₂ F := by
  rw [iotaM, fromBlocks_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [dotProduct, Fin.sum_univ_two]

theorem iotaM_mul (M N : Matrix (Fin 2) (Fin 2) F) : iotaM M * iotaM N = iotaM (M * N) := by
  refine mat_ext_mulVec fun v => ?_
  rw [← mulVec_mulVec, iotaM_mulVec, iotaM_mulVec, iotaM_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem iotaM_one : iotaM (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  refine mat_ext_mulVec fun v => ?_
  rw [iotaM_mulVec, one_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem iotaM_isom (M : Matrix.SpecialLinearGroup (Fin 2) F) (u v : V4 F) :
    form F (iotaM M *ᵥ u) (iotaM M *ᵥ v) = form F u v := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := M.2
    rwa [det_fin_two] at this
  rw [iotaM_mulVec, iotaM_mulVec, form_apply, form_apply]
  simp
  linear_combination (u (.inl 1) * v (.inr 1) - u (.inr 1) * v (.inl 1)) * hdet

@[expose] noncomputable def levHom₂ : Matrix.SpecialLinearGroup (Fin 2) F →* Sp4 F where
  toFun M := ofMat (iotaM M) (iotaM (M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F))
    (by rw [iotaM_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, iotaM_one])
    (by rw [iotaM_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, iotaM_one]) (iotaM_isom M)
  map_one' := mat_injective (by rw [mat_ofMat, Matrix.SpecialLinearGroup.coe_one, iotaM_one,
    mat_one])
  map_mul' M N := mat_injective (by rw [mat_ofMat, mat_mul, mat_ofMat, mat_ofMat, iotaM_mul,
    Matrix.SpecialLinearGroup.coe_mul])

theorem mat_levHom₂ (M : Matrix.SpecialLinearGroup (Fin 2) F) : mat (levHom₂ M) = iotaM M :=
  rfl

theorem levHom₂_injective : Function.Injective (levHom₂ (F := F)) := by
  intro M N h
  have h' := congrArg (fun g => mat g) h
  simp only [mat_levHom₂] at h'
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [iotaM] using congrFun₂ h' (.inl 1) (.inl 1)
  · simpa [iotaM] using congrFun₂ h' (.inl 1) (.inr 1)
  · simpa [iotaM] using congrFun₂ h' (.inr 1) (.inl 1)
  · simpa [iotaM] using congrFun₂ h' (.inr 1) (.inr 1)

theorem range_levHom₂ : (levHom₂ (F := F)).range = lev₂ F := by
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨M, rfl⟩
    refine mem_lev₂_iff.2 ⟨?_, ?_⟩ <;> rw [mat_levHom₂, iotaM_mulVec] <;>
      refine ext4 ?_ ?_ ?_ ?_ <;> simp
  · obtain ⟨h1, h2⟩ := mem_lev₂_iff.1 hg
    have hperp : ∀ w : V4 F, w (.inl 0) = 0 → w (.inr 0) = 0 →
        (mat g *ᵥ w) (.inl 0) = 0 ∧ (mat g *ᵥ w) (.inr 0) = 0 := by
      intro w hw0 hw2
      have hB1 := form_mat g (e₁ F) w
      have hB2 := form_mat g (f₁ F) w
      rw [h1, form_apply, form_apply] at hB1
      rw [h2, form_apply, form_apply] at hB2
      simp [hw0, hw2] at hB1 hB2
      exact ⟨hB2, hB1⟩
    obtain ⟨a0, a2⟩ := hperp (e₂ F) (by simp) (by simp)
    obtain ⟨b0, b2⟩ := hperp (f₂ F) (by simp) (by simp)
    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) F,
        M = !![(mat g *ᵥ e₂ F) (.inl 1), (mat g *ᵥ f₂ F) (.inl 1);
          (mat g *ᵥ e₂ F) (.inr 1), (mat g *ᵥ f₂ F) (.inr 1)] := ⟨_, rfl⟩
    have hdet : M.det = 1 := by
      have := form_mat g (e₂ F) (f₂ F)
      rw [form_apply, form_apply] at this
      simp [a0, a2, b0, b2] at this
      rw [det_fin_two, hM]
      simp
      linear_combination this
    refine ⟨⟨M, hdet⟩, ext_mulVec fun v => ?_⟩
    change iotaM M *ᵥ v = _
    rw [iotaM_mulVec]
    have hv : v = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F + v (.inr 0) • f₁ F +
        v (.inr 1) • f₂ F := by
      refine ext4 ?_ ?_ ?_ ?_ <;> simp
    conv_rhs => rw [hv]
    rw [mulVec_add, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
      h1, h2]
    have a0' : mat g (.inl 0) (.inl 1) = 0 := by simpa using a0
    have a2' : mat g (.inr 0) (.inl 1) = 0 := by simpa using a2
    have b0' : mat g (.inl 0) (.inr 1) = 0 := by simpa using b0
    have b2' : mat g (.inr 0) (.inr 1) = 0 := by simpa using b2
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [hM, a0', a2', b0', b2'] <;> ring

@[expose] noncomputable def lev₂Equiv : Matrix.SpecialLinearGroup (Fin 2) F ≃* lev₂ F :=
  (MonoidHom.ofInjective levHom₂_injective).trans (MulEquiv.subgroupCongr range_levHom₂)

@[expose] noncomputable def levHom₁ : Matrix.SpecialLinearGroup (Fin 2) F →* Sp4 F :=
  SymplecticTorusWeyl.leviSp.comp Matrix.SpecialLinearGroup.toGL

theorem mat_levHom₁ (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    mat (levHom₁ A) = fromBlocks (A : Matrix (Fin 2) (Fin 2) F) 0 0
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  rw [levHom₁, MonoidHom.comp_apply, mat, SymplecticTorusWeyl.coe_leviSp]
  simp only [Matrix.SpecialLinearGroup.coe_inv]
  congr 2

noncomputable abbrev lev₁ (F : Type) [Field F] : Subgroup (Sp4 F) := (levHom₁ (F := F)).range

noncomputable abbrev L₁ (F : Type) [Field F] : Subgroup (Sp4 F) := Q₁ F ⊔ lev₁ F

theorem levHom₁_injective : Function.Injective (levHom₁ (F := F)) := by
  intro A B h
  have h' := congrArg (fun g => mat g) h
  simp only [mat_levHom₁] at h'
  exact Subtype.ext (fromBlocks_inj.1 h').1

theorem lev₁_le_P₁ : lev₁ F ≤ P₁ F := by
  rintro _ ⟨A, rfl⟩
  refine mem_stab_of_le fun v hv => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  have hr : v ∘ Sum.inr = 0 := funext fun j => by fin_cases j <;> simp [h0, h1]
  refine mem_ln₀.2 ⟨?_, ?_⟩ <;> rw [mat_levHom₁, fromBlocks_mulVec, hr] <;> simp

theorem L₁_le_P₁ : L₁ F ≤ P₁ F := sup_le Q₁_le_P₁ lev₁_le_P₁

theorem Q₁_le_L₁ : Q₁ F ≤ L₁ F := le_sup_left

theorem lev₁_le_L₁ : lev₁ F ≤ L₁ F := le_sup_right

theorem L₁_le_normalizer_Q₁ : L₁ F ≤ Subgroup.normalizer (Q₁ F : Set (Sp4 F)) :=
  L₁_le_P₁.trans P₁_le_normalizer_Q₁

theorem Q₁_inf_lev₁ : Q₁ F ⊓ lev₁ F = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgQ, A, rfl⟩ := Subgroup.mem_inf.1 hg
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have hfix : ∀ j : Fin 2, mat (levHom₁ A) *ᵥ Pi.single (.inl j) 1 = Pi.single (.inl j) 1 :=
      fun j => hgQ _ (mem_ln₀.2 ⟨by simp, by simp⟩)
    ext i j
    have := congrFun (hfix j) (.inl i)
    rw [mat_levHom₁, fromBlocks_mulVec] at this
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] using this
  rw [Subgroup.mem_bot, show A = 1 from Subtype.ext hA, map_one]

theorem levHom₁_conj_tau (A : Matrix.SpecialLinearGroup (Fin 2) F)
    {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    levHom₁ A * tau hC * (levHom₁ A)⁻¹ = tau (C := (A : Matrix (Fin 2) (Fin 2) F) * C *
      (A : Matrix (Fin 2) (Fin 2) F)ᵀ)
      (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  refine mat_injective ?_
  rw [mat_mul, mat_mul, ← map_inv, mat_levHom₁, mat_levHom₁, inv_inv, mat_tau, mat_tau,
    blockMat, blockMat, unitri_zero, inv_one, transpose_one, Matrix.one_mul, Matrix.one_mul,
    fromBlocks_multiply, fromBlocks_multiply]
  have h1 : (A : Matrix (Fin 2) (Fin 2) F) *
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *
      (A : Matrix (Fin 2) (Fin 2) F)ᵀ = 1 := by
    rw [← transpose_mul, h1, transpose_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, h1, h2,
    Matrix.mul_assoc]

@[expose] noncomputable def shortHom : Multiplicative F →* Sp4 F where
  toFun c := tau (sym2_transpose 0 (Multiplicative.toAdd c) 0)
  map_one' := mat_injective (by
    rw [mat_tau, mat_one, unitri_zero]
    convert blockMat_one using 2
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)
  map_mul' c d := by
    rw [tau_mul_tau]
    exact tau_congr _ _ (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sym2])

noncomputable abbrev X₁ (F : Type) [Field F] : Subgroup (Sp4 F) := (shortHom (F := F)).range

theorem X₁_le_Q₁ : X₁ F ≤ Q₁ F := by
  rintro _ ⟨c, rfl⟩
  exact tau_mem_Q₁ _

theorem commSp_X₁ : commSp (X₁ F) = ln₀ F := by
  refine le_antisymm ((commSp_mono X₁_le_Q₁).trans commSp_Q₁.le) fun v hv => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  have k := sub_mem_commSp (MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (1 : F), rfl⟩ :
    shortHom (F := F) (Multiplicative.ofAdd 1) ∈ X₁ F) (v (.inl 1) • f₁ F + v (.inl 0) • f₂ F)
  convert k using 1
  change v = mat (tau (sym2_transpose (0 : F) 1 0)) *ᵥ _ - _
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_tau_sym2 (0 : F) 1 0 (v (.inl 1) • f₁ F + v (.inl 0) • f₂ F)
  refine ext4 ?_ ?_ ?_ ?_ <;> simp only [Pi.sub_apply]
  · rw [e0]
    simp
  · rw [e1]
    simp
  · rw [e2]
    simp [h0]
  · rw [e3]
    simp [h1]

theorem center_L₁ [CharP F 2] : Subgroup.center ↥(L₁ F) = (X₁ F).subgroupOf (L₁ F) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hcomm : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (c : F),
      (A : Matrix (Fin 2) (Fin 2) F) * sym2 0 c 0 * (A : Matrix (Fin 2) (Fin 2) F)ᵀ =
        sym2 0 c 0 := by
    intro A c
    have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      have := A.2
      rwa [det_fin_two] at this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym2, Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  ext ⟨z, hz⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · intro h
    have hc : ∀ x : V4 F, x ∈ ln₀ F → x ≠ 0 → mat z *ᵥ x = x := fun x hx hx0 =>
      mulVec_eq_of_commute_transv hx0
        (congrArg Subtype.val (h ⟨transv x 1, Q₁_le_L₁ (xPoint_le_qLine isLine_ln₀
          ((Submodule.span_singleton_le_iff_mem _ _).2 hx) (transv_mem_xPoint x 1))⟩)).symm
    have hzQ : z ∈ Q₁ F := by
      intro v hv
      obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
      have hv' : v = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F := by
        refine ext4 ?_ ?_ ?_ ?_ <;> simp [h0, h1]
      rw [hv', mulVec_add, mulVec_smul, mulVec_smul,
        hc _ (mem_ln₀.2 ⟨by simp, by simp⟩) e₁_ne_zero,
        hc _ (mem_ln₀.2 ⟨by simp, by simp⟩) e₂_ne_zero]
    rw [Q₁_eq_radical] at hzQ
    obtain ⟨C, hC, rfl⟩ := hzQ
    have hfix : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
        (A : Matrix (Fin 2) (Fin 2) F) * C * (A : Matrix (Fin 2) (Fin 2) F)ᵀ = C := fun A => by
      have hA := congrArg Subtype.val (h ⟨levHom₁ A, lev₁_le_L₁ ⟨A, rfl⟩⟩)
      change levHom₁ A * tau hC = tau hC * levHom₁ A at hA
      have : levHom₁ A * tau hC * (levHom₁ A)⁻¹ = tau hC := by rw [hA, mul_inv_cancel_right]
      rw [levHom₁_conj_tau] at this
      exact tau_injective _ _ this
    have hC10 : C 1 0 = C 0 1 := by simpa using congrFun₂ hC 0 1
    have hu := congrFun₂ (hfix ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩) 0 1
    have hl := congrFun₂ (hfix ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩) 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at hu hl
    have hC00 : C 0 0 = 0 := by linear_combination hl
    have hC11 : C 1 1 = 0 := by linear_combination hu
    refine ⟨Multiplicative.ofAdd (C 0 1), tau_congr _ _ ?_⟩
    conv_rhs => rw [eq_sym2 hC, hC00, hC11]
    rfl
  · rintro ⟨c, rfl⟩ g
    refine Subtype.ext ?_
    change (g : Sp4 F) * shortHom c = shortHom c * g
    have key : L₁ F ≤ Subgroup.centralizer {shortHom (F := F) c} := by
      refine sup_le (fun y hy => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Q₁_comm hy (X₁_le_Q₁ ⟨c, rfl⟩)
      · rintro _ ⟨A, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : levHom₁ A * shortHom c * (levHom₁ A)⁻¹ = shortHom c := by
          change levHom₁ A * tau _ * (levHom₁ A)⁻¹ = tau _
          rw [levHom₁_conj_tau]
          exact tau_congr _ _ (hcomm A _)
        calc levHom₁ A * shortHom c = levHom₁ A * shortHom c * (levHom₁ A)⁻¹ * levHom₁ A := by
              group
          _ = shortHom c * levHom₁ A := by rw [this]
    exact Subgroup.mem_centralizer_singleton_iff.1 (key g.2)

theorem normalizer_qLine {l : Submodule F (V4 F)} (hl : IsLine l) :
    Subgroup.normalizer (qLine l : Set (Sp4 F)) = stab l := by
  refine le_antisymm ?_ (stab_le_normalizer_fixer l)
  have h := normalizer_le_stab_fixSp (qLine l)
  rwa [fixSp_qLine hl] at h

theorem normalizer_qPoint {p : Submodule F (V4 F)} (hp : IsPoint p) :
    Subgroup.normalizer (qPoint p : Set (Sp4 F)) = stab p := by
  refine le_antisymm ?_ (stab_le_normalizer_qPoint p)
  have h := normalizer_le_stab_fixSp (qPoint p)
  rwa [fixSp_qPoint hp] at h

theorem normalizer_xPoint {p : Submodule F (V4 F)} (hp : IsPoint p) :
    Subgroup.normalizer (xPoint p : Set (Sp4 F)) = stab p := by
  refine le_antisymm ?_ (stab_le_normalizer_xPoint p)
  have h := normalizer_le_stab_fixSp (xPoint p)
  rwa [fixSp_xPoint hp, stab_perp] at h

theorem normalizer_Q₁ : Subgroup.normalizer (Q₁ F : Set (Sp4 F)) = P₁ F :=
  normalizer_qLine isLine_ln₀

theorem normalizer_Q₂ : Subgroup.normalizer (Q₂ F : Set (Sp4 F)) = P₂ F :=
  normalizer_qPoint isPoint_pt₀

theorem normalizer_X₂ : Subgroup.normalizer (X₂ F : Set (Sp4 F)) = P₂ F :=
  normalizer_xPoint isPoint_pt₀

@[expose] def wJ (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem levHom₁_wJ_not_mem_P₂ : levHom₁ (wJ F) ∉ P₂ F := by
  intro h
  have he : e₁ F ∈ pt₀ F := by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _
  have := (mem_pt₀.1 (mulVec_mem_of_mem_stab h he)).1
  rw [mat_levHom₁, fromBlocks_mulVec] at this
  simp [wJ, dotProduct, Fin.sum_univ_two] at this

theorem levHom₂_wJ_not_mem_P₁ : levHom₂ (wJ F) ∉ P₁ F := by
  intro h
  have he : e₂ F ∈ ln₀ F := mem_ln₀.2 ⟨by simp, by simp⟩
  have := (mem_ln₀.1 (mulVec_mem_of_mem_stab h he)).2
  rw [mat_levHom₂, iotaM_mulVec] at this
  simp [wJ] at this

theorem not_P₁_le_borel : ¬ P₁ F ≤ borel F := fun h =>
  levHom₁_wJ_not_mem_P₂ (borel_le_P₂ (h (lev₁_le_P₁ ⟨wJ F, rfl⟩)))

theorem levHom₂_wJ_mem_lev₂ : levHom₂ (wJ F) ∈ lev₂ F := by
  rw [← range_levHom₂]
  exact ⟨wJ F, rfl⟩

theorem not_P₂_le_borel : ¬ P₂ F ≤ borel F := fun h =>
  levHom₂_wJ_not_mem_P₁ (borel_le_P₁ (h (lev₂_le_P₂ levHom₂_wJ_mem_lev₂)))

theorem pCoreOf_P₁ [Finite F] [CharP F 2] : CFSG.Open.pCoreOf 2 (P₁ F) = Q₁ F := by
  rcases pCoreOf_of_sylS_le (sylS_le_P₁ (F := F)) with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -, -⟩ |
    ⟨h, -, -⟩
  · exact absurd h not_P₁_le_borel
  · exact h
  · exact absurd (h (lev₁_le_P₁ ⟨wJ F, rfl⟩)) levHom₁_wJ_not_mem_P₂
  · exact absurd le_rfl h

theorem pCoreOf_P₂ [Finite F] [CharP F 2] : CFSG.Open.pCoreOf 2 (P₂ F) = Q₂ F := by
  rcases pCoreOf_of_sylS_le (sylS_le_P₂ (F := F)) with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨-, -, h⟩ |
    ⟨-, h, -⟩
  · exact absurd h not_P₂_le_borel
  · exact absurd (h (lev₂_le_P₂ levHom₂_wJ_mem_lev₂)) levHom₂_wJ_not_mem_P₁
  · exact h
  · exact absurd le_rfl h

theorem pCoreOf_borel [Finite F] [CharP F 2] : CFSG.Open.pCoreOf 2 (borel F) = sylS F := by
  rcases pCoreOf_of_sylS_le (sylS_le_borel (F := F)) with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
    ⟨h, -, -⟩
  · exact h
  · exact absurd le_rfl h
  · exact absurd le_rfl h
  · exact absurd borel_le_P₁ h

end CFSG.Quasithin.MS93.MSP
