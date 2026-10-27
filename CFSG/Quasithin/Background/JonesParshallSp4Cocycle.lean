module

public import CFSG.Quasithin.Background.JonesParshallSp4
public import CFSG.Quasithin.Background.JonesParshallSL2

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit

variable {F : Type} [Field F]

theorem sp_rows {M : Matrix Ix Ix F} (hM : Mᵀ * spJ F * M = spJ F) :
    M * spJ F * Mᵀ = spJ F := by
  have h1 : spJ F * Mᵀ * spJ F * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM, spJ_mul_spJ]
  have h2 : M * (spJ F * Mᵀ * spJ F) = 1 :=
    (mul_eq_one_comm_of_card_eq Ix Ix F rfl).mp h1
  calc M * spJ F * Mᵀ = M * (spJ F * Mᵀ * spJ F) * spJ F := by
        simp only [Matrix.mul_assoc, spJ_mul_spJ, Matrix.mul_one]
    _ = spJ F := by rw [h2, Matrix.one_mul]

theorem sp_rows_apply {M : Matrix Ix Ix F} (hM : Mᵀ * spJ F * M = spJ F) (j k : Ix) :
    bil (M j) (M k) = spJ F j k := by
  have h := congrFun (congrFun (sp_rows hM) j) k
  rw [← h]
  simp [bil, spJ, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks, one_apply]
  ring

@[expose] def muSp : ↥(sp4 F) →* AddMonoid.End (Ix → F) :=
  (DistribMulAction.toAddMonoidEnd (GL Ix F) (Ix → F)).comp (sp4 F).subtype

theorem muSp_apply (g : ↥(sp4 F)) (v : Ix → F) : muSp g v = (g : GL Ix F) • v := rfl

@[expose] def quadQ (v : Ix → F) : F := v (.inl 0) * v (.inr 0) + v (.inl 1) * v (.inr 1)

variable [Fintype F] [CharP F 2]

@[expose] def spF0 (g : ↥(sp4 F)) : Ix → F :=
  fun i => sqrtF (quadQ (((g : GL Ix F) : Matrix Ix Ix F) i))

theorem spF0_sq (g : ↥(sp4 F)) (i : Ix) :
    spF0 g i ^ 2 = quadQ (((g : GL Ix F) : Matrix Ix Ix F) i) :=
  sqrtF_sq _

omit [Fintype F] in
theorem sum_sq_ix (c : Ix → F) : (∑ j, c j) ^ 2 = ∑ j, c j ^ 2 := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [add_sq_F, add_sq_F, add_sq_F]

theorem spF0_mem : spF0 ∈ Z1A (muSp (F := F)) := by
  intro g h
  have hH := sp_rows_apply h.2
  set G := ((g : GL Ix F) : Matrix Ix Ix F) with hG
  set H := ((h : GL Ix F) : Matrix Ix Ix F) with hHdef
  have hgh : (((g * h : ↥(sp4 F)) : GL Ix F) : Matrix Ix Ix F) = G * H := rfl
  funext i
  rw [Pi.add_apply, muSp_apply]
  apply sq_inj
  rw [add_sq_F, spF0_sq, spF0_sq, hgh]
  change quadQ ((G * H) i) = quadQ (G i) + ((G *ᵥ spF0 h) i) ^ 2
  have hv : ((G *ᵥ spF0 h) i) ^ 2 = ∑ j, G i j ^ 2 * quadQ (H j) := by
    rw [mulVec, dotProduct, sum_sq_ix]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, spF0_sq]
  rw [hv]
  have h12 := hH (.inl 0) (.inl 1)
  have h13 := hH (.inl 0) (.inr 0)
  have h14 := hH (.inl 0) (.inr 1)
  have h23 := hH (.inl 1) (.inr 0)
  have h24 := hH (.inl 1) (.inr 1)
  have h34 := hH (.inr 0) (.inr 1)
  simp only [bil, spJ, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₂,
    Matrix.zero_apply, one_apply, Fin.isValue] at h12 h13 h14 h23 h24 h34
  simp only [quadQ, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  norm_num at h12 h13 h14 h23 h24 h34
  linear_combination (G i (.inl 0) * G i (.inl 1)) * h12 + (G i (.inl 0) * G i (.inr 0)) * h13 +
    (G i (.inl 0) * G i (.inr 1)) * h14 + (G i (.inl 1) * G i (.inr 0)) * h23 +
    (G i (.inl 1) * G i (.inr 1)) * h24 + (G i (.inr 0) * G i (.inr 1)) * h34

theorem smul_spF0_mem (B : F) : B • spF0 ∈ Z1A (muSp (F := F)) := by
  intro g h
  rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, spF0_mem g h, smul_add, muSp_apply,
    muSp_apply, smul_comm]

omit [Fintype F] in
theorem det_add_SL2 (M : SL2 F) :
    (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 1 1 +
      (M : Matrix (Fin 2) (Fin 2) F) 0 1 * (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have h := M.2
  rw [det_fin_two] at h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h + ((M : Matrix (Fin 2) (Fin 2) F) 0 1 *
    (M : Matrix (Fin 2) (Fin 2) F) 1 0) * h2

@[expose] def iotaElt (M : SL2 F) : ↥(sp4 F) :=
  spElt (iotaMat ((M : Matrix (Fin 2) (Fin 2) F) 0 0) ((M : Matrix (Fin 2) (Fin 2) F) 0 1)
    ((M : Matrix (Fin 2) (Fin 2) F) 1 0) ((M : Matrix (Fin 2) (Fin 2) F) 1 1))
    (iotaMat_mem (det_add_SL2 M))

omit [Fintype F] in
theorem iotaElt_smul (M : SL2 F) (x y z w : F) :
    (iotaElt M : GL Ix F) • vec4 x y z w =
      vec4 x ((M : Matrix (Fin 2) (Fin 2) F) 0 0 * y + (M : Matrix (Fin 2) (Fin 2) F) 0 1 * w) z
        ((M : Matrix (Fin 2) (Fin 2) F) 1 0 * y + (M : Matrix (Fin 2) (Fin 2) F) 1 1 * w) :=
  iotaMat_smul _ _ _ _ _ _ _ _

@[expose] def iotaHom : SL2 F →* ↥(sp4 F) where
  toFun := iotaElt
  map_one' := sp4_ext fun x y z w => by
    rw [iotaElt_smul]
    simp
  map_mul' M N := sp4_ext fun x y z w => by
    rw [Subgroup.coe_mul, mul_smul, iotaElt_smul, iotaElt_smul, iotaElt_smul]
    have hMN : ((M * N : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F) * (N : Matrix (Fin 2) (Fin 2) F) := rfl
    simp only [hMN, mul_apply, Fin.sum_univ_two]
    congr 1 <;> ring

omit [Fintype F] in
theorem iotaHom_smul (M : SL2 F) (x y z w : F) :
    (iotaHom M : GL Ix F) • vec4 x y z w =
      vec4 x ((M : Matrix (Fin 2) (Fin 2) F) 0 0 * y + (M : Matrix (Fin 2) (Fin 2) F) 0 1 * w) z
        ((M : Matrix (Fin 2) (Fin 2) F) 1 0 * y + (M : Matrix (Fin 2) (Fin 2) F) 1 1 * w) :=
  iotaElt_smul M x y z w

theorem spF0_iotaHom (M : SL2 F) :
    spF0 (iotaHom M) = vec4 0 (f0 M 0) 0 (f0 M 1) := by
  funext i
  rcases i with i | i <;> fin_cases i
  · change sqrtF (1 * 0 + 0 * 0) = 0
    simp [sqrtF_zero]
  · change sqrtF (0 * 0 + (M : Matrix (Fin 2) (Fin 2) F) 0 0 *
      (M : Matrix (Fin 2) (Fin 2) F) 0 1) = sqrtF (_ * _)
    rw [zero_mul, zero_add]
  · change sqrtF (0 * 1 + 0 * 0) = 0
    simp [sqrtF_zero]
  · change sqrtF (0 * 0 + (M : Matrix (Fin 2) (Fin 2) F) 1 0 *
      (M : Matrix (Fin 2) (Fin 2) F) 1 1) = sqrtF (_ * _)
    rw [zero_mul, zero_add]

omit [Fintype F] in
theorem iotaHom_smul_apply (M : SL2 F) (v : Ix → F) :
    (iotaHom M : GL Ix F) • v = vec4 (v (.inl 0))
      ((M : Matrix (Fin 2) (Fin 2) F) 0 0 * v (.inl 1) +
        (M : Matrix (Fin 2) (Fin 2) F) 0 1 * v (.inr 1)) (v (.inr 0))
      ((M : Matrix (Fin 2) (Fin 2) F) 1 0 * v (.inl 1) +
        (M : Matrix (Fin 2) (Fin 2) F) 1 1 * v (.inr 1)) := by
  conv_lhs => rw [vec4_eta v]
  exact iotaHom_smul _ _ _ _ _

@[expose] def qElt (α β γ : F) : ↥(sp4 F) := spX (γ + α * β) β 0 * spZ α

omit [Fintype F] in
theorem qElt_smul (α β γ x y z w : F) :
    (qElt α β γ : GL Ix F) • vec4 x y z w =
      vec4 (x + α * y + γ * z + β * w) (y + β * z) z (w + α * z) := by
  rw [qElt, Subgroup.coe_mul, mul_smul, spZ_smul, spX_smul]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  congr 1
  · linear_combination (α * β * z) * h2
  · ring
  · ring

omit [Fintype F] in
theorem qElt_smul_apply (α β γ : F) (v : Ix → F) :
    (qElt α β γ : GL Ix F) • v = vec4 (v (.inl 0) + α * v (.inl 1) + γ * v (.inr 0) +
      β * v (.inr 1)) (v (.inl 1) + β * v (.inr 0)) (v (.inr 0)) (v (.inr 1) + α * v (.inr 0)) := by
  conv_lhs => rw [vec4_eta v]
  exact qElt_smul _ _ _ _ _ _ _

omit [Fintype F] in
theorem qElt_mul (α β γ α' β' γ' : F) :
    qElt α β γ * qElt α' β' γ' = qElt (α + α') (β + β') (γ + γ' + α * β' + β * α') :=
  sp4_ext fun x y z w => by
    rw [Subgroup.coe_mul, mul_smul, qElt_smul, qElt_smul, qElt_smul]
    congr 1 <;> ring

omit [Fintype F] in
theorem iota_mul_qElt (M : SL2 F) (α β γ : F) :
    iotaHom M * qElt α β γ =
      qElt ((M : Matrix (Fin 2) (Fin 2) F) 1 0 * β + (M : Matrix (Fin 2) (Fin 2) F) 1 1 * α)
        ((M : Matrix (Fin 2) (Fin 2) F) 0 0 * β + (M : Matrix (Fin 2) (Fin 2) F) 0 1 * α) γ *
          iotaHom M :=
  sp4_ext fun x y z w => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, qElt_smul, iotaHom_smul,
      iotaHom_smul, qElt_smul]
    have hd := det_add_SL2 M
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    congr 1
    · linear_combination (-(α * y + β * w)) * hd -
        ((M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 1 0 * β * y +
          (M : Matrix (Fin 2) (Fin 2) F) 0 1 * (M : Matrix (Fin 2) (Fin 2) F) 1 1 * α * w) * h2
    · ring
    · ring

omit [Fintype F] in
theorem eq_qElt_mul_iota {g : GL Ix F} (hg : g ∈ sp4 F)
    (h1 : g • vec4 (1 : F) 0 0 0 = vec4 1 0 0 0) :
    ∃ (α β γ : F) (M : SL2 F), g = ((qElt α β γ * iotaHom M : ↥(sp4 F)) : GL Ix F) := by
  set w := g • vec4 (0 : F) 0 1 0 with hw
  have hw3 : w (.inr 0) = 1 := by
    have h := bil_smul hg (vec4 0 0 1 0) (vec4 1 0 0 0)
    rw [h1, ← hw, bil_e1, bil_e1] at h
    simpa [vec4] using h
  set q : ↥(sp4 F) := qElt (w (.inr 1)) (w (.inl 1)) (w (.inl 0)) with hq
  have hq1 : (q : GL Ix F) • vec4 (1 : F) 0 0 0 = vec4 1 0 0 0 := by
    rw [hq, qElt_smul]
    congr 1 <;> ring
  have hqf : (q : GL Ix F) • vec4 (0 : F) 0 1 0 = w := by
    conv_rhs => rw [vec4_eta w, hw3]
    rw [hq, qElt_smul]
    congr 1 <;> ring
  set g' := (q : GL Ix F)⁻¹ * g with hg'def
  have hg' : g' ∈ sp4 F := Subgroup.mul_mem _ (Subgroup.inv_mem _ q.2) hg
  have hg'1 : g' • vec4 (1 : F) 0 0 0 = vec4 1 0 0 0 := by
    rw [hg'def, mul_smul, h1]
    conv_lhs => rw [← hq1]
    rw [inv_smul_smul]
  have hg'2 : g' • vec4 (0 : F) 0 1 0 = vec4 0 0 1 0 := by
    rw [hg'def, mul_smul, ← hw, ← hqf, inv_smul_smul]
  set x := g' • vec4 (0 : F) 1 0 0 with hx
  set y := g' • vec4 (0 : F) 0 0 1 with hy
  have hb : ∀ u u' : Ix → F, bil (g' • u) (g' • u') = bil u u' := bil_smul hg'
  have hx1 : x (.inl 0) = 0 := by
    have h := hb (vec4 0 1 0 0) (vec4 0 0 1 0)
    rw [hg'2, ← hx, bil_f1, bil_f1] at h
    simpa [vec4] using h
  have hx3 : x (.inr 0) = 0 := by
    have h := hb (vec4 0 1 0 0) (vec4 1 0 0 0)
    rw [hg'1, ← hx, bil_e1, bil_e1] at h
    simpa [vec4] using h
  have hy1 : y (.inl 0) = 0 := by
    have h := hb (vec4 0 0 0 1) (vec4 0 0 1 0)
    rw [hg'2, ← hy, bil_f1, bil_f1] at h
    simpa [vec4] using h
  have hy3 : y (.inr 0) = 0 := by
    have h := hb (vec4 0 0 0 1) (vec4 1 0 0 0)
    rw [hg'1, ← hy, bil_e1, bil_e1] at h
    simpa [vec4] using h
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : F, x (.inl 1) = X₂ := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ X₄ : F, x (.inr 1) = X₄ := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂ : F, y (.inl 1) = Y₂ := ⟨_, rfl⟩
  obtain ⟨Y₄, hY₄⟩ : ∃ Y₄ : F, y (.inr 1) = Y₄ := ⟨_, rfl⟩
  have hxv : x = vec4 0 X₂ 0 X₄ := by rw [vec4_eta x, hx1, hx3, hX₂, hX₄]
  have hyv : y = vec4 0 Y₂ 0 Y₄ := by rw [vec4_eta y, hy1, hy3, hY₂, hY₄]
  have hxy : X₂ * Y₄ + Y₂ * X₄ = 1 := by
    have h := hb (vec4 0 1 0 0) (vec4 0 0 0 1)
    rw [← hx, ← hy, hxv, hyv, bil_vec4, bil_vec4] at h
    linear_combination h
  have hdet : (!![X₂, Y₂; X₄, Y₄] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [det_fin_two_of]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination hxy - (Y₂ * X₄) * h2
  refine ⟨w (.inr 1), w (.inl 1), w (.inl 0), ⟨!![X₂, Y₂; X₄, Y₄], hdet⟩, ?_⟩
  have e : g' = (iotaHom ⟨!![X₂, Y₂; X₄, Y₄], hdet⟩ : GL Ix F) := by
    refine gl_ext_vec4 fun a b c d => ?_
    rw [iotaHom_smul ⟨!![X₂, Y₂; X₄, Y₄], hdet⟩ a b c d]
    change (g' : Matrix Ix Ix F) *ᵥ vec4 a b c d = _
    rw [mulVec_vec4]
    change a • (g' • vec4 (1 : F) 0 0 0) + b • (g' • vec4 (0 : F) 1 0 0) +
      c • (g' • vec4 (0 : F) 0 1 0) + d • (g' • vec4 (0 : F) 0 0 1) = _
    rw [hg'1, hg'2, ← hx, ← hy, hxv, hyv]
    simp only [vec4_smul, vec4_add, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one]
    congr 1 <;> ring
  rw [Subgroup.coe_mul, ← e, ← hq, hg'def, mul_inv_cancel_left]

omit [Fintype F] in
theorem orbit_vec_e1 :
    MulAction.orbit ↥(sp4 F) (vec4 (1 : F) 0 0 0) = {0}ᶜ := by
  ext v
  simp only [MulAction.mem_orbit_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, rfl⟩ h0
    have h := congrArg (fun v => g⁻¹ • v) h0
    simp only [inv_smul_smul, smul_zero] at h
    exact one_ne_zero (congrFun h (.inl 0))
  · intro hv
    obtain ⟨r, hr, hre⟩ := exists_closure_smul_e1 hv
    exact ⟨⟨r, (Subgroup.closure_le _).mpr rootGens_subset hr⟩, hre⟩

theorem odd_index_stab_vec {n : ℕ} (hF : Fintype.card F = 2 ^ n) (hn : 0 < n) :
    Odd (MulAction.stabilizer ↥(sp4 F) (vec4 (1 : F) 0 0 0)).index := by
  classical
  rw [MulAction.index_stabilizer, orbit_vec_e1, Set.ncard_compl, Set.ncard_singleton,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, hF,
    ← pow_mul]
  obtain ⟨k, hk⟩ : ∃ k, n * (2 + 2) = k + 1 := ⟨n * (2 + 2) - 1, by omega⟩
  rw [hk, pow_succ]
  exact ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩

end CFSG.Quasithin.JonesParshall
