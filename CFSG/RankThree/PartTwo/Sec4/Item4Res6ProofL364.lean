module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Minus
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofL3Pi
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

open CFSG CFSG.LieType.Seitz CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem isElemAbelian_map_conj (ψ : MulAut Y64) {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    CFSG.Assembly.IsElemAbelian 3 (E.map (MulAut.conj ψ).toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem card_map_conj (ψ : MulAut Y64) (E : Subgroup (MulAut Y64)) :
    Nat.card (E.map (MulAut.conj ψ).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj ψ).injective

theorem seitzHyperGamma_eq_top_of_conj (ψ : MulAut Y64) {E : Subgroup (MulAut Y64)}
    (h : seitzHyperGamma 3 (E.map (MulAut.conj ψ).toMonoidHom) = ⊤) : seitzHyperGamma 3 E = ⊤ :=
  seitzHyperGamma_eq_top_of_map ψ (MulAut.conj ψ).toMonoidHom
    (fun a x => by simp [MulAut.conj_apply]) (MulAut.conj ψ).injective h

theorem mem_map_conj_iff (ψ : MulAut Y64) {E : Subgroup (MulAut Y64)} {x : MulAut Y64} :
    x ∈ E.map (MulAut.conj ψ).toMonoidHom ↔ ψ⁻¹ * x * ψ ∈ E := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    refine ⟨_, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conj_fieldAut_of_mem_GLσ {g : GL (Fin 3) K64} (hg : g ∈ GLσ) :
    (conjAut 3 K64 g)⁻¹ * fieldAut 3 K64 σ4 * conjAut 3 K64 g = fieldAut 3 K64 σ4 := by
  have h := fieldAut_mul_conjAut (n := 3) σ4 g
  have hg' : Matrix.GeneralLinearGroup.map (σ4 : K64 →+* K64) g = g := hg
  rw [hg'] at h
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_conj_cases {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) (hf : fieldAut 3 K64 σ4 ∈ E) :
    ∃ g ∈ GLσ, fieldAut 3 K64 σ4 ∈ E.map (MulAut.conj (conjAut 3 K64 g)⁻¹).toMonoidHom ∧
      ((ρ t1Lab ∈ E.map (MulAut.conj (conjAut 3 K64 g)⁻¹).toMonoidHom ∧
          ρ t2Lab ∈ E.map (MulAut.conj (conjAut 3 K64 g)⁻¹).toMonoidHom) ∨
        (ρ zLab ∈ E.map (MulAut.conj (conjAut 3 K64 g)⁻¹).toMonoidHom ∧
          ∃ a : Fin 3, ρ (wLab a) ∈ E.map (MulAut.conj (conjAut 3 K64 g)⁻¹).toMonoidHom)) := by
  obtain ⟨g, hg, hlab⟩ := exists_conj_labels hE hf
  set ψ := (conjAut 3 K64 g)⁻¹ with hψ
  set E₁ := E.map (MulAut.conj ψ).toMonoidHom with hE₁
  have hE₁e := isElemAbelian_map_conj ψ hE
  have hE₁27 : Nat.card E₁ = 27 := by rw [hE₁, card_map_conj, h27]
  have hf₁ : fieldAut 3 K64 σ4 ∈ E₁ := by
    rw [hE₁, mem_map_conj_iff, hψ, inv_inv]
    have h1 := conj_fieldAut_of_mem_GLσ hg
    have : conjAut 3 K64 g * fieldAut 3 K64 σ4 * (conjAut 3 K64 g)⁻¹ = fieldAut 3 K64 σ4 := by
      calc conjAut 3 K64 g * fieldAut 3 K64 σ4 * (conjAut 3 K64 g)⁻¹
          = conjAut 3 K64 g * ((conjAut 3 K64 g)⁻¹ * fieldAut 3 K64 σ4 * conjAut 3 K64 g) *
              (conjAut 3 K64 g)⁻¹ := by rw [h1]
        _ = fieldAut 3 K64 σ4 := by group
    rw [this]; exact hf
  refine ⟨g, hg, hf₁, ?_⟩
  have hcomm : IsMulCommutative (E₁ ⊓ linearAutGroup 3 K64 : Subgroup (MulAut Y64)) :=
    ⟨⟨fun x y => Subtype.ext (show (x : MulAut Y64) * y = y * x from
      congrArg Subtype.val (hE₁e.1.is_comm.comm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩))⟩⟩
  have hρ : ∀ x ∈ (E₁ ⊓ linearAutGroup 3 K64 : Subgroup (MulAut Y64)), ∃ y : Lab, x = ρ y := by
    intro x hx
    have hx1 := (mem_map_conj_iff ψ).mp hx.1
    have hxD : ψ⁻¹ * x * ψ ∈ E ⊓ linearAutGroup 3 K64 := by
      refine ⟨hx1, ?_⟩
      have hψD : ψ ∈ linearAutGroup 3 K64 :=
        (linearAutGroup 3 K64).inv_mem (conjAut_mem_linearAutGroup g)
      exact (linearAutGroup 3 K64).mul_mem ((linearAutGroup 3 K64).mul_mem
        ((linearAutGroup 3 K64).inv_mem hψD) hx.2) hψD
    obtain ⟨y, hy⟩ := hlab _ hxD
    refine ⟨y, ?_⟩
    rw [← hy, hψ, inv_inv]
    group
  rcases labels_cases hcomm (card_inf_linearAutGroup_eq_nine hE₁e hE₁27) hρ with
    ⟨h1, h2⟩ | ⟨hz, a, ha⟩
  · exact Or.inl ⟨h1.1, h2.1⟩
  · exact Or.inr ⟨hz.1, a, ha.1⟩

theorem ρ_w0_not_mem_zpowers : ρ (wLab 0) ∉ Subgroup.zpowers (ρ zLab) := by
  intro h
  have h3 : ρ zLab ^ 3 = 1 := by
    rw [pow_three, ρ_mul, ρ_mul]
    have : (mulLab zLab (mulLab zLab zLab).1).1 = (0, 0, 0) := by decide
    rw [this, ρ_zero]
  rcases eq_of_mem_zpowers_of_pow_three h3 h with h0 | h0 | h0
  · exact absurd (ρ_injective (h0.trans ρ_zero.symm)) (by decide)
  · exact absurd (ρ_injective h0) (by decide)
  · rw [ρ_mul] at h0; exact absurd (ρ_injective h0) (by decide)

theorem det_L_z_w : (L zLab).det = 1 ∧ (L (wLab 0)).det = 1 := by decide

theorem det_glι_LGL (y : Lab) :
    Matrix.GeneralLinearGroup.det (glι (LGL y)) = Units.map ι.toMonoidHom
      (Matrix.GeneralLinearGroup.det (LGL y)) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, coe_glι, coe_LGL, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem det_glι_z_w : Matrix.GeneralLinearGroup.det (glι (LGL zLab)) = 1 ∧
    Matrix.GeneralLinearGroup.det (glι (LGL (wLab 0))) = 1 := by
  obtain ⟨hz, hw⟩ := det_L_z_w
  constructor
  · rw [det_glι_LGL]; apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, coe_LGL, hz]
  · rw [det_glι_LGL]; apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, coe_LGL, hw]

theorem seitzHyperGamma_eq_top_of_det {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27)
    (hf : fieldAut 3 K64 σ4 ∈ E) {A : GL (Fin 3) K64} (hAσ : A ∈ GLσ)
    (hAE : conjAut 3 K64 A ∈ E) (hAdet : Matrix.GeneralLinearGroup.det A ≠ 1) :
    seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨g, hg, hf₁, hcases⟩ := exists_conj_cases hE h27 hf
  set ψ := (conjAut 3 K64 g)⁻¹ with hψ
  set E₁ := E.map (MulAut.conj ψ).toMonoidHom with hE₁
  have hE₁e := isElemAbelian_map_conj ψ hE
  have hE₁27 : Nat.card E₁ = 27 := by rw [hE₁, card_map_conj, h27]
  apply seitzHyperGamma_eq_top_of_conj ψ
  rcases hcases with ⟨h1, h2⟩ | ⟨hz, a, ha⟩
  · exact seitzHyperGamma_eq_top_toral hE₁e hE₁27 hf₁ h1 h2
  · by_cases ha0 : a = 0
    · exfalso
      subst ha0
      have hA1 : conjAut 3 K64 (g⁻¹ * A * g) ∈ E₁ := by
        rw [hE₁, mem_map_conj_iff, hψ, inv_inv, map_mul, map_mul, map_inv]
        simpa [mul_assoc] using hAE
      have hcl : Subgroup.closure ({ρ zLab, ρ (wLab 0)} : Set (MulAut Y64)) =
          E₁ ⊓ linearAutGroup 3 K64 := by
        apply Subgroup.eq_of_le_of_card_ge
        · rw [Subgroup.closure_le]
          intro x hx
          rcases hx with rfl | rfl
          · exact ⟨hz, ρ_mem _⟩
          · exact ⟨ha, ρ_mem _⟩
        · rw [card_inf_linearAutGroup_eq_nine hE₁e hE₁27,
            card_closure_pair hE₁e hE₁27 hz ha (ρ_ne_one (by decide)) ρ_w0_not_mem_zpowers]
      have hmem : conjAut 3 K64 (g⁻¹ * A * g) ∈
          Subgroup.closure ({ρ zLab, ρ (wLab 0)} : Set (MulAut Y64)) := by
        rw [hcl]; exact ⟨hA1, conjAut_mem_linearAutGroup _⟩
      have hcomm : ρ zLab * ρ (wLab 0) = ρ (wLab 0) * ρ zLab :=
        congrArg Subtype.val (hE₁e.1.is_comm.comm ⟨_, hz⟩ ⟨_, ha⟩)
      obtain ⟨i, j, hij⟩ := exists_pow_mul_pow_of_mem_closure hcomm (hE₁e.2 _ hz)
        (hE₁e.2 _ ha) hmem
      set Z := glι (LGL zLab) with hZ
      set W := glι (LGL (wLab 0)) with hW
      have hij' : conjAut 3 K64 (g⁻¹ * A * g) = conjAut 3 K64 (Z ^ (i : ℕ) * W ^ (j : ℕ)) := by
        rw [hij, map_mul, map_pow, map_pow]; rfl
      obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq hij'
      have huσ : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ GLσ := by
        have : Matrix.GeneralLinearGroup.scalar (Fin 3) u =
            g⁻¹ * A * g * (Z ^ (i : ℕ) * W ^ (j : ℕ))⁻¹ := by
          rw [hu, mul_inv_cancel_right]
        rw [this]
        refine GLσ.mul_mem (GLσ.mul_mem (GLσ.mul_mem (GLσ.inv_mem hg) hAσ) hg)
          (GLσ.inv_mem (GLσ.mul_mem (GLσ.pow_mem (glι_mem_GLσ _) _)
            (GLσ.pow_mem (glι_mem_GLσ _) _)))
      have hu3 : u ^ 3 = 1 :=
        Units.ext (by simpa using pow_three_of_σ4_fixed (σ4_fixed_of_scalar_mem huσ) u.ne_zero)
      apply hAdet
      have hdet := congrArg Matrix.GeneralLinearGroup.det hu
      rw [map_mul, map_mul, map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar, map_mul,
        map_pow, map_pow, det_glι_z_w.1, det_glι_z_w.2, one_pow, one_pow, mul_one,
        Fintype.card_fin, hu3] at hdet
      rw [mul_one, mul_comm _ (Matrix.GeneralLinearGroup.det g), ← mul_assoc,
        mul_inv_cancel, one_mul] at hdet
      exact hdet
    · exact seitzHyperGamma_eq_top_minus hE₁e hE₁27 hf₁ ha0 hz ha

theorem L_w0_facts : L (wLab 0) * L (wLab 0) * L (wLab 0) = 1 ∧
    L (wLab 0) * L zLab = (ω4 * ω4) • (L zLab * L (wLab 0)) := by decide

theorem ω4u_sq : ((ω4u ^ 2 : F4ˣ) : F4) = ω4 * ω4 := by
  rw [Units.val_pow_eq_pow_val, pow_two]; rfl

theorem W_mul_Z : glι (LGL (wLab 0)) * glι (LGL zLab) =
    Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map ι.toMonoidHom (ω4u ^ 2)) *
      (glι (LGL zLab) * glι (LGL (wLab 0))) := by
  have h : LGL (wLab 0) * LGL zLab =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (ω4u ^ 2) * (LGL zLab * LGL (wLab 0)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_LGL, coe_LGL, L_w0_facts.2,
      Matrix.GeneralLinearGroup.coe_scalar, ω4u_sq, Matrix.scalar_apply, smul_eq_diagonal_mul]
  rw [← map_mul, h, map_mul, glι, Matrix.GeneralLinearGroup.map_scalar, ← glι, map_mul]
  rfl

theorem W_twisted_cube : Matrix.GeneralLinearGroup.scalar (Fin 3) (1 : K64ˣ) =
    glι (LGL (wLab 0)) * Matrix.GeneralLinearGroup.map (σ4 : K64 →+* K64) (glι (LGL (wLab 0))) *
      Matrix.GeneralLinearGroup.map ((σ4 * σ4 : K64 ≃+* K64) : K64 →+* K64)
        (glι (LGL (wLab 0))) := by
  have hσ : Matrix.GeneralLinearGroup.map (σ4 : K64 →+* K64) (glι (LGL (wLab 0))) =
      glι (LGL (wLab 0)) := glι_mem_GLσ _
  have hσσ : Matrix.GeneralLinearGroup.map ((σ4 * σ4 : K64 ≃+* K64) : K64 →+* K64)
      (glι (LGL (wLab 0))) = glι (LGL (wLab 0)) := by
    apply Units.ext
    ext a b
    change (σ4 * σ4) (ι _) = ι _
    rw [RingAut.mul_apply, σ4_ι, σ4_ι]
  rw [hσ, hσσ, map_one, ← map_mul, ← map_mul]
  have : LGL (wLab 0) * LGL (wLab 0) * LGL (wLab 0) = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_LGL, L_w0_facts.1, Units.val_one]
  rw [this, map_one]

theorem seitzHyperGamma_eq_top_of_mem {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27)
    (hf : fieldAut 3 K64 σ4 ∈ E) : seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨g, hg, hf₁, hcases⟩ := exists_conj_cases hE h27 hf
  set ψ := (conjAut 3 K64 g)⁻¹ with hψ
  set E₁ := E.map (MulAut.conj ψ).toMonoidHom with hE₁
  have hE₁e := isElemAbelian_map_conj ψ hE
  have hE₁27 : Nat.card E₁ = 27 := by rw [hE₁, card_map_conj, h27]
  apply seitzHyperGamma_eq_top_of_conj ψ
  rcases hcases with ⟨h1, h2⟩ | ⟨hz, a, ha⟩
  · exact seitzHyperGamma_eq_top_toral hE₁e hE₁27 hf₁ h1 h2
  · by_cases ha0 : a = 0
    · subst ha0
      set Z := glι (LGL zLab) with hZ
      set W := glι (LGL (wLab 0)) with hW
      obtain ⟨Hm, d, hHd⟩ := KFacts.exists_mul_map_eq_scalar_mul_of_orderOf_eq_three
        (n := 3) (by norm_num) orderOf_σ4 W W_twisted_cube
      have hconj := KFacts.conjAut_mul_fieldAut_eq_conj W Hm σ4 d hHd
      set ψ₂ := (conjAut 3 K64 Hm)⁻¹ with hψ₂
      set E₂ := E₁.map (MulAut.conj ψ₂).toMonoidHom with hE₂
      have hE₂e := isElemAbelian_map_conj ψ₂ hE₁e
      have hE₂27 : Nat.card E₂ = 27 := by rw [hE₂, card_map_conj, hE₁27]
      apply seitzHyperGamma_eq_top_of_conj ψ₂
      have hf₂ : fieldAut 3 K64 σ4 ∈ E₂ := by
        rw [hE₂, mem_map_conj_iff, hψ₂, inv_inv, ← hconj]
        exact E₁.mul_mem ha hf₁
      have hω21 : ω ^ 21 = 1 := by
        rw [show 21 = 3 * 7 by norm_num, pow_mul, omega_cube, one_pow]
      obtain ⟨μ, hμ⟩ := exists_cube_root hω21
      have hμ0 : μ ≠ 0 := by
        intro h; rw [h] at hμ; simp at hμ; exact omega_ne_zero hμ.symm
      set mu : K64ˣ := Units.mk0 μ hμ0 with hmu
      set A := Matrix.GeneralLinearGroup.scalar (Fin 3) mu * (Hm⁻¹ * Z * Hm) with hA
      have hAE : conjAut 3 K64 A ∈ E₂ := by
        rw [hE₂, mem_map_conj_iff]
        have e : ψ₂⁻¹ * conjAut 3 K64 A * ψ₂ = ρ zLab := by
          rw [hψ₂, inv_inv, hA, map_mul, conjAut_scalar, one_mul, map_mul, map_mul, map_inv]
          simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
          rfl
        rw [e]; exact hz
      have hAσ : A ∈ GLσ := by
        rw [mem_GLσ]
        have hZσ : mapσ Z = Z := glι_mem_GLσ _
        have hHm : mapσ Hm = W⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) d * Hm) := by
          rw [← hHd, inv_mul_cancel_left]
        have hWZ : W * Z * W⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map ι.toMonoidHom (ω4u ^ 2)) * Z := by
          rw [W_mul_Z, mul_assoc, mul_inv_cancel_right]
        have hσμ : Units.map (σ4 : K64 →* K64) mu * Units.map ι.toMonoidHom (ω4u ^ 2) = mu := by
          apply Units.ext
          simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, hmu, Units.val_mk0,
            RingHom.toMonoidHom_eq_coe, ω4u_sq]
          change σ4 μ * ι (ω4 * ω4) = μ
          rw [map_mul, ι_ω4, σ4_apply, show μ ^ 4 = μ ^ 3 * μ by ring, hμ]
          linear_combination μ * omega_cube
        rw [hA, map_mul, map_mul, map_mul, map_inv, mapσ_scalar, hZσ, hHm]
        have hc1 := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) d
        calc Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ4 : K64 →* K64) mu) *
              ((W⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) d * Hm))⁻¹ * Z *
                (W⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) d * Hm)))
            = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ4 : K64 →* K64) mu) *
              (Hm⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 3) d)⁻¹ * (W * Z * W⁻¹) *
                Matrix.GeneralLinearGroup.scalar (Fin 3) d) * Hm) := by group
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ4 : K64 →* K64) mu) *
              (Hm⁻¹ * (W * Z * W⁻¹) * Hm) := by
                rw [mul_assoc ((Matrix.GeneralLinearGroup.scalar (Fin 3) d)⁻¹), ← hc1 (W * Z * W⁻¹),
                  inv_mul_cancel_left]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ4 : K64 →* K64) mu) *
              Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map ι.toMonoidHom (ω4u ^ 2)) *
              (Hm⁻¹ * Z * Hm) := by
                have hc2 := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3)
                  (Units.map ι.toMonoidHom (ω4u ^ 2)) Hm⁻¹
                rw [hWZ]
                calc Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ4 : K64 →* K64) mu) *
                      (Hm⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3)
                        (Units.map ι.toMonoidHom (ω4u ^ 2)) * Z) * Hm)
                    = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ4 : K64 →* K64) mu) *
                      (Hm⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3)
                        (Units.map ι.toMonoidHom (ω4u ^ 2)) * Z * Hm) := by group
                  _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ4 : K64 →* K64) mu) *
                      (Matrix.GeneralLinearGroup.scalar (Fin 3)
                        (Units.map ι.toMonoidHom (ω4u ^ 2)) * Hm⁻¹ * Z * Hm) := by rw [hc2]
                  _ = _ := by group
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) mu * (Hm⁻¹ * Z * Hm) := by
                rw [← map_mul, hσμ]
      have hAdet : Matrix.GeneralLinearGroup.det A ≠ 1 := by
        intro h1
        rw [hA, map_mul, Matrix.GeneralLinearGroup.det_scalar, map_mul, map_mul, map_inv,
          det_glι_z_w.1, mul_one, mul_comm, inv_mul_cancel, Fintype.card_fin] at h1
        have := congrArg Units.val h1
        rw [Units.val_mul, Units.val_one, one_mul, Units.val_pow_eq_pow_val, hmu, Units.val_mk0,
          hμ] at this
        exact omega_ne_one this
      exact seitzHyperGamma_eq_top_of_det hE₂e hE₂27 hf₂ hAσ hAE hAdet
    · exact seitzHyperGamma_eq_top_minus hE₁e hE₁27 hf₁ ha0 hz ha

theorem seitzHyperGamma_eq_top_Y64 {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) : seitzHyperGamma 3 E = ⊤ :=
  seitzHyperGamma_eq_top_of_field (fun _ hE' h27' hf' => seitzHyperGamma_eq_top_of_mem hE' h27' hf')
    hE h27

end CFSG.RankThree.PartTwo.Sec4.Res6L364

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.RankThree.PartTwo.Sec4.Res6L364

theorem seitzL3SixtyFour_holds : SeitzL3SixtyFour := by
  intro X _ _ hX E hE h27
  obtain ⟨φ⟩ := hX
  let e : X ≃* Y64 := φ.trans (projSLEquivProjectiveSL 3 K64)
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  refine seitzHyperGamma_eq_top_of_map e (MulAut.congr e).toMonoidHom
    (fun a x => by simp [MulAut.congr_apply]) hinj (seitzHyperGamma_eq_top_Y64 ?_ ?_)
  · refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      simp only [Subgroup.coe_mul] at this ⊢
      rw [← map_mul, ← map_mul, this]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE.2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective hinj, h27]

end CFSG.RankThree.PartTwo.Sec4

