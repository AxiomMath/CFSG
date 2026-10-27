module

public import CFSG.Quasithin.Background.Harris.L2.Steinberg8Tensor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

noncomputable section

namespace CFSG.Quasithin.G112A2.Eleven

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups TensorProduct

abbrev F8 := GaloisField 2 3

theorem two_eq_zero_F8 : (2 : F8) = 0 := by exact_mod_cast CharP.cast_eq_zero F8 2

abbrev uMat : Matrix (Fin 2) (Fin 2) F8 := !![1, 1; 0, 1]

theorem invol_matrix_conj (G : Matrix (Fin 2) (Fin 2) F8)
    (hdet : G 0 0 * G 1 1 - G 0 1 * G 1 0 = 1) (hsq : G * G = 1) (hne : G ≠ 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) F8, P.det = 1 ∧ G * P = P * uMat := by
  have h2 : (2 : F8) = 0 := two_eq_zero_F8
  have hchar : ringChar F8 = 2 := ringChar.eq F8 2
  have e00 : G 0 0 * G 0 0 + G 0 1 * G 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hsq 0) 0
  have e11 : G 1 0 * G 0 1 + G 1 1 * G 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hsq 1) 1
  have hsum2 : (G 0 0 + G 1 1) * (G 0 0 + G 1 1) = 0 := by
    linear_combination e00 + e11 + (G 0 0 * G 1 1 - G 0 1 * G 1 0 + 1) * h2
  have hsum : G 0 0 + G 1 1 = 0 := mul_self_eq_zero.mp hsum2
  have hd : G 1 1 = G 0 0 := by linear_combination -hsum + G 1 1 * h2
  have hne' : ¬ (G 0 0 = 1 ∧ G 0 1 = 0 ∧ G 1 0 = 0 ∧ G 1 1 = 1) := by
    rintro ⟨ha, hb, hc, hd1⟩
    apply hne
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd1]
  by_cases hb : G 0 1 = 0
  ·
    have ha1 : G 0 0 = 1 := by
      have h' : (G 0 0 - 1) * (G 0 0 - 1) = 0 := by
        linear_combination e00 - G 1 0 * hb + (1 - G 0 0) * h2
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h')
    have hd1 : G 1 1 = 1 := by rw [hd, ha1]
    have hc : G 1 0 ≠ 0 := fun hc0 => hne' ⟨ha1, hb, hc0, hd1⟩
    obtain ⟨x, hx⟩ := FiniteField.isSquare_of_char_two hchar ((G 1 0)⁻¹)
    have hxc : x * x * G 1 0 = 1 := by rw [← hx]; exact inv_mul_cancel₀ hc
    refine ⟨!![0, x; x * G 1 0, 0], ?_, ?_⟩
    · simp [Matrix.det_fin_two]
      linear_combination (-1 : F8) * hxc - h2
    · ext i j
      revert i j
      refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue]
        linear_combination (x * G 1 0) * hb
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue]
        linear_combination x * ha1
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue]
        linear_combination (x * G 1 0) * hd1
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue]
        ring
  ·
    obtain ⟨x, hx⟩ := FiniteField.isSquare_of_char_two hchar ((G 0 1)⁻¹)
    have hxb : x * x * G 0 1 = 1 := by rw [← hx]; exact inv_mul_cancel₀ hb
    refine ⟨!![x * G 0 1, 0; x * (G 0 0 + 1), x], ?_, ?_⟩
    · simp [Matrix.det_fin_two]
      linear_combination hxb
    · ext i j
      revert i j
      refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue]
        linear_combination (x * G 0 0 * G 0 1) * h2
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue]
        ring
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue]
        linear_combination x * e00 + x * (G 0 0 + 1) * hd
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue]
        linear_combination x * hd - x * h2

theorem sl2_conj_uElt_of_invol (g : Matrix.SpecialLinearGroup (Fin 2) F8)
    (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    ∃ P : Matrix.SpecialLinearGroup (Fin 2) F8, g = P * uElt (1 : F8) * P⁻¹ := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F8) 0 0 * (g : Matrix (Fin 2) (Fin 2) F8) 1 1
      - (g : Matrix (Fin 2) (Fin 2) F8) 0 1 * (g : Matrix (Fin 2) (Fin 2) F8) 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  have hsq : (g : Matrix (Fin 2) (Fin 2) F8) * (g : Matrix (Fin 2) (Fin 2) F8) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hg2, Matrix.SpecialLinearGroup.coe_one]
  have hne : (g : Matrix (Fin 2) (Fin 2) F8) ≠ 1 := fun h =>
    hg1 (Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm))
  obtain ⟨P, hPdet, hGP⟩ := invol_matrix_conj _ hdet hsq hne
  obtain ⟨Ps, hPs⟩ : ∃ Ps : Matrix.SpecialLinearGroup (Fin 2) F8,
      (Ps : Matrix (Fin 2) (Fin 2) F8) = P := ⟨⟨P, hPdet⟩, rfl⟩
  have hmul : g * Ps = Ps * uElt (1 : F8) := by
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) F8) * (Ps : Matrix (Fin 2) (Fin 2) F8) =
      (Ps : Matrix (Fin 2) (Fin 2) F8) * uMat
    rw [hPs]
    exact hGP
  refine ⟨Ps, ?_⟩
  rw [← hmul, mul_inv_cancel_right]

abbrev Model := (Fin 3 → Fin 2) → F8

abbrev E3 : Fin 3 → ℕ := fun i => (i : ℕ)

abbrev rhoM := tensorRep F8 F8 E3

theorem tmatE_uElt_one (p y : Fin 3 → Fin 2) :
    tmatE F8 E3 (uElt (1 : F8)) p y = ∏ i, uMat (p i) (y i) := by
  simp [tmatE, twistMat_uElt, uMat]

def delta (y : Fin 3 → Fin 2) : Model := fun x => if x = y then 1 else 0

theorem rhoM_delta_apply (y p : Fin 3 → Fin 2) :
    rhoM (uElt (1 : F8)) (delta y) p = ∏ i, uMat (p i) (y i) := by
  rw [tensorRep_apply, ← tmatE_uElt_one]
  simp [delta, mul_ite]

abbrev Tu : Module.End F8 Model := rhoM (uElt (1 : F8)) - LinearMap.id

abbrev yy1 : Fin 3 → Fin 2 := ![1, 0, 0]
abbrev yy2 : Fin 3 → Fin 2 := ![1, 1, 0]
abbrev yy3 : Fin 3 → Fin 2 := ![1, 0, 1]
abbrev yy4 : Fin 3 → Fin 2 := ![1, 1, 1]
abbrev pp1 : Fin 3 → Fin 2 := ![0, 0, 0]
abbrev pp2 : Fin 3 → Fin 2 := ![0, 1, 0]
abbrev pp3 : Fin 3 → Fin 2 := ![0, 0, 1]
abbrev pp4 : Fin 3 → Fin 2 := ![1, 1, 0]

theorem four_vectors_indep :
    LinearIndependent F8 ![Tu (delta yy1), Tu (delta yy2), Tu (delta yy3), Tu (delta yy4)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have e1 := congrFun hc pp1
  have e2 := congrFun hc pp2
  have e3 := congrFun hc pp3
  have e4 := congrFun hc pp4
  simp [Fin.sum_univ_four, Finset.sum_apply, Tu, LinearMap.sub_apply, rhoM_delta_apply, delta,
    Fin.prod_univ_three, uMat] at e1 e2 e3 e4
  have h3 : c 3 = 0 := e4
  have h2 : c 2 = 0 := by linear_combination e3 - h3
  have h1 : c 1 = 0 := by linear_combination e2 - h3
  have h0 : c 0 = 0 := by linear_combination e1 - h1 - h2 - h3
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3]

theorem finrank_Tu_ge_four : 4 ≤ Module.finrank F8 (LinearMap.range Tu) := by
  have hli := four_vectors_indep
  have hspan : Submodule.span F8 (Set.range
      ![Tu (delta yy1), Tu (delta yy2), Tu (delta yy3), Tu (delta yy4)]) ≤ LinearMap.range Tu := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨delta yy1, rfl⟩
    · exact ⟨delta yy2, rfl⟩
    · exact ⟨delta yy3, rfl⟩
    · exact ⟨delta yy4, rfl⟩
  have h4 : Module.finrank F8 (Submodule.span F8 (Set.range
      ![Tu (delta yy1), Tu (delta yy2), Tu (delta yy3), Tu (delta yy4)])) = 4 :=
    finrank_span_eq_card hli
  have h5 := Submodule.finrank_mono hspan
  omega

theorem finrank_range_ge_four_of_conj (P g : Matrix.SpecialLinearGroup (Fin 2) F8)
    (hg : g = P * uElt (1 : F8) * P⁻¹) :
    4 ≤ Module.finrank F8 (LinearMap.range (rhoM g - LinearMap.id)) := by
  have hPP : rhoM P * rhoM P⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hPP' : rhoM P⁻¹ * rhoM P = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hg' : rhoM g = rhoM P * rhoM (uElt (1 : F8)) * rhoM P⁻¹ := by rw [hg, map_mul, map_mul]
  let Pe : Model ≃ₗ[F8] Model := LinearEquiv.ofLinear (rhoM P) (rhoM P⁻¹)
    (by rw [← Module.End.mul_eq_comp, hPP, Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, hPP', Module.End.one_eq_id])
  have key : ∀ z, ((rhoM g - LinearMap.id : Module.End F8 Model)) (Pe z) = Pe (Tu z) := by
    intro z
    have h1 : rhoM P⁻¹ (rhoM P z) = z := by
      have := congrArg (fun f : Module.End F8 Model => f z) hPP'
      simpa using this
    simp only [Pe, LinearEquiv.ofLinear_apply, Tu, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hg']
    simp only [Module.End.mul_apply, h1, map_sub]
  have hle : (LinearMap.range Tu).map (Pe : Model →ₗ[F8] Model) ≤
      LinearMap.range (rhoM g - LinearMap.id) := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨Pe z, key z⟩
  calc 4 ≤ Module.finrank F8 (LinearMap.range Tu) := finrank_Tu_ge_four
    _ = Module.finrank F8 ((LinearMap.range Tu).map (Pe : Model →ₗ[F8] Model)) :=
        (LinearEquiv.finrank_map_eq Pe _).symm
    _ ≤ Module.finrank F8 (LinearMap.range (rhoM g - LinearMap.id)) :=
        Submodule.finrank_mono hle

theorem finrank_range_one :
    Module.finrank F8 (LinearMap.range (rhoM (1 : Matrix.SpecialLinearGroup (Fin 2) F8) -
      LinearMap.id)) = 0 := by
  rw [map_one, Module.End.one_eq_id, sub_self, LinearMap.range_zero, finrank_bot]

theorem finrank_range_ne_two_of_invol (g : Matrix.SpecialLinearGroup (Fin 2) F8) (hg2 : g * g = 1) :
    Module.finrank F8 (LinearMap.range (rhoM g - LinearMap.id)) ≠ 2 := by
  by_cases h1 : g = 1
  · subst h1
    rw [finrank_range_one]
    norm_num
  · obtain ⟨P, hP⟩ := sl2_conj_uElt_of_invol g hg2 h1
    have := finrank_range_ge_four_of_conj P g hP
    omega

section Transfer

open CFSG.Quasithin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem finrank_range_baseChange_eq (f : V →ₗ[ZMod 2] V) :
    Module.finrank F8 (LinearMap.range (LinearMap.baseChange F8 f)) =
      Module.finrank (ZMod 2) (LinearMap.range f) := by
  have hinj : Function.Injective (LinearMap.baseChange F8 (LinearMap.range f).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hset : LinearMap.range (LinearMap.baseChange F8 f) =
      LinearMap.range (LinearMap.baseChange F8 (LinearMap.range f).subtype) := by
    ext y
    have h := congrArg (fun S : Submodule (ZMod 2) (F8 ⊗[ZMod 2] V) => y ∈ S)
      (LinearMap.lTensor_range (Q := F8) (g := f))
    exact h.to_iff
  rw [hset, LinearMap.finrank_range_of_inj hinj]
  exact Module.finrank_baseChange

theorem finrank_range_of_intertwine {A B : Type} [AddCommGroup A] [Module F8 A]
    [AddCommGroup B] [Module F8 B] (e : A ≃ₗ[F8] B) (S : A →ₗ[F8] A) (T : B →ₗ[F8] B)
    (h : T ∘ₗ (e : A →ₗ[F8] B) = (e : A →ₗ[F8] B) ∘ₗ S) :
    Module.finrank F8 (LinearMap.range S) = Module.finrank F8 (LinearMap.range T) := by
  have h1 : LinearMap.range ((e : A →ₗ[F8] B) ∘ₗ S) = (LinearMap.range S).map (e : A →ₗ[F8] B) :=
    LinearMap.range_comp _ _
  have h2 : LinearMap.range (T ∘ₗ (e : A →ₗ[F8] B)) = LinearMap.range T :=
    LinearMap.range_comp_of_range_eq_top T (LinearMap.range_eq_top.2 e.surjective)
  have h3 : Module.finrank F8 ((LinearMap.range S).map (e : A →ₗ[F8] B)) =
      Module.finrank F8 (LinearMap.range S) :=
    LinearEquiv.finrank_map_eq e _
  rw [← h3, ← h1, ← h, h2]

theorem exists_model_iso {H : Subgroup (CFSG.Quasithin.G11.GLV V)}
    (hL : CFSG.Quasithin.G11.IsL28TwistedTensorModule H) :
    ∃ (φ' : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) F8)
      (ψ' : (F8 ⊗[ZMod 2] V) ≃ₗ[F8] Model),
      ∀ (h : ↥H) (x : F8 ⊗[ZMod 2] V),
        ψ' (LinearMap.baseChange F8 ((h : CFSG.Quasithin.G11.GLV V) : V →ₗ[ZMod 2] V) x) =
          rhoM (φ' h) (ψ' x) := by
  obtain ⟨φ, ψ, hψ⟩ := hL
  obtain ⟨θ, hθ⟩ := CFSG.Quasithin.G11.Harris.L2.exists_tensorN3_equiv
  let φ' : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) F8 :=
    φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F8).symm
  refine ⟨φ', ψ.trans θ.symm, fun h x => ?_⟩
  apply θ.injective
  have hs : CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F8 (φ' h) = φ h :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F8).apply_symm_apply (φ h)
  have hcoe : (((φ h : ↥(CFSG.Open.StatedSL 2 F8)) : Matrix.GeneralLinearGroup (Fin 2) F8) :
      Matrix (Fin 2) (Fin 2) F8) = (φ' h : Matrix (Fin 2) (Fin 2) F8) := by
    rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 F8 (φ' h), hs]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hψ h x, hθ, LinearEquiv.apply_symm_apply, hcoe]

theorem finrank_range_ne_two_of_mem {H : Subgroup (CFSG.Quasithin.G11.GLV V)}
    (hL : CFSG.Quasithin.G11.IsL28TwistedTensorModule H) {t : CFSG.Quasithin.G11.GLV V}
    (ht : t ∈ H) (ht2 : t * t = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≠ 2 := by
  obtain ⟨φ', ψ', hint⟩ := exists_model_iso hL
  have hhh : (⟨t, ht⟩ : ↥H) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
  have hgg : φ' ⟨t, ht⟩ * φ' ⟨t, ht⟩ = 1 := by
    have := congrArg φ' hhh
    rwa [map_mul, map_one] at this
  have key : (rhoM (φ' ⟨t, ht⟩) - LinearMap.id : Module.End F8 Model) ∘ₗ
      (ψ' : (F8 ⊗[ZMod 2] V) →ₗ[F8] Model) =
      (ψ' : (F8 ⊗[ZMod 2] V) →ₗ[F8] Model) ∘ₗ
        LinearMap.baseChange F8 (t.toLinearMap - LinearMap.id) := by
    refine LinearMap.ext fun x => ?_
    have hx := hint ⟨t, ht⟩ x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe] at hx ⊢
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, LinearMap.baseChange_id,
      LinearMap.id_apply, map_sub, hx]
  have hrank := finrank_range_of_intertwine ψ'
    (LinearMap.baseChange F8 (t.toLinearMap - LinearMap.id))
    (rhoM (φ' ⟨t, ht⟩) - LinearMap.id) key
  have hBC := finrank_range_baseChange_eq (t.toLinearMap - LinearMap.id)
  have hne := finrank_range_ne_two_of_invol (φ' ⟨t, ht⟩) hgg
  rw [← hBC, hrank]
  exact hne

end Transfer

end CFSG.Quasithin.G112A2.Eleven

end

end
