module

public import CFSG.RankThree.GF2n.Smith81.TiD2Module
public import CFSG.RankThree.GF2n.Stroth80.Sec123Order
public import CFSG.RankThree.GF2n.Smith81.Lin31TwoModel
public import CFSG.RankThree.GF2n.Smith81.Lin31TwoWeyl

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

namespace TorusAux

section Alg

variable {F : Type} [Field F]

private theorem omega_mulVec (P : Matrix (Fin 2) (Fin 2) F) (x y : Fin 2 → F) :
    (P *ᵥ x) 0 * (P *ᵥ y) 1 - (P *ᵥ x) 1 * (P *ᵥ y) 0 = P.det * (x 0 * y 1 - x 1 * y 0) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

private theorem omega_vecMul (H : Matrix (Fin 2) (Fin 2) F) (x y : Fin 2 → F) :
    (x ᵥ* H) 0 * (y ᵥ* H) 1 - (x ᵥ* H) 1 * (y ᵥ* H) 0 = H.det * (x 0 * y 1 - x 1 * y 0) := by
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

private theorem eq_of_mulVec_relation {P : Matrix (Fin 2) (Fin 2) F} (hP : P.det = 1)
    {n₀ n₁ : Fin 2 → F} {γ μ σ : F} (h₀ : P *ᵥ n₀ = γ • n₀)
    (h₁ : μ • (P *ᵥ n₁) = n₁ + σ • n₀) (hω : n₀ 0 * n₁ 1 - n₀ 1 * n₁ 0 ≠ 0) : μ = γ := by
  have e1 := omega_mulVec P n₀ n₁
  rw [h₀, hP, one_mul] at e1
  have h10 := congrFun h₁ 0
  have h11 := congrFun h₁ 1
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e1 h10 h11
  set W := n₀ 0 * (P *ᵥ n₁) 1 - n₀ 1 * (P *ᵥ n₁) 0 with hW
  have e2 : μ * W = n₀ 0 * n₁ 1 - n₀ 1 * n₁ 0 := by
    rw [hW]; linear_combination n₀ 0 * h11 - n₀ 1 * h10
  have e3 : γ * W = n₀ 0 * n₁ 1 - n₀ 1 * n₁ 0 := by
    rw [hW]; linear_combination e1
  have hW0 : W ≠ 0 := by
    intro h; rw [h, mul_zero] at e3; exact hω e3.symm
  exact mul_right_cancel₀ hW0 (e2.trans e3.symm)

private theorem eq_of_vecMul_relation {H : Matrix (Fin 2) (Fin 2) F} {u₀ u₁ : Fin 2 → F}
    {γ μ σ : F} (h₀ : u₀ ᵥ* H = μ • u₀) (h₁ : γ • (u₁ ᵥ* H) = u₁ + σ • u₀)
    (hω : u₀ 0 * u₁ 1 - u₀ 1 * u₁ 0 ≠ 0) : μ = γ * H.det := by
  have e1 := omega_vecMul H u₀ u₁
  rw [h₀] at e1
  have h10 := congrFun h₁ 0
  have h11 := congrFun h₁ 1
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e1 h10 h11
  set W := u₀ 0 * (u₁ ᵥ* H) 1 - u₀ 1 * (u₁ ᵥ* H) 0 with hW
  have e2 : γ * W = u₀ 0 * u₁ 1 - u₀ 1 * u₁ 0 := by
    rw [hW]; linear_combination u₀ 0 * h11 - u₀ 1 * h10
  have e3 : μ * W = H.det * (u₀ 0 * u₁ 1 - u₀ 1 * u₁ 0) := by
    rw [hW]; linear_combination e1
  have e4 : μ * (u₀ 0 * u₁ 1 - u₀ 1 * u₁ 0) = γ * H.det * (u₀ 0 * u₁ 1 - u₀ 1 * u₁ 0) := by
    linear_combination γ * e3 - μ * e2
  exact mul_right_cancel₀ hω e4

private theorem vecMulVec_left_cancel {x y u : Fin 2 → F} (hu : u ≠ 0)
    (h : Matrix.vecMulVec x u = Matrix.vecMulVec y u) : x = y := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hu
  funext i
  have := congrFun (congrFun h i) j
  simp only [Matrix.vecMulVec_apply, Pi.zero_apply] at this hj
  exact mul_right_cancel₀ hj this

private theorem vecMulVec_right_cancel {n x y : Fin 2 → F} (hn : n ≠ 0)
    (h : Matrix.vecMulVec n x = Matrix.vecMulVec n y) : x = y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  funext j
  have := congrFun (congrFun h i) j
  simp only [Matrix.vecMulVec_apply, Pi.zero_apply] at this hi
  exact mul_left_cancel₀ hi this

private theorem eq_one_of_mul_mul_eq [CharP F 2] {A B : Matrix (Fin 2) (Fin 2) F}
    (hA : A.det = 1) (h : ∀ X, A * X * B = X) : B = 1 := by
  have hAB : A * B = 1 := by simpa using h 1
  have hBA : B * A = 1 := mul_eq_one_comm.mp hAB
  have hcomm : ∀ X, A * X = X * A := by
    intro X
    calc A * X = A * X * (B * A) := by rw [hBA, Matrix.mul_one]
      _ = A * X * B * A := by simp only [Matrix.mul_assoc]
      _ = X * A := by rw [h X]
  obtain ⟨c, hc⟩ : A ∈ Set.range (Matrix.scalar (Fin 2)) :=
    Matrix.mem_range_scalar_iff_commute_single'.mpr fun i j => (hcomm _).symm
  have hc1 : c = 1 := by
    have hdet : (Matrix.scalar (Fin 2) c).det = c ^ 2 := by
      simp [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, sq]
    rw [hc, hA] at hdet
    have : c ^ 2 = 1 ^ 2 := by rw [← hdet, one_pow]
    exact CharTwo.sq_inj.mp this
  have hA1 : A = 1 := by rw [← hc, hc1]; simp
  simpa [hA1] using hAB

private theorem torus_relation {P H D' : Matrix (Fin 2) (Fin 2) F} (hP : P.det = 1)
    {n₀ u₀ : Fin 2 → F} (hn₀ : n₀ ≠ 0) (hu₀ : u₀ ≠ 0) {γ μ μ' σ : F} (hμ0 : μ ≠ 0)
    (hγ : P *ᵥ n₀ = γ • n₀) (hμ : u₀ ᵥ* H = μ • u₀) (hdet : H.det = μ * μ')
    (hD'0 : D' ≠ 0) (hD'det : D'.det = 0) (hsum : (Matrix.vecMulVec n₀ u₀ + D').det = 0)
    (hline : ∀ c : F, D' ≠ c • Matrix.vecMulVec n₀ u₀)
    (hmat : P * D' * H - D' = σ • Matrix.vecMulVec n₀ u₀) : μ = γ ∨ γ * μ' = 1 := by
  obtain ⟨n₁, u₁, -, -, hD'⟩ := exists_vecMulVec_of_det_eq_zero hD'0 hD'det
  rw [hD', det_vecMulVec_add] at hsum
  rcases mul_eq_zero.mp hsum with hn | hu
  ·
    right
    obtain ⟨c, hc⟩ := D2.exists_smul_of_det_zero hn₀ hn
    have hD'' : D' = Matrix.vecMulVec n₀ (c • u₁) := by
      rw [hD', hc, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
    have hω : u₀ 0 * (c • u₁) 1 - u₀ 1 * (c • u₁) 0 ≠ 0 := by
      intro h0
      obtain ⟨c', hc'⟩ := D2.exists_smul_of_det_zero hu₀ h0
      exact hline c' (by rw [hD'', hc', Matrix.vecMulVec_smul])
    have heq : γ • ((c • u₁) ᵥ* H) = c • u₁ + σ • u₀ := by
      apply vecMulVec_right_cancel hn₀
      have h1 : P * D' * H = Matrix.vecMulVec n₀ (γ • ((c • u₁) ᵥ* H)) := by
        rw [hD'', Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hγ, Matrix.smul_vecMulVec,
          Matrix.vecMulVec_smul]
      rw [← h1, Matrix.vecMulVec_add, Matrix.vecMulVec_smul σ, ← hD'', ← hmat]
      abel
    have h3 := eq_of_vecMul_relation hμ heq hω
    rw [hdet] at h3
    have h4 : μ * (γ * μ') = μ * 1 := by linear_combination -h3
    exact mul_left_cancel₀ hμ0 h4
  ·
    left
    obtain ⟨c, hc⟩ := D2.exists_smul_of_det_zero hu₀ hu
    have hD'' : D' = Matrix.vecMulVec (c • n₁) u₀ := by
      rw [hD', hc, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
    have hω : n₀ 0 * (c • n₁) 1 - n₀ 1 * (c • n₁) 0 ≠ 0 := by
      intro h0
      obtain ⟨c', hc'⟩ := D2.exists_smul_of_det_zero hn₀ h0
      exact hline c' (by rw [hD'', hc', Matrix.smul_vecMulVec])
    have heq : μ • (P *ᵥ (c • n₁)) = c • n₁ + σ • n₀ := by
      apply vecMulVec_left_cancel hu₀
      have h1 : P * D' * H = Matrix.vecMulVec (μ • (P *ᵥ (c • n₁))) u₀ := by
        rw [hD'', Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hμ, Matrix.smul_vecMulVec,
          Matrix.vecMulVec_smul]
      rw [← h1, Matrix.add_vecMulVec, Matrix.smul_vecMulVec σ, ← hD'', ← hmat]
      abel
    exact eq_of_mulVec_relation hP hγ heq hω

end Alg

section Group

variable {G : Type} [Group G] [Finite G] {M Q Z C : Subgroup G}

private theorem comm_mem_sup_of_mem_sup (hC : Ctx M Q Z C) {x : G} (hx : x ∈ Q ⊔ QB C)
    {d : G} (hd : d ∈ Q ⊓ QB C) : ⁅x, d⁆ ∈ Z ⊔ C := by
  have hVD : Z ⊔ C ≤ Q ⊓ QB C := hC.ZB_le_inf
  have key : ∀ y, (y ∈ Q ∨ y ∈ QB C) → ∀ w ∈ Q ⊓ QB C, ⁅y, w⁆ ∈ Z ⊔ C := by
    rintro y (hy | hy) w hw
    · exact (le_sup_left : Z ≤ Z ⊔ C) (comm_mem_Z hC.hyp hy hw.1)
    · exact (le_sup_right : C ≤ Z ⊔ C) (hC.comm_QB_le_B hy hw.2)
  have hnorm : ∀ y, (y ∈ Q ∨ y ∈ QB C) →
      y ∈ Subgroup.normalizer ((Z ⊔ C : Subgroup G) : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have h1 : y * v * y⁻¹ = ⁅y, v⁆ * v := by rw [commutatorElement_def]; group
    rw [h1]
    exact (Z ⊔ C).mul_mem (key y hy v (hVD hv)) hv
  let X' : Subgroup G :=
    { carrier := {y | y ∈ Subgroup.normalizer ((Z ⊔ C : Subgroup G) : Set G) ∧
        ∀ w ∈ Q ⊓ QB C, ⁅y, w⁆ ∈ Z ⊔ C}
      mul_mem' := by
        rintro y₁ y₂ ⟨hn₁, hc₁⟩ ⟨hn₂, hc₂⟩
        refine ⟨Subgroup.mul_mem _ hn₁ hn₂, fun w hw => ?_⟩
        have h1 : ⁅y₁ * y₂, w⁆ = (y₁ * ⁅y₂, w⁆ * y₁⁻¹) * ⁅y₁, w⁆ := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact (Z ⊔ C).mul_mem ((Subgroup.mem_normalizer_iff.mp hn₁ _).mp (hc₂ w hw)) (hc₁ w hw)
      one_mem' := ⟨Subgroup.one_mem _, fun w _ => by
        rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      inv_mem' := by
        rintro y ⟨hn, hc⟩
        refine ⟨Subgroup.inv_mem _ hn, fun w hw => ?_⟩
        have h1 : ⁅y⁻¹, w⁆ = (y⁻¹ * ⁅y, w⁆ * y⁻¹⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact (Z ⊔ C).inv_mem
          ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) _).mp (hc w hw)) }
  have hle : Q ⊔ QB C ≤ X' :=
    sup_le (fun y hy => ⟨hnorm y (Or.inl hy), key y (Or.inl hy)⟩)
      (fun y hy => ⟨hnorm y (Or.inr hy), key y (Or.inr hy)⟩)
  exact (hle hx).2 d hd

private theorem exists_mem_inf_not_mem_sup (hC : Ctx M Q Z C) (hw : Width Q Z 2) :
    ∃ d ∈ Q ⊓ QB C, d ∉ Z ⊔ C := by
  by_contra hcon
  push Not at hcon
  have h1 := Subgroup.card_le_of_le (show Q ⊓ QB C ≤ Z ⊔ C from fun d hd => hcon d hd)
  have h2 : Nat.card ↥(Z ⊔ C) = Nat.card Z ^ 2 := by
    rw [sup_comm, hC.card_sup_Z]
    obtain ⟨g, hg⟩ := hC.conj
    rw [hg, card_conjSubgroup, sq]
  have h3 := hC.card_LB_mul hw
  have h4 := hC.card_LB_lt_of_width_two hw
  have hZ : 0 < Nat.card Z ^ 2 := pow_pos Nat.card_pos 2
  rw [h2] at h1
  have h5 : Nat.card (LB M Q C) * Nat.card ↥(Q ⊓ QB C) < Nat.card Q * Nat.card Z ^ (2 * 2) := by
    calc Nat.card (LB M Q C) * Nat.card ↥(Q ⊓ QB C) ≤ Nat.card (LB M Q C) * Nat.card Z ^ 2 :=
          Nat.mul_le_mul_left _ h1
      _ < Nat.card Q * Nat.card Z ^ 2 * Nat.card Z ^ 2 := Nat.mul_lt_mul_of_pos_right h4 hZ
      _ = Nat.card Q * Nat.card Z ^ (2 * 2) := by ring
  rw [h3] at h5
  exact lt_irrefl _ h5

end Group

section Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {TM : TensorModel M Q Z B}

private theorem conj_mem_Q (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ Q) :
    m * x * m⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx

private theorem exists_phi_eq (g : Matrix (Fin 2) (Fin 2) TM.F) (hg : g.det = 1) :
    ∃ s : ↥(Lgen M (LB M Q B)), (TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) = g := by
  have hmem : Matrix.GeneralLinearGroup.mkOfDetNeZero g (by rw [hg]; exact one_ne_zero) ∈
      TM.φ.range := by
    rw [TM.φ_range]
    exact StatedAPI.mem_statedSL_iff.mpr (by simpa using hg)
  obtain ⟨s, hs⟩ := hmem
  exact ⟨s, by rw [hs]; rfl⟩

private theorem exists_matrix_form (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M)
    (T : TM.M₀.E ≃ₗ[TM.K] TM.M₀.E)
    (hTπ : ∀ x ∈ Q, TM.M₀.π (t * x * t⁻¹) = T (TM.M₀.π x)) :
    ∃ P H : Matrix (Fin 2) (Fin 2) TM.F, P.det = 1 ∧ IsUnit H.det ∧
      ∀ e, TM.Φ (T e) = P * TM.Φ e * H := by
  set T' : Matrix (Fin 2) (Fin 2) TM.F →+ Matrix (Fin 2) (Fin 2) TM.F :=
    (TM.Φ.symm.trans (T.toAddEquiv.trans TM.Φ)).toAddMonoidHom
  have hT'_apply : ∀ X, T' X = TM.Φ (T (TM.Φ.symm X)) := fun X => rfl
  have hbij : Function.Bijective T' := (TM.Φ.symm.trans (T.toAddEquiv.trans TM.Φ)).bijective
  have hlin : ∀ (c : TM.F) X, T' (c • X) = c • T' X := by
    intro c X
    obtain ⟨k, rfl⟩ := TM.ε.surjective c
    rw [hT'_apply, hT'_apply]
    have h1 : TM.Φ.symm (TM.ε k • X) = k • TM.Φ.symm X := by
      rw [AddEquiv.symm_apply_eq, TM.smul, AddEquiv.apply_symm_apply]
    rw [h1, map_smul, TM.smul]
  have hT : ∀ g : Matrix (Fin 2) (Fin 2) TM.F, g.det = 1 →
      ∃ g' : Matrix (Fin 2) (Fin 2) TM.F, ∀ X, T' (g * X) = g' * T' X := by
    intro g hg
    obtain ⟨s, hs⟩ := exists_phi_eq (TM := TM) g hg
    have hsM : (s : G) ∈ M := hc.Lgen_le_M s.2
    have hs' : t * (s : G) * t⁻¹ ∈ Lgen M (LB M Q B) :=
      (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) htM) _).mp s.2
    refine ⟨(TM.φ ⟨_, hs'⟩ : Matrix (Fin 2) (Fin 2) TM.F), fun X => ?_⟩
    obtain ⟨x, hxQ, hx⟩ := TM.M₀.π_surj (TM.Φ.symm X)
    have hX : X = TM.Φ (TM.M₀.π x) := by rw [hx, AddEquiv.apply_symm_apply]
    rw [hX, hT'_apply, hT'_apply, AddEquiv.symm_apply_apply, ← hs, ← TM.act s x hxQ,
      AddEquiv.symm_apply_apply, ← hTπ _ (conj_mem_Q hc hsM hxQ), ← hTπ _ hxQ,
      ← TM.act ⟨_, hs'⟩ _ (conj_mem_Q hc htM hxQ)]
    have e : t * ((s : G) * x * (s : G)⁻¹) * t⁻¹ =
        (t * (s : G) * t⁻¹) * (t * x * t⁻¹) * (t * (s : G) * t⁻¹)⁻¹ := by group
    rw [e]
  obtain ⟨P₀, H₀, hP₀, hH₀, hform⟩ := exists_mul_mul_of_intertwine T' hbij hlin hT
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' P₀.det
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [mul_zero] at hr; exact hP₀.ne_zero hr
  refine ⟨r⁻¹ • P₀, r • H₀, ?_, ?_, fun e => ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, hr, ← sq, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hr0)]
  · rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hr0)).mul hH₀
  · have := hform (TM.Φ e)
    rw [hT'_apply, AddEquiv.symm_apply_apply] at this
    rw [this]
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hr0]

private theorem mem_Gamma_of_form (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M)
    {P : Matrix (Fin 2) (Fin 2) TM.F} (hP : P.det = 1) {H : GL (Fin 2) TM.F}
    (hform : ∀ x ∈ Q, TM.Φ (TM.M₀.π (t * x * t⁻¹)) =
      P * TM.Φ (TM.M₀.π x) * (H : Matrix (Fin 2) (Fin 2) TM.F)) : H ∈ TM.Gamma := by
  obtain ⟨st, hst⟩ := exists_phi_eq (TM := TM) P hP
  have hstM : (st : G) ∈ M := hc.Lgen_le_M st.2
  set h := t * (st : G)⁻¹ with hh
  have hhM : h ∈ M := M.mul_mem htM (M.inv_mem hstM)
  have hact : ∀ x ∈ Q, TM.Φ (TM.M₀.π (h * x * h⁻¹)) =
      TM.Φ (TM.M₀.π x) * (H : Matrix (Fin 2) (Fin 2) TM.F) := by
    intro x hx
    have hy : (st : G)⁻¹ * x * (st : G) ∈ Q := by
      simpa using conj_mem_Q hc (M.inv_mem hstM) hx
    have e : h * x * h⁻¹ = t * ((st : G)⁻¹ * x * (st : G)) * t⁻¹ := by rw [hh]; group
    have h1 := TM.act st⁻¹ x hx
    simp only [Subgroup.coe_inv, inv_inv, map_inv] at h1
    rw [e, hform _ hy, h1, ← Matrix.mul_assoc, ← hst, Units.mul_inv, Matrix.one_mul]
  have hinvact : ∀ y ∈ Q, TM.Φ (TM.M₀.π (h⁻¹ * y * h)) =
      TM.Φ (TM.M₀.π y) * ((H⁻¹ : GL (Fin 2) TM.F) : Matrix (Fin 2) (Fin 2) TM.F) := by
    intro y hy
    have h1 := hact _ (by simpa using conj_mem_Q hc (M.inv_mem hhM) hy)
    rw [show h * (h⁻¹ * y * h) * h⁻¹ = y by group] at h1
    rw [h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨h, hhM, hc.hyp.Q_normal.2 hhM, fun s' hs' => ?_, hact⟩
  have hs'M : s' ∈ M := hc.Lgen_le_M hs'
  have hkM : ⁅h, s'⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hhM hs'M) (M.inv_mem hhM)) (M.inv_mem hs'M)
  refine mem_Q_of_pi_conj_eq (M₀ := TM.M₀) hc.hyp hkM fun x hx => ?_
  apply TM.Φ.injective
  have hx₁ : s'⁻¹ * x * s' ∈ Q := by simpa using conj_mem_Q hc (M.inv_mem hs'M) hx
  have hx₂ : h⁻¹ * (s'⁻¹ * x * s') * h ∈ Q := by
    simpa using conj_mem_Q hc (M.inv_mem hhM) hx₁
  have e : ⁅h, s'⁆ * x * ⁅h, s'⁆⁻¹ =
      h * (s' * (h⁻¹ * (s'⁻¹ * x * s') * h) * s'⁻¹) * h⁻¹ := by
    rw [commutatorElement_def]; group
  have a1 := TM.act ⟨s', hs'⟩ _ hx₂
  have a2 := TM.act ⟨s', hs'⟩⁻¹ x hx
  simp only [Subgroup.coe_inv, inv_inv, map_inv] at a1 a2
  rw [e, hact _ (conj_mem_Q hc hs'M hx₂), a1, hinvact _ hx₁, a2]
  simp only [Matrix.mul_assoc, Units.inv_mul, Units.mul_inv_cancel_left, Matrix.mul_one]

private theorem pow_orderOf_eq_one_of_form (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M)
    {P H : Matrix (Fin 2) (Fin 2) TM.F} (hP : P.det = 1)
    (hform : ∀ x ∈ Q, TM.Φ (TM.M₀.π (t * x * t⁻¹)) = P * TM.Φ (TM.M₀.π x) * H) :
    H ^ orderOf t = 1 := by
  have hpow : ∀ n : ℕ, ∀ x ∈ Q,
      TM.Φ (TM.M₀.π (t ^ n * x * (t ^ n)⁻¹)) = P ^ n * TM.Φ (TM.M₀.π x) * H ^ n := by
    intro n
    induction n with
    | zero => intro x hx; simp
    | succ n ih =>
      intro x hx
      have e : t ^ (n + 1) * x * (t ^ (n + 1))⁻¹ = t * (t ^ n * x * (t ^ n)⁻¹) * t⁻¹ := by
        group
      rw [e, hform _ (conj_mem_Q hc (M.pow_mem htM n) hx), ih x hx, pow_succ', pow_succ]
      simp only [Matrix.mul_assoc]
  refine eq_one_of_mul_mul_eq (A := P ^ orderOf t) (by rw [Matrix.det_pow, hP, one_pow])
    fun X => ?_
  obtain ⟨x, hx, hxX⟩ := TM.M₀.π_surj (TM.Φ.symm X)
  have h1 := hpow (orderOf t) x hx
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, hxX, AddEquiv.apply_symm_apply] at h1
  exact h1.symm

end Model

end TorusAux

section Torus

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace TensorModel

variable {TM : TensorModel M Q Z B}

theorem torus_lemma_full (hc : Ctx M Q Z B) (hw : Width Q Z 2) {C : Subgroup G}
    (hC : Ctx M Q Z C) {u₀ : Fin 2 → TM.F} (hu₀ : u₀ ≠ 0) (hCu : C ≤ TM.plane u₀) :
    ∃ (H : GL (Fin 2) TM.F) (μ : TM.F), H ∈ TM.Gamma ∧ Odd (orderOf H) ∧
      (∀ c : TM.F, (H : Matrix (Fin 2) (Fin 2) TM.F) ≠ Matrix.scalar (Fin 2) c) ∧
      Matrix.vecMul u₀ (H : Matrix (Fin 2) (Fin 2) TM.F) = μ • u₀ ∧
      orderOf (H : Matrix (Fin 2) (Fin 2) TM.F).det = Nat.card TM.F - 1 ∧
      (μ * μ * (H : Matrix (Fin 2) (Fin 2) TM.F).det = 1 ∨ μ = 1) := by
  obtain ⟨t, T, a, ℓ, htM, htX, htodd, -, haord, hTπ, hTQ, -, hTℓ, haℓ⟩ :=
    exists_torus_full TM.gm hC
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one, TM.gm.card] at haord
    have := hc.hyp.q4
    omega
  obtain ⟨P, H, hP, hH, hform⟩ := TorusAux.exists_matrix_form (TM := TM) hc htM T hTπ
  have hformQ : ∀ x ∈ Q, TM.Φ (TM.M₀.π (t * x * t⁻¹)) = P * TM.Φ (TM.M₀.π x) * H :=
    fun x hx => by rw [hTπ x hx, hform]
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (by rw [hP]; exact isUnit_one)
  have hHu : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hH
  obtain ⟨b, hb0, hbQ, hbline, -, -⟩ := hC.dictB TM.gm
  obtain ⟨c₁, hc₁C, hc₁Q, hc₁b⟩ := (hbline b).mpr ⟨1, (one_smul _ b).symm⟩
  obtain ⟨n₀, hn₀⟩ := (TensorModel.mem_plane.mp (hCu hc₁C)).2
  rw [hc₁b] at hn₀
  have hn₀0 : n₀ ≠ 0 := by
    rintro rfl
    apply hb0
    apply TM.Φ.injective
    rw [hn₀, map_zero]
    simp
  have hTb : T b = ℓ • b := by
    rw [← hc₁b, ← hTπ c₁ hc₁Q]
    exact hTℓ c₁ hc₁C
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl; rw [mul_zero] at haℓ; exact zero_ne_one haℓ
  have hrel : Matrix.vecMulVec (P *ᵥ n₀) (u₀ ᵥ* H) = TM.ε ℓ • Matrix.vecMulVec n₀ u₀ := by
    have := hform b
    rw [hTb, TM.smul, hn₀, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul] at this
    exact this.symm
  have hPn₀ : P *ᵥ n₀ ≠ 0 := fun h =>
    hn₀0 (Matrix.mulVec_injective_of_isUnit hPu (by rw [h, Matrix.mulVec_zero]))
  have hu₀H : u₀ ᵥ* H ≠ 0 := fun h =>
    hu₀ (Matrix.vecMul_injective_of_isUnit hHu (by
      show u₀ ᵥ* H = 0 ᵥ* H
      rw [h, Matrix.zero_vecMul]))
  obtain ⟨γ, μ, hγ, hμ, hγμ⟩ :=
    vecMulVec_eq_smul_iff hPn₀ hu₀H hn₀0 hu₀ ((map_ne_zero TM.ε).mpr hℓ0) hrel
  have hdetH : H.det = TM.ε a := by
    have h1 := hform (TM.Φ.symm 1)
    have h2 := TM.qf (T (TM.Φ.symm 1))
    rw [hTQ, map_mul, TM.qf, AddEquiv.apply_symm_apply, Matrix.det_one, mul_one, h1,
      Matrix.det_mul, Matrix.det_mul, hP, AddEquiv.apply_symm_apply, Matrix.det_one, one_mul,
      one_mul] at h2
    exact h2.symm
  have hdetH1 : H.det ≠ 1 := by
    rw [hdetH]
    intro h
    exact ha1 (TM.ε.injective (h.trans (map_one TM.ε).symm))
  have hV : H.det * (γ * μ) = 1 := by
    rw [hγμ, hdetH, ← map_mul, haℓ, map_one]
  have hμ0 : μ ≠ 0 := by
    rintro rfl; rw [mul_zero, mul_zero] at hV; exact zero_ne_one hV
  have hγ0 : γ ≠ 0 := by
    rintro rfl; rw [zero_mul, mul_zero] at hV; exact zero_ne_one hV
  obtain ⟨μ', hμ'⟩ : ∃ μ' : TM.F, μ' = H.det / μ := ⟨_, rfl⟩
  have hμ'0 : μ' ≠ 0 := by rw [hμ']; exact div_ne_zero hH.ne_zero hμ0
  have hδμ : H.det = μ * μ' := by rw [hμ']; field_simp
  obtain ⟨d, hdD, hdV⟩ := TorusAux.exists_mem_inf_not_mem_sup hC hw
  have hdQ : d ∈ Q := hdD.1
  have hel := hC.inf_QB_elemAbelian
  have hQfd : TM.M₀.Qf (TM.M₀.π d) = 0 :=
    (Tim79.QuadModel.sq_iff_Qf TM.M₀ TM.gm.reg hdQ).mp (hel.2 d hdD)
  have hdetD : (TM.Φ (TM.M₀.π d)).det = 0 := by rw [← TM.qf, hQfd, map_zero]
  have hline : ∀ c : TM.F, TM.Φ (TM.M₀.π d) ≠ c • Matrix.vecMulVec n₀ u₀ := by
    intro c hcd
    obtain ⟨k, rfl⟩ := TM.ε.surjective c
    have hk : TM.M₀.π d = k • b := by
      apply TM.Φ.injective
      rw [hcd, TM.smul, hn₀]
    have h1 : TM.M₀.π d ∈ TM.M₀.img (Z ⊔ C) :=
      Tim79.QuadModel.img_mono TM.M₀ le_sup_right ((hbline _).mpr ⟨k, hk⟩)
    exact hdV ((Tim79.QuadModel.mem_img_iff TM.M₀ le_sup_left hdQ).mp h1)
  have hD'0 : TM.Φ (TM.M₀.π d) ≠ 0 := by
    intro h
    apply hline 0
    rw [h, zero_smul]
  have hcomm : c₁ * d = d * c₁ := by
    have := hel.1.is_comm.comm ⟨c₁, hC.ZB_le_inf (le_sup_right (a := Z) hc₁C)⟩ ⟨d, hdD⟩
    exact congrArg Subtype.val this
  have hBbd : TM.M₀.B b (TM.M₀.π d) = 0 := by
    rw [← hc₁b]
    exact (Tim79.QuadModel.comm_iff_B TM.M₀ TM.gm.reg hc₁Q hdQ).mp hcomm
  have hsum : (Matrix.vecMulVec n₀ u₀ + TM.Φ (TM.M₀.π d)).det = 0 := by
    rw [← hn₀, ← map_add, ← TM.qf, TM.M₀.Qf_add, hbQ, hQfd, hBbd, add_zero, add_zero, map_zero]
  have hlift : Z ⊔ C ≤ TM.M₀.lift (TM.M₀.img C) := by
    refine sup_le (fun z hz => ?_) (fun x hx => ?_)
    · have hzQ : z ∈ Q := hC.hyp.Z_normal.1 hz
      refine Tim79.QuadModel.mem_lift.mpr ⟨hzQ, ?_⟩
      rw [(TM.M₀.π_ker z hzQ).mpr hz]
      exact (TM.M₀.img C).zero_mem
    · exact Tim79.QuadModel.mem_lift.mpr
        ⟨hC.le hx, Tim79.QuadModel.pi_mem_img TM.M₀ hx (hC.le hx)⟩
  obtain ⟨s, hs⟩ := (hbline _).mp
    (Tim79.QuadModel.mem_lift.mp (hlift (TorusAux.comm_mem_sup_of_mem_sup hC htX hdD))).2
  have hTd : T (TM.M₀.π d) - TM.M₀.π d = s • b := by
    rw [← hs, commutatorElement_def,
      TM.M₀.π_mul _ (TorusAux.conj_mem_Q hc htM hdQ) _ (Q.inv_mem hdQ),
      Tim79.QuadModel.pi_inv TM.M₀ hdQ, hTπ d hdQ, sub_eq_add_neg]
  have hmat : P * TM.Φ (TM.M₀.π d) * H - TM.Φ (TM.M₀.π d) =
      TM.ε s • Matrix.vecMulVec n₀ u₀ := by
    rw [← hform, ← map_sub, hTd, TM.smul, hn₀]
  have hD := TorusAux.torus_relation hP hn₀0 hu₀ hμ0 hγ hμ hδμ hD'0 hdetD hsum hline hmat
  have hne : μ ≠ μ' := ne_of_torus_relations hγ0 hμ0 hμ'0 hδμ hdetH1 hV hD
  have hnsc : ∀ c : TM.F, H ≠ Matrix.scalar (Fin 2) c := by
    intro c hcH
    have h1 : u₀ ᵥ* H = c • u₀ := by
      rw [hcH]
      ext i
      simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
    have hcμ : μ = c := smul_left_injective TM.F hu₀ (hμ.symm.trans h1)
    have hdet : H.det = c ^ 2 := by
      rw [hcH]
      simp [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, sq]
    apply hne
    rw [hδμ, ← hcμ, sq] at hdet
    exact (mul_left_cancel₀ hμ0 hdet).symm
  let Hgl : GL (Fin 2) TM.F := Matrix.GeneralLinearGroup.mk'' H hH
  have hHgl : (Hgl : Matrix (Fin 2) (Fin 2) TM.F) = H := rfl
  have hHglr : Hgl ^ orderOf t = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hHgl, TorusAux.pow_orderOf_eq_one_of_form hc htM hP hformQ,
      Units.val_one]
  have hdetHord : orderOf (Hgl : Matrix (Fin 2) (Fin 2) TM.F).det = Nat.card TM.F - 1 := by
    rw [hHgl]
    have h1 : orderOf (TM.ε a) = orderOf a :=
      orderOf_injective TM.ε.toMulEquiv.toMonoidHom TM.ε.injective a
    rw [hdetH, h1, haord]
    rw [Nat.card_congr TM.ε.toEquiv]
  refine ⟨Hgl, μ, TorusAux.mem_Gamma_of_form hc htM hP hformQ,
    Odd.of_dvd_nat htodd (orderOf_dvd_of_pow_eq_one hHglr), hnsc, hμ, hdetHord, ?_⟩
  rcases hD with hD | hD
  · left
    rw [hHgl]
    rw [← hD] at hV
    simpa [mul_comm] using hV
  · right
    have hμμ : μ * μ = 1 := by
      have h2 : μ * μ' * γ * μ = 1 := by
        rw [← hV, hδμ]
        ring
      have h3 : μ * μ' * γ * μ = μ * μ := by
        calc μ * μ' * γ * μ = μ * (μ' * γ) * μ := by ring
          _ = μ * 1 * μ := by rw [mul_eq_one_comm.mp hD]
          _ = μ * μ := by ring
      rwa [h3] at h2
    exact CharTwo.sq_inj.mp (by rw [sq, one_pow]; exact hμμ)

theorem torus_lemma (hc : Ctx M Q Z B) (hw : Width Q Z 2) {C : Subgroup G} (hC : Ctx M Q Z C)
    {u₀ : Fin 2 → TM.F} (hu₀ : u₀ ≠ 0) (hCu : C ≤ TM.plane u₀) :
    ∃ (H : GL (Fin 2) TM.F) (μ : TM.F), H ∈ TM.Gamma ∧ Odd (orderOf H) ∧
      (∀ c : TM.F, (H : Matrix (Fin 2) (Fin 2) TM.F) ≠ Matrix.scalar (Fin 2) c) ∧
      Matrix.vecMul u₀ (H : Matrix (Fin 2) (Fin 2) TM.F) = μ • u₀ := by
  obtain ⟨H, μ, hHΓ, hHodd, hHns, hHeig, -, -⟩ :=
    torus_lemma_full hc hw hC hu₀ hCu
  exact ⟨H, μ, hHΓ, hHodd, hHns, hHeig⟩

end TensorModel

end Torus

end CFSG.RankThree.GF2n.Smith81
