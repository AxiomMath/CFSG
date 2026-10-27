module

public import CFSG.Quasithin.Background.HSU3Borel
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin

namespace H

namespace L3Nine

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix SU3
open scoped Matrix

abbrev HMod (n : ℕ) (K : Type) [Field K] [CharP K 2] : Type := ↥(hermSub n (Fin 3) K)

section Module

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

abbrev mat (X : HMod n K) : Matrix (Fin 3) (Fin 3) K :=
  Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 3) (Fin 3) K))

theorem mat_injective : Function.Injective (mat (n := n) (K := K)) := fun _ _ h =>
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem mat_mul (X Y : HMod n K) : mat (X * Y) = mat X + mat Y := rfl

theorem mat_one : mat (1 : HMod n K) = 0 := rfl

theorem mat_inv (X : HMod n K) : mat X⁻¹ = -mat X := rfl

end Module

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem frobPow_eq_conjM (A : Matrix (Fin 3) (Fin 3) K) : frobPow n A = conjM n A := by
  rw [conjM_eq_map_pow]
  rfl

theorem herm_mat (X : HMod n K) : (conjM n (mat X))ᵀ = mat X := by
  rw [← frobPow_eq_conjM]
  exact X.2

theorem herm_apply (X : HMod n K) (i j : Fin 3) : bar n (mat X j i) = mat X i j := by
  have h := congrFun (congrFun (herm_mat X) i) j
  simpa [conjM, Matrix.transpose_apply] using h

@[expose] def mkH (A : Matrix (Fin 3) (Fin 3) K) (hA : (conjM n A)ᵀ = A) : HMod n K :=
  ⟨Multiplicative.ofAdd A, by rw [mem_hermSub, toAdd_ofAdd, frobPow_eq_conjM]; exact hA⟩

theorem mat_mkH (A : Matrix (Fin 3) (Fin 3) K) (hA : (conjM n A)ᵀ = A) :
    mat (mkH A hA) = A := rfl

@[expose] noncomputable def tw (n : ℕ) (A X : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K :=
  A * X * (conjM n A)ᵀ

theorem tw_tw (A B X : Matrix (Fin 3) (Fin 3) K) : tw n A (tw n B X) = tw n (A * B) X := by
  simp only [tw, conjM_mul, transpose_mul, Matrix.mul_assoc]

theorem tw_one (X : Matrix (Fin 3) (Fin 3) K) : tw n 1 X = X := by
  simp [tw, conjM_one]

theorem tw_add (A X Y : Matrix (Fin 3) (Fin 3) K) : tw n A (X + Y) = tw n A X + tw n A Y := by
  simp [tw, Matrix.mul_add, Matrix.add_mul]

theorem tw_smul (A X : Matrix (Fin 3) (Fin 3) K) (c : K) : tw n A (c • X) = c • tw n A X := by
  simp [tw]

theorem herm_tw (hK : Nat.card K = (2 ^ n) ^ 2) (A : Matrix (Fin 3) (Fin 3) K)
    {X : Matrix (Fin 3) (Fin 3) K} (hX : (conjM n X)ᵀ = X) : (conjM n (tw n A X))ᵀ = tw n A X := by
  rw [tw, conjM_mul, conjM_mul, conjM_transpose, conjM_conjM hK, transpose_mul, transpose_mul,
    transpose_transpose, hX, Matrix.mul_assoc]

@[expose] noncomputable def twAut (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K) :
    MulAut (HMod n K) where
  toFun X := mkH (tw n (A : Matrix (Fin 3) (Fin 3) K) (mat X)) (herm_tw hK _ (herm_mat X))
  invFun X := mkH (tw n ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (mat X))
    (herm_tw hK _ (herm_mat X))
  left_inv X := mat_injective (by
    simp only [mat_mkH]
    rw [tw_tw, ← Units.val_mul, inv_mul_cancel, Units.val_one, tw_one])
  right_inv X := mat_injective (by
    simp only [mat_mkH]
    rw [tw_tw, ← Units.val_mul, mul_inv_cancel, Units.val_one, tw_one])
  map_mul' X Y := mat_injective (by
    simp only [mat_mkH, mat_mul]
    exact tw_add _ _ _)

@[expose] noncomputable def rhoT (hK : Nat.card K = (2 ^ n) ^ 2) :
    GL (Fin 3) K →* MulAut (HMod n K) where
  toFun := twAut hK
  map_one' := MulEquiv.ext fun X => mat_injective (by
    change tw n ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (mat X) = mat X
    rw [Units.val_one, tw_one])
  map_mul' A B := MulEquiv.ext fun X => mat_injective (by
    change tw n ((A * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (mat X) =
      tw n (A : Matrix (Fin 3) (Fin 3) K) (tw n (B : Matrix (Fin 3) (Fin 3) K) (mat X))
    rw [tw_tw, Units.val_mul])

theorem mat_rhoT (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K) (X : HMod n K) :
    mat (rhoT hK A X) = tw n (A : Matrix (Fin 3) (Fin 3) K) (mat X) := rfl

@[expose] noncomputable def rho (hK : Nat.card K = (2 ^ n) ^ 2) :
    SpecialLinearGroup (Fin 3) K →* MulAut (HMod n K) :=
  (rhoT hK).comp SpecialLinearGroup.toGL

theorem mat_rho (hK : Nat.card K = (2 ^ n) ^ 2) (g : SpecialLinearGroup (Fin 3) K)
    (X : HMod n K) : mat (rho hK g X) = tw n (g : Matrix (Fin 3) (Fin 3) K) (mat X) := rfl

noncomputable abbrev img (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  (rho hK).range

noncomputable abbrev norm (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  Subgroup.normalizer (img hK : Set (MulAut (HMod n K)))

theorem img_eq_map (hK : Nat.card K = (2 ^ n) ^ 2) : img hK = (StatedSL 3 K).map (rhoT hK) := by
  rw [img, rho, MonoidHom.range_comp, statedSL_eq_range_toGL]

theorem rhoT_mem_img (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K).det = 1) : rhoT hK A ∈ img hK :=
  ⟨(⟨A, hA⟩ : SpecialLinearGroup (Fin 3) K), by
    show rhoT hK (SpecialLinearGroup.toGL ⟨A, hA⟩) = rhoT hK A
    congr 1
    exact Units.ext rfl⟩

theorem bar_map (φ : K ≃+* K) (x : K) : bar n (φ x) = φ (bar n x) := by
  rw [bar_apply, bar_apply, map_pow]

theorem conjM_map (φ : K ≃+* K) (A : Matrix (Fin 3) (Fin 3) K) :
    conjM n (A.map φ) = (conjM n A).map φ := by
  ext i j
  simp [conjM, bar_map]

theorem herm_map (φ : K ≃+* K) {X : Matrix (Fin 3) (Fin 3) K} (hX : (conjM n X)ᵀ = X) :
    (conjM n (X.map φ))ᵀ = X.map φ := by
  rw [conjM_map, ← transpose_map, hX]

@[expose] noncomputable def fldAut (φ : K ≃+* K) : MulAut (HMod n K) where
  toFun X := mkH ((mat X).map φ) (herm_map φ (herm_mat X))
  invFun X := mkH ((mat X).map φ.symm) (herm_map φ.symm (herm_mat X))
  left_inv X := mat_injective (by
    simp only [mat_mkH, Matrix.map_map]
    ext i j
    simp)
  right_inv X := mat_injective (by
    simp only [mat_mkH, Matrix.map_map]
    ext i j
    simp)
  map_mul' X Y := mat_injective (by
    simp only [mat_mkH, mat_mul]
    exact Matrix.map_add _ (map_add φ) _ _)

theorem mat_fldAut (φ : K ≃+* K) (X : HMod n K) : mat (fldAut φ X) = (mat X).map φ := rfl

theorem fldAut_mul (φ ψ : K ≃+* K) : fldAut (n := n) (φ * ψ) = fldAut φ * fldAut ψ :=
  MulEquiv.ext fun X => mat_injective (by
    change (mat X).map (φ * ψ) = ((mat X).map ψ).map φ
    rw [Matrix.map_map]
    rfl)

theorem fldAut_one : fldAut (n := n) (1 : K ≃+* K) = 1 :=
  MulEquiv.ext fun X => mat_injective (by
    change (mat X).map (1 : K ≃+* K) = mat X
    ext i j
    rfl)

@[expose] noncomputable def fldHom : (K ≃+* K) →* MulAut (HMod n K) where
  toFun := fldAut
  map_one' := fldAut_one
  map_mul' := fldAut_mul

theorem fldHom_apply (φ : K ≃+* K) : fldHom (n := n) φ = fldAut φ := rfl

@[expose] noncomputable def mapGL (φ : K ≃+* K) : GL (Fin 3) K →* GL (Fin 3) K :=
  Units.map ((φ.toRingHom.mapMatrix : Matrix (Fin 3) (Fin 3) K →+* Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 3) (Fin 3) K)

omit [Finite K] [CharP K 2] in
theorem coe_mapGL (φ : K ≃+* K) (A : GL (Fin 3) K) :
    ((mapGL φ A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K).map φ := rfl

omit [Finite K] [CharP K 2] in
theorem det_mapGL (φ : K ≃+* K) (A : GL (Fin 3) K) :
    ((mapGL φ A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      φ (A : Matrix (Fin 3) (Fin 3) K).det := by
  rw [coe_mapGL]
  exact (RingHom.map_det φ.toRingHom _).symm

theorem tw_map (φ : K ≃+* K) (A X : Matrix (Fin 3) (Fin 3) K) :
    (tw n A X).map φ = tw n (A.map φ) (X.map φ) := by
  rw [tw, tw, Matrix.map_mul, Matrix.map_mul, transpose_map, ← conjM_map]

theorem fldAut_mul_rhoT (hK : Nat.card K = (2 ^ n) ^ 2) (φ : K ≃+* K) (A : GL (Fin 3) K) :
    fldAut φ * rhoT hK A = rhoT hK (mapGL φ A) * fldAut φ :=
  MulEquiv.ext fun X => mat_injective (by
    rw [MulAut.mul_apply, MulAut.mul_apply]
    change (tw n (A : Matrix (Fin 3) (Fin 3) K) (mat X)).map φ =
      tw n ((A : Matrix (Fin 3) (Fin 3) K).map φ) ((mat X).map φ)
    exact tw_map φ _ _)

theorem fldAut_conj_rhoT (hK : Nat.card K = (2 ^ n) ^ 2) (φ : K ≃+* K) (A : GL (Fin 3) K) :
    fldAut φ * rhoT hK A * (fldAut φ)⁻¹ = rhoT hK (mapGL φ A) := by
  rw [fldAut_mul_rhoT, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_norm_eq (hK : Nat.card K = (2 ^ n) ^ 2) {c : K} (hc : bar n c = c)
    (hc0 : c ≠ 0) : ∃ l : Kˣ, (l : K) * bar n (l : K) = c := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (2 ^ n) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = Units.mk0 c hc0 := by
    have hm := hg (Units.mk0 c hc0)
    rw [← mem_powers_iff_mem_zpowers] at hm
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, hk⟩
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hcq : (Units.mk0 c hc0) ^ (2 ^ n - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have h1 : c ^ 2 ^ n = c := by rw [← bar_apply]; exact hc
    have h2 : c ^ (2 ^ n - 1) * c = c * 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, h1, mul_one]
    exact mul_right_cancel₀ hc0 (h2.trans (mul_comm c 1))
  have hdvd : (2 ^ n) ^ 2 - 1 ∣ k * (2 ^ n - 1) := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hk, hcq]
  have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    have : (2 ^ n) ^ 2 = (2 ^ n + 1) * (2 ^ n - 1) + 1 := by
      zify [hq1]
      ring
    omega
  rw [hfac] at hdvd
  have hpos : 0 < 2 ^ n - 1 ∨ 2 ^ n - 1 = 0 := by omega
  obtain ⟨j, hj⟩ : 2 ^ n + 1 ∣ k := by
    rcases hpos with hpos | hzero
    · exact Nat.dvd_of_mul_dvd_mul_right hpos hdvd
    ·
      have : 2 ^ n = 1 := by omega
      have hK1 : Nat.card K = 1 := by rw [hK, this]; rfl
      exact absurd hK1 (Finite.one_lt_card).ne'
  refine ⟨g ^ j, ?_⟩
  have h1 : ((g ^ j : Kˣ) : K) * bar n ((g ^ j : Kˣ) : K) = ((g ^ k : Kˣ) : K) := by
    rw [bar_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_add, hj]
    congr 1
    ring
  rw [h1, hk, Units.val_mk0]

@[expose] noncomputable def scalGL (l : Kˣ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) l

omit [Finite K] [CharP K 2] in
theorem coe_scalGL (l : Kˣ) :
    ((scalGL l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (l : K) • 1 := by
  simp [scalGL, Matrix.smul_one_eq_diagonal]

theorem mat_rhoT_scalGL (hK : Nat.card K = (2 ^ n) ^ 2) (l : Kˣ) (X : HMod n K) :
    mat (rhoT hK (scalGL l) X) = ((l : K) * bar n (l : K)) • mat X := by
  rw [mat_rhoT, coe_scalGL, tw]
  have h1 : conjM n ((l : K) • (1 : Matrix (Fin 3) (Fin 3) K)) = bar n (l : K) • 1 := by
    ext i j
    by_cases h : i = j <;> simp [conjM, h]
  rw [h1, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]

theorem card_HMod (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card (HMod n K) = 2 ^ (9 * n) := by
  classical
  let Fq := {b : K // bar n b = b}
  let e : HMod n K ≃ (Fq × Fq × Fq) × (K × K × K) :=
    { toFun := fun X => ((⟨mat X 0 0, herm_apply X 0 0⟩, ⟨mat X 1 1, herm_apply X 1 1⟩,
          ⟨mat X 2 2, herm_apply X 2 2⟩), (mat X 0 1, mat X 0 2, mat X 1 2))
      invFun := fun p => mkH !![p.1.1.1, p.2.1, p.2.2.1; bar n p.2.1, p.1.2.1.1, p.2.2.2;
          bar n p.2.2.1, bar n p.2.2.2, p.1.2.2.1] (by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [conjM, bar_bar hK, p.1.1.2, p.1.2.1.2, p.1.2.2.2])
      left_inv := fun X => mat_injective (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [herm_apply, mat_mkH])
      right_inv := fun p => by
        simp only [mat_mkH]
        rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod]
  change Nat.card Fq * (Nat.card Fq * Nat.card Fq) *
    (Nat.card K * (Nat.card K * Nat.card K)) = _
  rw [card_fixed hn hK, hK]
  ring

theorem exists_model {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (h : (FFModel.twistTensor n (StatedSL 3 K)).Realizes H ⊤ ⊥) :
    ∃ e : V ≃* HMod n K, H.map (congrHom e) = img hK := by
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(hermSub n (Fin 3) K) ⧸
      (⊥ : Subgroup (Multiplicative (Matrix (Fin 3) (Fin 3) K))).subgroupOf
        (hermSub n (Fin 3) K) ≃* HMod n K :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot
  let e : V ≃* HMod n K :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans q
  have hqs : ∀ x, x = (QuotientGroup.mk (q x) : ↥(hermSub n (Fin 3) K) ⧸
      (⊥ : Subgroup (Multiplicative (Matrix (Fin 3) (Fin 3) K))).subgroupOf
        (hermSub n (Fin 3) K)) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have he : ∀ (γ : ↥(StatedSL 3 K)) (v : V),
      e (((π γ : ↥H) : MulAut V) v) = rhoT hK (γ : GL (Fin 3) K) (e v) := by
    intro γ v
    have hact : (FFModel.twistTensor n (StatedSL 3 K)).act γ
        ((e v : HMod n K) : Multiplicative (Matrix (Fin 3) (Fin 3) K)) =
        ((rhoT hK (γ : GL (Fin 3) K) (e v) : HMod n K) :
          Multiplicative (Matrix (Fin 3) (Fin 3) K)) := by
      change Multiplicative.ofAdd (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mat (e v) *
          (frobPow n ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ) =
        Multiplicative.ofAdd (tw n ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (mat (e v)))
      rw [frobPow_eq_conjM]
      rfl
    have hm : (FFModel.twistTensor n (StatedSL 3 K)).act γ
        ((e v : HMod n K) : Multiplicative (Matrix (Fin 3) (Fin 3) K)) ∈
          (FFModel.twistTensor n (StatedSL 3 K)).sec := by
      rw [hact]
      exact (rhoT hK (γ : GL (Fin 3) K) (e v)).2
    have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk (e v) := hqs _
    have h2 := hβe γ ⟨v, trivial⟩ (e v) trivial hm h1
    have h3 := congrArg q h2
    refine h3.trans (Subtype.ext ?_)
    exact hact
  have hpair : ∀ γ : ↥(StatedSL 3 K),
      congrHom e ((π γ : ↥H) : MulAut V) = rhoT hK (γ : GL (Fin 3) K) := fun γ =>
    MulEquiv.ext fun w => by
      show e (((π γ : ↥H) : MulAut V) (e.symm w)) = rhoT hK (γ : GL (Fin 3) K) w
      rw [he, MulEquiv.apply_symm_apply]
  refine ⟨e, ?_⟩
  rw [img_eq_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    refine ⟨Subtype.val (p := fun A => A ∈ StatedSL 3 K) γ, γ.2, ?_⟩
    rw [← hpair γ, hγ]
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨_, (π ⟨γ, hγ⟩).2, hpair ⟨γ, hγ⟩⟩

theorem exists_transport {V : Type*} [CommGroup V] {L X : Subgroup (MulAut V)}
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (hL : (FFModel.twistTensor n (StatedSL 3 K)).Realizes L ⊤ ⊥) (hLX : L ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    ∃ e : V ≃* HMod n K, img hK ≤ X.map (congrHom e) ∧ X.map (congrHom e) ≤ norm hK := by
  obtain ⟨e, he⟩ := exists_model hK hL
  refine ⟨e, he ▸ Subgroup.map_mono hLX, ?_⟩
  have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) =
      Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut (HMod n K))) :
        Set (MulAut (HMod n K))) :=
    Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
  rw [norm, ← he, ← h1]
  exact Subgroup.map_mono hXN

end L3Nine

end H

end CFSG.Quasithin
