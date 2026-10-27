module

public import CFSG.Quasithin.H13.KGFact22TorSz
public import CFSG.StronglyEmbedded.BenderUnitaryBorel

public section

namespace CFSG.Quasithin.H13.KG22

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.QuasithinUnique
open scoped Matrix LinearAlgebra.Projectivization Pointwise

section Torus

variable {K : Type} [Field K] (J : HermitianForm 3 K)

theorem conj_ne_zero (k : Kˣ) : J.conj (k : K) ≠ 0 :=
  (map_ne_zero J.conj).2 k.ne_zero

@[expose] noncomputable def uT : Kˣ →* GL (Fin 3) K where
  toFun k :=
    { val := !![(J.conj (k : K))⁻¹, 0, 0; 0, J.conj (k : K) * (k : K)⁻¹, 0; 0, 0, (k : K)]
      inv := !![J.conj (k : K), 0, 0; 0, (J.conj (k : K))⁻¹ * (k : K), 0; 0, 0, (k : K)⁻¹]
      val_inv := by
        have h1 := conj_ne_zero J k
        have h2 := k.ne_zero
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h2]
        all_goals field_simp
      inv_val := by
        have h1 := conj_ne_zero J k
        have h2 := k.ne_zero
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h2]
        all_goals field_simp }
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Units.ext
    have h1 := conj_ne_zero J a
    have h2 := conj_ne_zero J b
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, map_mul] <;> ring

theorem coe_uT (k : Kˣ) : ((uT J k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![(J.conj (k : K))⁻¹, 0, 0; 0, J.conj (k : K) * (k : K)⁻¹, 0; 0, 0, (k : K)] :=
  rfl

@[expose] def wGL : GL (Fin 3) K where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem coe_wGL : ((wGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![0, 0, 1; 0, 1, 0; 1, 0, 0] :=
  rfl

theorem wGL_inv : (wGL : GL (Fin 3) K)⁻¹ = wGL :=
  rfl

theorem wGL_conj_uT (k : Kˣ) :
    wGL * uT J k * wGL⁻¹ = uT J (Units.map J.conj.toMonoidHom k)⁻¹ := by
  apply Units.ext
  rw [wGL_inv, Units.val_mul, Units.val_mul, coe_uT, coe_uT, coe_wGL]
  have hc : ∀ x : K, J.conj (J.conj x) = x := J.conj_involutive
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hc, map_inv₀, mul_comm]

variable {J}

theorem uT_mem (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Kˣ) :
    uT J k ∈ J.specialSubgroup := by
  have h1 := conj_ne_zero J k
  have h2 := k.ne_zero
  have hc : ∀ x : K, J.conj (J.conj x) = x := J.conj_involutive
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, coe_uT]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hc, map_inv₀,
        h1, h2]
    all_goals field_simp
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_uT, Matrix.det_fin_three]
    simp [h1, h2]

theorem wGL_mem [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (wGL : GL (Fin 3) K) ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, coe_wGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_wGL, Matrix.det_fin_three]
    simp [CharTwo.neg_eq]

end Torus


section Group

variable {K : Type} [Field K] {J : HermitianForm 3 K}
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

@[expose] noncomputable def uS : Kˣ →* J.specialSubgroup :=
  (uT J).codRestrict _ (uT_mem hJ)

@[expose] noncomputable def uP : Kˣ →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup).comp (uS hJ)

theorem coe_uP (k : Kˣ) :
    ((uP hJ k : ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk (uT J k) :=
  rfl

@[expose] noncomputable def wP [CharP K 2] : ProjectiveSpecialUnitaryMatrixGroup J :=
  Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup ⟨wGL, wGL_mem hJ⟩

theorem coe_wP [CharP K 2] :
    ((wP hJ : ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk wGL :=
  rfl

theorem wP_conj_uP [CharP K 2] (k : Kˣ) :
    wP hJ * uP hJ k * (wP hJ)⁻¹ = uP hJ (Units.map J.conj.toMonoidHom k)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_wP, coe_uP, coe_uP, ← map_inv,
    ← map_mul, ← map_mul, wGL_conj_uT]

@[expose] def fixU (J : HermitianForm 3 K) : Subgroup Kˣ where
  carrier := {k | J.conj (k : K) = k}
  one_mem' := by
    show J.conj ((1 : Kˣ) : K) = ((1 : Kˣ) : K)
    simp
  mul_mem' := by
    intro a b ha hb
    have ha' : J.conj (a : K) = a := ha
    have hb' : J.conj (b : K) = b := hb
    show J.conj ((a * b : Kˣ) : K) = ((a * b : Kˣ) : K)
    rw [Units.val_mul, map_mul, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : J.conj (a : K) = a := ha
    show J.conj ((a⁻¹ : Kˣ) : K) = ((a⁻¹ : Kˣ) : K)
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha']

theorem mem_fixU {k : Kˣ} : k ∈ fixU J ↔ J.conj (k : K) = k :=
  Iff.rfl

@[expose] def normU (J : HermitianForm 3 K) : Subgroup Kˣ where
  carrier := {k | J.conj (k : K) * k = 1}
  one_mem' := by
    show J.conj ((1 : Kˣ) : K) * ((1 : Kˣ) : K) = 1
    simp
  mul_mem' := by
    intro a b ha hb
    have ha' : J.conj (a : K) * a = 1 := ha
    have hb' : J.conj (b : K) * b = 1 := hb
    show J.conj ((a * b : Kˣ) : K) * ((a * b : Kˣ) : K) = 1
    rw [Units.val_mul, map_mul]
    calc J.conj (a : K) * J.conj (b : K) * ((a : K) * b) =
        (J.conj (a : K) * a) * (J.conj (b : K) * b) := by ring
      _ = 1 := by rw [ha', hb', one_mul]
  inv_mem' := by
    intro a ha
    have ha' : J.conj (a : K) * a = 1 := ha
    show J.conj ((a⁻¹ : Kˣ) : K) * ((a⁻¹ : Kˣ) : K) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, ha', inv_one]

theorem mem_normU {k : Kˣ} : k ∈ normU J ↔ J.conj (k : K) * k = 1 :=
  Iff.rfl

theorem exists_fix_mul_norm [CharP K 2] [Finite K] (k : Kˣ) :
    ∃ k₁ ∈ fixU J, ∃ k₂ ∈ normU J, k = k₁ * k₂ := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (J.conj (k : K) * k)
  have hn0 : J.conj (k : K) * k ≠ 0 := mul_ne_zero (conj_ne_zero J k) k.ne_zero
  have hr0 : r ≠ 0 := fun h => hn0 (by rw [hr, h, mul_zero])
  have hc : ∀ x : K, J.conj (J.conj x) = x := J.conj_involutive
  have hσr : J.conj r = r := by
    have h1 : J.conj r * J.conj r = r * r := by
      rw [← map_mul, ← hr, map_mul, hc, mul_comm]
    have h2 : frobenius K 2 (J.conj r) = frobenius K 2 r := by
      rw [frobenius_def, frobenius_def, sq, sq, h1]
    exact frobenius_inj K 2 h2
  set k₁ : Kˣ := Units.mk0 r hr0 with hk₁
  refine ⟨k₁, mem_fixU.2 hσr, k₁⁻¹ * k, mem_normU.2 ?_, by rw [mul_inv_cancel_left]⟩
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hk₁, Units.val_mk0,
    hσr]
  calc r⁻¹ * J.conj (k : K) * (r⁻¹ * k) = (J.conj (k : K) * k) * (r * r)⁻¹ := by ring
    _ = 1 := by rw [← hr, mul_inv_cancel₀ hn0]

theorem card_fixU [Finite K] : Nat.card (fixU J) = Nat.card {x : K // J.conj x = x} - 1 := by
  classical
  let T := {x : K // J.conj x = x}
  let t0 : T := ⟨0, map_zero _⟩
  have e : ↥(fixU J) ≃ {x : T // x ≠ t0} :=
    { toFun := fun k => ⟨⟨((k : Kˣ) : K), k.2⟩, fun h => (k : Kˣ).ne_zero (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨Units.mk0 x.1.1 (fun h => x.2 (Subtype.ext h)), x.1.2⟩
      left_inv := fun k => by
        apply Subtype.ext
        apply Units.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have := Fintype.ofFinite T
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]

end Group

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {J : HermitianForm 3 K}

@[expose] def upImg (K : Type) [Field K] : Set (Matrix.ProjGenLinGroup (Fin 3) K) :=
  {x | ∃ M : GL (Fin 3) K, (M : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular ∧
    x = Matrix.ProjGenLinGroup.mk M}

omit [Finite K] [CharP K 2] in
theorem mul_mem_upImg {x y : Matrix.ProjGenLinGroup (Fin 3) K} (hx : x ∈ upImg K)
    (hy : y ∈ upImg K) : x * y ∈ upImg K := by
  obtain ⟨M, hM, rfl⟩ := hx
  obtain ⟨N, hN, rfl⟩ := hy
  refine ⟨M * N, ?_, (map_mul _ _ _).symm⟩
  rw [Units.val_mul]
  exact hM.mul hN

omit [Finite K] [CharP K 2] in
theorem wGL_not_mem_upImg : Matrix.ProjGenLinGroup.mk (wGL : GL (Fin 3) K) ∉ upImg K := by
  rintro ⟨M, hM, h⟩
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 h.symm
  have h20 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 0) hu
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_wGL] at h20
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, hM (show (0 : Fin 3) < 2 by decide),
    zero_mul] at h20
  simp at h20

theorem torusOut_psu3 {f : ℕ} (hf : 2 ≤ f) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) :
    ∃ S₀ : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      TorusOut (S₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := 2 ^ f
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Ω := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  rcases External.huppert_II_10_12 J q hKcard hfixed hJ with
    ⟨hΩcard, rho, a, _hinj, _hnatural, _hUcard,
      ⟨R, D, hRle, hDle, hN, _hinf, hsup, _hcyc, hRcard,
        _hcomm, _hcommcard, _hDcard, hreg, ⟨coord, hcoord⟩,
        hDcoord, hDsurj⟩, _htwo, _hGcard, _hthree⟩
  let : MulAction G Ω := MulAction.compHom Ω rho
  have hstab : (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho =
      MulAction.stabilizer G a := by
    ext g
    rfl
  have hRle' : R ≤ MulAction.stabilizer G a := hstab ▸ hRle
  have hsup' : R ⊔ D = MulAction.stabilizer G a := hsup.trans hstab
  have hDN : D ≤ Subgroup.normalizer (R : Set G) := hDle.trans hN
  have h3 : ∃ b c : Ω, b ≠ a ∧ c ≠ a ∧ b ≠ c := by
    classical
    have := Fintype.ofFinite Ω
    have hc : Fintype.card Ω = q ^ 3 + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact hΩcard
    have hq : 2 ≤ q := by
      show 2 ≤ 2 ^ f
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 < Fintype.card Ω := by
      have h8 : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
      rw [hc]
      omega
    obtain ⟨b₁, b₂, b₃, h12, h13, h23⟩ := Fintype.two_lt_card_iff.1 h2
    by_cases ha : b₁ = a
    · exact ⟨b₂, b₃, fun h => h12 (ha.trans h.symm), fun h => h13 (ha.trans h.symm), h23⟩
    · by_cases hb : b₂ = a
      · exact ⟨b₁, b₃, ha, fun h => h23 (hb.trans h.symm), h13⟩
      · exact ⟨b₁, b₂, ha, hb, h12⟩
  have hNR : Subgroup.normalizer (R : Set G) ≤ R ⊔ D := by
    rw [hsup']
    exact normalizer_le_stabilizer_of_regular hRle' hreg h3
  have huD : ∀ k : Kˣ, uP hJ k ∈ D := by
    intro k
    obtain ⟨h, M, hM, hhM⟩ := hDsurj k
    have hMk : M = uT J k := Units.ext (by rw [hM, coe_uT])
    have : uP hJ k = (h : G) := Subtype.ext (by rw [coe_uP, ← hMk, hhM])
    rw [this]
    exact h.2
  have hDY : D ≤ (fixU J).map (uP hJ) ⊔ (normU J).map (uP hJ) := by
    intro d hd
    obtain ⟨k, M, hM, hdM⟩ := hDcoord ⟨d, hd⟩
    have hMk : M = uT J k := Units.ext (by rw [hM, coe_uT])
    have hdk : d = uP hJ k := Subtype.ext (by rw [coe_uP, ← hMk, ← hdM])
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := exists_fix_mul_norm (J := J) k
    rw [hdk, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨k₁, hk₁, rfl⟩)
      (Subgroup.mem_sup_right ⟨k₂, hk₂, rfl⟩)
  have hR2 : IsPGroup 2 R :=
    IsPGroup.of_card (n := f * 3) (by simpa only [q, ← pow_mul] using hRcard)
  obtain ⟨P₀, hP₀⟩ := hR2.exists_le_sylow
  have hB := CFSG.Open.bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ
  have hP₀card : Nat.card (P₀ : Subgroup G) = q ^ 3 := (hB P₀).2.2.2.2
  have hRP : R = (P₀ : Subgroup G) := Subgroup.eq_of_le_of_card_ge hP₀ (by rw [hP₀card, hRcard])
  refine ⟨P₀, ?_⟩
  rw [← hRP]
  have hRup : ∀ r ∈ R, (r : Matrix.ProjGenLinGroup (Fin 3) K) ∈ upImg K := by
    intro r hr
    obtain ⟨z, hz⟩ := coord.surjective ⟨r, hr⟩
    obtain ⟨M, hM, hzM⟩ := hcoord z
    refine ⟨M, ?_, ?_⟩
    · intro i j hij
      rw [hM]
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | rfl
    · rw [← hzM, hz]
  have hDup : ∀ d ∈ D, (d : Matrix.ProjGenLinGroup (Fin 3) K) ∈ upImg K := by
    intro d hd
    obtain ⟨k, M, hM, hdM⟩ := hDcoord ⟨d, hd⟩
    refine ⟨M, ?_, hdM⟩
    intro i j hij
    rw [hM]
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | rfl
  have hRDup : ∀ x ∈ R ⊔ D, (x : Matrix.ProjGenLinGroup (Fin 3) K) ∈ upImg K := by
    intro x hx
    have hx' : x ∈ (R : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left R D hDN]
      exact hx
    obtain ⟨r, hr, d, hd, rfl⟩ := Set.mem_mul.1 hx'
    rw [Subgroup.coe_mul]
    exact mul_mem_upImg (hRup r hr) (hDup d hd)
  have hinj : ∀ y ∈ fixU J, uP hJ y = 1 → y = 1 := by
    intro k hk h
    have h1 : Matrix.ProjGenLinGroup.mk (uT J k) = 1 := by
      have := congrArg Subtype.val h
      rwa [coe_uP] at this
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨u, hu⟩ := h1
    have h11 : ((u : Kˣ) : K) = J.conj (k : K) * (k : K)⁻¹ := by
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) hu
      simpa [coe_uT] using this
    have h22 : ((u : Kˣ) : K) = k := by
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 2) hu
      simpa [coe_uT] using this
    have hσ : J.conj (k : K) = k := hk
    rw [hσ, mul_inv_cancel₀ k.ne_zero] at h11
    exact Units.ext (by rw [← h22, h11, Units.val_one])
  refine ⟨(fixU J).map (uP hJ), (normU J).map (uP hJ), wP hJ, ?_, ?_, ?_, isCyclic_map _
    inferInstance, isCyclic_map _ inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact hDN (huD k)
  · rintro _ ⟨k, -, rfl⟩
    exact hDN (huD k)
  · exact hNR.trans (sup_le le_sup_right (hDY.trans le_sup_left))
  · rw [card_map_of_injOn (uP hJ) hinj, card_fixU, hfixed]
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · intro hw
    have := hRDup _ (hNR hw)
    rw [coe_wP] at this
    exact wGL_not_mem_upImg this
  · rintro _ ⟨k, hk, rfl⟩
    have hσ : J.conj (k : K) = k := hk
    have hu : (Units.map J.conj.toMonoidHom k)⁻¹ = k⁻¹ := by
      have : Units.map J.conj.toMonoidHom k = k := Units.ext hσ
      rw [this]
    rw [wP_conj_uP, hu, map_inv]
  · rintro _ ⟨k, hk, rfl⟩
    have hσ : J.conj (k : K) * k = 1 := hk
    have hu : (Units.map J.conj.toMonoidHom k)⁻¹ = k := by
      apply Units.ext
      rw [Units.val_inv_eq_inv_val]
      exact inv_eq_of_mul_eq_one_right hσ
    rw [wP_conj_uP, hu]

theorem torusOut_of_isPSU3 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : IsPSU 3 2 f X) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) : TorusOut S f := by
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := hX
  have hcard : Nat.card K₀ = 2 ^ (2 * f) := by rw [hK₀, ← pow_mul, mul_comm]
  let e₁ : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K₀ (2 ^ f)) := e
  let e₂ : X ≃* CFSG.Open.PSU3 2 f :=
    e₁.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  have : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₃ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = CFSG.Open.PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₄ : ProjectiveSpecialUnitaryMatrixGroup J ≃* CFSG.Open.PSU3 2 f :=
    e₃.trans (MulEquiv.subgroupCongr hmodel)
  refine torusOut_of_equiv (e₂.trans e₄.symm) (fun S' hS' => ?_) hS
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (e₂.trans e₄.symm) (e₂.trans e₄.symm).surjective
  obtain ⟨S₀, hS₀⟩ := torusOut_psu3 hf hJ hKcard hfixed
  exact torusOut_of_sylow S₀ hS₀ hS'

end Main

end CFSG.Quasithin.H13.KG22
