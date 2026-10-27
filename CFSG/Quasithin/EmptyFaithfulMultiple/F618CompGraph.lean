module

public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompL3

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace F618Comp

open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

theorem centralizer_le_of_isExtendedByMatrixMap {W : Type*} [Group W]
    {H Z₀ : Subgroup (GL (Fin 3) K)} [(Z₀.subgroupOf H).Normal]
    (hZ₀ : Z₀ ≤ StatedScalars (Fin 3) K)
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hα : ∀ A ∈ H, ∃ B ∈ H,
      (B : Matrix (Fin 3) (Fin 3) K) = ((A : Matrix (Fin 3) (Fin 3) K)⁻¹)ᵀ)
    {C : GL (Fin 3) K} (hC : C ∈ H)
    (htr : (Matrix.trace ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 ≠
      (Matrix.trace (C : Matrix (Fin 3) (Fin 3) K)) ^ 3)
    {N : Subgroup W} (e : ↥N ≃* ↥H ⧸ Z₀.subgroupOf H) (t : W) (g : ↥H) (hidx : N.index = 2)
    (htN : t ∉ N)
    (hact : ∀ (n m : ↥N) (A B : ↥H), (m : W) = t * n * t⁻¹ →
      e n = (QuotientGroup.mk A : ↥H ⧸ Z₀.subgroupOf H) →
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (fun A : Matrix (Fin 3) (Fin 3) K => (A⁻¹)ᵀ)
            ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (((g : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
      e m = (QuotientGroup.mk B : ↥H ⧸ Z₀.subgroupOf H)) :
    Subgroup.centralizer (N : Set W) ≤ N := by
  intro x hx
  by_contra hxN
  rw [Subgroup.mem_centralizer_iff] at hx
  have hn₀ : t⁻¹ * x ∈ N := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false (fun h => htN (by simpa using N.inv_mem h)) hxN
  set n₀ : ↥N := ⟨t⁻¹ * x, hn₀⟩
  obtain ⟨A₀, hA₀⟩ := QuotientGroup.mk_surjective (e n₀)
  set c₀ : ↥H := ⟨C, hC⟩
  set n : ↥N := e.symm (QuotientGroup.mk c₀)
  set A : ↥H := A₀ * c₀ * A₀⁻¹
  have hen' : e (n₀ * n * n₀⁻¹) = (QuotientGroup.mk A : ↥H ⧸ Z₀.subgroupOf H) := by
    rw [map_mul, map_mul, map_inv, ← hA₀, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨U, hU, hUeq⟩ := hα _ A.2
  set B : ↥H := g * ⟨U, hU⟩ * g⁻¹
  have hB : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (fun A : Matrix (Fin 3) (Fin 3) K => (A⁻¹)ᵀ)
          ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((g : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simp only [B, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [hUeq]
  have hm : (n : W) = t * ((n₀ * n * n₀⁻¹ : ↥N) : W) * t⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, n₀]
    calc (n : W) = x * n * x⁻¹ := by rw [← hx _ n.2]; group
      _ = t * (t⁻¹ * x * n * (t⁻¹ * x)⁻¹) * t⁻¹ := by group
  have hen := hact _ n A B hm hen' hB
  rw [MulEquiv.apply_symm_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hen
  obtain ⟨u, hu⟩ := hZ₀ hen
  have hu3 : (u : K) ^ 3 = 1 := by
    have hd := hdet _ (c₀⁻¹ * B).2
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar] at hd
    simpa [Matrix.det_diagonal, Matrix.scalar_apply] using hd
  have hBC : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (u : K) • (C : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : ((B : GL (Fin 3) K)) = C * Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
      rw [hu]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, c₀]
      group
    rw [h1, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, mul_comm]
  have htrB : Matrix.trace ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.trace ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hB, Matrix.trace_units_conj, Matrix.trace_transpose, ← Matrix.coe_units_inv]
    have : ((A : GL (Fin 3) K))⁻¹ = (A₀ : GL (Fin 3) K) * C⁻¹ * (A₀ : GL (Fin 3) K)⁻¹ := by
      simp only [A, Subgroup.coe_mul, Subgroup.coe_inv, c₀]
      group
    rw [this, Units.val_mul, Units.val_mul, Matrix.trace_units_conj]
  apply htr
  rw [← htrB, hBC, Matrix.trace_smul, smul_eq_mul, mul_pow, hu3, one_mul]

theorem socle_of_isExtendedByMatrixMap {W : Type*} [Group W]
    {H Z₀ : Subgroup (GL (Fin 3) K)} [(Z₀.subgroupOf H).Normal]
    (h : F6.IsExtendedByMatrixMap H Z₀ (fun A => (A⁻¹)ᵀ) W)
    (hZ₀ : Z₀ ≤ StatedScalars (Fin 3) K)
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hα : ∀ A ∈ H, ∃ B ∈ H,
      (B : Matrix (Fin 3) (Fin 3) K) = ((A : Matrix (Fin 3) (Fin 3) K)⁻¹)ᵀ)
    {C : GL (Fin 3) K} (hC : C ∈ H)
    (htr : (Matrix.trace ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 ≠
      (Matrix.trace (C : Matrix (Fin 3) (Fin 3) K)) ^ 3)
    (hgood : GoodQuasi (↥H ⧸ Z₀.subgroupOf H)) : Socle W := by
  obtain ⟨N, e, t, g, hidx, htN, hact⟩ := h
  have hCN := centralizer_le_of_isExtendedByMatrixMap hZ₀ hdet hα hC htr e t g hidx htN hact
  have hgN : GoodQuasi ↥N := hgood.of_mulEquiv e
  exact Or.inr ⟨N, goodSocle_of_centralizer_le (Subgroup.normal_of_index_eq_two hidx) hgN.1 hCN
    hgN.2 hgN.3⟩

noncomputable def quotientBotSubgroupOf (H : Subgroup (GL (Fin 3) K)) :
    ↥H ⧸ (⊥ : Subgroup (GL (Fin 3) K)).subgroupOf H ≃* ↥H :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf H)).trans QuotientGroup.quotientBot

@[expose] def compMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 1]

@[expose] def compInvMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; -1, 0, 1; 1, 0, 0]

theorem det_compMat : (compMat K).det = 1 := by
  simp [compMat, Matrix.det_fin_three]

theorem compInvMat_mul : compInvMat K * compMat K = 1 := by
  rw [compInvMat, compMat, Matrix.mul_fin_three, Matrix.one_fin_three]
  simp

@[expose] noncomputable def compGL (K : Type) [Field K] : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (compMat K) (by rw [det_compMat]; exact one_ne_zero)

theorem coe_compGL : ((compGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = compMat K :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem coe_compGL_inv :
    (((compGL K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = compInvMat K := by
  rw [Matrix.coe_units_inv, coe_compGL]
  exact Matrix.inv_eq_left_inv compInvMat_mul

theorem compGL_mem_statedSL : compGL K ∈ StatedSL 3 K :=
  mem_statedSL_of_det (by rw [coe_compGL, det_compMat])

theorem trace_compGL_ne :
    (Matrix.trace (((compGL K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 ≠
      (Matrix.trace ((compGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 := by
  rw [coe_compGL_inv, coe_compGL]
  simp [compMat, compInvMat, Matrix.trace_fin_three]

theorem transposeInv_mem_statedSL {A : GL (Fin 3) K} (hA : A ∈ StatedSL 3 K) :
    ∃ B ∈ StatedSL 3 K,
      (B : Matrix (Fin 3) (Fin 3) K) = ((A : Matrix (Fin 3) (Fin 3) K)⁻¹)ᵀ := by
  have hd : (((A : Matrix (Fin 3) (Fin 3) K)⁻¹)ᵀ).det = 1 := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, det_eq_one_of_mem_statedSL hA,
      Ring.inverse_one]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by rw [hd]; exact one_ne_zero),
    mem_statedSL_of_det (by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hd]),
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩

@[expose] def monoMat (c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; -c⁻¹, 0, 0; 0, 0, c]

@[expose] def monoInvMat (c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, -c, 0; 1, 0, 0; 0, 0, c⁻¹]

theorem det_monoMat {c : K} (hc : c ≠ 0) : (monoMat c).det = 1 := by
  simp [monoMat, Matrix.det_fin_three, hc]

theorem monoInvMat_mul {c : K} (hc : c ≠ 0) : monoInvMat c * monoMat c = 1 := by
  rw [monoInvMat, monoMat, Matrix.mul_fin_three, Matrix.one_fin_three]
  simp [hc]

@[expose] noncomputable def monoGL {c : K} (hc : c ≠ 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (monoMat c) (by rw [det_monoMat hc]; exact one_ne_zero)

theorem coe_monoGL {c : K} (hc : c ≠ 0) :
    ((monoGL hc : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = monoMat c :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem coe_monoGL_inv {c : K} (hc : c ≠ 0) :
    (((monoGL hc)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = monoInvMat c := by
  rw [Matrix.coe_units_inv, coe_monoGL]
  exact Matrix.inv_eq_left_inv (monoInvMat_mul hc)

theorem trace_monoMat (c : K) : Matrix.trace (monoMat c) = c := by
  simp [monoMat, Matrix.trace_fin_three]

theorem trace_monoInvMat (c : K) : Matrix.trace (monoInvMat c) = c⁻¹ := by
  simp [monoInvMat, Matrix.trace_fin_three]

theorem trace_monoGL_ne {c : K} (hc : c ≠ 0) (h6 : c ^ 6 ≠ 1) :
    (Matrix.trace (((monoGL hc)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 ≠
      (Matrix.trace ((monoGL hc : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 := by
  rw [coe_monoGL_inv, coe_monoGL, trace_monoMat, trace_monoInvMat]
  intro h
  apply h6
  have h3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc
  calc c ^ 6 = c ^ 3 * c ^ 3 := by ring
    _ = c ^ 3 * c⁻¹ ^ 3 := by rw [h]
    _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]

section Unitary

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_pow_succ_eq_one (hK : Nat.card K = p ^ 2) (hp3 : 3 ≤ p) (hp5 : p ≠ 5) :
    ∃ c : K, c ^ (p + 1) = 1 ∧ c ^ 6 ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hζ
  have hpp : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    have h1 : 1 ≤ p := by omega
    zify [h1, Nat.one_le_pow 2 p h1]
    ring
  refine ⟨((ζ ^ (p - 1) : Kˣ) : K), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul, hpp, ← hζ, pow_orderOf_eq_one, Units.val_one]
  · intro h
    have h' : ζ ^ ((p - 1) * 6) = 1 := by
      apply Units.ext
      rw [pow_mul, Units.val_pow_eq_pow_val, h, Units.val_one]
    rw [← orderOf_dvd_iff_pow_eq_one, hζ, ← hpp] at h'
    have hd : p + 1 ∣ 6 := Nat.dvd_of_mul_dvd_mul_left (by omega) h'
    have hp6 : p ≤ 5 := by have := Nat.le_of_dvd (by norm_num) hd; omega
    interval_cases p <;> omega

theorem monoGL_mem_statedSU (hK : Nat.card K = p ^ 2) {c : K} (hc : c ≠ 0)
    (hc1 : c ^ (p + 1) = 1) : monoGL hc ∈ StatedSU 3 p K := by
  rw [mem_statedSU_iff hK, coe_monoGL]
  refine ⟨det_monoMat hc, ?_⟩
  have hσ : frobenius K p c = c⁻¹ := by
    rw [frobenius_def]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hc1])
  have hmap : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution K p 1) (monoMat c) = monoInvMat c := by
    rw [CFSG.LieType.Universal.Unitary.conjTr]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [monoMat, monoInvMat, hσ]
  rw [hmap, monoInvMat_mul hc]

theorem transposeInv_mem_statedSU (hK : Nat.card K = p ^ 2) {A : GL (Fin 3) K}
    (hA : A ∈ StatedSU 3 p K) :
    ∃ B ∈ StatedSU 3 p K,
      (B : Matrix (Fin 3) (Fin 3) K) = ((A : Matrix (Fin 3) (Fin 3) K)⁻¹)ᵀ := by
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K p 1
  obtain ⟨hdet, huni⟩ := (mem_statedSU_iff hK A).mp hA
  have hinv : (A : Matrix (Fin 3) (Fin 3) K)⁻¹ =
      CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin 3) (Fin 3) K) :=
    Matrix.inv_eq_left_inv huni
  have hmap : ((A : Matrix (Fin 3) (Fin 3) K)⁻¹)ᵀ = (A : Matrix (Fin 3) (Fin 3) K).map σ := by
    rw [hinv, CFSG.LieType.Universal.Unitary.conjTr, Matrix.transpose_transpose]
  have hd : ((A : Matrix (Fin 3) (Fin 3) K).map σ).det = 1 := by
    have := RingHom.map_det (σ : K →+* K) (A : Matrix (Fin 3) (Fin 3) K)
    rw [hdet, map_one, RingHom.mapMatrix_apply] at this
    exact this.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by rw [hd]; exact one_ne_zero), ?_,
    by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hmap]⟩
  rw [mem_statedSU_iff hK, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  refine ⟨hd, ?_⟩
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have hinvol : ((A : Matrix (Fin 3) (Fin 3) K).map σ).map σ = (A : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    simp only [Matrix.map_apply]
    exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hK1 _
  rw [CFSG.LieType.Universal.Unitary.conjTr, hinvol]
  have := congrArg Matrix.transpose huni
  rwa [CFSG.LieType.Universal.Unitary.conjTr, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_one] at this

end Unitary

theorem socle_of_isSLEps3GraphExt {D : Type} [Group D] {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (h : F6.IsSLEps3GraphExt p D) : Socle D := by
  obtain ⟨hp, K, _, _, h⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rcases hp8 with h | h <;> omega
  have hp3 : 3 ≤ p := by rcases hp8 with h | h <;> omega
  rcases h with ⟨-, hK, h | h⟩ | ⟨hp4, hK, h | h⟩
  · have : CharP K p := charP_of_card (f := 1) (by rw [pow_one]; exact hK)
    exact socle_of_isExtendedByMatrixMap h bot_le (fun _ hA => det_eq_one_of_mem_statedSL hA)
      (fun _ hA => transposeInv_mem_statedSL hA) compGL_mem_statedSL trace_compGL_ne
      ((goodQuasi_statedSL (two_ne_zero_of_charP hp hp2)).1.of_mulEquiv
        (quotientBotSubgroupOf _))
  · have : CharP K p := charP_of_card (f := 1) (by rw [pow_one]; exact hK)
    exact socle_of_isExtendedByMatrixMap h le_rfl (fun _ hA => det_eq_one_of_mem_statedSL hA)
      (fun _ hA => transposeInv_mem_statedSL hA) compGL_mem_statedSL trace_compGL_ne
      (goodQuasi_statedSL (two_ne_zero_of_charP hp hp2)).2
  · have : CharP K p := charP_of_card hK
    obtain ⟨c, hc1, hc6⟩ := exists_pow_succ_eq_one hK hp3 (by rcases hp8 with h | h <;> omega)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hc1
      exact zero_ne_one hc1
    exact socle_of_isExtendedByMatrixMap h bot_le
      (fun A hA => ((mem_statedSU_iff hK A).mp hA).1) (fun _ hA => transposeInv_mem_statedSU hK hA)
      (monoGL_mem_statedSU hK hc0 hc1) (trace_monoGL_ne hc0 hc6)
      ((goodQuasi_statedSU hp2 hK).1.of_mulEquiv (quotientBotSubgroupOf _))
  · have : CharP K p := charP_of_card hK
    obtain ⟨c, hc1, hc6⟩ := exists_pow_succ_eq_one hK hp3 (by rcases hp8 with h | h <;> omega)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hc1
      exact zero_ne_one hc1
    exact socle_of_isExtendedByMatrixMap h le_rfl
      (fun A hA => ((mem_statedSU_iff hK A).mp hA).1) (fun _ hA => transposeInv_mem_statedSU hK hA)
      (monoGL_mem_statedSU hK hc0 hc1) (trace_monoGL_ne hc0 hc6) (goodQuasi_statedSU hp2 hK).2

end F618Comp

end CFSG.Quasithin.EmptyFaithfulMultiple
