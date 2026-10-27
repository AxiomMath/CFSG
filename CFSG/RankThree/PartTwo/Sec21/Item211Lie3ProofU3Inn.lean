module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSU2
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Minus
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
import CFSG.Quasithin.EmptyFaithful.E22SUFrame
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedProj)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open scoped MatrixGroups Matrix

namespace Item211Lie3Proof

open Item211Lie2Proof

section Unitary

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def sZeroGL : GL (Fin 3) K :=
  blockGL (-1)

theorem coe_sZeroGL :
    ((sZeroGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![-1, -1, 1] :=
  coe_blockGL_neg_one

@[expose] def swapZeroTwo : GL (Fin 3) K :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

@[expose] def swapOneTwo : GL (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem swapZeroTwo_mem :
    (swapZeroTwo : GL (Fin 3) K) ∈ primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3) := by
  rw [mem_primeFormUnitary]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapZeroTwo, CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem swapOneTwo_mem :
    (swapOneTwo : GL (Fin 3) K) ∈ primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3) := by
  rw [mem_primeFormUnitary]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapOneTwo, CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem exists_unitary_frame_sZero (hp2 : p ≠ 2) {X₀ : unitarySU p f K 3} (hX₀2 : X₀ ^ 2 = 1)
    (hX₀1 : X₀ ≠ 1) :
    ∃ g : GL (Fin 3) K, g ∈ primeFormUnitary h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3) ∧
      g * (X₀ : GL (Fin 3) K) * g⁻¹ = sZeroGL := by
  classical
  have hK2 := CFSG.Quasithin.E22S.two_ne_zero_of_unitaryFieldData h hp2
  have hne1 : (-1 : K) ≠ 1 := fun h' => hK2 (by linear_combination -h')
  set A := Subgroup.zpowers (X₀ : StatedProj (unitarySU p f K 3)) with hA
  have hAe : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨m, rfl⟩⟩ := a
      obtain ⟨_, ⟨n, rfl⟩⟩ := b
      simp only [Subgroup.coe_mul]
      rw [← zpow_add, ← zpow_add, add_comm]
    · rintro _ ⟨m, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← QuotientGroup.mk_pow,
        hX₀2, QuotientGroup.mk_one, one_zpow]
  have hxA : X₀ ∈ CFSG.Quasithin.E22S.invLiftsU A hAe := ⟨Subgroup.mem_zpowers _, hX₀2⟩
  obtain ⟨g, hgU, hg⟩ := CFSG.Quasithin.E22S.exists_unitary_frame h hp2 hAe
  have hX₀2' : (X₀ : GL (Fin 3) K) ^ 2 = 1 := by simpa using congrArg Subtype.val hX₀2
  have hd := CFSG.Quasithin.E22S.conjU_eq_diagonal (hg X₀ hxA)
  have hsq : ∀ i, CFSG.Quasithin.E22S.dgU g X₀ i * CFSG.Quasithin.E22S.dgU g X₀ i = 1 :=
    fun i => CFSG.Quasithin.E22S.dgU_sq (hg X₀ hxA) hX₀2' i
  have hprod := CFSG.Quasithin.E22S.dgU_prod (hg X₀ hxA)
    (CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU X₀.2)
  rw [Fin.prod_univ_three] at hprod
  set d := CFSG.Quasithin.E22S.dgU g X₀ with hd_def
  have hperm : ∀ P : GL (Fin 3) K, P ∈ primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3) → P * P = 1 →
      ((P : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d * (P : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal ![-1, -1, 1]) →
      ∃ g : GL (Fin 3) K, g ∈ primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3) ∧
        g * (X₀ : GL (Fin 3) K) * g⁻¹ = sZeroGL := by
    intro P hPU hPP hPd
    refine ⟨P * g, mul_mem hPU hgU, ?_⟩
    have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hPP).symm
    apply Units.ext
    rw [coe_sZeroGL, mul_inv_rev, hPinv,
      show P * g * (X₀ : GL (Fin 3) K) * (g⁻¹ * P) = P * (g * X₀ * g⁻¹) * P by group,
      Units.val_mul, Units.val_mul, hd]
    exact hPd
  rcases mul_self_eq_one_iff.mp (hsq 0) with h0 | h0 <;>
    rcases mul_self_eq_one_iff.mp (hsq 1) with h1 | h1 <;>
    rcases mul_self_eq_one_iff.mp (hsq 2) with h2 | h2 <;>
    rw [h0, h1, h2] at hprod
  · exfalso
    apply hX₀1
    have h1' : g * (X₀ : GL (Fin 3) K) * g⁻¹ = 1 := by
      apply Units.ext
      rw [hd, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [d, h0, h1, h2]
    apply Subtype.ext
    calc (X₀ : GL (Fin 3) K) = g⁻¹ * (g * X₀ * g⁻¹) * g := by group
      _ = 1 := by rw [h1']; group
  · exact absurd (by linear_combination hprod) hne1
  · exact absurd (by linear_combination hprod) hne1
  · refine hperm swapZeroTwo (swapZeroTwo_mem h) (Units.ext ?_) ?_
    · rw [Units.val_mul, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapZeroTwo, Matrix.mul_apply, Fin.sum_univ_three]
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;> simp [swapZeroTwo, d, h0, h1, h2]
  · exact absurd (by linear_combination hprod) hne1
  · refine hperm swapOneTwo (swapOneTwo_mem h) (Units.ext ?_) ?_
    · rw [Units.val_mul, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapOneTwo, Matrix.mul_apply, Fin.sum_univ_three]
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;> simp [swapOneTwo, d, h0, h1, h2]
  · refine ⟨g, hgU, Units.ext ?_⟩
    rw [hd, coe_sZeroGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d, h0, h1, h2]
  · exact absurd (by linear_combination hprod) hne1

omit h in
theorem isBlock_of_commute_sZeroGL (hK2 : (2 : K) ≠ 0) {N : GL (Fin 3) K}
    (hN : N * sZeroGL = sZeroGL * N) : Item211Lie2Proof.IsBlock (N : Matrix (Fin 3) (Fin 3) K) := by
  apply isBlock_of_commute hK2
  rw [coe_sZero, ← coe_sZeroGL, ← Units.val_mul, ← Units.val_mul, hN]

omit h in
theorem apply_two_two_ne_zero_of_isBlock {N : GL (Fin 3) K}
    (hb : Item211Lie2Proof.IsBlock (N : Matrix (Fin 3) (Fin 3) K)) :
    (N : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
  intro h0
  have hdet := ((Matrix.isUnit_iff_isUnit_det _).mp N.isUnit).ne_zero
  rw [det_of_isBlock hb, h0, mul_zero] at hdet
  exact hdet rfl

omit h in
theorem isBlockScalar_of_commute_witnesses {M : Matrix (Fin 3) (Fin 3) K}
    (hM : Item211Lie2Proof.IsBlock M) {l l' : K} (hll' : l' ≠ l)
    (h1 : M * blockMat !![l, 0; 0, l'] = blockMat !![l, 0; 0, l'] * M)
    (h2 : M * blockMat !![0, 1; -1, 0] = blockMat !![0, 1; -1, 0] * M) : IsBlockScalar M := by
  have e1 := congrFun (congrFun h1 0) 1
  have e2 := congrFun (congrFun h1 1) 0
  have e3 := congrFun (congrFun h2 0) 1
  simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three] at e1 e2 e3
  have hll : l' - l ≠ 0 := sub_ne_zero.mpr hll'
  refine ⟨hM, ?_, ?_, ?_⟩
  · have : M 0 1 * (l' - l) = 0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_right hll
  · have : M 1 0 * (l' - l) = 0 := by linear_combination -e2
    exact (mul_eq_zero.mp this).resolve_right hll
  · linear_combination e3

theorem diag_mem_unitarySU_two {l : Kˣ} (hl : h.bar (l : K) * l = 1) :
    (⟨!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)], !![((l⁻¹ : Kˣ) : K), 0; 0, (l : K)],
      by ext i j; fin_cases i <;> fin_cases j <;> simp,
      by ext i j; fin_cases i <;> fin_cases j <;> simp⟩ : GL (Fin 2) K) ∈ unitarySU p f K 2 := by
  rw [mem_unitarySU_iff h]
  refine ⟨by simp [Matrix.det_fin_two], ?_⟩
  have hl' : (h.bar (l : K))⁻¹ * (l : K)⁻¹ = 1 := by
    rw [← mul_inv, hl, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hl, hl']

include h in
theorem J_mem_unitarySU_two :
    (⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩ :
      GL (Fin 2) K) ∈ unitarySU p f K 2 := by
  rw [mem_unitarySU_iff h]
  refine ⟨by simp [Matrix.det_fin_two], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_norm_one_sq_ne_one (hq : 2 < p ^ f) :
    ∃ l : Kˣ, h.bar (l : K) * l = 1 ∧ (l : K) * l ≠ 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨l, hl, hlo⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq hK
  refine ⟨l, ?_, ?_⟩
  · rw [UnitaryFieldData.bar_apply, ← CFSG.LieType.BorelTits.unitaryInvolution_apply]
    exact hl
  · intro h2
    have hl2 : l ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, sq, h2, Units.val_one])
    have := orderOf_dvd_of_pow_eq_one hl2
    rw [hlo] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem unitaryProj_eq_one_iff {g : unitarySU p f K 3} :
    unitaryProj h 3 g = 1 ↔
      ∃ c : Kˣ, (g : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  rw [← map_one (unitaryProj h 3), eq_comm, Item211Lie2Proof.unitaryProj_eq_iff h]
  simp

theorem eq_bot_of_le_inn_unitaryPSU (hp3 : 3 < p)
    {D T V W : Subgroup (MulAut (unitaryPSU h 3))}
    (hD9 : Nat.card D = 9) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTD : T ≤ Subgroup.centralizer (D : Set (MulAut (unitaryPSU h 3))))
    (hTi : T ≤ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range)
    (hnab : ¬ ∀ a ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range ⊓
        Subgroup.centralizer (T : Set (MulAut (unitaryPSU h 3))),
      ∀ b ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range ⊓
        Subgroup.centralizer (T : Set (MulAut (unitaryPSU h 3))), a * b = b * a)
    (hVi : V ≤ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range)
    (hV2 : IsPGroup 2 V) (hDV : D ≤ Subgroup.normalizer (V : Set (MulAut (unitaryPSU h 3))))
    (hVD : ⁅V, D⁆ = V) (hW2 : IsPGroup 2 W) (hVW : V ≤ W)
    (hWT : W ≤ Subgroup.centralizer (T : Set (MulAut (unitaryPSU h 3))))
    (hτ : ∀ τ ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range ⊓
        Subgroup.centralizer (T : Set (MulAut (unitaryPSU h 3))),
      τ ^ 3 = 1 → τ ∈ Subgroup.normalizer (W : Set (MulAut (unitaryPSU h 3)))) : V = ⊥ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hf := h.one_le
  have hpq : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hq4 : 4 ≤ p ^ f := by omega
  have hq2 : 2 < p ^ f := by omega
  have := h.finite
  have hK2 := CFSG.Quasithin.E22S.two_ne_zero_of_unitaryFieldData h hp2
  have : Finite (MulAut (unitaryPSU h 3)) :=
    Finite.of_injective (fun σ : MulAut (unitaryPSU h 3) => (σ : unitaryPSU h 3 → _))
      (fun a b h' => MulEquiv.ext (congrFun h'))
  have hZ := Item211Lie2Proof.center_unitaryPSU_three_eq_bot h hq2
  have hinj := conj_injective' hZ
  set G := unitarySU p f K 3 with hG
  obtain ⟨t, htT, ht1, ht2, htc⟩ := exists_central_involution hT2 hT1
  obtain ⟨x, rfl⟩ := hTi htT
  have hx2 : x ^ 2 = 1 := hinj (by rw [map_pow, ht2, map_one])
  have hx1 : x ≠ 1 := fun h' => ht1 (by rw [h', map_one])
  have hTx : ∀ y : unitaryPSU h 3, MulAut.conj y ∈ T → y * x = x * y := by
    intro y hy
    apply hinj
    rw [map_mul, map_mul]
    exact htc _ hy
  set Eq := unitaryPSUEquiv h (n := 3) (by norm_num) with hEq
  have hEqmk : ∀ g : G, Eq (unitaryProj h 3 g) = (g : StatedProj (unitarySU p f K 3)) :=
    fun g => unitaryPSUEquiv_unitaryProj h _ g
  obtain ⟨X₀, hX₀2, hX₀⟩ : ∃ X₀ : G, X₀ ^ 2 = 1 ∧ unitaryProj h 3 X₀ = x := by
    have hAe : IsElemAbelian 2 (Subgroup.zpowers (Eq x)) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨m, rfl⟩⟩ := a
        obtain ⟨_, ⟨n, rfl⟩⟩ := b
        simp only [Subgroup.coe_mul]
        rw [← zpow_add, ← zpow_add, add_comm]
      · rintro _ ⟨m, rfl⟩
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow, hx2,
          map_one, one_zpow]
    obtain ⟨X₀, hX₀, hX₀x⟩ :=
      CFSG.Quasithin.E22S.exists_invLiftU hAe (Subgroup.mem_zpowers (Eq x))
    exact ⟨X₀, hX₀.2, Eq.injective (by rw [hEqmk]; exact hX₀x)⟩
  have hX₀1 : X₀ ≠ 1 := fun h' => hx1 (by rw [← hX₀, h', map_one])
  obtain ⟨g, hgU, hg⟩ := exists_unitary_frame_sZero h hp2 hX₀2 hX₀1
  have hgX : g⁻¹ * sZeroGL * g = (X₀ : GL (Fin 3) K) := by rw [← hg]; group
  have hcommx : ∀ Z : G, unitaryProj h 3 Z * x = x * unitaryProj h 3 Z →
      (Z : GL (Fin 3) K) * X₀ = X₀ * Z := by
    intro Z hZ
    have h1 : (X₀ : StatedProj (unitarySU p f K 3)) * (Z : StatedProj (unitarySU p f K 3)) =
        (Z : StatedProj (unitarySU p f K 3)) * (X₀ : StatedProj (unitarySU p f K 3)) := by
      have h0 := congrArg Eq (show unitaryProj h 3 X₀ * unitaryProj h 3 Z =
        unitaryProj h 3 Z * unitaryProj h 3 X₀ by rw [hX₀]; exact hZ.symm)
      rw [map_mul, map_mul, hEqmk, hEqmk] at h0
      exact h0
    have h2 := CFSG.Quasithin.E22S.commute_of_proj_commute_two_U hX₀2 h1
    have h3 := congrArg (fun z : G => (z : GL (Fin 3) K)) h2
    simp only [Subgroup.coe_mul] at h3
    exact h3.symm
  have hblock : ∀ Z : G, unitaryProj h 3 Z * x = x * unitaryProj h 3 Z →
      g * (Z : GL (Fin 3) K) * g⁻¹ * sZeroGL = sZeroGL * (g * (Z : GL (Fin 3) K) * g⁻¹) := by
    intro Z hZx
    have hc := hcommx Z hZx
    rw [← hg]
    calc g * (Z : GL (Fin 3) K) * g⁻¹ * (g * (X₀ : GL (Fin 3) K) * g⁻¹)
        = g * ((Z : GL (Fin 3) K) * X₀) * g⁻¹ := by group
      _ = g * ((X₀ : GL (Fin 3) K) * Z) * g⁻¹ := by rw [hc]
      _ = g * (X₀ : GL (Fin 3) K) * g⁻¹ * (g * (Z : GL (Fin 3) K) * g⁻¹) := by group
  have hscal : ∀ Z Y : G, unitaryProj h 3 Z * unitaryProj h 3 Y =
      unitaryProj h 3 Y * unitaryProj h 3 Z → ∃ c : Kˣ,
      (g * (Y : GL (Fin 3) K) * g⁻¹) * (g * (Z : GL (Fin 3) K) * g⁻¹) =
        (g * (Z : GL (Fin 3) K) * g⁻¹) * (g * (Y : GL (Fin 3) K) * g⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    intro Z Y hZY
    have h1 : unitaryProj h 3 (Z * Y) = unitaryProj h 3 (Y * Z) := by rw [map_mul, map_mul, hZY]
    obtain ⟨c, hc⟩ := (Item211Lie2Proof.unitaryProj_eq_iff h).mp h1
    refine ⟨c, ?_⟩
    simp only [Subgroup.coe_mul] at hc
    have hsc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c g⁻¹).eq
    calc (g * (Y : GL (Fin 3) K) * g⁻¹) * (g * (Z : GL (Fin 3) K) * g⁻¹)
        = g * ((Y : GL (Fin 3) K) * Z) * g⁻¹ := by group
      _ = g * ((Z : GL (Fin 3) K) * Y) * (Matrix.GeneralLinearGroup.scalar (Fin 3) c * g⁻¹) := by
          rw [hc]; group
      _ = g * ((Z : GL (Fin 3) K) * Y) * (g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) c) := by
          rw [hsc]
      _ = (g * (Z : GL (Fin 3) K) * g⁻¹) * (g * (Y : GL (Fin 3) K) * g⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin 3) c := by group
  have hscal1 : ∀ (N N' : GL (Fin 3) K) (c : Kˣ),
      Item211Lie2Proof.IsBlock (N : Matrix (Fin 3) (Fin 3) K) →
      Item211Lie2Proof.IsBlock (N' : Matrix (Fin 3) (Fin 3) K) →
      N * N' = N' * N * Matrix.GeneralLinearGroup.scalar (Fin 3) c → N * N' = N' * N := by
    intro N N' c hN hN' he
    have e22 := congrFun (congrFun (congrArg (fun P : GL (Fin 3) K =>
      (P : Matrix (Fin 3) (Fin 3) K)) he) 2) 2
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at e22
    rw [mul_apply_two_two hN hN', Matrix.mul_apply, Fin.sum_univ_three] at e22
    have hN'N := mul_apply_two_two hN' hN
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _
      (show (0 : Fin 3) ≠ 2 by decide), Matrix.diagonal_apply_ne _
      (show (1 : Fin 3) ≠ 2 by decide), mul_zero, zero_add, hN'N] at e22
    have hc1 : (c : K) = 1 := by
      have h0 : ((N : Matrix (Fin 3) (Fin 3) K) 2 2 * (N' : Matrix (Fin 3) (Fin 3) K) 2 2) *
          (1 - c) = 0 := by
        linear_combination e22
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 (mul_ne_zero (apply_two_two_ne_zero_of_isBlock hN)
          (apply_two_two_ne_zero_of_isBlock hN'))
      · linear_combination -h0
    have hc : c = 1 := Units.ext hc1
    rw [hc, map_one, mul_one] at he
    exact he
  have hTbs : ∀ y : unitaryPSU h 3, MulAut.conj y ∈ T → ∀ Y : G, unitaryProj h 3 Y = y →
      IsBlockScalar ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro y hy Y hY
    by_contra hns
    apply hnab
    have hMs := hblock Y (by rw [hY]; exact hTx y hy)
    have hMb := isBlock_of_commute_sZeroGL hK2 hMs
    have hcomm : ∀ z : unitaryPSU h 3,
        MulAut.conj z ∈ Subgroup.centralizer (T : Set (MulAut (unitaryPSU h 3))) →
        ∀ Z : G, unitaryProj h 3 Z = z →
        Item211Lie2Proof.IsBlock ((g * Z * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
        ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((g * Z * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((g * Z * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro z hz Z hZ
      have hzs : ∀ s : unitaryPSU h 3, MulAut.conj s ∈ T → z * s = s * z := by
        intro s hs
        apply hinj
        rw [map_mul, map_mul]
        exact (Subgroup.mem_centralizer_iff.mp hz _ hs).symm
      have hNs := hblock Z (by rw [hZ]; exact hzs x htT)
      have hNb := isBlock_of_commute_sZeroGL hK2 hNs
      refine ⟨hNb, ?_⟩
      obtain ⟨c, hc⟩ := hscal Z Y (by rw [hZ, hY]; exact hzs y hy)
      have := hscal1 _ _ c hMb hNb hc
      rw [← Units.val_mul, this, Units.val_mul]
    rintro a ⟨⟨z, rfl⟩, hzT⟩ b ⟨⟨z', rfl⟩, hz'T⟩
    obtain ⟨Z, rfl⟩ := unitaryProj_surjective h 3 z
    obtain ⟨Z', rfl⟩ := unitaryProj_surjective h 3 z'
    obtain ⟨hNb, hMN⟩ := hcomm _ hzT Z rfl
    obtain ⟨hN'b, hMN'⟩ := hcomm _ hz'T Z' rfl
    have hNN' := commute_of_commute_of_not_blockScalar hMb hNb hN'b hns hMN hMN'
    have hZZ' : Z * Z' = Z' * Z := by
      have h1 : (g * Z * g⁻¹ : GL (Fin 3) K) * (g * Z' * g⁻¹) =
          (g * Z' * g⁻¹ : GL (Fin 3) K) * (g * Z * g⁻¹) := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact hNN'
      have h2 : g * ((Z : GL (Fin 3) K) * Z') * g⁻¹ = g * ((Z' : GL (Fin 3) K) * Z) * g⁻¹ := by
        calc g * ((Z : GL (Fin 3) K) * Z') * g⁻¹ = (g * Z * g⁻¹) * (g * Z' * g⁻¹) := by group
          _ = (g * Z' * g⁻¹) * (g * Z * g⁻¹) := h1
          _ = g * ((Z' : GL (Fin 3) K) * Z) * g⁻¹ := by group
      apply Subtype.ext
      simpa using h2
    rw [← map_mul MulAut.conj, ← map_mul MulAut.conj, ← map_mul (unitaryProj h 3),
      ← map_mul (unitaryProj h 3), hZZ']
  set gU : primeFormUnitary h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3) :=
    ⟨g⁻¹, inv_mem hgU⟩ with hgUdef
  let ι : unitarySU p f K 2 →* unitaryPSU h 3 :=
    (unitaryProj h 3).comp
      ((CFSG.RankThree.PartOne.KFU.conjSU h gU).toMonoidHom.comp (blockEmbU h))
  have hιcoe : ∀ A : unitarySU p f K 2,
      ((CFSG.RankThree.PartOne.KFU.conjSU h gU (blockEmbU h A) : G) : GL (Fin 3) K) =
        g⁻¹ * blockGL (A : GL (Fin 2) K) * g := by
    intro A
    rw [CFSG.RankThree.PartOne.KFU.coe_conjSU, coe_blockEmbU, hgUdef, inv_inv]
  have hιapp : ∀ A : unitarySU p f K 2,
      ι A = unitaryProj h 3 (CFSG.RankThree.PartOne.KFU.conjSU h gU (blockEmbU h A)) :=
    fun A => rfl
  have hconjι : ∀ (Y : G) (A : unitarySU p f K 2),
      g * ((CFSG.RankThree.PartOne.KFU.conjSU h gU (blockEmbU h A) : G) : GL (Fin 3) K) * g⁻¹ =
        blockGL (A : GL (Fin 2) K) := by
    intro Y A
    rw [hιcoe]
    group
  have hιT : ∀ A : unitarySU p f K 2,
      MulAut.conj (ι A) ∈ Subgroup.centralizer (T : Set (MulAut (unitaryPSU h 3))) := by
    intro A
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨y, rfl⟩ := hTi hs
    obtain ⟨Y, rfl⟩ := unitaryProj_surjective h 3 y
    have hcm := commute_blockMat_of_isBlockScalar (hTbs _ hs Y rfl) (A : GL (Fin 2) K)
    set B := CFSG.RankThree.PartOne.KFU.conjSU h gU (blockEmbU h A) with hB
    have h1 : (Y : GL (Fin 3) K) * B = B * Y := by
      have h2 : (g * Y * g⁻¹ : GL (Fin 3) K) * blockGL (A : GL (Fin 2) K) =
          blockGL (A : GL (Fin 2) K) * (g * Y * g⁻¹) := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, coe_blockGL]
        exact hcm
      have hB' : (B : GL (Fin 3) K) = g⁻¹ * blockGL (A : GL (Fin 2) K) * g := hιcoe A
      rw [hB']
      calc (Y : GL (Fin 3) K) * (g⁻¹ * blockGL (A : GL (Fin 2) K) * g)
          = g⁻¹ * ((g * Y * g⁻¹) * blockGL (A : GL (Fin 2) K)) * g := by group
        _ = g⁻¹ * (blockGL (A : GL (Fin 2) K) * (g * Y * g⁻¹)) * g := by rw [h2]
        _ = (g⁻¹ * blockGL (A : GL (Fin 2) K) * g) * Y := by group
    have h3 : Y * B = B * Y := Subtype.ext (by simpa using h1)
    rw [hιapp, ← map_mul MulAut.conj, ← map_mul MulAut.conj, ← map_mul (unitaryProj h 3),
      ← map_mul (unitaryProj h 3), h3]
  have hιneg : ι (negOneSU h) = x := by
    rw [hιapp, ← hX₀]
    congr 1
    apply Subtype.ext
    rw [hιcoe, coe_negOneSU, ← hgX]
    rfl
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro A hA
    rw [hιapp, unitaryProj_eq_one_iff h] at hA
    obtain ⟨c, hc⟩ := hA
    rw [hιcoe] at hc
    have hE : blockGL (A : GL (Fin 2) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      calc blockGL (A : GL (Fin 2) K) = g * (g⁻¹ * blockGL (A : GL (Fin 2) K) * g) * g⁻¹ := by
            group
        _ = g * Matrix.GeneralLinearGroup.scalar (Fin 3) c * g⁻¹ := by rw [hc]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
            rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c g).eq, mul_inv_cancel_right]
    have hEm := congrArg (fun P : GL (Fin 3) K => (P : Matrix (Fin 3) (Fin 3) K)) hE
    simp only [coe_blockGL, Matrix.GeneralLinearGroup.coe_scalar] at hEm
    have hc1 : (c : K) = 1 := by
      have h22 := congrFun (congrFun hEm 2) 2
      simp [blockMat] at h22
      exact h22.symm
    apply Subtype.ext
    apply Units.ext
    ext i j
    have hij := congrFun (congrFun hEm (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;> simpa [blockMat, hc1] using hij
  obtain ⟨l, hlN, hl2⟩ := exists_norm_one_sq_ne_one h hq2
  set Al : unitarySU p f K 2 := ⟨_, diag_mem_unitarySU_two h hlN⟩ with hAl
  set AJ : unitarySU p f K 2 := ⟨_, J_mem_unitarySU_two h⟩ with hAJ
  have hcentbs : ∀ Y : G, (∀ A, unitaryProj h 3 Y * ι A = ι A * unitaryProj h 3 Y) →
      IsBlockScalar ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro Y hY
    have hYx : unitaryProj h 3 Y * x = x * unitaryProj h 3 Y := by
      rw [← hιneg]
      exact hY _
    have hMs := hblock Y hYx
    have hMb := isBlock_of_commute_sZeroGL hK2 hMs
    have hcA : ∀ A : unitarySU p f K 2, ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        blockMat (A : GL (Fin 2) K) = blockMat (A : GL (Fin 2) K) *
          ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro A
      set B := CFSG.RankThree.PartOne.KFU.conjSU h gU (blockEmbU h A) with hB
      obtain ⟨c, hc⟩ := hscal B Y (hY A).symm
      have hBg : (g * (B : GL (Fin 3) K) * g⁻¹ : GL (Fin 3) K) = blockGL (A : GL (Fin 2) K) := by
        rw [hB, hιcoe]
        group
      rw [hBg] at hc
      have hbb : Item211Lie2Proof.IsBlock
          ((blockGL (A : GL (Fin 2) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [coe_blockGL]
        exact isBlock_blockMat _
      have := hscal1 _ _ c hMb hbb hc
      have h1 := congrArg (fun P : GL (Fin 3) K => (P : Matrix (Fin 3) (Fin 3) K)) this
      simpa only [Units.val_mul, coe_blockGL] using h1
    have hne : ((l⁻¹ : Kˣ) : K) ≠ (l : K) := by
      intro h0
      apply hl2
      calc (l : K) * l = l * ((l⁻¹ : Kˣ) : K) := by rw [h0]
        _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact isBlockScalar_of_commute_witnesses hMb hne (hcA Al) (hcA AJ)
  refine eq_bot_of_sl2Like hinj (by rw [hD9]; decide) hTD hVi hV2 hDV hVD hW2 hVW hWT hτ htT ι
    hιinj hιT hιneg (sl2Like_unitarySU_two h hq4) ?_ ?_ ?_
  ·
    intro w hw A
    obtain ⟨Wt, rfl⟩ := unitaryProj_surjective h 3 w
    have hwx : unitaryProj h 3 Wt * x = x * unitaryProj h 3 Wt := by
      apply hinj
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp (hWT hw) _ htT).symm
    have hMs := hblock Wt hwx
    have hMb := isBlock_of_commute_sZeroGL hK2 hMs
    set B := CFSG.RankThree.PartOne.KFU.conjSU h gU (blockEmbU h A) with hB
    set C : G := Wt * B * Wt⁻¹ * B⁻¹ with hC
    have hCg : (g * (C : GL (Fin 3) K) * g⁻¹ : GL (Fin 3) K) =
        (g * Wt * g⁻¹) * blockGL (A : GL (Fin 2) K) * (g * Wt * g⁻¹)⁻¹ *
          (blockGL (A : GL (Fin 2) K))⁻¹ := by
      have hB' : (B : GL (Fin 3) K) = g⁻¹ * blockGL (A : GL (Fin 2) K) * g := hιcoe A
      simp only [hC, Subgroup.coe_mul, Subgroup.coe_inv, hB']
      group
    have hCmem : (g * (C : GL (Fin 3) K) * g⁻¹ : GL (Fin 3) K) ∈ unitarySU p f K 3 :=
      CFSG.RankThree.PartOne.KFU.conj_mem_unitarySU h hgU C.2
    have hCb : Item211Lie2Proof.IsBlock
        ((g * (C : GL (Fin 3) K) * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have hbs : blockGL (A : GL (Fin 2) K) * sZeroGL = sZeroGL * blockGL (A : GL (Fin 2) K) := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, coe_blockGL, coe_sZeroGL, ← coe_sZero]
        exact commute_sZero_of_isBlock (isBlock_blockMat _)
      apply isBlock_of_commute_sZeroGL hK2
      rw [hCg]
      have hcM : Commute (g * (Wt : GL (Fin 3) K) * g⁻¹) sZeroGL := hMs
      have hcb : Commute (blockGL (A : GL (Fin 2) K)) sZeroGL := hbs
      exact (((hcM.mul_left hcb).mul_left hcM.inv_left).mul_left hcb.inv_left).eq
    have hC22 : ((g * (C : GL (Fin 3) K) * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
        1 := by
      rw [hCg]
      have hbb : Item211Lie2Proof.IsBlock
          ((blockGL (A : GL (Fin 2) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [coe_blockGL]
        exact isBlock_blockMat _
      have hbinvb : Item211Lie2Proof.IsBlock
          (((blockGL (A : GL (Fin 2) K))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [← map_inv, coe_blockGL]
        exact isBlock_blockMat _
      have hMinvb : Item211Lie2Proof.IsBlock
          (((g * Wt * g⁻¹ : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        apply isBlock_of_commute_sZeroGL hK2
        exact (show Commute (g * (Wt : GL (Fin 3) K) * g⁻¹) sZeroGL from hMs).inv_left.eq
      have hmul : ∀ P Q : GL (Fin 3) K, Item211Lie2Proof.IsBlock (P : Matrix (Fin 3) (Fin 3) K) →
          Item211Lie2Proof.IsBlock (Q : Matrix (Fin 3) (Fin 3) K) →
          Item211Lie2Proof.IsBlock ((P * Q : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
          ((P * Q : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
            (P : Matrix (Fin 3) (Fin 3) K) 2 2 * (Q : Matrix (Fin 3) (Fin 3) K) 2 2 := by
        intro P Q hP hQ
        refine ⟨?_, by rw [Units.val_mul]; exact mul_apply_two_two hP hQ⟩
        obtain ⟨a02, a12, a20, a21⟩ := hP
        obtain ⟨b02, b12, b20, b21⟩ := hQ
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, a02, a12, a20, a21, b02,
            b12, b20, b21]
      have hinv22 : ∀ P : GL (Fin 3) K, Item211Lie2Proof.IsBlock (P : Matrix (Fin 3) (Fin 3) K) →
          Item211Lie2Proof.IsBlock ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
          (P : Matrix (Fin 3) (Fin 3) K) 2 2 * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2
            = 1 := by
        intro P hP hPi
        have := (hmul P P⁻¹ hP hPi).2
        rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_eq] at this
        exact this.symm
      obtain ⟨hb1, e1⟩ := hmul _ _ hMb hbb
      obtain ⟨hb2, e2⟩ := hmul _ _ hb1 hMinvb
      obtain ⟨-, e3⟩ := hmul _ _ hb2 hbinvb
      rw [e3, e2, e1]
      have i1 := hinv22 _ hMb hMinvb
      have i2 := hinv22 _ hbb hbinvb
      linear_combination
        ((blockGL (A : GL (Fin 2) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 *
          (((blockGL (A : GL (Fin 2) K))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 * i1
          + i2
    obtain ⟨A', hA'⟩ := exists_blockGL_eq h hCmem hCb hC22
    refine ⟨A', ?_⟩
    rw [hιapp]
    have hC' : CFSG.RankThree.PartOne.KFU.conjSU h gU (blockEmbU h A') = C := by
      apply Subtype.ext
      rw [hιcoe, hA']
      group
    rw [hC', hC, map_mul, map_mul, map_mul, map_inv, map_inv, ← hιapp]
  ·
    intro y y' hy hy'
    obtain ⟨Y, rfl⟩ := unitaryProj_surjective h 3 y
    obtain ⟨Y', rfl⟩ := unitaryProj_surjective h 3 y'
    have h1 := commute_of_isBlockScalar (hcentbs Y hy) (hcentbs Y' hy')
    have h2 : (g * Y * g⁻¹ : GL (Fin 3) K) * (g * Y' * g⁻¹) =
        (g * Y' * g⁻¹ : GL (Fin 3) K) * (g * Y * g⁻¹) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact h1
    have h3 : Y * Y' = Y' * Y := by
      apply Subtype.ext
      have h4 : g * ((Y : GL (Fin 3) K) * Y') * g⁻¹ = g * ((Y' : GL (Fin 3) K) * Y) * g⁻¹ := by
        calc g * ((Y : GL (Fin 3) K) * Y') * g⁻¹ = (g * Y * g⁻¹) * (g * Y' * g⁻¹) := by group
          _ = (g * Y' * g⁻¹) * (g * Y * g⁻¹) := h2
          _ = g * ((Y' : GL (Fin 3) K) * Y) * g⁻¹ := by group
      simpa using h4
    rw [← map_mul, ← map_mul, h3]
  ·
    intro y hy hy2
    obtain ⟨Y, rfl⟩ := unitaryProj_surjective h 3 y
    obtain ⟨⟨h02, h12, h20, h21⟩, h01, h10, h00⟩ := hcentbs Y hy
    have hY2 : unitaryProj h 3 (Y ^ 2) = 1 := by rw [map_pow, hy2]
    obtain ⟨ζ, hζ⟩ := (unitaryProj_eq_one_iff h).mp hY2
    have hN2 : (g * (Y : GL (Fin 3) K) * g⁻¹) ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ := by
      rw [conj_pow, ← Subgroup.coe_pow, hζ,
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g).eq, mul_inv_cancel_right]
    have hNN : ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          Matrix.scalar (Fin 3) (ζ : K) := by
      rw [← Units.val_mul, ← pow_two, hN2, Matrix.GeneralLinearGroup.coe_scalar]
    have e00 := congrFun (congrFun hNN 0) 0
    have e22 := congrFun (congrFun hNN 2) 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h20, h21, h12, mul_zero,
      add_zero, zero_add, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e00 e22
    set m := ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 with hm
    set β := ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 with hβ
    have hm0 : m ≠ 0 := apply_two_two_ne_zero_of_isBlock ⟨h02, h12, h20, h21⟩
    have hYconj : ∀ S : GL (Fin 3) K, ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        m • (S : Matrix (Fin 3) (Fin 3) K) →
        (Y : GL (Fin 3) K) = (g⁻¹ * S * g) * Matrix.GeneralLinearGroup.scalar (Fin 3)
          (Units.mk0 m hm0) := by
      intro S hS
      have h1 : (g * Y * g⁻¹ : GL (Fin 3) K) = S * Matrix.GeneralLinearGroup.scalar (Fin 3)
          (Units.mk0 m hm0) := by
        apply Units.ext
        rw [hS, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
        ext i j
        simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
      calc (Y : GL (Fin 3) K) = g⁻¹ * (g * Y * g⁻¹) * g := by group
        _ = g⁻¹ * (S * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 m hm0)) * g := by
            rw [h1]
        _ = (g⁻¹ * S * g) * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 m hm0) := by
            rw [show g⁻¹ * (S * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 m hm0)) * g =
              g⁻¹ * S * (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 m hm0) * g) by group,
              ← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (Units.mk0 m hm0) g).eq]
            group
    have hsq : (β - m) * (β + m) = 0 := by linear_combination e00 - e22
    rcases mul_eq_zero.mp hsq with hb | hb
    · left
      have hb' : β = m := sub_eq_zero.mp hb
      have hS : ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          m • ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h01, h02, h10, h20, h21, h12, ← h00, hb', ← hm, ← hβ]
      have h1 := hYconj 1 hS
      rw [show g⁻¹ * 1 * g = 1 by group, one_mul] at h1
      rw [unitaryProj_eq_one_iff h]
      exact ⟨_, h1⟩
    · right
      have hb' : β = -m := by linear_combination hb
      have hS : ((g * Y * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          m • ((sZeroGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [coe_sZeroGL]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h01, h02, h10, h20, h21, h12, ← h00, hb', ← hm, ← hβ]
      have h1 := hYconj sZeroGL hS
      rw [hgX] at h1
      rw [← hX₀]
      exact ((Item211Lie2Proof.unitaryProj_eq_iff h).mpr ⟨_, h1⟩).symm

theorem l3PlusCoreFor_unitaryPSU_of_outer (hp3 : 3 < p)
    (hout : L3PlusOuterFor (unitaryPSU h 3)) : L3PlusCoreFor (unitaryPSU h 3) := by
  intro D T V W hDe hD9 hT2 hT1 hTD hnab hVi hV2 hDV hVD hVT hW2 hVW hWT hτ
  by_cases hTi : T ≤ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range
  · have hTT : T ⊓ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range = T :=
      inf_eq_left.mpr hTi
    rw [hTT] at hnab
    exact eq_bot_of_le_inn_unitaryPSU h hp3 hD9 hT2 hT1 hTD hTi hnab hVi hV2 hDV hVD hW2 hVW
      hWT hτ
  · exact hout D T V W hDe hD9 hT2 hT1 hTD hnab hTi hVi hV2 hDV hVD hVT hW2 hVW hWT hτ

end Unitary

end Item211Lie3Proof

open Item211Lie2Proof Item211Lie3Proof

@[expose] def KS211L3PlusUnitaryOuter : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData p f K), 3 < p → p ^ f % 3 = 2 →
    L3PlusOuterFor (unitaryPSU h 3)

theorem ks211L3PlusUnitaryCore_of_outer (h : KS211L3PlusUnitaryOuter) :
    KS211L3PlusUnitaryCore :=
  fun p f K _ hU hp3 hq => l3PlusCoreFor_unitaryPSU_of_outer hU hp3 (h p f K hU hp3 hq)

end CFSG.RankThree.PartTwo.Sec21
