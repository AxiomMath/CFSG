module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128NotHJTC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

section Schur

variable {𝕂 : Type} [Field 𝕂]

theorem false_of_commute_irreducible {τ : 𝕂} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : 𝕂) ≠ 0)
    {s y : GL (Fin 3) 𝕂} (hdet : (s : Matrix (Fin 3) (Fin 3) 𝕂).det = 1)
    (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) 𝕂) (hsZ : s ∉ StatedScalars (Fin 3) 𝕂)
    (hys : y * s = s * y)
    (hirr : ∀ W : Submodule 𝕂 (Fin 3 → 𝕂), (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) 𝕂) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤) : False := by
  obtain ⟨κ, hκ⟩ := hs3
  have hsm : (s : Matrix (Fin 3) (Fin 3) 𝕂) ^ 3 = (κ : 𝕂) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hκ, coe_scalar_eq_smul]
  by_cases hcube : ∃ μ : 𝕂, μ ^ 3 = κ
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hμ
      exact κ.ne_zero hμ.symm
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hτ
      exact zero_ne_one hτ
    set M : Matrix (Fin 3) (Fin 3) 𝕂 := μ⁻¹ • (s : Matrix (Fin 3) (Fin 3) 𝕂) with hM
    have hM3 : M ^ 3 = 1 := by
      rw [hM, smul_pow, hsm, smul_smul, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow, one_smul]
    obtain ⟨b, hb, hbe⟩ := exists_eigenbasis hτ hτ1 h3 hM3
    obtain ⟨k, hk⟩ := hbe 0
    set ν := τ ^ (k : ℕ) with hν
    set W : Submodule 𝕂 (Fin 3 → 𝕂) := LinearMap.ker (Matrix.toLin' (M - ν • 1)) with hW
    have hmemW : ∀ v, v ∈ W ↔ M *ᵥ v = ν • v := fun v => by
      rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
        Matrix.smul_mulVec ν (1 : Matrix (Fin 3) (Fin 3) 𝕂) v, Matrix.one_mulVec, sub_eq_zero]
    have hyM : (y : Matrix (Fin 3) (Fin 3) 𝕂) * M = M * y := by
      rw [hM, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul, hys, Units.val_mul]
    rcases hirr W (fun v hv => by
        rw [hmemW] at hv ⊢
        rw [Matrix.mulVec_mulVec, ← hyM, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul])
      with hbot | htop
    · apply hb.ne_zero 0
      have hb0 : b 0 ∈ W := (hmemW _).mpr hk
      rwa [hbot, Submodule.mem_bot] at hb0
    · apply hsZ
      have hMν : M = ν • 1 := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply,
          Matrix.smul_mulVec ν (1 : Matrix (Fin 3) (Fin 3) 𝕂) v, Matrix.one_mulVec]
        exact (hmemW v).mp (by rw [htop]; exact Submodule.mem_top)
      have hs : (s : Matrix (Fin 3) (Fin 3) 𝕂) = (μ * ν) • 1 := by
        calc (s : Matrix (Fin 3) (Fin 3) 𝕂) = μ • M := by
              rw [hM, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
          _ = (μ * ν) • 1 := by rw [hMν, smul_smul]
      exact mem_statedScalars_of_eq_smul hs (mul_ne_zero hμ0 (pow_ne_zero _ hτ0))
  · push Not at hcube
    have hd := det_eq_of_cube hcube hsm
    rw [hdet] at hd
    exact hcube 1 (by rw [one_pow]; exact hd)

end Schur

section Swap

variable {𝕂 : Type} [Field 𝕂]

theorem not_cube_of_irreducible {τ : 𝕂} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : 𝕂) ≠ 0)
    {y : GL (Fin 3) 𝕂} {ν : 𝕂} (hy : (y : Matrix (Fin 3) (Fin 3) 𝕂) ^ 3 = ν • 1)
    (hirr : ∀ W : Submodule 𝕂 (Fin 3 → 𝕂), (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) 𝕂) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤) : ∀ μ : 𝕂, μ ^ 3 ≠ ν := by
  intro μ hμ
  have hν : ν ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hy
    rw [h0, zero_smul, Matrix.det_pow, Matrix.det_zero] at hd
    exact (y.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) 𝕂 →* 𝕂)).ne_zero
      (pow_eq_zero_iff (by norm_num) |>.mp hd)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    exact hν hμ.symm
  set M : Matrix (Fin 3) (Fin 3) 𝕂 := μ⁻¹ • (y : Matrix (Fin 3) (Fin 3) 𝕂) with hM
  have hM3 : M ^ 3 = 1 := by
    rw [hM, smul_pow, hy, smul_smul, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow, one_smul]
  obtain ⟨b, hb, hbe⟩ := exists_eigenbasis hτ hτ1 h3 hM3
  obtain ⟨k, hk⟩ := hbe 0
  have hyb : (y : Matrix (Fin 3) (Fin 3) 𝕂) *ᵥ b 0 = (μ * τ ^ (k : ℕ)) • b 0 := by
    have e1 : (y : Matrix (Fin 3) (Fin 3) 𝕂) = μ • M := by
      rw [hM, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    rw [e1, Matrix.smul_mulVec, hk, smul_smul]
  have hv0 : b 0 ≠ 0 := hb.ne_zero 0
  rcases hirr (𝕂 ∙ b 0) (fun w hw => by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [Matrix.mulVec_smul, hyb, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) with h | h
  · exact hv0 ((Submodule.span_singleton_eq_bot).mp h)
  · have := finrank_span_singleton (K := 𝕂) hv0
    rw [h, finrank_top, Module.finrank_fin_fun] at this
    omega

@[expose] def swapNeg : GL (Fin 3) 𝕂 :=
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapNeg :
    ((swapNeg : GL (Fin 3) 𝕂) : Matrix (Fin 3) (Fin 3) 𝕂) = !![0, -1, 0; -1, 0, 0; 0, 0, -1] :=
  rfl

theorem swapNeg_inv : (swapNeg : GL (Fin 3) 𝕂)⁻¹ = swapNeg :=
  rfl

theorem swapNeg_mul_self : (swapNeg : GL (Fin 3) 𝕂) * swapNeg = 1 := by
  calc (swapNeg : GL (Fin 3) 𝕂) * swapNeg = swapNeg⁻¹ * swapNeg := by rw [swapNeg_inv]
    _ = 1 := inv_mul_cancel _

theorem swapNeg_mem_slPi {π : Bool} {p f : ℕ} (hπ : π = false → UnitaryFieldData p f 𝕂) :
    swapNeg ∈ slPi π 3 (p ^ f) 𝕂 := by
  have hdet : ((swapNeg : GL (Fin 3) 𝕂) : Matrix (Fin 3) (Fin 3) 𝕂).det = 1 := by
    rw [coe_swapNeg, Matrix.det_fin_three]
    simp
  cases π
  · have h := hπ rfl
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    rw [coe_swapNeg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  · rw [mem_slPi_true]
    exact hdet

theorem swapNeg_conj_diagTau {τ : 𝕂} (hτ : τ ^ 3 = 1) :
    swapNeg * diagTau hτ * swapNeg⁻¹ = (diagTau hτ)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, swapNeg_inv, coe_swapNeg]
  change _ = !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1]
  rw [coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swapNeg_conj_cycThree :
    swapNeg * cycThree * swapNeg⁻¹ = (cycThree : GL (Fin 3) 𝕂)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, swapNeg_inv, coe_swapNeg]
  change _ = !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  rw [coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swapNeg_conj_mul_ne {τ : 𝕂} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {y : GL (Fin 3) 𝕂}
    {lam : 𝕂ˣ} (hlam1 : lam ≠ 1)
    (hy : y * diagTau hτ * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * diagTau hτ)
    (hdet : ∀ μ : 𝕂, μ ^ 3 ≠ (y : Matrix (Fin 3) (Fin 3) 𝕂).det) (κ : 𝕂ˣ) :
    swapNeg * y * swapNeg⁻¹ * y ≠
      GeneralLinearGroup.scalar (Fin 3) κ * (y * (swapNeg * y * swapNeg⁻¹)) := by
  intro hc
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hτ
    exact zero_ne_one hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hlam3 : (lam : 𝕂) ^ 3 = 1 := by
    have h1 := congrArg Units.val (pow_three_eq_one_of_conj_eq_scalar_mul hy)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h1
  have hlam1' : (lam : 𝕂) ≠ 1 := fun h1 => hlam1 (Units.ext h1)
  set Y : Matrix (Fin 3) (Fin 3) 𝕂 := (y : Matrix (Fin 3) (Fin 3) 𝕂) with hYdef
  have hyd : y * diagTau hτ = GeneralLinearGroup.scalar (Fin 3) lam * diagTau hτ * y := by
    rw [← hy]
    group
  have hM := congrArg (fun A : GL (Fin 3) 𝕂 => (A : Matrix (Fin 3) (Fin 3) 𝕂)) hyd
  simp only [Units.val_mul, coe_scalar_eq_smul, coe_diagTau] at hM
  have ent : ∀ i j, (Y * !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1]) i j =
      (((lam : 𝕂) • (1 : Matrix (Fin 3) (Fin 3) 𝕂) * !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1]) * Y)
        i j := fun i j => by rw [hM]
  have aux : ∀ {X u v : 𝕂}, u ≠ v → X * u = v * X → X = 0 := fun {X u v} huv h => by
    have h' : X * (u - v) = 0 := by rw [mul_sub, h, mul_comm, sub_self]
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr huv)
  have e00 := ent 0 0
  have e01 := ent 0 1
  have e02 := ent 0 2
  have e10 := ent 1 0
  have e11 := ent 1 1
  have e12 := ent 1 2
  have e20 := ent 2 0
  have e21 := ent 2 1
  have e22 := ent 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  have hcM := congrArg (fun A : GL (Fin 3) 𝕂 => (A : Matrix (Fin 3) (Fin 3) 𝕂)) hc
  simp only [Units.val_mul, coe_scalar_eq_smul, swapNeg_inv, coe_swapNeg] at hcM
  rw [← hYdef] at hcM
  have c00 := congrFun (congrFun hcM 0) 0
  have c22 := congrFun (congrFun hcM 2) 2
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at c00 c22
  have hdetY : Y.det ≠ 0 :=
    (y.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) 𝕂 →* 𝕂)).ne_zero
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hlam3 with h1 | h1 | h1
  · exact hlam1' h1
  ·
    rw [h1] at e00 e02 e10 e11 e21 e22
    have y00 : Y 0 0 = 0 := aux hττ2 (by linear_combination e00)
    have y02 : Y 0 2 = 0 := aux (Ne.symm hτ2) (by linear_combination e02)
    have y10 : Y 1 0 = 0 := aux hτ1 (by linear_combination e10 + Y 1 0 * hτ)
    have y11 : Y 1 1 = 0 := aux hτ2 (by linear_combination e11 + Y 1 1 * hτ)
    have y21 : Y 2 1 = 0 := aux (Ne.symm hττ2) (by linear_combination e21)
    have y22 : Y 2 2 = 0 := aux (Ne.symm hτ1) (by linear_combination e22)
    have hdet3 : Y.det = Y 0 1 * Y 1 2 * Y 2 0 := by
      rw [Matrix.det_fin_three, y00, y02, y10, y11, y21, y22]
      ring
    simp only [y00, y02, y10, y11, y21, y22, mul_zero, add_zero, zero_add] at c00 c22
    have hβγ : Y 1 2 * Y 2 0 ≠ 0 := by
      intro h0
      apply hdetY
      rw [hdet3, mul_assoc, h0, mul_zero]
    have hκ : (κ : 𝕂) = 1 := by
      have : (Y 1 2 * Y 2 0) * (1 - κ) = 0 := by linear_combination c22
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hβγ)).symm
    rw [hκ] at c00
    apply hdet (Y 0 1)
    rw [hdet3]
    linear_combination -(Y 0 1) * c00
  ·
    rw [h1] at e00 e01 e11 e12 e20 e22
    have y00 : Y 0 0 = 0 := aux hτ1 (by linear_combination e00 + Y 0 0 * hτ)
    have y01 : Y 0 1 = 0 := aux hτ2 (by linear_combination e01 + Y 0 1 * hτ)
    have y11 : Y 1 1 = 0 := aux (Ne.symm hττ2) (by linear_combination e11 + Y 1 1 * τ * hτ)
    have y12 : Y 1 2 = 0 := aux (Ne.symm hτ1) (by linear_combination e12 + Y 1 2 * τ * hτ)
    have y20 : Y 2 0 = 0 := aux hττ2 (by linear_combination e20)
    have y22 : Y 2 2 = 0 := aux (Ne.symm hτ2) (by linear_combination e22)
    have hdet3 : Y.det = Y 0 2 * Y 1 0 * Y 2 1 := by
      rw [Matrix.det_fin_three, y00, y01, y11, y12, y20, y22]
      ring
    simp only [y00, y01, y11, y12, y20, y22, mul_zero, add_zero, zero_add] at c00 c22
    have hαγ : Y 0 2 * Y 2 1 ≠ 0 := by
      intro h0
      apply hdetY
      rw [hdet3, mul_right_comm, h0, zero_mul]
    have hκ : (κ : 𝕂) = 1 := by
      have : (Y 0 2 * Y 2 1) * (1 - κ) = 0 := by linear_combination c22
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hαγ)).symm
    rw [hκ] at c00
    apply hdet (Y 1 0)
    rw [hdet3]
    linear_combination (Y 1 0) * c00

end Swap

section Heis

variable {𝕂 : Type} [Field 𝕂] {π : Bool} {p f : ℕ}

theorem exists_scalar_of_conj_eq (hF : PiField π p f 𝕂) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) 𝕂))] {P Q : GL (Fin 3) 𝕂}
    (h : ∀ m ∈ slPi π 3 (p ^ f) 𝕂,
      ProjGenLinGroup.mk P * ProjGenLinGroup.mk m * (ProjGenLinGroup.mk P)⁻¹ =
        ProjGenLinGroup.mk Q * ProjGenLinGroup.mk m * (ProjGenLinGroup.mk Q)⁻¹) :
    ∃ κ : 𝕂ˣ, P = GeneralLinearGroup.scalar (Fin 3) κ * Q := by
  have hW : Q⁻¹ * P ∈ StatedScalars (Fin 3) 𝕂 := by
    refine mem_statedScalars_of_comm_mod hF hq fun m hm => ?_
    rw [← mk_eq_one_iff_mem_statedScalars]
    have h1 := h m hm
    simp only [map_mul, map_inv]
    set MP := ProjGenLinGroup.mk P
    set MQ := ProjGenLinGroup.mk Q
    set MM := ProjGenLinGroup.mk m
    calc MQ⁻¹ * MP * MM * (MQ⁻¹ * MP)⁻¹ * MM⁻¹ = MQ⁻¹ * (MP * MM * MP⁻¹) * MQ * MM⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨κ, hκ⟩ := hW
  refine ⟨κ, ?_⟩
  calc P = Q * (Q⁻¹ * P) := by group
    _ = Q * GeneralLinearGroup.scalar (Fin 3) κ := by rw [hκ]
    _ = GeneralLinearGroup.scalar (Fin 3) κ * Q :=
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar κ Q).eq

end Heis

section HeisBar

variable {G : Type} [Group G] [Finite G]

theorem exists_heis_bar {a : G} {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) {c x : G}
    (hcK : c ∈ K) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hxc : x * c = c * x)
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx : Sec4.InducesTypeOn K x 3) :
    Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ ∧
    ∃ Fb : Subgroup (K ⧸ aschbacherSolvableCore 3 K), CFSG.Assembly.IsElemAbelian 3 Fb ∧
      Nat.card Fb = 9 ∧ QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ ∈ Fb ∧
      (∃ nb ∈ Subgroup.normalizer (Fb : Set (K ⧸ aschbacherSolvableCore 3 K)),
        nb * QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ * nb⁻¹ ∉
          Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩)) ∧
      ∃ tb ∈ Subgroup.normalizer (Fb : Set (K ⧸ aschbacherSolvableCore 3 K)),
        (∀ u ∈ Fb, tb * u * tb⁻¹ = u⁻¹) ∧ tb * tb = 1 ∧
        MulAut.conj tb * Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) *
            MulAut.conj tb * Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) ≠
          Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) * MulAut.conj tb *
            Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) * MulAut.conj tb := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxN', π, p, f, 𝕂, _, hF, hq, e, y, hyH, hy3, hact⟩ := hx
  set σ := Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) with hσdef
  have hact' : ∀ z : K ⧸ aschbacherSolvableCore 3 K,
      ((e (σ z) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) 𝕂) * (ProjGenLinGroup.mk y)⁻¹ :=
    hact
  have hπ : π = false → UnitaryFieldData p f 𝕂 := fun h => by subst h; exact hF.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hF.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hF hq
  have hsc : ∀ (u : 𝕂ˣ) (A : GL (Fin 3) 𝕂),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  have : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) 𝕂)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv e (center_projImage_eq_bot hF hq)
  set cb : K ⧸ aschbacherSolvableCore 3 K :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ with hcbdef
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e cb).2
  have hc'3 : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hcb3 : cb ^ 3 = 1 := by rw [hcbdef, ← map_pow, hc'3, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (isPGroup_zpowers_of_pow_three hc'3) (Subgroup.mem_zpowers _) (Subgroup.one_mem _)
      (by rw [map_one]; exact h1)
    exact hc1 (congrArg Subtype.val h2)
  have hsH : s ∈ glPi π 3 (p ^ f) 𝕂 := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) 𝕂 := by
    intro hsZ
    apply hcb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) 𝕂 := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hcb3,
      map_one, Subgroup.coe_one]
  have hsdet : (s : Matrix (Fin 3) (Fin 3) 𝕂).det = 1 := ((mem_slPi_iff hπ).mp hs).2
  have hfix : σ cb = cb := by
    rw [hσdef, hcbdef, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, hxc, mul_inv_cancel_right]
  have h1 := hact' cb
  rw [hfix, ← hse] at h1
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) 𝕂 := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  obtain ⟨lam, hlam⟩ := hysZ
  have hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * s := by
    rw [hlam]
    group
  rcases eq_or_ne lam 1 with hlam1 | hlam1
  ·
    exfalso
    refine false_of_commute_irreducible hτ hτ1 h3 hsdet hs3 hsZ ?_ hy3.2.2
    rw [hlam1, map_one, one_mul] at hys
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hys]
  have htr := trace_eq_zero_of_conj_eq_scalar_mul hlam1 hys
  have hsZ' : s ∉ zPi π 3 (p ^ f) 𝕂 := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hF hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (p ^ f) 𝕂 := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  have htype : Type123 π (p ^ f) 𝕂 s 1 := by
    rcases type123_exhaust hF hq hsH hsZ' hs3' with h1 | h2 | h3
    · exact h1
    · exact absurd htr (trace_ne_zero_of_type2 hF hq h2)
    · exact absurd ⟨s, hs, fun m _ => rfl⟩ (not_inner_of_type3 hF hq hsH h3)
  obtain ⟨τ', hτ', hτ'1, z, hz, g, hg, hD⟩ := htype
  have hτ'0 : τ' ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hτ'
    exact zero_ne_one hτ'
  have hzs : z ∈ StatedScalars (Fin 3) 𝕂 := mem_statedScalars_of_mem_zPi hF hq hτ' hτ'1 hz
  have hsz : s * z = g * diagTau hτ' * g⁻¹ := by
    rw [← hD]
    group
  have he₁ : ((e cb : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (g * diagTau hτ' * g⁻¹) := by
    rw [← hse, ← hsz, map_mul, mk_eq_one_iff_mem_statedScalars.mpr hzs, mul_one]
  have hw : g * cycThree * g⁻¹ ∈ slPi π 3 (p ^ f) 𝕂 :=
    conj_mem_slPi hπ hg (cycThree_mem_slPi hπ)
  set x₂ : K ⧸ aschbacherSolvableCore 3 K :=
    e.symm (projOf _ ⟨g * cycThree * g⁻¹, hw⟩) with hx₂
  have he₂ : ((e x₂ : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (g * cycThree * g⁻¹) := by
    rw [hx₂, MulEquiv.apply_symm_apply, coe_projOf]
  set μ : 𝕂ˣ := Units.mk0 τ' hτ'0 ^ (2 * 1) with hμ
  have hcd : cycThree * diagTau hτ' * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) μ * diagTau hτ' := by
    have := cycThree_pow_conj_diagTau hτ' hτ'0 1
    rwa [pow_one] at this
  have hdc : diagTau hτ' * cycThree * (diagTau hτ')⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * cycThree := by
    have e1 : cycThree * diagTau hτ' * cycThree⁻¹ * (diagTau hτ')⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) μ := by
      rw [hcd]
      group
    have e2 : diagTau hτ' * cycThree * (diagTau hτ')⁻¹ * cycThree⁻¹ =
        (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ := by
      rw [← e1]
      group
    rw [map_inv, ← e2]
    group
  have hμ1 : μ ≠ 1 := by
    intro h1
    apply hτ'1
    have h2 : τ' ^ 2 = 1 := by
      have := congrArg Units.val h1
      rwa [hμ, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
    calc τ' = τ' ^ 3 / τ' ^ 2 := by field_simp
      _ = 1 := by rw [hτ', h2, div_one]
  have hζ1 : μ⁻¹ ≠ 1 := fun h1 => hμ1 (inv_eq_one.mp h1)
  have hmkconj : ∀ w : GL (Fin 3) 𝕂, ProjGenLinGroup.mk (g * w * g⁻¹) =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk w * (ProjGenLinGroup.mk g)⁻¹ := fun w => by
    rw [map_mul, map_mul, map_inv]
  have hx₂1 : x₂ ≠ 1 := by
    intro h1
    apply not_mem_statedScalars_of_heis (y₁ := cycThree) (ζ := μ) hμ1 hcd
    rw [← mk_eq_one_iff_mem_statedScalars]
    have h2 : ((e x₂ : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) = 1 := by
      rw [h1, map_one, Subgroup.coe_one]
    rw [he₂, hmkconj] at h2
    calc ProjGenLinGroup.mk cycThree = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = 1 := by rw [h2]; group
  have hx₂n : x₂ ∉ Subgroup.zpowers cb := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply not_mk_eq_zpow_of_heis (y₁ := diagTau hτ') (y₂ := cycThree) hζ1 hdc k
    have h2 := congrArg (fun m => ((e m : projImage (slPi π 3 (p ^ f) 𝕂)) :
      ProjGenLinGroup (Fin 3) 𝕂)) hk
    simp only [map_zpow, Subgroup.coe_zpow, he₁, he₂, hmkconj] at h2
    rw [conj_zpow] at h2
    rw [map_zpow]
    calc ProjGenLinGroup.mk cycThree = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ') ^ k *
            (ProjGenLinGroup.mk g)⁻¹) * ProjGenLinGroup.mk g := by rw [h2]
      _ = ProjGenLinGroup.mk (diagTau hτ') ^ k := by group
  have hcomm12 : cb * x₂ = x₂ * cb := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, he₁, he₂, hmkconj, hmkconj]
    have R := mk_diagTau_cycThree hτ'
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ') * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk (diagTau hτ') * ProjGenLinGroup.mk cycThree) *
          (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk cycThree * ProjGenLinGroup.mk (diagTau hτ')) *
          (ProjGenLinGroup.mk g)⁻¹ := by rw [R]
      _ = ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ') * (ProjGenLinGroup.mk g)⁻¹) := by
        group
  have hx₂3 : x₂ ^ 3 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, he₂, ← map_pow, conj_pow, cycThree_pow_three, mul_one,
      mul_inv_cancel, map_one, map_one, Subgroup.coe_one]
  have hFab : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers cb ⊔ Subgroup.zpowers x₂) :=
    Sec13.isElemAbelian_zpowers_sup hcb3 hx₂3 hcomm12
  have hF9 : Nat.card (Subgroup.zpowers cb ⊔ Subgroup.zpowers x₂ : Subgroup _) = 9 :=
    card_zpowers_sup_zpowers hx₂3 (orderOf_eq_prime hcb3 hcb1) hx₂n hcomm12.symm
  have key := transitive_of_normal_form hF hq
    (L := (⊤ : Subgroup (K ⧸ aschbacherSolvableCore 3 K)))
    (Subgroup.topEquiv.trans e) hτ' hτ'1 hg (x₁ := cb) (x₂ := x₂) (Subgroup.mem_top _)
    (Subgroup.mem_top _) he₁ he₂
  obtain ⟨nb, ⟨-, hnbN⟩, hnbx⟩ := key cb (Subgroup.mem_sup_left (Subgroup.mem_zpowers cb)) hcb1
    x₂ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)) hx₂1
  have hT' : g * swapNeg * g⁻¹ ∈ slPi π 3 (p ^ f) 𝕂 :=
    conj_mem_slPi hπ hg (swapNeg_mem_slPi hπ)
  set tb : K ⧸ aschbacherSolvableCore 3 K := e.symm (projOf _ ⟨g * swapNeg * g⁻¹, hT'⟩)
    with htb
  have he_t : ((e tb : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (g * swapNeg * g⁻¹) := by
    rw [htb, MulEquiv.apply_symm_apply, coe_projOf]
  have he_conj : ∀ u v : K ⧸ aschbacherSolvableCore 3 K,
      ((e (u * v * u⁻¹) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
        (e u : ProjGenLinGroup (Fin 3) 𝕂) * (e v : ProjGenLinGroup (Fin 3) 𝕂) *
          (e u : ProjGenLinGroup (Fin 3) 𝕂)⁻¹ := fun u v => by
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hinv_of : ∀ (u : K ⧸ aschbacherSolvableCore 3 K) (w : GL (Fin 3) 𝕂),
      ((e u : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
        ProjGenLinGroup.mk (g * w * g⁻¹) →
      swapNeg * w * swapNeg⁻¹ = w⁻¹ → tb * u * tb⁻¹ = u⁻¹ := by
    intro u w hu hw'
    apply e.injective
    apply Subtype.ext
    rw [he_conj, he_t, map_inv, Subgroup.coe_inv, hu]
    have hgl : g * swapNeg * g⁻¹ * (g * w * g⁻¹) * (g * swapNeg * g⁻¹)⁻¹ = (g * w * g⁻¹)⁻¹ := by
      calc g * swapNeg * g⁻¹ * (g * w * g⁻¹) * (g * swapNeg * g⁻¹)⁻¹ =
          g * (swapNeg * w * swapNeg⁻¹) * g⁻¹ := by group
        _ = (g * w * g⁻¹)⁻¹ := by rw [hw']; group
    have := congrArg ProjGenLinGroup.mk hgl
    rwa [map_mul, map_mul, map_inv, map_inv] at this
  have htc : tb * cb * tb⁻¹ = cb⁻¹ := hinv_of cb _ he₁ (swapNeg_conj_diagTau hτ')
  have htx : tb * x₂ * tb⁻¹ = x₂⁻¹ := hinv_of x₂ _ he₂ swapNeg_conj_cycThree
  have htinv : ∀ u ∈ Subgroup.zpowers cb ⊔ Subgroup.zpowers x₂, tb * u * tb⁻¹ = u⁻¹ := by
    intro u hu
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hcomm12 hu
    have h1 : tb * (cb ^ i * x₂ ^ j) * tb⁻¹ = (tb * cb * tb⁻¹) ^ i * (tb * x₂ * tb⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [h1, htc, htx, _root_.inv_zpow, _root_.inv_zpow, ← _root_.mul_inv_rev,
      (Commute.zpow_zpow hcomm12 i j).eq]
  have htN : tb ∈ Subgroup.normalizer
      ((Subgroup.zpowers cb ⊔ Subgroup.zpowers x₂ : Subgroup _) : Set _) :=
    Subgroup.mem_normalizer_fintype fun u hu => by
      rw [htinv u hu]
      exact inv_mem hu
  have htt : tb * tb = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, he_t, ← map_mul, map_one, Subgroup.coe_one,
      show g * swapNeg * g⁻¹ * (g * swapNeg * g⁻¹) = g * (swapNeg * swapNeg) * g⁻¹ by group,
      swapNeg_mul_self, mul_one, mul_inv_cancel, map_one]
  have hnc : MulAut.conj tb * σ * MulAut.conj tb * σ ≠ σ * MulAut.conj tb * σ * MulAut.conj tb := by
    intro hcomm
    have hCe : ∀ w : K ⧸ aschbacherSolvableCore 3 K,
        ((e (MulAut.conj tb w) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
          ProjGenLinGroup.mk (g * swapNeg * g⁻¹) * (e w : ProjGenLinGroup (Fin 3) 𝕂) *
            (ProjGenLinGroup.mk (g * swapNeg * g⁻¹))⁻¹ := fun w => by
      rw [MulAut.conj_apply, he_conj, he_t]
    obtain ⟨κ, hκ⟩ := exists_scalar_of_conj_eq hF hq
      (P := g * swapNeg * g⁻¹ * y * (g * swapNeg * g⁻¹) * y)
      (Q := y * (g * swapNeg * g⁻¹) * y * (g * swapNeg * g⁻¹)) (fun m hm => by
        have hzm : ((e (e.symm (projOf _ ⟨m, hm⟩)) : projImage (slPi π 3 (p ^ f) 𝕂)) :
            ProjGenLinGroup (Fin 3) 𝕂) = ProjGenLinGroup.mk m := by
          rw [MulEquiv.apply_symm_apply, coe_projOf]
        have h1 := congrArg (fun φ : MulAut (K ⧸ aschbacherSolvableCore 3 K) =>
          ((e (φ (e.symm (projOf _ ⟨m, hm⟩))) : projImage (slPi π 3 (p ^ f) 𝕂)) :
            ProjGenLinGroup (Fin 3) 𝕂)) hcomm
        simp only [MulAut.mul_apply] at h1
        rw [hCe, hact', hCe, hact', hzm, hact', hCe, hact', hCe, hzm] at h1
        simp only [map_mul, map_inv] at h1 ⊢
        calc _ = _ := by group
          _ = _ := h1
          _ = _ := by group)
    set y' := g⁻¹ * y * g with hy'def
    have hy' : y' * diagTau hτ' * y'⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * diagTau hτ' := by
      have hzc : y * z * y⁻¹ = z := by
        rw [commute_of_mem_statedScalars hzs y]
        group
      have hd : diagTau hτ' = g⁻¹ * (s * z) * g := by
        rw [hsz]
        group
      calc y' * diagTau hτ' * y'⁻¹ = g⁻¹ * ((y * s * y⁻¹) * (y * z * y⁻¹)) * g := by
            rw [hy'def, hd]
            group
        _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) lam * (s * z) * g := by
            rw [hys, hzc]
            group
        _ = GeneralLinearGroup.scalar (Fin 3) lam * g⁻¹ * (s * z) * g := by rw [hsc lam g⁻¹]
        _ = GeneralLinearGroup.scalar (Fin 3) lam * diagTau hτ' := by rw [hd]; group
    obtain ⟨ν, hν⟩ := mem_statedScalars_of_mem_zPi hF hq hτ hτ1 hy3.2.1
    have hym : (y : Matrix (Fin 3) (Fin 3) 𝕂) ^ 3 = (ν : 𝕂) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hν, coe_scalar_eq_smul]
    have hcube := not_cube_of_irreducible hτ hτ1 h3 hym hy3.2.2
    have hdety : (y' : Matrix (Fin 3) (Fin 3) 𝕂).det = ν := by
      rw [hy'def, Units.val_mul, Units.val_mul, Matrix.det_units_conj', det_eq_of_cube hcube hym]
    refine swapNeg_conj_mul_ne hτ' hτ'1 hlam1 hy' (by rw [hdety]; exact hcube) κ ?_
    rw [swapNeg_inv]
    calc swapNeg * y' * swapNeg * y' =
        g⁻¹ * (g * swapNeg * g⁻¹ * y * (g * swapNeg * g⁻¹) * y) * g := by
          rw [hy'def]
          group
      _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) κ *
          (y * (g * swapNeg * g⁻¹) * y * (g * swapNeg * g⁻¹))) * g := by rw [hκ]
      _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) κ *
          (y * (g * swapNeg * g⁻¹) * y * (g * swapNeg * g⁻¹)) * g := by group
      _ = GeneralLinearGroup.scalar (Fin 3) κ * g⁻¹ *
          (y * (g * swapNeg * g⁻¹) * y * (g * swapNeg * g⁻¹)) * g := by rw [hsc κ g⁻¹]
      _ = GeneralLinearGroup.scalar (Fin 3) κ * (y' * (swapNeg * y' * swapNeg)) := by
          rw [hy'def]
          group
  exact ⟨hZ, Subgroup.zpowers cb ⊔ Subgroup.zpowers x₂, hFab, hF9,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers cb),
    ⟨nb, hnbN, by rw [hnbx]; exact hx₂n⟩, tb, htN, htinv, htt, hnc⟩

end HeisBar

section PGL

variable {G : Type} [Group G] [Finite G]

theorem false_of_pgl
    (h45 : Sec4.Item4_5) (h125 : Item125BarTC) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hty : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) {K : Subgroup G} (hK : K ∈ lA422 A a)
    (hcK : c ∈ K) {x : G} (hxA : x ∈ A) (hx : Sec4.InducesTypeOn K x 3) : False := by
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  obtain ⟨haA, ha3', -⟩ := Sec13.zpowers_mem_omegaA_iff.mp ha
  have ha1 : a ≠ 1 := ne_one_of_card_zpowers_eq_three ha3'
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hxc : x * c = c * x := congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hxA⟩ ⟨c, h.mem_A⟩)
  obtain ⟨hZ, Fb, hFab, hF9, hcF, ⟨nb, hnbN, hnbc⟩, -⟩ :=
    exists_heis_bar hK.1 hcK (hAe.2 c h.mem_A) h.ne_one hxc hx.1 hx
  exact false_of_bar h45 h125 h hty ha3 hK.1 (Proof128.not_mem_of_center_eq_bot hK.1 hZ ha3 ha1)
    hcK hFab hF9 hcF hnbN hnbc

end PGL

end CFSG.RankThree.PartTwo.Sec12.KS128NotHJTC
