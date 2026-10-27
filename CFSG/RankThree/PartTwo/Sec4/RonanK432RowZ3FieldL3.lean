module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowZ3FieldCore
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3OuterLin
public import CFSG.RankThree.PartTwo.Sec4.RonanK432R2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts
open Matrix

namespace Z3Field

variable {K : Type} [Field K]

theorem exists_proj_matrix_L (τ : K ≃+* K) (H : GL (Fin 3) K)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    ∃ Y : Matrix.SpecialLinearGroup (Fin 3) K,
      (conjAut 3 K H * fieldAut 3 K τ * (conjAut 3 K H)⁻¹) (proj 3 K g) = proj 3 K Y ∧
      (Y : Matrix (Fin 3) (Fin 3) K) = (H : Matrix (Fin 3) (Fin 3) K) *
        (((H⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) *
          (H : Matrix (Fin 3) (Fin 3) K)).map τ * ((H⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K H
    (Matrix.SpecialLinearGroup.map τ.toRingHom
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K H⁻¹ g)), ?_, ?_⟩
  · rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, conjAut_proj, fieldAut_proj, conjAut_proj]
  · simp only [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      inv_inv]
    rfl

theorem exists_scalar_of_fix_L (τ : K ≃+* K) (H : GL (Fin 3) K) (ζ : Kˣ)
    {X : Matrix.SpecialLinearGroup (Fin 3) K}
    (hX : (X : Matrix (Fin 3) (Fin 3) K) =
      ((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (h : (conjAut 3 K H * fieldAut 3 K τ * (conjAut 3 K H)⁻¹) (proj 3 K X) = proj 3 K X) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧ H * frobGL τ (H⁻¹ * diagUnits ζ ζ⁻¹ 1 * H) * H⁻¹ =
      diagUnits ζ ζ⁻¹ 1 * GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨Y, hY1, hY2⟩ := exists_proj_matrix_L τ H X
  rw [hY1] at h
  obtain ⟨c, hc3, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h.symm)
  refine ⟨c, hc3, Units.ext ?_⟩
  have hY : (Y : Matrix (Fin 3) (Fin 3) K) =
      (X : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) (c : K) := by
    calc (Y : Matrix (Fin 3) (Fin 3) K)
        = ((X * (X⁻¹ * Y) : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [mul_inv_cancel_left]
      _ = _ := by rw [Matrix.SpecialLinearGroup.coe_mul, hc]
  rw [hY2, hX] at hY
  simp only [Units.val_mul, coe_frobGL, GeneralLinearGroup.coe_scalar]
  exact hY

theorem conj_mem_linearAutGroup (s : projectiveSL 3 K) :
    MulAut.conj s ∈ linearAutGroup 3 K := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K s
  rw [← conjAut_toGL]
  exact conjAut_mem_linearAutGroup _

theorem not_autWeaklyClosed_of_field_L [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h3f : 3 ∣ f) {m : ℕ} (hm : p ^ (f / 3) = m + 1)
    (hm3 : m % 3 = 0) (hm0 : 0 < m) [Finite (projectiveSL 3 K)]
    {σ : MulAut (projectiveSL 3 K)} (hσ : σ ^ 3 = 1)
    (hout : σ ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (hD : σ ∉ linearAutGroup 3 K) : ¬ AutWeaklyClosed σ := by
  intro hw
  have hK3 : Nat.card K = (m + 1) ^ 3 := by
    rw [hK, ← hm, ← pow_mul, Nat.div_mul_cancel h3f]
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_three_pow hK3 hm3 hm0
  obtain ⟨X, hX⟩ : ∃ X : Matrix.SpecialLinearGroup (Fin 3) K,
      (X : Matrix (Fin 3) (Fin 3) K) =
        ((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨⟨_, det_diagUnits_inv ζ⟩, rfl⟩
  have hXN : X ^ (3 ^ (padicValNat 3 m + 1)) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hX, ← Units.val_pow_eq_pow_val,
      diagUnits_pow_eq_one (by rw [← hζ]; exact pow_orderOf_eq_one ζ)]
    rfl
  have hR : IsPGroup 3 (Subgroup.zpowers (proj 3 K X)) :=
    isPGroup_zpowers_of_pow_eq_one (by rw [← map_pow, hXN, map_one])
  have hZ : Subgroup.center (projectiveSL 3 K) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)
  obtain ⟨s, hs⟩ := r2_exists_conj_fixes hZ hσ hout hw hR
  have hfix := hs (proj 3 K X) (Subgroup.mem_zpowers _)
  have hD' : MulAut.conj s * σ * (MulAut.conj s)⁻¹ ∉ linearAutGroup 3 K := by
    intro hmem
    apply hD
    have hc : MulAut.conj s ∈ linearAutGroup 3 K := conj_mem_linearAutGroup s
    have := mul_mem (mul_mem (inv_mem hc) hmem) hc
    simpa [mul_assoc] using this
  obtain ⟨τ, hτ, H, hσ'⟩ :=
    linear_order_three_field_descent (by norm_num) _ (r2_conj_pow_three hσ s) hD'
  rw [hσ'] at hfix
  obtain ⟨c, hc3, hcore⟩ := exists_scalar_of_fix_L τ H ζ hX hfix
  obtain ⟨hc, hc1⟩ := core_gl τ H ζ c hcore
  have hcone : c = 1 := eq_one_of_pow_three (one_le_padicValNat_three hm3 hm0) hζ hc3 hc
  obtain ⟨hne1, hne2⟩ := frob_moves_zeta hp hf hK hm hm3 hm0 hζ hτ
  rcases hc1 hcone with h | h
  · exact hne1 h
  · exact hne2 h

end Z3Field

open Z3Field

theorem outerRow_projectiveSL_three_of_frobenius {K : Type} [Field K] [Finite K]
    [Finite (projectiveSL 3 K)] (hK : Nat.card K % 3 = 1) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hKpf : Nat.card K = p ^ f) (h3f : 3 ∣ f) {m : ℕ} (hm : p ^ (f / 3) = m + 1)
    (hm3 : m % 3 = 0) (hm0 : 0 < m) : OuterRow (projectiveSL 3 K) := by
  intro _ σ hσ hout hw
  by_cases hD : σ ∈ linearAutGroup 3 K
  · obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hD
    obtain ⟨p', f', hPi, hq⟩ := L3Outer.exists_piField_true hK
    have hker := L3Outer.conjAut_eq_one_iff (K := K)
    refine (L3Outer.not_autWeaklyClosed_of_diagonal hPi hq (conjAut 3 K)
      (MonoidHom.id (GL (Fin 3) K)) hker (fun g => mem_glPi_true _ g)
      (fun g hg => L3Outer.conjAut_mem_range_conj_of_slPi hg) (fun t ht => ⟨t, rfl⟩) (y := A)
      ?_ ?_) hw
    · intro hA
      obtain ⟨c, rfl⟩ := hA
      exact hout (by rw [conjAut_scalar]; exact one_mem _)
    · refine mk_eq_one_iff_mem_statedScalars.mp ((hker _).mp ?_)
      rw [map_pow, MonoidHom.id_apply]
      exact hσ
  · exact not_autWeaklyClosed_of_field_L hp hf hKpf h3f hm hm3 hm0 hσ hout hD hw

theorem outerRow_projSL_three_two_pow_of_three_dvd {n : ℕ} (hn : 1 ≤ n) (heven : n % 2 = 0)
    (h3 : n % 3 = 0) : OuterRow (projSL 3 (GaloisField 2 n)) := by
  haveI : Finite (projectiveSL 3 (GaloisField 2 n)) :=
    Finite.of_equiv _ (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n)).toEquiv
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hmod : Nat.card (GaloisField 2 n) % 3 = 1 := by
    rw [hcard]
    exact two_pow_mod_three_of_even (Nat.even_iff.mpr heven)
  have hr : (2 ^ (n / 3)) % 3 = 1 :=
    two_pow_mod_three_of_even (Nat.even_iff.mpr (by omega))
  have h4 : 2 ^ 2 ≤ 2 ^ (n / 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact OuterRow.of_mulEquiv (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n)).symm
    (outerRow_projectiveSL_three_of_frobenius hmod Nat.prime_two hn hcard (by omega)
      (m := 2 ^ (n / 3) - 1) (by omega) (by omega) (by omega))

theorem rowOf_seven_SL3_of_even_of_three_dvd : ∀ n : ℕ, 1 ≤ n → n % 2 = 0 → n % 3 = 0 →
    RowOf (projSL 3 (GaloisField 2 n)) := by
  intro n hn heven h3 S _ _ _ _ ⟨eS⟩
  exact GoodRow.of_mulEquiv eS.symm
    ⟨listRow_projSL_three_two_pow_of_even (Nat.even_iff.mpr heven) (by omega),
      outerRow_projSL_three_two_pow_of_three_dvd hn heven h3⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
