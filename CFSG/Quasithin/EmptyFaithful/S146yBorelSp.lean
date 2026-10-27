module

public import CFSG.Quasithin.EmptyFaithful.S146yBorelBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplecticAut
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LocalAnalysis.ComponentInitial.SymplecticFour Matrix

namespace CFSG.Quasithin

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem core_statedSp_two (hK : 4 ≤ Nat.card K) :
    ∀ x : StatedSp 2 K, x * x = 1 → (∀ b ∈ borelSubgroup 2 K, x * b = b * x) → x = 1 := by
  intro x hx hc
  obtain ⟨-, ⟨S, hS⟩, -, -, -, -, -, hcenter, -⟩ :=
    unique_symplectic_four_Sylow_center (K := K) (Nat.card K) rfl
  have hxU : x ∈ unipotent 2 K := by
    rw [← hS]
    exact mem_sylow_of_involution_commute S hx
      (fun s hs => hc s (unipotent_le_borelSubgroup (hS ▸ hs)))
  have hxcenter : (⟨x, hxU⟩ : unipotent 2 K) ∈ Subgroup.center (unipotent 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g (unipotent_le_borelSubgroup g.2)).symm
  obtain ⟨b, c, hxbc⟩ := (hcenter ⟨x, hxU⟩).mp hxcenter
  have hxbc' : x = tau (sym2_transpose b c 0) := hxbc
  obtain ⟨t, ht⟩ : ∃ t : Kˣ, t ≠ 1 := by
    have h4 : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
    have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h4
    exact exists_ne 1
  let A : Matrix (Fin 2) (Fin 2) K := diagonal ![(t : K), 1]
  have hAdet : IsUnit A.det := by
    simp [A]
  have hAup : A.IsUpperTriangular := fun i j hij => diagonal_apply_ne _ (ne_of_gt hij)
  let h : StatedSp 2 K := blockElt hAdet (C := 0) transpose_zero
  have hh : h ∈ borelSubgroup 2 K :=
    mem_borelSubgroup_of_coe_eq_blockMat hAup hAdet (coe_blockElt hAdet transpose_zero)
  have hcomm := hc h hh
  have hM : ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * blockMat A 0 =
      blockMat A 0 * ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have := congrArg (fun g : StatedSp 2 K =>
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hcomm
    simpa [Subgroup.coe_mul, Units.val_mul, h, coe_blockElt] using this
  rw [hxbc', coe_tau] at hM
  rw [blockMat, fromBlocks_multiply, fromBlocks_multiply] at hM
  have hB := congrArg Matrix.toBlocks₁₂ hM
  simp only [Matrix.mul_zero, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    toBlocks_fromBlocks₁₂] at hB
  have htne : (t : K) ≠ 0 := t.ne_zero
  have hAinv : A⁻¹ = diagonal ![(t : K)⁻¹, 1] := by
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [htne]
  rw [hAinv, diagonal_transpose] at hB
  have h00 := congrFun₂ hB 0 0
  have h01 := congrFun₂ hB 0 1
  simp [sym2, A, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  have htK : (t : K) ≠ 1 := fun h' => ht (Units.ext h')
  have hc0 : c = 0 := by
    have h1 : c * ((t : K) - 1) = 0 := by linear_combination (-1 : K) * h01
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (sub_eq_zero.mp h2) htK
  have hb0 : b = 0 := by
    have h1 : b = (t : K) * t * b := by
      calc b = b * (t : K)⁻¹ * t := (inv_mul_cancel_right₀ htne b).symm
        _ = t * b * t := by rw [h00]
        _ = t * t * b := by ring
    have h2 : b * ((t - 1 : K) * (t - 1)) = 0 := by
      have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination (-1 : K) * h1 + b * (1 - t) * h3
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact h4
    · rcases mul_eq_zero.mp h4 with h5 | h5 <;> exact absurd (sub_eq_zero.mp h5) htK
  rw [hxbc', hb0, hc0]
  apply SymplecticTorusWeyl.statedSp_ext
  have hs0 : sym2 (0 : K) 0 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym2]
  rw [coe_tau, hs0, fromBlocks_one]
  rfl

omit [Finite K] [CharP K 2] in
theorem statedSp_two_not_comm : ∃ a b : StatedSp 2 K, a * b ≠ b * a := by
  refine ⟨lam 1, tau (sym2_transpose (0 : K) 0 1), fun h => ?_⟩
  have h1 : lam (1 : K) * tau (sym2_transpose (0 : K) 0 1) * (lam (1 : K))⁻¹ =
      tau (sym2_transpose (0 : K) 0 1) := by
    rw [h]
    group
  rw [lam_mul_tau_mul_inv] at h1
  have h2 := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h1
  simp only [coe_tau] at h2
  have h3 := congrArg Matrix.toBlocks₁₂ h2
  simp only [toBlocks_fromBlocks₁₂] at h3
  have h4 := congrFun₂ h3 0 0
  simp [unitri, sym2, Matrix.mul_apply, Fin.sum_univ_two] at h4

noncomputable def statedSpEquivProj : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
  MulEquiv.ofBijective (SymplecticFlag.proj 2 K)
    ⟨K1.proj_injective_charTwo, SymplecticHigher.proj_surjective⟩

theorem borelRigid_statedSp_two (hK : 4 ≤ Nat.card K) (hsimple : IsSimpleGroup (StatedSp 2 K)) :
    BorelRigid (StatedSp 2 K) := by
  obtain ⟨-, ⟨S, hS⟩, -, -, -, -, -, -, -⟩ :=
    unique_symplectic_four_Sylow_center (K := K) (Nat.card K) rfl
  have h0 : IsSylowTwoOf (unipotent 2 K) ⊤ := by
    rw [← hS]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  have hZ : Subgroup.center (StatedSp 2 K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedSp 2 K)) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := statedSp_two_not_comm (K := K)
      apply hab
      have : a ∈ Subgroup.center (StatedSp 2 K) := by rw [ht]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  refine borelRigid_of_inner (K1.SylowCentralizingAutInner.of_mulEquiv statedSpEquivProj
    K1.sylowCentralizingAutInner_statedProj) hZ h0 ?_
  rw [SymplecticHigher.normalizer_unipotent (r := 2) (K := K)]
  exact core_statedSp_two hK

end Four

theorem borelRigid_psp4 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f) (h : IsPSp4 2 f X) :
    BorelRigid X := by
  have hsimpleX : IsSimpleGroup X :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 2 2 f h
  obtain ⟨-, K, _, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* StatedSp 2 K := e.trans statedSpEquivProj.symm
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : IsSimpleGroup (StatedSp 2 K) := e'.symm.isSimpleGroup
  exact BorelRigid.of_mulEquiv e' (borelRigid_statedSp_two hK4 this)

end CFSG.Quasithin
