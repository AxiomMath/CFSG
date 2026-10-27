module

public import CFSG.Quasithin.Background.F7TwoInvSp4Crit

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

theorem sp4_addSubgroup_eq_top_of_one_add_mem [CharP K 2] [Finite K] (h3 : 3 ≤ Nat.card K)
    (S : AddSubgroup K) (hS : ∀ u : K, u ≠ 0 → 1 + u ∈ S) : S = ⊤ := by
  classical
  refine (AddSubgroup.eq_top_iff' S).2 fun s => ?_
  have : Fintype K := Fintype.ofFinite K
  have hcard : 3 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({0, s} : Finset K))
    (t := Finset.univ) (by
      rw [Finset.card_univ]
      exact lt_of_le_of_lt Finset.card_le_two (by omega))
  have hu0 : u ≠ 0 := fun h => hu (by simp [h])
  have hus : u ≠ s := fun h => hu (by simp [h])
  have hus' : u + s ≠ 0 := fun h => hus (CharTwo.add_eq_zero.mp h)
  have h := S.add_mem (hS u hu0) (hS (u + s) hus')
  have e : (1 + u) + (1 + (u + s)) = s := by
    linear_combination (1 + u) * (CharTwo.two_eq_zero (R := K))
  rwa [e] at h

theorem sp4_root_group_le [CharP K 2] [Finite K] (h3 : 3 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (x : K → StatedSp 2 K) (hadd : ∀ s s', x s * x s' = x (s + s')) (hzero : x 0 = 1)
    (χ : (Fin 2 → Kˣ) → K)
    (hχ : ∀ τ s, torusHom τ * x s * (torusHom τ)⁻¹ = x (χ τ * s))
    (hsurj : ∀ u : K, u ≠ 0 → ∃ τ, χ τ = u)
    (hT : ∀ τ : Fin 2 → Kˣ, torusHom τ ∈ H)
    (hb : ∀ τ : Fin 2 → Kˣ, x 1 * torusHom τ * (x 1)⁻¹ ∈ H) : ∀ s, x s ∈ H := by
  have hx1 : (x 1)⁻¹ = x 1 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hadd, CharTwo.add_self_eq_zero, hzero]
  have hone : ∀ τ, x (1 + χ τ) ∈ H := by
    intro τ
    have h1 := mul_mem (hb τ) (inv_mem (hT τ))
    have h2 : x 1 * torusHom τ * (x 1)⁻¹ * (torusHom τ)⁻¹ = x (1 + χ τ) := by
      calc x 1 * torusHom τ * (x 1)⁻¹ * (torusHom τ)⁻¹
          = x 1 * (torusHom τ * x 1 * (torusHom τ)⁻¹) := by rw [hx1]; group
        _ = x 1 * x (χ τ * 1) := by rw [hχ]
        _ = x (1 + χ τ) := by rw [hadd, mul_one]
    rwa [h2] at h1
  let S : AddSubgroup K :=
    { carrier := {s | x s ∈ H}
      zero_mem' := by
        change x 0 ∈ H
        rw [hzero]
        exact one_mem H
      add_mem' := fun {s s'} hs hs' => by
        change x (s + s') ∈ H
        rw [← hadd]
        exact mul_mem hs hs'
      neg_mem' := fun {s} hs => by
        change x (-s) ∈ H
        have : x (-s) = (x s)⁻¹ := eq_inv_of_mul_eq_one_right (by rw [hadd, add_neg_cancel, hzero])
        rw [this]
        exact inv_mem hs }
  have hS : S = ⊤ := sp4_addSubgroup_eq_top_of_one_add_mem h3 S fun u hu => by
    obtain ⟨τ, rfl⟩ := hsurj u hu
    exact hone τ
  intro s
  have hs : s ∈ S := by rw [hS]; trivial
  exact hs

@[expose] def sp4SymE : Fin 3 → Matrix (Fin 2) (Fin 2) K :=
  ![!![1, 0; 0, 0], !![0, 0; 0, 1], !![0, 1; 1, 0]]

theorem sp4SymE_transpose (i : Fin 3) : (sp4SymE i : Matrix (Fin 2) (Fin 2) K)ᵀ = sp4SymE i := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;> simp [sp4SymE])

theorem sp4SymE_map (σ : K ≃+* K) (i : Fin 3) :
    (sp4SymE i : Matrix (Fin 2) (Fin 2) K).map σ = sp4SymE i := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;> simp [sp4SymE])

@[expose] noncomputable def sp4UpRoot (i : Fin 3) (s : K) : StatedSp 2 K :=
  upperUnipotentSp 2 K (C := s • sp4SymE i) (by rw [transpose_smul, sp4SymE_transpose])

@[expose] noncomputable def sp4LowRoot (i : Fin 3) (s : K) : StatedSp 2 K :=
  lowerSp (C := s • sp4SymE i) (by rw [transpose_smul, sp4SymE_transpose])

theorem sp4UpRoot_add (i : Fin 3) (s s' : K) :
    sp4UpRoot i s * sp4UpRoot i s' = sp4UpRoot i (s + s') := by
  refine statedSp_ext ?_
  unfold sp4UpRoot
  rw [Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp, coe_upperUnipotentSp,
    coe_upperUnipotentSp, fromBlocks_multiply]
  simp [add_smul, add_comm]

theorem sp4UpRoot_zero (i : Fin 3) : sp4UpRoot i (0 : K) = 1 := by
  refine statedSp_ext ?_
  unfold sp4UpRoot
  rw [coe_upperUnipotentSp, zero_smul, fromBlocks_one]
  rfl

theorem sp4LowRoot_add [CharP K 2] (i : Fin 3) (s s' : K) :
    sp4LowRoot i s * sp4LowRoot i s' = sp4LowRoot i (s + s') := by
  refine statedSp_ext ?_
  unfold sp4LowRoot
  rw [Subgroup.coe_mul, Units.val_mul, coe_lowerSp, coe_lowerSp, coe_lowerSp, fromBlocks_multiply]
  simp [add_smul, add_comm]

theorem sp4LowRoot_zero [CharP K 2] (i : Fin 3) : sp4LowRoot i (0 : K) = 1 := by
  refine statedSp_ext ?_
  unfold sp4LowRoot
  rw [coe_lowerSp, zero_smul, fromBlocks_one]
  rfl

@[expose] def sp4CharQ (i : Fin 3) (d : Fin 2 → K) : K := ![d 0 * d 0, d 1 * d 1, d 0 * d 1] i

theorem sp4_diag_mul_symE (i : Fin 3) (d : Fin 2 → K) :
    diagonal d * sp4SymE i * diagonal d =
      sp4CharQ i d • (sp4SymE i : Matrix (Fin 2) (Fin 2) K) := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;>
    simp [sp4SymE, sp4CharQ, diagonal_mul, mul_diagonal] <;> ring)

theorem sp4CharQ_surj [CharP K 2] [Finite K] (i : Fin 3) (u : K) (hu : u ≠ 0) :
    ∃ τ : Fin 2 → Kˣ, sp4CharQ i (fun j => (τ j : K)) = u := by
  obtain ⟨w, hw⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) u
  have hw0 : w ≠ 0 := fun h => hu (by rw [hw, h, mul_zero])
  fin_cases i
  · exact ⟨![Units.mk0 w hw0, 1], by simp [sp4CharQ, hw]⟩
  · exact ⟨![1, Units.mk0 w hw0], by simp [sp4CharQ, hw]⟩
  · exact ⟨![Units.mk0 u hu, 1], by simp [sp4CharQ]⟩

theorem sp4_torusHom_mul_sp4UpRoot_mul_inv (τ : Fin 2 → Kˣ) (i : Fin 3) (s : K) :
    torusHom τ * sp4UpRoot i s * (torusHom τ)⁻¹ =
      sp4UpRoot i (sp4CharQ i (fun j => (τ j : K)) * s) := by
  change leviSp (TauCeti.diagGL τ) * upperUnipotentSp 2 K _ * (leviSp (TauCeti.diagGL τ))⁻¹ = _
  rw [leviSp_mul_ut_mul_inv]
  refine ut_congr ?_ _ _
  rw [TauCeti.diagGL_coe, diagonal_transpose, Matrix.mul_smul, Matrix.smul_mul,
    sp4_diag_mul_symE, smul_smul, mul_comm]

theorem sp4_torusHom_mul_sp4LowRoot_mul_inv [CharP K 2] (τ : Fin 2 → Kˣ) (i : Fin 3) (s : K) :
    torusHom τ * sp4LowRoot i s * (torusHom τ)⁻¹ =
      sp4LowRoot i (sp4CharQ i (fun j => (((τ j)⁻¹ : Kˣ) : K)) * s) := by
  change leviSp (TauCeti.diagGL τ) * lowerSp _ * (leviSp (TauCeti.diagGL τ))⁻¹ = _
  rw [leviSp_mul_lowerSp_mul_inv]
  refine lowerSp_congr ?_ _ _
  rw [← map_inv, TauCeti.diagGL_coe, diagonal_transpose, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Pi.inv_apply]
  rw [sp4_diag_mul_symE, smul_smul, mul_comm]

theorem sp4SymE_zero_mul_self : (sp4SymE 0 : Matrix (Fin 2) (Fin 2) K) * sp4SymE 0 = sp4SymE 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [sp4SymE, Matrix.mul_apply, Fin.sum_univ_two]

theorem sp4SymE_one_mul_self : (sp4SymE 1 : Matrix (Fin 2) (Fin 2) K) * sp4SymE 1 = sp4SymE 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [sp4SymE, Matrix.mul_apply, Fin.sum_univ_two]

theorem sp4_coe_n_symE [CharP K 2] (i : Fin 3)
    (hi : (sp4SymE i : Matrix (Fin 2) (Fin 2) K) * sp4SymE i = sp4SymE i) :
    (((sp4UpRoot i 1 * sp4LowRoot i 1 * sp4UpRoot i 1 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (1 + sp4SymE i) (sp4SymE i) (sp4SymE i) (1 + sp4SymE i) := by
  unfold sp4UpRoot sp4LowRoot
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_upperUnipotentSp,
    coe_lowerSp, fromBlocks_multiply, fromBlocks_multiply]
  have hE2 : sp4SymE i + sp4SymE i = (0 : Matrix (Fin 2) (Fin 2) K) := CharTwo.add_self_eq_zero _
  simp [hi]
  exact ⟨by rw [add_mul, one_mul, hi, hE2], add_comm _ _⟩

theorem sp4J_eq_mul [CharP K 2] :
    (sp4J : StatedSp 2 K) = (sp4UpRoot 0 1 * sp4LowRoot 0 1 * sp4UpRoot 0 1) *
      (sp4UpRoot 1 1 * sp4LowRoot 1 1 * sp4UpRoot 1 1) := by
  refine statedSp_ext ?_
  rw [Subgroup.coe_mul, Units.val_mul, sp4_coe_n_symE 0 sp4SymE_zero_mul_self,
    sp4_coe_n_symE 1 sp4SymE_one_mul_self, fromBlocks_multiply, coe_sp4J]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [sp4SymE, Matrix.one_fin_two, CharTwo.neg_eq] <;>
    (ext a b; fin_cases a <;> fin_cases b <;> simp [CharTwo.add_self_eq_zero])

theorem sp4_eq_top_of_torus_conj [CharP K 2] [Finite K] (h3 : 3 ≤ Nat.card K)
    {H : Subgroup (StatedSp 2 K)} (hT : ∀ τ : Fin 2 → Kˣ, torusHom τ ∈ H)
    (hX : ∀ (i : Fin 3) (τ : Fin 2 → Kˣ), sp4UpRoot i 1 * torusHom τ * (sp4UpRoot i 1)⁻¹ ∈ H)
    (hY : ∀ (i : Fin 3) (τ : Fin 2 → Kˣ), sp4LowRoot i 1 * torusHom τ * (sp4LowRoot i 1)⁻¹ ∈ H) :
    H = ⊤ := by
  have hup : ∀ (i : Fin 3) (s : K), sp4UpRoot i s ∈ H := fun i =>
    sp4_root_group_le h3 (sp4UpRoot i) (sp4UpRoot_add i) (sp4UpRoot_zero i)
      (fun τ => sp4CharQ i (fun j => (τ j : K))) (sp4_torusHom_mul_sp4UpRoot_mul_inv · i)
      (fun u hu => sp4CharQ_surj i u hu) hT (hX i)
  have hlow : ∀ (i : Fin 3) (s : K), sp4LowRoot i s ∈ H := fun i =>
    sp4_root_group_le h3 (sp4LowRoot i) (sp4LowRoot_add i) (sp4LowRoot_zero i)
      (fun τ => sp4CharQ i (fun j => (((τ j)⁻¹ : Kˣ) : K)))
      (sp4_torusHom_mul_sp4LowRoot_mul_inv · i)
      (fun u hu => by
        obtain ⟨τ, hτ⟩ := sp4CharQ_surj i u hu
        exact ⟨τ⁻¹, by simpa using hτ⟩) hT (hY i)
  refine eq_top_of_tau_mem_of_sp4J_mem (fun C hC => ?_) ?_
  · have hC10 : C 1 0 = C 0 1 := by simpa using congrFun₂ hC 0 1
    have hdec : C = C 0 0 • sp4SymE 0 + C 1 1 • sp4SymE 1 + C 0 1 • sp4SymE 2 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sp4SymE, hC10]
    have h : upperUnipotentSp 2 K hC =
        sp4UpRoot 0 (C 0 0) * sp4UpRoot 1 (C 1 1) * sp4UpRoot 2 (C 0 1) := by
      unfold sp4UpRoot
      rw [ut_mul, ut_mul]
      exact ut_congr hdec _ _
    rw [h]
    exact mul_mem (mul_mem (hup 0 _) (hup 1 _)) (hup 2 _)
  · rw [sp4J_eq_mul]
    exact mul_mem (mul_mem (mul_mem (hup 0 1) (hlow 0 1)) (hup 0 1))
      (mul_mem (mul_mem (hup 1 1) (hlow 1 1)) (hup 1 1))

end CFSG.Quasithin.F7Two
