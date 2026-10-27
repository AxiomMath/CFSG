module

public import CFSG.Quasithin.Vol2.F134LieSp4Borel

public section

namespace CFSG.Quasithin.S146zY

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher SymplecticFour Submodule
open CFSG.Quasithin.F134.Sp4

variable {K : Type} [Field K]

local notation "M[" g "]" => Units.val (Subtype.val g)

theorem sp4_tau_sym2_mulVec_inr_one (a b : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (M[tau (sym2_transpose a b 0)] *ᵥ v) (Sum.inr 1) = v (Sum.inr 1) := by
  rw [coe_tau]
  simp [mulVec, dotProduct, Fin.sum_univ_two, sym2]

theorem sp4_lam_mulVec_inl_zero (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (M[lam c] *ᵥ v) (Sum.inl 0) = v (Sum.inl 0) + c * v (Sum.inl 1) := by
  rw [coe_lam]
  simp [mulVec, dotProduct, Fin.sum_univ_two, unitri]

theorem sp4_lam_mulVec_inl_one (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (M[lam c] *ᵥ v) (Sum.inl 1) = v (Sum.inl 1) := by
  rw [coe_lam]
  simp [mulVec, dotProduct, Fin.sum_univ_two, unitri]

theorem sp4_lam_mulVec_inr_zero (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (M[lam c] *ᵥ v) (Sum.inr 0) = v (Sum.inr 0) := by
  rw [coe_lam]
  simp [mulVec, dotProduct, Fin.sum_univ_two, unitri]

theorem sp4_lam_mulVec_inr_one (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (M[lam c] *ᵥ v) (Sum.inr 1) = v (Sum.inr 1) - c * v (Sum.inr 0) := by
  rw [coe_lam]
  simp [mulVec, dotProduct, Fin.sum_univ_two, unitri]
  ring

theorem mulVec_e1_inr_zero_of_card_lt_cube [Finite K] {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hcard : Nat.card P < Nat.card K ^ 3) {x : StatedSp 2 K} (hx : x ∈ P) :
    (M[x] *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K)) (Sum.inr 0) = 0 := by
  by_contra hne
  set v := M[x] *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) with hv
  have key : ∀ p : K × K × K, ∃ y : P, M[(y : StatedSp 2 K)] *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) =
        M[tau (sym2_transpose p.1 p.2.1 0)] *ᵥ (M[lam p.2.2] *ᵥ v) := by
    intro p
    obtain ⟨y, hy, hyv⟩ := exists_mulVec_e1 hPU
      (mul_mem (tau_mem_unipotent (sym2_transpose p.1 p.2.1 0)) (lam_mem_unipotent p.2.2)) hx
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hyv, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
  choose f hf using key
  have hinj : Function.Injective f := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ hpp'
    have h := (hf (a, b, c)).symm.trans ((congrArg (fun y : P => M[(y : StatedSp 2 K)] *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K)) hpp').trans (hf (a', b', c')))
    have h0 := congrFun h (Sum.inl 0)
    have h1 := congrFun h (Sum.inl 1)
    have h3 := congrFun h (Sum.inr 1)
    simp only [tau_sym2_mulVec_inl_zero, tau_sym2_mulVec_inl_one, sp4_tau_sym2_mulVec_inr_one,
      sp4_lam_mulVec_inl_zero, sp4_lam_mulVec_inl_one, sp4_lam_mulVec_inr_zero,
      sp4_lam_mulVec_inr_one] at h0 h1 h3
    have hc : c = c' := mul_right_cancel₀ hne (by linear_combination (-1 : K) * h3)
    subst hc
    have hb : b = b' := mul_right_cancel₀ hne (by linear_combination h1)
    subst hb
    have ha : a = a' := mul_right_cancel₀ hne (by linear_combination h0)
    subst ha
    rfl
  have hle := Nat.card_le_card_of_injective f hinj
  have hcube : Nat.card (K × K × K) = Nat.card K ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod]
    ring
  omega

theorem exists_le_stabilizer_flag_of_card_lt_cube [Finite K] {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hcard : Nat.card P < Nat.card K ^ 3) :
    ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ P ≤ stabilizer 2 K (flag 2 K d) := by
  set s : P → Fin 2 ⊕ Fin 2 → K := fun y =>
    M[(y : StatedSp 2 K)] *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) with hs
  set W := span K (Set.range s) with hW
  have hiso : IsTotallyIsotropic (pairedSympForm K 2) W := by
    refine isTotallyIsotropic_span_range fun y z => ?_
    have h := pairedSympForm_mulVec ((y : StatedSp 2 K)⁻¹) (s y) (s z)
    simp only [hs] at h ⊢
    rw [← h, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one, one_mulVec,
      pairedSympForm_single_inl]
    exact mulVec_e1_inr_zero_of_card_lt_cube hPU hcard (P.mul_mem (P.inv_mem y.2) z.2)
  have hmap : ∀ g : StatedSp 2 K, (∀ y : P, ∃ y' : P, s y' = M[g] *ᵥ s y) →
      ∀ v ∈ W, M[g] *ᵥ v ∈ W := by
    intro g hg v hv
    have hle : W ≤ W.comap (mulVecLin M[g]) := by
      rw [hW, span_le]
      rintro _ ⟨y, rfl⟩
      obtain ⟨y', hy'⟩ := hg y
      change M[g] *ᵥ s y ∈ W
      rw [← hy']
      exact subset_span ⟨y', rfl⟩
    exact hle hv
  have hU : ∀ u ∈ unipotent 2 K, ∀ v ∈ W, M[u] *ᵥ v ∈ W := by
    intro u hu
    refine hmap u fun y => ?_
    obtain ⟨y', hy', h⟩ := exists_mulVec_e1 hPU hu y.2
    exact ⟨⟨y', hy'⟩, h⟩
  have hP : P ≤ stabilizer 2 K W := by
    intro g hg
    refine mem_stabilizer_of_mulVec_mem' (hmap g fun y => ⟨⟨g * y, P.mul_mem hg y.2⟩, ?_⟩)
    simp only [hs, Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]
  obtain ⟨d, hd, hWd⟩ :=
    ((unitriangular_invariant_isotropic_subspaces (r := 2) (K := K)).2.1 W).mp ⟨hiso, hU⟩
  have he1 : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    have : s 1 = Pi.single (Sum.inl 0) 1 := by
      simp only [hs, OneMemClass.coe_one, Units.val_one, one_mulVec]
    rw [← this]
    exact subset_span ⟨1, rfl⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [hWd, mem_flag_of_le (by norm_num), mem_isoFlag] at he1
    simpa using he1.2 0 (by simp)
  exact ⟨d, by omega, hWd ▸ hP⟩

end CFSG.Quasithin.S146zY
