module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Quasithin.Vol2.Ch10SecC3H
public import CFSG.Quasithin.Vol2.Ch10SecC3I

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut)
open scoped Matrix commutatorElement

variable {K : Type} [Field K]

theorem isSimpleGroup_SL [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) : IsSimpleGroup (SL K) := by
  have : Fintype K := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
    exact ⟨s, hs⟩
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) K) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 2) le_rfl (Or.inr h4)).2.1
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
    ext A
    rw [Subgroup.mem_bot]
    constructor
    · intro hA
      obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
      have hr1 : r = 1 := by
        rw [Fintype.card_fin] at hr
        exact eq_one_of_sq_eq_one (by rw [← sq]; exact hr)
      apply Subtype.ext
      rw [← hrA, hr1]
      simp
    · rintro rfl
      exact Subgroup.one_mem _
  let e1 : ProjectiveSpecialLinearGroup (Fin 2) K ≃* SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact MulEquiv.isSimpleGroup e1.symm

@[expose] def ut : SL K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

theorem u_mul_ne [CharP K 2] : (u : SL K) * ut ≠ ut * u := by
  intro h
  have h1 := congrArg (fun M : SL K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h1
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [u, ut, h2] at h1

theorem commutator_SL [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    ⁅(⊤ : Subgroup (SL K)), (⊤ : Subgroup (SL K))⁆ = (⊤ : Subgroup (SL K)) := by
  have hs := isSimpleGroup_SL hK
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _
    (Subgroup.commutator_normal (⊤ : Subgroup (SL K)) ⊤) with h | h
  · exfalso
    apply u_mul_ne (K := K)
    have hc : ⁅(u : SL K), (ut : SL K)⁆ ∈ ⁅(⊤ : Subgroup (SL K)), (⊤ : Subgroup (SL K))⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem tau_mem_norm : tau K ∈ norm K := by
  rw [norm, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨g, rfl⟩
    rw [tau_conj_rho]
    exact rho_mem_img _
  · intro hx
    obtain ⟨g, hg⟩ := hx
    have : x = tau K * rho K g * (tau K)⁻¹ := by
      rw [hg, tau_inv]
      calc x = (tau K * tau K) * x * (tau K * tau K) := by rw [tau_mul_self, one_mul, mul_one]
        _ = tau K * (tau K * x * tau K) * tau K := by simp only [mul_assoc]
    rw [this, tau_conj_rho]
    exact rho_mem_img _

theorem sc_mul_rho (y : Kˣ) (g : SL K × SL K) : sc y * rho K g = rho K g * sc y := by
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  change (y : K) • ((g.1 : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
    (g.2 : Matrix (Fin 2) (Fin 2) K)ᵀ) = (g.1 : Matrix (Fin 2) (Fin 2) K) *
      ((y : K) • Multiplicative.toAdd X) * (g.2 : Matrix (Fin 2) (Fin 2) K)ᵀ
  rw [Matrix.mul_smul, Matrix.smul_mul]

end CFSG.Quasithin.Vol2.Ch10.C3.Om
