module

public import CFSG.Quasithin.Background.F7TwoInvL3TwoGen

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.CGT.Timmesfeld75
open CFSG.LieType.Steinberg.SL (blockHom)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def sl3ElemE (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : K)

@[expose] noncomputable def sl3InnerT (K : Type) [Field K] : MulAut (projectiveSL 3 K) :=
  conjAut 3 K (SpecialLinearGroup.toGL (sl3ElemE K))

theorem conjAut_toGL_apply_proj (h g : SpecialLinearGroup (Fin 3) K) :
    conjAut 3 K (SpecialLinearGroup.toGL h) (proj 3 K g) = proj 3 K (h * g * h⁻¹) := by
  rw [conjAut_proj]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  simp only [map_mul, map_inv]

theorem sl3InnerT_proj (g : SpecialLinearGroup (Fin 3) K) :
    sl3InnerT K (proj 3 K g) = proj 3 K (sl3ElemE K * g * (sl3ElemE K)⁻¹) :=
  conjAut_toGL_apply_proj _ _

theorem sl3InnerT_proj_of_commute {g : SpecialLinearGroup (Fin 3) K} (h : Commute (sl3ElemE K) g) :
    sl3InnerT K (proj 3 K g) = proj 3 K g := by
  rw [sl3InnerT_proj, h.eq, mul_inv_cancel_right]

theorem sl3ElemE_eq : sl3ElemE K = blockHom K 0 (utriElt 1) := (blockHom_zero_utriElt 1).symm

theorem sl3InnerT_sl3BlockRho_zero (g : SL(2, K)) :
    sl3InnerT K (sl3BlockRho K 0 g) = sl3BlockRho K 0 (MulAut.conj (utriElt (1 : K)) g) := by
  rw [sl3BlockRho_apply, sl3InnerT_proj, sl3ElemE_eq, sl3BlockRho_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv]

theorem commute_sl3ElemE_t02 (c : K) :
    Commute (sl3ElemE K) (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c) :=
  SpecialLinearGroup.commute_transvection _ _ (by decide) (by decide) _ _

theorem commute_sl3ElemE_t21 (c : K) :
    Commute (sl3ElemE K) (SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c) :=
  SpecialLinearGroup.commute_transvection _ _ (by decide) (by decide) _ _

theorem charP_two_of_exists_two_pow_card [Finite K] (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) :
    CharP K 2 := by
  obtain ⟨f, -, hKf⟩ := hK
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hKf)

omit [Field K] in
theorem four_le_natCard_of_exists_two_pow_card (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) :
    4 ≤ Nat.card K := by
  obtain ⟨f, hf, hKf⟩ := hK
  rw [hKf]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem eq_top_of_inner_transvections {H : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (h01 : ∀ c : K, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H)
    (h10 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ H)
    (h02 : ∀ c : K, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H)
    (h21 : ∀ c : K, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H) :
    H = ⊤ := by
  refine eq_top_of_sl3_transvections fun i j hij c => ?_
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · exact h02 c
  · exact h10 c
  · exact absurd rfl hij
  · have := commutatorElement_mem_of_mem (h10 c) (h02 1)
    rwa [SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) hij,
      mul_one] at this
  · have := commutatorElement_mem_of_mem (h21 1) (h10 c)
    rwa [SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) hij,
      one_mul] at this
  · exact h21 c
  · exact absurd rfl hij

theorem invAutGen_sl3InnerT [Finite K] (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) :
    InvAutGen (projectiveSL 3 K) (sl3InnerT K) := by
  have := charP_two_of_exists_two_pow_card hK
  have hu1 : (utriElt (1 : K)) ≠ 1 := fun h =>
    one_ne_zero (utriElt_injective (h.trans utriElt_zero.symm))
  have h0 : (sl3BlockRho K 0).range ≤ Subgroup.closure (invXiAut (sl3InnerT K)) :=
    range_le_closure_invXiAut (sl3BlockRho K 0) (sl3BlockRho_injective 0)
      (fun g => sl3InnerT_sl3BlockRho_zero g)
      (invAutGen_sl2_conj_involution (utriElt_mul_self 1) hu1
        (four_le_natCard_of_exists_two_pow_card hK))
  have hne : (invXiAut (sl3InnerT K)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Subgroup.closure_empty] at h0
    have h1 : sl3BlockRho K 0 (utriElt 1) = 1 := by
      simpa using h0 ⟨utriElt 1, rfl⟩
    exact hu1 (sl3BlockRho_injective 0 (h1.trans (map_one _).symm))
  have hfix := fixSubgroup_le_closure_invXiAut hne
  refine invAutGen_of_transvections fun i j hij c => ?_
  have key := eq_top_of_inner_transvections
    (H := (Subgroup.closure (invXiAut (sl3InnerT K))).comap (proj 3 K))
    (fun c => proj_transvection_mem_of_sl3BlockRho h0 (blockHom_zero_utriElt c))
    (fun c => proj_transvection_mem_of_sl3BlockRho h0 (blockHom_zero_ltriElt c))
    (fun c => hfix (sl3InnerT_proj_of_commute (commute_sl3ElemE_t02 c)))
    (fun c => hfix (sl3InnerT_proj_of_commute (commute_sl3ElemE_t21 c)))
  have hg : SpecialLinearGroup.transvection hij c ∈
      (Subgroup.closure (invXiAut (sl3InnerT K))).comap (proj 3 K) := by
    rw [key]
    trivial
  exact hg

end CFSG.Quasithin.F7Two
