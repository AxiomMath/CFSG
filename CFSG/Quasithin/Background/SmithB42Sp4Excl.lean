module

public import CFSG.Quasithin.Background.SmithB42Sp4Desc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal

public section

namespace CFSG.Quasithin.B42Sp4

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem rank_fromBlocks_one_zero {K : Type} [Field K] (r s : ℕ) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0
      (0 : Matrix (Fin s) (Fin s) K)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0
      (0 : Matrix (Fin s) (Fin s) K)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin r => (1 : K)) (fun _ : Fin s => (0 : K))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem rank_map_eq {K L : Type} [Field K] [Field L] (φ : K →+* L) {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m K) : (A.map φ).rank = A.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form A
  have hVf : IsUnit (V.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hV.map φ.mapMatrix)
  have hUf : IsUnit (U.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hU.map φ.mapMatrix)
  have hE : (A.map φ).rank = ((V.map φ) * (A.map φ) * (U.map φ)).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUf,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * A * U).map φ = ((Matrix.fromBlocks (1 : Matrix (Fin A.rank) (Fin A.rank) K) 0 0
      (0 : Matrix (Fin (Fintype.card m - A.rank)) (Fin (Fintype.card m - A.rank)) K)).submatrix
        e e).map φ := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ)] at h1
  rw [hE, h1, Matrix.rank_submatrix, rank_fromBlocks_one_zero]

section Rank

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]

theorem rank_natRepS_sub_one_eq (z : antiSp F) (i : ℕ) :
    (natRepS k i z - 1).rank = if i % 2 = 0 then rk0 z else rk1 z := by
  have h : natRepS k i z - 1 = (natRepS F i z - 1).map (algebraMap F k) := by
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b),
      Matrix.map_one _ (map_zero _) (map_one _), natRepS_apply, natRepS_apply]
    congr 1
  rw [h, rank_map_eq, rank_natRepS_parity]

end Rank

section Excl

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

abbrev repOf (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) : Representation (ZMod 2) (antiSp F) M :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := M)).comp π

omit [CharP F 2] [Fintype F] [Finite M] in
theorem repOf_apply (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) (g : antiSp F) :
    repOf π g = (π g).toLinearMap := rfl

theorem eight_mul_le_four_pow {s : ℕ} (hs : 2 ≤ s) : 8 * s ≤ 4 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    omega

theorem displacement_ge {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hdim : Module.finrank (EndRing (repOf π)) M ≠ 4)
    {z : antiSp F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    3 * f ≤ dispRank (π z) ∧ (rk0 z = 2 → rk1 z = 2 → 4 * f ≤ dispRank (π z)) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sp4_descent hF hf hnt
  have : Module.Finite (EndRing (repOf π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, S, hSne, hS, ⟨Φ⟩, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOf π)) M)
  let _ : Algebra F E := ιF.toAlgebra
  have hdisp : dispRank (π z) = d * (tensorRepS (F := F) E S z - 1).rank :=
    finrank_range_eq hDcard _ ιF ιD S Φ hdimW z
  have hs1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hs2 : 2 ≤ S.card := by
    by_contra h
    have h1 : S.card = 1 := by omega
    rw [h1, pow_one] at hdimW
    exact hdim hdimW
  have hfd : f ≤ S.card * d := by
    have h := n_le_card_mul (n := 2 * f) (d := 2 * d) (by omega) (by omega)
      (fun i hi => Finset.mem_range.mp (hS hi)) hSne hshift
    nlinarith
  have h6 := six_mul_add_two_pow_le hs2
  have h8 := eight_mul_le_four_pow hs2
  refine ⟨?_, fun h0 h1 => ?_⟩
  · have hge := rank_tensorRepS_sub_one_ge E S hz hz1
    rw [hdisp]
    have h3 : 3 * S.card ≤ (4 ^ S.card - 2 ^ S.card) / 2 := by omega
    calc 3 * f ≤ 3 * (S.card * d) := Nat.mul_le_mul_left 3 hfd
      _ = d * (3 * S.card) := by ring
      _ ≤ d * (tensorRepS (F := F) E S z - 1).rank :=
          Nat.mul_le_mul_left d (h3.trans hge)
  · obtain ⟨i, hi⟩ := hSne
    have hr2 : (natRepS E i z - 1).rank = 2 := by
      rw [rank_natRepS_sub_one_eq]
      split_ifs <;> assumption
    have heq := rank_tensorRepS_sub_one_of_rank_two E S hz hi hr2
    rw [hdisp, heq]
    have h4 : 4 * S.card ≤ 4 ^ S.card / 2 := by omega
    calc 4 * f ≤ 4 * (S.card * d) := Nat.mul_le_mul_left 4 hfd
      _ = d * (4 * S.card) := by ring
      _ ≤ d * (4 ^ S.card / 2) := Nat.mul_le_mul_left d h4

theorem card_mul_card_fixed_lt_of_ne_four {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card F = 2 ^ f) (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π)
    [Fact (repOf π).IsIrreducible] (hdim : Module.finrank (EndRing (repOf π)) M ≠ 4)
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  classical
  have hKf : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have := hAe
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [_root_.sq] at this
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb' => by
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨b, hb'⟩)
  have hπ'inj : Function.Injective (repOf π) := fun g g' hg =>
    hπ (LinearEquiv.toLinearMap_injective hg)
  have hπ'nt : ∃ g, repOf π g ≠ 1 :=
    ⟨invX F, fun h1 => invX_ne_one (hπ'inj (h1.trans (map_one (repOf π)).symm))⟩
  obtain ⟨hnontriv, hirr⟩ :=
    (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOf π)).mp Fact.out
  have hsum : SimpleSummandsStable π A := by
    obtain ⟨g, hg⟩ := hπ'nt
    obtain ⟨x, hx⟩ : ∃ x, repOf π g x ≠ x := by
      by_contra h
      push Not at h
      exact hg (LinearMap.ext fun x => by rw [h x]; rfl)
    refine ⟨Unit, fun _ => ⊤, iSupIndep_subsingleton _, iSup_const, fun _ =>
      ⟨top_ne_bot, ⟨x, Submodule.mem_top, g, hx⟩, fun _ _ _ => Submodule.mem_top,
        fun U _ hU => hirr U hU, fun _ _ _ _ => Submodule.mem_top⟩⟩
  have H : Offender π A := ⟨hπ, hnorm, hsq, hcomm, hsum⟩
  obtain ⟨-, hcyc, hcard, hN24⟩ :=
    even_symplectic_four_outer_involution_rank_and_perfect_residual hf hK
  have : Finite (Outer (antiSp F)) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have h25 : ∀ z : antiSp F, z * z = 1 → z ≠ 1 → 3 * f ≤ dispRank (π z) ∧
      (rk0 z = 2 → rk1 z = 2 → 4 * f ≤ dispRank (π z)) := fun z hz hz1 =>
    displacement_ge hKf (by omega) π hπ'nt hdim hz hz1
  have hmax := (involution_rank_pairs_and_maximal_elementary_witness hK).2.2
  have h24 : ∀ θ : MulAut (antiSp F), θ * θ = 1 → θ ∉ inner (antiSp F) →
      ∀ E : Subgroup (antiSp F), E ≤ fixedSubgroup θ → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 2 ^ (if Even f then 3 * (f / 2) else 2 * f) :=
    fun θ hθ hθinn E hE hEsq => (hN24 θ hθ hθinn).2.1 E hE hEsq
  have h26 : ∀ a : A, normAut π H.inj A H.norm a ∉ inner (antiSp F) → 4 ≤ dispRank a.1 := by
    intro a ha
    have ha1 : a.1 ≠ 1 := fun h1 => ha (by
      have : a = 1 := Subtype.ext h1
      rw [this, map_one]
      exact one_mem _)
    have hord : orderOf a.1 = 2 :=
      orderOf_eq_prime (by rw [_root_.sq]; exact hsq a.1 a.2) ha1
    exact outer_involutions_have_binary_displacement_at_least_four hf hKf (repOf π) hπ'inj a.1
      hord (normAut π H.inj A H.norm a) ha (fun g w => by
        have := π_normAut π H.inj A H.norm a g
        have h2 := congrArg (fun e : M ≃ₗ[ZMod 2] M => e w) this
        exact h2.symm)
  exact offender_reduction hf H hA1 hcyc h25 hmax h24 h26

end Excl

end CFSG.Quasithin.B42Sp4
