module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneFrame
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameMatrix
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusNorm
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField

public section

namespace CFSG.StandardType.SpJoin

open Polynomial Module Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.StandardType.SpNS

variable {F : Type} [Field F] {p : ℕ}

theorem sl2W_conj_spCompanion (h2 : (2 : F) = 0) (t : F) :
    sl2W * spCompanion t * sl2W⁻¹ = (spCompanion t)⁻¹ := by
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  have hneg : (-1 : F) = 1 := neg_eq_iff_add_eq_zero.mpr h11
  rw [mul_inv_eq_iff_eq_mul]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_spCompanion, adjugate_fin_two_of]
  fin_cases i <;> fin_cases j <;>
    simp [sl2W, mul_apply, Fin.sum_univ_two, hneg]

theorem spPlaneZetaCompanion_conj_sl2W (hp : p.Prime) (h2 : (2 : F) = 0) (t : F)
    (ht : spCompanion t ^ p = 1) (a : Multiplicative (ZMod p)) :
    sl2W * spPlaneZetaCompanion t ht a * sl2W⁻¹ = spPlaneZetaCompanion t ht a⁻¹ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [map_inv, spPlaneZetaCompanion, CFSG.StandardType.TableBSymp.zmodPowHom_apply ht a,
    ← conj_pow, sl2W_conj_spCompanion h2 t, inv_pow]

theorem spCompanion_pow_eq_one (hp : p.Prime) {t : F}
    (hgd : (X ^ 2 + C t * X + 1 : F[X]) ∣ cyclotomic p F) : spCompanion t ^ p = 1 := by
  let M : Matrix (Fin 2) (Fin 2) F := (spCompanion t : SpecialLinearGroup (Fin 2) F)
  have hM : M = !![0, -1; 1, -t] := coe_spCompanion t
  have hCH : aeval M (X ^ 2 + C t * X + 1 : F[X]) = 0 := by
    have hquad : aeval M (X ^ 2 + C t * X + 1 : F[X]) = M ^ 2 + t • M + 1 := by
      simp [map_add, map_mul, map_pow, Algebra.smul_def]
    rw [hquad, hM]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hdiv : (X ^ 2 + C t * X + 1 : F[X]) ∣ X ^ p - 1 :=
    hgd.trans (Polynomial.cyclotomic.dvd_X_pow_sub_one p F)
  have hp1 : aeval M (X ^ p - 1 : F[X]) = 0 :=
    Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hCH
  have hMp : M ^ p = 1 := by
    have : aeval M (X ^ p - 1 : F[X]) = M ^ p - 1 := by
      simp [map_sub, map_pow]
    rw [this, sub_eq_zero] at hp1
    exact hp1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact congr_fun (congr_fun hMp i) j

theorem exists_quadratic_cyclotomic_factor [Finite F] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : (p : F) ≠ 0) (hpq : p ∣ Nat.card F + 1) :
    ∃ t : F, Irreducible (X ^ 2 + C t * X + 1 : F[X]) ∧
      (X ^ 2 + C t * X + 1 : F[X]) ∣ cyclotomic p F := by
  have hcyclo_notunit : ¬ IsUnit (cyclotomic p F) := by
    refine Polynomial.not_isUnit_of_natDegree_pos _ ?_
    rw [Polynomial.natDegree_cyclotomic p F, Nat.totient_prime hp]
    exact Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨g, hgmonic, hgirr, hgdvd⟩ :=
    Polynomial.exists_monic_irreducible_factor (cyclotomic p F) hcyclo_notunit
  haveI : Fact (Irreducible g) := ⟨hgirr⟩
  have hdeg : g.natDegree = 2 := SpNS.natDegree_eq_two hp hp2 hpF hgdvd hpq
  have hnorm : Algebra.norm F (AdjoinRoot.root g) = 1 :=
    SpNS.norm_root_eq_one hp hp2 hpF hgdvd hpq
  have hnorm_eq : Algebra.norm F (AdjoinRoot.root g) = g.coeff 0 := by
    have h1 := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (CoordSL.rootPB g)
    rw [show (CoordSL.rootPB g).gen = AdjoinRoot.root g by simp [CoordSL.rootPB],
      SpNS.rootPB_dim_eq_two hp hp2 hpF hgdvd hpq,
      show minpoly F (AdjoinRoot.root g) = g by
        rw [AdjoinRoot.minpoly_root hgmonic.ne_zero, hgmonic.leadingCoeff, inv_one,
          C.map_one, mul_one]] at h1
    simpa using h1
  have hcoeff0 : g.coeff 0 = 1 := by rw [← hnorm_eq, hnorm]
  have hg_eq : g = X ^ 2 + C (g.coeff 1) * X + 1 := by
    have h2 : g.coeff 2 = 1 := by rw [← hdeg]; exact hgmonic.coeff_natDegree
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' (p := g) (n := 3) (by rw [hdeg]; norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hcoeff0, h2]
    simp only [map_one, one_mul, mul_one, pow_one, pow_zero]
    ring
  exact ⟨g.coeff 1, by rwa [← hg_eq], by rwa [← hg_eq]⟩

theorem spPlaneConj_companion [Finite F] (h2 : (2 : F) = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {t : F} (hirr : Irreducible (X ^ 2 + C t * X + 1 : F[X]))
    (hgd : (X ^ 2 + C t * X + 1 : F[X]) ∣ cyclotomic p F) (ht : spCompanion t ^ p = 1) :
    SpPlaneConj F p (spPlaneZetaCompanion t ht) := by
  intro n E hE hcard
  obtain ⟨u, hind, hform, hact⟩ :=
    exists_plane_frame h2 hp hp2 hpq hirr hgd E hE hcard
  obtain ⟨c, hc⟩ := exists_conj_range_planeTorus_of_frame t ht E u hind hform hact
  refine ⟨c, ?_⟩
  let R := (spPlaneTorus n (spPlaneZetaCompanion t ht)).range
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hR_le : Nat.card R ≤ p ^ n := by
    let D := Fin n → Multiplicative (ZMod p)
    have hcardD : Nat.card D = p ^ n := by
      dsimp [D]
      rw [Nat.card_fun, Nat.card_fin, Nat.card_congr (Multiplicative.toAdd (α := ZMod p)),
        Nat.card_zmod]
    calc Nat.card R ≤ Nat.card D :=
          Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
      _ = p ^ n := hcardD
  have hmap : Nat.card (E.map (MulAut.conj c).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  refine Subgroup.eq_of_le_of_card_ge hc ?_
  rw [hmap]
  exact le_trans hR_le hcard

end CFSG.StandardType.SpJoin
