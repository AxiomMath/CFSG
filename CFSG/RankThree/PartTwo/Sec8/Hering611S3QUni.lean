module

import CFSG.CharacterTheory.BrauerLinearThree.CentralizerStructureMatrix
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL2Tools
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.RankThree.PartTwo.KFacts

private theorem exists_sl_lift_cube {K : Type} [Field K] {u : PSL2 K} (hu3 : u ^ 3 = 1) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) K, CFSG.PSL2Table.mk B = u ∧ B ^ 3 = 1 := by
  obtain ⟨A, rfl⟩ := CFSG.PSL2Table.mk_surjective u
  have hA3 : CFSG.PSL2Table.mk (A ^ 3) = 1 := by rw [map_pow, hu3]
  rcases (CFSG.PSL2Table.mk_eq_one_iff (A ^ 3)).mp hA3 with h | h
  · exact ⟨A, rfl, h⟩
  · have hodd : Odd (3 : ℕ) := ⟨1, rfl⟩
    exact ⟨-A, CFSG.PSL2Table.mk_neg A, by rw [hodd.neg_pow, h, neg_neg]⟩

private theorem toPGL_mk_mem_map_conj_unipPGL {K : Type} [Field K] [CharP K 3]
    {B : Matrix.SpecialLinearGroup (Fin 2) K} (hB3 : B ^ 3 = 1) :
    ∃ H : PGL2 K, Matrix.ProjectiveSpecialLinearGroup.toPGL (CFSG.PSL2Table.mk B) ∈
      (CFSG.RankThree.PartTwo.Sec4.Item434CharThree.unipPGL K).map
        (MulAut.conj H).toMonoidHom := by
  have hA3 : (Matrix.SpecialLinearGroup.toGL B) ^ 3 = 1 := by
    rw [← map_pow, hB3, map_one]
  have hN := CFSG.BrauerLinearThree.sub_one_mul_self_eq_zero 3
    (Matrix.SpecialLinearGroup.toGL B) hA3
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    exact (one_ne_zero : (1 : K) ≠ 0) (by linear_combination h3 - h)
  obtain ⟨P, c, hP⟩ := CFSG.BrauerLinearThree.exists_conj_upperGL h2
    (Matrix.SpecialLinearGroup.toGL B) hN
  have hUp : Matrix.SpecialLinearGroup.toGL (CFSG.PSL2Table.unip c) =
      CFSG.DesarguesianPlanes.upperGL c :=
    Units.ext rfl
  have hB' : Matrix.SpecialLinearGroup.toGL B =
      P * Matrix.SpecialLinearGroup.toGL (CFSG.PSL2Table.unip c) * P⁻¹ := by
    rw [hUp, ← hP]
    group
  refine ⟨Matrix.ProjGenLinGroup.mk P,
    Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (CFSG.PSL2Table.unip c)),
    CFSG.RankThree.PartTwo.Sec4.Item434CharThree.mk_toGL_unip_mem c, ?_⟩
  show Matrix.ProjGenLinGroup.mk P *
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (CFSG.PSL2Table.unip c)) *
      (Matrix.ProjGenLinGroup.mk P)⁻¹ =
    Matrix.ProjectiveSpecialLinearGroup.toPGL (CFSG.PSL2Table.mk B)
  rw [show Matrix.ProjectiveSpecialLinearGroup.toPGL (CFSG.PSL2Table.mk B) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL B) from rfl, hB',
    ← map_inv, ← map_mul, ← map_mul]

theorem eq_one_of_commute_conj_order_three {K : Type} [Field K] [Finite K] (hK3 : ringChar K = 3)
    {u : PSL2 K} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) {q : MulAut (PSL2 K)}
    (hq : q ∈ (pglAction K).range) (hqu : q * MulAut.conj u = MulAut.conj u * q) {k : ℕ}
    (hk : q ^ (2 ^ k) = 1) : q = 1 := by
  have hchar : CharP K 3 := by
    rw [← hK3]
    infer_instance
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hq
  obtain ⟨B, rfl, hB3⟩ := exists_sl_lift_cube hu3
  have hcomm : h * Matrix.ProjectiveSpecialLinearGroup.toPGL (CFSG.PSL2Table.mk B) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (CFSG.PSL2Table.mk B) * h := by
    rw [← pglAction_toPGL K (CFSG.PSL2Table.mk B), ← map_mul, ← map_mul] at hqu
    exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K hqu
  have hne : Matrix.ProjectiveSpecialLinearGroup.toPGL (CFSG.PSL2Table.mk B) ≠ 1 := by
    intro h1
    exact hu1 (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (h1.trans (map_one Matrix.ProjectiveSpecialLinearGroup.toPGL).symm))
  obtain ⟨H, hH⟩ := toPGL_mk_mem_map_conj_unipPGL hB3
  have hh : h ∈ (CFSG.RankThree.PartTwo.Sec4.Item434CharThree.unipPGL K).map
      (MulAut.conj H).toMonoidHom :=
    CFSG.RankThree.PartTwo.Sec4.Item434CharThree.mem_map_conj_unipPGL_of_commute hH hne hcomm
  have h3 : h ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.Sec4.Item434CharThree.pow_three_eq_one_of_mem_map_conj hh
  have h2k : h ^ (2 ^ k) = 1 :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K
      (by rw [map_pow, hk, map_one])
  have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
  have hgcd : h ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h3, h2k⟩
  rw [hcop, pow_one] at hgcd
  rw [hgcd, map_one]

end CFSG.RankThree.PartTwo.Sec8.Hering611
