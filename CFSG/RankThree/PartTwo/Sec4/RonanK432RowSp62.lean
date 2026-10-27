module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Wreath
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofSp62
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 card_H6)
open CFSG.Assembly.RankThreeEven (projSp)
open scoped Matrix

local instance decEqH6 : DecidableEq H6 := inferInstance

@[expose] def flipM : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem flipM_check : Res417Four.sm6 flipM * Res417Four.sm6 flipM = 1 ∧
    Res417Four.sm6 flipM * Res417Four.sm6 flipM = 1 ∧
    (Res417Four.sm6 flipM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * Res417Four.sm6 flipM =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def flip6 : H6 := Res417Four.mk6 flipM flipM flipM_check

theorem flip6_conj : flip6 * Res417Four.z6 0 * flip6⁻¹ = (Res417Four.z6 0)⁻¹ ∧
    flip6 * Res417Four.z6 1 * flip6⁻¹ = Res417Four.z6 1 ∧
    flip6 * Res417Four.z6 2 * flip6⁻¹ = Res417Four.z6 2 := by
  decide +kernel

theorem conj_vecElt_const {H : Type} [Group H] {z : Fin 3 → H} {t m : H} (hf : WreathFacts z t)
    (h0 : m * z 0 * m⁻¹ = (z 0)⁻¹) (h1 : m * z 1 * m⁻¹ = z 1) (h2 : m * z 2 * m⁻¹ = z 2) :
    m * vecElt z ![1, 1, 1] * m⁻¹ = vecElt z ![2, 1, 1] := by
  have hz2 : z 0 ^ 2 = (z 0)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hf.pow_z 0)
  have e1 : vecElt z ![1, 1, 1] = z 0 * z 1 * z 2 := by
    have hs : (![1, 1, 1] : Fin 3 → ZMod 3) = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 := by
      decide
    rw [hs, vecElt_add hf, vecElt_add hf, vecElt_single_one, vecElt_single_one,
      vecElt_single_one]
  have e2 : vecElt z ![2, 1, 1] = (z 0)⁻¹ * z 1 * z 2 := by
    have hs : (![2, 1, 1] : Fin 3 → ZMod 3) = Pi.single 0 2 + Pi.single 1 1 + Pi.single 2 1 := by
      decide
    have hv2 : (2 : ZMod 3).val = 2 := rfl
    rw [hs, vecElt_add hf, vecElt_add hf, vecElt_single, hv2, vecElt_single_one,
      vecElt_single_one, hz2]
  rw [e1, e2,
    show m * (z 0 * z 1 * z 2) * m⁻¹ = (m * z 0 * m⁻¹) * (m * z 1 * m⁻¹) * (m * z 2 * m⁻¹) by
      group,
    h0, h1, h2]

theorem flip_facts {H : Type} [Group H] {z : Fin 3 → H} {t m : H} (hf : WreathFacts z t)
    (h0 : m * z 0 * m⁻¹ = (z 0)⁻¹) (h1 : m * z 1 * m⁻¹ = z 1) (h2 : m * z 2 * m⁻¹ = z 2) :
    m * vecElt z ![1, 1, 1] * m⁻¹ ∈ baseA z ∧
      m * vecElt z ![1, 1, 1] * m⁻¹ ∉ Subgroup.zpowers (vecElt z ![1, 1, 1]) := by
  rw [conj_vecElt_const hf h0 h1 h2]
  have hc3 : vecElt z ![1, 1, 1] ^ 3 = 1 :=
    (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)
  refine ⟨vecElt_mem_baseA hf _, fun hmem => ?_⟩
  rcases mem_zpowers_cases_of_pow_three hc3 hmem with h | h | h
  · exact absurd (congrFun (hf.inj _ h) 1) (by decide)
  · exact absurd (congrFun (vecElt_injective hf h) 0) (by decide)
  · have hsum : vecElt z (![2, 1, 1] + ![1, 1, 1]) = 1 := by
      rw [vecElt_add hf, h, inv_mul_cancel]
    exact absurd (congrFun (hf.inj _ hsum) 1) (by decide)

theorem listRow_H6 : ListRow H6 :=
  listRow_of_wreath3 Res417Four.wreathFacts_sp6 Res417Four.card_W6 (by rw [card_H6]; norm_num)
    ⟨flip6, flip_facts Res417Four.wreathFacts_sp6 flip6_conj.1 flip6_conj.2.1 flip6_conj.2.2⟩

theorem outerRow_H6 : OuterRow H6 :=
  outerRow_of_forall_pow_three_inner fun σ _ => Item434SmallTwoIII.mem_range_conj_H6 σ

theorem listRow_sp62 : ListRow (projSp 3 (GaloisField 2 1)) := by
  haveI : Finite (projSp 3 (GaloisField 2 1)) :=
    Finite.of_equiv _ Item434SmallTwoIII.sp62Equiv.symm.toEquiv
  exact ListRow.of_mulEquiv Item434SmallTwoIII.sp62Equiv.symm listRow_H6

theorem outerRow_sp62 : OuterRow (projSp 3 (GaloisField 2 1)) := by
  haveI : Finite (projSp 3 (GaloisField 2 1)) :=
    Finite.of_equiv _ Item434SmallTwoIII.sp62Equiv.symm.toEquiv
  exact OuterRow.of_mulEquiv Item434SmallTwoIII.sp62Equiv.symm outerRow_H6

theorem row_sp62 : RowOf (projSp 3 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSp 3 (GaloisField 2 1)) := Finite.of_equiv _ e.toEquiv
  exact GoodRow.of_mulEquiv (S := projSp 3 (GaloisField 2 1)) e.symm
    ⟨listRow_sp62, outerRow_sp62⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
