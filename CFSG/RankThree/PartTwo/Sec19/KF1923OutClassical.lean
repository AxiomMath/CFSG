module

public import CFSG.RankThree.PartTwo.Sec19.KF1923OutGeneric
import CFSG.Quasithin.H13.NQCatLieThompsonSp4
import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFA9
import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIOut

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.Assembly.RankThreeEven (projSp projSU projOmegaMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Open

theorem isCyclic_outer_projSp_two (F : Type) [Field F] [Finite F] [CharP F 2] :
    IsCyclic (Outer (projSp 2 F)) :=
  isCyclic_outer_of_mulEquiv (CFSG.PGLModel.projSpEquivStatedProj 2 F)
    (CFSG.Quasithin.H13.NQCat.LieThompson.Sp4.isCyclic_outer_projSp (F := F))

theorem outTwoCyclic_projSp_two (F : Type) [Field F] [Finite F] [CharP F 2] :
    CFSG.ClassicalInvolution.Nobq.OutTwoCyclic (projSp 2 F) :=
  outTwoCyclic_of_isCyclic_outer (isCyclic_outer_projSp_two F)

theorem card_outer_projSp_three_one (S : Type) [Group S]
    (e : S ≃* projSp 3 (GaloisField 2 1)) : Nat.card (Outer S) ∣ 2 := by
  have hsub : ∀ x : Outer S, x = 1 := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨s, hs⟩ := CFSG.RankThree.PartTwo.Sec14.Ronan1422S.sp62_aut_inner_of_iso e α
    exact MonoidHom.mem_range.mpr ⟨s, hs.symm⟩
  haveI : Subsingleton (Outer S) := ⟨fun x y => by rw [hsub x, hsub y]⟩
  rw [Nat.card_of_subsingleton (1 : Outer S)]
  exact one_dvd 2

theorem outTwoCyclic_projSU (n p f : ℕ) [Fact p.Prime] (hn : 3 ≤ n) (hne : (n, p ^ f) ≠ (3, 2))
    (hf : 1 ≤ f) (hodd : Odd (Nat.gcd n (p ^ f + 1))) :
    CFSG.ClassicalInvolution.Nobq.OutTwoCyclic (projSU n p f) := by
  have hcard : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  exact CFSG.ClassicalInvolution.Q3.TA3.outTwoCyclic_PSU
    ⟨⟨Fact.out, hf, hn, hne⟩, GaloisField p (2 * f), inferInstance, inferInstance, hcard,
      ⟨CFSG.PGLModel.projSUEquivStatedProj n p f⟩⟩ hodd

noncomputable def projOmegaMinusEquivStatedProj (K : Type) [Field K] (b c : K) :
    projOmegaMinus 3 K b c ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) :=
  (MulEquiv.subgroupCongr (CFSG.PGLModel.projImage_statedOmegaMinus 4 K b c).symm).trans
    (CFSG.Open.StatedAPI.mapMkEquivStatedProj _)

theorem outTwoCyclic_projOmegaMinus_three (b c : GaloisField 2 1)
    (hirr : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    CFSG.ClassicalInvolution.Nobq.OutTwoCyclic (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  have hmod : StatedClassicalModel (projOmegaMinus 3 (GaloisField 2 1) b c) .POmegaMinus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩, GaloisField 2 1, inferInstance, inferInstance, hK, b, c,
      hirr, ⟨projOmegaMinusEquivStatedProj _ b c⟩⟩
  have h := CFSG.AGLEmbedding.card_outer_le_two_of_omegaMinus_two hmod
  exact outTwoCyclic_of_card_le_two h.1 h.2

end CFSG.RankThree.PartTwo.Late
