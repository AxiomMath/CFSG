module

public import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofGen
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofRead
import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS1518Norm : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (r : ℕ) [Fact r.Prime], r ≠ 2 →
    Sec4.IsoLThreePi X r 2 →
    ∀ M : Subgroup X, IsLThreeEpsAt ↥M r 1 →
      ∀ U : Subgroup X, IsPGroup 2 ↥U → U ≤ Subgroup.normalizer (M : Set X) → U ≤ M

theorem step1518R_of_norm (h1516 : Step1516R) (h1517 : Step1517R) (hTL : Step1518TL)
    (hN : KS1518Norm) : Step1518R := by
  intro G _ _ A c L h Y hctx p e _ he hiso
  by_contra hp2
  obtain ⟨hno, hs, -⟩ := h1517 G A c L h Y hctx
  obtain ⟨he2, hLY⟩ := step1518Read G A c L h Y hctx hno hs p e he hiso hp2
  subst he2
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2)))
    (Proof1514.bot_mem_scriptQPi_two A (lB A) _)
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hS.prop.1.2
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hT := h1516 G A c L h Y hctx S hS
  have hTY := hTL G A c L h Y hctx hno hs p 2 he hiso hp2 _ hT
  apply hTY
  have hθ := Proof1520.theta_eq_bot_of_isSimpleGroup h.mem_thetaComponentsAt hs
  have hisoL : Sec4.IsoLThreePi ↥L p 2 := Proof1520.isoLThreePi_of_theta_eq_bot hθ hiso
  have hM : IsLThreeEpsAt ↥((L ⊓ Y).subgroupOf L) p 1 :=
    IsLThreeEpsAt.of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm hLY
  have hT2 : IsPGroup 2 ↥(S ⊓ H) := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hT.prop.2
  have hU2 : IsPGroup 2 ↥((S ⊓ H ⊓ L).subgroupOf L) :=
    (hT2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hUN : (S ⊓ H ⊓ L).subgroupOf L ≤
      Subgroup.normalizer (((L ⊓ Y).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxY : (x : G) ∈ Subgroup.normalizer (Y : Set G) := hSY hx.1.1
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨-, hyY⟩
      exact ⟨(x * y * x⁻¹).2, (Subgroup.mem_normalizer_iff.mp hxY y).mp hyY⟩
    · rintro ⟨-, hyY⟩
      exact ⟨y.2, (Subgroup.mem_normalizer_iff.mp hxY y).mpr hyY⟩
  have hle := hN ↥L p hp2 hisoL ((L ⊓ Y).subgroupOf L) hM ((S ⊓ H ⊓ L).subgroupOf L) hU2 hUN
  intro z hz
  have hzL : z ∈ L := hz.2
  have hz' : (⟨z, hzL⟩ : ↥L) ∈ (S ⊓ H ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hz
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hle hz'))).2

end CFSG.RankThree.PartTwo.Sec15
