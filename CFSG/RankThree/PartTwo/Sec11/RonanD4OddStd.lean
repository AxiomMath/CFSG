module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofOuter
public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddG2
public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddPlus
public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddMinus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.RonanD4Cocycle

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

set_option linter.unusedSectionVars false

section Support


theorem ronanD4Odd_not_hasType424_fieldActor {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ¬ KS11Lie2Proof.HasType424
      ↥(Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨e⟩ := nonempty_fixSubgroup_fieldActor_equiv_G2 (ℓ := p) hp3 hf (Or.inr hp5) hK σ hσ
  have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hp hf hK σ hσ]
    exact le_trans (by norm_num) (hp5.trans (Nat.le_self_pow (by omega) p))
  intro hT
  exact RonanD4Odd.not_hasType424_g2 hk3
    (hT.of_mulEquiv ((MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans e))

end Support

theorem d4OuterStdNoType424_holds :
    D4OuterStdNoType424 := by
  intro p f hp hp2 hp3 hf K _ _ hK σ hσ s hsfix hs3
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  have hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) s 3 = 1 := by
    rw [normSeq_three, hsfix, hsfix, ← pow_three']
    exact hs3
  obtain ⟨y, s', hconj, -, -, hcls⟩ := d4_cocycle_toralClass hp hp2 hp3 hf hK σ hσ s hN
  have hkey : ¬ KS11Lie2Proof.HasType424
      ↥(Sec4.autFix (MulAut.conj s' * fieldActor (t := TwistTag.D4) σ σ)) := by
    rcases hcls with hs1 | ⟨hq, d, hd, hd3, hd1, hsd⟩ | ⟨hq, hs'⟩
    · rw [hs1, map_one, one_mul]
      exact ronanD4Odd_not_hasType424_fieldActor hp hp3 hf hp5 hK σ hσ
    · exact RonanD4Odd.not_hasType424_fixSub_a2Plus hp hp2 hf hq hK hσ hd hd3 hd1 hsd
    · exact RonanD4Odd.not_hasType424_fixSub_a2Minus hp hp2 hp3 hf hq hK σ hσ s' hs'
  intro h
  have h1 := RonanD4Odd.hasType424_autFix_conj (MulAut.conj y)
    (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) h
  rw [hconj] at h1
  exact hkey h1

end CFSG.RankThree.PartTwo.Sec11
