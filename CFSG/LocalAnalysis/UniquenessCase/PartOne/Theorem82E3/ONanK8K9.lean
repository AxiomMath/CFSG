module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.Quasithin.Background.SmithB45J2Cls
public import CFSG.Milestones.ASVolI.A3Spor.Out
public import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec4.Item426RestInner
public import CFSG.RankThree.PartTwo.Sec17.Item17Res15ProofAut
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.CGT.Timmesfeld75.NodeAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.Sporadic.Schreier
open CFSG.Quasithin.J2Cls

theorem K9J2Order_holds :
    K9J2Order := by
  intro y hy
  let g : j2P := j2PermEquiv y
  have hord : orderOf g = orderOf y := MulEquiv.orderOf_eq j2PermEquiv y
  rw [← hord] at hy
  have hg : IsPRegular 2 g := by
    rw [IsPRegular, hy]
    decide
  have hmem := orderOf_mem_of_isPRegular g hg
  rw [hy] at hmem
  exact absurd hmem (by decide)

theorem K9J2Out_holds :
    K9J2Out := by
  intro σ hσ
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.1
  have hodd : Odd (orderOf σ) := by
    have hdvd : orderOf σ ∣ 7 := orderOf_dvd_of_pow_eq_one hσ
    rcases Nat.dvd_prime Nat.prime_seven |>.1 hdvd with h | h <;> rw [h] <;> norm_num
  obtain ⟨l, hl⟩ := CFSG.ASVolI.burnsideA315s_oddInner_J2 (MulEquiv.refl _) σ hodd
  rw [hl]
  exact ⟨l, rfl⟩

theorem K9Five_holds :
    K9Five := by
  constructor
  · rw [CFSG.PGLModel.card_projSU_three_three]
    decide
  · intro X _ _ hX h
    have hdvd := CFSG.RankThree.PartTwo.Sec4.Item426Rest.card_dvd_of_G2_three hX
    have h5 : ¬ 5 ∣ 4245696 := by decide
    exact h5 (Nat.dvd_trans h hdvd)

@[expose] def K8Cat : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .ONan →
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ¬ 3 ∣ Nat.card S → CFSG.Assembly.InCatalog S →
        ∀ H : Subgroup (MulAut Y), ∀ f : ↥H →* S, ¬ Function.Surjective f

theorem K8Cat_holds :
    K8Cat := by
  intro Y _ _ hY S _ _ hsimple hnab h3 hcat H f hf
  obtain ⟨e⟩ := hY
  have hNoSz : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection (MulAut Y) :=
    CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_mulAut_of_mulEquiv e
      CFSG.RankThree.PartTwo.Sec17.Proof17Res15.noSzSection_mulAut_on
  obtain ⟨f', hSuz⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd S hnab hcat h3
  let N : Subgroup ↥H := f.ker
  have hN : N.Normal := inferInstance
  have eS : (↥H ⧸ N) ≃* S := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hSuzQuot : CFSG.Blueprint.SuzukiModel (↥H ⧸ N) 2 f' :=
    CFSG.CGT.Timmesfeld75.suzukiModel_of_mulEquiv eS.symm hSuz
  exact hNoSz H N 2 f' hSuzQuot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

end
