module

public import CFSG.LocalAnalysis.StandardType.L34SylowOvergroup
public import CFSG.LocalAnalysis.StandardType.PSL3FourThreeFixedPoints

public section

namespace CFSG.StandardType

open CFSG.ComponentClassification.PSL3Four CFSG.Blueprint CFSG.StandardType.L34Sylow
open CFSG.PSL3Four.Native (gensS)

namespace L34Overgroup

@[expose] def SolvableOrAltSix (A : Type) [Group A] : Prop :=
  Group.IsSolvable A ∨
    (IsSimpleGroup ↥(commutator A) ∧ Nonempty (↥(commutator A) ≃* alternatingGroup (Fin 6)))

theorem SolvableOrAltSix.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : SolvableOrAltSix A) : SolvableOrAltSix B := by
  rcases h with h | ⟨hs, ⟨c⟩⟩
  · exact Or.inl (SylowOvergroup.isSolvable_of_mulEquiv e.symm h)
  · haveI := hs
    let c' := SylowOvergroup.commutatorEquiv e
    exact Or.inr ⟨c'.symm.isSimpleGroup, ⟨c'.symm.trans c⟩⟩

theorem solvableOrAltSix_of_aSix {M : Type} [Group M] (hperf : commutator M = ⊤)
    (e : M ≃* alternatingGroup (Fin 6)) : SolvableOrAltSix M := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let c : ↥(commutator M) ≃* alternatingGroup (Fin 6) :=
    ((MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv).trans e
  exact Or.inr ⟨c.isSimpleGroup, ⟨c⟩⟩

theorem solvableOrAltSix_of_not_dvd_index
    {Y : Subgroup ↥S} (hY : Y ≠ ⊤) (h3 : ¬ 3 ∣ Y.index) :
    SolvableOrAltSix ↥Y := by
  classical
  have hF := overgroupFacts
  have hPS : closureTabs pGens ≤ S := closureTabs_gensS ▸ hF.P_le_S
  have hcardS : Nat.card ↥S = 20160 := by
    rw [← closureTabs_gensS]
    exact hF.card_S
  haveI : Finite ↥S := Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcard : Nat.card ↥((closureTabs pGens).subgroupOf S) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hF.card_P
  have hPgrp : IsPGroup 3 ↥((closureTabs pGens).subgroupOf S) :=
    IsPGroup.of_card (n := 2) (by rw [hPcard]; norm_num)
  have hPidx : ¬ 3 ∣ ((closureTabs pGens).subgroupOf S).index := by
    have h := Subgroup.card_mul_index ((closureTabs pGens).subgroupOf S)
    rw [hPcard, hcardS] at h
    have h2 : ((closureTabs pGens).subgroupOf S).index = 2240 := by omega
    rw [h2]
    norm_num
  let PS : Sylow 3 ↥S := hPgrp.toSylow hPidx
  have hPS' : (PS : Subgroup ↥S) = (closureTabs pGens).subgroupOf S := IsPGroup.toSylow_coe _ _
  refine SylowOvergroup.forall_of_sylow_le PS (fun Y => SolvableOrAltSix ↥Y) ?_ ?_ hY h3
  · intro g Y h
    exact SolvableOrAltSix.of_mulEquiv
      (Subgroup.equivMapOfInjective Y (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm h
  · intro Y hPY hYtop
    set Z : Subgroup (Equiv.Perm (Fin 42)) := Y.map S.subtype with hZ
    have hPZ : closureTabs pGens ≤ Z := by
      intro g hg
      have hgS : g ∈ S := hPS hg
      refine ⟨⟨g, hgS⟩, hPY ?_, rfl⟩
      rw [hPS', Subgroup.mem_subgroupOf]
      exact hg
    have hZS : Z ≤ closureTabs gensS := by
      rw [closureTabs_gensS]
      exact Subgroup.map_subtype_le Y
    have e : ↥Y ≃* ↥Z := Subgroup.equivMapOfInjective Y S.subtype S.subtype_injective
    refine SolvableOrAltSix.of_mulEquiv e.symm ?_
    rcases hF.trichotomy Z hPZ hZS with hZtop | ⟨j, hj, hZj⟩ | hsol
    · exfalso
      apply hYtop
      rw [Subgroup.eq_top_iff']
      intro y
      have hy : (y : Equiv.Perm (Fin 42)) ∈ Z := by
        rw [hZtop, closureTabs_gensS]
        exact y.2
      obtain ⟨y', hy', hyy'⟩ := hy
      have : y' = y := Subtype.ext hyy'
      rwa [this] at hy'
    · obtain ⟨hperf, ⟨a6⟩⟩ := hF.aSix j hj
      have e2 : ↥Z ≃* ↥(closureTabs (pGensWith mRs[j]!)) := MulEquiv.subgroupCongr hZj
      exact SolvableOrAltSix.of_mulEquiv e2.symm (solvableOrAltSix_of_aSix hperf a6)
    · exact Or.inl hsol

end L34Overgroup

theorem ggSeitzExcLThreeFourOvergroupInput_holds :
    GGSeitzExcLThreeFourOvergroupInput := by
  intro K _ _ d q hq2 hq3 hd he X hX1 h3
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel
    (ggLieModel_lThreeFour d q hq2 hq3 hd e)
  exact SylowOvergroup.forall_of_mulEquiv e' (fun A _ => L34Overgroup.SolvableOrAltSix A)
    (fun A B _ _ f h => L34Overgroup.SolvableOrAltSix.of_mulEquiv f h)
    (fun Y hY h3 => L34Overgroup.solvableOrAltSix_of_not_dvd_index hY h3) X hX1 h3

end CFSG.StandardType
