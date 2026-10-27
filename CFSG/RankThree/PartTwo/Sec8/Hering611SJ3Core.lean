module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3StepA
public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Bridge
public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3CovK
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.RankThree.PartTwo.Sec15.Item1510StepsProof

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.AGLEmbedding.KFactProofs.J3Sylow CFSG.AGLEmbedding

theorem exists_noncentral_lift
    {X : Type} [Group X] [Finite X] (hX : Group.IsPerfect X)
    {Z : Subgroup X} [Z.Normal] (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    (hJ : Nonempty ((X ⧸ Z) ≃* Blueprint.NativeSporadic.J3))
    {Ab Eb : Subgroup (X ⧸ Z)} (hA : CFSG.Assembly.IsElemAbelian 3 Ab) (hA27 : Nat.card Ab = 27)
    (hEA : Eb ≤ Ab) (hE9 : Nat.card Eb = 9) :
    ∃ e ∈ Eb, e ≠ 1 ∧ ∀ x : X, QuotientGroup.mk' Z x = e →
      ∃ t : X, QuotientGroup.mk' Z t * e = e * QuotientGroup.mk' Z t ∧ x * t ≠ t * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eJ⟩ := hJ
  obtain ⟨Tb, hAT⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA).exists_le_sylow
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  obtain ⟨sb, hF⟩ := kFactJ3Cover (X ⧸ Z) ⟨eJ.trans b⟩ Tb
  have hidx : ¬ 3 ∣ (Tb : Subgroup (X ⧸ Z)).index := Sylow.not_dvd_index Tb
  set T : Subgroup (X ⧸ Z) := (Tb : Subgroup (X ⧸ Z))
  set Rb : Subgroup (X ⧸ Z) := CFSG.Quasithin.centerOf T
  have hR9 : Nat.card Rb = 9 := hF.R_card
  have hRel : CFSG.Open.IsElemAbelian 3 Rb := hF.R_elem
  have hcomm : ∀ a ∈ Ab, ∀ c ∈ Rb, a * c = c * a := fun a ha c hc =>
    ((hF.mem_R c).1 hc).2 a (hAT ha)
  have hjoin : CFSG.Assembly.IsElemAbelian 3 (Ab ⊔ Rb) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hA hRel hcomm
  have hle27 : Nat.card ↥(Ab ⊔ Rb) ≤ 27 := card_le_27_of_isElemAbelian eJ (Ab ⊔ Rb) hjoin
  have hAeq : Ab = Ab ⊔ Rb :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hA27]; exact hle27)
  have hRA : Rb ≤ Ab := le_sup_right.trans_eq hAeq.symm
  obtain ⟨e, heE, heR, he1⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Proof1510Steps.exists_mem_inf_ne_one hA.1 hA27 hEA hE9 hRA hR9
  refine ⟨e, heE, he1, fun x hx => ?_⟩
  obtain ⟨t, htT, hxt⟩ := exists_noncentral_of_facts hX hZc hZ3 hF hidx heR he1 hx
  exact ⟨t, ((hF.mem_R e).1 heR).2 _ htT, hxt⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
