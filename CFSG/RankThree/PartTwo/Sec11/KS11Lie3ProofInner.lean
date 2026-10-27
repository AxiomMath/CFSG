module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.Adapters.TauCetiExceptional.EvenAll

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

namespace KS11Lie3Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem not_hasType424_g2 {K : Type} [Field K] [Finite K] (hK : 3 ≤ Nat.card K) :
    ¬ KS11Lie2Proof.HasType424 (adjointGroup .G2 K) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have : IsSimpleGroup (adjointGroup .G2 K) := KS11Lie2Proof.isSimpleGroup_g2 hK
  have : IsSimpleGroup (⊤ : Subgroup (adjointGroup .G2 K)) :=
    MulEquiv.isSimpleGroup Subgroup.topEquiv
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := KS11Lie2Proof.g2_exists_e9 K
  have hc : ⁅u, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr huv
  exact KS11Lie2Proof.not_hasType424_of_simple ⊤ (fun _ _ => Subgroup.mem_top _)
    (Subgroup.mem_top u) (Subgroup.mem_top v) hu1 hu3 hv3 (by rw [hc]; exact Commute.one_left _)
    (by rw [hc]; exact Commute.one_left _) hvu

theorem exists_mulEquiv_adjointGroup_g2 {Z : Type} [Group Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), 3 ≤ Nat.card K ∧
      Nonempty (Z ≃* adjointGroup .G2 K) := by
  obtain ⟨X, _, ⟨q, hq, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  have hq3 : 3 ≤ q.card := by
    have h1 := ((TauCeti.LieTypeIndex.valid_iff _).mp hq).1
    rwa [TauCeti.LieTypeIndex.inStandardRange_iff] at h1
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hq K hK
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  exact ⟨K, inferInstance, inferInstance, hK ▸ hq3,
    ⟨((e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)).trans
      (f.trans b.symm)).trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)⟩⟩

theorem ne_one_of_isType424_g2 {Z : Type} [Group Z] [Finite Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X))
    {z : Z} {J : Subgroup Z} (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) : z ≠ 1 := by
  rintro rfl
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_adjointGroup_g2 hZ
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hT := KS11Lie2Proof.hasType424_of_mem hJ hJT
  rw [map_one, Item426.fixSub_one] at hT
  exact not_hasType424_g2 hK ((hT.of_mulEquiv Subgroup.topEquiv).of_mulEquiv E)

end KS11Lie3Proof

end CFSG.RankThree.PartTwo.Sec11
