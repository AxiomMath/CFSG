module

public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofJTypeRee
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.Quasithin.H13.L32NSp4S6
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofTools
import CFSG.Quasithin.Background.FFC2G2

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88C

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp StatedSU)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open Item89Res2

theorem type419_of_projSp {C : Type} [Group C] {m : ℕ} (hm : 1 ≤ m)
    (e : C ≃* projSp 2 (GaloisField 2 m)) : Sec4.IsType419 (perfectResidual C) := by
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    have hF2 : Nat.card (GaloisField 2 1) = 2 := by rw [hF, pow_one]
    set ψ : C ≃* Equiv.Perm (Fin 6) :=
      ((e.trans (Sec4.projSpEquivStatedProj 2 _)).trans
        (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2)).trans
        CFSG.Quasithin.H13.Sp4Cert.sympFourEquiv with hψ
    set eR : perfectResidual C ≃* alternatingGroup (Fin 6) :=
      (perfectResidualEquiv ψ).trans (MulEquiv.subgroupCongr perfectResidual_perm_six) with heR
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨eR⟩))))
  · have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have h4' : ∃ s : Finset (GaloisField 2 m), s.card = 4 := by
      have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
        Finset (GaloisField 2 m))) (n := 4) (by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
          exact h4)
      exact ⟨s, hs⟩
    have hp := CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2
      (GaloisField 2 m) (Or.inl h4')
    set ψ := e.trans (Sec4.projSpEquivStatedProj 2 _) with hψ
    have hperfC : Group.IsPerfect C :=
      hp.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
    set eR : perfectResidual C ≃* projSp 2 (GaloisField 2 m) :=
      (perfectResidualEquivSelf hperfC).trans e with heR
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm2, ⟨eR⟩⟩))))

section Types


theorem type419_of_isoGTwoEven {C : Type} [Group C] {m : ℕ} (hm : 1 ≤ m) (h : IsoGTwoEven C m) :
    Sec4.IsType419 (perfectResidual C) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  set Q := CFSG.Blueprint.Chevalley.adjointGroup .G2 K
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    obtain ⟨eU⟩ := nonempty_commutator_g2_two_mulEquiv hK2
    have hUs : IsSimpleGroup (projSU 3 3 1) :=
      Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 3 1 le_rfl (by norm_num)
    have hcs : IsSimpleGroup (commutator Q) := eU.isSimpleGroup
    have hnc : ∃ x y : commutator Q, x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := (CFSG.Quasithin.FFC.commutator_data_g2 hK2
        (Subgroup.topEquiv.trans
          (Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK2).some)).2.1
      refine ⟨(MulEquiv.subgroupCongr (commutator_def Q)).symm x,
        (MulEquiv.subgroupCongr (commutator_def Q)).symm y, fun h' => hxy ?_⟩
      have := congrArg (MulEquiv.subgroupCongr (commutator_def Q)) h'
      simpa using this
    have hcp : Group.IsPerfect (commutator Q) :=
      Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
    have hres : perfectResidual Q = commutator Q := perfectResidual_eq_commutator hcp
    set eR : perfectResidual C ≃* projSU 3 3 1 :=
      ((perfectResidualEquiv e).trans (MulEquiv.subgroupCongr hres)).trans eU with heR
    exact Or.inr (Or.inl ⟨eR⟩)
  · have hq : 4 ≤ 2 ^ m := (Nat.pow_le_pow_right (by norm_num) hm2 : 2 ^ 2 ≤ 2 ^ m)
    have hK3 : 3 ≤ Nat.card K := by omega
    have hperf : Group.IsPerfect Q :=
      CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K hK3
    have hperfC : Group.IsPerfect C :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    set eR : perfectResidual C ≃* Q := (perfectResidualEquivSelf hperfC).trans e with heR
    have eA : Q ≃* AdjointQuotient .G2 K :=
      ((QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot).symm
    exact Or.inl ⟨m, ⟨Nat.prime_two, hm, rfl, by omega⟩, K, inferInstance, inferInstance, hK,
      ⟨eR.trans eA⟩⟩

end Types

section Ree


theorem type419_of_reeGamma {C : Type} [Group C] {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1))
    (φ : C ≃* ReeTag.F4.reeGamma k b) : Sec4.IsType419 (perfectResidual C) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
    exact Or.inr (Or.inr (Or.inr (Or.inl (reeTitsModel_perfectResidual_two hk2 φ))))
  · have hperf : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    have hperfC : Group.IsPerfect C :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    have hRC : ReeTitsModel (perfectResidual C) .twistedF4 2 (2 * b + 1) :=
      CFSG.SectionRank.reeTitsModel_of_mulEquiv ((perfectResidualEquivSelf hperfC).trans φ)
        (reeTitsModel_reeGamma hb hk)
    exact Or.inr (Or.inr (Or.inl ⟨2 * b + 1, hRC⟩))

end Ree

section Main


@[expose] def KF89JCentType419 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (a : G) (m : ℕ), 1 ≤ m →
    IsGammaType (X ⧸ aschbacherSolvableCore 3 X) m →
    (∀ k : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) k) → a ^ 3 = 1 →
    (KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField) →
    (∀ k : ℕ, Sec8PairGTwo X a k) →
      Sec4.IsType419 (perfectResidual (barCentralizer (Subgroup.zpowers a) X))

theorem kF89JCentType419_holds :
    KF89JCentType419 := by
  intro G _ _ X a m hm htype hU ha3 hk hg
  have hout : Sec4.InducesOuterTheta a X := by
    rcases hk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta X h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h (by decide)
  rcases htype with hRee | hD | ⟨q, hq2, hqe, hGq⟩ | hSU | hSU' | hSp
  · obtain ⟨k, hk', hkm, ⟨e₀⟩⟩ := hRee
    have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk'
    obtain ⟨-, k', hk'1, -, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
    obtain ⟨b, k₀, _, _, _, hk₀, ⟨φ⟩⟩ :=
      Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk'1 hK (e₀.trans e₁) ha3 hout
    exact type419_of_reeGamma hk₀ φ
  · exact type419_of_isoGTwoEven hm (hg m (Or.inl hD))
  · exact type419_of_isoGTwoEven hm
      (hg m (Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq)))
  · exact absurd (Or.inl hSU) (hU (3 * m))
  · exact absurd (Or.inr hSU') (hU (3 * m))
  · obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (by omega) ha3 hout hSp
    exact type419_of_projSp hm ι

end Main

end Hering88C

end CFSG.RankThree.PartTwo.Sec8
