module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LUSa
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowGF2
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SNoCQ
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Assembly.RankThreeEven (projSL projSU)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

section Gen


theorem card_theta_ne_1080 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : ValidLieTypeIndex)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) {s : S} {K : Subgroup S}
    (hcc : CC425 s K) : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ≠ 1080 := by
  intro h1080
  have hs3 : s ^ 3 = 1 := by rw [← hcc.orderOf_eq]; exact pow_orderOf_eq_one s
  have hA6 := noA6At_of_lie hs hna idx he (MulAut.conj s) (by rw [← map_pow, hs3, map_one])
  have hfix : Sec4.autFix (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) :=
    RonanK429.RowV.autFix_conj_eq_centralizer s
  have hK : K ≤ Sec4.autFix (MulAut.conj s) := hfix ▸ hcc.le_centralizer
  have hsn : (K.subgroupOf (Sec4.autFix (MulAut.conj s))).IsSubnormal := by
    rw [hfix]
    exact hcc.isSubnormal
  have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rcases hcc.isType with hSL | hA6' | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩
  · exact Sec13.Item131bProof.card_ne_of_isSLThreePi hSL h1080
  · exact hA6 K hK hcc.isQuasisimple hsn
      ((isTripleCover_iff_isExtOf (isQuasisimple_theta_quot hcc.isQuasisimple)
        (center_alternatingGroup_eq_bot (by norm_num))).2 hA6')
  all_goals
    have hcard : Nat.card (K ⧸ aschbacherSolvableCore 3 K) =
        Nat.card N * Nat.card ((K ⧸ aschbacherSolvableCore 3 K) ⧸ N) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup N).trans (mul_comm _ _)
    rw [Nat.card_congr eN.toEquiv, Nat.card_congr eQ.toEquiv, hZ3, h1080] at hcard
  · rw [KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at hcard
    norm_num [Nat.factorial] at hcard
  · rw [KFacts.KS14.card_nativeM22] at hcard
    norm_num at hcard

theorem noCC425_of_lie_at {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : ValidLieTypeIndex)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (h : ∀ s : S, orderOf s = 3 →
      (∃ M B : ℕ, Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ M ∧ 0 < M ∧ M < B ^ 3 ∧
        ∀ t ∈ typeOrders425 M B, t = 1080) ∨
      s ∉ ⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆) :
    NoCC425 S := by
  intro s K hcc
  rcases h s hcc.orderOf_eq with ⟨M, B, hC, hM0, hB, hfree⟩ | hcomm
  · have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ M :=
      (card_theta_quot_dvd K).trans ((Subgroup.card_dvd_of_le hcc.le_centralizer).trans hC)
    exact card_theta_ne_1080 hs hna idx he hcc
      (hfree _ (card_mem_typeOrders425 (isQuasisimple_theta_quot hcc.isQuasisimple) hM0 hB
        hcc.isType hdvd))
  · exact noCQAt_of_not_mem_commutator hcomm K hcc.mem hcc.le_centralizer hcc.isQuasisimple
      hcc.isType

theorem rowOf425_of_lie_card {X : Type} [Group X] (idx : ValidLieTypeIndex)
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group)) {M B : ℕ}
    (hM : ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* X) → Nat.card S ∣ M) (hM0 : 0 < M)
    (hB : M < B ^ 3) (hfree : ∀ t ∈ typeOrders425 M B, t = 1080) : RowOf425 X := by
  obtain ⟨eX⟩ := hX
  refine rowOf425_of_noCC fun S _ _ hs hna ⟨e⟩ => ?_
  refine noCC425_of_lie_at hs hna idx ⟨e.trans eX⟩ fun s _ => Or.inl ⟨M, B, ?_, hM0, hB, hfree⟩
  exact (Subgroup.card_subgroup_dvd_card _).trans (hM S ⟨e⟩)

theorem kT2_eight_SU5 : RowOf425 (projSU 5 2 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : (LieTypeIndex.twistedA 4 ⟨2, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_twistedA (by norm_num) (by omega)
  refine rowOf425_of_lie_card ⟨_, hv⟩
    ⟨(Census.typeTwistedAGroupEquivProjSU 4 ⟨2, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩
    (M := 13685760) (B := 240) (fun S _ _ ⟨e⟩ => ?_) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [Nat.card_congr e.toEquiv, RonanEps.card_projSU_five_two_gf2]

theorem kT2_seven_Tits : ∀ ht : LieTypeIndex.tits.Valid,
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := by
  intro ht
  refine rowOf425_of_lie_card ⟨_, ht⟩ ⟨MulEquiv.refl _⟩ (M := 17971200) (B := 262)
    (fun S _ _ ⟨e⟩ => ?_) (by norm_num) (by norm_num) (by decide +kernel)
  rw [lieOrderBridge_holds ⟨_, ht⟩ S ⟨e⟩]
  rfl

end Gen

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
