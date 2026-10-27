module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofField
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuter
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofE9

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item8KFactsProof

theorem mem_normalizer_residual_of_commute {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {a b : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) (hba : b * a = a * b) :
    a ∈ Subgroup.normalizer
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) : Set G) := by
  have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hba.symm)
  have haLb : a ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp ha y),
      (Subgroup.mem_normalizer_iff.mp haC y)]
  exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
    _ haLb


theorem isoGTwoEven_of_isoGTwo {X : Type} [Group X] {q : TauCeti.PrimePower} {f : ℕ}
    (hq2 : q.p = 2) (hqe : q.exponent = f) (h : Sec4.IsoGTwo X q) : IsoGTwoEven X f := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : f ≠ 0 := by
    have := q.exponent_pos
    omega
  have hK2 : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hK : Nat.card (GaloisField 2 f) = q.card := by
    rw [hK2, TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq2 (GaloisField 2 f) hK
  have hZ : Subgroup.center (adjointGroup .G2 (GaloisField 2 f)) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨GaloisField 2 f, inferInstance, inferInstance, hK2,
    ⟨e.trans (e₂.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot))⟩⟩

theorem odd_of_sec8Pair
    (h82 : Item86ResProof.Item82TwoList) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) :
    Odd n := by
  obtain ⟨m, hm, hT⟩ := h82 G A c L a h.toHyp81 h.card_eq
  have hT' : Item86ResProof.IsGammaType (L ⧸ aschbacherSolvableCore 3 L) m := by
    rcases hT with hD | hG | hR | hSp | hU | ⟨K, _, _, ⟨-, h1, -⟩ | ⟨hK, -, hS⟩⟩
    · exact Or.inr (Or.inl hD)
    · exact Or.inr (Or.inr (Or.inl hG))
    · exact Or.inl hR
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSp))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hU)))
    · have := two_pow_mod_three_of_odd (Odd.mul (by decide : Odd 3) hm)
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨K, inferInstance, inferInstance, hK, hS⟩))))
  have hmn := Item86ResProof.eq_of_isGammaType hm.pos
    (Item86ResProof.one_le_of_isGammaIndex h.isGammaIndex) hT'
    (Item86ResProof.isGammaType_of_isGammaIndex h.isGammaIndex)
  exact hmn ▸ hm

end Item8KFactsProof

open Item8KFactsProof


theorem kF84Outer_of (h82 : Item86ResProof.Item82TwoList) (h47 : Sec4.Inputs47ClassesD4)
    (hR : KF84FieldRee) : KF84Outer := by
  intro G _ _ A c L a b X n h
  obtain ⟨hbA, -, hn1, hcases⟩ := h.isGammaIndex
  rcases hcases with ⟨k, hk, hkn, he, -⟩ | ⟨hL, ⟨eK⟩⟩
  · exact KFacts.InducesStdKind.inducesOuterTheta _ (hR G A c L a b X n h ⟨k, hk, hkn, he⟩)
      (by decide)
  · have hn := odd_of_sec8Pair h82 h
    have hAe := h.mem_partTwoF.1
    have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
    have hba : b * a = a * b :=
      congrArg Subtype.val (hAe.1.is_comm.comm ⟨b, hbA⟩ ⟨a, h.a_mem⟩)
    have haN := h.toHyp81.a_mem_normalizer
    by_contra hnot
    obtain ⟨k', hk'L, hk'a, hk'3, hle⟩ :=
      Item86ResProof.Item8KFactsOuter.exists_twist_of_not_outer hn1 haN
        (mem_normalizer_residual_of_commute haN hba) ha3 eK hnot
    refine Item86ResProof.Item8KFactsOuter.false_of_twist h47 hn h.inducesStdKind ha3 hk'L hk'a
      hk'3 eK hle ?_
    rcases hL with hD | ⟨q, hq2, hqe, hG⟩ | hU | hS | hSp
    · exact Or.inl (Or.inl hD)
    · exact Or.inl (Or.inr (isoGTwoEven_of_isoGTwo hq2 hqe hG))
    · exact Or.inr (Or.inr (Or.inl hU))
    · exact Or.inr (Or.inl hS)
    · exact Or.inr (Or.inr (Or.inr hSp))

theorem kF84Field_of_inputs (h82 : Item86ResProof.Item82TwoList) (h47 : Sec4.Inputs47ClassesD4)
    (hR : KF84FieldRee) : KF84Field :=
  kF84Field_of (kF84Outer_of h82 h47 hR) hR

end CFSG.RankThree.PartTwo.Sec8
