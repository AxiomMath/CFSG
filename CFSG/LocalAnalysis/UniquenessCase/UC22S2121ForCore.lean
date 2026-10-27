module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121For
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xd
import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem bot_mem_calB1 {T M L A : Subgroup G} (hA : A ∈ calB1 T M L) :
    (⊥ : Subgroup G) ∈ calB1 T M L := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨t, htL, htM, ht2, -⟩, -⟩ := hA
  have hinv : InvertedOutside M L ⊥ := ⟨t, htL, htM, ht2, fun x hx => by
    rw [Subgroup.mem_bot.mp hx]
    simp⟩
  have hperm : Permutes ⊥ T := by
    simp only [Permutes, Subgroup.coe_bot, Set.singleton_one, one_mul, mul_one]
  have hcomm : IsMulCommutative (⊥ : Subgroup G) :=
    IsMulCommutative.of_comm fun _ _ => Subsingleton.elim _ _
  have hnone : ∀ p : ℕ, p.Prime → ¬ p ∣ Nat.card (⊥ : Subgroup G) := fun p hp hdvd => by
    rw [Subgroup.card_bot] at hdvd
    exact hp.not_dvd_one hdvd
  have hodd : Odd (Nat.card (⊥ : Subgroup G)) := by
    rw [Subgroup.card_bot]
    exact odd_one
  refine ⟨bot_le, hcomm, ⊥, ⊥, ⟨bot_le, inferInstance, ?_, hodd, hperm, hinv⟩, hcomm, hodd,
    fun p hp hdvd => (hnone p hp hdvd).elim, (sup_bot_eq ⊥).symm, hperm, hinv,
    fun p hp hdvd => (hnone p hp hdvd).elim⟩
  rw [Subgroup.card_bot]
  exact squarefree_one

@[expose] def Ctx21.withBot {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) : Ctx21 D Ch :=
  { c with B := ⊥, hB := bot_mem_calB1 c.hB, hle := bot_le }

theorem pRank_centE_le_one_of_hyp2120For {D : Data G} (h61 : UC6.R6_1 D) {L X : Subgroup G}
    (hX : X ∈ calB1 D.T D.M L) (hH : Hyp2120For D X) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p (barPreimage D.M (centE D.M)) ≤ 1 := by
  obtain ⟨-, -, h3, h4⟩ := hH
  obtain ⟨hpP, -⟩ := D.sig_prime p hp
  by_contra hlt
  obtain ⟨P, hPsyl, hPX⟩ := h3 p hp
  have hPM : P ≤ D.M := hPsyl.le.trans (Subgroup.map_subtype_le _)
  have hnc : ¬ IsCyclic P := fun hc => by
    have h1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hpP hc
    rw [PrimeRankSylowTransport.pRank_sylow hpP hPsyl] at h1
    exact hlt h1
  have hPU := uc22p2121_mem_uniqueSet_of_noncyclic h61 hp hPM hPsyl.isPGroup hnc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨t, -, -, -, ht⟩, -⟩ := hX
  exact h4 p hp (not_le.1 hlt) (uc22p21b_core (UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal) hpP
    hPsyl.isPGroup hPX ⟨hPU.1, fun g hg => hPU.2 g⁻¹ hg⟩ ht)

theorem hyp2120_withBot {D : Data G} {Ch : Choice2011 G} (h61 : UC6.R6_1 D) (c : Ctx21 D Ch)
    {L X : Subgroup G} (hX : X ∈ calB1 D.T D.M L) (hH : Hyp2120For D X) :
    Hyp2120 D c.withBot := by
  refine ⟨hH.1, hH.2.1, fun p hp => ?_, fun p hp hlt =>
    absurd (pRank_centE_le_one_of_hyp2120For h61 hX hH hp) (not_le.2 hlt)⟩
  obtain ⟨P, hP, -⟩ := hH.2.2.1 p hp
  exact ⟨P, hP, le_top.trans_eq (Subgroup.normalizer_eq_top (⊥ : Subgroup G)).symm⟩

theorem case136b_of_hyp2120For (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hSig : UC6S846.SigmaStd D)
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    (hN : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) (hsig : D.sig = D.sig1) {L X : Subgroup G}
    (hX : X ∈ calB1 D.T D.M L) (hXM : X ≤ D.M) (hXne : X ≠ ⊥) (hH : Hyp2120For D X) {p : ℕ}
    (hp : p ∈ D.sig) : F13.Case136b D p X := by
  have hodd : Odd (Nat.card X) := by
    by_contra h
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 h
    have h1 := uc22p21d_odd_orderOf_of_mem_calB1 hX x.2
    rw [Subgroup.orderOf_coe, hx] at h1
    exact (by decide : ¬ Odd 2) h1
  obtain ⟨-, -, -, -, -, -, -, -, -, hperm, ⟨t, -, htM, -, ht⟩, -⟩ := hX
  have hp' := D.sig_prime p hp
  have : Fact p.Prime := ⟨hp'.1⟩
  obtain ⟨P, hPsyl, hPX⟩ := hH.2.2.1 p hp
  refine ⟨hXne, hXM, hodd, hperm, fun hle => htM (hle (mem_normalizer_of_inverts le_rfl ht)), P,
    hPsyl.of_le ?_ (uc22s13xd_Sp_le_centE hThin hCyc hSig hTU hN hsig hp), hPX⟩
  intro x hxP
  obtain ⟨k, hk⟩ := hPsyl.isPGroup ⟨x, hxP⟩
  have hk' : x ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp'.1).1 (orderOf_dvd_of_pow_eq_one hk')
  show x ∈ Subgroup.closure
    {x : G | x ∈ F13.cMStar D.M (F13.Lp D.M p) ∧ ∃ k : ℕ, orderOf x = p ^ k}
  exact Subgroup.subset_closure ⟨uc22s13xd_centE_le_cMStar D.M p (hPsyl.le hxP), m, hm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
