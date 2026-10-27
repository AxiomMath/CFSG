module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFourTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanProductRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3Borel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s17_45_su3_false
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hU3 : IsU3 (BarInf L) n) (hN : uc22p20rNativeGriess)
    (h1 : R17_1At D V₀ V ctx.hyp125)
    (h33_2 : R17_33_2At D V₀ V) (h33_3 : R17_33_3At D V₀ V)
    (h846 : F08.R846 D)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34) : False := by
  classical
  have hL : L ∈ calC D.M := ctx.mem_calC
  obtain ⟨eBar⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hSU3 : IsSU3 (Bar2 L) n :=
    ⟨hL.2.2, CFSG.Blueprint.LieModel.of_mulEquiv eBar hU3⟩
  obtain ⟨hnEven, h3notdvd, s, hs, hs5, hsdvd⟩ :=
    s17_45_su3_arithmetic_of_ctx ctx h33_2 hSU3
  have hs2 : s ≠ 2 := by omega
  have hs3 : 3 < s := by omega
  have hoddZ : Odd (Nat.card (Subgroup.center (Bar2 L))) := uc22p20p_odd_center_bar2 ↥L
  have hZ3 : Nat.card (Subgroup.center (Bar2 L)) ∣ 3 :=
    uc22p20v_center_dvd_three_psu hN hSU3.1 hoddZ hSU3.2
  have hZbot : Subgroup.center (Bar2 L) = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hZ3 with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have h3dvd : 3 ∣ 2 ^ n + 1 := by
        have h := uc22p20v_card_center_dvd hN hSU3.1 hoddZ hSU3.2
        simp only [CFSG.Blueprint.Multiplier.genericOrders, Nat.mul_one] at h
        rw [h3] at h
        exact h.trans (Nat.gcd_dvd_right 3 (2 ^ n + 1))
      exact h3notdvd h3dvd
  have hU3bar2 : IsU3 (Bar2 L) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot) hSU3.2
  have hXL : X ≠ L := by
    intro hXL
    refine ctx.counter (Or.inl (Or.inr (Or.inl ⟨n, ?_⟩)))
    rw [hXL]
    exact hU3bar2
  have hΓeq : Gamma.ncard = (conjSetOf D.M L).ncard := ctx.ncard_Gamma_eq_card_conjSet
  have hpos : 0 < (conjSetOf D.M L).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨L, ⟨1, D.M.one_mem, by ext x; simp⟩⟩
  have hne1 : (conjSetOf D.M L).ncard ≠ 1 := by
    intro h1
    exact hXL (ctx.X_eq.trans (uc22s217_conjClosure_eq_of_ncard_eq_one h1))
  have hΓ2 : 2 ≤ Gamma.ncard := by
    rw [hΓeq]
    omega
  let S : Subgroup (Bar2 L) :=
    ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    simpa [S] using isSylowTwoOf_sylowBar2 hL
  have hidx : s ∣ (S.subgroupOf (Subgroup.normalizer (S : Set (Bar2 L)))).index :=
    Inputs1719.uc2_17_36b_dvd_index hSU3
      (CFSG.Quasithin.E1.isSylowIn_two_iff.mpr hS) hs hs3 hsdvd
  have hcard : Nat.card (TauCeti.Subgroup.normalizerQuotient S) =
      (S.subgroupOf (Subgroup.normalizer (S : Set (Bar2 L)))).index := by
    rw [TauCeti.Subgroup.normalizerQuotient, Subgroup.index_eq_card]
  have hdiv : s ∣ Nat.card (TauCeti.Subgroup.normalizerQuotient S) := by
    rwa [hcard]
  have hrank1 : 1 ≤ CFSG.Open.pRank s
      (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) :=
    CFSG.AGLEmbedding.KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd hs
      (by simpa using hdiv)
  have hC1 : 1 ≤ CFSG.Open.pRank s C := by
    refine hrank1.trans ?_
    have hb := pRank_normalizerQuotient_bar2_le_pRank_cartan hL ctx.cartan hs hs2
    simpa [S] using hb
  have hZ : ¬ s ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    rw [hZbot, Subgroup.card_bot]
    exact hs.not_dvd_one
  have hDc2 : 2 ≤ CFSG.Open.pRank s Dc :=
    hΓ2.trans (ctx.ncard_le_pRank_Dc hs hs2 hZ hC1)
  obtain ⟨E, hEM, hEel, hperm, hDcE⟩ :=
    exists_permuting_elemAbelian_of_ctx_of_borel ctx
      (Inputs1719.BorelChevOver.of_on hK3 hU3 ⟨by decide, by simp⟩) hs hs2
  have hE2 : 2 ≤ CFSG.Open.pRank s E := hDc2.trans hDcE
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have hle := CFSG.SectionRank.pRank_le_one_of_isCyclic hs (S := E) hcyc
    omega
  have hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded s D.M :=
    h846 L hL n hSU3 s hs hs3 hsdvd
  have hin : F11.InP11 D E :=
    inP11_of_strongly hs hs2 hstrong hEM
      (CFSG.Open.IsElemAbelian.isPGroup hEel) hEel.2 hEnc hperm
  have hV0 : V₀ = ⊥ := (h1.2 ⟨E, hin⟩).1
  have h33app : 1 < mSub V₀ := h33_3 L n hL hSU3
  rw [hV0] at h33app
  have hmSub0 : mSub (⊥ : Subgroup G) = 0 := CFSG.Quasithin.rk_bot
  rw [hmSub0] at h33app
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
