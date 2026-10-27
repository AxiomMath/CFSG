module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent361
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340M
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340Z
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340G
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private theorem res1340_pCore_quot_eq_bot {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hN : N = CFSG.pCore 2 H) : CFSG.pCore 2 (H ⧸ N) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hN
  exact Sec18.pCore_quotient_pCore_eq_bot 2

namespace Res1Tau

variable {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
  {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

theorem eq_of_competing_of_le
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z) (hbot : Item145BotS14)
    (h1444 : Item1444 A (lB A)) (h149 : Item149 A (lB A)) (hSz : KFacts.KPSz)
    (hQE9 : Res1QE9 Q) (hn : Claim153Normal A (lB A)) {M' : Subgroup G}
    (hC' : Ctx155 A X K Y M' T) (hstep3 : deltaZero A (lB A) M' ≤ L ⊔ pPrimeCoreOf 3 M') :
    M' = M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := τ.isPerfect_l
  set O' := pPrimeCoreOf 3 M' with hO'
  set P₀ := CFSG.Open.pCoreOf 2 O' with hP₀
  have hN : n155 A K ≤ Subgroup.normalizer (K : Set G) :=
    (normalizer_x_eq_of_normal τ.std h149 hn τ.ctx.mem_k).le
  have hXY : X ≤ Y := τ.ctx.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hAYM' : A ⊔ Y ≤ M' := SetLike.coe_subset_coe.mp hC'.mem_m.2
  have hM'O : M' ≤ Subgroup.normalizer (O' : Set G) := le_normalizer_pPrimeCoreOf 3 M'
  have hOP : O' ≤ Subgroup.normalizer (P₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 O'
  have hM'P : M' ≤ Subgroup.normalizer (P₀ : Set G) :=
    hM'O.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O')
  have hP₀O : P₀ ≤ O' := CFSG.LieType.BorelTits.pCoreOf_le 2 O'
  have hP₀2 : IsPGroup 2 P₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 O'
  have hLM' : L ≤ M' := τ.l_le.trans (hXY.trans (le_sup_right.trans hAYM'))
  have hP₀X : P₀ ≤ Subgroup.normalizer (X : Set G) :=
    τ.le_normalizer_of_competing hbot h1444 hN hC' hP₀2
      (hP₀O.trans (Sec14.pPrimeCoreOf_le 3 M')) (hAYM'.trans hM'P)
  haveI : (P₀.subgroupOf O').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP₀O).mpr hOP
  have hO3 : ¬ 3 ∣ Nat.card O' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M')
  have hS2 : CFSG.pCore 2 (↥O' ⧸ P₀.subgroupOf O') = ⊥ :=
    res1340_pCore_quot_eq_bot _
      (Subgroup.comap_map_eq_self_of_injective O'.subtype_injective (CFSG.pCore 2 ↥O'))
  have hSzQ : CFSG.RankThree.S4Free.SzSections (↥O' ⧸ P₀.subgroupOf O') :=
    (τ.std.toTheoremFourHyp.szSections hSz hO3).quotient _
  have hrank : ∀ p : ℕ, p.Prime → 5 ≤ p →
      CFSG.Open.pRank p (⊤ : Subgroup (↥O' ⧸ P₀.subgroupOf O')) ≤ 2 := by
    intro p hp hp5
    haveI : Fact p.Prime := ⟨hp⟩
    have hNp : ¬ p ∣ Nat.card (P₀.subgroupOf O') := by
      intro hdvd
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
        (hP₀2.comap_of_injective O'.subtype Subtype.val_injective)
      rw [Subgroup.subgroupOf, hn] at hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
      omega
    rw [CFSG.SectionRank.pRank_quotient_eq _ hNp,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    have h2 : CFSG.Open.pRank p O' ≤ CFSG.Open.pRank p M' :=
      CFSG.SectionRank.pRank_mono hp.one_lt (Sec14.pPrimeCoreOf_le 3 M')
    have h3 : CFSG.Open.pRank p M' ≤ CFSG.Assembly.RankThreeEven.localRank p G := by
      refine le_csSup ⟨Nat.card G, ?_⟩ ⟨M', ?_, rfl⟩
      · rintro _ ⟨Z, -, rfl⟩
        exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt Z
      · obtain ⟨R, hR1, hR2, hRe⟩ := hC'.mem_m.1.1
        exact ⟨R, hR1, hR2, hRe⟩
    have h4 := τ.std.toTheoremFourHyp.localRank_lt p hp (by omega)
    omega
  have hLO : ⁅L, O'⁆ ≤ P₀ :=
    res1340_commutator_le (hQE9 _ τ.q).1 (hQE9 _ τ.q).2 hP₀O (hLM'.trans hM'O)
      (hLM'.trans hM'P) hOP hO3 hS2 hSzQ hrank
  have hE'L := τ.oPrimeResidualOf_delta_le_sup_commutator_of_le h149 hC' hstep3
  have hcop : Nat.Coprime 3 (Nat.card P₀) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP₀2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hle : L ⊔ ⁅L, O'⁆ ≤ X ⊔ P₀ := sup_le_sup τ.l_le hLO
  have hE'X : oPrimeResidualOf 3 (delta A (lB A) M') ≤ X := by
    rw [Sec14.oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro y ⟨hy, k, hk⟩
    have hyE : y ∈ oPrimeResidualOf 3 (delta A (lB A) M') := by
      rw [Sec14.oPrimeResidualOf_eq_closure]
      exact Subgroup.subset_closure ⟨hy, k, hk⟩
    exact Sec14.mem_left_of_pow_prime_pow Nat.prime_three hP₀X hcop (hle (hE'L hyE)) hk
  have hE'eq : oPrimeResidualOf 3 (delta A (lB A) M') = X :=
    le_antisymm hE'X (τ.le_oPrimeResidualOf_delta_of_competing hC')
  have hM'M : M' ≤ M := by
    have h := (τ.oPrimeResidualOf_delta_le_of_competing h149 hC').2
    rw [hE'eq] at h
    exact h.trans τ.m_eq.ge
  rcases lt_or_eq_of_le hM'M with hlt | heq
  · exact (hC'.mem_m.1.2 M hlt τ.ctx.mem_m.1.1).elim
  · exact heq

end Res1Tau

theorem res1Thm340_of_le (hbot : Item145BotS14)
    (h1444 : Item1444S14) (h149 : Sec16.Item149S14) (hSz : KFacts.KPSz)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop} (hQE9 : Res1QE9 Q)
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau Q P A c L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (hstep3 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
      (L X K Y M T P' : Subgroup G) (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau Q P A c L X K Y M T P' Yc z → ∀ M' : Subgroup G, Ctx155 A X K Y M' T →
        deltaZero A (lB A) M' ≤ L ⊔ pPrimeCoreOf 3 M') :
    Res1Thm340 Q P := by
  intro G _ _ A c L X K Y M T P' Yc z τ M' hC'
  exact τ.eq_of_competing_of_le hbot (h1444 G A c L τ.std) (h149 G A c L τ.std) hSz hQE9
    (hn G A c L X K Y M T P' Yc z τ) hC' (hstep3 G A c L X K Y M T P' Yc z τ M' hC')

theorem res1Thm340_of
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h148 : Item148R) (h149 : Sec16.Item149S14)
    (hSz : KFacts.KPSz) {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hQE9 : Res1QE9 Q)
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau Q P A c L X K Y M T P' Yc z → Claim153Normal A (lB A)) :
    Res1Thm340 Q P :=
  res1Thm340_of_le hbot h1444 h149 hSz hQE9 hn fun G _ _ A c L _ _ _ _ _ _ _ _ τ _ hC' =>
    τ.deltaZero_le_sup_of_competing hQ hQE9 (h148 G A c L τ.sec15) (h149 G A c L τ.std) hC'

theorem res1Thm340_a7
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h148 : Item148R) (h149 : Sec16.Item149S14)
    (hSz : KFacts.KPSz) {P : ∀ (Y : Type) [Group Y], Prop}
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P A c L X K Y M T P' Yc z →
        Claim153Normal A (lB A)) :
    Res1Thm340 (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P :=
  res1Thm340_of hbot h1444 h148 h149 hSz (fun _ _ h => Or.inl h) res1QE9_a7 hn

theorem res1Thm340_m22
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h148 : Item148R) (h149 : Sec16.Item149S14)
    (hSz : KFacts.KPSz) {P : ∀ (Y : Type) [Group Y], Prop}
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P A c L X K Y M T P'
        Yc z → Claim153Normal A (lB A)) :
    Res1Thm340 (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P :=
  res1Thm340_of hbot h1444 h148 h149 hSz (fun _ _ h => Or.inr h) res1QE9_m22 hn

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
