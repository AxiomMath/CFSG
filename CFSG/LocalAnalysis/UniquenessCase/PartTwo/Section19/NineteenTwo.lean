module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OppThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelQuotientA5U34Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

theorem opp_three_eq_sup (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) : Opp 3 (L ⊔ K) = L ⊔ K := by
  have hLsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_shape h.shape
  have hKsimple : IsSimpleGroup (Bar2 K) := isSimpleGroup_bar2_of_isAlt_five h.hKshape
  have hLo : Opp 3 L = L :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.opp_three_eq_self_of_bar2 h.hyp.hL.1 hLsimple
      (three_dvd_bar2_of_shape h.shape)
  have hKo : Opp 3 K = K :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.opp_three_eq_self_of_bar2 h.hK hKsimple
      (three_dvd_bar2_of_isAlt h.hKshape)
  refine le_antisymm
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_Thirteen2_pElementSubgroup_le 3 _) ?_
  refine sup_le ?_ ?_
  · calc L = Opp 3 L := hLo.symm
      _ ≤ Opp 3 (L ⊔ K) :=
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_Thirteen2_pElementSubgroup_mono le_sup_left
  · calc K = Opp 3 K := hKo.symm
      _ ≤ Opp 3 (L ⊔ K) :=
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_Thirteen2_pElementSubgroup_mono le_sup_right

theorem opp_three_eq_of_isSylow_le {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M) (hSle : S ≤ L ⊔ K) :
    Opp 3 D.M = L ⊔ K := by
  have hLKle : L ⊔ K ≤ D.M := by
    rw [← h.hLK]
    exact S17.Lp_le_M D 5
  have hnorm : ((L ⊔ K).subgroupOf D.M).Normal := by
    rw [← h.hLK]
    exact s13_Lp_normal D.M 5
  exact (PartTwo.opp_three_eq hLKle hnorm (opp_three_eq_sup D h) hS hSle).symm

theorem nineteen_two_strong {D : Data G} {p : ℕ}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hsig : D.sig ⊆ D.sig1)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (hp : p ∈ D.sig) (h3 : 3 ∉ D.sig)
    {S E : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M)
    (hEel : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 2)
    (hEZ : E ≤ S ⊓ Subgroup.centralizer (S : Set G))
    (hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G))) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    hSg.sig1_sp p (hsig hp)
  have hEM : E ≤ D.M := fun x hx => hS.le (hEZ hx).1
  have : Fact p.Prime := ⟨hp'⟩
  have hB : IsPGroup 3 E := IsPGroup.of_card (n := 2) hEcard
  have hBr : 2 ≤ CFSG.Open.pRank 3 E :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hEel hEcard
  have hGamma : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M :=
    rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp (h76 p hp' hp2 hsp) hEM hB hBr hF
  exact h614 hsig 3 Nat.prime_three (by norm_num) h3 S hS E hEZ hEel hEcard hGamma

theorem nineteen_two_strong' {D : Data G} {p : ℕ}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hsig : D.sig ⊆ D.sig1)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (hp : p ∈ D.sig)
    {S E : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M)
    (hEel : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 2)
    (hEZ : E ≤ S ⊓ Subgroup.centralizer (S : Set G))
    (hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G))) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  by_cases h3 : 3 ∈ D.sig
  · exact hSg.sig1_sp 3 (hsig h3)
  · exact nineteen_two_strong hSg hsig h76 h614 hp h3 hS hEel hEcard hEZ hF

@[expose] def Gap19_2_E (D : Data G) (L K : Subgroup G) : Prop :=
  ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S D.M → ¬ S ≤ L ⊔ K →
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ≤ S ⊓ Subgroup.centralizer (S : Set G) ∧
      2 ≤ CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer (E : Set G))

theorem nineteen_two_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (hk : D.k = 2) (hE : Gap19_2_E D L K) :
    R19_2At D V₀ V p L K h := by
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  by_cases hSle : S ≤ L ⊔ K
  · exact opp_three_eq_of_isSylow_le h hS hSle
  · exfalso
    obtain ⟨E, hEel, hEcard, hEZ, hF⟩ := hE S hS hSle
    have hp5 : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
    have hsig : D.sig ⊆ D.sig1 :=
      UC6S846.sig_subset_sig1 hSg
        (UC6S846.not_solvable_of_mem_calC (S17.calLp_subset_calC D p h.hyp.hL))
    exact (Data.k_eq_two_iff D).mp hk
      (nineteen_two_strong' hSg hsig h76 h614 hp5 hS hEel hEcard hEZ hF)

theorem k_eq_two_of_borel {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h171 : S17.R17_1At D V₀ V h.hyp.hyp125)
    (h642 : P17_64_2 D 5 2) :
    D.k = 2 := by
  have hYM : S17.Lp D 5 ≤ D.M := S17.Lp_le_M D 5
  have hYn : ((S17.Lp D 5).subgroupOf D.M).Normal := s13_Lp_normal D.M 5
  have hTY : D.T ≤ Subgroup.normalizer ((S17.Lp D 5 : Subgroup G) : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYn)
  have hTM : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hSyl : CFSG.Quasithin.IsSylowIn 2 (D.T ⊓ (S17.Lp D 5)) (S17.Lp D 5) :=
    hTM.inf_normal hYM hYn
  have hshape : IsL2Square (Bar2 (S17.Lp D 5)) 2 ∨ IsL2U3Product (Bar2 (S17.Lp D 5)) 2 := by
    rcases h642 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨-, hcart⟩ := Inputs1719.k_A5U34BorelQuotient_holds
    (Bar2 (S17.Lp D 5)) 2 rfl hshape
  obtain ⟨hQ, E9, hE9el, hE9card⟩ := cartanQuotient_of_bar2 hSyl.toSylow hcart
  exact (Data.k_eq_two_iff D).mpr
    (not_isStronglyPEmbedded_of_normalizerQuotient h.hyp.hyp125 (ne_bot_of_one_lt_mSub h.hyp.big)
      h171 hYM hTY hSyl hQ.is_comm.comm hE9el hE9card)

theorem nineteen_two (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (h171 : S17.R17_1At D V₀ V h.hyp.hyp125) (h642 : P17_64_2 D 5 2)
    (hE : Gap19_2_E D L K) :
    R19_2At D V₀ V p L K h :=
  nineteen_two_of D h hSg h76 h614 (k_eq_two_of_borel h h171 h642) hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
