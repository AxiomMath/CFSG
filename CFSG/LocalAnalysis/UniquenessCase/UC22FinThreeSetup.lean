module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finB
import CFSG.LocalAnalysis.UniquenessCase.UC22P22re

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P22fin3

theorem exists_orderOf_eq_mem_centralizer (D : Data G) {V : Subgroup G} (hVU : V ≤ D.U)
    (hVM : D.M ≤ normalizer (V : Set G)) {p : ℕ} (hpP : p.Prime) (hp2 : p ≠ 2)
    (h3 : 3 ≤ CFSG.Open.pRank p D.M) {K : Subgroup G} (hK : K ∈ calC D.M) {n : ℕ}
    (hL : IsL2 ↥(mbarImage D.M V K) n) {t : G} (htM : t ∈ D.M)
    (htN : t ∉ normalizer (K : Set G))
    (hX : mbarImage D.M V (K ⊔ K.map (MulAut.conj t).toMonoidHom) =
      CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup (MBar D.M V))) :
    ∃ x ∈ D.M ⊓ centralizer (V : Set G), orderOf x = p := by
  haveI : Fact p.Prime := ⟨hpP⟩
  by_contra hno
  push Not at hno
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hpP.one_lt D.M
  let f : ↥E →* MBar D.M V :=
    (QuotientGroup.mk' (kerAct D.M V).normalCore).comp (Subgroup.inclusion hEM)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hN : Subgroup.inclusion hEM a ∈ (kerAct D.M V).normalCore :=
      (QuotientGroup.eq_one_iff _).1 ha
    have hc : ((Subgroup.inclusion hEM a : ↥D.M) : G) ∈ centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.1 ((kerAct D.M V).normalCore_le hN)
    by_contra ha1
    exact hno a ⟨hEM a.2, hc⟩
      (orderOf_eq_prime (hEel.2 a a.2) fun h => ha1 (Subtype.ext h))
  have hlo : CFSG.Open.pRank p D.M ≤ CFSG.Open.pRank p (⊤ : Subgroup (MBar D.M V)) :=
    CFSG.SectionRank.le_pRank_of_injective hpP.one_lt (fun a b => hEel.1.is_comm.comm a b)
      (fun a => Subtype.ext (hEel.2 a a.2)) hEcard f hf le_top
  have hhi : CFSG.Open.pRank p (⊤ : Subgroup (MBar D.M V)) ≤ 2 :=
    CFSG.SectionRank.pRank_le hpP.one_lt fun _ _ hE =>
      P22fin.card_le_sq_of_mbar_eq_pElementSubgroup D hVU hVM hpP hp2 hK hL htM htN hX hE
  omega

theorem exists_centralizer_mem_hSet (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch) :
    ∃ H ∈ hSet D.T D.M, centralizer (D.Z : Set G) ≤ H ∧
      D.M ⊓ centralizer (c.V : Set G) ≤ H := by
  obtain ⟨z, hzV, hz1, hzZ, hz2⟩ := uc22p22f_exists_z c
  refine ⟨centralizer ({z} : Set G), uc22p22r_centralizer_mem_hSet D hzZ hz1 hz2 c.hC,
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ), fun x hx => ?_⟩
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzV) hx.2

theorem setup (D : Data G) {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h15 : S22_15 D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ} (hp : p ∈ D.sig) {K : Subgroup G} {n : ℕ}
    (hK : K2213 D c p K n) {t : G} (htT : t ∈ D.T) (htN : t ∉ normalizer (K : Set G))
    (hX : mbarImage D.M c.V (K ⊔ K.map (MulAut.conj t).toMonoidHom) =
      CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup (MBar D.M c.V))) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M ∧
      ∃ H ∈ hSet D.T D.M, centralizer (D.Z : Set G) ≤ H ∧
        D.M ⊓ centralizer (c.V : Set G) ≤ H ∧ p ∣ Nat.card ↥(H ⊓ D.M) ∧
        ∃ x ∈ D.M ⊓ centralizer (c.V : Set G), orderOf x = p := by
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have hns := UC6S846.not_solvable_of_mem_calC hK.1
  obtain ⟨x, hx, hxp⟩ := exists_orderOf_eq_mem_centralizer D c.hVU c.hVM hpP hp2
    (hSg.three_le p hp) hK.1 (h15 h1930 c p hp K n hK) (D.sylowM.le htT) htN hX
  obtain ⟨H, hH, hZH, hVH⟩ := exists_centralizer_mem_hSet D c
  refine ⟨UC6S846.sp_of_mem_sig hSg hns hp, H, hH, hZH, hVH, ?_, x, hx, hxp⟩
  rw [← hxp]
  exact Subgroup.orderOf_dvd_natCard _ ⟨hVH hx, hx.1⟩

end P22fin3

end CFSG.LocalAnalysis.UniquenessCase.UC22
