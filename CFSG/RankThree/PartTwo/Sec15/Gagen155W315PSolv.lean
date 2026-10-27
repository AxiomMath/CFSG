module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.Foundations.Catalog
import CFSG.RankThree.PartTwo.Sec4.T444.LiftMin
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.PRankQuotientLift
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.IndexNormalSup

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Proof155P

theorem isSolvable_of_pRank_five_le_one (hSz : KFacts.KPSz)
    {M W N : Subgroup G} (hK : CFSG.IsKGroup ↥M) (hWM : W ≤ M) (hWp : Group.IsPerfect ↥W)
    (hNW : N ≤ W) (hNn : (N.subgroupOf W).Normal) (hN3 : ¬ 3 ∣ Nat.card N)
    (hθ : inSubgroup (aschbacherSolvableCore 3) W ≤ N) (h5 : 5 ∣ (N.subgroupOf W).index)
    (hrk : CFSG.Open.pRank 5 W ≤ 1) : IsSolvable ↥N := by
  classical
  by_contra hns
  let F : Subgroup ↥W := aschbacherSolvableCore 3 ↥W
  haveI hFnormal : F.Normal := aschbacherSolvableCore_normal 3 ↥W
  let Y := ↥W ⧸ F
  let ρ : ↥W →* Y := QuotientGroup.mk' F
  let Nbar : Subgroup Y := (N.subgroupOf W).map ρ
  have hF_solv : Group.IsSolvable F :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have hθF : F ≤ N.subgroupOf W := fun x hx =>
    hθ (Subgroup.mem_map_of_mem W.subtype hx)
  have hNbar_normal : Nbar.Normal := hNn.map ρ (QuotientGroup.mk'_surjective F)
  have hNbar_ne : Nbar ≠ ⊥ := by
    intro hbot
    apply hns
    have hmap : (N.subgroupOf W).map ρ = ⊥ := hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    haveI : Group.IsSolvable F := hF_solv
    have hsolvSub : Group.IsSolvable (N.subgroupOf W) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hmap)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNW).symm.toMonoidHom) (MulEquiv.injective _)
  have hNbar3 : ¬ 3 ∣ Nat.card Nbar := by
    intro h
    apply hN3
    have hdvd : Nat.card Nbar ∣ Nat.card (N.subgroupOf W) := Subgroup.card_map_dvd _ _
    have hcard : Nat.card (N.subgroupOf W) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
    rw [← hcard]
    exact h.trans hdvd
  have hθY : aschbacherSolvableCore 3 Y = ⊥ := (theta_quotient_core_and_ranks (G := ↥W)).1
  obtain ⟨K, hKcomp, hKNbar⟩ :=
    Sec4.exists_isComponent_le_of_isSubnormal hθY hNbar_normal.isSubnormal hNbar_ne hNbar3
  have hK3 : ¬ 3 ∣ Nat.card K := fun h => hNbar3 (h.trans (Subgroup.card_dvd_of_le hKNbar))
  have hKZ : K ⊓ Subgroup.centralizer (K : Set Y) = ⊥ := by
    rw [CFSG.GroupTheory.inf_centralizer_eq_map_center]
    have hle := Sec4.le_aschbacherSolvableCore_of_isSubnormal
      (T := (Subgroup.center K).map K.subtype)
      (Subgroup.IsSubnormal.trans' (Subgroup.normal_of_characteristic _).isSubnormal hKcomp.2)
      (Group.isSolvable_of_isSolvable_injective (f :=
        ((Subgroup.center K).equivMapOfInjective _ K.subtype_injective).symm.toMonoidHom)
        (MulEquiv.injective _))
      (fun h => hK3 (h.trans (by
        rw [Subgroup.card_map_of_injective K.subtype_injective]
        exact Subgroup.card_subgroup_dvd_card _)))
    rwa [hθY, le_bot_iff] at hle
  have hcenter : Subgroup.center K = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective,
      ← CFSG.GroupTheory.inf_centralizer_eq_map_center, hKZ]
  have hsimp : IsSimpleGroup K := by
    have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center K)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcenter]
    have e := MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center K))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
    haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hKcomp.1.2.1
    haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKcomp.1
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  haveI : IsSimpleGroup K := hsimp
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKcomp.1.2.2
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        exact ⟨a, b, fun h => hab (by
          rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  have hKW : CFSG.IsKGroup ↥W :=
    hK.of_injective (Subgroup.inclusion hWM) (Subgroup.inclusion_injective hWM)
  have hcat : CFSG.Assembly.InCatalog K :=
    Sec4.inCatalog_of_le_quotient (G := ↥W) (N := F) (K := K) hKW
  have hout := KFacts.commutator_le_inner_of_not_three_dvd hSz hnab hcat hK3
  have h5K : 5 ∣ Nat.card K := by
    obtain ⟨f, hf⟩ := hSz K hnab hcat hK3
    exact Sec16.KSL3PiNoSzProof.five_dvd_card_of_suzukiModel hf
  have key : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    by_cases hKN : K.Normal
    ·
      haveI : K.Normal := hKN
      let C : Subgroup Y := Subgroup.centralizer (K : Set Y)
      haveI hCnormal : C.Normal := Subgroup.normal_centralizer
      haveI : Group.IsPerfect ↥W := hWp
      haveI hYperf : Group.IsPerfect Y :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' F)
          (QuotientGroup.mk'_surjective F)
      haveI : Group.IsPerfect (⊤ : Subgroup Y) := Group.IsPerfect.top_iff.mpr hYperf
      have hYsup : K ⊔ C = ⊤ := by
        rw [eq_top_iff]
        intro r _
        have hRK : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) := by
          rw [Subgroup.normalizer_eq_top_iff.mpr hKN]
        obtain ⟨k, hk, hkc⟩ := Sec4.exists_mem_inv_mul_mem_centralizer (K := K) (R := ⊤)
          hRK hout (r := r) trivial
        have hkc' : k⁻¹ * r ∈ C := hkc
        have hrk : r = k * (k⁻¹ * r) := by group
        exact Subgroup.mem_sup_of_normal_left.mpr ⟨k, hk, k⁻¹ * r, hkc', hrk.symm⟩
      have hCsup : C ⊔ Nbar = ⊤ := by
        rw [eq_top_iff]
        calc ⊤ = K ⊔ C := hYsup.symm
          _ ≤ Nbar ⊔ C := sup_le_sup_right hKNbar C
          _ = C ⊔ Nbar := sup_comm _ _
      have hidx : Nbar.index = (C ⊓ Nbar).relIndex C :=
        CFSG.GorensteinWalter.index_eq_relIndex_inf_of_normal_sup C Nbar hCnormal hCsup
      have hNbar_index : Nbar.index = (N.subgroupOf W).index := by
        have h := Subgroup.index_map (N.subgroupOf W) ρ
        rw [show ρ.ker = F from QuotientGroup.ker_mk' F,
          show ρ.range = ⊤ from QuotientGroup.range_mk' F,
          sup_eq_left.mpr hθF, Subgroup.index_top, mul_one] at h
        exact h
      have h5rel : 5 ∣ (C ⊓ Nbar).relIndex C := by
        rw [← hidx, hNbar_index]
        exact h5
      have h5C : 5 ∣ Nat.card C :=
        h5rel.trans ⟨Nat.card ↥((C ⊓ Nbar) ⊓ C),
          (Subgroup.relIndex_mul_card (H := C ⊓ Nbar) (K := C)).symm⟩
      obtain ⟨c, hcord⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 h5C
      obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 h5K
      have hx5 : (x : Y) ^ 5 = 1 := by
        rw [← Subgroup.coe_pow, ← hxord, pow_orderOf_eq_one, Subgroup.coe_one]
      have hc5 : (c : Y) ^ 5 = 1 := by
        rw [← Subgroup.coe_pow, ← hcord, pow_orderOf_eq_one, Subgroup.coe_one]
      have hcomm : Commute (x : Y) (c : Y) :=
        Subgroup.mem_centralizer_iff.mp c.2 x x.2
      have hx1 : (x : Y) ≠ 1 := by
        intro h
        have hx : x = 1 := Subtype.ext h
        rw [hx, orderOf_one] at hxord
        omega
      have hind : ∀ n : ℕ, (x : Y) ^ n ≠ (c : Y) := by
        intro n hn
        have hxK : (x : Y) ^ n ∈ K := K.pow_mem x.2 n
        have hcK : (c : Y) ∈ K := by rw [← hn]; exact hxK
        have hmem : (c : Y) ∈ K ⊓ C := ⟨hcK, c.2⟩
        rw [show K ⊓ C = ⊥ from hKZ] at hmem
        have hc1 : (c : Y) = 1 := hmem
        have hc1' : c = 1 := Subtype.ext hc1
        rw [hc1', orderOf_one] at hcord
        omega
      exact CFSG.SectionRank.two_le_pRank_top_of_commute hx5 hc5 hcomm hx1 hind
    ·
      rw [Subgroup.normal_iff_map_conj_eq] at hKN
      push Not at hKN
      obtain ⟨y, hy⟩ := hKN
      let L : Subgroup Y := K.map (MulAut.conj y).toMonoidHom
      have hL : IsComponent L := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hKcomp
      have hLKcomm : ⁅K, L⁆ = ⊥ := by
        rcases CFSG.LocalCores.distinct_components_commute hKcomp hL with h | h
        · exact absurd h.symm hy
        · exact h
      have hLK : L ≤ Subgroup.centralizer (K : Set Y) := by
        have h' : ⁅L, K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hLKcomm
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h'
      have hKLbot : K ⊓ L = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        have haC : a ∈ Subgroup.centralizer (K : Set Y) := hLK ha.2
        have hmem : a ∈ K ⊓ Subgroup.centralizer (K : Set Y) := ⟨ha.1, haC⟩
        rw [hKZ] at hmem
        exact hmem
      have h5L : 5 ∣ Nat.card L := by
        rw [show Nat.card L = Nat.card K from
          Subgroup.card_map_of_injective (MulAut.conj y).injective]
        exact h5K
      obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 h5K
      obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := L) 5 h5L
      have hx5 : (x : Y) ^ 5 = 1 := by
        rw [← Subgroup.coe_pow, ← hxord, pow_orderOf_eq_one, Subgroup.coe_one]
      have hz5 : (z : Y) ^ 5 = 1 := by
        rw [← Subgroup.coe_pow, ← hzord, pow_orderOf_eq_one, Subgroup.coe_one]
      have hcomm : Commute (x : Y) (z : Y) :=
        Subgroup.mem_centralizer_iff.mp (hLK z.2) x x.2
      have hx1 : (x : Y) ≠ 1 := by
        intro h
        have hx : x = 1 := Subtype.ext h
        rw [hx, orderOf_one] at hxord
        omega
      have hind : ∀ n : ℕ, (x : Y) ^ n ≠ (z : Y) := by
        intro n hn
        have hxK : (x : Y) ^ n ∈ K := K.pow_mem x.2 n
        have hzK : (z : Y) ∈ K := by rw [← hn]; exact hxK
        have hmem : (z : Y) ∈ K ⊓ L := ⟨hzK, z.2⟩
        rw [hKLbot] at hmem
        have hz1 : (z : Y) = 1 := hmem
        have hz1' : z = 1 := Subtype.ext hz1
        rw [hz1', orderOf_one] at hzord
        omega
      exact CFSG.SectionRank.two_le_pRank_top_of_commute hx5 hz5 hcomm hx1 hind
  have h2W : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥W) :=
    CFSG.GroupTheory.two_le_pRank_of_quotient (Y := ↥W) F (by norm_num) (by norm_num) key
  have h2 : 2 ≤ CFSG.Open.pRank 5 W := by
    rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup W]
  omega

end Proof155P

end CFSG.RankThree.PartTwo.Sec15
