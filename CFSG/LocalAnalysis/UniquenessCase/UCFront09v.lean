module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09e
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
import CFSG.LocalAnalysis.UniquenessCase.UCFront09h
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Alt5
import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBridge
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Section8.NormalizerEscapeRankReduction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Section8.NormalizerEscapeRankReduction
  (one_le_pRank_of_dvd)

variable {G : Type} [Group G] [Finite G]

theorem mem_calH9_of_pRank_le_three (hK : UCK.K332Cyc) (D : Data G)
    (h3 : CFSG.Open.pRank 3 D.M ≤ 3) {L X H : Subgroup G}
    (hLN : D.M ≤ normalizer (L : Set G)) (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5)
    (hU3 : ∀ A : Subgroup G, A ≤ X → Nat.card A = 3 → A ∈ uniqueSet D.M) (hX : Opp 3 X = X)
    (hH : H ≠ ⊤) (hXH : X ≤ H) (hHM : ¬ H ≤ D.M) : H ∈ calH9 D X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3X := three_dvd_card_of_isAlt_bar2 hXL hcov hA5
  obtain ⟨E, hEX, hE⟩ := exists_card_eq_three hXL hcov hA5
  have hEU := hU3 E hEX hE
  have hEH : E ≤ H := hEX.trans hXH
  have hEL : E ≤ L := hEX.trans hXL
  have hEp : IsPGroup 3 ↥E := IsPGroup.of_card (n := 1) (hE.trans (pow_one 3).symm)
  obtain ⟨P, hP, hEP⟩ := UC6.exists_isSylowOf_ge hEH hEp
  have hPM : P ≤ D.M := by
    by_contra hnot
    have hlt : P ⊓ D.M < P := lt_of_le_of_ne inf_le_left fun h => hnot (h ▸ inf_le_right)
    have hgrow := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hP.isPGroup hlt
    have hNY := normalizer_le_of_mem_uniqueSet D.maxLocal
      (mem_uniqueSet_of_le hEU (le_inf hEP hEU.1) inf_le_right)
    exact (not_lt_of_ge (le_inf inf_le_left (inf_le_right.trans hNY))) hgrow
  have hcovL : L = L ⊔ pCoreOf 2 L := (sup_eq_left.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
  obtain ⟨m, hm, hm3⟩ := exists_card_eq_three_mul le_rfl hcovL hA5
  have hLP : Nat.card ↥(L ⊓ P) ≤ 3 := by
    obtain ⟨k, hk⟩ := (hP.isPGroup.to_le inf_le_right : IsPGroup 3 ↥(L ⊓ P)).exists_card_eq
    have hdvd : 3 ^ k ∣ 3 * m := by
      rw [← hk, ← hm]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hk1 : k ≤ 1 := by
      by_contra h
      obtain ⟨c, hc⟩ := (pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hdvd
      exact hm3 ⟨c, by norm_num at hc; omega⟩
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := pow_one 3
  have hwc : ∀ h ∈ H, E.map (MulAut.conj h).toMonoidHom ≤ P →
      E.map (MulAut.conj h).toMonoidHom = E := by
    intro h _ hhP
    have hhM : h ∈ D.M := by
      have h1 : E ≤ D.M.map (MulAut.conj h⁻¹).toMonoidHom := by
        intro e he
        refine Subgroup.mem_map.2 ⟨h * e * h⁻¹, hPM (hhP (Subgroup.mem_map.2 ⟨e, he, rfl⟩)), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have h2 : h⁻¹ ∈ normalizer (D.M : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.2 (hEU.2 h⁻¹ h1)
      rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal] at h2
      simpa using D.M.inv_mem h2
    have hLh : L.map (MulAut.conj h).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hLN hhM)
    have hEhL : E.map (MulAut.conj h).toMonoidHom ≤ L := by
      rw [← hLh]
      exact Subgroup.map_mono hEL
    have hEh : Nat.card (E.map (MulAut.conj h).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hE]
    have e1 : E = L ⊓ P := Subgroup.eq_of_le_of_card_ge (le_inf hEL hEP) (by rw [hE]; exact hLP)
    have e2 : E.map (MulAut.conj h).toMonoidHom = L ⊓ P :=
      Subgroup.eq_of_le_of_card_ge (le_inf hEhL hhP) (by rw [hEh]; exact hLP)
    rw [e2, ← e1]
  have hPN : P ≤ normalizer (L : Set G) := hPM.trans hLN
  obtain ⟨ι⟩ := id hA5
  let f : ↥P →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hPN)
  have hfr : Nat.card ↥f.range ∣ 3 := by
    have hR : IsPGroup 3 ↥f.range :=
      hP.isPGroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    have h120 : Nat.card ↥f.range ∣ 120 := by
      rw [← CFSG.RankThree.PartTwo.KFacts.KS166.card_mulAut_of_alt5 ι]
      exact Subgroup.card_subgroup_dvd_card f.range
    rw [hk] at h120 ⊢
    have hk1 : k ≤ 1 := by
      by_contra h
      have h9 := (pow_dvd_pow 3 (by omega : 2 ≤ k)).trans h120
      norm_num at h9
    interval_cases k <;> norm_num
  have hQ : IsCyclic ↥f.range := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hfr with h | h
    · have : Subsingleton ↥f.range := (Nat.card_eq_one_iff_unique.1 h).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card h
  have hφ : ∀ x : ↥P, (x : G) ∈ E → f.rangeRestrict x = 1 → x = 1 := by
    intro x hxE hx1
    have hxL : (x : G) ∈ L := hEL hxE
    have hx1' : f x = 1 := by simpa using congrArg Subtype.val hx1
    have hf : f x = UC6S846.rhoL L ⟨x, hPN x.2⟩ := rfl
    rw [hf, UC6S846.rhoL_inner L x hxL] at hx1'
    have hq1 : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) = 1 := by
      refine CFSG.RankThree.PartTwo.KFacts.KS166.eq_one_of_commute_alt5 ι fun y => ?_
      have h := DFunLike.congr_fun hx1' y
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) * y
          = ((QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) * y *
              (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L)⁻¹) *
              (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) := by group
        _ = y * (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) := by rw [h]
    have hpc : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 hq1
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hpc⟩
    obtain ⟨b, hb⟩ := hP.isPGroup x
    have h2 : (x : G) ^ 2 ^ a = 1 := by
      simpa using congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => (((y : ↥L) : G))) ha
    have h3' : (x : G) ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3')
    rw [(Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 3)).gcd_eq_one] at hd
    exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd))
  have hHK : CFSG.Open.IsKGroup ↥H := D.standing.kProper.isKGroup H hH
  have htr : ∀ Y : Subgroup ↥H, CFSG.Open.pRank 3 (Y.map H.subtype) = CFSG.Open.pRank 3 Y := by
    intro Y
    rw [← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three,
      ← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
    exact CFSG.RankThree.PartOne.Quotient36.pRank_map_subtype Nat.prime_three.one_lt Y
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf H) (⊤ : Subgroup ↥H) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hP.le, Subgroup.map_top, Subgroup.range_subtype]
    exact hP
  have hS3 : CFSG.Open.pRank 3 (P.subgroupOf H) ≤ 3 := by
    rw [← htr (P.subgroupOf H), Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hP.le]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) hPM).trans h3
  have hwc' : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (E.subgroupOf H) (P.subgroupOf H) := by
    intro g hg
    unfold CFSG.conjugate at hg ⊢
    have hEg : E.map (MulAut.conj ((g⁻¹ : ↥H) : G)).toMonoidHom ≤ P := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_subgroupOf.1 (hg (Subgroup.mem_map.2
        ⟨⟨z, hEH hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩))
    have hEq := hwc ((g⁻¹ : ↥H) : G) (g⁻¹).2 hEg
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      have h1 : (((MulAut.conj g⁻¹).toMonoidHom z : ↥H) : G) ∈
          E.map (MulAut.conj ((g⁻¹ : ↥H) : G)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨z, hz, by simp⟩
      rwa [hEq] at h1
    · intro hx
      have hx' : (x : G) ∈ E := Subgroup.mem_subgroupOf.1 hx
      rw [← hEq] at hx'
      obtain ⟨e, he, hex⟩ := Subgroup.mem_map.1 hx'
      refine Subgroup.mem_map.2 ⟨⟨e, hEH he⟩, Subgroup.mem_subgroupOf.2 he, Subtype.ext ?_⟩
      simpa [MulAut.conj_apply] using hex
  let ψ : ↥(P.subgroupOf H) →* ↥f.range :=
    f.rangeRestrict.comp (Subgroup.subgroupOfEquivOfLe hP.le).toMonoidHom
  have hdisj : Disjoint ((E.subgroupOf H).subgroupOf (P.subgroupOf H)) ψ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hx hψx
    have hxE : ((x : ↥H) : G) ∈ E := hx
    exact (MulEquiv.map_eq_one_iff _).1 (hφ (Subgroup.subgroupOfEquivOfLe hP.le x) hxE hψx)
  have hcl := hK ↥H hHK (P.subgroupOf H) hS hS3 (E.subgroupOf H)
    (fun x hx => Subgroup.mem_subgroupOf.2 (hEP (Subgroup.mem_subgroupOf.1 hx)))
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv]; exact hE)
    hwc' ↥f.range hQ ψ hdisj
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G,
      N = (Subgroup.normalClosure ((E.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype :=
    ⟨_, rfl⟩
  have hN1 : CFSG.Open.pRank 3 N = 1 := by
    rw [hNdef, htr]
    exact hcl
  have hNH : ∀ h ∈ H, ∀ y ∈ N, h * y * h⁻¹ ∈ N := by
    intro h hh y hy
    rw [hNdef] at hy ⊢
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map.2 ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹,
      Subgroup.normalClosure_normal.conj_mem n hn _, by simp⟩
  have hEN : E ≤ N := by
    intro e he
    rw [hNdef]
    exact Subgroup.mem_map.2 ⟨⟨e, hEH he⟩,
      Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 he), rfl⟩
  have hXN : X ≤ N := by
    refine le_of_forall_map_conj_le hXL hcov hA5 hX hEX hE fun x hx y hy => ?_
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hNH x (hXH hx) e (hEN he)
  have hL9 : L9 X H ≤ N := by
    rw [L9, hX]
    refine iSup_le fun h y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hNH h h.2 x (hXN hx)
  refine ⟨hXH, hHM, ?_⟩
  show CFSG.Open.pRank 3 (L9 X H) = 1
  exact le_antisymm ((CFSG.SectionRank.pRank_mono (by norm_num) hL9).trans hN1.le)
    (one_le_pRank_of_dvd Nat.prime_three _ (h3X.trans (Subgroup.card_dvd_of_le (le_L9 hX))))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
