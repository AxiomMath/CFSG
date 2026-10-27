module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846i
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl3
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem r846_of_key (hgr : CFSG.Open.GriessAllModelsStatement) (D : Data G) (hSg : SigmaStd D)
    (h614 : UC6.R6_14 D)
    (hkey : ∀ L ∈ calC D.M, ∀ n : ℕ, IsSU3 (Bar2 L) n → ∀ q : ℕ, q.Prime → 3 < q →
      q ∣ 2 ^ n + 1 → q ∉ D.sig → D.M ≤ normalizer (L : Set G) → ∀ p ∈ D.sig, p ≠ q →
        IsStronglyPEmbedded p D.M → UC22.F10.OpRes p D.M = D.M →
        ∃ S E : Subgroup G, S ≤ L ∧ IsPGroup q S ∧
          (∀ T : Subgroup G, T ≤ L → IsPGroup q T → S ≤ T → T = S) ∧
          E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧ rankThreeGamma 1 q E ≤ D.M ∧
          ∃ Sb : Subgroup (Bar2 L), IsPGroup q Sb ∧ ¬ q ∣ Sb.index ∧
            (S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Sb) :
    UC22.F08.R846 D := by
  classical
  have hSyl := UCK.u3Syl_of_griess hgr
  intro L hL n hX q hq hq3 hqn
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by rintro rfl; omega
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  by_cases hqs : q ∈ D.sig
  · exact sp_of_mem_sig hSg hns hqs
  have hN : D.M ≤ normalizer (L : Set G) := by
    by_contra hnN
    obtain ⟨E, hEL, hEel, hEcard⟩ := exists_elemAbelian_sq_of_isSU3 hSyl hX hq hq3 hqn
    have hZq : ¬ q ∣ Nat.card (center (Bar2 L)) := fun hdvd => by
      have := Nat.le_of_dvd (by norm_num) (hdvd.trans (UCK.u3Center_of_griess hgr (Bar2 L) n hX))
      omega
    have h4 := calCRankTwice D.M L hL hnN q hq hq2 hZq E hEL hEel 2 hEcard
    exact hqs (hSg.four_mem q hq hq2 (by omega))
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hpq : p ≠ q := fun h => hqs (h ▸ hpσ)
  have hsp : IsStronglyPEmbedded p D.M := sp_of_mem_sig hSg hns hpσ
  obtain ⟨S, E, hSL, hSp, hSmax, hES, hEel, hEcard, hG, Sb, hSbp, hSbidx, hSbmap⟩ :=
    hkey L hL n hX q hq hq3 hqn hqs hN p hpσ hpq hsp
      (UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp hsp)
  have hSM : S ≤ D.M := hSL.trans hLM
  obtain ⟨R', hR'⟩ := (hSp.comap_subtype : IsPGroup q (S.subgroupOf D.M)).exists_le_sylow
  let R : Subgroup G := (R' : Subgroup ↥D.M).map D.M.subtype
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf q R D.M := ⟨R', rfl⟩
  have hRq : IsPGroup q R := R'.isPGroup'.map _
  have hRM : R ≤ D.M := Subgroup.map_subtype_le _
  have hSR : S ≤ R := fun x hx => ⟨⟨x, hSM hx⟩, hR' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hRL : R ⊓ L = S := hSmax _ inf_le_right (hRq.to_le inf_le_left) (le_inf hSR hSL)
  have hEZ : E ≤ R ⊓ centralizer (R : Set G) := by
    refine le_inf (hES.trans hSR) ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrN : r ∈ normalizer (L : Set G) := hN (hRM hr)
    let m : ↥(normalizer (L : Set G)) := ⟨r, hrN⟩
    have hα1 : ∃ k : ℕ, (rhoL L m) ^ (q ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hRq ⟨r, hr⟩
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have : m ^ q ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    have hα2 : ∀ s ∈ Sb, rhoL L m s ∈ Sb := by
      intro s hs
      rw [← hSbmap] at hs ⊢
      obtain ⟨y, hy, rfl⟩ := hs
      have hyS : (y : G) ∈ S := hy
      refine ⟨Subgroup.normalizerMonoidHom L m y, ?_, rfl⟩
      show ((Subgroup.normalizerMonoidHom L m y : ↥L) : G) ∈ S
      have hmemR : ((Subgroup.normalizerMonoidHom L m y : ↥L) : G) ∈ R := by
        rw [rhoL_mk_coe]
        exact R.mul_mem (R.mul_mem hr (hSR hyS)) (R.inv_mem hr)
      have hboth : ((Subgroup.normalizerMonoidHom L m y : ↥L) : G) ∈ R ⊓ L :=
        ⟨hmemR, (Subgroup.normalizerMonoidHom L m y).2⟩
      rw [hRL] at hboth
      exact hboth
    have hfix := (hSyl (Bar2 L) n hX q hq hq3 hqn Sb hSbp hSbidx).2 (rhoL L m) hα1 hα2
    have heS : e ∈ S := hES he
    have heL : e ∈ L := hSL heS
    have hēSb : (QuotientGroup.mk (⟨e, heL⟩ : ↥L) : Bar2 L) ∈ Sb := by
      rw [← hSbmap]
      exact ⟨⟨e, heL⟩, heS, rfl⟩
    have hē : (QuotientGroup.mk (⟨e, heL⟩ : ↥L) : Bar2 L) ^ q = 1 := by
      have : (⟨e, heL⟩ : ↥L) ^ q = 1 := Subtype.ext (by simpa using hEel.2 e he)
      rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
    have h2 := (rhoL_fix_iff L m ⟨e, heL⟩).1 (hfix _ hēSb hē)
    have h3 : r * e * r⁻¹ * e⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem hr (hSR heS)) (R.inv_mem hr)) (R.inv_mem (hSR heS))
    have h4 : r * e * r⁻¹ * e⁻¹ = 1 :=
      eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hRq (isPGroup_pCoreOf L) h3 h2
    have h5 : r * e * r⁻¹ = e := mul_inv_eq_one.1 h4
    calc r * e = (r * e * r⁻¹) * r := by group
      _ = e * r := by rw [h5]
  exact h614 (sig_subset_sig1 hSg hns) q hq hq2 hqs R hRsyl E hEZ hEel hEcard hG

theorem r846_of_rank_four (hgr : CFSG.Open.GriessAllModelsStatement) (D : Data G)
    (hSg : SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ Open.pRank p D.M) (h77 : UC22.F07.R77E2 D)
    (h614 : UC6.R6_14 D) : UC22.F08.R846 D := by
  refine r846_of_key hgr D hSg h614 fun L hL n hX q hq hq3 hqn hqs hN p hpσ hpq hsp hOp => ?_
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hq2 : q ≠ 2 := by rintro rfl; omega
  obtain ⟨S, E, hSL, hSp, hSmax, hES, hEel, hEcard, hE3, Sb, hSbp, hSbidx, hSbmap⟩ :=
    keyLemma4 hgr hL.1.le hN hX hq hq3 hqn hp hp2 hpq hOp (hfour p hpσ)
  exact ⟨S, E, hSL, hSp, hSmax, hES, hEel, hEcard,
    h77 (sig_subset_sig1 hSg (not_solvable_of_mem_calC hL)) p hpσ hp2 hsp q hq hq2 hqs E
      (hES.trans (hSL.trans hL.1.le)) hEel hEcard (by omega), Sb, hSbp, hSbidx, hSbmap⟩

theorem r846_dataOfSetup4 (hgr : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G]
    [Finite G] (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hPart : PartIAt S.M) (h77 : UC22.F07.R77E2 (UC6.dataOfSetup4 hS hU S)) :
    UC22.F08.R846 (UC6.dataOfSetup4 hS hU S) :=
  r846_of_rank_four hgr _ (sigmaStd_dataOfSetup4 hS hU S)
    (fun _ hp => UC6.four_le_pRank_of_sigma hp) h77
    ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1)

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
