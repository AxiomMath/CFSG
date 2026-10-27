module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Str
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Cz

public section

namespace CFSG.Quasithin.J4M2Core

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.J4M2
open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique (IsSylowTwoOf CharTwo)

theorem isSylowTwoOf_P0_M2 :
    IsSylowTwoOf P0 M2 := by
  have hF := j4Facts
  refine ⟨P0_le_M2 hF, isPGroup_P0 hF, ?_⟩
  have h := Subgroup.card_mul_index (P0.subgroupOf M2)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P0_le_M2 hF)).toEquiv, card_P0 hF.mat hF,
    card_M2_two_part hF] at h
  omega

theorem pCoreOf_M2_eq :
    pCoreOf 2 M2 = Qgrp := by
  have hF := j4Facts
  have hM := hF.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : M2 ≤ Subgroup.normalizer (Qgrp : Set J) := fun m hm =>
    CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun x hx => Qgrp_conj_mem hF m hm x hx
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Qgrp_le_M2 hM) hQn
    (isPGroup_Qgrp hM))
  have hOK : pCoreOf 2 M2 ≤ Kgrp := by
    intro n hn
    have hnM : n ∈ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2 hn
    refine (mem_Kgrp_iff hF ⟨n, hnM⟩).mpr (Equiv.ext fun i => ?_)
    rw [Equiv.Perm.one_apply, rho_spec]
    have hg := ptElt_mem_M2 hM i.2
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M2 (M2.inv_mem hg)
    have hn' : (ptElt i)⁻¹ * n * ptElt i ∈ pCoreOf 2 M2 := by
      have := (Subgroup.mem_normalizer_iff.mp hN n).mp hn
      simpa using this
    have hH : (ptElt i)⁻¹ * n * ptElt i ∈ Hj :=
      P0_le_Hj (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf isSylowTwoOf_P0_M2 hn')
    show n • pt i = pt i
    rw [← ptElt_smul_basePt]
    calc n • (ptElt i • basePt) = ptElt i • (((ptElt i)⁻¹ * n * ptElt i) • basePt) := by
          rw [smul_smul, smul_smul, show n * ptElt i = ptElt i * ((ptElt i)⁻¹ * n * ptElt i) by
            group]
      _ = ptElt i • basePt := by rw [smul_basePt_eq_self_iff.mpr hH]
  have hsup : IsPGroup 2 ↥(Qgrp ⊔ pCoreOf 2 M2) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_Qgrp hM)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 M2).trans hQn)
  obtain ⟨k, hk⟩ := hsup.exists_card_eq
  have hdvd : 2 ^ k ∣ 3 * 2 ^ 13 := by
    rw [← hk, ← card_Kgrp hF]
    exact Subgroup.card_dvd_of_le (sup_le Qgrp_le_Kgrp hOK)
  have hk13 : 2 ^ k ∣ 2 ^ 13 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_left hdvd
  have hle : Nat.card ↥(Qgrp ⊔ pCoreOf 2 M2) ≤ Nat.card ↥Qgrp := by
    rw [hk, card_Qgrp hM]
    exact Nat.le_of_dvd (by positivity) hk13
  exact le_sup_right.trans (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm.le

theorem centralizer_pCoreOf_M2_le :
    Subgroup.centralizer ((pCoreOf 2 (Subgroup.centralizer
      ({CFSG.Quasithin.J4Loc.z0} : Set J)) : Subgroup J) : Set J) ≤
      Subgroup.zpowers CFSG.Quasithin.J4Loc.z0 := by
  have hM := j4Facts.mat
  have hO : pCoreOf 2 M2 = Qgrp := pCoreOf_M2_eq
  have hchar : CharTwo M2 := by
    have h := CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs.goodLocal_centralizer_zJ J
      (Subgroup.centralizer ({CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs.zJ} : Set J))
      (MonoidHom.id _) Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    exact h.1
  intro c hc
  have hz : z0 ∈ pCoreOf 2 M2 := hO ▸ z0_mem_Qgrp hM
  have hcM : c ∈ M2 := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact Subgroup.mem_centralizer_iff.mp hc z0 hz
  have hcO : c ∈ pCoreOf 2 M2 := hchar ⟨hcM, hc⟩
  rw [hO] at hcO
  refine center_Qgrp hM c hcO fun y hy => ?_
  exact (Subgroup.mem_centralizer_iff.mp hc y (hO ▸ hy)).symm

end CFSG.Quasithin.J4M2Core
