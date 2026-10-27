module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentralizerPort
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBLemmas
public import CFSG.LocalAnalysis.StandardType.GGStdSubExistAdmissible
public import CFSG.LocalAnalysis.LargeEvenClassification.RankOneComparable

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

theorem externalTransfer_holds
    : externalTransfer := by
  intro G instG instFin p B Bs x L D J hS R instR θ hN hxL hT j hjL hjC hjP
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hS.1.1.tableB_facts
  haveI hFact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hSstar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := hSstar.2.2.2.2
  have hLperf : commutator L = ⊤ :=
    (isQuasisimple_of_largeEvenMarking (K := L) hS.2.1).1
  let r : R := θ ((⟨j, hjL⟩ : L) : L ⧸ Subgroup.center L)
  obtain ⟨m, hm⟩ := IsPGroup.exists_pow_pow_eq_one hjP ⟨j, Subgroup.mem_zpowers j⟩
  have hjm : j ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hLpow : (⟨j, hjL⟩ : L) ^ 3 ^ m = 1 := by
    apply Subtype.ext
    simpa using hjm
  have hrpow : r ^ 3 ^ m = 1 := by
    change (θ ((⟨j, hjL⟩ : L) : L ⧸ Subgroup.center L)) ^ 3 ^ m = 1
    rw [← map_pow]
    have hquot : ((⟨j, hjL⟩ : L) : L ⧸ Subgroup.center L) ^ 3 ^ m = 1 := by
      change (QuotientGroup.mk' (Subgroup.center L) ⟨j, hjL⟩) ^ 3 ^ m = 1
      rw [← map_pow, hLpow, map_one]
    rw [hquot, map_one]
  have hrP : IsPGroup 3 (Subgroup.zpowers r) :=
    isPGroup_zpowers_of_pow (p := 3) hp hrpow
  have hfix : ∀ a ∈ (ggBeta L θ hN).range, a r = r := by
    rintro a ⟨b, rfl⟩
    have hbj : (b : G) * j * (b : G)⁻¹ = j := by
      have hcomm : (b : G) * j = j * (b : G) :=
        Subgroup.mem_centralizer_iff.mp hjC (b : G) b.2
      rw [hcomm]
      group
    have hLeq : L.normalizerMonoidHom ⟨b, hN b.2⟩ ⟨j, hjL⟩ = ⟨j, hjL⟩ := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe]
      exact hbj
    change ggBeta L θ hN b r = r
    rw [ggBeta_eq]
    change ggLAut L θ ⟨b, hN b.2⟩
        (θ ((⟨j, hjL⟩ : L) : L ⧸ Subgroup.center L)) =
      θ ((⟨j, hjL⟩ : L) : L ⧸ Subgroup.center L)
    rw [ggLAut_apply, hLeq]
  have hA : MulAut.conj r ∈ (ggBeta L θ hN).range := hT r hfix hrP
  obtain ⟨b, hb⟩ := hA
  have hbN : (b : G) ∈ Subgroup.normalizer (L : Set G) := hN b.2
  have hb_aut : ggLAut L θ ⟨b, hbN⟩ = MulAut.conj r := by
    have hb' := hb
    rw [ggBeta_eq] at hb'
    simpa [hbN] using hb'
  have hj_aut : ggLAut L θ ⟨j, Subgroup.le_normalizer hjL⟩ = MulAut.conj r := by
    rw [ggLAut_of_mem_conj θ ⟨j, hjL⟩ (Subgroup.le_normalizer hjL)]
  have hsame : ggLAut L θ ⟨b, hbN⟩ = ggLAut L θ ⟨j, Subgroup.le_normalizer hjL⟩ :=
    hb_aut.trans hj_aut.symm
  let z : G := j⁻¹ * b
  have hzcent : z ∈ Subgroup.centralizer (L : Set G) := by
    let bN : Subgroup.normalizer (L : Set G) := ⟨b, hbN⟩
    let jN : Subgroup.normalizer (L : Set G) := ⟨j, Subgroup.le_normalizer hjL⟩
    have hgg : ggLAut L θ bN = ggLAut L θ jN := hsame
    have hprod : ggLAut L θ (jN⁻¹ * bN) = 1 := by
      rw [map_mul, map_inv, hgg, inv_mul_cancel]
    have hmem := mem_centralizer_of_ggLAut_eq_one L θ hLperf hprod
    simpa [z, jN, bN] using hmem
  have hjb : j * b = b * j :=
    (Subgroup.mem_centralizer_iff.mp hjC b b.2).symm
  have hb3 : (b : G) ^ 3 = 1 := hBs.2 (b : G) b.2
  have hb3s : b ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hzx : Commute z x := by
    have hjx : Commute j x := (Subgroup.mem_centralizer_iff.mp hjC x hxBs).symm
    have hbx : Commute (b : G) x := TableB.IsElemAbelian.comm hBs b.2 hxBs
    have : Commute (j⁻¹ * b) x := (hjx.inv_left).mul_left hbx
    simpa [z] using this
  have hxcentL : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_le_centralizer hLx
  have hzP : IsPGroup 3 (Subgroup.zpowers z) := by
    refine isPGroup_zpowers_of_pow (p := 3) hp (k := max m 1) ?_
    have hmle : m ≤ max m 1 := le_max_left _ _
    have h1le : 1 ≤ max m 1 := le_max_right _ _
    have hjm' : j ^ 3 ^ max m 1 = 1 := by
      rw [show 3 ^ max m 1 = 3 ^ m * 3 ^ (max m 1 - m) by
        rw [← pow_add, Nat.add_sub_cancel' hmle], pow_mul, hjm, one_pow]
    have hbm's : b ^ 3 ^ max m 1 = 1 := by
      rw [show 3 ^ max m 1 = 3 * 3 ^ (max m 1 - 1) by
        rw [← pow_succ', Nat.sub_add_cancel h1le], pow_mul, hb3s, one_pow]
    have hbm' : (b : G) ^ 3 ^ max m 1 = 1 := by
      simpa using congrArg Subtype.val hbm's
    have hcomm : Commute j⁻¹ b := (show Commute j b from hjb).inv_left
    calc z ^ 3 ^ max m 1 = (j⁻¹ * b) ^ 3 ^ max m 1 := rfl
      _ = (j⁻¹) ^ 3 ^ max m 1 * b ^ 3 ^ max m 1 := hcomm.mul_pow _
      _ = (j ^ 3 ^ max m 1)⁻¹ * b ^ 3 ^ max m 1 := by rw [inv_pow]
      _ = 1 := by rw [hjm', hbm', inv_one, one_mul]
  let S : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers x
  have hzS : z ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have hxS : x ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hSle : S ≤ Subgroup.centralizer (L : Set G) := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr hzcent
    · exact Subgroup.zpowers_le.mpr hxcentL
  have hxP' : x ^ 3 = 1 := hBs.2 x hxBs
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    isPGroup_zpowers_of_pow (p := 3) hp (k := 1) (by simpa using hxP')
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    have hxcz : x ∈ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact hzx.zpow_left n
    exact (Subgroup.zpowers_le.mpr hxcz).trans
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers z : Set G))
  have hSp : IsPGroup 3 S := IsPGroup.to_sup_of_normal_left' hzP hxP hnorm
  have hScyc : IsCyclic S := hcyc S hSle hSp
  have hz3L : z ^ 3 ∈ L := by
    have hz3eq : z ^ 3 = (j ^ 3)⁻¹ := by
      have hcomm : Commute j⁻¹ b := (show Commute j b from hjb).inv_left
      calc z ^ 3 = (j⁻¹ * b) ^ 3 := rfl
        _ = (j⁻¹) ^ 3 * b ^ 3 := hcomm.mul_pow 3
        _ = (j ^ 3)⁻¹ * 1 := by rw [inv_pow, hb3]
        _ = (j ^ 3)⁻¹ := mul_one _
    rw [hz3eq]
    exact Subgroup.inv_mem L (Subgroup.pow_mem L hjL 3)
  have hfinal : z ∈ Bs := by
    by_cases hz3 : z ^ 3 = 1
    ·
      have hzm : z ∈ Subgroup.zpowers x :=
        mem_zpowers_of_isCyclic (p := 3) hp hScyc hxS hzS hxP' hx1 hz3
      exact (Subgroup.zpowers_le.mpr hxBs) hzm
    ·
      exfalso
      obtain ⟨s, hs⟩ := (hzP : IsPGroup 3 (Subgroup.zpowers z)).exists_card_eq
      have hzs : orderOf z = 3 ^ s := by
        rw [← Nat.card_zpowers]
        exact hs
      have hs2 : 2 ≤ s := by
        rcases Nat.lt_or_ge s 2 with h | h
        · exfalso
          have hs01 : s = 0 ∨ s = 1 := by omega
          rcases hs01 with hs0 | hs1
          · rw [hs0] at hzs
            have hz1 : z = 1 := orderOf_eq_one_iff.mp (by simpa using hzs)
            exact hz3 (by rw [hz1]; simp)
          · rw [hs1] at hzs
            exact hz3 (by simpa [hzs] using pow_orderOf_eq_one z)
        · exact h
      have hz3le : Subgroup.zpowers (z ^ 3) ≤ Subgroup.zpowers z :=
        Subgroup.zpowers_le.mpr (Subgroup.pow_mem (Subgroup.zpowers z) (Subgroup.mem_zpowers z) 3)
      have hdvd : Nat.card ↥(Subgroup.zpowers (z ^ 3)) ∣ 3 ^ s := by
        have hdvd' : Nat.card ↥((Subgroup.zpowers (z ^ 3)).subgroupOf (Subgroup.zpowers z)) ∣
            Nat.card ↥(Subgroup.zpowers z) := Subgroup.card_subgroup_dvd_card _
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz3le).toEquiv, hs] at hdvd'
      obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have hc1 : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with hc0 | hcpos
        · exfalso
          rw [hc0] at hc
          have hbot : Subgroup.zpowers (z ^ 3) = ⊥ :=
            Subgroup.card_eq_one.mp (by simpa using hc)
          have hmem : z ^ 3 ∈ Subgroup.zpowers (z ^ 3) := Subgroup.mem_zpowers _
          rw [hbot] at hmem
          exact hz3 (Subgroup.mem_bot.mp hmem)
        · exact hcpos
      have hcardT : 3 ≤ Nat.card ↥(Subgroup.zpowers (z ^ 3)) := by
        rw [hc]
        exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hc1
      have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hxP' hx1]
      have hxSsub : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
      have hz3Ssub : Subgroup.zpowers (z ^ 3) ≤ S :=
        Subgroup.zpowers_le.mpr (Subgroup.pow_mem S hzS 3)
      have hcard : Nat.card ↥((Subgroup.zpowers x).subgroupOf S) ≤
          Nat.card ↥((Subgroup.zpowers (z ^ 3)).subgroupOf S) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxSsub).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz3Ssub).toEquiv]
        omega
      have hcomp :=
        CFSG.LargeEvenClassification.Helpers.cyclic_pGroup_subgroups_comparable
          (Ambient := ↥S) hp hSp ((Subgroup.zpowers x).subgroupOf S)
          ((Subgroup.zpowers (z ^ 3)).subgroupOf S) hcard
      have hmapped := Subgroup.map_mono (f := S.subtype) hcomp
      rw [Subgroup.map_subgroupOf_eq_of_le hxSsub,
        Subgroup.map_subgroupOf_eq_of_le hz3Ssub] at hmapped
      exact hxL ((Subgroup.zpowers_le.mpr hz3L) (hmapped (Subgroup.mem_zpowers x)))
  have hj_eq : j = b * z⁻¹ := by
    dsimp [z]
    group
  rw [hj_eq]
  exact Subgroup.mul_mem Bs b.2 (Subgroup.inv_mem Bs hfinal)

end CFSG.StandardType.GGQ2CentPort

end
