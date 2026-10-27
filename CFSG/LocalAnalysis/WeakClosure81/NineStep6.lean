module

public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.RankThree.GF2n.Tim78RootType
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.UniquenessCase.PartTwo
  Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {y : G}

private theorem nineStep6_mQuot_inf_eq (V U : Subgroup G) :
    E3.mQuot V (V ⊓ U) = E3.mQuot V U := by
  unfold E3.mQuot
  rw [inf_comm V U, Subgroup.inf_relIndex_right]

private theorem nineStep6_mQuot_bot_eq_rk (V : Subgroup G) :
    E3.mQuot V ⊥ = rk ↥V := by
  unfold E3.mQuot rk
  rw [Subgroup.relIndex_bot_left]

private theorem nineStep6_conjSubgroup_ne (hO : InCalO 1 (normalizer (A : Set G)) ⊥ A y) :
    conjSubgroup A y ≠ A := by
  obtain ⟨h1, -, -⟩ := hO.1
  intro h
  apply h1
  rw [h]
  exact Subgroup.le_normalizer

private theorem nineStep6_eq_one_of_mem_isPGroup_of_odd {J : Subgroup G} (hJ2 : IsPGroup 2 J)
    {x : G} (hx : x ∈ J) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := CFSG.CGT.Timmesfeld75.exists_orderOf_eq_two_pow_of_mem hJ2 hx
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
  have hdvd : orderOf x ∣ 2 ^ k := by rw [hk]
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd)

private theorem nineStep6_conj_reflection_mul_inv {u t : G} (hu : u * u = 1)
    (hutu : u * t * u⁻¹ = t⁻¹) (k : ℤ) :
    t * (t ^ k * u) * t⁻¹ * (t ^ k * u)⁻¹ = t * t := by
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h1 : (t ^ k * u)⁻¹ = u * t ^ (-k) := by
    rw [mul_inv_rev, hu_inv, ← zpow_neg]
  have h2 : u * t⁻¹ * u = t := by
    have h' : t⁻¹ = u * t * u := by rw [← hutu, hu_inv]
    rw [h']
    rw [show u * (u * t * u) * u = (u * u) * t * (u * u) by group, hu, one_mul, mul_one]
  have h4 : t * t ^ k * t * t ^ (-k) = t * t := by
    have e1 : t * t ^ k = t ^ (1 + k) := by rw [zpow_add, zpow_one]
    have e2 : t * t ^ (-k) = t ^ (1 + -k) := by rw [zpow_add, zpow_one]
    rw [show t * t ^ k * t * t ^ (-k) = (t * t ^ k) * (t * t ^ (-k)) by group, e1, e2,
      ← zpow_add]
    have he : (1 : ℤ) + k + (1 + -k) = 2 := by ring
    rw [he, show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one]
  rw [h1]
  calc t * (t ^ k * u) * t⁻¹ * (u * t ^ (-k))
      = t * t ^ k * (u * t⁻¹ * u) * t ^ (-k) := by group
    _ = t * t ^ k * t * t ^ (-k) := by rw [h2]
    _ = t * t := h4

theorem mQuot_nVSub_eq_one (hA : IsElemAbelian 2 A)
    (hO : InCalO 1 (normalizer (A : Set G)) ⊥ A y) :
    E3.mQuot A (nVSub A y) = 1 := by
  obtain ⟨h1, h2, -⟩ := hO.1
  obtain ⟨h4, -, -⟩ := hO.2
  have hle : E3.mQuot A (nVSub A y) ≤ 1 := by
    rw [nVSub, nineStep6_mQuot_inf_eq, ← conjSubgroup_normalizer A y]
    exact h2
  have hne0 : E3.mQuot A (nVSub A y) ≠ 0 := by
    intro h0
    have hE : nVSub A y = A :=
      (E3.mQuot_eq_zero_iff (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hA)
        inf_le_left).mp h0
    have hp : nVSub A y ≤ conjSubgroup (normalizer (A : Set G)) y := by
      rw [nVSub, ← conjSubgroup_normalizer A y]
      exact inf_le_right
    exact h4 ((le_of_eq hE.symm).trans hp)
  omega

theorem nVSub_ne_bot (hA : IsElemAbelian 2 A) (hm : 2 < rk ↥A)
    (hO : InCalO 1 (normalizer (A : Set G)) ⊥ A y) :
    nVSub A y ≠ ⊥ := by
  intro hbot
  have h1 := mQuot_nVSub_eq_one hA hO
  rw [hbot, nineStep6_mQuot_bot_eq_rk] at h1
  omega

theorem pCoreOf_sup_conj_eq_nVSub_sup_bSub (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hm : 2 < rk ↥A) (hO : InCalO 1 (normalizer (A : Set G)) ⊥ A y) :
    pCoreOf 2 (A ⊔ conjSubgroup A y) = nVSub A y ⊔ bSub A y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg : conjSubgroup A y ≠ A := nineStep6_conjSubgroup_ne hO
  have hP2 : IsPGroup 2 (pCoreOf 2 (A ⊔ conjSubgroup A y)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (A ⊔ conjSubgroup A y)
  have hM_le_P : nVSub A y ⊔ bSub A y ≤ pCoreOf 2 (A ⊔ conjSubgroup A y) :=
    sup_nVSub_bSub_le_pCoreOf hA hTI hg
  refine le_antisymm ?_ hM_le_P
  have hU2 : (nVSub A y).relIndex A = 2 := by
    rw [E3.relIndex_eq_two_pow (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hA),
      mQuot_nVSub_eq_one hA hO]
    norm_num
  have hB2 : (bSub A y).relIndex (conjSubgroup A y) = 2 := by
    have hmq : E3.mQuot (conjSubgroup A y) (bSub A y) = 1 := by
      have hle : E3.mQuot (conjSubgroup A y) (bSub A y) ≤ 1 := by
        rw [bSub, nineStep6_mQuot_inf_eq]
        exact hO.2.2.1
      have hne0 : E3.mQuot (conjSubgroup A y) (bSub A y) ≠ 0 := by
        intro h0
        have hBeq : bSub A y = conjSubgroup A y :=
          (E3.mQuot_eq_zero_iff
            (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
              (isElemAbelian_conjSubgroup' hA y)) inf_le_left).mp h0
        exact hO.1.1 (by rw [← hBeq]; exact inf_le_right)
      omega
    rw [E3.relIndex_eq_two_pow (V := conjSubgroup A y)
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
        (isElemAbelian_conjSubgroup' hA y)), hmq]
    norm_num
  obtain ⟨u, huA, huU, hu_char⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hU2)
  obtain ⟨w, hwAy, hwB, hw_char⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hB2)
  have hu2 : u * u = 1 := by
    have := hA.2 u huA
    rwa [pow_two] at this
  have hw2 : w * w = 1 := by
    have := (isElemAbelian_conjSubgroup' hA y).2 w hwAy
    rwa [pow_two] at this
  have hL_le : A ⊔ conjSubgroup A y ≤
      (nVSub A y ⊔ bSub A y) ⊔ Subgroup.closure ({u, w} : Set G) := by
    refine sup_le ?_ ?_
    · intro a ha
      rcases hu_char a ha with h | h
      · have huD : u⁻¹ ∈ Subgroup.closure ({u, w} : Set G) :=
          Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
        have ha_eq : a = u⁻¹ * (u * a) := by group
        rw [ha_eq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right huD)
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left h))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left h)
    · intro a ha
      rcases hw_char a ha with h | h
      · have hwD : w⁻¹ ∈ Subgroup.closure ({u, w} : Set G) :=
          Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
        have ha_eq : a = w⁻¹ * (w * a) := by group
        rw [ha_eq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hwD)
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right h))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right h)
  have hL_le_NM : A ⊔ conjSubgroup A y ≤
      Subgroup.normalizer ((nVSub A y ⊔ bSub A y : Subgroup G) : Set G) :=
    sup_le_normalizer_sup_nVSub_bSub hA hTI hg
  have hD_le_L : Subgroup.closure ({u, w} : Set G) ≤ A ⊔ conjSubgroup A y := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_left huA
    · exact Subgroup.mem_sup_right hwAy
  have hD_le_NM : Subgroup.closure ({u, w} : Set G) ≤
      Subgroup.normalizer ((nVSub A y ⊔ bSub A y : Subgroup G) : Set G) :=
    hD_le_L.trans hL_le_NM
  have htodd : Odd (orderOf (u * w)) :=
    odd_orderOf_mul hA hTI (nVSub_ne_bot hA hm hO) huA huU hwAy hwB
  have ht_ne : u * w ≠ 1 := by
    intro ht1
    have huw : u = w := by
      have h : u = (u * w) * w := by rw [mul_assoc, hw2, mul_one]
      rw [ht1, one_mul] at h
      exact h
    have hu_inf : u ∈ A ⊓ conjSubgroup A y := ⟨huA, by rw [huw]; exact hwAy⟩
    have hbot := inf_conjSubgroup_eq_bot_of_isTI hTI hg
    have hu1 : u = 1 := Subgroup.mem_bot.mp (hbot ▸ hu_inf)
    exact huU (hu1 ▸ (nVSub A y).one_mem)
  intro p hp
  have hprod : ↑((nVSub A y ⊔ bSub A y) ⊔ Subgroup.closure ({u, w} : Set G)) =
      (((nVSub A y ⊔ bSub A y : Subgroup G)) : Set G) *
      (Subgroup.closure ({u, w} : Set G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hD_le_NM
  have hpMD : p ∈ (↑(nVSub A y ⊔ bSub A y) : Set G) *
      (↑(Subgroup.closure ({u, w} : Set G)) : Set G) := by
    rw [← hprod]
    exact hL_le (CFSG.LieType.BorelTits.pCoreOf_le 2 (A ⊔ conjSubgroup A y) hp)
  obtain ⟨m, hm, d, hd, hmd⟩ := hpMD
  have hmP : m ∈ pCoreOf 2 (A ⊔ conjSubgroup A y) := hM_le_P hm
  have hdP : d ∈ pCoreOf 2 (A ⊔ conjSubgroup A y) := by
    have hd_eq : d = m⁻¹ * p := by rw [← hmd]; group
    rw [hd_eq]
    exact (pCoreOf 2 (A ⊔ conjSubgroup A y)).mul_mem
      ((pCoreOf 2 (A ⊔ conjSubgroup A y)).inv_mem hmP) hp
  have hd1 : d = 1 := by
    obtain ⟨k, hk | hk⟩ :=
      CFSG.RankThree.GF2n.Tim78.mem_closure_pair_involutions hu2 hw2 hd
    · have hodd_d : Odd (orderOf d) := by
        rw [hk]
        exact htodd.of_dvd_nat
          (orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))
      exact nineStep6_eq_one_of_mem_isPGroup_of_odd hP2 hdP hodd_d
    · exfalso
      have hutu : u * (u * w) * u⁻¹ = (u * w)⁻¹ :=
        CFSG.CGT.Timmesfeld75.left_invol_inverts hu2 hw2
      have heq := nineStep6_conj_reflection_mul_inv hu2 hutu k
      have htL : u * w ∈ A ⊔ conjSubgroup A y :=
        (A ⊔ conjSubgroup A y).mul_mem (Subgroup.mem_sup_left huA)
          (Subgroup.mem_sup_right hwAy)
      have hLP : A ⊔ conjSubgroup A y ≤
          Subgroup.normalizer (pCoreOf 2 (A ⊔ conjSubgroup A y) : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (A ⊔ conjSubgroup A y)
      have hconj_mem : (u * w) * d * (u * w)⁻¹ ∈ pCoreOf 2 (A ⊔ conjSubgroup A y) :=
        (Subgroup.mem_normalizer_iff.mp (hLP htL) d).mp hdP
      have h2P : (u * w) * (u * w) ∈ pCoreOf 2 (A ⊔ conjSubgroup A y) := by
        have hmem := (pCoreOf 2 (A ⊔ conjSubgroup A y)).mul_mem hconj_mem
          ((pCoreOf 2 (A ⊔ conjSubgroup A y)).inv_mem hdP)
        rw [hk, heq] at hmem
        exact hmem
      have h2odd : Odd (orderOf ((u * w) * (u * w))) :=
        htodd.of_dvd_nat (orderOf_dvd_of_mem_zpowers
          (Subgroup.mem_zpowers_iff.mpr ⟨2, by rw [zpow_ofNat, pow_two]⟩))
      have h2 : (u * w) * (u * w) = 1 :=
        nineStep6_eq_one_of_mem_isPGroup_of_odd hP2 h2P h2odd
      exact ht_ne (CFSG.CGT.Timmesfeld75.eq_one_of_mul_self_eq_one_of_odd h2 htodd)
  have hp_eq : p = m := by
    rw [← hmd, hd1]
    simp
  rw [hp_eq]
  exact hm

theorem inf_pCoreOf_sup_conj_eq (hA : IsElemAbelian 2 A) (hTI : IsTI A) (hm : 2 < rk ↥A)
    (hO : InCalO 1 (normalizer (A : Set G)) ⊥ A y) :
    A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A y) = nVSub A y := by
  have hne : conjSubgroup A y ≠ A := nineStep6_conjSubgroup_ne hO
  rw [pCoreOf_sup_conj_eq_nVSub_sup_bSub hA hTI hm hO]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxUB⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨u, hu, b, hb, rfl⟩ := exists_mul_of_mem_sup_nVSub_bSub hA hTI hne hxUB
    have huA : u ∈ A := (mem_nVSub.mp hu).1
    have hbA : b ∈ A := by
      have : b = u⁻¹ * (u * b) := by group
      rw [this]
      exact A.mul_mem (A.inv_mem huA) hxA
    have hbInf : b ∈ A ⊓ conjSubgroup A y := ⟨hbA, (mem_bSub.mp hb).1⟩
    rcases inf_conjSubgroup_eq_bot_or_eq hTI 1 y with hbot | heq
    · rw [CFSG.Quasithin.conjSubgroup_one] at hbot
      have hb1 : b = 1 := Subgroup.mem_bot.mp (by rw [← hbot]; exact hbInf)
      rw [hb1, mul_one]
      exact hu
    · rw [CFSG.Quasithin.conjSubgroup_one] at heq
      exact absurd heq.symm hne
  · intro x hx
    exact ⟨(mem_nVSub.mp hx).1, Subgroup.mem_sup_left hx⟩

end CFSG.LocalAnalysis.WeakClosure81
