module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.Quasithin.EmptyFaithful.S1421F112

import CFSG.GroupTheory.ConjQuot
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.St84

open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem NatQuot.exists_conj_mul_mem {L E Z : Subgroup G} [Finite ↥L] {n : ℕ}
    (h : NatQuot L E Z n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hE : IsPGroup 2 ↥E)
    {x y : G} (hx : x ∈ E) (hxZ : x ∉ Z) (hy : y ∈ E) (hyZ : y ∉ Z) :
    ∃ l ∈ L, y⁻¹ * (l * x * l⁻¹) ∈ Z := by
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exfalso
      have hEZ : E ≤ Z := by
        apply Subgroup.relIndex_eq_one.mp
        simpa [hn0] using h.index
      exact hxZ (hEZ hx)
    · exact hnpos
  have hLE : L ≤ Subgroup.normalizer (E : Set G) := fun l hl => (h.normal hl).1
  have hLZ : L ≤ Subgroup.normalizer (Z : Set G) := fun l hl => (h.normal hl).2
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := h.E_le.trans hLZ
  haveI : (Z.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.Z_le).mpr hEZ
  let Q := ↥E ⧸ Z.subgroupOf E
  let q : ℕ := 2 ^ n
  have hcardQ : Nat.card Q = q ^ 2 := by
    have hidx : Nat.card Q = 2 ^ (2 * n) := by
      have hidx' := h.index
      rw [Subgroup.relIndex, Subgroup.index_eq_card] at hidx'
      exact hidx'
    have hpow : q ^ 2 = 2 ^ (2 * n) := by
      show (2 ^ n) ^ 2 = 2 ^ (2 * n)
      rw [← pow_mul, mul_comm n 2]
    exact hidx.trans hpow.symm
  haveI hQfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcardQ]; positivity)
  letI : MulAction ↥L Q := MulAction.compHom Q (CFSG.GroupTheory.conjQuotHom hLE hLZ)
  have hsmul : ∀ (l : ↥L) (e : ↥E),
      l • (e : Q) = ((⟨(l : G) * e * (l : G)⁻¹, (hLE l.2 e).mp e.2⟩ : ↥E) : Q) := by
    intro l e
    rw [MulAction.compHom_smul_def, MulAut.smul_def, CFSG.GroupTheory.conjQuotHom_apply,
      CFSG.GroupTheory.conjQuotAut_mk]
  have hsmul_one : ∀ l : ↥L, l • (1 : Q) = 1 := by
    intro l
    rw [MulAction.compHom_smul_def]
    exact map_one _
  let xQ : Q := (⟨x, hx⟩ : ↥E)
  let yQ : Q := (⟨y, hy⟩ : ↥E)
  let Stab : Subgroup ↥L := MulAction.stabilizer ↥L xQ
  have hxQ : xQ ≠ 1 := by
    intro h1
    apply hxZ
    have hmem : (⟨x, hx⟩ : ↥E) ∈ Z.subgroupOf E := (QuotientGroup.eq_one_iff _).mp h1
    exact (Subgroup.mem_subgroupOf).mp hmem
  have hyQ : yQ ≠ 1 := by
    intro h1
    apply hyZ
    have hmem : (⟨y, hy⟩ : ↥E) ∈ Z.subgroupOf E := (QuotientGroup.eq_one_iff _).mp h1
    exact (Subgroup.mem_subgroupOf).mp hmem
  have hstab : IsPGroup 2 Stab := by
    rw [IsPGroup.iff_orderOf]
    intro k
    let kL : ↥L := (k : Stab)
    obtain ⟨a, o, ho, horder⟩ :=
      Nat.exists_eq_two_pow_mul_odd (isOfFinOrder_of_finite kL).orderOf_pos.ne'
    let k' : ↥L := kL ^ 2 ^ a
    have hk'order : orderOf k' = o := by
      dsimp [k']
      rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
        (horder ▸ dvd_mul_right _ _), horder]
      exact Nat.mul_div_cancel_left o (pow_pos (by norm_num) a)
    have hk'stab : k' ∈ Stab := by
      dsimp [k', kL, Stab]
      exact Subgroup.pow_mem _ k.2 _
    have hk'fix : k' • xQ = xQ := (MulAction.mem_stabilizer_iff).mp hk'stab
    by_cases ho1 : o = 1
    · refine ⟨a, ?_⟩
      rw [← Subgroup.orderOf_coe k, horder, ho1, mul_one]
    · exfalso
      have hnotE : ((k' : ↥L) : G) ∉ E := by
        intro hmem
        have hordE : orderOf (⟨((k' : ↥L) : G), hmem⟩ : ↥E) = o := by
          rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hk'order]
        have hc := hE.orderOf_coprime (Nat.coprime_two_left.mpr ho) (⟨_, hmem⟩ : ↥E)
        rw [hordE] at hc
        exact ho1 (by simpa [Nat.Coprime, Nat.gcd_self] using hc)
      have hcomm : ⁅x⁻¹, ((k' : ↥L) : G)⁆ ∈ Z := by
        have hquot : ((⟨(k' : G) * x * (k' : G)⁻¹, (hLE k'.2 x).mp hx⟩ : ↥E) : Q)
            = ((⟨x, hx⟩ : ↥E) : Q) := by
          rw [← hsmul k' ⟨x, hx⟩]
          exact hk'fix
        have hmemZ : (((k' : G) * x * (k' : G)⁻¹)⁻¹ * x) ∈ Z := by
          have h := (Subgroup.mem_subgroupOf).mp (QuotientGroup.eq.mp hquot)
          simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
        have hgoal : ⁅x⁻¹, ((k' : ↥L) : G)⁆ =
            (((k' : G) * x * (k' : G)⁻¹)⁻¹ * x)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [hgoal]
        exact Z.inv_mem hmemZ
      have hxZ' := h.fpf ((k' : ↥L) : G) k'.2 (by
        rw [Subgroup.orderOf_coe, hk'order]
        exact ho) hnotE x⁻¹ (E.inv_mem hx) hcomm
      exact hxZ (by simpa using Z.inv_mem hxZ')
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨a', ha'⟩ := hP.exists_card_eq
  obtain ⟨b, hb⟩ := hstab.exists_card_eq
  have hcardL : Nat.card ↥L =
      Nat.card (CFSG.pCore 2 ↥L) * Nat.card (oTwoQuot ↥L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), Nat.mul_comm]
  have hcardO : Nat.card (oTwoQuot ↥L) = q * (q ^ 2 - 1) := by
    obtain ⟨e⟩ := hq
    rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card (by omega : n ≠ 0)]
  have hpar : Odd (q ^ 2 - 1) := by
    have hqeven : Even q := by
      dsimp [q]
      exact even_two.pow_of_ne_zero (by omega : n ≠ 0)
    have hqpos : 0 < q := by dsimp [q]; positivity
    exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (pow_pos hqpos 2).ne')
      (hqeven.pow_of_ne_zero (by norm_num : 2 ≠ 0)) odd_one
  have hcop : Nat.Coprime (2 ^ b) (q ^ 2 - 1) :=
    Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hpar)
  have hdiv : Nat.card ↥Stab ∣ Nat.card ↥L := Subgroup.card_subgroup_dvd_card Stab
  rw [hcardL, ha', hb, hcardO] at hdiv
  have hdiv2 : 2 ^ b ∣ 2 ^ a' * q :=
    hcop.dvd_of_dvd_mul_right (by rwa [← mul_assoc] at hdiv)
  obtain ⟨c, hc⟩ := hdiv2
  have hcancel : Nat.card ↥Stab * Stab.index = Nat.card ↥L := Subgroup.card_mul_index Stab
  rw [hcardL, ha', hb, hcardO] at hcancel
  have hidx : Stab.index = c * (q ^ 2 - 1) := by
    refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ b) ?_
    have hmul : 2 ^ b * Stab.index = 2 ^ b * (c * (q ^ 2 - 1)) := by
      rw [hcancel]
      calc
        2 ^ a' * (q * (q ^ 2 - 1)) = (2 ^ a' * q) * (q ^ 2 - 1) := by ring
        _ = (2 ^ b * c) * (q ^ 2 - 1) := by rw [hc]
        _ = 2 ^ b * (c * (q ^ 2 - 1)) := by ring
    exact hmul
  have hidx_ge : q ^ 2 - 1 ≤ Stab.index := by
    rw [hidx]
    refine Nat.le_mul_of_pos_left (q ^ 2 - 1) ?_
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · exfalso
      rw [hc0, mul_zero] at hc
      have hpos : 0 < 2 ^ a' * q := by positivity
      omega
    · exact hcpos
  have horbit_subset : MulAction.orbit ↥L xQ ⊆ {c : Q | c ≠ 1} := by
    rintro c ⟨l, rfl⟩ hc
    apply hxQ
    have hone : l • (1 : Q) = 1 := hsmul_one l
    exact (smul_left_cancel_iff l).mp (hc.trans hone.symm)
  have hS_ncard : ({c : Q | c ≠ 1} : Set Q).ncard = q ^ 2 - 1 := by
    have hset : {c : Q | c ≠ 1} = Set.univ \ ({1} : Set Q) := by
      ext c
      simp
    rw [hset, Set.ncard_sdiff (Set.singleton_subset_iff.mpr (Set.mem_univ 1))
      (Set.finite_singleton 1), Set.ncard_univ, Set.ncard_singleton, hcardQ]
  have hindex_stab : Stab.index = (MulAction.orbit ↥L xQ).ncard :=
    MulAction.index_stabilizer ↥L xQ
  have horbit_eq : MulAction.orbit ↥L xQ = {c : Q | c ≠ 1} := by
    refine Set.eq_of_subset_of_ncard_le horbit_subset ?_
    rw [hS_ncard, ← hindex_stab]
    exact hidx_ge
  have hy_in : yQ ∈ MulAction.orbit ↥L xQ := by
    rw [horbit_eq]
    exact hyQ
  obtain ⟨l, hl⟩ := (MulAction.mem_orbit_iff).mp hy_in
  refine ⟨(l : G), l.2, ?_⟩
  have hquot : ((⟨(l : G) * x * (l : G)⁻¹, (hLE l.2 x).mp hx⟩ : ↥E) : Q)
      = ((⟨y, hy⟩ : ↥E) : Q) := by
    rw [← hsmul l ⟨x, hx⟩]
    exact hl
  have hmemZ : (((l : G) * x * (l : G)⁻¹)⁻¹ * y) ∈ Z := by
    have h := (Subgroup.mem_subgroupOf).mp (QuotientGroup.eq.mp hquot)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hfin : y⁻¹ * ((l : G) * x * (l : G)⁻¹) ∈ Z := by
    have h := Z.inv_mem hmemZ
    simpa [mul_inv_rev] using h
  exact hfin

end CFSG.Quasithin.St84
