module

public import CFSG.Timmesfeld.Bridge.OddTranspLocal
import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

variable {X : Type} [Group X] [Finite X] {D : Set X}

private def fixedFreeCount_CQ (Q : Subgroup X) (u : X) : Subgroup X :=
  Q ⊓ Subgroup.centralizer ({u} : Set X)

private lemma fixedFreeCount_mem_CQ {Q : Subgroup X} {u y : X} :
    y ∈ fixedFreeCount_CQ Q u ↔ y ∈ Q ∧ Commute y u := by
  rw [fixedFreeCount_CQ, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  rfl

private lemma fixedFreeCount_ncard_conj_eq_relIndex (Q : Subgroup X) (u : X) :
    ((fun y => y * u * y⁻¹) '' (Q : Set X)).ncard =
      (Q ⊓ Subgroup.centralizer ({u} : Set X)).relIndex Q :=
  (CFSG.ComponentClassification.HSFLit.relIndex_inf_centralizer_eq_ncard Q u).symm

private lemma fixedFreeCount_stabilizer_card {G : Type*} [Group G] {H K : Subgroup G}
    [MulAction (H × K) G]
    (hact : ∀ (p : H × K) (x : G), p • x = (p.1 : G) * x * (p.2 : G)⁻¹) :
    Nat.card (MulAction.stabilizer (H × K) (1 : G)) = Nat.card ↥(H ⊓ K) := by
  refine Nat.card_congr
    { toFun := fun p => ⟨((p.1).1 : G), (p.1).1.2, by
        have hp : ((p.1).1 : G) = ((p.1).2 : G) := by
          have h := MulAction.mem_stabilizer_iff.mp p.2
          rw [hact, mul_one] at h
          exact mul_inv_eq_one.mp h
        rw [hp]
        exact (p.1).2.2⟩
      invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨z, z.2.2⟩), by
        rw [MulAction.mem_stabilizer_iff, hact]
        simp⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          have hp : ((p.1).1 : G) = ((p.1).2 : G) := by
            have h := MulAction.mem_stabilizer_iff.mp p.2
            rw [hact, mul_one] at h
            exact mul_inv_eq_one.mp h
          exact hp
      right_inv := by
        intro z
        rfl }

private theorem fixedFreeCount_card_mul_card_inf_of_setMul {G : Type*} [Group G] [Finite G]
    {H K Q : Subgroup G} (hH : H ≤ Q) (hK : K ≤ Q)
    (hmul : ∀ q ∈ Q, ∃ h ∈ H, ∃ k ∈ K, h * k = q) :
    Nat.card Q * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  classical
  letI : MulAction (H × K) G :=
    { smul := fun p x => (p.1 : G) * x * (p.2 : G)⁻¹
      one_smul := by
        intro x
        change (1 : G) * x * (1 : G)⁻¹ = x
        group
      mul_smul := by
        intro p q x
        change ((p.1 * q.1 : H) : G) * x * (((p.2 * q.2 : K) : G))⁻¹ =
          (p.1 : G) * ((q.1 : G) * x * (q.2 : G)⁻¹) * (p.2 : G)⁻¹
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        group }
  have hstab := fixedFreeCount_stabilizer_card (H := H) (K := K) (fun _ _ => rfl)
  have horb : MulAction.orbit (H × K) (1 : G) = (Q : Set G) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      show (p.1 : G) * 1 * (p.2 : G)⁻¹ ∈ Q
      simpa using Q.mul_mem (hH p.1.2) (Q.inv_mem (hK p.2.2))
    · intro hx
      obtain ⟨h, hh, k, hk, hkq⟩ := hmul x hx
      refine ⟨(⟨h, hh⟩, (⟨k, hk⟩ : K)⁻¹), ?_⟩
      change (h : G) * 1 * ((k : G)⁻¹)⁻¹ = x
      rw [inv_inv]
      simpa using hkq
  have hOS : Nat.card (MulAction.orbit (H × K) (1 : G)) *
      Nat.card (MulAction.stabilizer (H × K) (1 : G)) = Nat.card (H × K) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (H × K) 1)
  rw [horb, hstab, Nat.card_prod] at hOS
  simpa using hOS

private lemma fixedFreeCount_card_eq_mul_relIndex {Q Ca Cc C : Subgroup X}
    (hCaQ : Ca ≤ Q) (hCcQ : Cc ≤ Q)
    (hprod : Nat.card Q * Nat.card C = Nat.card Ca * Nat.card Cc) :
    Nat.card Q = Nat.card C * (Ca.relIndex Q * Cc.relIndex Q) := by
  have hia : Ca.relIndex Q * Nat.card Ca = Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := Ca) (K := Q)
    rwa [inf_eq_left.mpr hCaQ] at h
  have hic : Cc.relIndex Q * Nat.card Cc = Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := Cc) (K := Q)
    rwa [inf_eq_left.mpr hCcQ] at h
  have hmain : Ca.relIndex Q * Cc.relIndex Q * Nat.card C = Nat.card Q := by
    apply Nat.mul_right_cancel (Nat.mul_pos (Nat.card_pos (α := Ca)) (Nat.card_pos (α := Cc)))
    calc (Ca.relIndex Q * Cc.relIndex Q * Nat.card C) * (Nat.card Ca * Nat.card Cc)
        = (Ca.relIndex Q * Nat.card Ca) * (Cc.relIndex Q * Nat.card Cc) * Nat.card C := by
          ring
      _ = Nat.card Q * Nat.card Q * Nat.card C := by rw [hia, hic]
      _ = Nat.card Q * (Nat.card Ca * Nat.card Cc) := by rw [← hprod]; ring
  rw [← hmain]
  ring

theorem card_eq_ncard_inter_centralizer_mul (hS : Setup X D) {Q : Subgroup X} [Q.Normal]
    (hQ : IsPGroup 2 Q) {a c : X} (ha : a ∈ D) (hc : c ∈ D) (hac : ¬ Commute a c)
    (hgen : Subgroup.closure (insert a {f | f ∈ D ∧ Commute f c}) = ⊤) :
    Nat.card Q = {y | y ∈ Q ∧ Commute y a ∧ Commute y c}.ncard *
      (((fun y => y * a * y⁻¹) '' (Q : Set X)).ncard *
        ((fun y => y * c * y⁻¹) '' (Q : Set X)).ncard) := by
  classical
  let Ca := fixedFreeCount_CQ Q a
  let Cc := fixedFreeCount_CQ Q c
  let C := Ca ⊓ Cc
  have hCaQ : Ca ≤ Q := inf_le_left
  have hCcQ : Cc ≤ Q := inf_le_left
  have hthree := localQ_three hS.oddT hS.normal hQ hS hc ha (fun h => hac h.symm) hgen
  have hmul : ∀ q ∈ Q, ∃ h ∈ Cc, ∃ k ∈ Ca, h * k = q := by
    intro q hq
    obtain ⟨y₁, hy₁Q, hy₁c, y₂, hy₂, hyeq⟩ := hthree.2.1 q hq
    refine ⟨y₁, ?_, y₂, ?_, hyeq.symm⟩
    · exact ⟨hy₁Q, Subgroup.mem_centralizer_singleton_iff.mpr hy₁c.eq⟩
    · exact ⟨Subgroup.commutator_le_left Q _ hy₂,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (commute_of_mem_commutator hS.oddT hS.normal hQ ha ha (Commute.refl a) hy₂).symm.eq⟩
  have hprod := fixedFreeCount_card_mul_card_inf_of_setMul hCcQ hCaQ hmul
  have hprod' : Nat.card Q * Nat.card C = Nat.card Ca * Nat.card Cc := by
    rw [inf_comm Cc Ca, mul_comm (Nat.card Cc) (Nat.card Ca)] at hprod
    simpa [C] using hprod
  have hra : ((fun y => y * a * y⁻¹) '' (Q : Set X)).ncard = Ca.relIndex Q := by
    simpa [Ca, fixedFreeCount_CQ] using fixedFreeCount_ncard_conj_eq_relIndex Q a
  have hrc : ((fun y => y * c * y⁻¹) '' (Q : Set X)).ncard = Cc.relIndex Q := by
    simpa [Cc, fixedFreeCount_CQ] using fixedFreeCount_ncard_conj_eq_relIndex Q c
  have hset : {y | y ∈ Q ∧ Commute y a ∧ Commute y c}.ncard = Nat.card C := by
    have hEq : {y | y ∈ Q ∧ Commute y a ∧ Commute y c} = (C : Set X) := by
      ext y
      simp [C, Ca, Cc, fixedFreeCount_CQ, Subgroup.mem_centralizer_singleton_iff, Commute,
        SemiconjBy]
      tauto
    rw [hEq]
    exact (Nat.card_coe_set_eq (C : Set X)).symm
  rw [hset, hra, hrc]
  exact fixedFreeCount_card_eq_mul_relIndex hCaQ hCcQ hprod'

private theorem fixedFreeCount_card_Q_eq_centralizer_mul_sq (hS : Setup X D)
    {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup 2 Q) {m : ℕ}
    (hm : ∀ d ∈ D, ((fun y => y * d * y⁻¹) '' (Q : Set X)).ncard = m)
    (hgen : ∀ a ∈ D, ∀ c ∈ D, ¬ Commute a c →
      Subgroup.closure (insert a {f | f ∈ D ∧ Commute f c}) = ⊤)
    {a c : X} (ha : a ∈ D) (hc : c ∈ D) (hac : ¬ Commute a c) :
    Nat.card Q = Nat.card (fixedFreeCount_CQ Q (a * c)) * (m * m) := by
  classical
  let S : Set X := {y | y ∈ Q ∧ Commute y a ∧ Commute y c}
  have h := card_eq_ncard_inter_centralizer_mul hS hQ ha hc hac (hgen a ha c hc hac)
  rw [hm a ha, hm c hc] at h
  have hset : S = (fixedFreeCount_CQ Q (a * c) : Set X) := by
    ext y
    constructor
    · rintro ⟨hyQ, hya, hyc⟩
      exact ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr (hya.mul_right hyc).eq⟩
    · rintro ⟨hyQ, hyac⟩
      have hyac' : Commute y (a * c) := Subgroup.mem_centralizer_singleton_iff.mp hyac
      obtain ⟨hya, hyc⟩ :=
        (commute_iff_of_mem hS.oddT hS.normal hQ ha hc hac hyQ).mp hyac'
      exact ⟨hyQ, hya, hyc⟩
  have hSn : S.ncard = Nat.card (fixedFreeCount_CQ Q (a * c)) := by
    rw [hset]
    exact (Nat.card_coe_set_eq (fixedFreeCount_CQ Q (a * c) : Set X)).symm
  rw [hSn] at h
  exact h

private theorem fixedFreeCount_conj_pow (hS : Setup X D) {a b : X} (ha : a ∈ D)
    (hb : b ∈ D) : ∀ j : ℕ, a * (a * b) ^ j * a = ((a * b) ^ j)⁻¹ := by
  have haxa : a * (a * b) * a = (a * b)⁻¹ := by
    calc a * (a * b) * a = b * a := by
          rw [← mul_assoc, hS.oddT.mul_self_eq_one ha, one_mul]
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, hS.oddT.inv_eq ha, hS.oddT.inv_eq hb]
  have hconj : MulAut.conj a (a * b) = (a * b)⁻¹ := by
    rw [MulAut.conj_apply, hS.oddT.inv_eq ha, haxa]
  intro j
  have h := map_pow (MulAut.conj a) (a * b) j
  rw [hconj, inv_pow] at h
  rw [MulAut.conj_apply, hS.oddT.inv_eq ha] at h
  exact h

private theorem fixedFreeCount_conj_mul_pow_mem (hS : Setup X D) {a b : X} (ha : a ∈ D)
    (hb : b ∈ D) (hab : ¬ Commute a b) :
    ∀ i : ℕ, a * (a * b) ^ i ∈ D := by
  set N := orderOf (a * b) with hN
  have hNodd : Odd N := by
    rw [hN]
    exact hS.oddT.odd_of_not_commute ha hb hab
  obtain ⟨t, ht⟩ := hNodd
  have hNm1 : N - 1 = 2 * t := by omega
  have hNpos : 0 < N := by rw [hN]; exact orderOf_pos (a * b)
  have hxN : (a * b) ^ N = 1 := by rw [hN]; exact pow_orderOf_eq_one (a * b)
  have hxNm1 : (a * b) ^ (N - 1) = (a * b)⁻¹ := by
    have h1 : (a * b) ^ (N - 1) * (a * b) = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ N), hxN]
    calc (a * b) ^ (N - 1) = ((a * b) ^ (N - 1) * (a * b)) * (a * b)⁻¹ := by group
      _ = 1 * (a * b)⁻¹ := by rw [h1]
      _ = (a * b)⁻¹ := one_mul _
  have hconjpow := fixedFreeCount_conj_pow hS ha hb
  intro i
  let j := i * t
  have h2j : 2 * j = i * (N - 1) := by rw [hNm1]; ring
  have hx2j : (a * b) ^ (2 * j) = ((a * b) ^ i)⁻¹ := by
    rw [h2j, mul_comm i (N - 1), pow_mul, hxNm1, inv_pow]
  have hxa : (a * b) ^ j * a = a * ((a * b) ^ j)⁻¹ := by
    calc (a * b) ^ j * a = (a * a) * (a * b) ^ j * a := by
          rw [hS.oddT.mul_self_eq_one ha, one_mul]
      _ = a * (a * (a * b) ^ j * a) := by group
      _ = a * ((a * b) ^ j)⁻¹ := by rw [hconjpow j]
  have hconj : (a * b) ^ j * a * ((a * b) ^ j)⁻¹ = a * (a * b) ^ i := by
    calc (a * b) ^ j * a * ((a * b) ^ j)⁻¹
        = (a * ((a * b) ^ j)⁻¹) * ((a * b) ^ j)⁻¹ := by rw [hxa]
      _ = a * (((a * b) ^ j)⁻¹ * ((a * b) ^ j)⁻¹) := by group
      _ = a * ((a * b) ^ (2 * j))⁻¹ := by
            congr 1
            rw [← pow_two, inv_pow, ← pow_mul, mul_comm j 2]
      _ = a * (a * b) ^ i := by rw [hx2j, inv_inv]
  have hmem : (a * b) ^ j * a * ((a * b) ^ j)⁻¹ ∈ D := hS.conj_mem ((a * b) ^ j) ha
  rwa [hconj] at hmem

private theorem fixedFreeCount_not_commute_mul_pow (hS : Setup X D) {a b : X} (ha : a ∈ D)
    (hb : b ∈ D) (hab : ¬ Commute a b) :
    ∀ i : ℕ, (a * b) ^ i ≠ 1 → ¬ Commute a (a * (a * b) ^ i) := by
  have hbase := fixedFreeCount_conj_mul_pow_mem hS ha hb hab
  have hNodd : Odd (orderOf (a * b)) := hS.oddT.odd_of_not_commute ha hb hab
  intro i hi h
  have hcD : a * (a * b) ^ i ∈ D := hbase i
  have hxieq : a * (a * (a * b) ^ i) = (a * b) ^ i := by
    rw [← mul_assoc, hS.oddT.mul_self_eq_one ha, one_mul]
  have hsq : ((a * b) ^ i) * ((a * b) ^ i) = 1 := by
    have h1 : (a * (a * (a * b) ^ i)) * (a * (a * (a * b) ^ i)) = 1 := by
      calc (a * (a * (a * b) ^ i)) * (a * (a * (a * b) ^ i))
          = a * ((a * (a * b) ^ i) * a) * (a * (a * b) ^ i) := by group
        _ = a * (a * (a * (a * b) ^ i)) * (a * (a * b) ^ i) := by rw [h.eq]
        _ = ((a * a) * (a * (a * b) ^ i)) * (a * (a * b) ^ i) := by group
        _ = (a * (a * b) ^ i) * (a * (a * b) ^ i) := by
              rw [hS.oddT.mul_self_eq_one ha, one_mul]
        _ = 1 := hS.oddT.mul_self_eq_one hcD
    rwa [hxieq] at h1
  have hdvd2 : orderOf ((a * b) ^ i) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hodd : Odd (orderOf ((a * b) ^ i)) := hNodd.of_dvd_nat (orderOf_pow_dvd i)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
  · exact hi (orderOf_eq_one_iff.mp h1)
  · rw [h1] at hodd
    exact absurd hodd (by decide)

private theorem fixedFreeCount_CQ_pow_eq (hS : Setup X D) {Q : Subgroup X} [Q.Normal]
    (hQ : IsPGroup 2 Q) {m : ℕ}
    (hm : ∀ d ∈ D, ((fun y => y * d * y⁻¹) '' (Q : Set X)).ncard = m)
    (hgen : ∀ a ∈ D, ∀ c ∈ D, ¬ Commute a c →
      Subgroup.closure (insert a {f | f ∈ D ∧ Commute f c}) = ⊤)
    {a b : X} (ha : a ∈ D) (hb : b ∈ D) (hab : ¬ Commute a b) :
    ∀ i : ℕ, (a * b) ^ i ≠ 1 →
      fixedFreeCount_CQ Q ((a * b) ^ i) = fixedFreeCount_CQ Q (a * b) := by
  have hm_pos : 0 < m := by
    have hmem : a ∈ ((fun y => y * a * y⁻¹) '' (Q : Set X)) := ⟨1, Q.one_mem, by simp⟩
    rw [← hm a ha]
    exact Set.Nonempty.ncard_pos (Set.toFinite _) ⟨a, hmem⟩
  intro i hi
  have hc := fixedFreeCount_conj_mul_pow_mem hS ha hb hab i
  have hnc := fixedFreeCount_not_commute_mul_pow hS ha hb hab i hi
  have h1 := fixedFreeCount_card_Q_eq_centralizer_mul_sq hS hQ hm hgen ha hc hnc
  have h2 := fixedFreeCount_card_Q_eq_centralizer_mul_sq hS hQ hm hgen ha hb hab
  have hx : a * (a * (a * b) ^ i) = (a * b) ^ i := by
    rw [← mul_assoc, hS.oddT.mul_self_eq_one ha, one_mul]
  rw [hx] at h1
  have hpos : 0 < m * m := Nat.mul_pos hm_pos hm_pos
  have hcard : Nat.card (fixedFreeCount_CQ Q ((a * b) ^ i)) =
      Nat.card (fixedFreeCount_CQ Q (a * b)) := by
    rw [h2] at h1
    exact (Nat.mul_right_cancel hpos h1).symm
  have hle : fixedFreeCount_CQ Q (a * b) ≤ fixedFreeCount_CQ Q ((a * b) ^ i) := by
    intro y hy
    rw [fixedFreeCount_mem_CQ] at hy ⊢
    exact ⟨hy.1, hy.2.pow_right i⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

private instance fixedFreeCount_conjAction (Q : Subgroup X) [Q.Normal] (x : X) :
    MulAction (Subgroup.zpowers x) {y : X // y ∈ Q ∧ ¬ Commute y x} :=
  { smul := fun r y => ⟨(r : X) * (y : X) * (r : X)⁻¹, by
      refine ⟨?_, ?_⟩
      · exact (inferInstance : Q.Normal).conj_mem (y : X) y.2.1 (r : X)
      · intro hcy
        have hcomm_rx : Commute (r : X) x := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp r.2
          rw [← hk]
          exact (Commute.refl x).zpow_left k
        have hxr : (r : X) * x * (r : X)⁻¹ = x := by
          rw [hcomm_rx.eq]
          group
        have hcy' : Commute ((r : X) * (y : X) * (r : X)⁻¹) ((r : X) * x * (r : X)⁻¹) := by
          rwa [hxr]
        exact y.2.2 ((Commute.conj_iff (r : X)).mp hcy')⟩
    one_smul := by
      intro y
      apply Subtype.ext
      change (1 : X) * (y : X) * (1 : X)⁻¹ = (y : X)
      group
    mul_smul := by
      intro r s y
      apply Subtype.ext
      change ((r * s : Subgroup.zpowers x) : X) * (y : X) *
          ((r * s : Subgroup.zpowers x) : X)⁻¹ =
        (r : X) * ((s : X) * (y : X) * (s : X)⁻¹) * (r : X)⁻¹
      rw [Subgroup.coe_mul]
      group }

private theorem fixedFreeCount_stabilizer_eq_bot {Q : Subgroup X} [Q.Normal] {x : X}
    (hCQ : ∀ i : ℕ, x ^ i ≠ 1 → fixedFreeCount_CQ Q (x ^ i) = fixedFreeCount_CQ Q x) :
    ∀ y : {y : X // y ∈ Q ∧ ¬ Commute y x},
      MulAction.stabilizer (Subgroup.zpowers x) y = ⊥ := by
  classical
  intro y
  rw [eq_bot_iff]
  intro r hr
  by_contra hr1
  have hry : (r : X) * (y : X) * (r : X)⁻¹ = (y : X) := by
    have h := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hr)
    change (r : X) * (y : X) * (r : X)⁻¹ = (y : X) at h
    exact h
  have hcomm : Commute (r : X) (y : X) := by
    rw [Commute]
    calc (r : X) * (y : X) = ((r : X) * (y : X) * (r : X)⁻¹) * (r : X) := by group
      _ = (y : X) * (r : X) := by rw [hry]
  have hr_mem : (r : X) ∈ (Finset.range (orderOf x)).image (fun n => x ^ n) :=
    (isOfFinOrder_of_finite x).mem_zpowers_iff_mem_range_orderOf.mp r.2
  obtain ⟨n, hnlt, hnr⟩ := Finset.mem_image.mp hr_mem
  rw [Finset.mem_range] at hnlt
  have hn0 : n ≠ 0 := by
    intro hn
    apply hr1
    apply Subtype.ext
    rw [← hnr, hn, pow_zero]
    rfl
  have hxnne : x ^ n ≠ 1 := by
    intro hx1
    have hdvd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hx1
    have hle : orderOf x ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    omega
  have hCQn := hCQ n hxnne
  have hy_mem : (y : X) ∈ fixedFreeCount_CQ Q (x ^ n) := by
    refine ⟨y.2.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [hnr]; exact hcomm.symm.eq)
  rw [hCQn] at hy_mem
  exact y.2.2 (Subgroup.mem_centralizer_singleton_iff.mp hy_mem.2)

private lemma fixedFreeCount_natCard_compl {Q : Subgroup X} [Q.Normal] (x : X) :
    Nat.card {y : X // y ∈ Q ∧ ¬ Commute y x} =
      Nat.card Q - Nat.card (fixedFreeCount_CQ Q x) := by
  classical
  let NS := {y : X // y ∈ Q ∧ ¬ Commute y x}
  let S : Set X := (Q : Set X) \ (fixedFreeCount_CQ Q x : Set X)
  have hsub : (fixedFreeCount_CQ Q x : Set X) ⊆ (Q : Set X) := by
    intro y hy
    exact (fixedFreeCount_mem_CQ.mp hy).1
  have hcardS : Nat.card NS = S.ncard := by
    rw [← Nat.card_coe_set_eq S]
    refine Nat.card_congr ?_
    refine
      { toFun := fun y => ⟨y.1, ?_⟩
        invFun := fun y => ⟨y.1, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
    · exact ⟨y.2.1, fun h => y.2.2 (fixedFreeCount_mem_CQ.mp h).2⟩
    · exact ⟨y.2.1, fun hc => y.2.2 (fixedFreeCount_mem_CQ.mpr ⟨y.2.1, hc⟩)⟩
  have hQn : Nat.card Q = (Q : Set X).ncard := (Nat.card_coe_set_eq (Q : Set X)).symm
  have hCn : Nat.card (fixedFreeCount_CQ Q x) =
      (fixedFreeCount_CQ Q x : Set X).ncard :=
    (Nat.card_coe_set_eq (fixedFreeCount_CQ Q x : Set X)).symm
  change Nat.card NS = Nat.card Q - Nat.card (fixedFreeCount_CQ Q x)
  calc Nat.card NS = S.ncard := hcardS
    _ = (Q : Set X).ncard - (fixedFreeCount_CQ Q x : Set X).ncard := Set.ncard_sdiff hsub
    _ = Nat.card Q - Nat.card (fixedFreeCount_CQ Q x) := by rw [← hQn, ← hCn]

private theorem fixedFreeCount_dvd_natCard_sub {Q : Subgroup X} [Q.Normal] {x : X}
    (hfree : ∀ y : {y : X // y ∈ Q ∧ ¬ Commute y x},
      MulAction.stabilizer (Subgroup.zpowers x) y = ⊥) :
    orderOf x ∣ Nat.card Q - Nat.card (fixedFreeCount_CQ Q x) := by
  classical
  let NS := {y : X // y ∈ Q ∧ ¬ Commute y x}
  have hcard : Nat.card NS =
      Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers x) NS)) *
        Nat.card (Subgroup.zpowers x) := by
    calc Nat.card NS = Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers x) NS) ×
          Subgroup.zpowers x) :=
            Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd
              (G := Subgroup.zpowers x) (X := NS) hfree)
      _ = Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers x) NS)) *
            Nat.card (Subgroup.zpowers x) := Nat.card_prod _ _
  have hdvd : orderOf x ∣ Nat.card NS := by
    rw [hcard, Nat.card_zpowers]
    exact dvd_mul_left _ _
  have hNS : Nat.card NS = Nat.card Q - Nat.card (fixedFreeCount_CQ Q x) :=
    fixedFreeCount_natCard_compl (Q := Q) x
  rwa [hNS] at hdvd

theorem orderOf_mul_dvd_sq_sub_one (hS : Setup X D) {Q : Subgroup X} [Q.Normal]
    (hQ : IsPGroup 2 Q) {m : ℕ}
    (hm : ∀ d ∈ D, ((fun y => y * d * y⁻¹) '' (Q : Set X)).ncard = m)
    (hgen : ∀ a ∈ D, ∀ c ∈ D, ¬ Commute a c →
      Subgroup.closure (insert a {f | f ∈ D ∧ Commute f c}) = ⊤)
    {a b : X} (ha : a ∈ D) (hb : b ∈ D) (hab : ¬ Commute a b) :
    orderOf (a * b) ∣ m ^ 2 - 1 := by
  classical
  have hCQpow := fixedFreeCount_CQ_pow_eq hS hQ hm hgen ha hb hab
  have hfree := fixedFreeCount_stabilizer_eq_bot hCQpow
  have hdvdS := fixedFreeCount_dvd_natCard_sub (Q := Q) (x := a * b) hfree
  have hQx := fixedFreeCount_card_Q_eq_centralizer_mul_sq hS hQ hm hgen ha hb hab
  have hsub : Nat.card (fixedFreeCount_CQ Q (a * b)) * (m * m) -
      Nat.card (fixedFreeCount_CQ Q (a * b)) =
      Nat.card (fixedFreeCount_CQ Q (a * b)) * (m * m - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  have hdvd : orderOf (a * b) ∣ Nat.card (fixedFreeCount_CQ Q (a * b)) * (m * m - 1) := by
    rw [hQx] at hdvdS
    rwa [hsub] at hdvdS
  have hodd : Odd (orderOf (a * b)) := hS.oddT.odd_of_not_commute ha hb hab
  have hCQ2 : IsPGroup 2 (fixedFreeCount_CQ Q (a * b)) := hQ.to_le inf_le_left
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hCQ2
  have hcop : Nat.Coprime (orderOf (a * b)) (Nat.card (fixedFreeCount_CQ Q (a * b))) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Odd.coprime_two_right hodd)
  have hdvdm : orderOf (a * b) ∣ m * m - 1 :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop (by rwa [mul_comm] at hdvd)
  simpa [pow_two] using hdvdm

end CFSG.OddTranspositions.PartFour
