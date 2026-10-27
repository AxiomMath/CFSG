module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrKcdA5
public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Three
import CFSG.RankThree.PartTwo.Sec16.Item166CtrKcdB1
import CFSG.RankThree.PartTwo.Sec16.Item166ThetaDich
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.NormalizerInfCentralizer
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitPerf
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private theorem inf_centralizer_eq_inf_centralizer_of_mem_pair {H : Subgroup G} {c d b : G}
    (hHc : H ≤ Subgroup.centralizer ({c} : Set G)) (hcd : Commute c d) (hd3 : d ^ 3 = 1)
    (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) :
    H ⊓ Subgroup.centralizer ({b} : Set G) =
      H ⊓ Subgroup.centralizer ({d} : Set G) := by
  rcases Set.mem_insert_iff.mp hb with hb | hb
  · subst b
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxb⟩
      refine ⟨hx, ?_⟩
      have hxc : Commute x c := Subgroup.mem_centralizer_singleton_iff.mp (hHc hx)
      have hxb' : Commute x (c * d) := hxb
      have hxd : Commute x d := by
        have h := hxb'.mul_right hxc.inv_right
        rwa [show (c * d) * c⁻¹ = d by
          rw [hcd.eq, mul_assoc, mul_inv_cancel, mul_one]] at h
      exact hxd.eq
    · rintro ⟨hx, hxd⟩
      refine ⟨hx, ?_⟩
      have hxc : Commute x c := Subgroup.mem_centralizer_singleton_iff.mp (hHc hx)
      have hxd' : Commute x d := hxd
      exact (hxc.mul_right hxd').eq
  · rw [Set.mem_singleton_iff.mp hb]
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxb⟩
      refine ⟨hx, ?_⟩
      have hxc : Commute x c := Subgroup.mem_centralizer_singleton_iff.mp (hHc hx)
      have hxb' : Commute x (c * d ^ 2) := hxb
      have hxd2 : Commute x (d ^ 2) := by
        have h := hxb'.mul_right hxc.inv_right
        rwa [show (c * d ^ 2) * c⁻¹ = d ^ 2 by
          rw [show c * d ^ 2 = d ^ 2 * c from (hcd.pow_right 2).eq,
            mul_assoc, mul_inv_cancel, mul_one]] at h
      have hd : (d ^ 2) ^ 2 = d := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hd3, one_mul]
      have h := hxd2.pow_right 2
      rwa [hd] at h
    · rintro ⟨hx, hxd⟩
      refine ⟨hx, ?_⟩
      have hxc : Commute x c := Subgroup.mem_centralizer_singleton_iff.mp (hHc hx)
      have hxd' : Commute x d := hxd
      exact (hxc.mul_right (hxd'.pow_right 2)).eq

private lemma exists_mul_mem_of_mul_conj_eq {Q : Subgroup G} {q b : G} (hq : q ∈ Q)
    (hb : b ∈ Subgroup.normalizer (Q : Set G)) :
    ∃ c ∈ Q, q * b * q⁻¹ = b * c := by
  refine ⟨b⁻¹ * q * b * q⁻¹, ?_, by group⟩
  have hb' : b⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).inv_mem hb
  have h1 : b⁻¹ * q * b ∈ Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp hb' q).mp hq
  exact Q.mul_mem h1 (Q.inv_mem hq)

private theorem commutator_mem_sup_commutator_map_conj {L Q : Subgroup G} {q : G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hq : q ∈ Q) {a b : G}
    (ha : a ∈ L) (hb : b ∈ L) :
    ⁅a, b⁆ ∈ ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ ⊔ Q := by
  obtain ⟨c, hcQ, hbc⟩ := exists_mul_mem_of_mul_conj_eq hq (hLQ hb)
  have hmem : ⁅a, b * c⁆ ∈ ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ := by
    refine Subgroup.commutator_mem_commutator ha ?_
    rw [← hbc]
    exact Subgroup.mem_map_of_mem (MulAut.conj q).toMonoidHom hb
  have hac : ⁅a, c⁆ ∈ Q := by
    have h : a * c * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ ha) c).mp hcQ
    rw [commutatorElement_def]
    exact Q.mul_mem h (Q.inv_mem hcQ)
  have hQ : b * ⁅a, c⁆ * b⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hLQ hb) _).mp hac
  rw [show ⁅a, b⁆ = ⁅a, b * c⁆ * (b * ⁅a, c⁆ * b⁻¹)⁻¹ by
    rw [CFSG.commutator_mul_right]
    group]
  exact Subgroup.mul_mem_sup hmem (Q.inv_mem hQ)

private theorem le_sup_commutator_map_conj_of_le_normalizer {L Q : Subgroup G} {q : G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hL : ⁅L, L⁆ = L) (hq : q ∈ Q) :
    L ≤ ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ ⊔ Q := by
  have hle : ⁅L, L⁆ ≤ ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ ⊔ Q := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact commutator_mem_sup_commutator_map_conj hLQ hq ha hb
  rwa [hL] at hle

private theorem commutator_map_conj_le_sup {L Q : Subgroup G} {q : G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hq : q ∈ Q) :
    ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ ≤ L ⊔ Q := by
  rw [Subgroup.commutator_le]
  intro a ha x hx
  obtain ⟨b, hb, rfl⟩ := hx
  obtain ⟨c, hcQ, hbc⟩ := exists_mul_mem_of_mul_conj_eq hq (hLQ hb)
  have hac : ⁅a, c⁆ ∈ Q := by
    have h : a * c * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ ha) c).mp hcQ
    rw [commutatorElement_def]
    exact Q.mul_mem h (Q.inv_mem hcQ)
  have hQ : b * ⁅a, c⁆ * b⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hLQ hb) _).mp hac
  change ⁅a, q * b * q⁻¹⁆ ∈ L ⊔ Q
  rw [hbc, show ⁅a, b * c⁆ = ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ from
    CFSG.commutator_mul_right a b c,
    show ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) by group]
  exact Subgroup.mul_mem_sup
    (Subgroup.commutator_le_self L (Subgroup.commutator_mem_commutator ha hb)) hQ

private theorem conj_mem_inf_of_mul_mem_centralizer {L Q : Subgroup G} {b l q x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxQ : x ∈ Subgroup.normalizer (Q : Set G)) (hl : l ∈ L) (hq : q ∈ Q)
    (hy : (l * q) * b = b * (l * q)) (hx : x ∈ Subgroup.zpowers b) :
    l⁻¹ * (x * l * x⁻¹) ∈ L ⊓ Q := by
  have hyx : Commute (l * q) x := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hyb : Commute (l * q) b := hy
    exact hyb.zpow_right k
  refine ⟨?_, ?_⟩
  · have hxl : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL l).mp hl
    exact L.mul_mem (L.inv_mem hl) hxl
  · have hxq : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxQ q).mp hq
    have hqx : q * x * q⁻¹ * x⁻¹ ∈ Q := by
      have e : q * x * q⁻¹ * x⁻¹ = q * (x * q * x⁻¹)⁻¹ := by group
      rw [e]
      exact Q.mul_mem hq (Q.inv_mem hxq)
    have hyinv : (l * q)⁻¹ * x = x * (l * q)⁻¹ := hyx.inv_left
    have e : l⁻¹ * (x * l * x⁻¹) = q * x * q⁻¹ * x⁻¹ := by
      have hl' : l = (l * q) * q⁻¹ := by group
      have h1 : l⁻¹ * (x * l * x⁻¹) =
          q * ((l * q)⁻¹ * x) * (l * q) * q⁻¹ * x⁻¹ := by
        rw [hl']
        group
      have h2 : q * ((l * q)⁻¹ * x) * (l * q) * q⁻¹ * x⁻¹ =
          q * (x * (l * q)⁻¹) * (l * q) * q⁻¹ * x⁻¹ := by rw [hyinv]
      have h3 : q * (x * (l * q)⁻¹) * (l * q) * q⁻¹ * x⁻¹ =
          q * x * q⁻¹ * x⁻¹ := by group
      exact h1.trans (h2.trans h3)
    rw [e]
    exact hqx

private theorem le_sup_centralizerPCore_of_mem_centralizer (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) {d : G} (hdA : d ∈ A) {b : G}
    (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) :
    Y₀ ⊓ Subgroup.centralizer ({b} : Set G) ≤
      (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
        (CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G)) := by
  classical
  have hD : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hcA : c ∈ A := hD.mem_A
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1
  have hcd : Commute c d := hD.commute hcA hdA
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hbA : b ∈ A := by
    rcases Set.mem_insert_iff.mp hb with hb' | hb'
    · rw [hb']
      exact A.mul_mem hcA hdA
    · rw [Set.mem_singleton_iff.mp hb']
      exact A.mul_mem hcA (A.pow_mem hdA 2)
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have hLb : L ⊓ Subgroup.centralizer ({b} : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) :=
    inf_centralizer_eq_inf_centralizer_of_mem_pair hLc hcd hd3 hb
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 G A c L h.toSec15R hJ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right h.le_y0] at h1
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 Y₀ with hQ
  set Qb : Subgroup G := Q ⊓ Subgroup.centralizer ({b} : Set G) with hQb
  have hYle : Y₀ ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := h.le_y0.trans hYle
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    h.mem_y0Star.prop.1.1.2.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hPQ : Subgroup.zpowers b ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (hAQ hbA)
  have hPL : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (h.mem_lA.2.1 hbA)
  have hP : IsPGroup 3 (Subgroup.zpowers b) := Sec6.isPGroup_zpowers_of_pow_three hb3
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLQp : IsPGroup 2 ((L ⊓ Q : Subgroup G)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀).to_le
      (inf_le_right : L ⊓ Q ≤ Q)
  have hN3 : ¬ 3 ∣ Nat.card ((L ⊓ Q : Subgroup G)) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hLQp
      Nat.prime_three (by norm_num)
  have hBN : Subgroup.zpowers b ≤ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hPL hx, hPQ hx⟩
  intro y hy
  have hyY : y ∈ (L : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L Q hLQ, ← hY]
    exact hy.1
  obtain ⟨l, hl, q, hq, rfl⟩ := hyY
  have hk : ∀ x ∈ Subgroup.zpowers b, l⁻¹ * (x * l * x⁻¹) ∈ L ⊓ Q := by
    intro x hx
    exact conj_mem_inf_of_mul_mem_centralizer (hPL hx) (hPQ hx) hl hq
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2) hx
  obtain ⟨y', hy'l, hy'C⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Step199Proof.exists_fixed_mem_coset hP hN3 hBN hk
  have hy'L : y' ∈ L := by
    have h : y' = l * (l⁻¹ * y') := by group
    rw [h]
    exact L.mul_mem hl hy'l.1
  have hy'Cb : y' ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hy'C b (Subgroup.mem_zpowers b)).symm
  have hq'Q : y'⁻¹ * (l * q) ∈ Q := by
    have h : y'⁻¹ * (l * q) = (l⁻¹ * y')⁻¹ * q := by group
    rw [h]
    exact Q.mul_mem (Q.inv_mem hy'l.2) hq
  have hq'Cb : y'⁻¹ * (l * q) ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : Commute (l * q) b := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have h2 : Commute y' b := Subgroup.mem_centralizer_singleton_iff.mp hy'Cb
    exact (h2.inv_left.mul_left h1).eq
  have hy'M : y' ∈ L ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [← hLb]
    exact ⟨hy'L, hy'Cb⟩
  have hdecomp : l * q = y' * (y'⁻¹ * (l * q)) := by group
  change l * q ∈ (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ Qb
  rw [hdecomp]
  exact Subgroup.mul_mem_sup hy'M (Subgroup.mem_inf.mpr ⟨hq'Q, hq'Cb⟩)

private theorem le_of_commutator_map_conj_le_theta {LB Qb X θX : Subgroup G} {q : G}
    (hLBcomm : ⁅LB, LB⁆ = LB) (hLBX : LB ≤ X)
    (hLBQb : LB ≤ Subgroup.normalizer (Qb : Set G))
    (hcomm : ⁅X, X.map (MulAut.conj q).toMonoidHom⁆ ≤ θX)
    (hθsolv : Group.IsSolvable ↥θX) (hq : q ∈ Qb) : LB ≤ Qb := by
  have hN0θ : ⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆ ≤ θX :=
    (Subgroup.commutator_mono hLBX
      (Subgroup.map_mono (f := (MulAut.conj q).toMonoidHom) hLBX)).trans hcomm
  have hN0solv : Group.IsSolvable ↥(⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hN0θ) (Subgroup.inclusion_injective hN0θ)
  have hN0leK : ⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆ ≤ LB ⊔ Qb :=
    commutator_map_conj_le_sup hLBQb hq
  have hLBle : LB ≤ ⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆ ⊔ Qb :=
    le_sup_commutator_map_conj_of_le_normalizer hLBQb hLBcomm hq
  set K : Subgroup G := LB ⊔ Qb with hK
  have hLBK : LB ≤ K := le_sup_left
  have hQbK : Qb ≤ K := le_sup_right
  have hN0K : ⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆ ≤ K := hN0leK
  have hQbNormK : (Qb.subgroupOf K).Normal := by
    rw [hK]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hLBQb
  haveI : (Qb.subgroupOf K).Normal := hQbNormK
  have hHK : ⁅LB.subgroupOf K, LB.subgroupOf K⁆ = LB.subgroupOf K := by
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq hLBK hLBK, hLBcomm]
  have hN0Ksolv : Group.IsSolvable
      ↥(⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆.subgroupOf K) := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hN0K).toMonoidHom) ?_
    exact (Subgroup.subgroupOfEquivOfLe hN0K).injective
  have hHDP : LB.subgroupOf K ≤
      Qb.subgroupOf K ⊔ (⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆).subgroupOf K := by
    have hsub : LB.subgroupOf K ≤
        (⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆ ⊔ Qb).subgroupOf K :=
      Subgroup.subgroupOf_mono K hLBle
    rw [Subgroup.subgroupOf_sup hN0K hQbK] at hsub
    simpa [sup_comm] using hsub
  have hcontra := CFSG.OddStandard.HigherRank.YamadaG23.lit_perfect_le_of_le_sup_solvable
    (H := LB.subgroupOf K) (D := Qb.subgroupOf K)
    (P := (⁅LB, LB.map (MulAut.conj q).toMonoidHom⁆).subgroupOf K) hHK hN0Ksolv hHDP
  intro x hx
  have hxK : x ∈ K := hLBK hx
  have hxQ : (⟨x, hxK⟩ : ↥K) ∈ Qb.subgroupOf K :=
    hcontra (Subgroup.mem_subgroupOf.mpr hx)
  exact Subgroup.mem_subgroupOf.mp hxQ

private theorem centralizerPCore_le_normalizer (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {b : G}
    (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 b)
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
  classical
  have hD : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hcA : c ∈ A := hD.mem_A
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1
  have hcd : Commute c d := hD.commute hcA hdA
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hbA : b ∈ A := by
    rcases Set.mem_insert_iff.mp hb with hb' | hb'
    · rw [hb']
      exact A.mul_mem hcA hdA
    · rw [Set.mem_singleton_iff.mp hb']
      exact A.mul_mem hcA (A.pow_mem hdA 2)
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have hLb : L ⊓ Subgroup.centralizer ({b} : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) :=
    inf_centralizer_eq_inf_centralizer_of_mem_pair hLc hcd hd3 hb
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 Y₀ with hQ
  set Qb : Subgroup G := Q ⊓ Subgroup.centralizer ({b} : Set G) with hQb
  set LB : Subgroup G := lB A (Subgroup.closure {c, d}) with hLB
  set θX : Subgroup G := inSubgroup (aschbacherSolvableCore 3) X with hθX
  have hθsolv : Group.IsSolvable ↥θX :=
    CFSG.RankThree.PartTwo.Sec11.isSolvable_inSubgroup_theta X
  have hLBres : LB = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [hLB, lB_closure_eq_residual h hJ hdA hd1 hdc]
  have hLBperf : Group.IsPerfect ↥LB := by
    rw [hLBres]
    exact Item148HJ.residual_isPerfect L d
  have hLBcomm : ⁅LB, LB⁆ = LB := Sec6.commutator_self_eq_of_isPerfect hLBperf
  have hLBX : LB ≤ X := by
    rw [hXL, hθX]
    exact le_sup_left
  have hLBleL : LB ≤ L := by
    rw [hLBres]
    exact Item148HJ.residual_le L d
  have hLBQ : LB ≤ Subgroup.normalizer (Q : Set G) :=
    hLBleL.trans (h.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀))
  have hbClos : b ∈ Subgroup.closure ({c, d} : Set G) := by
    rcases Set.mem_insert_iff.mp hb with hb' | hb'
    · rw [hb']
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert c _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d)))
    · rw [Set.mem_singleton_iff.mp hb']
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert c _))
        (Subgroup.pow_mem _ (Subgroup.subset_closure
          (Set.mem_insert_of_mem c (Set.mem_singleton d))) 2)
  have hLBCb : LB ≤ Subgroup.centralizer ({b} : Set G) :=
    (lB_le_centralizer A (Subgroup.closure {c, d})).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbClos))
  have hLBCz : LB ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rwa [CFSG.centralizer_zpowers_eq_centralizer_singleton]
  have hLBNCb : LB ≤ Subgroup.normalizer
      (Subgroup.centralizer ({b} : Set G) : Set G) := by
    have h2 : LB ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
      hLBCz.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers b : Set G))
    have h3 : LB ≤ Subgroup.normalizer
        (Subgroup.centralizer (Subgroup.zpowers b : Set G) : Set G) :=
      h2.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (Subgroup.zpowers b))
    rwa [CFSG.centralizer_zpowers_eq_centralizer_singleton] at h3
  have hLBQb : LB ≤ Subgroup.normalizer (Qb : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hLBQ hx, hLBNCb hx⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀
  have hQb2 : IsPGroup 2 Qb := hQ2.to_le inf_le_left
  have hQbsolv : Group.IsSolvable ↥Qb := @IsNilpotent.to_isSolvable ↥Qb _ hQb2.isNilpotent
  intro q hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hqQ : q ∈ Q := (Subgroup.mem_inf.mp hq).1
  have hqC : q ∈ Subgroup.centralizer ({b} : Set G) := (Subgroup.mem_inf.mp hq).2
  have hXq : X.map (MulAut.conj q).toMonoidHom ∈ thetaComponentsAt 3 b :=
    CFSG.RankThree.PartTwo.Sec6.map_conj_mem_thetaComponentsAt hqC hX
  have hXIn : X ∈ thetaComponentsIn (Subgroup.centralizer ({b} : Set G)) := by
    rwa [← thetaComponentsAt_eq_thetaComponentsIn]
  have hXqIn : X.map (MulAut.conj q).toMonoidHom ∈
      thetaComponentsIn (Subgroup.centralizer ({b} : Set G)) := by
    rwa [← thetaComponentsAt_eq_thetaComponentsIn]
  rcases dichotomy_of_mem_thetaComponentsIn hXIn hXqIn with hle | ⟨-, hcomm⟩
  · have hcard : Nat.card (X.map (MulAut.conj q).toMonoidHom) = Nat.card X :=
      Subgroup.card_map_of_injective (MulAut.conj q).injective
    have heq : X = X.map (MulAut.conj q).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
    exact hne heq.symm
  · have hLBQbEq : LB ≤ Qb :=
      le_of_commutator_map_conj_le_theta hLBcomm hLBX hLBQb hcomm hθsolv hq
    have hdLB : d ∈ LB := by
      rw [hLB]
      exact mem_lB_closure h hJ hdA hd1 hdc
    have hdQbNot : d ∉ Qb := by
      have hdo : orderOf d = 3 := orderOf_eq_prime (by simpa using hd3) hd1
      intro hdQb
      have hdvd : 3 ∣ Nat.card Qb := by
        rw [← hdo]
        exact Subgroup.orderOf_dvd_natCard Qb hdQb
      exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hQb2 Nat.prime_three (by norm_num) hdvd
    exact hdQbNot (hLBQbEq hdLB)

private theorem le_sup_pCoreOf_of_isPerfect (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    {b : G} (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) {I : Subgroup G} (hIY : I ≤ Y₀)
    (hIb : I ≤ Subgroup.centralizer ({b} : Set G)) (hI : Group.IsPerfect ↥I) :
    I ≤ lB A (Subgroup.closure {c, d}) ⊔
      (CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G)) := by
  classical
  have hD : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hcA : c ∈ A := hD.mem_A
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1
  have hcd : Commute c d := hD.commute hcA hdA
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hLb : L ⊓ Subgroup.centralizer ({b} : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) :=
    inf_centralizer_eq_inf_centralizer_of_mem_pair hLc hcd hd3 hb
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 Y₀ with hQ
  set Qb : Subgroup G := Q ⊓ Subgroup.centralizer ({b} : Set G) with hQb
  have hMQ : L ⊓ Subgroup.centralizer ({d} : Set G) ≤
      Subgroup.normalizer (Q : Set G) :=
    (inf_le_left.trans h.le_y0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  have hMb : L ⊓ Subgroup.centralizer ({d} : Set G) ≤
      Subgroup.centralizer ({b} : Set G) := by
    rw [← hLb]
    exact inf_le_right
  have hMnorm : L ⊓ Subgroup.centralizer ({d} : Set G) ≤
      Subgroup.normalizer (Qb : Set G) := by
    intro x hx
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := hMQ hx
    have hxzb : x ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
      rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
      exact hMb hx
    have hxzN : x ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
      Subgroup.centralizer_le_normalizer (Subgroup.zpowers b : Set G) hxzb
    have := CFSG.GroupTheory.mem_normalizer_inf_centralizer
      (L := Subgroup.zpowers b) (Q := Q) hxzN hxQ
    simpa [hQb, CFSG.centralizer_zpowers_eq_centralizer_singleton] using this
  have hIle : I ≤ (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ Qb :=
    (le_inf hIY hIb).trans
      (le_sup_centralizerPCore_of_mem_centralizer h hJ h1523 hdA hb)
  have hres := Sec6.le_perfectResidual_sup (L := I)
    (X := L ⊓ Subgroup.centralizer ({d} : Set G)) (N := Qb) hI hMnorm hIle
  rwa [← lB_closure_eq_residual h hJ hdA hd1 hdc] at hres

private theorem le_of_isPerfect_of_le_sup_of_normal {X Q I : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer (X : Set G)) (hQsolv : Group.IsSolvable ↥Q)
    (hI : Group.IsPerfect ↥I) (hIXQ : I ≤ X ⊔ Q) : I ≤ X := by
  classical
  set K : Subgroup G := X ⊔ Q with hK
  have hXK : X ≤ K := le_sup_left
  have hQK : Q ≤ K := le_sup_right
  have hIK : I ≤ K := hIXQ
  have hIcomm : ⁅I, I⁆ = I := Sec6.commutator_self_eq_of_isPerfect hI
  have hHcomm : ⁅I.subgroupOf K, I.subgroupOf K⁆ = I.subgroupOf K := by
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq hIK hIK, hIcomm]
  have hXnormal : (X.subgroupOf K).Normal := by
    have h := Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := Q) (N := X) hQN
    rw [show Q ⊔ X = K by rw [sup_comm, ← hK]] at h
    exact h
  haveI : (X.subgroupOf K).Normal := hXnormal
  have hQsolvK : Group.IsSolvable ↥(Q.subgroupOf K) := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQK).toMonoidHom) ?_
    exact (Subgroup.subgroupOfEquivOfLe hQK).injective
  have hHDP : I.subgroupOf K ≤ X.subgroupOf K ⊔ Q.subgroupOf K := by
    have hsub : I.subgroupOf K ≤ (X ⊔ Q).subgroupOf K := Subgroup.subgroupOf_mono K hIXQ
    rwa [Subgroup.subgroupOf_sup hXK hQK] at hsub
  have hcontra := CFSG.OddStandard.HigherRank.YamadaG23.lit_perfect_le_of_le_sup_solvable
    (H := I.subgroupOf K) (D := X.subgroupOf K) (P := Q.subgroupOf K) hHcomm hQsolvK hHDP
  intro x hx
  have hxK : x ∈ K := hIK hx
  have hxX : (⟨x, hxK⟩ : ↥K) ∈ X.subgroupOf K :=
    hcontra (Subgroup.mem_subgroupOf.mpr hx)
  exact Subgroup.mem_subgroupOf.mp hxX

theorem le_of_isPerfect_of_le_centralizer (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    {b : G} (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 b)
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) X)
    {I : Subgroup G} (hIY : I ≤ Y₀) (hIb : I ≤ Subgroup.centralizer ({b} : Set G))
    (hI : Group.IsPerfect ↥I) : I ≤ X := by
  have hLBX : lB A (Subgroup.closure {c, d}) ≤ X := by
    rw [hXL]
    exact le_sup_left
  have hIQb : I ≤ lB A (Subgroup.closure {c, d}) ⊔
      (CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G)) :=
    le_sup_pCoreOf_of_isPerfect h hJ h1523 hdA hd1 hdc hb hIY hIb hI
  have hIXQ : I ≤ X ⊔ (CFSG.Open.pCoreOf 2 Y₀ ⊓
      Subgroup.centralizer ({b} : Set G)) := hIQb.trans (sup_le_sup hLBX le_rfl)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y₀) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀
  have hQb2 : IsPGroup 2
      ((CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G)) :=
    hQ2.to_le inf_le_left
  exact le_of_isPerfect_of_le_sup_of_normal
    (centralizerPCore_le_normalizer h hJ hdA hd1 hdc hb hX hXL)
    (@IsNilpotent.to_isSolvable _ _ hQb2.isNilpotent) hI hIXQ

theorem step166A5Data_of (h1523 : Item1523R) (hK3 : KFacts.KS166J2A5Three) :
    Step166A5Data := by
  intro G _ _ A c L Y₀ h hJ d hdA hd1 hdc b hb X hX hXL _ J hJY hJperf hJA5 hAJ
  obtain ⟨hIp, hIA5, hAI⟩ := residual_facts h hJ h1523 hK3 hJY hJperf hJA5 hAJ hdA hdc hb
  refine ⟨le_of_isPerfect_of_le_centralizer h hJ h1523 hdA hd1 hdc hb hX hXL ?_ ?_ hIp, hIp,
    hIA5, hAI⟩
  · exact (Subgroup.map_subtype_le _).trans (inf_le_left.trans hJY)
  · exact (Subgroup.map_subtype_le _).trans inf_le_right

end CFSG.RankThree.PartTwo.Sec16.Ctr166
