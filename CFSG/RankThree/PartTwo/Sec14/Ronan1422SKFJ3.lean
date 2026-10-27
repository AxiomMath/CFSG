module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFJ3S6
public import CFSG.RankThree.PartTwo.KFacts.K426J3
public import Certificates.Certificate142200
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open Equiv Equiv.Perm Subgroup

section J3

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Sporadic.Schreier CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.PartTwo.KFacts.K426

theorem evalW_mem_of_forall {m : ℕ} {G : Type*} [Group G] {H : Subgroup G} {g : Fin m → G}
    (hg : ∀ i, g i ∈ H) (w : List (Fin m × Bool)) : evalW g w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons x w ih =>
    rw [evalW_cons]
    obtain ⟨i, b⟩ := x
    cases b
    · exact H.mul_mem (H.inv_mem (hg i)) ih
    · exact H.mul_mem (hg i) ih

theorem centralizer_pow_two_eq_of_pow_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) :
    Subgroup.centralizer ({x ^ 2} : Set G) = Subgroup.centralizer {x} := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hx4 : (x ^ 2) ^ 2 = x := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hx, one_mul]
  constructor
  · intro h
    have h2 : Commute y ((x ^ 2) ^ 2) := (Commute.pow_right (Commute.symm (Commute.symm h)) 2)
    rw [hx4] at h2
    exact h2.eq
  · intro h
    exact (Commute.pow_right h 2).eq

@[expose] noncomputable def j3tU : Equiv.Perm (Fin 6156) := evalW j3tD j3tWu

@[expose] noncomputable def j3tV : Equiv.Perm (Fin 6156) := evalW j3tD j3tWv

@[expose] noncomputable def j3tB0 : Subgroup (Equiv.Perm (Fin 6156)) :=
  Subgroup.closure {j3tU, j3tV}


theorem j3t_norm_facts :
    j3tGPerm * j3tXA * j3tGPerm⁻¹ = j3tXA ^ 2 ∧ j3tU ^ 3 = 1 ∧ j3tU ≠ 1 ∧ j3tV ≠ 1 ∧
      j3tV ≠ j3tU ∧ j3tV ≠ j3tU ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (Certificates.certificate142200)
  have hd := j3t_derived_check.2.2.2.2
  simp only [detOK, Bool.and_eq_true] at hd
  have hvg : validA 6156 j3tG = true := hd.1.1.1
  have hx : Rep 6156 j3tReps[0]! j3tXA := rep_of_validA (j3tReps_spec (by norm_num)).1
  have hu : Rep 6156 (evalWA 6156 j3tDGens j3tWu) j3tU := rep_evalWA_j3tD j3tWu
  have hv : Rep 6156 (evalWA 6156 j3tDGens j3tWv) j3tV := rep_evalWA_j3tD j3tWv
  refine ⟨eq_of_eqA (rep_conjA hvg hx) (rep_powArr hx 2) h1,
    eq_of_eqA (rep_powArr hu 3) rep_idA h2, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [(eqA_iff hu rep_idA).2 h] at h3
    exact absurd h3 (by decide)
  · rw [(eqA_iff hv rep_idA).2 h] at h4
    exact absurd h4 (by decide)
  · rw [(eqA_iff hv hu).2 h] at h5
    exact absurd h5 (by decide)
  · rw [(eqA_iff hv (rep_powArr hu 2)).2 h] at h6
    exact absurd h6 (by decide)

theorem j3t_det' : j3tGPerm * j3tU * j3tGPerm⁻¹ = j3tV ∧
    j3tGPerm * j3tV * j3tGPerm⁻¹ = j3tU * j3tV ∧ j3tU * j3tV = j3tV * j3tU := by
  obtain ⟨h1, h2, h3⟩ := j3t_det
  rw [pow_one] at h2
  exact ⟨h1, h2, h3⟩

theorem conj_pow_four_of_det {G : Type*} [Group G] {g u v : G} (hu3 : u ^ 3 = 1)
    (hgu : g * u * g⁻¹ = v) (hgv : g * v * g⁻¹ = u * v) (hc : u * v = v * u) :
    g ^ 4 * u * (g ^ 4)⁻¹ = u⁻¹ ∧ g ^ 4 * v * (g ^ 4)⁻¹ = v⁻¹ := by
  have hv3 : v ^ 3 = 1 := by rw [← hgu, conj_pow, hu3]; group
  have hc2 : ∀ x : G, g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := fun x => by
    rw [sq, mul_inv_rev]
    simp only [mul_assoc]
  have hc4 : ∀ x : G, g ^ 4 * x * (g ^ 4)⁻¹ = g ^ 2 * (g ^ 2 * x * (g ^ 2)⁻¹) * (g ^ 2)⁻¹ :=
    fun x => by
      rw [show g ^ 4 = g ^ 2 * g ^ 2 by rw [← pow_add], mul_inv_rev]
      simp only [mul_assoc]
  have hmul : ∀ a b : G, g ^ 2 * (a * b) * (g ^ 2)⁻¹ =
      (g ^ 2 * a * (g ^ 2)⁻¹) * (g ^ 2 * b * (g ^ 2)⁻¹) := fun a b => by group
  have hnf : ∀ i j k l : ℕ, u ^ i * v ^ j * (u ^ k * v ^ l) = u ^ (i + k) * v ^ (j + l) := by
    intro i j k l
    have h1 : v ^ j * u ^ k = u ^ k * v ^ j := ((Commute.pow_pow (Commute.symm hc) j k)).eq
    calc u ^ i * v ^ j * (u ^ k * v ^ l) = u ^ i * (v ^ j * u ^ k) * v ^ l := by
          simp only [mul_assoc]
      _ = u ^ i * (u ^ k * v ^ j) * v ^ l := by rw [h1]
      _ = u ^ (i + k) * v ^ (j + l) := by rw [pow_add, pow_add]; simp only [mul_assoc]
  have h2u : g ^ 2 * u * (g ^ 2)⁻¹ = u * v := by rw [hc2, hgu, hgv]
  have h2v : g ^ 2 * v * (g ^ 2)⁻¹ = u * v ^ 2 := by
    rw [hc2, hgv, show g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) by group, hgu, hgv,
      ← mul_assoc, ← hc, mul_assoc, ← sq]
  constructor
  · rw [hc4, h2u, hmul, h2u, h2v]
    rw [show u * v * (u * v ^ 2) = u ^ 1 * v ^ 1 * (u ^ 1 * v ^ 2) by rw [pow_one, pow_one],
      hnf]
    rw [show 1 + 1 = 2 by norm_num, show 1 + 2 = 3 by norm_num, hv3, mul_one,
      eq_inv_iff_mul_eq_one, ← pow_succ, hu3]
  · rw [hc4, h2v, hmul, h2u, ← conj_pow, h2v, sq]
    rw [show u * v ^ 2 * (u * v ^ 2) = u ^ 1 * v ^ 2 * (u ^ 1 * v ^ 2) by rw [pow_one], hnf,
      show u * v * (u ^ (1 + 1) * v ^ (2 + 2)) = u ^ 1 * v ^ 1 * (u ^ (1 + 1) * v ^ (2 + 2)) by
        rw [pow_one, pow_one], hnf]
    rw [show 1 + (1 + 1) = 3 by norm_num, show 1 + (2 + 2) = 3 + 2 by norm_num, hu3, one_mul,
      pow_add, hv3, one_mul, eq_inv_iff_mul_eq_one, ← pow_succ, hv3]

theorem j3t_conj_pow_four :
    j3tGPerm ^ 4 * j3tU * (j3tGPerm ^ 4)⁻¹ = j3tU⁻¹ ∧
      j3tGPerm ^ 4 * j3tV * (j3tGPerm ^ 4)⁻¹ = j3tV⁻¹ := by
  obtain ⟨-, hu3, -, -, -, -⟩ := j3t_norm_facts
  obtain ⟨hgu, hgv, hc⟩ := j3t_det'
  exact conj_pow_four_of_det hu3 hgu hgv hc

end J3

section Config

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Sporadic.Schreier CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.PartTwo.KFacts.K426

theorem conj_inv_mem_centralizer_of_mem {G : Type*} [Group G] {k x y : G}
    (h : y ∈ Subgroup.centralizer ({k * x * k⁻¹} : Set G)) :
    k⁻¹ * y * k ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  calc k⁻¹ * y * k * x = k⁻¹ * (y * (k * x * k⁻¹)) * k := by group
    _ = k⁻¹ * ((k * x * k⁻¹) * y) * k := by rw [h]
    _ = x * (k⁻¹ * y * k) := by group


theorem closure_range_j3tD_le_j3P : Subgroup.closure (Set.range j3tD) ≤ j3P := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact j3tD_mem i

theorem j3tB0_le_D : j3tB0 ≤ Subgroup.closure (Set.range j3tD) := by
  rw [j3tB0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact evalW_mem_of_forall (fun i => Subgroup.subset_closure (Set.mem_range_self i)) j3tWu
  · exact evalW_mem_of_forall (fun i => Subgroup.subset_closure (Set.mem_range_self i)) j3tWv

theorem card_j3tB0 : Nat.card j3tB0 = 9 := by
  obtain ⟨-, hu3, hu1, hv1, hvu, hvu2⟩ := j3t_norm_facts
  obtain ⟨hgu, -, hc⟩ := j3t_det'
  have hv3 : j3tV ^ 3 = 1 := by rw [← hgu, conj_pow, hu3]; group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB : j3tB0 = Subgroup.zpowers j3tU ⊔ Subgroup.zpowers j3tV := by
    rw [j3tB0, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hou : orderOf j3tU = 3 := orderOf_eq_prime hu3 hu1
  have hpu : IsPGroup 3 (Subgroup.zpowers j3tU) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hou, pow_one])
  have hpv : IsPGroup 3 (Subgroup.zpowers j3tV) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hv3 hv1, pow_one])
  have hvN : Subgroup.zpowers j3tV ≤
      Subgroup.normalizer (Subgroup.zpowers j3tU : Set (Equiv.Perm (Fin 6156))) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left hc k)).eq
  have hp : IsPGroup 3 j3tB0 := hB ▸ IsPGroup.to_sup_of_normal_left' hpu hpv hvN
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd : Nat.card j3tB0 ∣ 360 := j3t_derived.2 ▸ Subgroup.card_dvd_of_le j3tB0_le_D
  have hule : Subgroup.zpowers j3tU ≤ j3tB0 := hB ▸ le_sup_left
  have h3 : 3 ∣ Nat.card j3tB0 := by
    have := Subgroup.card_dvd_of_le hule
    rwa [Nat.card_zpowers, hou] at this
  have hne : Nat.card j3tB0 ≠ 3 := by
    intro h3'
    have heq : Subgroup.zpowers j3tU = j3tB0 :=
      Subgroup.eq_of_le_of_card_ge hule (by rw [h3', Nat.card_zpowers, hou])
    have hvB : j3tV ∈ j3tB0 := hB ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers j3tV)
    rw [← heq] at hvB
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvB
    rw [← zpow_mod_orderOf, hou] at hk
    have hk0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have hk3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r : ℕ, k % ((3 : ℕ) : ℤ) = r := ⟨(k % ((3 : ℕ) : ℤ)).toNat, by omega⟩
    rw [hr, zpow_natCast] at hk
    have hr3 : r < 3 := by omega
    interval_cases r
    · exact hv1 (by rw [← hk, pow_zero])
    · exact hvu (by rw [← hk, pow_one])
    · exact hvu2 hk.symm
  rw [hn] at hdvd h3 hne ⊢
  have hn2 : n ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have := this.trans hdvd
    norm_num at this
  interval_cases n
  · norm_num at h3
  · norm_num at hne
  · norm_num

theorem j3tB0_comm {a b : Equiv.Perm (Fin 6156)} (ha : a ∈ j3tB0)
    (hb : b ∈ j3tB0) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := j3tB0)
    (by rw [card_j3tB0]; norm_num) ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

theorem j3tB0_map_conj_g :
    j3tB0.map (MulAut.conj j3tGPerm).toMonoidHom = j3tB0 := by
  obtain ⟨hgu, hgv, -⟩ := j3t_det'
  have hle : j3tB0.map (MulAut.conj j3tGPerm).toMonoidHom ≤ j3tB0 := by
    rw [j3tB0, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hu : j3tU ∈ j3tB0 := Subgroup.subset_closure (by simp)
    have hv : j3tV ∈ j3tB0 := Subgroup.subset_closure (by simp)
    rcases hx with rfl | rfl
    · show j3tGPerm * j3tU * j3tGPerm⁻¹ ∈ j3tB0
      rw [hgu]
      exact hv
    · show j3tGPerm * j3tV * j3tGPerm⁻¹ ∈ j3tB0
      rw [hgv]
      exact j3tB0.mul_mem hu hv
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])

theorem j3tB0_pow_four {b : Equiv.Perm (Fin 6156)}
    (hb : b ∈ j3tB0) : j3tGPerm ^ 4 * b * (j3tGPerm ^ 4)⁻¹ = b⁻¹ := by
  obtain ⟨h4u, h4v⟩ := j3t_conj_pow_four
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h4u
    · exact h4v
  | one => group
  | mul x y hx hy ihx ihy =>
    calc j3tGPerm ^ 4 * (x * y) * (j3tGPerm ^ 4)⁻¹ =
        (j3tGPerm ^ 4 * x * (j3tGPerm ^ 4)⁻¹) * (j3tGPerm ^ 4 * y * (j3tGPerm ^ 4)⁻¹) := by
          group
      _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
      _ = (x * y)⁻¹ := by rw [mul_inv_rev, j3tB0_comm (inv_mem hx) (inv_mem hy)]
  | inv x hx ihx =>
    calc j3tGPerm ^ 4 * x⁻¹ * (j3tGPerm ^ 4)⁻¹ = (j3tGPerm ^ 4 * x * (j3tGPerm ^ 4)⁻¹)⁻¹ := by
          group
      _ = x⁻¹⁻¹ := by rw [ihx]

theorem false_of_le_centralizer_caseB {k : Equiv.Perm (Fin 6156)} (hk : k ∈ j3P) {e : ℕ}
    (he : e = 1 ∨ e = 2) {K : Subgroup (Equiv.Perm (Fin 6156))} (hKR : K ≤ j3P)
    (hKc : K ≤ Subgroup.centralizer {k * j3tXB ^ e * k⁻¹}) (hK : Nat.card K = 360) : False := by
  have hx3 : j3tXB ^ 3 = 1 := (j3tReps_spec (by norm_num : 1 < 2)).2
  have hce : Subgroup.centralizer ({j3tXB ^ e} : Set (Equiv.Perm (Fin 6156))) =
      Subgroup.centralizer {j3tXB} := by
    rcases he with rfl | rfl
    · rw [pow_one]
    · exact centralizer_pow_two_eq_of_pow_three hx3
  have hK'le : K.map (MulAut.conj k⁻¹).toMonoidHom ≤ Subgroup.centralizer {j3tXB} ⊓ j3P := by
    rintro _ ⟨y, hy, rfl⟩
    have e1 : (MulAut.conj k⁻¹).toMonoidHom y = k⁻¹ * y * k := by
      simp [MulAut.conj_apply]
    rw [e1]
    refine ⟨?_, j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hk) (hKR hy)) hk⟩
    rw [← hce]
    exact conj_inv_mem_centralizer_of_mem (hKc hy)
  have h1 := Subgroup.card_dvd_of_le hK'le
  rw [← j3t_caseB.1, j3t_caseB.2, Subgroup.card_map_of_injective (MulAut.conj _).injective,
    hK] at h1
  norm_num at h1

theorem eq_D_of_perfect_le_centralizer {K : Subgroup (Equiv.Perm (Fin 6156))} (hKR : K ≤ j3P)
    (hKc : K ≤ Subgroup.centralizer {j3tXA}) (hKp : Group.IsPerfect K)
    (hK : Nat.card K = 360) : K = Subgroup.closure (Set.range j3tD) := by
  have h1 : ⁅K, K⁆ = K := Subgroup.commutator_eq_self
  have h2 : K ≤ Subgroup.centralizer {j3tXA} ⊓ j3P := le_inf hKc hKR
  have h3 : K ≤ Subgroup.closure (Set.range j3tD) := by
    rw [← h1]
    exact (Subgroup.commutator_mono h2 h2).trans j3t_derived.1
  exact Subgroup.eq_of_le_of_card_ge h3 (by rw [j3t_derived.2, hK])

theorem exists_eq_map_conj_j3tB0
    {B : Subgroup (Equiv.Perm (Fin 6156))} (hBD : B ≤ Subgroup.closure (Set.range j3tD))
    (hB : Nat.card B = 9) :
    ∃ m ∈ Subgroup.closure (Set.range j3tD), B = j3tB0.map (MulAut.conj m).toMonoidHom := by
  set D := Subgroup.closure (Set.range j3tD) with hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDf : (Nat.card D).factorization 3 = 2 := by
    rw [j3t_derived.2, show (360 : ℕ) = 3 ^ 2 * 40 by norm_num]
    exact Sec4.Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)
  have hP0 : Nat.card (j3tB0.subgroupOf D) = 3 ^ (Nat.card D).factorization 3 := by
    rw [hDf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe j3tB0_le_D).toEquiv, card_j3tB0]
    norm_num
  have hE : IsPGroup 3 (B.subgroupOf D) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBD).toEquiv, hB]
    norm_num)
  obtain ⟨m, hm⟩ := Sec4.Item434AltPerm.exists_le_map_conj_of_card hP0 hE
  refine ⟨m, m.2, ?_⟩
  have hle : B ≤ j3tB0.map (MulAut.conj (m : Equiv.Perm (Fin 6156))).toMonoidHom := by
    intro b hb
    have hb' : (⟨b, hBD hb⟩ : D) ∈ B.subgroupOf D := Subgroup.mem_subgroupOf.mpr hb
    obtain ⟨b₀, hb₀, hbb⟩ := hm hb'
    refine ⟨b₀, Subgroup.mem_subgroupOf.mp hb₀, ?_⟩
    have h1 := congrArg Subtype.val hbb
    simpa [MulAut.conj_apply] using h1
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, card_j3tB0, hB])

end Config

theorem conj_mem_centralizer_conj_iff {G : Type*} [Group G] {t x y : G} :
    t * y * t⁻¹ ∈ Subgroup.centralizer ({t * x * t⁻¹} : Set G) ↔
      y ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : t⁻¹ * (t * y * t⁻¹ * (t * x * t⁻¹)) * t =
        t⁻¹ * (t * x * t⁻¹ * (t * y * t⁻¹)) * t := by
      rw [h]
    simpa [mul_assoc] using h1
  · intro h
    calc t * y * t⁻¹ * (t * x * t⁻¹) = t * (y * x) * t⁻¹ := by group
      _ = t * (x * y) * t⁻¹ := by rw [h]
      _ = t * x * t⁻¹ * (t * y * t⁻¹) := by group

section Config2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Sporadic.Schreier CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.PartTwo.KFacts.K426


theorem exists_t_at_x0 {E : Subgroup (Equiv.Perm (Fin 6156))}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {e : ℕ}
    (hcE : j3tXA ^ e ∈ E)
    (hDc : Subgroup.closure (Set.range j3tD) ≤ Subgroup.centralizer {j3tXA})
    (hDp : Group.IsPerfect (Subgroup.closure (Set.range j3tD)))
    (hxD : j3tXA ^ e ∉ Subgroup.closure (Set.range j3tD))
    (hED : Nat.card (E ⊓ Subgroup.closure (Set.range j3tD) : Subgroup (Equiv.Perm (Fin 6156))) =
      9) :
    ∃ t ∈ j3P, t ∈ Subgroup.normalizer
        ((Subgroup.closure (Set.range j3tD) : Subgroup _) : Set (Equiv.Perm (Fin 6156))) ∧
      t ∈ Subgroup.normalizer (E : Set (Equiv.Perm (Fin 6156))) ∧
      t ∈ Subgroup.normalizer (Subgroup.zpowers (j3tXA ^ e) : Set (Equiv.Perm (Fin 6156))) ∧
      ∀ b ∈ E ⊓ Subgroup.closure (Set.range j3tD), t ^ 4 * b * (t ^ 4)⁻¹ = b⁻¹ := by
  set D := Subgroup.closure (Set.range j3tD) with hD
  set B := E ⊓ D with hB
  have hx3 : j3tXA ^ 3 = 1 := (j3tReps_spec (by norm_num : 0 < 2)).2
  obtain ⟨hgx, -, -, -, -, -⟩ := j3t_norm_facts
  obtain ⟨m, hmD, hBm⟩ := exists_eq_map_conj_j3tB0 (inf_le_right : B ≤ D) hED
  replace hBm : B = j3tB0.map (MulAut.conj m).toMonoidHom := hBm
  set g := j3tGPerm with hg
  set t := m * g * m⁻¹ with ht
  have hmR : m ∈ j3P := closure_range_j3tD_le_j3P hmD
  have htR : t ∈ j3P := j3P.mul_mem (j3P.mul_mem hmR j3tGPerm_mem) (j3P.inv_mem hmR)
  have hmx : Commute m j3tXA := Subgroup.mem_centralizer_singleton_iff.mp (hDc hmD)
  have htx : t * j3tXA * t⁻¹ = j3tXA ^ 2 := by
    have e1 : m⁻¹ * j3tXA * m = j3tXA := by
      rw [mul_assoc, ← hmx.eq, inv_mul_cancel_left]
    have e2 : m * j3tXA ^ 2 * m⁻¹ = j3tXA ^ 2 := by
      rw [(hmx.pow_right 2).eq, mul_inv_cancel_right]
    calc t * j3tXA * t⁻¹ = m * (g * (m⁻¹ * j3tXA * m) * g⁻¹) * m⁻¹ := by rw [ht]; group
      _ = j3tXA ^ 2 := by rw [e1, hg, hgx, e2]
  have hxe : t * j3tXA ^ e * t⁻¹ = (j3tXA ^ e) ^ 2 := by
    rw [← conj_pow, htx, ← pow_mul, ← pow_mul, mul_comm]
  have htc : t ∈
      Subgroup.normalizer (Subgroup.zpowers (j3tXA ^ e) : Set (Equiv.Perm (Fin 6156))) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow, hxe]
    exact zpow_mem (pow_mem (Subgroup.mem_zpowers _) 2) k
  set C := Subgroup.centralizer {j3tXA} ⊓ j3P with hC
  have hcC : Subgroup.centralizer ({j3tXA ^ 2} : Set (Equiv.Perm (Fin 6156))) =
      Subgroup.centralizer {j3tXA} := centralizer_pow_two_eq_of_pow_three hx3
  have htC : C.map (MulAut.conj t) = C := by
    have hle : C.map (MulAut.conj t) ≤ C := by
      rintro _ ⟨y, ⟨hyc, hyR⟩, rfl⟩
      have e1 : (MulAut.conj t : Equiv.Perm (Fin 6156) →* Equiv.Perm (Fin 6156)) y =
          t * y * t⁻¹ := by simp [MulAut.conj_apply]
      rw [e1]
      refine ⟨?_, j3P.mul_mem (j3P.mul_mem htR hyR) (j3P.inv_mem htR)⟩
      rw [← hcC, ← htx]
      exact conj_mem_centralizer_conj_iff.mpr hyc
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])
  have hDC : D ≤ C := le_inf hDc closure_range_j3tD_le_j3P
  have hDeq : ⁅C, C⁆ = D := by
    refine le_antisymm j3t_derived.1 ?_
    have h1 : ⁅D, D⁆ = D := Subgroup.commutator_eq_self
    rw [← h1]
    exact Subgroup.commutator_mono hDC hDC
  have htD : t ∈ Subgroup.normalizer (D : Set (Equiv.Perm (Fin 6156))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hDeq, Subgroup.map_commutator, htC]
  have hBmem : ∀ b ∈ B, ∃ b₀ ∈ j3tB0, b = m * b₀ * m⁻¹ := by
    intro b hb
    rw [hBm] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact ⟨b₀, hb₀, by simp [MulAut.conj_apply]⟩
  have hBin : ∀ b₀ ∈ j3tB0, m * b₀ * m⁻¹ ∈ B := by
    intro b₀ hb₀
    rw [hBm]
    exact ⟨b₀, hb₀, by simp [MulAut.conj_apply]⟩
  have hgB : ∀ b₀ ∈ j3tB0, g * b₀ * g⁻¹ ∈ j3tB0 := by
    intro b₀ hb₀
    have h1 : (MulAut.conj g).toMonoidHom b₀ ∈ j3tB0.map (MulAut.conj g).toMonoidHom :=
      ⟨b₀, hb₀, rfl⟩
    rw [hg, j3tB0_map_conj_g] at h1
    simpa [MulAut.conj_apply] using h1
  have htB : t ∈ Subgroup.normalizer (B : Set (Equiv.Perm (Fin 6156))) := by
    apply Subgroup.mem_normalizer_fintype
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := hBmem b hb
    have e1 : t * (m * b₀ * m⁻¹) * t⁻¹ = m * (g * b₀ * g⁻¹) * m⁻¹ := by rw [ht]; group
    rw [e1]
    exact hBin _ (hgB b₀ hb₀)
  have ht4 : ∀ b ∈ B, t ^ 4 * b * (t ^ 4)⁻¹ = b⁻¹ := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := hBmem b hb
    have e1 : t ^ 4 = m * g ^ 4 * m⁻¹ := by rw [ht, conj_pow]
    rw [e1]
    have e2 : m * g ^ 4 * m⁻¹ * (m * b₀ * m⁻¹) * (m * g ^ 4 * m⁻¹)⁻¹ =
        m * (g ^ 4 * b₀ * (g ^ 4)⁻¹) * m⁻¹ := by group
    rw [e2, hg, j3tB0_pow_four hb₀]
    group
  have hZB : Subgroup.zpowers (j3tXA ^ e) ⊔ B ≤ E :=
    sup_le (Subgroup.zpowers_le.mpr hcE) inf_le_left
  have hEeq : Subgroup.zpowers (j3tXA ^ e) ⊔ B = E := by
    refine Subgroup.eq_of_le_of_card_ge hZB ?_
    have h1 : Nat.card (Subgroup.zpowers (j3tXA ^ e) ⊔ B : Subgroup _) ∣ 27 :=
      hE27 ▸ Subgroup.card_dvd_of_le hZB
    have h2 : 9 ∣ Nat.card (Subgroup.zpowers (j3tXA ^ e) ⊔ B : Subgroup _) :=
      hED ▸ Subgroup.card_dvd_of_le le_sup_right
    have h3 : Nat.card (Subgroup.zpowers (j3tXA ^ e) ⊔ B : Subgroup _) ≠ 9 := by
      intro h9
      have heq : B = Subgroup.zpowers (j3tXA ^ e) ⊔ B :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h9, hED])
      have : j3tXA ^ e ∈ B := heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      exact hxD this.2
    rw [hE27]
    obtain ⟨k, hk⟩ := h2
    have hk27 : 9 * k ∣ 27 := hk ▸ h1
    have hk3 : k ∣ 3 :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by simpa using hk27)
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h | h
    · exact absurd (by rw [hk, h]) h3
    · rw [hk, h]
  have htE : t ∈ Subgroup.normalizer (E : Set (Equiv.Perm (Fin 6156))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hEeq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htc,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htB]
  exact ⟨t, htR, htD, htE, htc, ht4⟩

end Config2

theorem map_conj_map_conj_inv_kfj3 {G : Type*} [Group G] (H : Subgroup G) (k : G) :
    (H.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj k).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj k).toMonoidHom.comp (MulAut.conj k⁻¹).toMonoidHom = MonoidHom.id G := by
    refine MonoidHom.ext fun x => ?_
    show k * (k⁻¹ * x * k⁻¹⁻¹) * k⁻¹ = x
    group
  rw [h, Subgroup.map_id]

theorem conj_mem_normalizer_of_map {G : Type*} [Group G] {H : Subgroup G} {k t : G}
    (h : t ∈ Subgroup.normalizer ((H.map (MulAut.conj k⁻¹).toMonoidHom : Subgroup G) : Set G)) :
    k * t * k⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
  have h1 := Subgroup.map_equiv_normalizer_eq (H.map (MulAut.conj k⁻¹).toMonoidHom)
    (MulAut.conj k)
  rw [map_conj_map_conj_inv_kfj3] at h1
  rw [← h1]
  exact ⟨t, h, rfl⟩

section Config3

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Sporadic.Schreier CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.PartTwo.KFacts.K426


theorem j3PermConfig_holds : J3PermConfig := by
  intro E K c hER hKR hE hE27 hcE hc1 hKc hK6 hEK
  obtain ⟨ψ⟩ := hK6
  have hA6c : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨hA6p, hA6Z⟩ := Sec13.isPerfect_center_of_isSimpleGroup hsimple (by rw [hA6c]; norm_num)
  have hK360 : Nat.card K = 360 := by rw [Nat.card_congr ψ.toEquiv, hA6c]
  have hc3 : c ^ 3 = 1 := hE.2 c hcE
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  obtain ⟨k, hk, x, hx, e, he, rfl⟩ := j3t_fusion (hER hcE) hco
  rcases hx with rfl | rfl
  swap
  · exact (false_of_le_centralizer_caseB hk he hKR hKc hK360).elim
  have hx3 : j3tXA ^ 3 = 1 := (j3tReps_spec (by norm_num : 0 < 2)).2
  have hce : Subgroup.centralizer ({j3tXA ^ e} : Set (Equiv.Perm (Fin 6156))) =
      Subgroup.centralizer {j3tXA} := by
    rcases he with rfl | rfl
    · rw [pow_one]
    · exact centralizer_pow_two_eq_of_pow_three hx3
  set f := (MulAut.conj k⁻¹).toMonoidHom with hf
  have hfapp : ∀ y, f y = k⁻¹ * y * k := fun y => by simp [hf, MulAut.conj_apply]
  have hfinj : Function.Injective f := (MulAut.conj k⁻¹).injective
  have hfR : ∀ y ∈ j3P, f y ∈ j3P := fun y hy => by
    rw [hfapp]
    exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hk) hy) hk
  set E₁ := E.map f with hE₁
  set K₁ := K.map f with hK₁
  have hfc : f (k * j3tXA ^ e * k⁻¹) = j3tXA ^ e := by
    rw [hfapp]
    simp [mul_assoc]
  have hK₁R : K₁ ≤ j3P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hfR y (hKR hy)
  have hK₁c : K₁ ≤ Subgroup.centralizer {j3tXA} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hfapp, ← hce]
    exact conj_inv_mem_centralizer_of_mem (hKc hy)
  set eK : K ≃* K₁ := K.equivMapOfInjective f hfinj with heK
  have hK₁p : Group.IsPerfect K₁ :=
    Group.IsPerfect.ofSurjective (f := (eK.symm.trans ψ).symm.toMonoidHom)
      (eK.symm.trans ψ).symm.surjective
  have hK₁card : Nat.card K₁ = 360 := by rw [← Nat.card_congr eK.toEquiv, hK360]
  have hK₁D : K₁ = Subgroup.closure (Set.range j3tD) :=
    eq_D_of_perfect_le_centralizer hK₁R hK₁c hK₁p hK₁card
  have hE₁e : CFSG.Assembly.IsElemAbelian 3 E₁ :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 f E hE
  have hE₁27 : Nat.card E₁ = 27 := by rw [hE₁, Subgroup.card_map_of_injective hfinj, hE27]
  have hcE₁ : j3tXA ^ e ∈ E₁ := hfc ▸ ⟨_, hcE, rfl⟩
  have hDc : Subgroup.closure (Set.range j3tD) ≤ Subgroup.centralizer {j3tXA} := hK₁D ▸ hK₁c
  have hDp : Group.IsPerfect (Subgroup.closure (Set.range j3tD)) := hK₁D ▸ hK₁p
  have hxD : j3tXA ^ e ∉ Subgroup.closure (Set.range j3tD) := by
    intro hxD
    rw [← hK₁D, ← hfc] at hxD
    obtain ⟨y, hyK, hy⟩ := hxD
    have hyc : y = k * j3tXA ^ e * k⁻¹ := hfinj hy
    subst hyc
    have hz : ψ ⟨_, hyK⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨⟨w, hw⟩, rfl⟩ := ψ.surjective a
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKc hw)
    rw [hA6Z, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hz
    exact hc1 (congrArg Subtype.val hz)
  have hE₁D : Nat.card (E₁ ⊓ Subgroup.closure (Set.range j3tD) : Subgroup _) = 9 := by
    rw [← hK₁D, hE₁, hK₁, ← Subgroup.map_inf_eq E K f hfinj,
      Subgroup.card_map_of_injective hfinj, hEK]
  obtain ⟨t, htR, htD, htE, htc, ht4⟩ := exists_t_at_x0 hE₁e hE₁27 hcE₁ hDc hDp hxD hE₁D
  refine ⟨k * t * k⁻¹, j3P.mul_mem (j3P.mul_mem hk htR) (j3P.inv_mem hk), ?_, ?_, ?_, ?_⟩
  · rw [← hK₁D] at htD
    exact conj_mem_normalizer_of_map htD
  · exact conj_mem_normalizer_of_map htE
  · apply conj_mem_normalizer_of_map
    rw [MonoidHom.map_zpowers]
    change t ∈ Subgroup.normalizer (Subgroup.zpowers (f (k * j3tXA ^ e * k⁻¹)) : Set _)
    rw [hfc]
    exact htc
  · intro b hb
    have hfb : f b ∈ E₁ ⊓ Subgroup.closure (Set.range j3tD) := by
      rw [← hK₁D]
      exact ⟨⟨b, hb.1, rfl⟩, ⟨b, hb.2, rfl⟩⟩
    have h1 := ht4 (f b) hfb
    rw [hfapp] at h1
    have e1 : (k * t * k⁻¹) ^ 4 = k * t ^ 4 * k⁻¹ := conj_pow
    rw [e1]
    calc k * t ^ 4 * k⁻¹ * b * (k * t ^ 4 * k⁻¹)⁻¹ =
        k * (t ^ 4 * (k⁻¹ * b * k) * (t ^ 4)⁻¹) * k⁻¹ := by group
      _ = k * (k⁻¹ * b * k)⁻¹ * k⁻¹ := by rw [h1]
      _ = b⁻¹ := by group

end Config3

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
