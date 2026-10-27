module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.Ordering
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_eq_of_perfect_of_isSylowTwoOf {A T : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hT : IsSylowTwoOf T A) : conjClosure T A = A := by
  have hTA : T ≤ A := hT.1
  have hNA : conjClosure T A ≤ A := conjClosure_le fun h hh z hz =>
    A.mul_mem (A.mul_mem hh (hTA hz)) (A.inv_mem hh)
  have hnorm : ((conjClosure T A).subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_conjClosure T A)
  have hperf : Group.IsPerfect A := Subgroup.isPerfect_iff.mpr hA
  have hle : T.subgroupOf A ≤ (conjClosure T A).subgroupOf A := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (le_conjClosure T A (Subgroup.mem_subgroupOf.mp hx))
  have hodd : Odd (Nat.card (↥A ⧸ (conjClosure T A).subgroupOf A)) := by
    have hdvd : ((conjClosure T A).subgroupOf A).index ∣ (T.subgroupOf A).index :=
      Subgroup.index_dvd_of_le hle
    have h2 : ¬ 2 ∣ ((conjClosure T A).subgroupOf A).index := fun h => hT.2.2 (h.trans hdvd)
    have : Nat.card (↥A ⧸ (conjClosure T A).subgroupOf A) % 2 = 1 := by
      change ((conjClosure T A).subgroupOf A).index % 2 = 1
      omega
    exact Nat.odd_iff.mpr this
  have hsolv : Group.IsSolvable (↥A ⧸ (conjClosure T A).subgroupOf A) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsub : Subsingleton (↥A ⧸ (conjClosure T A).subgroupOf A) := by
    by_contra hns
    have : Nontrivial (↥A ⧸ (conjClosure T A).subgroupOf A) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (↥A ⧸ (conjClosure T A).subgroupOf A) hsolv
  refine le_antisymm hNA fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ (conjClosure T A).subgroupOf A) =
      QuotientGroup.mk 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq] at h1
  simpa [Subgroup.mem_subgroupOf] using h1

namespace C2Coprime

theorem mem_of_pow_eq_one {H : Type*} [Group H] (U : Subgroup H) [U.Normal] {q x : H} {s n : ℕ}
    (hn : Odd n) (hq : q ^ 2 ^ s = 1) (hx : x ^ n = 1) (hqx : (q * x) ^ n = 1)
    (hc : q * x * q⁻¹ * x⁻¹ ∈ U) : q ∈ U := by
  have hcomm : Commute (QuotientGroup.mk q : H ⧸ U) (QuotientGroup.mk x) := by
    show (QuotientGroup.mk q : H ⧸ U) * QuotientGroup.mk x =
      QuotientGroup.mk x * QuotientGroup.mk q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_assoc] using hc
  have h1 : (QuotientGroup.mk q : H ⧸ U) ^ n = 1 := by
    have e1 : ((QuotientGroup.mk q : H ⧸ U) * QuotientGroup.mk x) ^ n = 1 := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hqx]
      exact QuotientGroup.mk_one U
    have e2 : (QuotientGroup.mk x : H ⧸ U) ^ n = 1 := by
      rw [← QuotientGroup.mk_pow, hx]
      exact QuotientGroup.mk_one U
    rwa [hcomm.mul_pow, e2, mul_one] at e1
  have h2 : (QuotientGroup.mk q : H ⧸ U) ^ 2 ^ s = 1 := by
    rw [← QuotientGroup.mk_pow, hq]
    exact QuotientGroup.mk_one U
  have h3 : (QuotientGroup.mk q : H ⧸ U) ^ Nat.gcd (2 ^ s) n = 1 :=
    pow_gcd_eq_one.mpr ⟨h2, h1⟩
  have hcop : Nat.gcd (2 ^ s) n = 1 := Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hn)
  rw [hcop, pow_one] at h3
  exact (QuotientGroup.eq_one_iff q).mp h3

theorem commutator_mem_blockU {K A : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKA : ⁅K, A⁆ ≤ pCoreOf 2 K) {x a : G} (hx : x ∈ K) (ha : a ∈ A) {n : ℕ} (hn : Odd n)
    (hxn : x ^ n = 1) : a * x * a⁻¹ * x⁻¹ ∈ blockU K := by
  have hy : a * x * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAK ha) x).mp hx
  have hqK : a * x * a⁻¹ * x⁻¹ ∈ K := K.mul_mem hy (K.inv_mem hx)
  have hq : a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 K :=
    hKA (Subgroup.commutator_comm_le A K (Subgroup.commutator_mem_commutator ha hx))
  have : ((blockU K).subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.normalizer_commutator_ge_right (pCoreOf 2 K) K)
  obtain ⟨s, hs⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hq⟩
  have hs' : (a * x * a⁻¹ * x⁻¹) ^ 2 ^ s = 1 := by simpa using congrArg Subtype.val hs
  have key := mem_of_pow_eq_one ((blockU K).subgroupOf K)
    (q := (⟨a * x * a⁻¹ * x⁻¹, hqK⟩ : K)) (x := ⟨x, hx⟩) (s := s) (n := n) hn
    (Subtype.ext (by simpa using hs')) (Subtype.ext (by simpa using hxn)) ?_ ?_
  · exact Subgroup.mem_subgroupOf.mp key
  · apply Subtype.ext
    have e : a * x * a⁻¹ * x⁻¹ * x = a * x * a⁻¹ := by group
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, e, conj_pow, hxn, OneMemClass.coe_one]
    group
  · rw [Subgroup.mem_subgroupOf]
    exact Subgroup.commutator_mem_commutator hq hx

omit [Finite G] in
theorem commute_of_perfect {A U : Subgroup G} {x : G} (hA : ⁅A, A⁆ = A)
    (hUab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u = u * a)
    (hφ : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ U) : ∀ a ∈ A, a * x = x * a := by
  have hmul : ∀ c ∈ A, ∀ d ∈ A, ∀ uc ud : G, uc = c * x * c⁻¹ * x⁻¹ → ud = d * x * d⁻¹ * x⁻¹ →
      c * d * x * (c * d)⁻¹ = ud * (uc * x) := by
    intro c hc d hd uc ud huc hud
    have hudU : ud ∈ U := by rw [hud]; exact hφ d hd
    have h1 : c * ud * c⁻¹ = ud := mul_inv_eq_iff_eq_mul.mpr (hAU c hc ud hudU)
    calc c * d * x * (c * d)⁻¹ = (c * ud * c⁻¹) * (c * x * c⁻¹) := by rw [hud]; group
      _ = ud * (uc * x) := by rw [h1, huc]; group
  have key : ∀ a ∈ A, ∀ b ∈ A, a * b * x * (a * b)⁻¹ = b * a * x * (b * a)⁻¹ := by
    intro a ha b hb
    obtain ⟨ua, hua⟩ : ∃ ua, ua = a * x * a⁻¹ * x⁻¹ := ⟨_, rfl⟩
    obtain ⟨ub, hub⟩ : ∃ ub, ub = b * x * b⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hua' : ua ∈ U := by rw [hua]; exact hφ a ha
    have hub' : ub ∈ U := by rw [hub]; exact hφ b hb
    rw [hmul a ha b hb ua ub hua hub, hmul b hb a ha ub ua hub hua, ← mul_assoc, ← mul_assoc,
      hUab ub hub' ua hua']
  have hcomm : ⁅A, A⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have E := key b⁻¹ (A.inv_mem hb) a⁻¹ (A.inv_mem ha)
    have h : (a * b) * (b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹) * (a * b)⁻¹ =
        (a * b) * (a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹) * (a * b)⁻¹ := by rw [E]
    have h1 : (a * b) * (b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹) * (a * b)⁻¹ = x := by group
    have h2 : (a * b) * (a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹) * (a * b)⁻¹ =
        (a * b * a⁻¹ * b⁻¹) * x * (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
    rw [h1, h2] at h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact eq_mul_inv_iff_mul_eq.mp h
  rw [hA] at hcomm
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hcomm ha) x rfl).symm

theorem le_of_forall_odd_order {K C : Subgroup G}
    (hK : ∀ (N : Subgroup K) [N.Normal], IsPGroup 2 (K ⧸ N) → N = ⊤)
    (hC : ∀ x ∈ K, ∀ n : ℕ, Odd n → x ^ n = 1 → x ∈ C) : K ≤ C := by
  set S : Set K := {x | ∃ n : ℕ, Odd n ∧ x ^ n = 1} with hSdef
  have hS : ∀ g : K, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    rintro g x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [conj_pow, hx, mul_one, mul_inv_cancel]⟩
  have : (Subgroup.closure S).Normal := by
    refine ⟨fun x hx g => ?_⟩
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hS g x hx)
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using (Subgroup.closure S).mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using (Subgroup.closure S).inv_mem ih
  have hp : IsPGroup 2 (K ⧸ Subgroup.closure S) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      refine Subgroup.subset_closure ⟨m, hm, ?_⟩
      rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  have htop : Subgroup.closure S = ⊤ := hK _ hp
  have hsub : Subgroup.closure S ≤ C.comap K.subtype := by
    rw [Subgroup.closure_le]
    rintro x ⟨n, hn, hxn⟩
    exact hC x x.2 n hn (by simpa using congrArg Subtype.val hxn)
  intro k hk
  exact hsub (htop ▸ Subgroup.mem_top (⟨k, hk⟩ : K))

end C2Coprime

theorem le_centralizer_of_perfect_of_le_centralizer_blockU {K A : Subgroup G} (hK : IsShort2 K)
    (hA : ⁅A, A⁆ = A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKA : ⁅K, A⁆ ≤ pCoreOf 2 K) (hU : A ≤ Subgroup.centralizer (blockU K : Set G)) :
    A ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨hK1, -, ⟨hUQ, -⟩, -⟩ := hK
  have hUab : ∀ u ∈ blockU K, ∀ v ∈ blockU K, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.mp ((le_inf_iff.mp hUQ).2 hu) v ((le_inf_iff.mp hUQ).1 hv)).symm
  have hAU : ∀ a ∈ A, ∀ u ∈ blockU K, a * u = u * a := fun a ha u hu =>
    (Subgroup.mem_centralizer_iff.mp (hU ha) u hu).symm
  have hKC : K ≤ Subgroup.centralizer (A : Set G) := by
    refine C2Coprime.le_of_forall_odd_order hK1 fun x hx n hn hxn => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact C2Coprime.commute_of_perfect hA hUab hAU
      (fun a ha => C2Coprime.commutator_mem_blockU hAK hKA hx ha hn hxn) a ha
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.mp (hKC hk) a ha).symm

end CFSG.Quasithin
