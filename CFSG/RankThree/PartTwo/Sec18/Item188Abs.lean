module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.ThompsonAxB
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeOmega

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item188Proof

open scoped commutatorElement

open Subgroup in
theorem commutator_commutator_le_of_rotate {G : Type*} [Group G] {A B C N : Subgroup G}
    (hA : A ≤ normalizer (N : Set G)) (hB : B ≤ normalizer (N : Set G))
    (hC : C ≤ normalizer (N : Set G))
    (h1 : ⁅⁅A, B⁆, C⁆ ≤ N) (h2 : ⁅⁅B, C⁆, A⁆ ≤ N) : ⁅⁅C, A⁆, B⁆ ≤ N := by
  set Y := normalizer (N : Set G) with hY
  have hN : (N.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer (le_normalizer)).mpr le_rfl
  let q := QuotientGroup.mk' (N.subgroupOf Y)
  have hcomm : ∀ {P R : Subgroup G}, P ≤ Y → R ≤ Y →
      ⁅P, R⁆.subgroupOf Y = ⁅P.subgroupOf Y, R.subgroupOf Y⁆ := by
    intro P R hP hR
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hP hR),
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hP,
      Subgroup.map_subgroupOf_eq_of_le hR]
  have hAB : ⁅A, B⁆ ≤ Y := Subgroup.commutator_le_of_le hA hB
  have hBC : ⁅B, C⁆ ≤ Y := Subgroup.commutator_le_of_le hB hC
  have hCA : ⁅C, A⁆ ≤ Y := Subgroup.commutator_le_of_le hC hA
  have e1 : ⁅⁅A.subgroupOf Y, B.subgroupOf Y⁆, C.subgroupOf Y⁆ ≤ N.subgroupOf Y := by
    rw [← hcomm hA hB, ← hcomm hAB hC]
    exact (Subgroup.comap_mono h1)
  have e2 : ⁅⁅B.subgroupOf Y, C.subgroupOf Y⁆, A.subgroupOf Y⁆ ≤ N.subgroupOf Y := by
    rw [← hcomm hB hC, ← hcomm hBC hA]
    exact (Subgroup.comap_mono h2)
  have f1 : ⁅⁅(A.subgroupOf Y).map q, (B.subgroupOf Y).map q⁆, (C.subgroupOf Y).map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simpa [q] using e1
  have f2 : ⁅⁅(B.subgroupOf Y).map q, (C.subgroupOf Y).map q⁆, (A.subgroupOf Y).map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simpa [q] using e2
  have f3 := Subgroup.commutator_commutator_eq_bot_of_rotate f1 f2
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff] at f3
  have f4 : ⁅⁅C, A⁆, B⁆.subgroupOf Y ≤ N.subgroupOf Y := by
    rw [hcomm hCA hB, hcomm hC hA]
    simpa [q] using f3
  intro x hx
  have := f4 (show (⟨x, Subgroup.commutator_le_of_le hCA hB hx⟩ : Y) ∈
    ⁅⁅C, A⁆, B⁆.subgroupOf Y from hx)
  exact this

theorem pow_conj_eq_inv_pow_mul {G : Type*} [Group G] {q x c : G}
    (hc : c = q * x * q⁻¹ * x⁻¹) (hcx : Commute c x) (n : ℕ) :
    x ^ n * q * (x ^ n)⁻¹ = c⁻¹ ^ n * q := by
  have e1 : x * q * x⁻¹ = c⁻¹ * q := by
    rw [hc]
    group
  have hd : Commute c⁻¹ x := hcx.inv_left
  induction n with
  | zero => simp
  | succ n ih =>
    have e2 : x * c⁻¹ ^ n * x⁻¹ = c⁻¹ ^ n := by
      rw [← (hd.pow_left n).eq, mul_inv_cancel_right]
    calc x ^ (n + 1) * q * (x ^ (n + 1))⁻¹
        = x * (x ^ n * q * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          simp only [mul_assoc]
      _ = x * (c⁻¹ ^ n * q) * x⁻¹ := by rw [ih]
      _ = (x * c⁻¹ ^ n * x⁻¹) * (x * q * x⁻¹) := by group
      _ = c⁻¹ ^ n * (c⁻¹ * q) := by rw [e2, e1]
      _ = c⁻¹ ^ (n + 1) * q := by rw [pow_succ, mul_assoc]

theorem eq_one_of_pow_two_pow_three_pow {G : Type*} [Group G] {g : G} {k m : ℕ}
    (h2 : g ^ 2 ^ k = 1) (h3 : g ^ 3 ^ m = 1) : g = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (3 ^ m) :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).pow_right m
  have hord : orderOf g ∣ Nat.gcd (2 ^ k) (3 ^ m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [Nat.Coprime.gcd_eq_one hcop] at hord
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)

theorem exists_pow_eq_one_of_mem {G : Type*} [Group G] {p : ℕ} {P : Subgroup G}
    (hP : IsPGroup p P) {g : G} (hg : g ∈ P) : ∃ k : ℕ, g ^ p ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem conj_eq_of_commute {G : Type*} [Group G] {g k : G} (h : Commute g k) :
    g * k * g⁻¹ = k := by
  rw [h.eq, mul_inv_cancel_right]

theorem mem_normalizer_of_forall_commute {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (hg : ∀ k ∈ K, Commute g k) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rw [conj_eq_of_commute (hg k hk)]
    exact hk
  · have h1 := conj_eq_of_commute (hg (g * k * g⁻¹) hk).inv_left
    have h2 : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k := by group
    rw [h2] at h1
    rw [h1]
    exact hk

theorem conj_mem_centralizer_of_forall {G : Type*} [Group G] {S : Set G} {x y : G}
    (hx : ∀ s ∈ S, Commute x s) (hy : y ∈ Subgroup.centralizer S) :
    x * y * x⁻¹ ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro s hs
  have hsx : Commute s x := (hx s hs).symm
  exact (hsx.mul_right (show Commute s y from hy s hs)).mul_right hsx.inv_right

theorem mem_normalizer_centralizer_of_forall {G : Type*} [Group G] {S : Set G} {g : G}
    (hg : ∀ s ∈ S, Commute g s) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_centralizer_of_forall hg hy, fun hy => ?_⟩
  have h1 := conj_mem_centralizer_of_forall (fun s hs => (hg s hs).inv_left) hy
  have h2 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rw [h2] at h1
  exact h1

theorem mem_normalizer_inf {G : Type*} [Group G] {K L : Subgroup G} {g : G}
    (hK : g ∈ Subgroup.normalizer (K : Set G)) (hL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hK hL ⊢
  intro y
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (hK y) (hL y)

theorem centralizes_of_thompson_AxB {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {P R B : Subgroup H} (hP : IsPGroup p P) (hR : Nat.Coprime (Nat.card R) p)
    (hB : IsPGroup p B) (hRP : R ≤ Subgroup.normalizer (P : Set H))
    (hBP : B ≤ Subgroup.normalizer (P : Set H)) (hRB : ⁅R, B⁆ = ⊥)
    (hfix : P ⊓ Subgroup.centralizer (B : Set H) ≤ Subgroup.centralizer (R : Set H)) :
    P ≤ Subgroup.centralizer (R : Set H) := by
  have hRB' : R ≤ Subgroup.centralizer (B : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRB
  let α : R →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hRP)
  let β : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hα : ∀ (r : R) (x : P), ((α r x : P) : H) = r * x * (r : H)⁻¹ := fun r x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hRP r) x
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : H) = b * x * (b : H)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hBP b) x
  have hcomm : ∀ r b, α r * β b = β b * α r := by
    intro r b
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hrb : (b : H) * r = r * b := Subgroup.mem_centralizer_iff.mp (hRB' r.2) b b.2
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα]
    calc (r : H) * (b * x * (b : H)⁻¹) * (r : H)⁻¹ = (r * b) * x * ((r : H) * b)⁻¹ := by
          group
      _ = (b * r) * x * ((b : H) * r)⁻¹ := by rw [hrb]
      _ = b * (r * x * (r : H)⁻¹) * (b : H)⁻¹ := by group
  have hfix' : ∀ r x, (∀ b, β b x = x) → α r x = x := by
    intro r x hx
    have hxB : (x : H) ∈ Subgroup.centralizer (B : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hx ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (x : H) = b * x * b⁻¹ * b := by group
        _ = x * b := by rw [h]
    have hrx : (r : H) * x = x * r :=
      Subgroup.mem_centralizer_iff.mp (hfix ⟨x.2, hxB⟩) r r.2
    apply Subtype.ext
    rw [hα, hrx, mul_inv_cancel_right]
  have hR' : ¬ p ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hR.symm
  have key := CFSG.GroupTheory.thompson_A_times_B hP hR' hB α β hcomm hfix'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h := congrArg (fun f : MulAut P => ((f ⟨x, hx⟩ : P) : H)) (key ⟨r, hr⟩)
  simp only [hα, MulAut.one_apply] at h
  calc r * x = r * x * r⁻¹ * r := by group
    _ = x * r := by rw [h]

theorem le_centralizer_of_fix_order_three {X : Type*} [Group X] [Finite X] {U T : Subgroup X}
    (hU : IsPGroup 3 U) (hT : IsPGroup 2 T) (hTU : T ≤ Subgroup.normalizer (U : Set X))
    (hfix : ∀ t ∈ T, ∀ u : X, u ∈ U → u ^ 3 = 1 → t * u * t⁻¹ = u) :
    T ≤ Subgroup.centralizer (U : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : T →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hTU)
  have hφ : ∀ (t : T) (u : U), ((φ t u : U) : X) = (t : X) * (u : X) * (t : X)⁻¹ := fun t u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion hTU t) u
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hφt : φ ⟨t, ht⟩ = 1 := by
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have hord : orderOf (φ ⟨t, ht⟩) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hk, map_one]
    have hcop : Nat.Coprime (orderOf (φ ⟨t, ht⟩)) 3 :=
      Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.pow_left k (by norm_num))
    apply CFSG.HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
      (by norm_num) hU hcop
    intro x hx
    apply Subtype.ext
    rw [hφ]
    exact hfix t ht x x.2 (by simpa using congrArg Subtype.val hx)
  have h := hφ ⟨t, ht⟩ ⟨u, hu⟩
  rw [hφt, MulAut.one_apply] at h
  calc u * t = (t * u * t⁻¹) * t := by rw [show t * u * t⁻¹ = u from h.symm]
    _ = t * u := by group

theorem eq_bot_of_isPGroup_two {X : Type*} [Group X] [Finite X] {Q A T : Subgroup X}
    (hQ : IsPGroup 3 Q) (hQn : Q.Normal) (hCQ : Subgroup.centralizer (Q : Set X) ≤ Q)
    (hA : IsPGroup 3 A) (hQA : Q ≤ Subgroup.normalizer (A : Set X))
    (hA3 : ∀ x ∈ Q, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A)
    (hT : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set X)) : T = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNQ : ∀ g : X, g ∈ Subgroup.normalizer (Q : Set X) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hQn]
    exact Subgroup.mem_top g
  have hTQ : ∀ g ∈ T, g ∈ Q → g = 1 := fun g hgT hgQ => by
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hT hgT
    obtain ⟨m, hm⟩ := exists_pow_eq_one_of_mem hQ hgQ
    exact eq_one_of_pow_two_pow_three_pow hk hm
  have hTB : ∀ t ∈ T, ∀ b ∈ A ⊓ Q, t * b = b * t := by
    intro t ht b hb
    obtain ⟨hbA, hbQ⟩ := Subgroup.mem_inf.mp hb
    have h1 : ⁅t, b⁆ ∈ T := by
      have hc : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hAT hbA) t).mp ht
      rw [commutatorElement_def]
      have e : t * b * t⁻¹ * b⁻¹ = t * (b * t * b⁻¹)⁻¹ := by group
      rw [e]
      exact T.mul_mem ht (T.inv_mem hc)
    have h2 : ⁅t, b⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (hQn.conj_mem b hbQ t) (Q.inv_mem hbQ)
    exact commutatorElement_eq_one_iff_mul_comm.mp (hTQ _ h1 h2)
  have hQA' : ⁅Q, A⁆ ≤ A ⊓ Q := by
    rw [Subgroup.commutator_le]
    intro q hq a ha
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQA hq) a).mp ha) (A.inv_mem ha)
    · have e : q * a * q⁻¹ * a⁻¹ = q * (a * q⁻¹ * a⁻¹) := by group
      rw [e]
      exact Q.mul_mem hq (hQn.conj_mem q⁻¹ (Q.inv_mem hq) a)
  have hBT : ⁅A ⊓ Q, T⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact hTB t ht b hb
  have hN_T : T ≤ Subgroup.normalizer ((A ⊓ Q : Subgroup X) : Set X) := by
    intro t ht
    exact mem_normalizer_of_forall_commute (fun b hb => hTB t ht b hb)
  have hN_Q : Q ≤ Subgroup.normalizer ((A ⊓ Q : Subgroup X) : Set X) := by
    intro q hq
    exact mem_normalizer_inf (hQA hq) (hNQ q)
  have hN_A : A ≤ Subgroup.normalizer ((A ⊓ Q : Subgroup X) : Set X) := by
    intro a ha
    exact mem_normalizer_inf (Subgroup.le_normalizer ha) (hNQ a)
  have hT1 : ⁅⁅T, Q⁆, A⁆ ≤ A ⊓ Q :=
    le_trans (Subgroup.commutator_mono (Subgroup.commutator_le_right T Q) le_rfl) hQA'
  have hT2 : ⁅⁅Q, A⁆, T⁆ ≤ A ⊓ Q :=
    le_trans (Subgroup.commutator_mono hQA' le_rfl) (by rw [hBT]; exact bot_le)
  have hrot : ⁅⁅A, T⁆, Q⁆ ≤ A ⊓ Q :=
    commutator_commutator_le_of_rotate hN_T hN_Q hN_A hT1 hT2
  have hATle : ⁅A, T⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro a ha t ht
    rw [commutatorElement_def]
    exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAT ha) t).mp ht) (T.inv_mem ht)
  have hAT0 : ⁅A, T⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxT : x ∈ T := hATle hx
    have hxQ : x ∈ Q := by
      apply hCQ
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hm : ⁅q, x⁆ ∈ ⁅Q, ⁅A, T⁆⁆ := Subgroup.commutator_mem_commutator hq hx
      rw [Subgroup.commutator_comm Q ⁅A, T⁆] at hm
      have hcB : ⁅q, x⁆ ∈ A ⊓ Q := hrot hm
      have hcx : Commute ⁅q, x⁆ x := (hTB x hxT _ hcB).symm
      obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hT hxT
      obtain ⟨m, hm3⟩ := exists_pow_eq_one_of_mem hQ (Subgroup.mem_inf.mp hcB).2
      have hd2 : ⁅q, x⁆⁻¹ ^ 2 ^ k = 1 := by
        have h := pow_conj_eq_inv_pow_mul (commutatorElement_def q x) hcx (2 ^ k)
        rw [hk, inv_one, mul_one, one_mul] at h
        exact mul_eq_right.mp h.symm
      have hd3 : ⁅q, x⁆⁻¹ ^ 3 ^ m = 1 := by
        rw [inv_pow, hm3, inv_one]
      exact commutatorElement_eq_one_iff_mul_comm.mp
        (inv_eq_one.mp (eq_one_of_pow_two_pow_three_pow hd2 hd3))
    exact Subgroup.mem_bot.mpr (hTQ x hxT hxQ)
  have hTA : ∀ t ∈ T, ∀ a ∈ A, t * a = a * t := by
    intro t ht a ha
    have hm : ⁅a, t⁆ ∈ ⁅A, T⁆ := Subgroup.commutator_mem_commutator ha ht
    rw [hAT0, Subgroup.mem_bot] at hm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hm).symm
  have hTC : ∀ t ∈ T,
      t ∈ Subgroup.normalizer ((Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
    intro t ht
    exact mem_normalizer_centralizer_of_forall (fun a ha => hTA t ht a ha)
  have hTU : T ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
    intro t ht
    exact mem_normalizer_inf (hNQ t) (hTC t ht)
  have hUp : IsPGroup 3 (Q ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) := by
    intro g
    obtain ⟨k, hk⟩ := hQ ⟨(g : X), (Subgroup.mem_inf.mp g.2).1⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  have hcentU : T ≤ Subgroup.centralizer
      ((Q ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
    refine le_centralizer_of_fix_order_three hUp hT hTU ?_
    intro t ht u hu hu3
    have huQ : u ∈ Q := (Subgroup.mem_inf.mp hu).1
    have huC : ∀ a ∈ A, a * u = u * a := fun a ha =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 a ha
    have huA : u ∈ A := hA3 u huQ hu3 huC
    rw [hTB t ht u (Subgroup.mem_inf.mpr ⟨huA, huQ⟩), mul_inv_cancel_right]
  have hfix : Q ⊓ Subgroup.centralizer (A : Set X) ≤ Subgroup.centralizer (T : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hcentU ht) y hy).symm
  have hTcard : Nat.Coprime (Nat.card T) 3 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hT
    rw [hn]
    exact Nat.Coprime.pow_left n (by norm_num)
  have hTA_bot : ⁅T, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm T A]
    exact hAT0
  have hQT : Q ≤ Subgroup.centralizer (T : Set X) :=
    centralizes_of_thompson_AxB hQ hTcard hA
      (by intro t _; exact hNQ t) (by intro a _; exact hNQ a) hTA_bot hfix
  have hTbot : T ≤ ⊥ := by
    intro t ht
    have htQ : t ∈ Q := hCQ (Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (hQT hq) t ht).symm)
    exact Subgroup.mem_bot.mpr (hTQ t ht htQ)
  exact eq_bot_iff.mpr hTbot

end CFSG.RankThree.PartTwo.Sec18.Item188Proof
