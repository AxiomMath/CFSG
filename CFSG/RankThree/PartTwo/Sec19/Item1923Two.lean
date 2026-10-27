module

import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec3.Sims321
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.RankThree.PartTwo.Sec19.Item1923Plane
public import CFSG.RankThree.PartTwo.Sec19.Item1923Rank
import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem item1923Two_mk_eq_one_iff {M : Subgroup G} {g : G} (hg : g ∈ M) :
    QuotientGroup.mk' (CFSG.pCore 2 M) (⟨g, hg⟩ : M) = 1 ↔ g ∈ CFSG.Open.pCoreOf 2 M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, CFSG.Open.pCoreOf, Subgroup.mem_map]
  refine ⟨fun h => ⟨⟨g, hg⟩, h, rfl⟩, ?_⟩
  rintro ⟨x, hx, hxg⟩
  have hx' : x = ⟨g, hg⟩ := Subtype.ext hxg
  rwa [hx'] at hx

private theorem item1923Two_mem_pCoreOf_of_mem {M K : Subgroup G} (hKM : K ≤ M) {g : G}
    (hgK : g ∈ K) (hgP : g ∈ CFSG.Open.pCoreOf 2 M) : g ∈ CFSG.Open.pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTn : ((CFSG.Open.pCoreOf 2 M).subgroupOf K).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hxN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM x.2)
    have := (Subgroup.mem_normalizer_iff.mp hxN (n : G)).mp hn
    simpa [mul_assoc] using this
  have hTp : IsPGroup 2 ((CFSG.Open.pCoreOf 2 M).subgroupOf K) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).comap_subtype
  have hle := CFSG.LieType.BorelTits.le_pCore 2 hTn hTp
  have hmem : (⟨g, hgK⟩ : K) ∈ CFSG.pCore 2 K := hle (Subgroup.mem_subgroupOf.mpr hgP)
  rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
  exact ⟨⟨g, hgK⟩, hmem, rfl⟩

private theorem item1923Two_mem_sup_decomp {M K : Subgroup G} (hKM : K ≤ M) {b : G}
    (hb : b ∈ K ⊔ CFSG.Open.pCoreOf 2 M) :
    ∃ k ∈ K, ∃ p ∈ CFSG.Open.pCoreOf 2 M, b = k * p := by
  have hnorm : ∀ x ∈ K, ∀ p ∈ CFSG.Open.pCoreOf 2 M,
      x * p * x⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun x hx p hp =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hx)) p).mp hp
  rw [Subgroup.sup_eq_closure] at hb
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hxK | hxP
    · exact ⟨x, hxK, 1, one_mem _, by simp⟩
    · exact ⟨1, one_mem _, x, hxP, by simp⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k1, hk1, p1, hp1, rfl⟩ := hx
    obtain ⟨k2, hk2, p2, hp2, rfl⟩ := hy
    refine ⟨k1 * k2, mul_mem hk1 hk2, (k2⁻¹ * p1 * k2) * p2, ?_, ?_⟩
    · exact mul_mem (by simpa using hnorm k2⁻¹ (inv_mem hk2) p1 hp1) hp2
    · group
  | inv x _ hx =>
    obtain ⟨k, hk, p, hp, rfl⟩ := hx
    refine ⟨k⁻¹, inv_mem hk, k * p⁻¹ * k⁻¹, hnorm k hk p⁻¹ (inv_mem hp), ?_⟩
    group

private theorem item1923Two_exists_iota {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) :
    ∃ ι : (K ⧸ CFSG.pCore 2 K) →* (M ⧸ CFSG.pCore 2 M), Function.Injective ι ∧
      ∀ k : K, ι (QuotientGroup.mk k) =
        QuotientGroup.mk' (CFSG.pCore 2 M) (⟨k.1, le_of_mem_oTwoComponentsIn hK k.2⟩ : M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  let ψ : K →* (M ⧸ CFSG.pCore 2 M) :=
    (QuotientGroup.mk' (CFSG.pCore 2 M)).comp (Subgroup.inclusion hKM)
  have hψ : ∀ k : K, ψ k = QuotientGroup.mk' (CFSG.pCore 2 M) (⟨k.1, hKM k.2⟩ : M) :=
    fun k => rfl
  have hle : CFSG.pCore 2 K ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ, item1923Two_mk_eq_one_iff (hKM x.2)]
    have hxK : (x : G) ∈ CFSG.Open.pCoreOf 2 K := ⟨x, hx, rfl⟩
    exact CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK hxK
  have hinj : Function.Injective (QuotientGroup.lift (CFSG.pCore 2 K) ψ hle) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.lift_mk, hψ, item1923Two_mk_eq_one_iff (hKM k.2)] at hy
    rw [QuotientGroup.eq_one_iff]
    have hkK : (k : G) ∈ CFSG.Open.pCoreOf 2 K :=
      item1923Two_mem_pCoreOf_of_mem hKM k.2 hy
    obtain ⟨q, hq, hqk⟩ := Subgroup.mem_map.mp hkK
    have hqk' : q = k := Subtype.ext hqk
    rwa [← hqk']
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 K) ψ hle, hinj, fun k => ?_⟩
  rw [QuotientGroup.lift_mk, hψ]

private theorem item1923Two_barQ_commute {M X Y : Subgroup G}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    {a b : M ⧸ CFSG.pCore 2 M}
    (ha : a ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (X.subgroupOf M))
    (hb : b ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (Y.subgroupOf M)) :
    a * b = b * a := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hb
  have hc := hXY (m : G) (Subgroup.mem_subgroupOf.mp hm) (n : G) (Subgroup.mem_subgroupOf.mp hn)
  rw [CFSG.Open.pCoreOf, Subgroup.mem_map] at hc
  obtain ⟨q, hq, hqe⟩ := hc
  have hq' : q = m * n * m⁻¹ * n⁻¹ := Subtype.ext (by simpa using hqe)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 M) (m * n * m⁻¹ * n⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hq']
    exact hq
  simp only [map_mul, map_inv] at h1
  calc QuotientGroup.mk' (CFSG.pCore 2 M) m * QuotientGroup.mk' (CFSG.pCore 2 M) n
      = (QuotientGroup.mk' (CFSG.pCore 2 M) m * QuotientGroup.mk' (CFSG.pCore 2 M) n *
          (QuotientGroup.mk' (CFSG.pCore 2 M) m)⁻¹ * (QuotientGroup.mk' (CFSG.pCore 2 M) n)⁻¹) *
          (QuotientGroup.mk' (CFSG.pCore 2 M) n * QuotientGroup.mk' (CFSG.pCore 2 M) m) := by
        group
    _ = QuotientGroup.mk' (CFSG.pCore 2 M) n * QuotientGroup.mk' (CFSG.pCore 2 M) m := by
        rw [h1, one_mul]

private theorem item1923Two_comm_of_isElemAbelian {Γ : Type*} [Group Γ] {p : ℕ} {E : Subgroup Γ}
    (hE : CFSG.Open.IsElemAbelian p E) {a b : Γ} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)

private theorem item1923Two_isElemAbelian_mono {Γ : Type*} [Group Γ] {p : ℕ}
    {E F : Subgroup Γ} (hEF : E ≤ F) (hF : CFSG.Open.IsElemAbelian p F) :
    CFSG.Open.IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (item1923Two_comm_of_isElemAbelian hF (hEF a.2) (hEF b.2))⟩⟩,
    fun x hx => hF.2 x (hEF hx)⟩

private theorem item1923Two_isElemAbelian_of {Γ : Type*} [Group Γ] {p : ℕ} {E : Subgroup Γ}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : ∀ x ∈ E, x ^ p = 1) :
    CFSG.Open.IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)⟩⟩, hp⟩

private theorem item1923Two_barQ_isElemAbelian {M E : Subgroup G} (hEM : E ≤ M)
    (hE : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3
        (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (E.subgroupOf M)) ∧
      Nat.card ↥(Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (E.subgroupOf M)) =
        Nat.card E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 M)).comp (E.subgroupOf M).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hxE⟩ hx
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 M) x = 1 := hx
    have hxq : x ∈ CFSG.pCore 2 M := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx'
    have hx3 : x ^ 3 = 1 := Subtype.ext (by
      simpa using hE.2 (x : G) (Subgroup.mem_subgroupOf.mp hxE))
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := M)) ⟨x, hxq⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have hg := (pow_gcd_eq_one (a := x) (m := 3) (n := 2 ^ k)).mpr ⟨hx3, hk'⟩
    rw [show Nat.gcd 3 (2 ^ k) = 1 from hcop, pow_one] at hg
    exact Subtype.ext hg
  constructor
  · refine item1923Two_isElemAbelian_of (p := 3) ?_ ?_
    · intro a ha b hb
      refine item1923Two_barQ_commute (fun x hx y hy => ?_) ha hb
      rw [show x * y * x⁻¹ * y⁻¹ = 1 by rw [item1923Two_comm_of_isElemAbelian hE hx hy]; group]
      exact one_mem _
    · intro x hx
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow]
      have hm3 : m ^ 3 = 1 := Subtype.ext (by
        simpa using hE.2 (m : G) (Subgroup.mem_subgroupOf.mp hm))
      rw [hm3, map_one]
  · have hrange : ((QuotientGroup.mk' (CFSG.pCore 2 M)).comp (E.subgroupOf M).subtype).range =
        Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (E.subgroupOf M) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv]

private theorem item1923Two_sup_elemAbelian {Γ : Type*} [Group Γ] {H₁ H₂ : Subgroup Γ}
    (h₁ : CFSG.Open.IsElemAbelian 3 H₁) (h₂ : CFSG.Open.IsElemAbelian 3 H₂)
    (hc : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) (hint : H₁ ⊓ H₂ = ⊥) :
    CFSG.Open.IsElemAbelian 3 (H₁ ⊔ H₂) ∧ Nat.card ↥(H₁ ⊔ H₂) = Nat.card H₁ * Nat.card H₂ ∧
      ∀ x ∈ H₁ ⊔ H₂, ∃ a ∈ H₁, ∃ b ∈ H₂, x = a * b := by
  let Φ : H₁ × H₂ →* Γ :=
    { toFun := fun p => (p.1 : Γ) * (p.2 : Γ)
      map_one' := by simp
      map_mul' := fun p q => by
        have hqp : (q.1 : Γ) * (p.2 : Γ) = (p.2 : Γ) * (q.1 : Γ) := hc _ q.1.2 _ p.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (p.1 : Γ) * (q.1 : Γ) * ((p.2 : Γ) * (q.2 : Γ))
            = (p.1 : Γ) * ((q.1 : Γ) * (p.2 : Γ)) * (q.2 : Γ) := by group
          _ = (p.1 : Γ) * ((p.2 : Γ) * (q.1 : Γ)) * (q.2 : Γ) := by rw [hqp]
          _ = (p.1 : Γ) * (p.2 : Γ) * ((q.1 : Γ) * (q.2 : Γ)) := by group }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : Γ) * (b : Γ) = 1 := hab
    have ha2 : (a : Γ) ∈ H₂ := by
      rw [eq_inv_of_mul_eq_one_left hab']
      exact inv_mem b.2
    have ha0 : a = 1 := by
      have hmem : (a : Γ) ∈ H₁ ⊓ H₂ := ⟨a.2, ha2⟩
      rw [hint, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    subst ha0
    have hb0 : b = 1 := Subtype.ext (by simpa using hab')
    subst hb0
    rfl
  have hrange : Φ.range = H₁ ⊔ H₂ := by
    apply le_antisymm
    · intro y hy
      obtain ⟨⟨a, b⟩, rfl⟩ := MonoidHom.mem_range.mp hy
      exact mul_mem (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2)
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact MonoidHom.mem_range.mpr ⟨(⟨x, hx⟩, 1), by simp [Φ]⟩
      · exact MonoidHom.mem_range.mpr ⟨(1, ⟨x, hx⟩), by simp [Φ]⟩
  have hcard : Nat.card ↥(H₁ ⊔ H₂) = Nat.card H₁ * Nat.card H₂ := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv.symm, Nat.card_prod]
  have hdec : ∀ x ∈ H₁ ⊔ H₂, ∃ a ∈ H₁, ∃ b ∈ H₂, x = a * b := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨⟨a, b⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨a, a.2, b, b.2, rfl⟩
  have hcomm : ∀ x ∈ H₁ ⊔ H₂, ∀ y ∈ H₁ ⊔ H₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec y hy
    have h1 : a * a' = a' * a := item1923Two_comm_of_isElemAbelian h₁ ha ha'
    have h2 : b * b' = b' * b := item1923Two_comm_of_isElemAbelian h₂ hb hb'
    have h3 : b * a' = a' * b := (hc a' ha' b hb).symm
    have h4 : b' * a = a * b' := (hc a ha b' hb').symm
    calc a * b * (a' * b') = (a * a') * (b * b') := by
          calc a * b * (a' * b') = a * (b * a') * b' := by group
            _ = a * (a' * b) * b' := by rw [h3]
            _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [h1, h2]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [← h4]
      _ = a' * b' * (a * b) := by group
  have hexp : ∀ x ∈ H₁ ⊔ H₂, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    have hab : Commute a b := hc a ha b hb
    rw [hab.mul_pow, h₁.2 a ha, h₂.2 b hb, one_mul]
  exact ⟨item1923Two_isElemAbelian_of hcomm hexp, hcard, hdec⟩

private theorem item1923Two_zpowers {r : G} (hr : orderOf r = 3) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers r) ∧ Nat.card ↥(Subgroup.zpowers r) = 3 := by
  have hr3 : r ^ 3 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
  refine ⟨item1923Two_isElemAbelian_of (fun a ha b hb => ?_) (fun x hx => ?_), ?_⟩
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hr3, one_zpow]
  · rw [Nat.card_zpowers, hr]

private theorem item1923Two_isElemAbelian_map {Γ Δ : Type*} [Group Γ] [Group Δ] {D : Subgroup Γ}
    (f : Γ →* Δ) (hf : Function.Injective f) (hD : CFSG.Open.IsElemAbelian 3 D) :
    CFSG.Open.IsElemAbelian 3 (D.map f) := by
  refine item1923Two_isElemAbelian_of (fun a ha b hb => ?_) (fun x hx => ?_)
  · obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, item1923Two_comm_of_isElemAbelian hD ha' hb']
  · obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hD.2 a' ha', map_one]

private theorem item1923Two_isElemAbelian_of_mulEquiv {Γ Δ : Type*} [Group Γ] [Group Δ]
    {D : Subgroup Γ} {F : Subgroup Δ} (e : D ≃* F) (hF : CFSG.Open.IsElemAbelian 3 F) :
    CFSG.Open.IsElemAbelian 3 D := by
  refine item1923Two_isElemAbelian_of (fun a ha b hb => ?_) (fun x hx => ?_)
  · have hab : (⟨a, ha⟩ : D) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      exact item1923Two_comm_of_isElemAbelian hF (e ⟨a, ha⟩).2 (e ⟨b, hb⟩).2
    exact congrArg Subtype.val hab
  · have h1 : e ⟨x, hx⟩ ^ 3 = 1 := Subtype.ext (by
      simpa using hF.2 _ (e ⟨x, hx⟩).2)
    have h2 : (⟨x, hx⟩ : D) ^ 3 = 1 := e.injective (by rw [map_pow, h1, map_one])
    exact congrArg Subtype.val h2

private theorem item1923Two_iota_mem {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    {ι : (K ⧸ CFSG.pCore 2 K) →* (M ⧸ CFSG.pCore 2 M)}
    (hιmk : ∀ k : K, ι (QuotientGroup.mk k) =
      QuotientGroup.mk' (CFSG.pCore 2 M) (⟨k.1, le_of_mem_oTwoComponentsIn hK k.2⟩ : M))
    (w : K ⧸ CFSG.pCore 2 K) :
    ι w ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (K.subgroupOf M) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
  rw [hιmk k]
  exact Subgroup.mem_map.mpr ⟨⟨k.1, le_of_mem_oTwoComponentsIn hK k.2⟩,
    Subgroup.mem_subgroupOf.mpr k.2, rfl⟩

private theorem item1923Two_false_of_sub (kf2 : KF2) (h194 : Item194UsedWide3)
    (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) {K : Subgroup G}
    (hK : K ∈ scriptJ M N)
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hsub : ∀ b ∈ A ⊓ L, b ∈ K ⊔ CFSG.Open.pCoreOf 2 M) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, hιinj, hιmk⟩ := item1923Two_exists_iota hK.1
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK.1
  have hAM : A ⊓ L ≤ M := inf_le_left.trans h.le_M
  have hBι : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) ((A ⊓ L).subgroupOf M) ≤
      ι.range := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk, p, hp, hbkp⟩ :=
      item1923Two_mem_sup_decomp hKM (hsub (b : G) (Subgroup.mem_subgroupOf.mp hb))
    have hpM : p ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hp
    have hbeq : b = (⟨k, hKM hk⟩ : M) * ⟨p, hpM⟩ := Subtype.ext (by simp [hbkp])
    have hp1 : QuotientGroup.mk' (CFSG.pCore 2 M) (⟨p, hpM⟩ : M) = 1 :=
      (item1923Two_mk_eq_one_iff hpM).mpr hp
    refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk (⟨k, hk⟩ : K), ?_⟩
    rw [hιmk ⟨k, hk⟩, hbeq, map_mul, hp1, mul_one]
  have hZc : (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) ((A ⊓ L).subgroupOf M)).comap ι ≤
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hcomm := item1923Two_barQ_commute (X := A ⊓ L) (Y := K)
      (fun x hx y hy => CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn
        hK.1 (hone x hx y hy))
      (Subgroup.mem_comap.mp hz) (item1923Two_iota_mem hK.1 hιmk w)
    apply hιinj
    rw [map_mul, map_mul]
    exact hcomm.symm
  have hlist : InK194 (K ⧸ CFSG.pCore 2 K) := (step1923_list h194 h hK).1
  have hcardB : Nat.card ↥(Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M))
      ((A ⊓ L).subgroupOf M)) = 9 := by
    have hab : CFSG.Open.IsElemAbelian 3 (A ⊓ L) :=
      item1923Two_isElemAbelian_mono inf_le_left h.isE27.1
    rw [(item1923Two_barQ_isElemAbelian hAM hab).2, hF.card]
  have hZcard : Nat.card ↥((Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M))
      ((A ⊓ L).subgroupOf M)).comap ι) = 9 := by
    rw [← Subgroup.card_map_of_injective hιinj, Subgroup.map_comap_eq,
      inf_eq_right.mpr hBι, hcardB]
  have h9 : 9 ∣ 3 := by
    rw [← hZcard]
    exact (Subgroup.card_dvd_of_le hZc).trans (kf2 _ hlist).1
  norm_num at h9

private theorem item1923Two_inf_eq_bot (kf2 : KF2) (h194 : Item194UsedWide3)
    (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) {K : Subgroup G}
    (hK : K ∈ scriptJ M N)
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    {b : G} (hb : b ∈ A ⊓ L) (hbK : b ∈ K ⊔ CFSG.Open.pCoreOf 2 M) : b = 1 := by
  have hirr := (step1923_irreducible h hF hK.1).1
  have hW := step1923_W_le h hF
  have hconj : ∀ g ∈ planeGroup A L c ⊓ Subgroup.normalizer (K : Set G),
      ∀ x ∈ (A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M),
        g * x * g⁻¹ ∈ (A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M) := by
    rintro g ⟨hgP, hgK⟩ x ⟨hxB, hxKP⟩
    have hgPl : g ∈ L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({c} : Set G) := hgP
    have hgM : g ∈ M := (hW hgP).1.2
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgPl.1.2 x).mp hxB, ?_⟩
    have hgP' : g ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hgM
    have hsub : K ⊔ CFSG.Open.pCoreOf 2 M ≤
        (K ⊔ CFSG.Open.pCoreOf 2 M).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun k hk => ?_) (fun p hp => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hgK k).mp hk)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hgP' p).mp hp)
    have hx' := hsub hxKP
    rw [Subgroup.mem_comap] at hx'
    exact hx'
  have hS : ∀ φ ∈ Sec4.autIn (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)) (A ⊓ L),
      ∀ x ∈ ((A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M)).subgroupOf (A ⊓ L),
        φ x ∈ ((A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M)).subgroupOf (A ⊓ L) := by
    intro φ hφ x hx
    obtain ⟨g, hgN, hgH, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [Sec4.normalizerMonoidHom_apply_coe hgN x]
    exact hconj g hgH x hx
  have hinv : ∀ φ ∈ Sec4.autIn (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)) (A ⊓ L),
      Subgroup.map φ.toMonoidHom (((A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M)).subgroupOf (A ⊓ L)) =
        ((A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M)).subgroupOf (A ⊓ L) := by
    intro φ hφ
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact hS φ hφ x hx
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨φ⁻¹ x, hS φ⁻¹ (inv_mem hφ) x hx, ?_⟩
      show φ (φ⁻¹ x) = x
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rcases hirr (((A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M)).subgroupOf (A ⊓ L)) hinv with hbot | htop
  · have hmem : (⟨b, hb⟩ : ↥(A ⊓ L)) ∈
        ((A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M)).subgroupOf (A ⊓ L) := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hb, hbK⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    refine item1923Two_false_of_sub kf2 h194 h hF hK hone (fun b' hb' => ?_)
    have hall : (⟨b', hb'⟩ : ↥(A ⊓ L)) ∈
        ((A ⊓ L) ⊓ (K ⊔ CFSG.Open.pCoreOf 2 M)).subgroupOf (A ⊓ L) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hall).2

private theorem item1923Two_barQ_inf_eq_bot (kf2 : KF2) (h194 : Item194UsedWide3)
    (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) {K : Subgroup G}
    (hK : K ∈ scriptJ M N)
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) ((A ⊓ L).subgroupOf M) ⊓
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (K.subgroupOf M) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxB, hxK⟩ := hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hxB
  obtain ⟨k, hk, hkb⟩ := Subgroup.mem_map.mp hxK
  have hbk1 : QuotientGroup.mk' (CFSG.pCore 2 M) (b * k⁻¹) = 1 := by
    rw [map_mul, map_inv, hkb, mul_inv_cancel]
  have hgP : ((b * k⁻¹ : M) : G) ∈ CFSG.Open.pCoreOf 2 M :=
    (item1923Two_mk_eq_one_iff (b * k⁻¹).2).mp hbk1
  have hbKP : (b : G) ∈ K ⊔ CFSG.Open.pCoreOf 2 M := by
    have hbe : (b : G) = ((b * k⁻¹ : M) : G) * (k : G) := by simp
    rw [hbe]
    exact mul_mem (Subgroup.mem_sup_right hgP)
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk))
  have hb1 : (b : G) = 1 :=
    item1923Two_inf_eq_bot kf2 h194 h hF hK hone (Subgroup.mem_subgroupOf.mp hb) hbKP
  have hb1' : b = 1 := Subtype.ext (by simpa using hb1)
  rw [Subgroup.mem_bot, hb1', map_one]

private theorem item1923Two_bot_isElemAbelian {Γ : Type*} [Group Γ] (p : ℕ) :
    CFSG.Open.IsElemAbelian p (⊥ : Subgroup Γ) :=
  item1923Two_isElemAbelian_of (fun a ha b hb => by
      rw [Subgroup.mem_bot] at ha hb
      simp [ha, hb]) (fun x hx => by
      rw [Subgroup.mem_bot] at hx
      simp [hx])

private theorem item1923Two_pRank_le_one (kf2 : KF2) (h194 : Item194UsedWide3)
    (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) {K : Subgroup G}
    (hK : K ∈ scriptJ M N)
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    CFSG.Open.pRank 3 K ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK.1
  have hAM : A ⊓ L ≤ M := inf_le_left.trans h.le_M
  have hmem : CFSG.Open.pRank 3 K ∈ {k : ℕ | ∃ E : Subgroup G, E ≤ K ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} :=
    Nat.sSup_mem ⟨0, ⊥, bot_le, item1923Two_bot_isElemAbelian 3, by simp⟩
      (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three K)
  obtain ⟨E, hEK, hE, hEcard⟩ := hmem
  have hEM : E ≤ M := hEK.trans hKM
  obtain ⟨hEQ, hEQcard⟩ := item1923Two_barQ_isElemAbelian hEM hE
  have hBab : CFSG.Open.IsElemAbelian 3 (A ⊓ L) :=
    item1923Two_isElemAbelian_mono inf_le_left h.isE27.1
  obtain ⟨hBQ, hBQcard⟩ := item1923Two_barQ_isElemAbelian hAM hBab
  have hcomm : ∀ x ∈ A ⊓ L, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    fun x hx y hy => CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn
      hK.1 (hone x hx y (hEK hy))
  have hle : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (E.subgroupOf M) ≤
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (K.subgroupOf M) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M hEK)
  have hint : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) ((A ⊓ L).subgroupOf M) ⊓
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (E.subgroupOf M) = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf_left _ hle).trans
      (item1923Two_barQ_inf_eq_bot kf2 h194 h hF hK hone).le
  obtain ⟨hPab, hPcard, -⟩ := item1923Two_sup_elemAbelian hBQ hEQ
    (fun a ha b hb => item1923Two_barQ_commute hcomm ha hb) hint
  have hle27 := Hyp1921.card_le_of_isElemAbelian_quotient h hPab
  rw [hPcard, hBQcard, hEQcard, hEcard, hF.card] at hle27
  have h9 : 9 * 3 ^ CFSG.Open.pRank 3 K ≤ 9 * 3 := le_trans hle27 (by norm_num)
  have h3m : 3 ^ CFSG.Open.pRank 3 K ≤ 3 ^ 1 := by
    rw [pow_one]
    exact Nat.le_of_mul_le_mul_left h9 (by norm_num)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3m

private theorem item1923Two_central_eq_one {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hL : IsL3OddType (K ⧸ CFSG.pCore 2 K)) {z : M ⧸ CFSG.pCore 2 M}
    (hz : z ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (K.subgroupOf M))
    (hzc : ∀ y ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (K.subgroupOf M),
      z * y = y * z) : z = 1 := by
  obtain ⟨ι, hιinj, hιmk⟩ := item1923Two_exists_iota hK
  obtain ⟨n, -, ⟨e⟩⟩ := hL
  obtain ⟨kM, hkM, rfl⟩ := Subgroup.mem_map.mp hz
  have hιx : ι (QuotientGroup.mk (⟨kM.1, Subgroup.mem_subgroupOf.mp hkM⟩ : K)) =
      QuotientGroup.mk' (CFSG.pCore 2 M) kM := hιmk _
  have hcen : QuotientGroup.mk (⟨kM.1, Subgroup.mem_subgroupOf.mp hkM⟩ : K) ∈
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply hιinj
    rw [map_mul, map_mul, hιx]
    exact (hzc (ι w) (item1923Two_iota_mem hK hιmk w)).symm
  have hx1 : (QuotientGroup.mk (⟨kM.1, Subgroup.mem_subgroupOf.mp hkM⟩ : K) :
      K ⧸ CFSG.pCore 2 K) = 1 := by
    have hbot := CFSG.RankThree.PartTwo.Sec3.Sims321.center_quot_eq_bot e
    rw [hbot] at hcen
    exact hcen
  rw [← hιx, hx1, map_one]

private theorem item1923Two_isL3odd (kf3a : KF3a) (kf2 : KF2) (h194 : Item194UsedWide3)
    (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) {K : Subgroup G}
    (hK : K ∈ scriptJ M N)
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    IsL3OddType (K ⧸ CFSG.pCore 2 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  have hlist : InK194 (K ⧸ CFSG.pCore 2 K) := (step1923_list h194 h hK).1
  have h2 := kf3a _ hlist hnot
  have hmem : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) ∈
      {k : ℕ | ∃ F : Subgroup (K ⧸ CFSG.pCore 2 K), F ≤ ⊤ ∧
        CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 3 ^ k} :=
    Nat.sSup_mem ⟨0, ⊥, bot_le, item1923Two_bot_isElemAbelian 3, by simp⟩
      (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three ⊤)
  obtain ⟨F, -, hF3, hFcard⟩ := hmem
  have hcop : Nat.Coprime 3 (Nat.card ↥(CFSG.pCore 2 K)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := K))
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hFp : IsPGroup 3 F := IsPGroup.of_card hFcard
  obtain ⟨D, -, ⟨eD⟩, -⟩ :=
    CFSG.GroupTheory.exists_isPGroup_of_coprime_kernel (CFSG.pCore 2 K) Nat.prime_three hcop hFp
  have hDab : CFSG.Open.IsElemAbelian 3 D := item1923Two_isElemAbelian_of_mulEquiv eD hF3
  have hEab := item1923Two_isElemAbelian_map K.subtype K.subtype_injective hDab
  have hEcard : Nat.card ↥(D.map K.subtype) =
      3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, Nat.card_congr eD.toEquiv, hFcard]
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) ≤ CFSG.Open.pRank 3 K :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three K)
      ⟨D.map K.subtype, Subgroup.map_subtype_le D, hEab, hEcard⟩
  have h1 := item1923Two_pRank_le_one kf2 h194 h hF hK hone
  omega

private theorem item1923Two_exists_order_three {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hL : IsL3OddType (K ⧸ CFSG.pCore 2 K)) :
    ∃ r ∈ K, orderOf r = 3 ∧ 1 ≤ CFSG.Open.pRank 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, -, ⟨e⟩⟩ := hL
  have h3 : 3 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) :=
    CFSG.RankThree.PartTwo.KFacts.three_dvd_card_of_mulEquiv_projSL e
  have h3K : 3 ∣ Nat.card ↥K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 K)]
    exact h3.mul_right _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
  have hr : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  refine ⟨x, x.2, hr, ?_⟩
  have hmem : (1 : ℕ) ∈ {k : ℕ | ∃ E : Subgroup G, E ≤ K ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} :=
    ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.mpr x.2,
      (item1923Two_zpowers hr).1, by rw [(item1923Two_zpowers hr).2, pow_one]⟩
  exact le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three K)
    hmem

private theorem item1923Two_false_of_two (kf2 : KF2) (kf3a : KF3a) (h194 : Item194UsedWide3)
    (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) {K K' : Subgroup G}
    (hK : K ∈ scriptJ M N) (hK' : K' ∈ scriptJ M N) (hne : K ≠ K')
    (hone : ∀ K'' ∈ scriptJ M N, ∀ b ∈ A ⊓ L, ∀ k ∈ K'',
      b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K'') : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have honeK : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
    fun b hb k hk => hone K hK b hb k hk
  have honeK' : ∀ b ∈ A ⊓ L, ∀ k ∈ K', b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K' :=
    fun b hb k hk => hone K' hK' b hb k hk
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK.1
  have hKM' : K' ≤ M := le_of_mem_oTwoComponentsIn hK'.1
  have hAM : A ⊓ L ≤ M := inf_le_left.trans h.le_M
  have hL : IsL3OddType (K ⧸ CFSG.pCore 2 K) :=
    item1923Two_isL3odd kf3a kf2 h194 h hF hK honeK
  have hL' : IsL3OddType (K' ⧸ CFSG.pCore 2 K') :=
    item1923Two_isL3odd kf3a kf2 h194 h hF hK' honeK'
  obtain ⟨r, hrK, hr3, -⟩ := item1923Two_exists_order_three hK.1 hL
  obtain ⟨r', hrK', hr3', -⟩ := item1923Two_exists_order_three hK'.1 hL'
  have hrK0 : Subgroup.zpowers r ≤ K := Subgroup.zpowers_le.mpr hrK
  have hrK0' : Subgroup.zpowers r' ≤ K' := Subgroup.zpowers_le.mpr hrK'
  have hrM : Subgroup.zpowers r ≤ M := hrK0.trans hKM
  have hr'M : Subgroup.zpowers r' ≤ M := hrK0'.trans hKM'
  obtain ⟨hRQab, hRQcard⟩ := item1923Two_barQ_isElemAbelian hrM (item1923Two_zpowers hr3).1
  obtain ⟨hR'Qab, hR'Qcard⟩ :=
    item1923Two_barQ_isElemAbelian hr'M (item1923Two_zpowers hr3').1
  rw [(item1923Two_zpowers hr3).2] at hRQcard
  rw [(item1923Two_zpowers hr3').2] at hR'Qcard
  have hBab : CFSG.Open.IsElemAbelian 3 (A ⊓ L) :=
    item1923Two_isElemAbelian_mono inf_le_left h.isE27.1
  obtain ⟨hBQab, hBQcard⟩ := item1923Two_barQ_isElemAbelian hAM hBab
  rw [hF.card] at hBQcard
  have hBK : ∀ x ∈ A ⊓ L, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun x hx y hy =>
    CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK.1
      (honeK x hx y hy)
  have hBK' : ∀ x ∈ A ⊓ L, ∀ y ∈ K', x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun x hx y hy =>
    CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK'.1
      (honeK' x hx y hy)
  have hKK' : ∀ x ∈ K, ∀ y ∈ K', x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun x hx y hy =>
    CFSG.RankThree.PartTwo.Sec19.Step1910Proof.commutator_mem_pCoreOf hK.1 hK'.1 hne hx hy
  set BQ := Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) ((A ⊓ L).subgroupOf M) with hBQdef
  set RQ := Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M))
    ((Subgroup.zpowers r).subgroupOf M) with hRQdef
  set R'Q := Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M))
    ((Subgroup.zpowers r').subgroupOf M) with hR'Qdef
  set KQ := Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (K.subgroupOf M) with hKQdef
  set K'Q := Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 M)) (K'.subgroupOf M) with hK'Qdef
  have hRK : RQ ≤ KQ := Subgroup.map_mono (Subgroup.subgroupOf_mono M hrK0)
  have hR'K' : R'Q ≤ K'Q := Subgroup.map_mono (Subgroup.subgroupOf_mono M hrK0')
  have hBQR : ∀ a ∈ BQ, ∀ b ∈ RQ, a * b = b * a := fun a ha b hb =>
    item1923Two_barQ_commute (fun x hx y hy => hBK x hx y (hrK0 hy)) ha hb
  have hBQR' : ∀ a ∈ BQ, ∀ b ∈ R'Q, a * b = b * a := fun a ha b hb =>
    item1923Two_barQ_commute (fun x hx y hy => hBK' x hx y (hrK0' hy)) ha hb
  have hRQR' : ∀ a ∈ RQ, ∀ b ∈ R'Q, a * b = b * a := fun a ha b hb =>
    item1923Two_barQ_commute (fun x hx y hy => hKK' x (hrK0 hx) y (hrK0' hy)) ha hb
  have hBKQ : ∀ a ∈ BQ, ∀ b ∈ KQ, a * b = b * a := fun a ha b hb =>
    item1923Two_barQ_commute hBK ha hb
  have hKK'Q : ∀ a ∈ KQ, ∀ b ∈ K'Q, a * b = b * a := fun a ha b hb =>
    item1923Two_barQ_commute hKK' ha hb
  have hBRinf : BQ ⊓ RQ = ⊥ := le_antisymm
    ((inf_le_inf_left _ hRK).trans (item1923Two_barQ_inf_eq_bot kf2 h194 h hF hK honeK).le) bot_le
  have hBR'inf : BQ ⊓ R'Q = ⊥ := le_antisymm
    ((inf_le_inf_left _ hR'K').trans (item1923Two_barQ_inf_eq_bot kf2 h194 h hF hK' honeK').le)
    bot_le
  obtain ⟨hP1ab, hP1card, hP1dec⟩ := item1923Two_sup_elemAbelian hBQab hRQab hBQR hBRinf
  rw [hBQcard, hRQcard] at hP1card
  have hP1R' : (BQ ⊔ RQ) ⊓ R'Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP1, hxR'⟩ := hx
    obtain ⟨b, hb, ρ, hρ, hxbρ⟩ := hP1dec x hxP1
    have hρc : ∀ y ∈ KQ, ρ * y = y * ρ := by
      intro y hy
      have hby : b * y = y * b := hBKQ b hb y hy
      have hyx : y * x = x * y := hKK'Q y hy x (hR'K' hxR')
      have key : b * (y * ρ) = b * (ρ * y) := by
        calc b * (y * ρ) = (b * y) * ρ := by group
          _ = (y * b) * ρ := by rw [hby]
          _ = y * (b * ρ) := by group
          _ = y * x := by rw [hxbρ]
          _ = x * y := hyx
          _ = (b * ρ) * y := by rw [hxbρ]
          _ = b * (ρ * y) := by group
      exact (mul_left_cancel key).symm
    have hρ1 : ρ = 1 :=
      item1923Two_central_eq_one hK.1 hL (hRK hρ) hρc
    have hxB : x ∈ BQ := by
      rw [hxbρ, hρ1, mul_one]
      exact hb
    have hmem : x ∈ BQ ⊓ R'Q := ⟨hxB, hxR'⟩
    rw [hBR'inf, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr hmem
  have hc2 : ∀ a ∈ BQ ⊔ RQ, ∀ b ∈ R'Q, a * b = b * a := by
    intro a ha b hb
    obtain ⟨b1, hb1, ρ1, hρ1, rfl⟩ := hP1dec a ha
    calc b1 * ρ1 * b = b1 * (ρ1 * b) := by group
      _ = b1 * (b * ρ1) := by rw [hRQR' ρ1 hρ1 b hb]
      _ = (b1 * b) * ρ1 := by group
      _ = (b * b1) * ρ1 := by rw [hBQR' b1 hb1 b hb]
      _ = b * (b1 * ρ1) := by group
  obtain ⟨hP2ab, hP2card, -⟩ := item1923Two_sup_elemAbelian hP1ab hR'Qab hc2 hP1R'
  have hle81 := Hyp1921.card_le_of_isElemAbelian_quotient h hP2ab
  rw [hP2card, hP1card, hR'Qcard] at hle81
  norm_num at hle81

theorem item1923_two (kf3a : KF3a) (kf2 : KF2) (h194 : Item194UsedWide3) (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) (hK : K ∈ scriptJ M N)
    (hone : ∀ K' ∈ scriptJ M N, ∀ b ∈ A ⊓ L, ∀ k ∈ K',
      b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K') :
    scriptJ M N = {K} ∧ CFSG.Open.pRank 3 K = 1 ∧ IsL3OddType (K ⧸ CFSG.pCore 2 K) := by
  have hone' : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
    fun b hb k hk => hone K hK b hb k hk
  have hL : IsL3OddType (K ⧸ CFSG.pCore 2 K) := item1923Two_isL3odd kf3a kf2 h194 h hF hK hone'
  have hrank : CFSG.Open.pRank 3 K = 1 := by
    apply le_antisymm (item1923Two_pRank_le_one kf2 h194 h hF hK hone')
    obtain ⟨r, -, -, hr1⟩ := item1923Two_exists_order_three hK.1 hL
    exact hr1
  refine ⟨?_, hrank, hL⟩
  ext K'
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hK'
    by_contra hne
    exact item1923Two_false_of_two kf2 kf3a h194 h hF hK hK' (Ne.symm hne) hone
  · intro h'
    rw [h']
    exact hK

end CFSG.RankThree.PartTwo.Late
