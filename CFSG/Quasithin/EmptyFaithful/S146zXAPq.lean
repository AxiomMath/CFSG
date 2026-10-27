module

public import CFSG.Quasithin.EmptyFaithful.S146zLSgn
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.EmptyFaithful.S152Y22

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Generic

variable {Γ : Type*} [Group Γ]

theorem mem_sup_of_pow_mem {x : Γ} {m n : ℕ} (h : Nat.Coprime m n) {A B : Subgroup Γ}
    (hm : x ^ m ∈ A) (hn : x ^ n ∈ B) : x ∈ A ⊔ B := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr h
  have e : x = (x ^ m) ^ u * (x ^ n) ^ v := by
    rw [← zpow_natCast x m, ← zpow_natCast x n, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (m : ℤ) * u + (n : ℤ) * v = 1 := by linarith
    rw [this, zpow_one]
  rw [e]
  exact Subgroup.mul_mem_sup (A.zpow_mem hm u) (B.zpow_mem hn v)

theorem le_normalizer_of_forall_conj {S Y : Subgroup Γ}
    (h : ∀ g ∈ S, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : S ≤ Subgroup.normalizer (Y : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem card_zpowers_sup [Finite Γ] {p : ℕ} (hp : p.Prime) {A B : Γ} (hAB : A * B = B * A)
    (hAp : A ^ p = 1) (hBp : B ^ p = 1) (hA1 : A ≠ 1) (hB1 : B ≠ 1)
    (hinf : Subgroup.zpowers A ⊓ Subgroup.zpowers B = ⊥) :
    Nat.card ↥(Subgroup.zpowers A ⊔ Subgroup.zpowers B) = p ^ 2 := by
  have hcomm : ∀ x ∈ Subgroup.zpowers A, ∀ y ∈ Subgroup.zpowers B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute A B from hAB) m n).eq
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers A)
    (Subgroup.zpowers B) hcomm).1
  have : Fact p.Prime := ⟨hp⟩
  have hoA : orderOf A = p := orderOf_eq_prime hAp hA1
  have hoB : orderOf B = p := orderOf_eq_prime hBp hB1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoA, hoB] at hc
  rw [hc]
  ring

end Generic

section Rot

variable {G : Type} [Group G]

structure RotPair (H H₁ H₂ : Subgroup G) (p : ℕ) where
  φ₁ : ↥H₁ →* DihedralGroup p
  φ₂ : ↥H₂ →* DihedralGroup p
  a₁ : ↥H₁
  a₂ : ↥H₂
  ker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H
  ker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H
  rot₁ : φ₁ a₁ = DihedralGroup.r 1
  rot₂ : φ₂ a₂ = DihedralGroup.r 1

variable {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem nonempty_rotPair (h : IsDecP T M H p H₀ H₁ H₂ t) : Nonempty (RotPair H H₁ H₂ p) := by
  obtain ⟨φ₁, hφ₁s, hker₁⟩ := h.exists_phi_gen
  obtain ⟨φ₂, hφ₂s, hker₂⟩ := h.swap.exists_phi_gen
  obtain ⟨a₁, ha₁⟩ := hφ₁s (DihedralGroup.r 1)
  obtain ⟨a₂, ha₂⟩ := hφ₂s (DihedralGroup.r 1)
  exact ⟨⟨φ₁, φ₂, a₁, a₂, hker₁, hker₂, ha₁, ha₂⟩⟩

theorem rot_facts {Hi : Subgroup G} [Fact p.Prime] (φ : ↥Hi →* DihedralGroup p)
    (hker : ∀ y : ↥Hi, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a : ↥Hi}
    (ha : φ a = DihedralGroup.r 1) : (a : G) ∉ pCoreOf 2 H ∧ (a : G) ^ p ∈ pCoreOf 2 H := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨fun hQ => ?_, ?_⟩
  · have := (hker a).mpr hQ
    rw [ha] at this
    have h1 : (DihedralGroup.r (1 : ZMod p)) = DihedralGroup.r 0 := this
    exact one_ne_zero (DihedralGroup.r.inj h1)
  · have h1 : φ (a ^ p) = 1 := by
      rw [map_pow, ha]
      exact DihedralGroup.r_one_pow_n
    simpa using (hker _).mp h1

end Rot

section Pq

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}
  {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem mem_pq_of_pow_mem (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) {x : G}
    (hx : x ∈ H) {n : ℕ} (hn : x ^ p ^ n ∈ PQ) : x ∈ PQ := by
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTH : T ≤ H := hred.isHTM.1.1
  have hxPT : x ∈ PQ ⊔ T := by
    rw [← hred.eq]
    exact hx
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT2 (hTH.trans hred.normal) hxPT
  have hcop : Nat.Coprime (p ^ n) (2 ^ k) :=
    Nat.Coprime.pow n k ((Nat.coprime_primes hred.prime Nat.prime_two).mpr hred.odd)
  simpa using mem_sup_of_pow_mem hcop hn hk

theorem exists_mul_of_mem_pq (hred : IsRedCE T M H PQ p) {y : G} (hy : y ∈ PQ) :
    ∃ q ∈ pCoreOf 2 H, ∃ k ∈ oTwoUpper H, y = q * k := by
  obtain ⟨i, hi⟩ := exists_pow_mem_oTwoUpper H (hred.le hy)
  obtain ⟨j, hj⟩ := hred.pSec y hy
  have hcop : Nat.Coprime (2 ^ i) (p ^ j) :=
    Nat.Coprime.pow i j ((Nat.coprime_primes Nat.prime_two hred.prime).mpr (Ne.symm hred.odd))
  have hy' : y ∈ pCoreOf 2 H ⊔ oTwoUpper H := by
    rw [sup_comm]
    exact mem_sup_of_pow_mem hcop hi hj
  exact (Ch1Sec3.mem_sup_iff_of_le_normalizer ((oTwoUpper_le H).trans
    (le_normalizer_pCoreOf 2 H))).mp hy'

omit [Finite G] in
theorem relIndex_inf_pCoreOf_eq_card_map {X : Subgroup G} (hXH : X ≤ H) :
    (X ⊓ pCoreOf 2 H).relIndex X = Nat.card ((X.subgroupOf H).map (piQ H)) := by
  let f : ↥X →* ↥H ⧸ (pCoreOf 2 H).subgroupOf H := (piQ H).comp (Subgroup.inclusion hXH)
  have hker : f.ker = (X ⊓ pCoreOf 2 H).subgroupOf X := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      exact ⟨x.2, (piQ_eq_one_iff H ⟨x, hXH x.2⟩).mp hx⟩
    · rintro ⟨-, h2⟩
      exact (piQ_eq_one_iff H ⟨x, hXH x.2⟩).mpr h2
  have hrange : f.range = (X.subgroupOf H).map (piQ H) := by
    ext u
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hXH x.2⟩, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange]

theorem exists_pqAB (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∃ A B : ↥H ⧸ (pCoreOf 2 H).subgroupOf H,
      A * B = B * A ∧ A ^ p = 1 ∧ B ^ p = 1 ∧ A ≠ 1 ∧ B ≠ 1 ∧
      Subgroup.zpowers A ⊓ Subgroup.zpowers B = ⊥ ∧
      A ∈ (PQ.subgroupOf H).map (piQ H) ∧ B ∈ (PQ.subgroupOf H).map (piQ H) ∧
      ∀ (y : G) (hy : y ∈ PQ), ∃ i j : ℕ, piQ H ⟨y, hred.le hy⟩ = A ^ i * B ^ j := by
  classical
  have hp : p.Prime := hred.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R⟩ := nonempty_rotPair h
  have ha₁H : (R.a₁ : G) ∈ H := h.le (h.le₁ R.a₁.2)
  have ha₂H : (R.a₂ : G) ∈ H := h.le (h.le₂ R.a₂.2)
  obtain ⟨haQ₁, hap₁⟩ := rot_facts R.φ₁ R.ker₁ R.rot₁
  obtain ⟨haQ₂, hap₂⟩ := rot_facts R.φ₂ R.ker₂ R.rot₂
  have hQPQ : pCoreOf 2 H ≤ PQ := hred.lt.le
  have ha₁PQ : (R.a₁ : G) ∈ PQ :=
    mem_pq_of_pow_mem S hred ha₁H (n := 1) (by simpa using hQPQ hap₁)
  have ha₂PQ : (R.a₂ : G) ∈ PQ :=
    mem_pq_of_pow_mem S hred ha₂H (n := 1) (by simpa using hQPQ hap₂)
  set α₁ := piQ H ⟨(R.a₁ : G), ha₁H⟩ with hα₁
  set α₂ := piQ H ⟨(R.a₂ : G), ha₂H⟩ with hα₂
  have hα₁ne : α₁ ≠ 1 := fun e => haQ₁ ((piQ_eq_one_iff H _).mp e)
  have hα₂ne : α₂ ≠ 1 := fun e => haQ₂ ((piQ_eq_one_iff H _).mp e)
  have hα₁p : α₁ ^ p = 1 := by
    rw [hα₁, ← map_pow]
    exact (piQ_eq_one_iff H _).mpr (by simpa using hap₁)
  have hα₂p : α₂ ^ p = 1 := by
    rw [hα₂, ← map_pow]
    exact (piQ_eq_one_iff H _).mpr (by simpa using hap₂)
  have hα₁α₂ : α₁ * α₂ = α₂ * α₁ := by
    have h1 : (R.a₁ : G) * (R.a₂ : G) * (R.a₁ : G)⁻¹ * (R.a₂ : G)⁻¹ ∈ pCoreOf 2 H :=
      h.comm (Subgroup.commutator_mem_commutator R.a₁.2 R.a₂.2)
    exact mul_inv_eq_iff_eq_mul.mp ((cent_iff ha₁H ha₂H).mp h1)
  have hinf : Subgroup.zpowers α₁ ⊓ Subgroup.zpowers α₂ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers (x := α₁) (y := y)).mpr hy.1
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers (x := α₂) (y := y)).mpr hy.2
    have hm' : α₁ ^ m = y := hm
    have hn' : α₂ ^ n = y := hn
    have e1 : (⟨(R.a₁ : G) ^ m, H.pow_mem ha₁H m⟩ : ↥H) = ⟨(R.a₁ : G), ha₁H⟩ ^ m := rfl
    have e2 : (⟨(R.a₂ : G) ^ n, H.pow_mem ha₂H n⟩ : ↥H) = ⟨(R.a₂ : G), ha₂H⟩ ^ n := rfl
    have hmn : piQ H ⟨(R.a₁ : G) ^ m, H.pow_mem ha₁H m⟩ =
        piQ H ⟨(R.a₂ : G) ^ n, H.pow_mem ha₂H n⟩ := by
      rw [e1, e2, map_pow, map_pow, ← hα₁, ← hα₂, hm', hn']
    have hq : ((⟨(R.a₁ : G) ^ m, H.pow_mem ha₁H m⟩ : ↥H)⁻¹ *
        ⟨(R.a₂ : G) ^ n, H.pow_mem ha₂H n⟩ : ↥H) ∈ (pCoreOf 2 H).subgroupOf H :=
      QuotientGroup.eq.mp hmn
    have hqQ : ((R.a₁ : G) ^ m)⁻¹ * (R.a₂ : G) ^ n ∈ pCoreOf 2 H := hq
    have hv₂ : (R.a₂ : G) ^ n ∈ H₂ := H₂.pow_mem R.a₂.2 n
    have hv₁ : (R.a₂ : G) ^ n ∈ H₁ := by
      have e : (R.a₂ : G) ^ n =
          (R.a₁ : G) ^ m * (((R.a₁ : G) ^ m)⁻¹ * (R.a₂ : G) ^ n) := by group
      rw [e]
      exact H₁.mul_mem (H₁.pow_mem R.a₁.2 m) (h.Q₁ hqQ)
    have hvQ : (R.a₂ : G) ^ n ∈ pCoreOf 2 H := by
      have : (R.a₂ : G) ^ n ∈ H₁ ⊓ H₂ := ⟨hv₁, hv₂⟩
      rwa [h.inf] at this
    rw [← hn', show α₂ ^ n = piQ H ⟨(R.a₂ : G) ^ n, H.pow_mem ha₂H n⟩ by rw [e2, map_pow]]
    exact (piQ_eq_one_iff H _).mpr hvQ
  refine ⟨α₁, α₂, hα₁α₂, hα₁p, hα₂p, hα₁ne, hα₂ne, hinf,
    ⟨⟨(R.a₁ : G), ha₁H⟩, Subgroup.mem_subgroupOf.mpr ha₁PQ, rfl⟩,
    ⟨⟨(R.a₂ : G), ha₂H⟩, Subgroup.mem_subgroupOf.mpr ha₂PQ, rfl⟩, fun y hy => ?_⟩
  obtain ⟨i, j, hij⟩ := h.pq_rot_K S hred R.φ₁ R.ker₁ R.rot₁ R.φ₂ R.ker₂ R.rot₂ y hy
  exact ⟨i, j, hij⟩

theorem pq_section (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) :
    (∀ y ∈ PQ, ∀ z ∈ PQ, y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 H) ∧
      (∀ y ∈ PQ, y ^ p ∈ pCoreOf 2 H) ∧
      Nat.card ((PQ.subgroupOf H).map (piQ H)) = p ^ 2 := by
  obtain ⟨A, B, hAB, hAp, hBp, hA1, hB1, hinf, hAm, hBm, hrep⟩ := exists_pqAB S hred h
  have hcom : Commute A B := hAB
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨i, j, hij⟩ := hrep y hy
    obtain ⟨k, l, hkl⟩ := hrep z hz
    have hc : Commute (A ^ i * B ^ j) (A ^ k * B ^ l) :=
      Commute.mul_left
        (Commute.mul_right (Commute.pow_pow_self A i k) (hcom.pow_pow i l))
        (Commute.mul_right (hcom.symm.pow_pow j k) (Commute.pow_pow_self B j l))
    rw [cent_iff (hred.le hy) (hred.le hz), hij, hkl, hc.eq]
    exact mul_inv_cancel_right _ _
  · obtain ⟨i, j, hij⟩ := hrep y hy
    have hyH : y ∈ H := hred.le hy
    have e : (⟨y ^ p, H.pow_mem hyH p⟩ : ↥H) = ⟨y, hyH⟩ ^ p := rfl
    have hone : piQ H ⟨y ^ p, H.pow_mem hyH p⟩ = 1 := by
      rw [e, map_pow, hij, (hcom.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i p,
        mul_comm j p, pow_mul, pow_mul, hAp, hBp, one_pow, one_pow, mul_one]
    exact (piQ_eq_one_iff H _).mp hone
  · have hset : (PQ.subgroupOf H).map (piQ H) = Subgroup.zpowers A ⊔ Subgroup.zpowers B := by
      apply le_antisymm
      · rintro z ⟨y, hy, rfl⟩
        obtain ⟨i, j, hij⟩ := hrep (y : G) (Subgroup.mem_subgroupOf.mp hy)
        have : piQ H y = A ^ i * B ^ j := hij
        rw [this]
        exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers A) i)
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers B) j)
      · exact sup_le (Subgroup.zpowers_le.mpr hAm) (Subgroup.zpowers_le.mpr hBm)
    rw [hset]
    exact card_zpowers_sup hred.prime hAB hAp hBp hA1 hB1 hinf

theorem oTwoUpper_star_eq (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) :
    ((oTwoUpper H).subgroupOf H).map (piQ H) = (PQ.subgroupOf H).map (piQ H) := by
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hKPQ : oTwoUpper H ≤ PQ := hred.oTwoUpper_le_pq hT2
  apply le_antisymm
  · exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hKPQ (Subgroup.mem_subgroupOf.mp hx))
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨q, hq, k, hk, hyqk⟩ := exists_mul_of_mem_pq hred (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨⟨k, oTwoUpper_le H hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
    have e : y = ⟨q, pCoreOf_le 2 H hq⟩ * ⟨k, oTwoUpper_le H hk⟩ := Subtype.ext hyqk
    rw [e, map_mul, (piQ_eq_one_iff H ⟨q, pCoreOf_le 2 H hq⟩).mpr hq, one_mul]

theorem relIndex_pCoreOf_oTwoUpper_of_isDecP (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = p ^ 2 := by
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  rw [S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H),
    relIndex_inf_pCoreOf_eq_card_map hKH, oTwoUpper_star_eq S hred]
  exact (pq_section S hred h).2.2

end Pq

end CFSG.Quasithin.S146zX
