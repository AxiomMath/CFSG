module

public import CFSG.Walter.W67.Section6.Core62K

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_isT {r : ℕ} [Fact r.Prime] {S : Subgroup G} {y₀ t z : G}
    (ht : IsT S y₀ r t) (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) (hyo : orderOf y₀ = r)
    (hz : z ∈ S) (hcz : z * t * z⁻¹ * t⁻¹ ≠ 1) :
    S ≤ (S ⊓ Subgroup.centralizer ({t} : Set G)) ⊔ Subgroup.zpowers z := by
  have hyr : y₀ ^ r = 1 := by rw [← hyo, pow_orderOf_eq_one]
  set c₀ := z * t * z⁻¹ * t⁻¹ with hc₀
  have hc₀Y : c₀ ∈ Subgroup.zpowers y₀ := ht.2.2 z hz
  have hc₀o : orderOf c₀ = r := orderOf_eq_prime (IsT.pow_eq_one_of_mem_zpowers hyr hc₀Y) hcz
  have hzz := eq_of_le_cyclic (Subgroup.isCyclic_zpowers y₀) (Subgroup.zpowers_le.mpr hc₀Y)
    le_rfl (by rw [Nat.card_zpowers, Nat.card_zpowers, hc₀o, hyo])
  intro s hs
  have hcs : s * t * s⁻¹ * t⁻¹ ∈ Subgroup.zpowers c₀ := hzz ▸ ht.2.2 s hs
  obtain ⟨j, hj⟩ := (isOfFinOrder_of_finite c₀).mem_powers_iff_mem_zpowers.mpr hcs
  have h1 : z ^ j * t * (z ^ j)⁻¹ * t⁻¹ = s * t * s⁻¹ * t⁻¹ := by
    rw [ht.conj_pow hyC hz j]
    exact hj
  have hzjS : (z ^ j)⁻¹ ∈ S := S.inv_mem (S.pow_mem hz j)
  have h2 := IsT.conj_mul hyC ht (S.pow_mem hz j) hzjS
  have h2' : (z ^ j * t * (z ^ j)⁻¹ * t⁻¹) * ((z ^ j)⁻¹ * t * ((z ^ j)⁻¹)⁻¹ * t⁻¹) = 1 := by
    rw [← h2]
    group
  have hc2 := eq_inv_of_mul_eq_one_right h2'
  have h3 := IsT.conj_mul hyC ht hzjS hs
  rw [hc2, h1, inv_mul_cancel] at h3
  have hu : (z ^ j)⁻¹ * s ∈ S ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨S.mul_mem hzjS hs, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (z ^ j)⁻¹ * s * t
        = ((z ^ j)⁻¹ * s) * t * ((z ^ j)⁻¹ * s)⁻¹ * t⁻¹ * t * ((z ^ j)⁻¹ * s) := by group
      _ = t * ((z ^ j)⁻¹ * s) := by rw [h3, one_mul]
  have e : s = z ^ j * ((z ^ j)⁻¹ * s) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) j))
    (Subgroup.mem_sup_left hu)

structure CaseB (r : ℕ) (J x₀ y₀ : G) (P₀ P₁ S : Subgroup G) : Prop where
  hS : IsPGroup r S
  hScard : Nat.card S = r ^ (Nat.card G).factorization r
  hPS : P₀ ⊔ P₁ ≤ S
  hJS : J ∈ Subgroup.normalizer (S : Set G)
  hSP : ¬ S ≤ P₀ ⊔ P₁
  hx : IsT S y₀ r x₀

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

omit [Finite G] in
theorem mem_zpowers_sq {Q : Subgroup G} (hQ : IsPGroup r Q) {z : G} (hz : z ∈ Q) :
    z ∈ Subgroup.zpowers (z ^ 2) := by
  obtain ⟨m, hm⟩ := h.odd_orderOf hQ hz
  have e : z = (z ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf z + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have : (z ^ 2) ^ (m + 1) ∈ Subgroup.zpowers (z ^ 2) :=
    Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  rwa [← e] at this

section CaseB

variable {S : Subgroup G} (c : CaseB r J x₀ y₀ P₀ P₁ S)
include c

theorem caseB_yC : y₀ ∈ Subgroup.centralizer (S : Set G) :=
  h.y₀_mem_centralizer c.hS c.hPS c.hJS c.hSP

theorem caseB_mem_P {s : G} (hs : s ∈ S) (hc : s * x₀ * s⁻¹ * x₀⁻¹ = 1) : s ∈ P₀ ⊔ P₁ := by
  rw [← h.inf_centralizer_eq c.hS c.hPS]
  refine Subgroup.mem_inf.mpr ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc s * x₀ = s * x₀ * s⁻¹ * x₀⁻¹ * x₀ * s := by group
    _ = x₀ * s := by rw [hc, one_mul]

theorem caseB_exists_z : ∃ z ∈ S, J * z * J⁻¹ = z⁻¹ ∧ z * x₀ * z⁻¹ * x₀⁻¹ ≠ 1 := by
  have hyC := h.caseB_yC c
  obtain ⟨s, hs, hsP⟩ := Set.not_subset.mp c.hSP
  have hJinv := h.J_inv
  refine ⟨s⁻¹ * (J * s * J⁻¹), S.mul_mem (S.inv_mem hs)
    ((Subgroup.mem_normalizer_iff.mp c.hJS s).mp hs), ?_, ?_⟩
  · rw [hJinv]
    calc J * (s⁻¹ * (J * s * J)) * J = J * s⁻¹ * J * s * (J * J) := by group
      _ = J * s⁻¹ * J * s := by rw [h.J_mul_J, mul_one]
      _ = (s⁻¹ * (J * s * J))⁻¹ := by
          rw [show (s⁻¹ * (J * s * J))⁻¹ = J⁻¹ * s⁻¹ * J⁻¹ * s by group, hJinv]
  · intro hc
    apply hsP
    have hJs : J * s * J⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp c.hJS s).mp hs
    have h1 := IsT.conj_mul hyC c.hx (S.inv_mem hs) hJs
    rw [hc] at h1
    have hJx : J * x₀ * J⁻¹ = x₀ := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (h.P₀_le h.x₀_mem), mul_inv_cancel_right]
    have h2 : (J * s * J⁻¹) * x₀ * (J * s * J⁻¹)⁻¹ * x₀⁻¹ = (s * x₀ * s⁻¹ * x₀⁻¹)⁻¹ := by
      have e : (J * s * J⁻¹) * x₀ * (J * s * J⁻¹)⁻¹ * x₀⁻¹ =
          J * (s * (J⁻¹ * x₀ * J) * s⁻¹ * (J⁻¹ * x₀⁻¹ * J)) * J⁻¹ := by group
      have hJx' : J⁻¹ * x₀ * J = x₀ := by rw [hJinv]; rw [hJinv] at hJx; exact hJx
      have hJx'' : J⁻¹ * x₀⁻¹ * J = x₀⁻¹ := by
        rw [show J⁻¹ * x₀⁻¹ * J = (J⁻¹ * x₀ * J)⁻¹ by group, hJx']
      rw [e, hJx', hJx'']
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (c.hx.2.2 s hs)
      rw [← hk, ← conj_zpow, h.J_y₀, inv_zpow]
    have h3 : s⁻¹ * x₀ * s⁻¹⁻¹ * x₀⁻¹ = (s * x₀ * s⁻¹ * x₀⁻¹)⁻¹ := by
      have h4 := IsT.conj_mul hyC c.hx hs (S.inv_mem hs)
      rw [mul_inv_cancel] at h4
      have h5 : (s * x₀ * s⁻¹ * x₀⁻¹) * (s⁻¹ * x₀ * s⁻¹⁻¹ * x₀⁻¹) = 1 := by
        rw [← h4]; group
      exact eq_inv_of_mul_eq_one_right h5
    rw [h2, h3] at h1
    have hcs := c.hx.2.2 s hs
    have h6 : (s * x₀ * s⁻¹ * x₀⁻¹) * (s * x₀ * s⁻¹ * x₀⁻¹) = 1 := by
      have := congrArg (·⁻¹) h1
      simp only [mul_inv_rev, inv_inv, inv_one] at this
      exact this.symm
    have h7 := h.eq_one_of_sq (Q := Subgroup.zpowers y₀)
      (h.P₁_r.to_le (Subgroup.zpowers_le.mpr h.y₀_mem)) hcs h6
    exact h.caseB_mem_P c hs h7

omit [Finite G] in
theorem caseB_comm_of_mem {z : G} (hz : z ∈ S) (hzJ : J * z * J⁻¹ = z⁻¹) {y : G} (hy : y ∈ P₁)
    (hzy : z * y * z⁻¹ ∈ P₁) : z * y = y * z := by
  have h1 : J * (z * y * z⁻¹) * J⁻¹ = (z * y * z⁻¹)⁻¹ := h.P₁_inv _ hzy
  have h2 : J * (z * y * z⁻¹) * J⁻¹ = z⁻¹ * y⁻¹ * z := by
    calc J * (z * y * z⁻¹) * J⁻¹ = (J * z * J⁻¹) * (J * y * J⁻¹) * (J * z * J⁻¹)⁻¹ := by group
      _ = z⁻¹ * y⁻¹ * z := by rw [hzJ, h.P₁_inv y hy, inv_inv]
  rw [h2] at h1
  have h3 : (z * z) * y⁻¹ = y⁻¹ * (z * z) := by
    calc (z * z) * y⁻¹ = z * (z * y * z⁻¹)⁻¹ * z := by group
      _ = z * (z⁻¹ * y⁻¹ * z) * z := by rw [← h1]
      _ = y⁻¹ * (z * z) := by group
  have h4 : Commute (z ^ 2) y := by
    rw [pow_two]
    exact Commute.inv_right_iff.mp h3
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.mem_zpowers_sq c.hS hz)
  rw [← hk]
  exact (h4.zpow_left k).eq

theorem caseB_sup {z : G} (hz : z ∈ S) (hzx : z * x₀ * z⁻¹ * x₀⁻¹ ≠ 1) :
    S ≤ (P₀ ⊔ P₁) ⊔ Subgroup.zpowers z := by
  have := le_sup_of_isT c.hx (h.caseB_yC c) h.orderOf_y₀ hz hzx
  rwa [h.inf_centralizer_eq c.hS c.hPS] at this

theorem caseB_zr {z : G} (hz : z ∈ S) (hzJ : J * z * J⁻¹ = z⁻¹) : z ^ r ∈ P₁ := by
  have hyC := h.caseB_yC c
  have h1 := c.hx.conj_pow hyC hz r
  rw [IsT.pow_eq_one_of_mem_zpowers h.y₀_pow (c.hx.2.2 z hz)] at h1
  have hP := h.caseB_mem_P c (S.pow_mem hz r) h1
  refine h.mem_P₁_of_inv hP ?_
  rw [← conj_pow, hzJ, inv_pow]

end CaseB

theorem false_of_caseC {S : Subgroup G} {w : G} (c : CaseC r J y₀ P₀ P₁ S w)
    (hScard : Nat.card S = r ^ (Nat.card G).factorization r) : False := by
  by_cases hlt : r * Nat.card P₁ < Nat.card ↥(S ⊓ Subgroup.centralizer ({w} : Set G))
  · exact h.false_of_caseC_large c hScard hlt
  · exact h.false_of_caseC_small c (not_lt.mp hlt) hScard

section CaseBEps

variable {S : Subgroup G} (c : CaseB r J x₀ y₀ P₀ P₁ S) {z : G} (hz : z ∈ S)
  (hzJ : J * z * J⁻¹ = z⁻¹) (hzx : z * x₀ * z⁻¹ * x₀⁻¹ ≠ 1)
  (hzP₁ : ∀ y ∈ P₁, z * y = y * z)
include c hz hzJ hzx hzP₁

omit hzx in
theorem caseB_eps_conj {a : G} (ha : a ∈ P₀) : z * a * z⁻¹ * a⁻¹ ∈ P₁ := by
  have hSN := h.le_normalizer_of_isT c.hS c.hPS c.hx
  have hsq : ∀ a ∈ P₀, (z * z) * a * (z * z)⁻¹ * a⁻¹ ∈ P₁ := by
    intro a ha
    have hu : z * a * z⁻¹ ∈ P₀ ⊔ P₁ :=
      (Subgroup.mem_normalizer_iff.mp (hSN hz) a).mp (Subgroup.mem_sup_left ha)
    obtain ⟨b, hb, a', ha', hba⟩ := h.mem_P.mp hu
    have hJa : ∀ x ∈ P₀, J * x * J⁻¹ = x := fun x hx => by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (h.P₀_le hx), mul_inv_cancel_right]
    have h1 : z⁻¹ * a * z = b⁻¹ * a' := by
      have e1 : J * (z * a * z⁻¹) * J⁻¹ = z⁻¹ * a * z := by
        calc J * (z * a * z⁻¹) * J⁻¹ = (J * z * J⁻¹) * (J * a * J⁻¹) * (J * z * J⁻¹)⁻¹ := by
              group
          _ = z⁻¹ * a * z := by rw [hzJ, hJa a ha, inv_inv]
      have e2 : J * (b * a') * J⁻¹ = b⁻¹ * a' := by
        calc J * (b * a') * J⁻¹ = (J * b * J⁻¹) * (J * a' * J⁻¹) := by group
          _ = b⁻¹ * a' := by rw [h.P₁_inv b hb, hJa a' ha']
      rw [← e1, ← hba, e2]
    have h2 : z * a' * z⁻¹ = b * a := by
      have e : a' = b * (z⁻¹ * a * z) := by rw [h1]; group
      rw [e]
      calc z * (b * (z⁻¹ * a * z)) * z⁻¹ = (z * b) * z⁻¹ * a := by group
        _ = (b * z) * z⁻¹ * a := by rw [hzP₁ b hb]
        _ = b * a := by group
    have h3 : (z * z) * a * (z * z)⁻¹ = b * b * a := by
      calc (z * z) * a * (z * z)⁻¹ = z * (z * a * z⁻¹) * z⁻¹ := by group
        _ = z * (b * a') * z⁻¹ := by rw [← hba]
        _ = (z * b) * z⁻¹ * (z * a' * z⁻¹) := by group
        _ = (b * z) * z⁻¹ * (b * a) := by rw [hzP₁ b hb, h2]
        _ = b * b * a := by group
    rw [h3, mul_inv_cancel_right]
    exact P₁.mul_mem hb hb
  obtain ⟨y, hy⟩ : ∃ y : G, z * z = y := ⟨_, rfl⟩
  rw [hy] at hsq
  have hyP₁ : ∀ b ∈ P₁, y * b = b * y := fun b hb => by
    rw [← hy]
    calc z * z * b = z * (z * b) := by group
      _ = z * (b * z) := by rw [hzP₁ b hb]
      _ = (z * b) * z := by group
      _ = (b * z) * z := by rw [hzP₁ b hb]
      _ = b * (z * z) := by group
  have hpow : ∀ n : ℕ, ∀ a ∈ P₀, y ^ n * a * (y ^ n)⁻¹ * a⁻¹ ∈ P₁ := by
    intro n
    induction n with
    | zero =>
      intro a _
      rw [pow_zero, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact P₁.one_mem
    | succ n ih =>
      intro a ha
      have hc := ih a ha
      have e : y ^ (n + 1) * a * (y ^ (n + 1))⁻¹ * a⁻¹ =
          (y * (y ^ n * a * (y ^ n)⁻¹ * a⁻¹) * y⁻¹) * (y * a * y⁻¹ * a⁻¹) := by
        rw [pow_succ']
        group
      have e2 : y * (y ^ n * a * (y ^ n)⁻¹ * a⁻¹) * y⁻¹ = y ^ n * a * (y ^ n)⁻¹ * a⁻¹ := by
        rw [hyP₁ _ hc, mul_inv_cancel_right]
      rw [e, e2]
      exact P₁.mul_mem hc (hsq a ha)
  obtain ⟨n, hn⟩ := (isOfFinOrder_of_finite y).mem_powers_iff_mem_zpowers.mpr
    (by rw [← hy, ← pow_two]; exact h.mem_zpowers_sq c.hS hz)
  have hn' : y ^ n = z := hn
  have := hpow n a ha
  rwa [hn'] at this

theorem false_of_caseB_eps : False := by
  have hSN := h.le_normalizer_of_isT c.hS c.hPS c.hx
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (P₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hzP₁ b hb).symm
  set R := P₁ ⊔ Subgroup.zpowers z with hR
  have hmemR : ∀ {x : G}, x ∈ R → ∃ b ∈ P₁, ∃ k : ℤ, b * z ^ k = x := fun {x} hx => by
    obtain ⟨b, hb, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hzN).mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨b, hb, k, rfl⟩
  have hzb : ∀ b ∈ P₁, ∀ k : ℤ, z ^ k * b = b * z ^ k := fun b hb k =>
    (Commute.zpow_left (show Commute z b from hzP₁ b hb) k).eq
  have hRab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    obtain ⟨b, hb, k, rfl⟩ := hmemR hx
    obtain ⟨b', hb', k', rfl⟩ := hmemR hy
    have hbb := h.P₁_comm b hb b' hb'
    calc b * z ^ k * (b' * z ^ k') = b * (z ^ k * b') * z ^ k' := by group
      _ = b * (b' * z ^ k) * z ^ k' := by rw [hzb b' hb' k]
      _ = b' * b * (z ^ k * z ^ k') := by rw [← mul_assoc, hbb]; group
      _ = b' * b * (z ^ k' * z ^ k) := by rw [← zpow_add, ← zpow_add, add_comm]
      _ = b' * (b * z ^ k') * z ^ k := by group
      _ = b' * (z ^ k' * b) * z ^ k := by rw [hzb b hb k']
      _ = b' * z ^ k' * (b * z ^ k) := by group
  have hRJ : ∀ x ∈ R, J * x * J⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨b, hb, k, rfl⟩ := hmemR hx
    calc J * (b * z ^ k) * J⁻¹ = (J * b * J⁻¹) * (J * z * J⁻¹) ^ k := by rw [conj_zpow]; group
      _ = b⁻¹ * (z ^ k)⁻¹ := by rw [h.P₁_inv b hb, hzJ, inv_zpow]
      _ = (b * z ^ k)⁻¹ := by
          rw [mul_inv_rev]
          have := congrArg (·⁻¹) (hzb b hb k)
          simp only [mul_inv_rev] at this
          exact this
  have hRS : R ≤ S := sup_le (le_sup_right.trans c.hPS) (Subgroup.zpowers_le.mpr hz)
  have hP₀R : P₀ ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    apply JT.mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨b, hb, k, rfl⟩ := hmemR hx
    have hq := h.caseB_eps_conj c hz hzJ hzP₁ ha
    have hq' : a * z * a⁻¹ * z⁻¹ ∈ P₁ := by
      have := P₁.inv_mem hq
      have e : (z * a * z⁻¹ * a⁻¹)⁻¹ = a * z * a⁻¹ * z⁻¹ := by group
      rw [e] at this
      exact this
    have hazR : a * z * a⁻¹ ∈ R := by
      have e : a * z * a⁻¹ = (a * z * a⁻¹ * z⁻¹) * z := by group
      rw [e]
      exact R.mul_mem (Subgroup.mem_sup_left hq') (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    have habR : a * b * a⁻¹ ∈ R :=
      Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (h.P₀_le_N ha) b).mp hb)
    have e : a * (b * z ^ k) * a⁻¹ = (a * b * a⁻¹) * (a * z * a⁻¹) ^ k := by
      rw [conj_zpow]; group
    rw [e]
    exact R.mul_mem habR (R.zpow_mem hazR k)
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := by
    refine (h.caseB_sup c hz hzx).trans (sup_le (sup_le hP₀R ?_) ?_)
    · exact (le_sup_left : P₁ ≤ R).trans Subgroup.le_normalizer
    · exact (le_sup_right : Subgroup.zpowers z ≤ R).trans Subgroup.le_normalizer
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  have hnc : ¬ ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun hab => hzx (by
    rw [hab z hz x₀ hx₀S]; group)
  by_cases hRc : IsCyclic R
  ·
    obtain ⟨⟨g₀, hg₀⟩, hg⟩ := h.P₀_cyc.exists_generator
    have hP₀g : P₀ ≤ Subgroup.zpowers g₀ := by
      intro a ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
      have : g₀ ^ k = a := congrArg Subtype.val hk
      rw [← this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g₀) k
    exact false_of_metacyclic h.perfect h.r_ne_two c.hScard hRS hSR hRc
      (c.hPS (Subgroup.mem_sup_left hg₀)) ((h.caseB_sup c hz hzx).trans
        (sup_le (sup_le (hP₀g.trans le_sup_right) (le_sup_left.trans le_sup_left))
          (le_sup_right.trans le_sup_left))) hnc
  ·
    obtain ⟨⟨g₁, hg₁⟩, hg₁gen⟩ := h.P₁_cyc.exists_generator
    have hP₁g : P₁ ≤ Subgroup.zpowers g₁ := by
      intro a ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₁gen ⟨a, ha⟩)
      have : g₁ ^ k = a := congrArg Subtype.val hk
      rw [← this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g₁) k
    have hzr := h.caseB_zr c hz hzJ
    obtain ⟨i, hi⟩ := (isOfFinOrder_of_finite g₁).mem_powers_iff_mem_zpowers.mpr (hP₁g hzr)
    have hi' : g₁ ^ i = z ^ r := hi
    by_cases hri : r ∣ i
    · obtain ⟨i', rfl⟩ := hri
      have hg₁i' : g₁ ^ i' ∈ P₁ := P₁.pow_mem hg₁ i'
      have hwR : z * (g₁ ^ i')⁻¹ ∈ R :=
        R.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
          (Subgroup.mem_sup_left (P₁.inv_mem hg₁i'))
      have hzg : Commute z (g₁ ^ i')⁻¹ := hzP₁ _ (P₁.inv_mem hg₁i')
      have hwr : (z * (g₁ ^ i')⁻¹) ^ r = 1 := by
        rw [hzg.mul_pow, ← hi', inv_pow, ← pow_mul, mul_comm i' r, mul_inv_cancel]
      have hwY : z * (g₁ ^ i')⁻¹ ∉ Subgroup.zpowers y₀ := by
        intro hw
        apply hzx
        have hzP : z ∈ P₁ := by
          have e : z = (z * (g₁ ^ i')⁻¹) * g₁ ^ i' := by group
          rw [e]
          exact P₁.mul_mem ((Subgroup.zpowers_le.mpr h.y₀_mem) hw) hg₁i'
        rw [Subgroup.mem_centralizer_singleton_iff.mp (h.M_le (h.P₁_le_M hzP)),
          mul_inv_cancel_right, mul_inv_cancel]
      have hwT : IsT S y₀ r (z * (g₁ ^ i')⁻¹) := by
        refine ⟨hRS hwR, hwr, fun s hs => ?_⟩
        set w := z * (g₁ ^ i')⁻¹ with hw
        have hzNP : Subgroup.zpowers z ≤ Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) :=
          Subgroup.zpowers_le.mpr (hSN hz)
        obtain ⟨p, hp, e, he, rfl⟩ :=
          (mem_sup_iff_of_le_normalizer hzNP).mp (h.caseB_sup c hz hzx hs)
        obtain ⟨b, hb, a, ha, rfl⟩ := h.mem_P.mp hp
        have heR : e ∈ R := (le_sup_right : Subgroup.zpowers z ≤ R) he
        have hbR : b ∈ R := Subgroup.mem_sup_left hb
        have hawR : a * w * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hP₀R ha) w).mp hwR
        have e1 : b * a * e * w * (b * a * e)⁻¹ * w⁻¹ = a * w * a⁻¹ * w⁻¹ := by
          calc b * a * e * w * (b * a * e)⁻¹ * w⁻¹ = b * a * (e * w * e⁻¹) * a⁻¹ * b⁻¹ * w⁻¹ := by
                group
            _ = b * (a * w * a⁻¹) * b⁻¹ * w⁻¹ := by
                rw [hRab e heR w hwR, mul_inv_cancel_right]; group
            _ = a * w * a⁻¹ * w⁻¹ := by
                rw [hRab b hbR _ hawR, mul_inv_cancel_right]
        rw [e1]
        have hq : a * z * a⁻¹ * z⁻¹ ∈ P₁ := by
          have := P₁.inv_mem (h.caseB_eps_conj c hz hzJ hzP₁ ha)
          have e2 : (z * a * z⁻¹ * a⁻¹)⁻¹ = a * z * a⁻¹ * z⁻¹ := by group
          rwa [e2] at this
        have hb'' : a * (g₁ ^ i')⁻¹ * a⁻¹ ∈ P₁ :=
          (Subgroup.mem_normalizer_iff.mp (h.P₀_le_N ha) _).mp (P₁.inv_mem hg₁i')
        have htP : a * w * a⁻¹ * w⁻¹ ∈ P₁ := by
          have e3 : a * w * a⁻¹ * w⁻¹ = (a * z * a⁻¹ * z⁻¹) *
              (z * ((a * (g₁ ^ i')⁻¹ * a⁻¹) * g₁ ^ i') * z⁻¹) := by rw [hw]; group
          rw [e3]
          refine P₁.mul_mem hq ?_
          have hy : (a * (g₁ ^ i')⁻¹ * a⁻¹) * g₁ ^ i' ∈ P₁ := P₁.mul_mem hb'' hg₁i'
          rw [hzP₁ _ hy, mul_inv_cancel_right]
          exact hy
        have htr : (a * w * a⁻¹ * w⁻¹) ^ r = 1 := by
          have hcomm : Commute (a * w * a⁻¹) w⁻¹ := hRab _ hawR _ (R.inv_mem hwR)
          rw [hcomm.mul_pow, conj_pow, hwr, inv_pow, hwr]
          group
        exact h.mem_Y_of_pow htP htr
      exact h.false_of_caseC ⟨c.hS, c.hPS, c.hJS, c.hSP, hwT, hwY, hRJ _ hwR⟩ c.hScard
    ·
      apply hRc
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.P₁_r) ⟨g₁, hg₁⟩
      rw [Subgroup.orderOf_mk] at hk
      have hcop : Nat.Coprime i (orderOf g₁) := by
        rw [hk]
        exact Nat.Coprime.pow_right k
          (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hri))
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      have hP₁z : P₁ ≤ Subgroup.zpowers z := by
        refine hP₁g.trans (Subgroup.zpowers_le.mpr ?_)
        rw [← hm, hi', ← pow_mul]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
      have hReq : R = Subgroup.zpowers z := le_antisymm (sup_le hP₁z le_rfl) le_sup_right
      rw [hReq]
      exact Subgroup.isCyclic_zpowers z

end CaseBEps

end Hyp62

end CFSG.Walter.W67.Sec6
