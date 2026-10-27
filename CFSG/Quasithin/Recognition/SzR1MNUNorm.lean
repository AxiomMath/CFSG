module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Quasithin.SzR1.MNU

namespace Norm

variable {G : Type*} [Group G]

theorem eq_or_eq_of_relIndex_prime {p : ℕ} (hp : p.Prime) {A B H : Subgroup G}
    (hAB : A.relIndex B = p) (hAH : A ≤ H) (hHB : H ≤ B) : H = A ∨ H = B := by
  have h := Subgroup.relIndex_mul_relIndex A H B hAH hHB
  rw [hAB] at h
  rcases (Nat.dvd_prime hp).mp (Dvd.intro _ h) with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAH)
  · refine Or.inr (le_antisymm hHB (Subgroup.relIndex_eq_one.mp ?_))
    rw [h1] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (mul_one p).symm)

theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

theorem cube_eq_one {a : G} (ha3 : orderOf a = 3) : a * a * a = 1 := by
  have h := pow_orderOf_eq_one a
  rw [ha3] at h
  simpa [pow_succ] using h

theorem zpowers_cases {a : G} (ha3 : orderOf a = 3) {b : G} (hb : b ∈ Subgroup.zpowers a) :
    b = 1 ∨ b = a ∨ b = a⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hmod : a ^ (k % 3) = a ^ k := by
    have h := zpow_mod_orderOf a k
    rw [ha3] at h
    exact_mod_cast h
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h0 | h1 | h2
  · left
    rw [← hmod, h0, zpow_zero]
  · right
    left
    rw [← hmod, h1, zpow_one]
  · right
    right
    rw [← hmod, h2, zpow_two]
    exact eq_inv_of_mul_eq_one_left (cube_eq_one ha3)

theorem exists_order_three [Finite G] {P S : Subgroup G} (hS3 : S.relIndex P = 3)
    (hS2 : IsPGroup 2 S) : ∃ a ∈ P, orderOf a = 3 ∧ a ∉ S := by
  have h3 : 3 ∣ Nat.card P := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := P)
    rw [hS3] at h
    exact Dvd.intro _ h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3
  have hxo : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  refine ⟨x, x.2, hxo, fun hxS => ?_⟩
  obtain ⟨n, hn⟩ := hS2 ⟨(x : G), hxS⟩
  have hpow : (x : G) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hdvd : orderOf (x : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpow
  rw [hxo] at hdvd
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem sup_zpowers_eq {P S : Subgroup G} (hS3 : S.relIndex P = 3) (hSP : S ≤ P) {a : G}
    (haP : a ∈ P) (haS : a ∉ S) : S ⊔ Subgroup.zpowers a = P := by
  rcases eq_or_eq_of_relIndex_prime Nat.prime_three hS3 (H := S ⊔ Subgroup.zpowers a)
      le_sup_left (sup_le hSP (Subgroup.zpowers_le.mpr haP)) with h | h
  · exact absurd (h.le (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))) haS
  · exact h

theorem conj_mem_sup_zpowers {P S Q : Subgroup G} (hSP : S ≤ P) (hQS : Q ≤ S)
    (hS3 : S.relIndex P = 3) (hQ2 : Q.relIndex S = 2) (hS2 : IsPGroup 2 S)
    (hQn : P ≤ Subgroup.normalizer (Q : Set G)) {a : G} (haP : a ∈ P) (ha3 : orderOf a = 3)
    {s : G} (hs : s ∈ S) : s * a * s⁻¹ ∈ Q ⊔ Subgroup.zpowers a := by
  have hTn : Subgroup.zpowers a ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (hQn haP)
  have hbot : Q ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxa⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn⟩ := hS2 ⟨x, hQS hxQ⟩
    have h2 : orderOf x ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
    have h3 : orderOf x ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers hxa
      rwa [ha3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
    · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
    · rw [h1] at h2
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
  have hQa3 : Q.relIndex (Subgroup.zpowers a) = 3 := by
    have h := Subgroup.inf_relIndex_right Q (Subgroup.zpowers a)
    rw [hbot, Subgroup.relIndex_bot_left, Nat.card_zpowers, ha3] at h
    exact h.symm
  have hR3 : Q.relIndex (Subgroup.zpowers a ⊔ Q) = 3 :=
    (relIndex_sup_eq_of_le_normalizer hTn).trans hQa3
  have hQR : Q ≤ Subgroup.zpowers a ⊔ Q := le_sup_right
  have hRP : Subgroup.zpowers a ⊔ Q ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr haP) (hQS.trans hSP)
  have h6 : Q.relIndex P = 6 := by
    have h := Subgroup.relIndex_mul_relIndex Q S P hQS hSP
    rw [hQ2, hS3] at h
    omega
  have hR2 : (Subgroup.zpowers a ⊔ Q).relIndex P = 2 := by
    have h := Subgroup.relIndex_mul_relIndex Q (Subgroup.zpowers a ⊔ Q) P hQR hRP
    rw [hR3, h6] at h
    omega
  have hnorm : ((Subgroup.zpowers a ⊔ Q).subgroupOf P).Normal :=
    Subgroup.normal_of_index_eq_two hR2
  have haR : a ∈ Subgroup.zpowers a ⊔ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hc := hnorm.conj_mem ⟨a, haP⟩ (Subgroup.mem_subgroupOf.mpr haR) ⟨s, hSP hs⟩
  have hc' : s * a * s⁻¹ ∈ Subgroup.zpowers a ⊔ Q := Subgroup.mem_subgroupOf.mp hc
  rwa [sup_comm]

theorem conj_mem_Q {P Q : Subgroup G} (hQn : P ≤ Subgroup.normalizer (Q : Set G)) {g y : G}
    (hg : g ∈ P) (hy : y ∈ Q) : g * y * g⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hQn hg) y).mp hy

theorem inv_conj_mem_Q {P Q : Subgroup G} (hQn : P ≤ Subgroup.normalizer (Q : Set G)) {g y : G}
    (hg : g ∈ P) (hy : y ∈ Q) : g⁻¹ * y * g ∈ Q := by
  have := conj_mem_Q hQn (P.inv_mem hg) hy
  simpa using this

theorem conj_commute_Q {P Q : Subgroup G} (hQn : P ≤ Subgroup.normalizer (Q : Set G)) {g y : G}
    (hg : g ∈ P) (hy : ∀ q ∈ Q, y * q = q * y) :
    ∀ q ∈ Q, g * y * g⁻¹ * q = q * (g * y * g⁻¹) := by
  intro q hq
  have h := hy _ (inv_conj_mem_Q hQn hg hq)
  calc g * y * g⁻¹ * q = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * q * g) * y) * g⁻¹ := by rw [h]
    _ = q * (g * y * g⁻¹) := by group

theorem conj_mul_mem {P Q : Subgroup G} (hQn : P ≤ Subgroup.normalizer (Q : Set G)) {g y q : G}
    (hg : g ∈ P) (hq : q ∈ Q) (hy : ∀ x ∈ Q, y * x = x * y) :
    q * g * y * (q * g)⁻¹ = g * y * g⁻¹ ∧ (q * g)⁻¹ * y * (q * g) = g⁻¹ * y * g := by
  have hc := conj_commute_Q hQn hg hy q hq
  have h1 := hy q hq
  constructor
  · calc q * g * y * (q * g)⁻¹ = q * (g * y * g⁻¹) * q⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [← hc]; group
  · have h2 : q⁻¹ * y * q = y := by
      calc q⁻¹ * y * q = q⁻¹ * (y * q) := by group
        _ = q⁻¹ * (q * y) := by rw [h1]
        _ = y := by group
    calc (q * g)⁻¹ * y * (q * g) = g⁻¹ * (q⁻¹ * y * q) * g := by group
      _ = g⁻¹ * y * g := by rw [h2]

theorem swap_or_fix {P S Q : Subgroup G} (hSP : S ≤ P)
    (hQn : P ≤ Subgroup.normalizer (Q : Set G)) {a y s v w : G} (haP : a ∈ P) (haQ : a ∉ Q)
    (ha3 : orderOf a = 3) (hyQ : ∀ q ∈ Q, y * q = q * y) (hsS : s ∈ S) (hsy : y * s = s * y)
    (hconj : s * a * s⁻¹ ∈ Q ⊔ Subgroup.zpowers a) (hv : v = a * y * a⁻¹)
    (hw : w = a⁻¹ * y * a) :
    (s * v * s⁻¹ = v ∧ s * w * s⁻¹ = w) ∨ (s * v * s⁻¹ = w ∧ s * w * s⁻¹ = v) := by
  subst hv hw
  have hTn : Subgroup.zpowers a ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (hQn haP)
  have hmem : s * a * s⁻¹ ∈ ((Q ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := hconj
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q (Subgroup.zpowers a) hTn] at hmem
  obtain ⟨q, hq, b, hb, hqb⟩ := Set.mem_mul.mp hmem
  have hsy' : s⁻¹ * y * s = y := by
    calc s⁻¹ * y * s = s⁻¹ * (y * s) := by group
      _ = s⁻¹ * (s * y) := by rw [hsy]
      _ = y := by group
  have e1 : s * (a * y * a⁻¹) * s⁻¹ = (s * a * s⁻¹) * y * (s * a * s⁻¹)⁻¹ := by
    have h : (s * a * s⁻¹) * y * (s * a * s⁻¹)⁻¹ = s * a * (s⁻¹ * y * s) * a⁻¹ * s⁻¹ := by group
    rw [h, hsy']
    group
  have e2 : s * (a⁻¹ * y * a) * s⁻¹ = (s * a * s⁻¹)⁻¹ * y * (s * a * s⁻¹) := by
    have h : (s * a * s⁻¹)⁻¹ * y * (s * a * s⁻¹) = s * a⁻¹ * (s⁻¹ * y * s) * a * s⁻¹ := by group
    rw [h, hsy']
    group
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply haQ
    have h2 : a = s⁻¹ * q * s := by
      calc a = s⁻¹ * (s * a * s⁻¹) * s := by group
        _ = s⁻¹ * (q * 1) * s := by rw [← hqb]
        _ = s⁻¹ * q * s := by group
    rw [h2]
    exact inv_conj_mem_Q hQn (hSP hsS) hq
  rw [e1, e2, ← hqb]
  rcases zpowers_cases ha3 hb with h1 | h1 | h1
  · exact absurd h1 hb1
  · rw [h1]
    exact Or.inl (conj_mul_mem hQn haP hq hyQ)
  · rw [h1]
    right
    have key := conj_mul_mem hQn (P.inv_mem haP) hq hyQ
    rw [inv_inv] at key
    exact key

theorem conj_prod_cyc {u v w x : G} (huv : u * v = v * u) (huw : u * w = w * u)
    (h1 : x * u * x⁻¹ = v) (h2 : x * v * x⁻¹ = w) (h3 : x * w * x⁻¹ = u) :
    x * (u * v * w) * x⁻¹ = u * v * w := by
  have e : x * (u * v * w) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) * (x * w * x⁻¹) := by group
  rw [e, h1, h2, h3]
  calc v * w * u = v * (w * u) := mul_assoc _ _ _
    _ = v * (u * w) := by rw [huw]
    _ = (v * u) * w := (mul_assoc _ _ _).symm
    _ = (u * v) * w := by rw [huv]

theorem conj_prod_swap {u v w x : G} (hvw : v * w = w * v) (h1 : x * u * x⁻¹ = u)
    (h : (x * v * x⁻¹ = v ∧ x * w * x⁻¹ = w) ∨ (x * v * x⁻¹ = w ∧ x * w * x⁻¹ = v)) :
    x * (u * v * w) * x⁻¹ = u * v * w := by
  have e : x * (u * v * w) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) * (x * w * x⁻¹) := by group
  rw [e, h1]
  rcases h with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · rw [h2, h3]
  · rw [h2, h3]
    calc u * w * v = u * (w * v) := mul_assoc _ _ _
      _ = u * (v * w) := by rw [hvw]
      _ = u * v * w := (mul_assoc _ _ _).symm

theorem prod_mul_self {u v w : G} (hu : u * u = 1) (hv : v * v = 1) (hw : w * w = 1)
    (huv : u * v = v * u) (huw : u * w = w * u) (hvw : v * w = w * v) :
    u * v * w * (u * v * w) = 1 := by
  have cuv : Commute u v := huv
  have cuw : Commute u w := huw
  have cvw : Commute v w := hvw
  have h : (u * v * w) ^ 2 = 1 := by
    rw [(cuw.mul_left cvw).mul_pow, cuv.mul_pow, sq u, sq v, sq w, hu, hv, hw]
    simp
  rwa [sq] at h

theorem comm_of_conj_eq {n s : G} (h : s * n * s⁻¹ = n) : n * s = s * n := by
  calc n * s = s * n * s⁻¹ * s := by rw [h]
    _ = s * n := by group

theorem mem_normalizer_zpowers {n g : G} (h : n * g = g * n) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers n : Subgroup G) : Set G) := by
  have hgcen : g ∈ Subgroup.centralizer ((Subgroup.zpowers n : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute n g from h) k).eq
  exact Subgroup.centralizer_le_normalizer _ hgcen

theorem mem_normalizer_closure_pair [Finite G] {u v x : G}
    (hu : x * u * x⁻¹ ∈ Subgroup.closure ({u, v} : Set G))
    (hv : x * v * x⁻¹ ∈ Subgroup.closure ({u, v} : Set G)) :
    x ∈ Subgroup.normalizer ((Subgroup.closure ({u, v} : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hn' : n ∈ Subgroup.closure ({u, v} : Set G) := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with h | h
    · rw [h]
      exact hu
    · rw [Set.mem_singleton_iff.mp h]
      exact hv
  | one => simp
  | mul z z' _ _ h1 h2 =>
    have e : x * (z * z') * x⁻¹ = (x * z * x⁻¹) * (x * z' * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 h2
  | inv z _ h1 =>
    have e : x * z⁻¹ * x⁻¹ = (x * z * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h1

end Norm

end CFSG.Quasithin.SzR1.MNU
