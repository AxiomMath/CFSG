module

public import CFSG.Walter.W67.Section6.Core62D

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External

theorem inv_of_fixedPointFree {Q : Subgroup G} {J : G} (hJ2 : J * J = 1)
    (hJQ : J ∈ Subgroup.normalizer (Q : Set G)) (hfp : ∀ q ∈ Q, J * q * J⁻¹ = q → q = 1) :
    ∀ q ∈ Q, J * q * J⁻¹ = q⁻¹ := by
  set φ := conjAut hJQ with hφ
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ2
  have hfpf : MonoidHom.FixedPointFree φ := fun g hg =>
    Subtype.ext (hfp g g.2 (congrArg Subtype.val hg))
  have hinv : Function.Involutive φ := fun g => by
    apply Subtype.ext
    change J * (J * g * J⁻¹) * J⁻¹ = g
    rw [hJinv]
    calc J * (J * g * J) * J = (J * J) * g * (J * J) := by group
      _ = g := by rw [hJ2, one_mul, mul_one]
  intro q hq
  have := congrArg Subtype.val (congrFun (hfpf.coe_eq_inv_of_involutive hinv) ⟨q, hq⟩)
  exact this

theorem le_sup_of_conj_mem {N K₀ : Subgroup G} {J : G} (hJ : orderOf J = 2) (hJN : J ∈ N)
    (hK₀N : K₀ ≤ N) (hNK₀ : N ≤ Subgroup.normalizer (K₀ : Set G))
    (h2 : (Nat.card N).factorization 2 ≤ 1) (hcomm : ∀ n ∈ N, J⁻¹ * (n * J * n⁻¹) ∈ K₀) :
    N ≤ (N ⊓ Subgroup.centralizer ({J} : Set G)) ⊔ K₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n hn
  set K := K₀ ⊔ Subgroup.zpowers J with hK
  have hJK₀ : Subgroup.zpowers J ≤ Subgroup.normalizer (K₀ : Set G) :=
    Subgroup.zpowers_le.mpr (hNK₀ hJN)
  have hKN : K ≤ N := sup_le hK₀N (Subgroup.zpowers_le.mpr hJN)
  have hnJ : n * J * n⁻¹ ∈ K := by
    have e : n * J * n⁻¹ = J * (J⁻¹ * (n * J * n⁻¹)) := by group
    rw [e]
    exact K.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers J))
      (Subgroup.mem_sup_left (hcomm n hn))
  have hK2 : (Nat.card K).factorization 2 = 1 := by
    have hle : (Nat.card K).factorization 2 ≤ 1 :=
      ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hKN) 2).trans h2
    have hge : 1 ≤ (Nat.card K).factorization 2 := by
      have hJ2 : 2 ∣ Nat.card K := by
        have := Subgroup.orderOf_dvd_natCard K (Subgroup.mem_sup_right (Subgroup.mem_zpowers J))
        rwa [hJ] at this
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp hJ2
    omega
  have hc1 : Nat.card (Subgroup.zpowers J) = 2 ^ (Nat.card K).factorization 2 := by
    rw [hK2, pow_one, Nat.card_zpowers, hJ]
  have hc2 : Nat.card (Subgroup.zpowers (n * J * n⁻¹)) = 2 ^ (Nat.card K).factorization 2 := by
    rw [hK2, pow_one, Nat.card_zpowers, orderOf_conj_mul, hJ]
  obtain ⟨ℓ, hℓK, hℓ⟩ := exists_conj_of_sylowIn (Subgroup.zpowers_le.mpr hnJ)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers J))) hc2 hc1
  have h1 : (ℓ * n) * J * (ℓ * n)⁻¹ = J := by
    have hmem : ℓ * (n * J * n⁻¹) * ℓ⁻¹ ∈ Subgroup.zpowers J := by
      rw [hℓ]
      exact conj_mem_cj (Subgroup.mem_zpowers _)
    have ho : orderOf (ℓ * (n * J * n⁻¹) * ℓ⁻¹) = 2 := by
      rw [orderOf_conj_mul, orderOf_conj_mul, hJ]
    have := eq_of_mem_of_cyclic_of_orderOf_two (Subgroup.isCyclic_zpowers J) hmem
      (Subgroup.mem_zpowers J) ho hJ
    calc (ℓ * n) * J * (ℓ * n)⁻¹ = ℓ * (n * J * n⁻¹) * ℓ⁻¹ := by group
      _ = J := this
  obtain ⟨k, hk, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hJK₀).mp hℓK
  have heJ : e * J = J * e := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (Commute.zpow_left (Commute.refl J) i).eq
  have heN : e ∈ N := (Subgroup.zpowers_le.mpr hJN) he
  have hb : e⁻¹ * (k * e * n) ∈ N ⊓ Subgroup.centralizer ({J} : Set G) := by
    refine Subgroup.mem_inf.mpr
      ⟨N.mul_mem (N.inv_mem heN) (N.mul_mem (N.mul_mem (hK₀N hk) heN) hn), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : (k * e * n) * J = J * (k * e * n) := by
      calc (k * e * n) * J = (k * e * n) * J * (k * e * n)⁻¹ * (k * e * n) := by group
        _ = J * (k * e * n) := by rw [h1]
    have h3 : e⁻¹ * J = J * e⁻¹ := by
      calc e⁻¹ * J = e⁻¹ * (J * e) * e⁻¹ := by group
        _ = e⁻¹ * (e * J) * e⁻¹ := by rw [heJ]
        _ = J * e⁻¹ := by group
    calc e⁻¹ * (k * e * n) * J = e⁻¹ * ((k * e * n) * J) := by group
      _ = e⁻¹ * (J * (k * e * n)) := by rw [h2]
      _ = (e⁻¹ * J) * (k * e * n) := by group
      _ = J * (e⁻¹ * (k * e * n)) := by rw [h3]; group
  have ha : e⁻¹ * k * e ∈ K₀ := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hJK₀ he)) k).mp hk
    simpa using this
  have e1 : n = (e⁻¹ * k * e)⁻¹ * (e⁻¹ * (k * e * n)) := by group
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (K₀.inv_mem ha)) (Subgroup.mem_sup_left hb)

theorem normalizer_le_normalizer_centralizer' (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
  intro g hg
  apply JT.mem_normalizer_of_conj_mem
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : g⁻¹ * q * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
    simpa using this
  have := Subgroup.mem_centralizer_iff.mp hc _ hq'
  calc q * (g * c * g⁻¹) = g * ((g⁻¹ * q * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * q * g)) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * q := by group

omit [Finite G] in
theorem comm_of_inv {Q : Subgroup G} {J : G} (hJQ : ∀ q ∈ Q, J * q * J⁻¹ = q⁻¹) :
    ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  intro a ha b hb
  have h1 := hJQ _ (Q.mul_mem ha hb)
  have h2 : J * (a * b) * J⁻¹ = (J * a * J⁻¹) * (J * b * J⁻¹) := by group
  rw [h2, hJQ a ha, hJQ b hb] at h1
  have h3 : (b * a)⁻¹ = (a * b)⁻¹ := by rw [mul_inv_rev, h1]
  exact (inv_injective h3).symm

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

theorem eq_one_of_inv {A : Subgroup G} (hA : IsPGroup r A) {t u : G} (ht2 : t * t = 1)
    (htA : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) (huA : u ∈ Subgroup.centralizer (A : Set G))
    (hu2 : u * u = 1) (hu1 : u ≠ 1) : ∀ a ∈ A, a = 1 := by
  intro a ha
  have huo : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hua : ∀ b ∈ A, u * b * u⁻¹ = b := fun b hb => by
    rw [← Subgroup.mem_centralizer_iff.mp huA b hb, mul_inv_cancel_right]
  have haP : IsPGroup r (Subgroup.zpowers a) := hA.to_le (Subgroup.zpowers_le.mpr ha)
  set v := u * t with hv
  have hvA : ∀ b ∈ A, v * b * v⁻¹ = b⁻¹ := fun b hb => by
    have e : v * b * v⁻¹ = u * (t * b * t⁻¹) * u⁻¹ := by rw [hv]; group
    rw [e, htA b hb, hua _ (A.inv_mem hb)]
  have hvN : v ∈ Subgroup.normalizer (A : Set G) :=
    JT.mem_normalizer_of_conj_mem fun b hb => by rw [hvA b hb]; exact A.inv_mem hb
  have hv2C : v ^ 2 ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have e : v ^ 2 * b * (v ^ 2)⁻¹ = v * (v * b * v⁻¹) * v⁻¹ := by rw [pow_two]; group
    have e2 : v ^ 2 * b * (v ^ 2)⁻¹ = b := by rw [e, hvA b hb, hvA _ (A.inv_mem hb), inv_inv]
    calc b * v ^ 2 = v ^ 2 * b * (v ^ 2)⁻¹ * v ^ 2 := by rw [e2]
      _ = v ^ 2 * b := by group
  have htv1 : t * v * t⁻¹ = v⁻¹ := by
    rw [show v⁻¹ = t * u by rw [hv, mul_inv_rev, htinv, huinv], hv]
    group
  have huv1 : u * v * u⁻¹ = v⁻¹ := by
    rw [show v⁻¹ = t * u by rw [hv, mul_inv_rev, htinv, huinv], hv, huinv]
    calc u * (u * t) * u = (u * u) * t * u := by group
      _ = t * u := by rw [hu2, one_mul]
  have htv : ∀ n : ℕ, t * (v ^ n)⁻¹ = v ^ n * t := fun n => by
    have e : t * (v ^ n)⁻¹ * t⁻¹ = v ^ n := by
      calc t * (v ^ n)⁻¹ * t⁻¹ = (t * v ^ n * t⁻¹)⁻¹ := by group
        _ = ((t * v * t⁻¹) ^ n)⁻¹ := by rw [conj_pow]
        _ = v ^ n := by rw [htv1, inv_pow, inv_inv]
    calc t * (v ^ n)⁻¹ = t * (v ^ n)⁻¹ * t⁻¹ * t := by group
      _ = v ^ n * t := by rw [e]
  have huvn : ∀ n : ℕ, u * (v ^ n)⁻¹ = v ^ n * u := fun n => by
    have e : u * (v ^ n)⁻¹ * u⁻¹ = v ^ n := by
      calc u * (v ^ n)⁻¹ * u⁻¹ = (u * v ^ n * u⁻¹)⁻¹ := by group
        _ = ((u * v * u⁻¹) ^ n)⁻¹ := by rw [conj_pow]
        _ = v ^ n := by rw [huv1, inv_pow, inv_inv]
    calc u * (v ^ n)⁻¹ = u * (v ^ n)⁻¹ * u⁻¹ * u := by group
      _ = v ^ n * u := by rw [e]
  rcases Nat.even_or_odd (orderOf v) with ⟨m', hm'⟩ | ⟨c, hc⟩
  ·
    have hm0 : 0 < orderOf v := orderOf_pos v
    have hm'0 : m' ≠ 0 := by omega
    have hz1 : v ^ m' ≠ 1 := pow_ne_one_of_lt_orderOf hm'0 (by omega)
    have hz2 : v ^ m' * v ^ m' = 1 := by
      rw [← pow_add, ← hm', pow_orderOf_eq_one]
    have hzinv : (v ^ m')⁻¹ = v ^ m' := inv_eq_of_mul_eq_one_right hz2
    have hzo : orderOf (v ^ m') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    have htz : t * v ^ m' = v ^ m' * t := by
      have := htv m'
      rwa [hzinv] at this
    have huz : u * v ^ m' = v ^ m' * u := by
      have := huvn m'
      rwa [hzinv] at this
    rcases Nat.even_or_odd m' with ⟨i, hi⟩ | ⟨i, hi⟩
    ·
      have hzC : v ^ m' ∈ Subgroup.centralizer (A : Set G) := by
        rw [hi, ← two_mul, pow_mul]
        exact Subgroup.pow_mem _ hv2C i
      exact h.no_real (v ^ m') a t hzo
        (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzC a ha))
        (Subgroup.mem_centralizer_singleton_iff.mpr htz) ht2 (htA a ha) haP
    ·
      have hzA : v ^ m' * a * (v ^ m')⁻¹ = a⁻¹ := by
        have hC := Subgroup.pow_mem _ hv2C i
        have e : v ^ m' = v * (v ^ 2) ^ i := by rw [hi, ← pow_mul, ← pow_succ']
        have hci : (v ^ 2) ^ i * a * ((v ^ 2) ^ i)⁻¹ = a := by
          rw [← Subgroup.mem_centralizer_iff.mp hC a ha, mul_inv_cancel_right]
        calc v ^ m' * a * (v ^ m')⁻¹ = v * ((v ^ 2) ^ i * a * ((v ^ 2) ^ i)⁻¹) * v⁻¹ := by
              rw [e]; group
          _ = a⁻¹ := by rw [hci, hvA a ha]
      exact h.no_real u a (v ^ m') huo
        (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp huA a ha))
        (Subgroup.mem_centralizer_singleton_iff.mpr huz.symm) hz2 hzA haP
  ·
    have hug : v ^ (c + 1) * t * (v ^ (c + 1))⁻¹ = u := by
      have e1 : v ^ (c + 1) * t * (v ^ (c + 1))⁻¹ = v ^ (c + 1) * (t * (v ^ (c + 1))⁻¹) := by
        group
      rw [e1, htv (c + 1), ← mul_assoc, ← pow_add,
        show c + 1 + (c + 1) = orderOf v + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul,
        hv, mul_assoc, ht2, mul_one]
    have hgN : v ^ (c + 1) ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hvN _
    have hga : v ^ (c + 1) * a * (v ^ (c + 1))⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hgN a).mp ha
    have hta : t * a * t⁻¹ = a := by
      have ht : t = (v ^ (c + 1))⁻¹ * u * v ^ (c + 1) := by rw [← hug]; group
      rw [ht]
      calc (v ^ (c + 1))⁻¹ * u * v ^ (c + 1) * a * ((v ^ (c + 1))⁻¹ * u * v ^ (c + 1))⁻¹
          = (v ^ (c + 1))⁻¹ * (u * (v ^ (c + 1) * a * (v ^ (c + 1))⁻¹) * u⁻¹) * v ^ (c + 1) := by
            group
        _ = (v ^ (c + 1))⁻¹ * (v ^ (c + 1) * a * (v ^ (c + 1))⁻¹) * v ^ (c + 1) := by
            rw [hua _ hga]
        _ = a := by group
    have h1 := htA a ha
    rw [hta] at h1
    refine h.eq_one_of_sq hA ha ?_
    calc a * a = a * a⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel a

theorem mem_H₃_of_coprime {g : G} (hg : g ∈ Subgroup.centralizer ({J} : Set G))
    (hcop : Nat.Coprime r (orderOf g)) : g ∈ H₃ := by
  obtain ⟨k, hk⟩ := h.P₀_r.exists_card_eq
  have hcop' : Nat.Coprime (Nat.card P₀) (orderOf g) := by rw [hk]; exact hcop.pow_left k
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop'
  rw [← hm]
  exact H₃.pow_mem (h.H_pow g hg) m

theorem no_involution_of_J {Q : Subgroup G} (hQ : IsPGroup r Q)
    (hJQ : ∀ q ∈ Q, J * q * J⁻¹ = q⁻¹) (hQ1 : Q ≠ ⊥) :
    ∀ u ∈ Subgroup.centralizer (Q : Set G), u * u = 1 → u = 1 := by
  intro u hu hu2
  by_contra hu1
  apply hQ1
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  exact h.eq_one_of_inv hQ h.J_mul_J hJQ hu hu2 hu1 q hq

theorem false_of_inv (T : Sylow r G) {Q : Subgroup G} (hQr : IsPGroup r Q) (hQ1 : Q ≠ ⊥)
    (hJQ : ∀ q ∈ Q, J * q * J⁻¹ = q⁻¹) (hweak : WeaklyClosedIn (T : Subgroup G) Q)
    (hP₀Q : P₀ ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : ∀ g ∈ Subgroup.centralizer (Q : Set G), orderOf g = r → g ∈ Q) : False := by
  have hab := comm_of_inv hJQ
  have htop := hallPResidual_normalizer_eq_top h.perfect T hweak
    (Or.inl (engelSymbol_eq_one_of_comm h.three_le hab))
  have hJN : J ∈ Subgroup.normalizer (Q : Set G) :=
    JT.mem_normalizer_of_conj_mem fun q hq => by rw [hJQ q hq]; exact Q.inv_mem hq
  set N := Subgroup.normalizer (Q : Set G) with hN
  set C := Subgroup.centralizer (Q : Set G) with hC
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hNC : N ≤ Subgroup.normalizer (C : Set G) := normalizer_le_normalizer_centralizer' Q
  have h2 := h.factorization_two_le_of hQr (h.no_involution_of_J hQr hJQ hQ1) (le_refl N)
  have hcover := le_sup_of_conj_mem h.orderOf_J hJN hCN hNC h2 (fun n hn => by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : n⁻¹ * q * n ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) q).mp hq
      simpa using this
    have h1 : J * (n⁻¹ * q * n) * J⁻¹ = (n⁻¹ * q * n)⁻¹ := hJQ _ hq'
    have h3 : J⁻¹ * q⁻¹ * J = q := by
      have := hJQ _ (Q.inv_mem hq)
      calc J⁻¹ * q⁻¹ * J = J * q⁻¹ * J⁻¹ := by rw [h.J_inv]
        _ = q := by rw [this, inv_inv]
    have key : (J⁻¹ * (n * J * n⁻¹)) * q * (J⁻¹ * (n * J * n⁻¹))⁻¹ = q := by
      calc (J⁻¹ * (n * J * n⁻¹)) * q * (J⁻¹ * (n * J * n⁻¹))⁻¹
          = J⁻¹ * (n * (J * (n⁻¹ * q * n) * J⁻¹) * n⁻¹) * J := by group
        _ = J⁻¹ * (n * (n⁻¹ * q * n)⁻¹ * n⁻¹) * J := by rw [h1]
        _ = J⁻¹ * q⁻¹ * J := by group
        _ = q := h3
    calc q * (J⁻¹ * (n * J * n⁻¹)) =
        ((J⁻¹ * (n * J * n⁻¹)) * q * (J⁻¹ * (n * J * n⁻¹))⁻¹) * (J⁻¹ * (n * J * n⁻¹)) := by
          rw [key]
      _ = J⁻¹ * (n * J * n⁻¹) * q := by group)
  refine hallPResidual_ne_top (N := N) (K₀ := C) (H := Subgroup.centralizer ({J} : Set G))
    (H₃ := H₃) (P₀ := P₀) hNC hCN hcover h.H_pow ?_ (le_inf hP₀Q h.P₀_le) h.P₀_H₃ h.P₀_ne_bot
    h.P₀_r htop
  intro g hg
  obtain ⟨hg1, hgC⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨-, hgJ⟩ := Subgroup.mem_inf.mp hg1
  apply h.mem_H₃_of_coprime hgJ
  apply (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
  intro hdvd
  have ho : orderOf (g ^ (orderOf g / r)) = r := orderOf_pow_orderOf_div (orderOf_pos g).ne' hdvd
  have hg'C : g ^ (orderOf g / r) ∈ C := C.pow_mem hgC _
  have hg'J : g ^ (orderOf g / r) ∈ Subgroup.centralizer ({J} : Set G) :=
    Subgroup.pow_mem _ hgJ _
  have hg'Q := hCQ _ hg'C ho
  have h1 := hJQ _ hg'Q
  rw [← Subgroup.mem_centralizer_singleton_iff.mp hg'J, mul_inv_cancel_right] at h1
  have h1' : g ^ (orderOf g / r) = 1 := h.eq_one_of_sq hQr hg'Q (by
    calc g ^ (orderOf g / r) * g ^ (orderOf g / r)
        = g ^ (orderOf g / r) * (g ^ (orderOf g / r))⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel _)
  rw [h1', orderOf_one] at ho
  exact (Fact.out : r.Prime).one_lt.ne ho

end Hyp62

end CFSG.Walter.W67.Sec6
