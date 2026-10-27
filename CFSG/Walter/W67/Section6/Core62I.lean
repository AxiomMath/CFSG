module

public import CFSG.Walter.W67.Section6.Core62H

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_Vsub {x₀ y₀ u : G} (hx : u * x₀ = x₀ * u) (hy : u * y₀ = y₀ * u) :
    u ∈ Subgroup.centralizer ((Vsub x₀ y₀ : Subgroup G) : Set G) := by
  have hle : Vsub x₀ y₀ ≤ Subgroup.centralizer ({u} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hx.symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hy.symm))
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)

omit [Finite G] in
theorem conj_pow_eq_pow_pow {g y : G} {m : ℕ} (hg : g * y * g⁻¹ = y ^ m) (n : ℕ) :
    g ^ n * y * (g ^ n)⁻¹ = y ^ (m ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc g ^ (n + 1) * y * (g ^ (n + 1))⁻¹ = g * (g ^ n * y * (g ^ n)⁻¹) * g⁻¹ := by
          rw [pow_succ']; group
      _ = (g * y * g⁻¹) ^ (m ^ n) := by rw [ih, conj_pow]
      _ = y ^ (m ^ (n + 1)) := by rw [hg, ← pow_mul, pow_succ', mul_comm]

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

theorem le_normalizer_of_isT {S : Subgroup G} (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S)
    (hx : IsT S y₀ r x₀) : S ≤ Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) := by
  intro s hs
  apply JT.mem_normalizer_of_conj_mem
  intro p hp
  rw [← h.inf_centralizer_eq hS hPS]
  refine Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem hs (hPS hp)) (S.inv_mem hs), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc := hx.2.2 _ (S.inv_mem hs)
  rw [inv_inv] at hc
  have hcP : s⁻¹ * x₀ * s * x₀⁻¹ ∈ Subgroup.zpowers y₀ := hc
  have hpc : p * (s⁻¹ * x₀ * s * x₀⁻¹) = (s⁻¹ * x₀ * s * x₀⁻¹) * p := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcP
    rw [← hk]
    exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp h.y₀_mem_center p hp) k).eq
  have hpx : p * x₀ = x₀ * p := Subgroup.mem_centralizer_iff.mp h.x₀_mem_center p hp
  have e : s⁻¹ * x₀ * s = (s⁻¹ * x₀ * s * x₀⁻¹) * x₀ := by group
  have hp1 : p * (s⁻¹ * x₀ * s) = (s⁻¹ * x₀ * s) * p := by
    rw [e, ← mul_assoc, hpc, mul_assoc, hpx, ← mul_assoc]
  calc s * p * s⁻¹ * x₀ = s * (p * (s⁻¹ * x₀ * s)) * s⁻¹ := by group
    _ = s * ((s⁻¹ * x₀ * s) * p) * s⁻¹ := by rw [hp1]
    _ = x₀ * (s * p * s⁻¹) := by group

theorem exists_d₁ {S : Subgroup G} (hS : IsPGroup r S)
    (hScard : Nat.card S = r ^ (Nat.card G).factorization r) (hPS : P₀ ⊔ P₁ ≤ S)
    (hJS : J ∈ Subgroup.normalizer (S : Set G)) (hSP : ¬ S ≤ P₀ ⊔ P₁) (hx : IsT S y₀ r x₀)
    {m : ℕ} (hm : d * y₀ * d⁻¹ = y₀ ^ m) :
    ∃ d₁ : G, d₁ ∈ Subgroup.normalizer (S : Set G) ∧
      d₁ ∈ Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) ∧
      d₁ * x₀ * d₁⁻¹ = x₀ ∧ d₁ * y₀ * d₁⁻¹ = y₀ ^ m := by
  have hyC := h.y₀_mem_centralizer hS hPS hJS hSP
  have hSN := h.le_normalizer_of_isT hS hPS hx
  have hNV := h.normalizer_le
  have hdx : d * x₀ * d⁻¹ = x₀ := by
    rw [← Subgroup.mem_centralizer_iff.mp h.d_P₀ x₀ h.x₀_mem, mul_inv_cancel_right]
  have hdx' : d⁻¹ * x₀ * d = x₀ := by
    calc d⁻¹ * x₀ * d = d⁻¹ * (d * x₀ * d⁻¹) * d := by rw [hdx]
      _ = x₀ := by group
  have hdY : ∀ y ∈ Subgroup.zpowers y₀, d * y * d⁻¹ = y ^ m := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hm, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hdinvY : d⁻¹ * y₀ * d ∈ Subgroup.zpowers y₀ := by
    have hN : d ∈ Subgroup.normalizer ((Subgroup.zpowers y₀ : Subgroup G) : Set G) := by
      apply JT.mem_normalizer_of_conj_mem
      intro y hy
      rw [hdY y hy]
      exact Subgroup.pow_mem _ hy m
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) y₀).mp
      (Subgroup.mem_zpowers y₀)
    simpa using this
  set P := P₀ ⊔ P₁ with hP
  set K := Subgroup.normalizer (P : Set G) ⊓
    Subgroup.centralizer ((Vsub x₀ y₀ : Subgroup G) : Set G) with hK
  have hKN : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (K : Set G) := fun n hn =>
    mem_normalizer_inf (Subgroup.le_normalizer hn)
      (normalizer_le_normalizer_centralizer' _ (hNV hn))
  have hdS : cj d S ≤ S ⊔ K := by
    rintro _ ⟨s, hs, rfl⟩
    change d * s * d⁻¹ ∈ S ⊔ K
    have hcs := hx.2.2 s hs
    have h1 : (d * s * d⁻¹) * x₀ * (d * s * d⁻¹)⁻¹ = (s * x₀ * s⁻¹ * x₀⁻¹) ^ m * x₀ := by
      calc (d * s * d⁻¹) * x₀ * (d * s * d⁻¹)⁻¹ = d * s * (d⁻¹ * x₀ * d) * s⁻¹ * d⁻¹ := by group
        _ = (d * (s * x₀ * s⁻¹ * x₀⁻¹) * d⁻¹) * (d * x₀ * d⁻¹) := by rw [hdx']; group
        _ = (s * x₀ * s⁻¹ * x₀⁻¹) ^ m * x₀ := by rw [hdY _ hcs, hdx]
    have h2 : s ^ m * x₀ * (s ^ m)⁻¹ = (s * x₀ * s⁻¹ * x₀⁻¹) ^ m * x₀ := by
      rw [← hx.conj_pow hyC hs m]
      group
    have hy1 : s * (d⁻¹ * y₀ * d) = (d⁻¹ * y₀ * d) * s :=
      (IsT.comm_of_mem_zpowers hyC hdinvY hs).symm
    have hym' : s ^ m * y₀ = y₀ * s ^ m :=
      (Subgroup.mem_centralizer_iff.mp hyC _ (S.pow_mem hs m))
    set u := (s ^ m)⁻¹ * (d * s * d⁻¹) with hu
    have huN : u ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hSN (S.pow_mem hs m)))
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ h.d_mem_normalizer (hSN hs))
          (Subgroup.inv_mem _ h.d_mem_normalizer))
    have hux : u * x₀ = x₀ * u := by
      have e : u * x₀ * u⁻¹ = x₀ := by
        calc u * x₀ * u⁻¹ = (s ^ m)⁻¹ * ((d * s * d⁻¹) * x₀ * (d * s * d⁻¹)⁻¹) * s ^ m := by
              rw [hu]; group
          _ = (s ^ m)⁻¹ * (s ^ m * x₀ * (s ^ m)⁻¹) * s ^ m := by rw [h1, h2]
          _ = x₀ := by group
      calc u * x₀ = u * x₀ * u⁻¹ * u := by group
        _ = x₀ * u := by rw [e]
    have huy : u * y₀ = y₀ * u := by
      have e : u * y₀ * u⁻¹ = y₀ := by
        calc u * y₀ * u⁻¹ = (s ^ m)⁻¹ * (d * (s * (d⁻¹ * y₀ * d)) * s⁻¹ * d⁻¹) * s ^ m := by
              rw [hu]; group
          _ = (s ^ m)⁻¹ * y₀ * s ^ m := by rw [hy1]; group
          _ = y₀ := by
              calc (s ^ m)⁻¹ * y₀ * s ^ m = (s ^ m)⁻¹ * (y₀ * s ^ m) := by group
                _ = y₀ := by rw [← hym']; group
      calc u * y₀ = u * y₀ * u⁻¹ * u := by group
        _ = y₀ * u := by rw [e]
    have huK : u ∈ K := Subgroup.mem_inf.mpr ⟨huN, mem_centralizer_Vsub hux huy⟩
    have e : d * s * d⁻¹ = s ^ m * u := by rw [hu]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (S.pow_mem hs m)) (Subgroup.mem_sup_right huK)
  have hSL : S ≤ S ⊔ K := le_sup_left
  have hSc := card_eq_of_le_of_card_eq hSL hScard
  have hdSc : Nat.card (cj d S) = r ^ (Nat.card ↥(S ⊔ K)).factorization r := by
    rw [card_cj, hSc]
  obtain ⟨ℓ, hℓ, hℓS⟩ := exists_conj_of_sylowIn hSL hdS hSc hdSc
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := hSN.trans hKN
  rw [sup_comm] at hℓ
  obtain ⟨k, hk, s₁, hs₁, rfl⟩ := (mem_sup_iff_of_le_normalizer hSK).mp hℓ
  obtain ⟨hkN, hkC⟩ := Subgroup.mem_inf.mp hk
  have hcj : cj (k * s₁) S = cj k S := by rw [cj_mul, cj_eq_self_of_mem hs₁]
  refine ⟨k⁻¹ * d, ?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) h.d_mem_normalizer, ?_, ?_⟩
  · apply mem_normalizer_of_cj_eq
    rw [cj_mul, hℓS, hcj, ← cj_mul, inv_mul_cancel, cj_one]
  · have hkx := Subgroup.mem_centralizer_iff.mp hkC x₀ (mem_Vsub_left x₀ y₀)
    calc k⁻¹ * d * x₀ * (k⁻¹ * d)⁻¹ = k⁻¹ * (d * x₀ * d⁻¹) * k := by group
      _ = k⁻¹ * (x₀ * k) := by rw [hdx, mul_assoc]
      _ = x₀ := by rw [hkx]; group
  · have hky : ∀ y ∈ Subgroup.zpowers y₀, y * k = k * y := fun y hy =>
      Subgroup.mem_centralizer_iff.mp hkC y (Subgroup.mem_sup_right hy)
    calc k⁻¹ * d * y₀ * (k⁻¹ * d)⁻¹ = k⁻¹ * (d * y₀ * d⁻¹) * k := by group
      _ = k⁻¹ * (y₀ ^ m * k) := by rw [hm, mul_assoc]
      _ = y₀ ^ m := by
          rw [hky _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) m)]
          group

theorem exists_d' {S : Subgroup G} (hS : IsPGroup r S)
    (hScard : Nat.card S = r ^ (Nat.card G).factorization r) (hPS : P₀ ⊔ P₁ ≤ S)
    (hJS : J ∈ Subgroup.normalizer (S : Set G)) (hSP : ¬ S ≤ P₀ ⊔ P₁) (hx : IsT S y₀ r x₀) :
    ∃ d' : G, d' ∈ Subgroup.normalizer (S : Set G) ∧
      d' ∈ Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) ∧ d' * J = J * d' ∧
      d' * x₀ * d'⁻¹ = x₀ ∧ (∃ m : ℕ, d' * y₀ * d'⁻¹ = y₀ ^ m ∧ (m : ZMod r) ≠ 1) ∧
      Odd (orderOf d') := by
  have : Fact (1 < r) := ⟨(Fact.out : r.Prime).one_lt⟩
  obtain ⟨m, hm⟩ := h.exists_d_y₀
  have hym : ∀ n : ℕ, y₀ ^ n = y₀ ^ ((n : ZMod r)).val := fun n => by
    rw [ZMod.val_natCast, ← h.orderOf_y₀, pow_mod_orderOf]
  have hm1 : (m : ZMod r) ≠ 1 := by
    intro hk1
    apply h.d_y₀
    rw [hm, hym, hk1, ZMod.val_one, pow_one]
  have hmo : (m : ZMod r) ^ orderOf d = 1 := by
    have h1 := conj_pow_eq_pow_pow hm (orderOf d)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
    have h2 : y₀ ^ (m ^ orderOf d) = y₀ ^ 1 := by rw [← h1, pow_one]
    rw [pow_eq_pow_iff_modEq, h.orderOf_y₀] at h2
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    push_cast at this
    exact this
  obtain ⟨d₁, hd₁S, hd₁P, hd₁x, hd₁y⟩ := h.exists_d₁ hS hScard hPS hJS hSP hx hm
  set P := P₀ ⊔ P₁ with hP
  set X := Subgroup.zpowers x₀ with hX
  set Y := Subgroup.zpowers y₀ with hY
  set N' := Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G) ⊓
    Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (Y : Set G) with hN'
  set K' := N' ⊓ Subgroup.centralizer ((Vsub x₀ y₀ : Subgroup G) : Set G) with hK'
  have hJx : ∀ x ∈ X, J * x * J⁻¹ = x := fun x hx' => by
    have := h.P₀_le ((Subgroup.zpowers_le.mpr h.x₀_mem) hx')
    rw [← Subgroup.mem_centralizer_singleton_iff.mp this, mul_inv_cancel_right]
  have hJy : ∀ y ∈ Y, J * y * J⁻¹ = y⁻¹ := fun y hy =>
    h.P₁_inv y ((Subgroup.zpowers_le.mpr h.y₀_mem) hy)
  have hJN' : J ∈ N' := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hJS,
      h.J_mem_normalizer⟩, ?_⟩, ?_⟩
    · exact JT.mem_normalizer_of_conj_mem fun x hx' => by rw [hJx x hx']; exact hx'
    · exact JT.mem_normalizer_of_conj_mem fun y hy => by rw [hJy y hy]; exact Y.inv_mem hy
  have hd₁N' : d₁ ∈ N' := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hd₁S, hd₁P⟩,
      ?_⟩, ?_⟩
    · apply JT.mem_normalizer_of_conj_mem
      intro x hx'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
      rw [← conj_zpow, hd₁x]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
    · apply JT.mem_normalizer_of_conj_mem
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← conj_zpow, hd₁y]
      exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m) k
  have hN'P : N' ≤ Subgroup.normalizer (P : Set G) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hN'X : N' ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans inf_le_right
  have hN'Y : N' ≤ Subgroup.normalizer (Y : Set G) := inf_le_right
  have hK'N' : N' ≤ Subgroup.normalizer (K' : Set G) := fun n hn =>
    mem_normalizer_inf (Subgroup.le_normalizer hn)
      (normalizer_le_normalizer_centralizer' _ (h.normalizer_le (hN'P hn)))
  have h2 := h.factorization_two_le h.isPGroup_P le_rfl hN'P
  have hcomm : ∀ n ∈ N', J⁻¹ * (n * J * n⁻¹) ∈ K' := by
    intro n hn
    refine Subgroup.mem_inf.mpr ⟨N'.mul_mem (N'.inv_mem hJN') (N'.mul_mem (N'.mul_mem hn hJN')
      (N'.inv_mem hn)), mem_centralizer_Vsub ?_ ?_⟩
    · have hx' : n⁻¹ * x₀ * n ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN'X hn)) x₀).mp
          (Subgroup.mem_zpowers x₀)
        simpa using this
      have e : J⁻¹ * (n * J * n⁻¹) * x₀ * (J⁻¹ * (n * J * n⁻¹))⁻¹ =
          J⁻¹ * (n * (J * (n⁻¹ * x₀ * n) * J⁻¹) * n⁻¹) * J := by group
      have e2 : J⁻¹ * (n * J * n⁻¹) * x₀ * (J⁻¹ * (n * J * n⁻¹))⁻¹ = x₀ := by
        rw [e, hJx _ hx', h.J_inv]
        calc J * (n * (n⁻¹ * x₀ * n) * n⁻¹) * J = J * x₀ * J⁻¹ := by rw [h.J_inv]; group
          _ = x₀ := hJx x₀ (Subgroup.mem_zpowers x₀)
      calc J⁻¹ * (n * J * n⁻¹) * x₀ = J⁻¹ * (n * J * n⁻¹) * x₀ * (J⁻¹ * (n * J * n⁻¹))⁻¹ *
            (J⁻¹ * (n * J * n⁻¹)) := by group
        _ = x₀ * (J⁻¹ * (n * J * n⁻¹)) := by rw [e2]
    · have hy' : n⁻¹ * y₀ * n ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN'Y hn)) y₀).mp
          (Subgroup.mem_zpowers y₀)
        simpa using this
      have e : J⁻¹ * (n * J * n⁻¹) * y₀ * (J⁻¹ * (n * J * n⁻¹))⁻¹ =
          J⁻¹ * (n * (J * (n⁻¹ * y₀ * n) * J⁻¹) * n⁻¹) * J := by group
      have e2 : J⁻¹ * (n * J * n⁻¹) * y₀ * (J⁻¹ * (n * J * n⁻¹))⁻¹ = y₀ := by
        rw [e, hJy _ hy']
        calc J⁻¹ * (n * (n⁻¹ * y₀ * n)⁻¹ * n⁻¹) * J = J * y₀⁻¹ * J⁻¹ := by rw [h.J_inv]; group
          _ = y₀ := by rw [hJy _ (Y.inv_mem (Subgroup.mem_zpowers y₀)), inv_inv]
      calc J⁻¹ * (n * J * n⁻¹) * y₀ = J⁻¹ * (n * J * n⁻¹) * y₀ * (J⁻¹ * (n * J * n⁻¹))⁻¹ *
            (J⁻¹ * (n * J * n⁻¹)) := by group
        _ = y₀ * (J⁻¹ * (n * J * n⁻¹)) := by rw [e2]
  have hcov := le_sup_of_conj_mem h.orderOf_J hJN' inf_le_left hK'N' h2 hcomm hd₁N'
  obtain ⟨a, ha, k₂, hk₂, hak⟩ := exists_mul_of_mem_sup
    ((inf_le_left : N' ⊓ Subgroup.centralizer ({J} : Set G) ≤ N').trans hK'N') hcov
  obtain ⟨haN', haJ⟩ := Subgroup.mem_inf.mp ha
  have hk₂C := (Subgroup.mem_inf.mp hk₂).2
  have hae : a = d₁ * k₂⁻¹ := by rw [← hak]; group
  have hax : a * x₀ * a⁻¹ = x₀ := by
    have hk := Subgroup.mem_centralizer_iff.mp hk₂C x₀ (mem_Vsub_left x₀ y₀)
    rw [hae]
    calc d₁ * k₂⁻¹ * x₀ * (d₁ * k₂⁻¹)⁻¹ = d₁ * (k₂⁻¹ * (x₀ * k₂)) * d₁⁻¹ := by group
      _ = d₁ * x₀ * d₁⁻¹ := by rw [hk]; group
      _ = x₀ := hd₁x
  have hay : a * y₀ * a⁻¹ = y₀ ^ m := by
    have hk := Subgroup.mem_centralizer_iff.mp hk₂C y₀ (mem_Vsub_right x₀ y₀)
    rw [hae]
    calc d₁ * k₂⁻¹ * y₀ * (d₁ * k₂⁻¹)⁻¹ = d₁ * (k₂⁻¹ * (y₀ * k₂)) * d₁⁻¹ := by group
      _ = d₁ * y₀ * d₁⁻¹ := by rw [hk]; group
      _ = y₀ ^ m := hd₁y
  set α := (orderOf a).factorization 2 with hα
  have haS : a ∈ Subgroup.normalizer (S : Set G) :=
    (inf_le_left.trans (inf_le_left.trans inf_le_left) : N' ≤ _) haN'
  have haP : a ∈ Subgroup.normalizer (P : Set G) := hN'P haN'
  have haJ' : a * J = J * a := Subgroup.mem_centralizer_singleton_iff.mp haJ
  refine ⟨a ^ (2 ^ α), Subgroup.pow_mem _ haS _, Subgroup.pow_mem _ haP _,
    (Commute.pow_left (show Commute a J from haJ') _).eq, ?_,
    ⟨m ^ (2 ^ α), conj_pow_eq_pow_pow hay _, ?_⟩, ?_⟩
  · have := conj_pow_eq_pow_pow (g := a) (y := x₀) (m := 1) (by rw [pow_one]; exact hax) (2 ^ α)
    rwa [one_pow, pow_one] at this
  · push_cast
    intro h1
    apply hm1
    have hcop : Nat.Coprime (2 ^ α) (orderOf d) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr h.d_odd)
    have := (pow_gcd_eq_one (a := (m : ZMod r))).mpr ⟨h1, hmo⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  · have hdvd : 2 ^ α ∣ orderOf a := Nat.ordProj_dvd _ _
    rw [orderOf_pow' a (pow_ne_zero _ two_ne_zero), Nat.gcd_eq_right hdvd]
    exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (orderOf_pos a).ne')

end Hyp62

end CFSG.Walter.W67.Sec6
