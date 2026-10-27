module

public import CFSG.Walter.ReeOrder.JT.Section6E

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

namespace JTHyp

variable (h : JTHyp G) (hp : h.p ≠ 2) (hp3 : h.p ≠ 3) (hS : SuzukiFourGroupTheorem)
  (hH : HuppertMetacyclicTheorem)
include hp hp3 hS hH

theorem q_mod_three :
    h.q % 3 = 2 := by
  obtain ⟨s⟩ := h.nonempty_setup hp
  have h3Q := s.lemma_4_5 hp hS hH
  have h3m := s.three_dvd_m hp hp3 h3Q
  have hm := s.m_add hp
  have hq5 := h.lemma_4_6_c hp hp3 hS hH
  rcases s.four_mul_card_Q_cases hp with ⟨h4, -⟩ | ⟨-, h4⟩
  · omega
  · omega

end JTHyp

namespace JTHyp

variable (h : JTHyp G) (hp : h.p ≠ 2) (hp3 : h.p ≠ 3) (hq3 : h.q % 3 = 2)
include hp hp3 hq3

theorem not_three_dvd_card_of_odd
    {u : G} (hu : orderOf u = 2) {Y : Subgroup G}
    (hYu : Y ≤ Subgroup.centralizer ({u} : Set G)) (hYodd : Odd (Nat.card Y))
    (hq : h.q ∣ Nat.card Y) : ¬ 3 ∣ Nat.card Y := by
  have h3q1 : ¬ 3 ∣ (h.q - 1) / 2 := by
    obtain ⟨k, hk⟩ := h.odd_q hp
    omega
  rcases h.odd_cases hp hu hYu hYodd with ⟨-, -, -, -, m, t, -, -, hYcard, htq, -⟩ | hdvd
  · rw [hYcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : h.p.Prime)).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      exact hp3 this.symm
    · exact h3q1 (h3.trans htq)
  · exfalso
    have hq1 : 1 < h.q := by
      have h5 := h.five_lt
      rw [← JTHyp.q_eq] at h5
      omega
    have := Nat.le_of_dvd (by omega) (hq.trans hdvd)
    omega

end JTHyp

namespace BorelData

variable {h : JTHyp G} {b : BorelData h}

namespace M1Data

variable (d : b.M1Data) (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5) (hp3 : h.p ≠ 3)
  (hq3 : h.q % 3 = 2)
include d hp hq5 hp3 hq3

theorem not_three_dvd_of_le_R
    {D : Subgroup G} (hDR : D ≤ b.R) (hD1 : D ≠ ⊥) :
    ¬ 3 ∣ Nat.card (Subgroup.normalizer (D : Set G)) := by
  classical
  have hDp : IsPGroup h.p D := b.isPGroup_R.to_le hDR
  have htD : h.t ∈ Subgroup.normalizer (D : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun _ hx => b.R_comm_t (hDR hx))
  have hτD : b.τ ∈ Subgroup.normalizer (D : Set G) :=
    mem_normalizer_of_conj_mem fun x hx => by rw [b.τ_inv x (hDR hx)]; exact D.inv_mem hx
  have hTD := b.T_le_normalizer htD hτD
  have hPD : d.P ≤ Subgroup.normalizer (D : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      d.commute hp hq5 hp3 (d.R_le (hDR hy)) hx)
  have htτ1 : h.t * b.τ ≠ 1 := by
    have := b.orderOf_eq_two (Or.inr (Or.inr rfl))
    intro h0
    rw [h0, orderOf_one] at this
    omega
  have hDt : Nat.card (D ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) = Nat.card D := by
    rw [inf_eq_left.mpr fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (b.R_comm_t (hDR hx))]
  have hDtτ : Nat.card (D ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) : Subgroup G) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro x hx
    have hxR := hDR hx.1
    have h1 : h.t * b.τ * x * (h.t * b.τ)⁻¹ = x⁻¹ := by
      calc h.t * b.τ * x * (h.t * b.τ)⁻¹ = h.t * (b.τ * x * b.τ⁻¹) * h.t⁻¹ := by group
        _ = h.t * x⁻¹ * h.t⁻¹ := by rw [b.τ_inv x hxR]
        _ = x⁻¹ := by
          rw [← (Commute.inv_left (b.R_comm_t hxR : Commute x h.t)).eq, mul_inv_cancel_right]
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [← h2, mul_inv_cancel_right] at h1
    have hxx : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel x
    exact Subgroup.mem_bot.mpr (eq_one_of_mul_self_of_odd hxx (Odd.of_dvd_nat
      (h.odd_card_of_isPGroup hp hDp) (Subgroup.orderOf_dvd_natCard _ hx.1)))
  have huw : ∀ g ∈ Subgroup.normalizer (D : Set G), g * h.t * g⁻¹ ≠ h.t * b.τ := by
    intro g hg hgt
    have := card_inf_le_of_conj hg hgt
    rw [hDt, hDtτ, Subgroup.card_le_one_iff_eq_bot] at this
    exact hD1 this
  obtain ⟨M, hMN, hModd, hMn, hMmem, hMcard⟩ := exists_odd_normal_of_kleinFour b.isKleinFour_T
    hTD (h.not_eight_dvd hp hDp hD1) b.t_mem_T (b.mem_T_iff.mpr (Or.inl rfl)) h.t_ne_one htτ1
    huw
  have hPM : d.P ≤ M := fun x hx => hMmem x (hPD hx)
    (Odd.of_dvd_nat (h.odd_card_of_isPGroup hp d.isPGroup) (Subgroup.orderOf_dvd_natCard _ hx))
  have hMu : ∀ {u : G}, (u = h.t ∨ u = b.τ ∨ u = h.t * b.τ) →
      ¬ 3 ∣ Nat.card (M ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
    intro u hu
    refine h.not_three_dvd_card_of_odd hp hp3 hq3 (b.orderOf_eq_two hu) inf_le_right
      (Odd.of_dvd_nat hModd (Subgroup.card_dvd_of_le inf_le_left)) ?_
    rw [← d.card_inf hp hq5 hp3 hu]
    exact Subgroup.card_dvd_of_le (inf_le_inf_right _ hPM)
  have hBW := b.card_mul_sq M (hMn _ htD) (hMn _ hτD) hModd
  have h3M : ¬ 3 ∣ Nat.card M := by
    intro h3
    have : 3 ∣ Nat.card (M ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) *
        Nat.card (M ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) *
        Nat.card (M ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) : Subgroup G) := by
      rw [← hBW]
      exact Dvd.dvd.mul_right h3 _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp this with h1 | h1
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
      · exact hMu (Or.inl rfl) h2
      · exact hMu (Or.inr (Or.inl rfl)) h2
    · exact hMu (Or.inr (Or.inr rfl)) h1
  rw [hMcard]
  intro h3
  exact h3M ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 4)) h3)

theorem not_mem_normalizer
    {u : G} (hu : orderOf u = 2) {D : Subgroup G}
    (hDu : D ≤ Subgroup.centralizer ({u} : Set G)) (hDp : IsPGroup h.p D) (hD1 : D ≠ ⊥)
    {y : G} (hy : orderOf y = 3) : y ∉ Subgroup.normalizer (D : Set G) := by
  classical
  intro hyD
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hu
  set D' := D.map (MulAut.conj g).toMonoidHom with hD'def
  have hD't : D' ≤ Subgroup.centralizer ({h.t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hxu := Subgroup.mem_centralizer_singleton_iff.mp (hDu hx)
    change g * x * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  have hD'p : IsPGroup h.p D' := hDp.map _
  have hD'F : D' ≤ h.F := h.le_F_of_odd hD't (h.odd_card_of_isPGroup hp hD'p)
  obtain ⟨R', hD'R', hR'F, hR'⟩ := (psl2UnipotentFacts h.F h.iso hp h.f_pos).exists_le D' hD'F
    hD'p
  obtain ⟨g', hg'⟩ := h.exists_conj_of_card_eq hp b.R_le_F b.card_R h.orderOf_t
    (hR'F.trans h.le_centralizer) (by rw [hR', JTHyp.q_eq])
  set D'' := D'.map (MulAut.conj g').toMonoidHom with hD''def
  have hD''R : D'' ≤ b.R := by
    rw [← hg']
    exact Subgroup.map_mono hD'R'
  have hD''1 : D'' ≠ ⊥ := by
    rw [Ne, hD''def, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g').injective, hD'def,
      Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
    exact hD1
  have hconj : ∀ {X : Subgroup G} {a z : G}, z ∈ Subgroup.normalizer (X : Set G) →
      a * z * a⁻¹ ∈ Subgroup.normalizer ((X.map (MulAut.conj a).toMonoidHom : Subgroup G) :
        Set G) := by
    intro X a z hz
    have := Subgroup.le_normalizer_map (MulAut.conj a).toMonoidHom ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using this
  have hy'' : g' * (g * y * g⁻¹) * g'⁻¹ ∈ Subgroup.normalizer (D'' : Set G) :=
    hconj (hconj hyD)
  have hy''o : orderOf (g' * (g * y * g⁻¹) * g'⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  apply d.not_three_dvd_of_le_R hp hq5 hp3 hq3 hD''R hD''1
  rw [← hy''o]
  exact Subgroup.orderOf_dvd_natCard _ hy''

end M1Data

end BorelData

end CFSG.Walter.JT
