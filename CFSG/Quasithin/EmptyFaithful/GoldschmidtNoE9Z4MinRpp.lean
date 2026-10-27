module

import Mathlib.Tactic.Group
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinPair

public section

namespace CFSG.Quasithin.NoE9Z4MinGrp

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem rpp_conj_comm (y a b : G) : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem rpp_comm_inv_right {x : G} (hx : x * x = 1) (r : G) :
    ⁅x, r⁻¹⁆ = x * (r⁻¹ * x * r) := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_left hx]
  group

theorem rpp_comm_mem_U {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z) {u h : G}
    (hu : u ∈ U) (hh : h ∈ Hs) : ⁅u, h⁆ ∈ U := by
  have e : ⁅u, h⁆ = u * (h * u⁻¹ * h⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact U.mul_mem hu (P.normU h hh u⁻¹ (U.inv_mem hu))

theorem rpp_pair_comm {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z) {x q r : G}
    (hx : x ∈ U) (hq : q ∈ Q) (hr : r ∈ Hs) : ⁅x, ⁅q, r⁆⁆ = ⁅x * (r⁻¹ * x * r), q⁆ := by
  have hrq : r * q⁻¹ * r⁻¹ ∈ Q := P.normQ r hr q⁻¹ (Q.inv_mem hq)
  have hx' : r⁻¹ * x * r ∈ U := by simpa using P.normU r⁻¹ (Hs.inv_mem hr) x hx
  have e1 : ⁅q, r⁆ = q * (r * q⁻¹ * r⁻¹) := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅x, r * q⁻¹ * r⁻¹⁆ = ⁅r⁻¹ * x * r, q⁻¹⁆ := by
    have h := P.pair_conj hr hx' (Q.inv_mem hq)
    have e3 : r * (r⁻¹ * x * r) * r⁻¹ = x := by group
    rwa [e3] at h
  rw [e1, P.pair_mul_right hx hq hrq, e2, P.pair_inv_right hx' hq, P.pair_mul_left hx hx' hq,
    inv_eq_of_mul_eq_one_left (P.pair_sq hx' hq)]

theorem rpp_exists_pair {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z)
    {V : Subgroup G} (hZV : Z ≤ V) {v w : G} (hv : v ∈ U) (hvV : v ∈ V) (hvZ : v ∉ Z)
    (hw : w ∈ U) (hwV : w ∉ V) : ∃ q ∈ Q, ⁅v, q⁆ = 1 ∧ ⁅w, q⁆ = z := by
  by_contra hcon
  have h1 : ∀ q ∈ Q, ⁅v, q⁆ = 1 → ⁅w, q⁆ = 1 := fun q hq hvq =>
    (P.Z_eq _ (P.pair_mem w hw q hq)).resolve_right fun hwz => hcon ⟨q, hq, hvq, hwz⟩
  obtain ⟨q₀, hq₀, hvq₀⟩ : ∃ q₀ ∈ Q, ⁅v, q₀⁆ ≠ 1 := by
    by_contra hno
    exact hvZ (P.ker_right v hv fun q hq => by_contra fun hne => hno ⟨q, hq, hne⟩)
  have hvq₀z : ⁅v, q₀⁆ = z := (P.Z_eq _ (P.pair_mem v hv q₀ hq₀)).resolve_left hvq₀
  have h2 : ∀ q ∈ Q, ⁅v, q⁆ ≠ 1 → ⁅v, q⁆ = z ∧ ⁅w, q⁆ = ⁅w, q₀⁆ := by
    intro q hq hvq
    have hvqz : ⁅v, q⁆ = z := (P.Z_eq _ (P.pair_mem v hv q hq)).resolve_left hvq
    refine ⟨hvqz, ?_⟩
    have hmul : ⁅v, q * q₀⁆ = 1 := by
      rw [P.pair_mul_right hv hq hq₀, hvqz, hvq₀z]
      exact P.Z_sq P.z_mem
    have h := h1 (q * q₀) (Q.mul_mem hq hq₀) hmul
    rw [P.pair_mul_right hw hq hq₀] at h
    exact mul_right_cancel (h.trans (P.pair_sq hw hq₀).symm)
  rcases P.Z_eq _ (P.pair_mem w hw q₀ hq₀) with hε | hε
  · refine hwV (hZV (P.ker_right w hw fun q hq => ?_))
    by_cases hvq : ⁅v, q⁆ = 1
    · exact h1 q hq hvq
    · rw [(h2 q hq hvq).2, hε]
  · have hvw : v * w ∈ Z := by
      refine P.ker_right (v * w) (U.mul_mem hv hw) fun q hq => ?_
      rw [P.pair_mul_left hv hw hq]
      by_cases hvq : ⁅v, q⁆ = 1
      · rw [hvq, h1 q hq hvq, mul_one]
      · obtain ⟨hvqz, hwq⟩ := h2 q hq hvq
        rw [hvqz, hwq, hε]
        exact P.Z_sq P.z_mem
    refine hwV ?_
    have e : w = v⁻¹ * (v * w) := by group
    rw [e]
    exact V.mul_mem (V.inv_mem hvV) (hZV hvw)

theorem rpp_conj_z {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z) {R : Subgroup G}
    {y : G} (hQ' : ∀ x ∈ Q, ∀ x' ∈ Q, ⁅x, x'⁆ ∈ Z) (hRQ : ∀ a ∈ R, ∀ b ∈ R, ⁅a, b⁆ ∈ Q)
    (hy : ∀ a ∈ R, y * a * y⁻¹ ∈ R) {a b c : G} (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R)
    (h : ⁅⁅a, b⁆, ⁅c, b⁆⁆ = z) : y * z * y⁻¹ = z := by
  have hR'Q : ⁅R, R⁆ ≤ Q := Subgroup.commutator_le.2 hRQ
  have hR''Z : ⁅⁅R, R⁆, ⁅R, R⁆⁆ ≤ Z :=
    Subgroup.commutator_le.2 fun a ha b hb => hQ' a (hR'Q ha) b (hR'Q hb)
  have hmem : y * z * y⁻¹ ∈ Z := by
    rw [← h, rpp_conj_comm, rpp_conj_comm, rpp_conj_comm]
    exact hR''Z (Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (hy a ha) (hy b hb))
      (Subgroup.commutator_mem_commutator (hy c hc) (hy b hb)))
  refine (P.Z_eq _ hmem).resolve_left fun h1 => P.z_ne ?_
  calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
    _ = 1 := by rw [h1]; group

theorem rpp_false {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z)
    (T V : Subgroup G) (y : G)
    (hQ' : ∀ x ∈ Q, ∀ x' ∈ Q, ⁅x, x'⁆ ∈ Z)
    (hTH : T ≤ Hs) (hQT : Q ≤ T) (hTQ : ∀ x ∈ T, ∀ x' ∈ T, ⁅x, x'⁆ ∈ Q)
    (hVU : V ≤ U) (hZV : Z ≤ V)
    (hV : ∃ v ∈ V, v ∉ Z ∧ ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z)
    (hS1 : ∃ r ∈ T ⊓ Subgroup.centralizer (V : Set G), ∃ u₀ ∈ U, ⁅⁅u₀, r⁆, r⁻¹⁆ ∉ V)
    (hy : y ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hyz : y * z * y⁻¹ ≠ z) : False := by
  obtain ⟨v, hvV, hvZ, hV4⟩ := hV
  obtain ⟨r, hr, u₀, hu₀, hw⟩ := hS1
  have hrT : r ∈ T := (Subgroup.mem_inf.1 hr).1
  have hrH : r ∈ Hs := hTH hrT
  have hu₀R : u₀ ∈ T ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.mem_inf.2 ⟨hQT (P.U_le_Q hu₀), Subgroup.mem_centralizer_iff.2 fun h hh =>
      P.U_comm h (hVU hh) u₀ hu₀⟩
  have hxU : ⁅u₀, r⁆ ∈ U := rpp_comm_mem_U P hu₀ hrH
  have hwU : ⁅⁅u₀, r⁆, r⁻¹⁆ ∈ U := rpp_comm_mem_U P hxU (Hs.inv_mem hrH)
  obtain ⟨q, hqQ, hvq, hwq⟩ := rpp_exists_pair P hZV (hVU hvV) hvV hvZ hwU hw
  have hqR : q ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hQT hqQ, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have hvq' : Commute v q := commutatorElement_eq_one_iff_mul_comm.1 hvq
    have hzq : Commute z q := (P.z_cent q (P.Q_le_H hqQ)).symm
    rcases hV4 h hh with h1 | h1 | h1 | h1
    · rw [h1, one_mul, mul_one]
    · rw [h1]
      exact hzq
    · rw [h1]
      exact hvq'
    · rw [h1]
      exact hvq'.mul_left hzq
  have hxc : ⁅⁅u₀, r⁆, ⁅q, r⁆⁆ = z := by
    rw [rpp_pair_comm P hxU hqQ hrH, ← rpp_comm_inv_right (P.U_sq _ hxU) r]
    exact hwq
  exact hyz (rpp_conj_z (R := T ⊓ Subgroup.centralizer (V : Set G)) P hQ'
    (fun a ha b hb => hTQ a ha.1 b hb.1)
    (fun a ha => (Subgroup.mem_set_normalizer_iff.1 hy a).1 ha) hu₀R hr hqR hxc)

end CFSG.Quasithin.NoE9Z4MinGrp
