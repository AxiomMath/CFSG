module

import Mathlib.Tactic.Group
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenPair

public section

namespace CFSG.Quasithin.NoE9Z4GenGrp

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem rpp_conj_comm (y a b : G) : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem rpp_comm_inv_right {x : G} (hx : x * x = 1) (r : G) :
    ⁅x, r⁻¹⁆ = x * (r⁻¹ * x * r) := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_left hx]
  group

theorem rpp_comm_mem_U {Q U Z Cq Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Cq Hs z) {u h : G}
    (hu : u ∈ U) (hh : h ∈ Hs) : ⁅u, h⁆ ∈ U := by
  have e : ⁅u, h⁆ = u * (h * u⁻¹ * h⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact U.mul_mem hu (P.normU h hh u⁻¹ (U.inv_mem hu))

theorem rpp_pair_comm {Q U Z Cq Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Cq Hs z)
    {x q r : G}
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

theorem rpp_exists_pair {Q U Z Cq Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Cq Hs z)
    {V : Subgroup G} {v w : G} (hv : v ∈ U) (hvV : v ∈ V) (hvC : v ∉ Cq)
    (hw : w ∈ U) (hwV : ∀ c ∈ Cq, w * c ∉ V) : ∃ q ∈ Q, ⁅v, q⁆ = 1 ∧ ⁅w, q⁆ = z := by
  by_contra hcon
  have h1 : ∀ q ∈ Q, ⁅v, q⁆ = 1 → ⁅w, q⁆ = 1 := fun q hq hvq =>
    (P.Z_eq _ (P.pair_mem w hw q hq)).resolve_right fun hwz => hcon ⟨q, hq, hvq, hwz⟩
  obtain ⟨q₀, hq₀, hvq₀⟩ : ∃ q₀ ∈ Q, ⁅v, q₀⁆ ≠ 1 := by
    by_contra hno
    exact hvC (P.ker_right v hv fun q hq => by_contra fun hne => hno ⟨q, hq, hne⟩)
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
  · have hwC : w ∈ Cq := by
      refine P.ker_right w hw fun q hq => ?_
      by_cases hvq : ⁅v, q⁆ = 1
      · exact h1 q hq hvq
      · rw [(h2 q hq hvq).2, hε]
    exact hwV w⁻¹ (Cq.inv_mem hwC) (by rw [mul_inv_cancel]; exact V.one_mem)
  · have hvw : v * w ∈ Cq := by
      refine P.ker_right (v * w) (U.mul_mem hv hw) fun q hq => ?_
      rw [P.pair_mul_left hv hw hq]
      by_cases hvq : ⁅v, q⁆ = 1
      · rw [hvq, h1 q hq hvq, mul_one]
      · obtain ⟨hvqz, hwq⟩ := h2 q hq hvq
        rw [hvqz, hwq, hε]
        exact P.Z_sq P.z_mem
    refine hwV (v * w)⁻¹ (Cq.inv_mem hvw) ?_
    have e : w * (v * w)⁻¹ = v⁻¹ := by group
    rw [e]
    exact V.inv_mem hvV

theorem rpp_conj_z {z : G} {R : Subgroup G} {y : G} (hy : ∀ a ∈ R, y * a * y⁻¹ ∈ R)
    {a b c : G} (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (h : ⁅⁅a, b⁆, ⁅c, b⁆⁆ = z) :
    z ∈ ⁅⁅R, R⁆, ⁅R, R⁆⁆ ∧ y * z * y⁻¹ ∈ ⁅⁅R, R⁆, ⁅R, R⁆⁆ := by
  refine ⟨?_, ?_⟩
  · rw [← h]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator ha hb) (Subgroup.commutator_mem_commutator hc hb)
  · rw [← h, rpp_conj_comm, rpp_conj_comm, rpp_conj_comm]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (hy a ha) (hy b hb))
      (Subgroup.commutator_mem_commutator (hy c hc) (hy b hb))

theorem rpp_false_of_not_mem {Q U Z Cq Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Cq Hs z)
    (T V : Subgroup G) (y : G)
    (hQv : ∀ v ∈ V, v ∉ Z → v ∉ ⁅Q, Q⁆)
    (hTH : T ≤ Hs) (hQT : Q ≤ T) (hTQ : ∀ x ∈ T, ∀ x' ∈ T, ⁅x, x'⁆ ∈ Q)
    (hVU : V ≤ U) (hZV : Z ≤ V)
    (hV : ∃ v ∈ V, v ∉ Z ∧ v ∉ Cq ∧ ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z)
    (hS1 : ∃ r ∈ T ⊓ Subgroup.centralizer (V : Set G), ∃ u₀ ∈ U,
      ∀ c ∈ Cq, ⁅⁅u₀, r⁆, r⁻¹⁆ * c ∉ V)
    (hy : y ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hyV : ∀ x ∈ V, y * x * y⁻¹ ∈ V)
    (hyz : y * z * y⁻¹ ≠ z) : False := by
  obtain ⟨v, hvV, hvZ, hvC, hV4⟩ := hV
  obtain ⟨r, hr, u₀, hu₀, hw⟩ := hS1
  have hrT : r ∈ T := (Subgroup.mem_inf.1 hr).1
  have hrH : r ∈ Hs := hTH hrT
  have hu₀R : u₀ ∈ T ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.mem_inf.2 ⟨hQT (P.U_le_Q hu₀), Subgroup.mem_centralizer_iff.2 fun h hh =>
      P.U_comm h (hVU hh) u₀ hu₀⟩
  have hxU : ⁅u₀, r⁆ ∈ U := rpp_comm_mem_U P hu₀ hrH
  have hwU : ⁅⁅u₀, r⁆, r⁻¹⁆ ∈ U := rpp_comm_mem_U P hxU (Hs.inv_mem hrH)
  obtain ⟨q, hqQ, hvq, hwq⟩ := rpp_exists_pair P (V := V) (hVU hvV) hvV hvC hwU hw
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
  obtain ⟨hzR, hyzR⟩ := rpp_conj_z (R := T ⊓ Subgroup.centralizer (V : Set G)) (y := y)
    (fun a ha => (Subgroup.mem_set_normalizer_iff.1 hy a).1 ha) hu₀R hr hqR hxc
  have hR'Q : ⁅T ⊓ Subgroup.centralizer (V : Set G), T ⊓ Subgroup.centralizer (V : Set G)⁆ ≤ Q :=
    Subgroup.commutator_le.2 fun a ha b hb => hTQ a ha.1 b hb.1
  have hR''Q : ⁅⁅T ⊓ Subgroup.centralizer (V : Set G), T ⊓ Subgroup.centralizer (V : Set G)⁆,
      ⁅T ⊓ Subgroup.centralizer (V : Set G), T ⊓ Subgroup.centralizer (V : Set G)⁆⁆ ≤ ⁅Q, Q⁆ :=
    Subgroup.commutator_mono hR'Q hR'Q
  have hz1 : y * z * y⁻¹ ≠ 1 := fun h1 => P.z_ne (by
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group)
  have hz2 : z * z = 1 := P.Z_sq P.z_mem
  refine hQv v hvV hvZ (hR''Q ?_)
  rcases hV4 _ (hyV z (hZV P.z_mem)) with h | h | h | h
  · exact absurd h hz1
  · exact absurd h hyz
  · rw [← h]
    exact hyzR
  · have e : v = (y * z * y⁻¹) * z := by rw [h, mul_assoc, hz2, mul_one]
    rw [e]
    exact Subgroup.mul_mem _ hyzR hzR

theorem rpp_false {Q U Z Cq Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Cq Hs z)
    (T V : Subgroup G) (y : G)
    (hQ' : ∀ x ∈ Q, ∀ x' ∈ Q, ⁅x, x'⁆ ∈ Cq)
    (hTH : T ≤ Hs) (hQT : Q ≤ T) (hTQ : ∀ x ∈ T, ∀ x' ∈ T, ⁅x, x'⁆ ∈ Q)
    (hVU : V ≤ U) (hZV : Z ≤ V)
    (hV : ∃ v ∈ V, v ∉ Z ∧ v ∉ Cq ∧ ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z)
    (hS1 : ∃ r ∈ T ⊓ Subgroup.centralizer (V : Set G), ∃ u₀ ∈ U,
      ∀ c ∈ Cq, ⁅⁅u₀, r⁆, r⁻¹⁆ * c ∉ V)
    (hy : y ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hyV : ∀ x ∈ V, y * x * y⁻¹ ∈ V)
    (hyz : y * z * y⁻¹ ≠ z) : False := by
  obtain ⟨v₀, hv₀V, hv₀Z, hv₀C, hV4⟩ := hV
  refine rpp_false_of_not_mem P T V y (fun v hv hvZ hvQ => ?_) hTH hQT hTQ hVU hZV
    ⟨v₀, hv₀V, hv₀Z, hv₀C, hV4⟩ hS1 hy hyV hyz
  have hle : ⁅Q, Q⁆ ≤ Cq := Subgroup.commutator_le.2 hQ'
  rcases hV4 v hv with h | h | h | h
  · exact hvZ (by rw [h]; exact Z.one_mem)
  · exact hvZ (by rw [h]; exact P.z_mem)
  · exact hv₀C (h ▸ hle hvQ)
  · refine hv₀C ?_
    have e : v₀ = v * z⁻¹ := by rw [h]; group
    rw [e]
    exact Cq.mul_mem (hle hvQ) (Cq.inv_mem (P.Z_le_Cq P.z_mem))

end CFSG.Quasithin.NoE9Z4GenGrp
