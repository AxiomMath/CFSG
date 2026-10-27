module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin

open Subgroup

variable {I : Type*} [Group I]

structure KleinCore (K V : Subgroup I) (z y : I) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_mem : z ∈ V
  V_le : V ≤ K
  V_card : Nat.card V = 4
  V_sq : ∀ v ∈ V, v * v = 1
  cent : ∀ k ∈ K, k * z = z * k → k ∈ V
  y_mem : y ∈ K
  y_cube : y * y * y = 1
  y_norm : ∀ v ∈ V, y * v * y⁻¹ ∈ V
  y_ne : y * z * y⁻¹ ≠ z
  syl : ∀ W : Subgroup I, W ≤ K → IsPGroup 2 W → Nat.card W ≤ 4

namespace KleinCore

variable {K V : Subgroup I} {z y : I}

theorem V_comm (h : KleinCore K V z y) {v w : I} (hv : v ∈ V) (hw : w ∈ V) : v * w = w * v := by
  have h1 := h.V_sq (v * w) (V.mul_mem hv hw)
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.V_sq v hv)
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (h.V_sq w hw)
  calc v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = w * v := by rw [mul_inv_rev, hv', hw']

theorem V_sharp [Finite I] (h : KleinCore K V z y) {v : I} (hv : v ∈ V) (hv1 : v ≠ 1) :
    v = z ∨ v = y * z * y⁻¹ ∨ v = y * (y * z * y⁻¹) * y⁻¹ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  set z1 := y * z * y⁻¹ with hz1
  set z2 := y * z1 * y⁻¹ with hz2
  have hz1V : z1 ∈ V := h.y_norm z h.z_mem
  have hz2V : z2 ∈ V := h.y_norm z1 hz1V
  have hcinj : ∀ a b : I, y * a * y⁻¹ = y * b * y⁻¹ → a = b := by
    intro a b e
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = y⁻¹ * (y * b * y⁻¹) * y := by rw [e]
      _ = b := by group
  have hc3 : ∀ w : I, y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = w := by
    intro w
    calc y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * w * (y * y * y)⁻¹ := by group
      _ = w := by rw [h.y_cube]; group
  have hz1_ne1 : z1 ≠ 1 := by
    intro e
    apply h.z_ne
    apply hcinj z 1
    rw [show y * 1 * y⁻¹ = 1 by group]; exact e
  have hz2_ne1 : z2 ≠ 1 := by
    intro e
    apply hz1_ne1
    apply hcinj z1 1
    rw [show y * 1 * y⁻¹ = 1 by group]; exact e
  have hz12 : z1 ≠ z2 := fun e => h.y_ne (hcinj z z1 e).symm
  have hz2z : z2 ≠ z := by
    intro e
    apply h.y_ne
    have : y * z2 * y⁻¹ = z := by rw [← hc3 z]
    calc y * z * y⁻¹ = y * z2 * y⁻¹ := by rw [e]
      _ = z := this
  have f01 : (1 : I) ≠ z := h.z_ne.symm
  have f02 : (1 : I) ≠ z1 := hz1_ne1.symm
  have f03 : (1 : I) ≠ z2 := hz2_ne1.symm
  have f04 : (1 : I) ≠ v := hv1.symm
  have f12 : z ≠ z1 := fun e => h.y_ne e.symm
  have f13 : z ≠ z2 := hz2z.symm
  have f14 : z ≠ v := h1.symm
  have f23 : z1 ≠ z2 := hz12
  have f24 : z1 ≠ v := h2.symm
  have f34 : z2 ≠ v := h3.symm
  have hF : ({1, z, z1, z2, v} : Finset I).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals (simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; tauto)
  have hsub : (({1, z, z1, z2, v} : Finset I) : Set I) ⊆ (V : Set I) := by
    intro w hw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    exacts [V.one_mem, h.z_mem, hz1V, hz2V, hv]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hF] at hle
  have e : Nat.card V = (V : Set I).ncard := Nat.card_coe_set_eq _
  have := h.V_card
  omega

theorem cent_sharp [Finite I] (h : KleinCore K V z y) {v : I} (hv : v ∈ V) (hv1 : v ≠ 1) {k : I}
    (hk : k ∈ K) (hkv : k * v = v * k) : k ∈ V := by
  rcases h.V_sharp hv hv1 with rfl | rfl | rfl
  · exact h.cent k hk hkv
  · have hk' : y⁻¹ * k * y ∈ K := K.mul_mem (K.mul_mem (K.inv_mem h.y_mem) hk) h.y_mem
    have hcomm : (y⁻¹ * k * y) * z = z * (y⁻¹ * k * y) := by
      calc (y⁻¹ * k * y) * z = y⁻¹ * (k * (y * z * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * z * y⁻¹) * k) * y := by rw [hkv]
        _ = z * (y⁻¹ * k * y) := by group
    have hV := h.cent _ hk' hcomm
    have := h.y_norm _ hV
    rwa [show y * (y⁻¹ * k * y) * y⁻¹ = k by group] at this
  · have hk1 : y⁻¹ * k * y ∈ K := K.mul_mem (K.mul_mem (K.inv_mem h.y_mem) hk) h.y_mem
    have hk2 : y⁻¹ * (y⁻¹ * k * y) * y ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem h.y_mem) hk1) h.y_mem
    have hcomm : (y⁻¹ * (y⁻¹ * k * y) * y) * z = z * (y⁻¹ * (y⁻¹ * k * y) * y) := by
      calc (y⁻¹ * (y⁻¹ * k * y) * y) * z
          = y⁻¹ * (y⁻¹ * (k * (y * (y * z * y⁻¹) * y⁻¹)) * y) * y := by group
        _ = y⁻¹ * (y⁻¹ * ((y * (y * z * y⁻¹) * y⁻¹) * k) * y) * y := by rw [hkv]
        _ = z * (y⁻¹ * (y⁻¹ * k * y) * y) := by
          have hy3 : y * y * y = 1 := h.y_cube
          calc y⁻¹ * (y⁻¹ * ((y * (y * z * y⁻¹) * y⁻¹) * k) * y) * y
              = (y * y * y)⁻¹ * ((y * y * y) * z * (y * y * y)⁻¹) * ((y * y * y) *
                (y⁻¹ * (y⁻¹ * k * y) * y)) := by group
            _ = z * (y⁻¹ * (y⁻¹ * k * y) * y) := by rw [hy3]; group
    have hV := h.cent _ hk2 hcomm
    have := h.y_norm _ (h.y_norm _ hV)
    rwa [show y * (y * (y⁻¹ * (y⁻¹ * k * y) * y) * y⁻¹) * y⁻¹ = k by group] at this

theorem exists_conj_mem [Finite I] (h : KleinCore K V z y) {x : I} (hxK : x ∈ K)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : ∃ k ∈ K, k⁻¹ * x * k ∈ V := by
  classical
  set V' : Subgroup K := V.subgroupOf K with hV'
  have hV'card : Nat.card V' = 4 := by
    rw [← h.V_card]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.V_le).toEquiv
  have hV'p : IsPGroup 2 V' := IsPGroup.of_card (n := 2) (by rw [hV'card]; norm_num)
  obtain ⟨S0, hS0⟩ := hV'p.exists_le_sylow
  have hmapcard : ∀ W : Subgroup K, Nat.card (W.map K.subtype) = Nat.card W := fun W =>
    (Nat.card_congr (Subgroup.equivMapOfInjective W K.subtype K.subtype_injective)).symm
  have hS0card : Nat.card (S0 : Subgroup K) ≤ 4 := by
    have hp : IsPGroup 2 ((S0 : Subgroup K).map K.subtype) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 S0.isPGroup'
      refine (IsPGroup.iff_card).2 ⟨n, ?_⟩
      rw [hmapcard, hn]
    have := h.syl _ (Subgroup.map_subtype_le _) hp
    rwa [hmapcard] at this
  have hS0eq : V' = (S0 : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hS0 (by rw [hV'card]; exact hS0card)
  set xK : K := ⟨x, hxK⟩ with hxK'
  have hxK2 : xK ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hx2)
  have hxKne : xK ≠ 1 := fun e => hx1 (congrArg Subtype.val e)
  have hxp : IsPGroup 2 (Subgroup.zpowers xK) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hxK2 hxKne]; simp
  obtain ⟨S1, hS1⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S0 S1
  have hxmem : xK ∈ ((g • S0 : Sylow 2 K) : Subgroup K) := by
    rw [hg]; exact hS1 (Subgroup.mem_zpowers xK)
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, ← hS0eq] at hxmem
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.1 hxmem
  refine ⟨(g : I), g.2, ?_⟩
  have hwx' : (g : I) * (w : I) * (g : I)⁻¹ = x := by
    have := congrArg Subtype.val hwx
    simpa [MulAut.conj_apply] using this
  have : (g : I)⁻¹ * x * g = (w : I) := by
    rw [← hwx']; group
  rw [this]
  exact Subgroup.mem_subgroupOf.1 hw

theorem cent_conj [Finite I] (h : KleinCore K V z y) {x : I} (hxK : x ∈ K) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : ∃ k ∈ K, ∀ w ∈ K, (w * x = x * w ↔ k⁻¹ * w * k ∈ V) := by
  obtain ⟨k, hkK, hkx⟩ := h.exists_conj_mem hxK hx2 hx1
  refine ⟨k, hkK, fun w hw => ⟨fun hwx => ?_, fun hwV => ?_⟩⟩
  · have hv1 : k⁻¹ * x * k ≠ 1 := by
      intro e
      apply hx1
      calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
        _ = 1 := by rw [e]; group
    have hkw : k⁻¹ * w * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hkK) hw) hkK
    refine h.cent_sharp hkx hv1 hkw ?_
    calc (k⁻¹ * w * k) * (k⁻¹ * x * k) = k⁻¹ * (w * x) * k := by group
      _ = k⁻¹ * (x * w) * k := by rw [hwx]
      _ = (k⁻¹ * x * k) * (k⁻¹ * w * k) := by group
  · have hc := h.V_comm hwV hkx
    calc w * x = k * ((k⁻¹ * w * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * x * k) * (k⁻¹ * w * k)) * k⁻¹ := by rw [hc]
      _ = x * w := by group

theorem exists_conj_z [Finite I] (h : KleinCore K V z y) {x : I} (hxK : x ∈ K) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : ∃ k ∈ K, k * z * k⁻¹ = x := by
  obtain ⟨k0, hk0K, hk0⟩ := h.exists_conj_mem hxK hx2 hx1
  have hv1 : k0⁻¹ * x * k0 ≠ 1 := by
    intro e
    apply hx1
    calc x = k0 * (k0⁻¹ * x * k0) * k0⁻¹ := by group
      _ = 1 := by rw [e]; group
  rcases h.V_sharp hk0 hv1 with e | e | e
  · refine ⟨k0, hk0K, ?_⟩
    calc k0 * z * k0⁻¹ = k0 * (k0⁻¹ * x * k0) * k0⁻¹ := by rw [e]
      _ = x := by group
  · refine ⟨k0 * y, K.mul_mem hk0K h.y_mem, ?_⟩
    calc k0 * y * z * (k0 * y)⁻¹ = k0 * (y * z * y⁻¹) * k0⁻¹ := by group
      _ = k0 * (k0⁻¹ * x * k0) * k0⁻¹ := by rw [e]
      _ = x := by group
  · refine ⟨k0 * y * y, K.mul_mem (K.mul_mem hk0K h.y_mem) h.y_mem, ?_⟩
    calc k0 * y * y * z * (k0 * y * y)⁻¹ = k0 * (y * (y * z * y⁻¹) * y⁻¹) * k0⁻¹ := by group
      _ = k0 * (k0⁻¹ * x * k0) * k0⁻¹ := by rw [e]
      _ = x := by group

theorem odd_order [Finite I] (h : KleinCore K V z y) {x y' : I} (hx : x ∈ K) (hx2 : x * x = 1)
    (hy : y' ∈ K) (hy2 : y' * y' = 1) (hne : x * y' ≠ y' * x) :
    Odd (orderOf (x * y')) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨r, hr⟩ := hodd
  have hpos : 0 < orderOf (x * y') := orderOf_pos _
  have hr0 : r ≠ 0 := by omega
  set w := x * y' with hw
  set c := w ^ r with hc
  have hcK : c ∈ K := K.pow_mem (K.mul_mem hx hy) r
  have hc2 : c * c = 1 := by
    rw [hc, ← pow_add, ← hr]; exact pow_orderOf_eq_one w
  have hc1 : c ≠ 1 := pow_ne_one_of_lt_orderOf hr0 (by omega)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hy2
  have hwi : w⁻¹ = y' * x := by rw [hw, mul_inv_rev, hxi, hyi]
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hxc : x * c = c * x := by
    have h1 : x * w * x⁻¹ = w⁻¹ := by
      rw [hxi, hwi, hw]; calc x * (x * y') * x = (x * x) * y' * x := by group
        _ = y' * x := by rw [hx2, one_mul]
    have h2 : x * c * x⁻¹ = c⁻¹ := by
      rw [hc, ← conj_pow, h1, inv_pow]
    rw [hci, hxi] at h2
    calc x * c = (x * c * x) * x := by rw [mul_assoc (x * c) x x, hx2, mul_one]
      _ = c * x := by rw [h2]
  have hyc : y' * c = c * y' := by
    have h1 : y' * w * y'⁻¹ = w⁻¹ := by
      rw [hyi, hwi, hw]; calc y' * (x * y') * y' = y' * x * (y' * y') := by group
        _ = y' * x := by rw [hy2, mul_one]
    have h2 : y' * c * y'⁻¹ = c⁻¹ := by
      rw [hc, ← conj_pow, h1, inv_pow]
    rw [hci, hyi] at h2
    calc y' * c = (y' * c * y') * y' := by rw [mul_assoc (y' * c) y' y', hy2, mul_one]
      _ = c * y' := by rw [h2]
  obtain ⟨k, hkK, hk⟩ := h.cent_conj hcK hc2 hc1
  have hxV := (hk x hx).1 hxc.symm.symm
  have hyV := (hk y' hy).1 hyc
  apply hne
  have := h.V_comm hxV hyV
  calc x * y' = k * ((k⁻¹ * x * k) * (k⁻¹ * y' * k)) * k⁻¹ := by group
    _ = k * ((k⁻¹ * y' * k) * (k⁻¹ * x * k)) * k⁻¹ := by rw [this]
    _ = y' * x := by group

theorem V_three_ne [Finite I] (h : KleinCore K V z y) :
    z ≠ y * z * y⁻¹ ∧ z ≠ y * (y * z * y⁻¹) * y⁻¹ ∧
      y * z * y⁻¹ ≠ y * (y * z * y⁻¹) * y⁻¹ := by
  have hcinj : ∀ a b : I, y * a * y⁻¹ = y * b * y⁻¹ → a = b := by
    intro a b e
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = y⁻¹ * (y * b * y⁻¹) * y := by rw [e]
      _ = b := by group
  have hc3 : ∀ w : I, y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = w := by
    intro w
    calc y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * w * (y * y * y)⁻¹ := by group
      _ = w := by rw [h.y_cube]; group
  refine ⟨fun e => h.y_ne e.symm, ?_, fun e => h.y_ne (hcinj z _ e).symm⟩
  intro e
  apply h.y_ne
  have : y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ = y * z * y⁻¹ := by rw [← e]
  rw [hc3] at this
  exact this.symm

theorem card_commuting [Finite I] [DecidableEq I] (h : KleinCore K V z y) (Zf : Finset I)
    (hZf : ∀ x, x ∈ Zf ↔ x ∈ K ∧ x * x = 1 ∧ x ≠ 1) {x : I} (hx : x ∈ Zf) :
    (Zf.filter (fun y' => y' * x = x * y')).card = 3 := by
  obtain ⟨hxK, hx2, hx1⟩ := (hZf x).1 hx
  obtain ⟨k, hkK, hk⟩ := h.cent_conj hxK hx2 hx1
  obtain ⟨n12, n13, n23⟩ := h.V_three_ne
  set z1 := y * z * y⁻¹ with hz1
  set z2 := y * z1 * y⁻¹ with hz2
  have hz1V : z1 ∈ V := h.y_norm z h.z_mem
  have hz2V : z2 ∈ V := h.y_norm z1 hz1V
  have hkinj : ∀ a b : I, k * a * k⁻¹ = k * b * k⁻¹ → a = b := by
    intro a b e
    calc a = k⁻¹ * (k * a * k⁻¹) * k := by group
      _ = k⁻¹ * (k * b * k⁻¹) * k := by rw [e]
      _ = b := by group
  have hne1 : ∀ v : I, v ≠ 1 → k * v * k⁻¹ ≠ 1 := by
    intro v hv e
    apply hv
    apply hkinj v 1
    rw [show k * 1 * k⁻¹ = 1 by group]; exact e
  have hz1ne : z1 ≠ 1 := by
    intro e; apply h.z_ne
    have : y * z * y⁻¹ = y * 1 * y⁻¹ := by rw [← hz1, e]; group
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = y⁻¹ * (y * 1 * y⁻¹) * y := by rw [this]
      _ = 1 := by group
  have hz2ne : z2 ≠ 1 := by
    intro e; apply hz1ne
    have : y * z1 * y⁻¹ = y * 1 * y⁻¹ := by rw [← hz2, e]; group
    calc z1 = y⁻¹ * (y * z1 * y⁻¹) * y := by group
      _ = y⁻¹ * (y * 1 * y⁻¹) * y := by rw [this]
      _ = 1 := by group
  have hmem : ∀ v ∈ V, v ≠ 1 →
      k * v * k⁻¹ ∈ Zf ∧ (k * v * k⁻¹) * x = x * (k * v * k⁻¹) := by
    intro v hv hv1
    have hvK : v ∈ K := h.V_le hv
    have hK' : k * v * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hkK hvK) (K.inv_mem hkK)
    refine ⟨(hZf _).2 ⟨hK', ?_, hne1 v hv1⟩, ?_⟩
    · calc k * v * k⁻¹ * (k * v * k⁻¹) = k * (v * v) * k⁻¹ := by group
        _ = 1 := by rw [h.V_sq v hv]; group
    · exact (hk _ hK').2 (by rw [show k⁻¹ * (k * v * k⁻¹) * k = v by group]; exact hv)
  have hset : Zf.filter (fun y' => y' * x = x * y') = {k * z * k⁻¹, k * z1 * k⁻¹, k * z2 * k⁻¹} := by
    ext y'
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hyZ, hyc⟩
      obtain ⟨hyK, hy2, hy1⟩ := (hZf y').1 hyZ
      have hV := (hk y' hyK).1 hyc
      have hv1 : k⁻¹ * y' * k ≠ 1 := by
        intro e; apply hy1
        calc y' = k * (k⁻¹ * y' * k) * k⁻¹ := by group
          _ = 1 := by rw [e]; group
      have hy' : y' = k * (k⁻¹ * y' * k) * k⁻¹ := by group
      rcases h.V_sharp hV hv1 with e | e | e
      · left; rw [hy', e]
      · right; left; rw [hy', e]
      · right; right; rw [hy', e]
    · rintro (rfl | rfl | rfl)
      · exact hmem z h.z_mem h.z_ne
      · exact hmem z1 hz1V hz1ne
      · exact hmem z2 hz2V hz2ne
  rw [hset, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    exact fun e => n23 (hkinj _ _ e)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => n12 (hkinj _ _ e), fun e => n13 (hkinj _ _ e)⟩

end KleinCore

end CFSG.Quasithin
