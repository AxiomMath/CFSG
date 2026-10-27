module

public import CFSG.Quasithin.Recognition.HSTypeB3

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

@[expose] noncomputable def hsChi (x y : G) : ZMod 2 := by
  classical
  exact if y ∈ hsQ x then 0 else 1

theorem hsChi_eq_zero_iff {x y : G} : hsChi x y = 0 ↔ y ∈ hsQ x := by
  classical
  unfold hsChi
  split_ifs with h <;> simp [h]

theorem hsChi_eq_one_iff {x y : G} : hsChi x y = 1 ↔ y ∉ hsQ x := by
  classical
  unfold hsChi
  split_ifs with h <;> simp [h]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

theorem hsChi_mul [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x y y' : G} (hx : x ∈ hsB z s)
    (hx1 : x ≠ 1) (hy : y ∈ hsB z s) (hy' : y' ∈ hsB z s) :
    hsChi x (y * y') = hsChi x y + hsChi x y' := by
  set W := (hsQ x ⊓ hsB z s).subgroupOf (hsB z s) with hW
  have hidx : W.index = 2 := by
    have h1 := Subgroup.card_mul_index W
    have hWc : Nat.card ↥W = 8 := by
      rw [hW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : hsQ x ⊓ hsB z s ≤ hsB z s)).toEquiv]
      exact h.card_hsQ_inf_hsB hsmemH hsnotK hss hg₀ hx hx1
    rw [hWc, h.card_hsB hsmemH hsnotK hss] at h1
    omega
  have hmem : ∀ a : ↥(hsB z s), a ∈ W ↔ (a : G) ∈ hsQ x := by
    intro a
    rw [hW, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, a.2⟩⟩
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y, hy⟩) (b := ⟨y', hy'⟩)
  rw [hmem, hmem, hmem] at key
  simp only [Subgroup.coe_mul] at key
  by_cases h1 : y ∈ hsQ x <;> by_cases h2 : y' ∈ hsQ x
  · rw [hsChi_eq_zero_iff.mpr (key.mpr (iff_of_true h1 h2)), hsChi_eq_zero_iff.mpr h1,
      hsChi_eq_zero_iff.mpr h2, add_zero]
  · rw [hsChi_eq_one_iff.mpr (fun h3 => h2 ((key.mp h3).mp h1)), hsChi_eq_zero_iff.mpr h1,
      hsChi_eq_one_iff.mpr h2, zero_add]
  · rw [hsChi_eq_one_iff.mpr (fun h3 => h1 ((key.mp h3).mpr h2)), hsChi_eq_one_iff.mpr h1,
      hsChi_eq_zero_iff.mpr h2, add_zero]
  · rw [hsChi_eq_zero_iff.mpr (key.mpr (iff_of_false h1 h2)), hsChi_eq_one_iff.mpr h1,
      hsChi_eq_one_iff.mpr h2]
    decide

theorem hsChi_one (x : G) : hsChi x 1 = 0 := hsChi_eq_zero_iff.mpr (hsQ x).one_mem

theorem hsChi_self [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : G} (hx : x ∈ hsB z s)
    (hx1 : x ≠ 1) : hsChi x x = 0 := by
  obtain ⟨n, -, rfl⟩ := h.exists_normalizer_conj_hsB hsmemH hsnotK hss hg₀ hx hx1
  exact hsChi_eq_zero_iff.mpr (h.mem_hsQ_self n)

theorem hsChi_symm [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x y : G} (hx : x ∈ hsB z s)
    (hx1 : x ≠ 1) (hy : y ∈ hsB z s) (hy1 : y ≠ 1) : hsChi x y = hsChi y x := by
  have := h.mem_hsQ_symm_of_mem_hsB hsmemH hsnotK hss hg₀ hx hx1 hy hy1
  by_cases h1 : y ∈ hsQ x
  · rw [hsChi_eq_zero_iff.mpr h1, hsChi_eq_zero_iff.mpr (this.mp h1)]
  · rw [hsChi_eq_one_iff.mpr h1, hsChi_eq_one_iff.mpr (fun h2 => h1 (this.mpr h2))]

theorem hsChi_conj (x y n : G) : hsChi (n * x * n⁻¹) (n * y * n⁻¹) = hsChi x y := by
  by_cases h1 : y ∈ hsQ x
  · rw [hsChi_eq_zero_iff.mpr h1, hsChi_eq_zero_iff.mpr
      ((mem_hsQ_conj_of_normalizer x y n).mp h1)]
  · rw [hsChi_eq_one_iff.mpr h1, hsChi_eq_one_iff.mpr
      (fun h2 => h1 ((mem_hsQ_conj_of_normalizer x y n).mpr h2))]

theorem card_inf_hsQ_s [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    4 ≤ Nat.card ↥((hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
      (hsQ s ⊓ Subgroup.centralizer ({z} : Set G))) := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  have hs' := h.setting_s hg₀
  have hzH := z_mem_hsH_s hsmemH
  have hzK := h.z_not_mem_hsK_s hsQ' hg₀
  have hzz : z * z = 1 := h.z_mul_z
  have hB := h.hsB_symm hsmemH hsnotK hss hg₀
  set C := hsQ z ⊓ Subgroup.centralizer ({s} : Set G)
  set C' := hsQ s ⊓ Subgroup.centralizer ({z} : Set G)
  have hC'B : C' ≤ hsB z s := hB ▸ centralizer_le_hsB
  have hCB : C ≤ hsB z s := centralizer_le_hsB
  have hle : C ≤ Subgroup.normalizer (C' : Set G) :=
    le_normalizer_of_conj_mem fun a ha b hb => by
      rw [h.hsB_comm hsmemH hsnotK hss (hCB ha) (hC'B hb), mul_inv_cancel_right]
      exact hb
  have hprod := card_sup_mul_card_inf_of_le_normalizer hle
  rw [h.card_centralizer_invol hsmemH hsnotK hss, hs'.card_centralizer_invol hzH hzK hzz] at hprod
  have hsup : Nat.card ↥(C ⊔ C') ≤ 16 := by
    rw [← h.card_hsB hsmemH hsnotK hss]
    exact Subgroup.card_le_of_le (sup_le hCB hC'B)
  nlinarith

theorem le_normalizer_of_le_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {X Y : Subgroup G} (hX : X ≤ hsB z s)
    (hY : Y ≤ hsB z s) : X ≤ Subgroup.normalizer (Y : Set G) :=
  le_normalizer_of_conj_mem fun a ha b hb => by
    rw [h.hsB_comm hsmemH hsnotK hss (hX ha) (hY hb), mul_inv_cancel_right]
    exact hb

theorem card_sup_zpowers [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {X : Subgroup G} (hX : X ≤ hsB z s) {x : G}
    (hx : x ∈ hsB z s) (hxX : x ∉ X) (hxx : x * x = 1) :
    Nat.card ↥(X ⊔ Subgroup.zpowers x) = 2 * Nat.card X := by
  have hx1 : x ≠ 1 := fun h1 => hxX (h1 ▸ X.one_mem)
  have hxB : Subgroup.zpowers x ≤ hsB z s := (Subgroup.zpowers_le).mpr hx
  have hprod := card_sup_mul_card_inf_of_le_normalizer
    (h.le_normalizer_of_le_hsB hsmemH hsnotK hss hX hxB)
  have hinf : X ⊓ Subgroup.zpowers x = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y ⟨hyX, hyx⟩ => ?_
    have ho : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
    rcases eq_one_or_eq_of_mem_zpowers ho hyx with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hyX) hxX
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers,
    orderOf_eq_prime (by rw [sq]; exact hxx) hx1] at hprod
  omega

theorem exists_sympBasis [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    ∃ c c' : G, c ∈ (hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
        (hsQ s ⊓ Subgroup.centralizer ({z} : Set G)) ∧
      c' ∈ (hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
        (hsQ s ⊓ Subgroup.centralizer ({z} : Set G)) ∧ c ≠ 1 ∧ c' ∉ hsQ c := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  have hs' := h.setting_s hg₀
  have hzQs := h.z_not_mem_hsQ_s hsQ' hg₀
  have hB := h.hsB_symm hsmemH hsnotK hss hg₀
  set C := hsQ z ⊓ Subgroup.centralizer ({s} : Set G)
  set C' := hsQ s ⊓ Subgroup.centralizer ({z} : Set G)
  have hC'B : C' ≤ hsB z s := hB ▸ centralizer_le_hsB
  have hCB : C ≤ hsB z s := centralizer_le_hsB
  have h4 : 4 ≤ Nat.card ↥(C ⊓ C') := h.card_inf_hsQ_s hsmemH hsnotK hss hg₀
  obtain ⟨c, hc, hc1⟩ : ∃ c ∈ C ⊓ C', c ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot (C ⊓ C')).mp (by omega))
    exact ⟨a, a.2, fun h1 => ha (Subtype.ext h1)⟩
  refine ⟨c, ?_⟩
  by_contra hne
  push Not at hne
  have hle : C ⊓ C' ≤ hsQ c := fun c' hc' => hne c' hc hc' hc1
  have hcB : c ∈ hsB z s := hCB hc.1
  have hzB := h.z_mem_hsB hsmemH
  have hzc : z ∈ hsQ c := (h.mem_hsQ_symm_of_mem_hsB hsmemH hsnotK hss hg₀ hcB hc1 hzB
    h.z_ne_one).mpr hc.1.1
  have hsc : s ∈ hsQ c := (h.mem_hsQ_symm_of_mem_hsB hsmemH hsnotK hss hg₀ hcB hc1
    s_mem_hsB (fun h1 => hsQ' (h1 ▸ (hsQ z).one_mem))).mpr hc.2.1
  have hX : C ⊓ C' ≤ hsB z s := inf_le_left.trans hCB
  have hzX : z ∉ C ⊓ C' := fun h1 => hzQs h1.2.1
  have hY : (C ⊓ C') ⊔ Subgroup.zpowers z ≤ hsB z s :=
    sup_le hX ((Subgroup.zpowers_le).mpr hzB)
  have hsY : s ∉ (C ⊓ C') ⊔ Subgroup.zpowers z := by
    intro h1
    apply hsQ'
    have hle' : (C ⊓ C') ⊔ Subgroup.zpowers z ≤ hsQ z :=
      sup_le (inf_le_left.trans inf_le_left) ((Subgroup.zpowers_le).mpr h.mem_Q)
    exact hle' h1
  have hcard1 := h.card_sup_zpowers hsmemH hsnotK hss hX hzB hzX h.z_mul_z
  have hcard2 := h.card_sup_zpowers hsmemH hsnotK hss hY s_mem_hsB hsY hss
  have hYle : (C ⊓ C') ⊔ Subgroup.zpowers z ⊔ Subgroup.zpowers s ≤ hsQ c ⊓ hsB z s := by
    refine le_inf (sup_le (sup_le hle ((Subgroup.zpowers_le).mpr hzc))
      ((Subgroup.zpowers_le).mpr hsc)) (sup_le hY ((Subgroup.zpowers_le).mpr s_mem_hsB))
  have := Subgroup.card_le_of_le hYle
  rw [h.card_hsQ_inf_hsB hsmemH hsnotK hss hg₀ hcB hc1, hcard2, hcard1] at this
  omega

end HSSetting

end CFSG.Quasithin.HSType
