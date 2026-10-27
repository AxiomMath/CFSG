module

public import CFSG.Quasithin.Recognition.HSType18d
public import CFSG.Quasithin.Recognition.HSTypeStar

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G}

abbrev hAction (z : G) : MulAction ↥(hsH z) G :=
  MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp (hsH z).subtype)

theorem ncard_orbit_H_invol [Finite G] (h : HSSetting z V) {s : G} (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    (@MulAction.orbit ↥(hsH z) G (hAction z).toSMul s).ncard = 80 := by
  let := hAction z
  obtain ⟨w, hwZ, hw1, hwz', -⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  have hC := (h.card_centralizer_H_invol_not_K hsmemH hsnotK hss hwZ hwz hg₀).1
  have hstab : MulAction.stabilizer ↥(hsH z) s =
      (Subgroup.centralizer ({s} : Set G)).subgroupOf (hsH z) := by
    ext q
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    change (q : G) * s * (q : G)⁻¹ = s ↔ _
    constructor
    · intro hq
      calc (q : G) * s = (q : G) * s * (q : G)⁻¹ * (q : G) := by group
        _ = s * (q : G) := by rw [hq]
    · intro hq
      rw [hq, mul_inv_cancel_right]
  have hcardstab : Nat.card (MulAction.stabilizer ↥(hsH z) s) = 96 := by
    rw [hstab, ← hC, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(hsH z) s)
  rw [MulAction.index_stabilizer, hcardstab, h.card_H] at hmul
  omega

theorem ncard_invol_Q_le [Finite G] (h : HSSetting z V) :
    {u : G | u ∈ hsQ z ∧ u * u = 1 ∧ u ≠ 1}.ncard ≤ 31 := by
  classical
  have := Fintype.ofFinite ↥(hsQ z)
  have h30 := card_noncentral_invol_of_isZ4Q8Q8 h.one.fstar
  set F := Finset.univ.filter fun x : ↥(hsQ z) => x * x = 1 ∧ x ∉ Subgroup.center ↥(hsQ z)
  have hsub : {u : G | u ∈ hsQ z ∧ u * u = 1 ∧ u ≠ 1} ⊆
      (Subtype.val '' (F : Set ↥(hsQ z))) ∪ {z} := by
    rintro u ⟨huQ, hu2, hu1⟩
    by_cases huZ : u ∈ hsZQ z
    · right
      exact h.eq_z_of_mem_ZQ huZ hu2 hu1
    · left
      refine ⟨⟨u, huQ⟩, ?_, rfl⟩
      simp only [F, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨Subtype.ext hu2, fun hc => huZ ?_⟩
      have : (⟨u, huQ⟩ : ↥(hsQ z)) ∈ (hsZQ z).subgroupOf (hsQ z) := by
        rw [ZQ_subgroupOf_eq_center]
        exact hc
      exact this
  calc {u : G | u ∈ hsQ z ∧ u * u = 1 ∧ u ≠ 1}.ncard
      ≤ ((Subtype.val '' (F : Set ↥(hsQ z))) ∪ {z}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Subtype.val '' (F : Set ↥(hsQ z))).ncard + ({z} : Set G).ncard :=
        Set.ncard_union_le _ _
    _ = 31 := by
        rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset, h30,
          Set.ncard_singleton]

theorem card_conj_comm_z_le [Finite G] (h : HSSetting z V) {s : G} (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    Nat.card {u : G // IsConj z u ∧ u * z = z * u} ≤ 111 := by
  let := hAction z
  obtain ⟨w, hwZ, hw1, hwz', -⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  obtain ⟨hnc, -⟩ := h.not_conj_mul_of_conj_z hsmemH hsnotK hss hwZ hwz hg₀
  have hsub : {u : G | IsConj z u ∧ u * z = z * u} ⊆
      {u : G | u ∈ hsQ z ∧ u * u = 1 ∧ u ≠ 1} ∪ MulAction.orbit ↥(hsH z) s := by
    rintro u ⟨hu, huz⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hu
    have hzz : z * z = 1 := h.z_mul_z
    have hu2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
    have hu1 : g * z * g⁻¹ ≠ 1 := fun h1 => h.z_ne_one (by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
    have huH : g * z * g⁻¹ ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr huz
    by_cases huK : g * z * g⁻¹ ∈ hsK z
    · left
      exact ⟨h.mem_Q_of_conj_mem_K huK, hu2, hu1⟩
    · right
      obtain ⟨k, hkK, hk⟩ := h.exists_K_conj_of_invol_not_K hsmemH hsnotK hss hwZ hwz huH huK
        hu2
      rcases hk with hk | hk
      · refine ⟨⟨k⁻¹, (hsH z).inv_mem hkK.1⟩, ?_⟩
        change k⁻¹ * s * k⁻¹⁻¹ = _
        rw [← hk]
        group
      · exfalso
        apply hnc (k * g)
        rw [← hk]
        group
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hle2 := Set.ncard_union_le {u : G | u ∈ hsQ z ∧ u * u = 1 ∧ u ≠ 1}
    (MulAction.orbit ↥(hsH z) s)
  rw [h.ncard_orbit_H_invol hsmemH hsnotK hss hg₀] at hle2
  have h31 := h.ncard_invol_Q_le
  rw [← Nat.card_coe_set_eq] at hle
  change Nat.card {u : G // IsConj z u ∧ u * z = z * u} ≤ _ at hle
  omega

end HSSetting

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

theorem card_quot_eq_100_of_le
    (hF : FactM22SubgroupIndex)
    (hn : ∀ t ∈ hsK C.z, t ∉ hsQ C.z → t * t = 1 →
      Nat.card {u : G // IsConj C.z u ∧ u * t = t * u} ≤ 82) :
    Nat.card (G ⧸ C.J) = 100 := by
  obtain ⟨t, htK, htQ, htt, -, htz, hcl⟩ := C.h.two_classes
  have ht1 : t ≠ 1 := fun h1 => htQ (h1 ▸ (hsQ C.z).one_mem)
  have hzt : ¬ IsConj C.z t := fun hc => by
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    exact htz c hc
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  refine C.card_quot_eq_100 hF ht2 hzt (fun x hx => ?_) (C.h.star) (hn t htK htQ htt)
    (C.h.card_conj_comm_z_le C.hsmemH C.hsnotK C.hss C.hg₀)
  have hx2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx; exact absurd hx (by norm_num)
  rcases hcl x hx2 hx1 with ⟨g, hg⟩ | ⟨g, hg⟩
  · left
    exact isConj_comm.mp (isConj_iff.mpr ⟨g, hg⟩)
  · right
    exact isConj_comm.mp (isConj_iff.mpr ⟨g, hg⟩)

end HSCtx

end CFSG.Quasithin.HSType
