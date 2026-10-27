module

public import CFSG.Quasithin.Recognition.HSTypeB2

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

theorem normalizer_H_hsB_eq [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) :
    hsH z ⊓ Subgroup.normalizer (hsB z s : Set G) =
      (hsH z ⊓ Subgroup.centralizer ({s} : Set G)) ⊔ hsQ z := by
  refine le_antisymm ?_ (sup_le (le_inf inf_le_left (centralizer_le_normalizer_hsB hss))
    (le_inf h.Q_le_H (h.Q_le_normalizer_hsB hsmemH hsnotK hss)))
  rintro x ⟨hxH, hxN⟩
  obtain ⟨r, hr, hrx⟩ := h.exists_conj_of_mem_normalizer_hsB hsmemH hsnotK hss hxH hxN
  have hc : r⁻¹ * x ∈ hsH z ⊓ Subgroup.centralizer ({s} : Set G) := by
    refine ⟨(hsH z).mul_mem ((hsH z).inv_mem (h.Q_le_H hr)) hxH,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc r⁻¹ * x * s = r⁻¹ * (x * s * x⁻¹) * x := by group
      _ = r⁻¹ * (r * s * r⁻¹) * x := by rw [hrx]
      _ = s * (r⁻¹ * x) := by group
  have e : x = r * (r⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hr) (Subgroup.mem_sup_left hc)

theorem card_normalizer_H_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    Nat.card ↥(hsH z ⊓ Subgroup.normalizer (hsB z s : Set G)) = 768 := by
  obtain ⟨w, hwZ, hw1, hwz', -⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  have hle : hsH z ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (hsQ z : Set G) :=
    inf_le_left.trans (le_normalizer_quasithinGenFitting (hsH z))
  have hprod := card_sup_mul_card_inf_of_le_normalizer hle
  have hinf : hsH z ⊓ Subgroup.centralizer ({s} : Set G) ⊓ hsQ z =
      hsQ z ⊓ Subgroup.centralizer ({s} : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨h.Q_le_H hx.1, hx.2⟩, hx.1⟩⟩
  rw [hinf, h.card_centralizer_invol hsmemH hsnotK hss,
    (h.card_centralizer_H_invol_not_K hsmemH hsnotK hss hwZ hwz hg₀).1, h.card_Q] at hprod
  rw [h.normalizer_H_hsB_eq hsmemH hsnotK hss]
  omega

theorem card_normalizer_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    Nat.card ↥(Subgroup.normalizer (hsB z s : Set G)) = 11520 := by
  classical
  set N := Subgroup.normalizer (hsB z s : Set G) with hN
  let : MulAction ↥N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (n : ↥N) (g : G), n • g = (n : G) * g * (n : G)⁻¹ := fun _ _ => rfl
  have horbit : MulAction.orbit ↥N z = {x : G | x ∈ hsB z s ∧ x ≠ 1} := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      show n • z ∈ _
      rw [hsmul]
      refine ⟨(Subgroup.mem_normalizer_iff.mp n.2 z).mp (h.z_mem_hsB hsmemH), fun h1 => ?_⟩
      apply h.z_ne_one
      calc z = (n : G)⁻¹ * ((n : G) * z * (n : G)⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    · rintro ⟨hx, hx1⟩
      obtain ⟨n, hn, hnx⟩ := h.exists_normalizer_conj_hsB hsmemH hsnotK hss hg₀ hx hx1
      exact ⟨⟨n, hn⟩, by show (⟨n, hn⟩ : ↥N) • z = x; rw [hsmul]; exact hnx⟩
  have hstab : MulAction.stabilizer ↥N z = (hsH z).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      calc (n : G) * z = (n : G) * z * (n : G)⁻¹ * n := by group
        _ = z * n := by rw [h1]
    · intro h1
      rw [h1, mul_inv_cancel_right]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥N z)
  rw [MulAction.index_stabilizer, horbit, hstab] at h1
  have hB : ({x : G | x ∈ hsB z s ∧ x ≠ 1} : Set G).ncard = 15 := by
    have e : ({x : G | x ∈ hsB z s ∧ x ≠ 1} : Set G) = (hsB z s : Set G) \ {1} := by
      ext x
      simp
    rw [e, Set.ncard_sdiff_singleton_of_mem (by simp), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, h.card_hsB hsmemH hsnotK hss]
  have hS : Nat.card ↥((hsH z).subgroupOf N) = 768 := by
    rw [← h.card_normalizer_H_hsB hsmemH hsnotK hss hg₀]
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.2, x.1.2⟩, fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [hB, hS] at h1
  omega

theorem card_hsQ_inf_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : G}
    (hx : x ∈ hsB z s) (hx1 : x ≠ 1) : Nat.card ↥(hsQ x ⊓ hsB z s) = 8 := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  obtain ⟨n, hn, rfl⟩ := h.exists_normalizer_conj_hsB hsmemH hsnotK hss hg₀ hx hx1
  have hBn : (hsB z s).map (MulAut.conj n).toMonoidHom = hsB z s := by
    ext y
    rw [mem_map_conj_iff]
    constructor
    · intro hy
      have := (Subgroup.mem_normalizer_iff.mp hn _).mp hy
      simpa [mul_assoc] using this
    · intro hy
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) y).mp hy
      simpa using this
  rw [hsQ_conj, ← hBn, ← Subgroup.map_inf_eq _ _ (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective,
    Subgroup.card_map_of_injective (MulAut.conj n).injective, inf_comm, hsB_inf_Q hss hsQ',
    h.card_centralizer_invol hsmemH hsnotK hss]

theorem mem_hsQ_symm_of_mem_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x y : G}
    (hx : x ∈ hsB z s) (hx1 : x ≠ 1) (hy : y ∈ hsB z s) (hy1 : y ≠ 1) :
    y ∈ hsQ x ↔ x ∈ hsQ y := by
  obtain ⟨a, -, rfl⟩ := h.exists_normalizer_conj_hsB hsmemH hsnotK hss hg₀ hx hx1
  obtain ⟨b, -, rfl⟩ := h.exists_normalizer_conj_hsB hsmemH hsnotK hss hg₀ hy hy1
  exact h.mem_hsQ_conj_iff a b

theorem mem_hsQ_conj_of_normalizer (x y n : G) :
    y ∈ hsQ x ↔ n * y * n⁻¹ ∈ hsQ (n * x * n⁻¹) := by
  rw [hsQ_conj, mem_map_conj_iff]
  have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
  rw [e]

theorem mem_hsQ_self [Finite G] (h : HSSetting z V) (a : G) :
    a * z * a⁻¹ ∈ hsQ (a * z * a⁻¹) := by
  rw [hsQ_conj, mem_map_conj_iff]
  have e : a⁻¹ * (a * z * a⁻¹) * a = z := by group
  rw [e]
  exact h.mem_Q

end HSSetting

end CFSG.Quasithin.HSType
