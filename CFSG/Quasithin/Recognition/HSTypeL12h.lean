module

public import CFSG.Quasithin.Recognition.HSTypeL12g

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

theorem card_centralizer_transposition_filter : ∀ σ : Equiv.Perm (Fin 5),
    Equiv.Perm.sign σ = -1 → σ * σ = 1 →
      (Finset.univ.filter fun π : Equiv.Perm (Fin 5) => π * σ = σ * π).card = 12 := by
  decide +kernel

theorem card_centralizer_transposition {σ : Equiv.Perm (Fin 5)}
    (hs : Equiv.Perm.sign σ = -1) (h2 : σ * σ = 1) :
    Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 5)))) = 12 := by
  classical
  rw [← card_centralizer_transposition_filter σ hs h2, Nat.card_eq_fintype_card,
    ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun π =>
    Subgroup.mem_centralizer_singleton_iff)

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem not_mem_K_of_inverts [Finite G] (h : HSSetting z V) {s : G}
    (hsinv : ∀ u ∈ hsZQ z, s * u * s⁻¹ = u⁻¹) : s ∉ hsK z := by
  obtain ⟨w, hwZ, -, -, hww⟩ := h.exists_mem_ZQ_ne
  intro hs
  have h1 := hsinv w hwZ
  rw [← Subgroup.mem_centralizer_iff.mp hs.2 w hwZ, mul_inv_cancel_right] at h1
  have : w * w = 1 := by
    calc w * w = w * w⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel w
  rw [hww] at this
  exact h.z_ne_one this

theorem mul_not_mem_K [Finite G] (h : HSSetting z V) {s w : G} (hsnotK : s ∉ hsK z)
    (hwZ : w ∈ hsZQ z) : s * w ∉ hsK z := by
  intro h1
  apply hsnotK
  have := (hsK z).mul_mem h1 ((hsK z).inv_mem (h.Q_le_K hwZ.1))
  simpa using this

theorem mul_mul_self_eq_one [Finite G] (h : HSSetting z V) {s w : G} (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) (hwZ : w ∈ hsZQ z) : s * w * (s * w) = 1 := by
  have h1 := h.inv_of_not_mem_K hsmemH hsnotK hwZ
  calc s * w * (s * w) = (s * w * s⁻¹) * (s * s) * w := by group
    _ = w⁻¹ * 1 * w := by rw [h1, hss]
    _ = 1 := by group

theorem exists_K_conj_of_invol_not_K [Finite G] (h : HSSetting z V) {s : G} (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {w : G} (hwZ : w ∈ hsZQ z)
    (hwz : w ∉ Subgroup.zpowers z) {i : G} (hiH : i ∈ hsH z) (hiK : i ∉ hsK z)
    (hii : i * i = 1) : ∃ k ∈ hsK z, k * i * k⁻¹ = s ∨ k * i * k⁻¹ = s * w := by
  obtain ⟨φ, -, hker⟩ := h.one.quot
  set a : ↥(hsH z) := ⟨i, hiH⟩
  set b : ↥(hsH z) := ⟨s, hsmemH⟩
  have hsq : ∀ c : ↥(hsH z), (c : G) * c = 1 → φ c * φ c = 1 := by
    intro c hc
    rw [← map_mul]
    have : c * c = 1 := Subtype.ext hc
    rw [this, map_one]
  obtain ⟨ρa, hρa, ha⟩ := perm_five_odd_invol_conj (φ a)
    (h.sign_eq_neg_one_of_not_mem_K hker hiK) (hsq a hii)
  obtain ⟨ρb, hρb, hb⟩ := perm_five_odd_invol_conj (φ b)
    (h.sign_eq_neg_one_of_not_mem_K hker hsnotK) (hsq b hss)
  have hρ : Equiv.Perm.sign (ρb⁻¹ * ρa) = 1 := by
    rw [map_mul, map_inv, hρa, hρb, inv_one, one_mul]
  have hab : ρb⁻¹ * ρa * φ a * (ρb⁻¹ * ρa)⁻¹ = φ b := by
    calc ρb⁻¹ * ρa * φ a * (ρb⁻¹ * ρa)⁻¹ = ρb⁻¹ * (ρa * φ a * ρa⁻¹) * ρb := by group
      _ = ρb⁻¹ * (ρb * φ b * ρb⁻¹) * ρb := by rw [ha, hb]
      _ = φ b := by group
  obtain ⟨k, hk, q, hq, hkq⟩ := h.exists_K_conj_eq_mul hker hρ hab
  have hsq' : s * q * (s * q) = 1 := by
    have : k * i * k⁻¹ * (k * i * k⁻¹) = 1 := by
      calc k * i * k⁻¹ * (k * i * k⁻¹) = k * (i * i) * k⁻¹ := by group
        _ = 1 := by rw [hii, mul_one, mul_inv_cancel]
    rw [hkq] at this
    exact this
  obtain ⟨r, hr, hrq⟩ := h.exists_conj_of_invol_mul hsmemH hsnotK hss hwZ hwz hq hsq'
  refine ⟨r⁻¹ * k, (hsK z).mul_mem (h.Q_le_K ((hsQ z).inv_mem hr)) hk, ?_⟩
  have hkq' : k * i * k⁻¹ = s * q := hkq
  have e : r⁻¹ * k * i * (r⁻¹ * k)⁻¹ = r⁻¹ * (s * q) * r := by
    rw [← hkq']
    group
  rcases hrq with hrq | hrq
  · left
    rw [e, hrq]
    group
  · right
    rw [e, hrq]
    group

theorem exists_conj_of_invol [Finite G] (h : HSSetting z V) {s : G} (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {w : G} (hwZ : w ∈ hsZQ z)
    (hwz : w ∉ Subgroup.zpowers z) {i : G} (hii : i * i = 1) (hi1 : i ≠ 1) :
    ∃ g : G, g * i * g⁻¹ = s ∨ g * i * g⁻¹ = s * w := by
  obtain ⟨g, hgH, hgK⟩ := h.exists_conj_mem_H_not_mem_K hii hi1
  have hg2 : g * i * g⁻¹ * (g * i * g⁻¹) = 1 := by
    calc g * i * g⁻¹ * (g * i * g⁻¹) = g * (i * i) * g⁻¹ := by group
      _ = 1 := by rw [hii, mul_one, mul_inv_cancel]
  obtain ⟨k, -, hk⟩ := h.exists_K_conj_of_invol_not_K hsmemH hsnotK hss hwZ hwz hgH hgK hg2
  refine ⟨k * g, ?_⟩
  have e : k * g * i * (k * g)⁻¹ = k * (g * i * g⁻¹) * k⁻¹ := by group
  rw [e]
  exact hk

theorem not_conj_mul_of_conj_z [Finite G] (h : HSSetting z V) {s : G} (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {w : G} (hwZ : w ∈ hsZQ z)
    (hwz : w ∉ Subgroup.zpowers z) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    (∀ g : G, g * z * g⁻¹ ≠ s * w) ∧ ∃ t ∈ hsK z, t ∉ hsQ z ∧ t * t = 1 ∧
      (∃ v ∈ V, v * t * v⁻¹ = z * t) ∧ ∃ g : G, g * t * g⁻¹ = s * w := by
  obtain ⟨t, htK, htQ, htt, -, v, hvV, hvt⟩ := h.exists_invol_K_not_Q
  have ht1 : t ≠ 1 := fun h1 => htQ (h1 ▸ (hsQ z).one_mem)
  have htz : ∀ g : G, g * z * g⁻¹ ≠ t := by
    intro g hg
    apply htQ
    rw [← hg]
    exact h.mem_Q_of_conj_mem_K (hg ▸ htK)
  obtain ⟨g, hg⟩ := h.exists_conj_of_invol hsmemH hsnotK hss hwZ hwz htt ht1
  rcases hg with hg | hg
  · exfalso
    apply htz (g⁻¹ * g₀)
    rw [← hg₀] at hg
    calc g⁻¹ * g₀ * z * (g⁻¹ * g₀)⁻¹ = g⁻¹ * (g₀ * z * g₀⁻¹) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hg]
      _ = t := by group
  · refine ⟨fun g' hg' => htz (g⁻¹ * g') ?_, t, htK, htQ, htt, ⟨v, hvV, hvt⟩, g, hg⟩
    calc g⁻¹ * g' * z * (g⁻¹ * g')⁻¹ = g⁻¹ * (g' * z * g'⁻¹) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hg', hg]
      _ = t := by group

theorem two_classes [Finite G] (h : HSSetting z V) :
    ∃ t ∈ hsK z, t ∉ hsQ z ∧ t * t = 1 ∧ (∃ v ∈ V, v * t * v⁻¹ = z * t) ∧
      (∀ g : G, g * z * g⁻¹ ≠ t) ∧
      ∀ i : G, i * i = 1 → i ≠ 1 → (∃ g : G, g * i * g⁻¹ = z) ∨ ∃ g : G, g * i * g⁻¹ = t := by
  obtain ⟨s, ⟨hsmemH, -⟩, hss, hsinv, g₀, hg₀⟩ := h.exists_invol_inverts_ZQ
  obtain ⟨w, hwZ, hw1, hwz', -⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  have hsnotK := h.not_mem_K_of_inverts hsinv
  obtain ⟨-, t, htK, htQ, htt, hv, g₁, hg₁⟩ :=
    h.not_conj_mul_of_conj_z hsmemH hsnotK hss hwZ hwz hg₀
  have htQ' := htQ
  refine ⟨t, htK, htQ, htt, hv, fun g hg => htQ' ?_, fun i hii hi1 => ?_⟩
  · rw [← hg]
    exact h.mem_Q_of_conj_mem_K (hg ▸ htK)
  · obtain ⟨g, hg⟩ := h.exists_conj_of_invol hsmemH hsnotK hss hwZ hwz hii hi1
    rcases hg with hg | hg
    · left
      refine ⟨g₀⁻¹ * g, ?_⟩
      calc g₀⁻¹ * g * i * (g₀⁻¹ * g)⁻¹ = g₀⁻¹ * (g * i * g⁻¹) * g₀ := by group
        _ = z := by rw [hg, ← hg₀]; group
    · right
      refine ⟨g₁⁻¹ * g, ?_⟩
      calc g₁⁻¹ * g * i * (g₁⁻¹ * g)⁻¹ = g₁⁻¹ * (g * i * g⁻¹) * g₁ := by group
        _ = t := by rw [hg, ← hg₁]; group

theorem card_centralizer_H_of_not_conj [Finite G] (h : HSSetting z V) {j : G}
    (hjH : j ∈ hsH z) (hjK : j ∉ hsK z) (hjj : j * j = 1) {w : G} (hwZ : w ∈ hsZQ z)
    (hwz : w ∉ Subgroup.zpowers z) (hnc : ∀ g : G, g * j * g⁻¹ ≠ j * w) :
    Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({j} : Set G)) = 96 := by
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hconj : ∀ g ∈ hsH z, g * j * g⁻¹ * j⁻¹ ∈ hsQ z →
      ∃ r ∈ hsQ z, g * j * g⁻¹ = r * j * r⁻¹ := by
    intro g hg hq
    have hmem : j⁻¹ * (g * j * g⁻¹) ∈ hsQ z := by
      have := conj_mem_Q ((hsH z).inv_mem hjH) hq
      have heq : j⁻¹ * (g * j * g⁻¹ * j⁻¹) * j⁻¹⁻¹ = j⁻¹ * (g * j * g⁻¹) := by group
      rwa [heq] at this
    have hinvol : j * (j⁻¹ * (g * j * g⁻¹)) * (j * (j⁻¹ * (g * j * g⁻¹))) = 1 := by
      calc j * (j⁻¹ * (g * j * g⁻¹)) * (j * (j⁻¹ * (g * j * g⁻¹))) = g * (j * j) * g⁻¹ := by
            group
        _ = 1 := by rw [hjj, mul_one, mul_inv_cancel]
    have he : j * (j⁻¹ * (g * j * g⁻¹)) = g * j * g⁻¹ := by group
    obtain ⟨r, hr, hrj⟩ := h.exists_conj_of_invol_mul hjH hjK hjj hwZ hwz hmem hinvol
    rw [he] at hrj
    rcases hrj with hrj | hrj
    · exact ⟨r, hr, hrj⟩
    · exfalso
      apply hnc (r⁻¹ * g)
      calc r⁻¹ * g * j * (r⁻¹ * g)⁻¹ = r⁻¹ * (g * j * g⁻¹) * r := by group
        _ = j * w := by rw [hrj]; group
  rw [h.card_centralizer_H_of_conj hjH hφ hker hconj, h.card_centralizer_invol hjH hjK hjj]
  have h2 : φ ⟨j, hjH⟩ * φ ⟨j, hjH⟩ = 1 := by
    rw [← map_mul]
    have : (⟨j, hjH⟩ : ↥(hsH z)) * ⟨j, hjH⟩ = 1 := Subtype.ext hjj
    rw [this, map_one]
  rw [card_centralizer_transposition (h.sign_eq_neg_one_of_not_mem_K hker hjK) h2]

theorem card_centralizer_H_invol_not_K [Finite G] (h : HSSetting z V) {s : G}
    (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z) (hss : s * s = 1) {w : G} (hwZ : w ∈ hsZQ z)
    (hwz : w ∉ Subgroup.zpowers z) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({s} : Set G)) = 96 ∧
      Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({s * w} : Set G)) = 96 := by
  obtain ⟨hnc, -⟩ := h.not_conj_mul_of_conj_z hsmemH hsnotK hss hwZ hwz hg₀
  have hsw : ∀ g : G, g * s * g⁻¹ ≠ s * w := by
    intro g hg
    apply hnc (g * g₀)
    rw [← hg, ← hg₀]
    group
  have hw1 : w ≠ 1 := fun h1 => hwz (h1 ▸ (Subgroup.zpowers z).one_mem)
  have hwz' : w ≠ z := fun h1 => hwz (h1 ▸ Subgroup.mem_zpowers z)
  have hww : w * w = z := by
    rcases h.z_eq_or_sq_of_mem_ZQ hwZ hw1 with h1 | h1
    · exact absurd h1.symm hwz'
    · exact h1.symm
  refine ⟨h.card_centralizer_H_of_not_conj hsmemH hsnotK hss hwZ hwz hsw,
    h.card_centralizer_H_of_not_conj ((hsH z).mul_mem hsmemH (h.Q_le_H hwZ.1))
      (h.mul_not_mem_K hsnotK hwZ) (h.mul_mul_self_eq_one hsmemH hsnotK hss hwZ) hwZ hwz ?_⟩
  have hzC : z ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm⟩
  obtain ⟨r', -, hr'z⟩ := h.exists_conj_eq_mul_of_invol hsmemH hsnotK hss hzC
  intro g hg
  apply hsw (g⁻¹ * r')
  calc g⁻¹ * r' * s * (g⁻¹ * r')⁻¹ = g⁻¹ * (r' * s * r'⁻¹) * g := by group
    _ = g⁻¹ * (s * (w * w)) * g := by rw [← hr'z, hww]
    _ = g⁻¹ * (g * (s * w) * g⁻¹) * g := by rw [hg]; group
    _ = s * w := by group

end HSSetting

end CFSG.Quasithin.HSType
