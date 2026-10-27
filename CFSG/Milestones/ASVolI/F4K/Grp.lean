module

public import CFSG.Milestones.ASVolI.F4K.Iface

public section

namespace CFSG.ASVolI

section Orbit

variable {K X : Type*} [Group K] [MulAction K X]

theorem burnsideF4k_pb_orbit_eq {Λ : Set X} (hinv : ∀ k : K, ∀ r ∈ Λ, k • r ∈ Λ)
    (htr : ∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ k : K, k • r₁ = r₂) {r : X} (hr : r ∈ Λ) :
    MulAction.orbit K r = Λ := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact hinv k r hr
  · intro hy
    obtain ⟨k, rfl⟩ := htr r hr y hy
    exact MulAction.mem_orbit r k

theorem burnsideF4k_pb_card_stab_mul {Λ : Set X} (hinv : ∀ k : K, ∀ r ∈ Λ, k • r ∈ Λ)
    (htr : ∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ k : K, k • r₁ = r₂) {r : X} (hr : r ∈ Λ) :
    Nat.card (MulAction.stabilizer K r) * Nat.card Λ = Nat.card K := by
  have h1 := MulAction.index_stabilizer K r
  rw [burnsideF4k_pb_orbit_eq hinv htr hr, ← Nat.card_coe_set_eq] at h1
  rw [← h1]
  exact Subgroup.card_mul_index _

end Orbit

section Dihedral

theorem burnsideF4k_pb_d10_sq : ∀ d s : DihedralGroup 5, s * s = 1 → s ≠ 1 →
    d * d = 1 ∨ (d * s) * (d * s) = 1 := by
  decide

theorem burnsideF4k_pb_d10_cent : ∀ g s : DihedralGroup 5, s * s = 1 → s ≠ 1 → g * s = s * g →
    g = 1 ∨ g = s := by
  decide

variable {K : Type*} [Group K]

theorem burnsideF4k_pb_d10_sq_of (e : K ≃* DihedralGroup 5) (d s : K) (hs : s * s = 1)
    (hs1 : s ≠ 1) : d * d = 1 ∨ (d * s) * (d * s) = 1 := by
  have hs' : e s * e s = 1 := by rw [← map_mul, hs, map_one]
  have hs1' : e s ≠ 1 := fun h => hs1 (e.injective (by rw [h, map_one]))
  rcases burnsideF4k_pb_d10_sq (e d) (e s) hs' hs1' with h | h
  · left
    apply e.injective
    rw [map_mul, h, map_one]
  · right
    apply e.injective
    rw [map_mul, map_mul, h, map_one]

theorem burnsideF4k_pb_d10_cent_of (e : K ≃* DihedralGroup 5) (g s : K) (hs : s * s = 1)
    (hs1 : s ≠ 1) (hgs : g * s = s * g) : g = 1 ∨ g = s := by
  have hs' : e s * e s = 1 := by rw [← map_mul, hs, map_one]
  have hs1' : e s ≠ 1 := fun h => hs1 (e.injective (by rw [h, map_one]))
  have hgs' : e g * e s = e s * e g := by rw [← map_mul, hgs, map_mul]
  rcases burnsideF4k_pb_d10_cent (e g) (e s) hs' hs1' hgs' with h | h
  · left
    apply e.injective
    rw [h, map_one]
  · right
    exact e.injective h

theorem burnsideF4k_pb_d10_action {X : Type*} [MulAction K X] (e : K ≃* DihedralGroup 5)
    {Λ : Set X} (hinv : ∀ k : K, ∀ r ∈ Λ, k • r ∈ Λ)
    (htr : ∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ k : K, k • r₁ = r₂) (hcard : Nat.card Λ = 5) :
    (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, r₁ ≠ r₂ → ∃ k : K, k • r₁ = r₂ ∧ k • r₂ = r₁) ∧
      (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, r₁ ≠ r₂ → ∀ k : K, k • r₁ = r₁ → k • r₂ = r₂ → k = 1) := by
  have hK : Nat.card K = 10 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hstab : ∀ r ∈ Λ, Nat.card (MulAction.stabilizer K r) = 2 := by
    intro r hr
    have := burnsideF4k_pb_card_stab_mul hinv htr hr
    rw [hcard, hK] at this
    omega
  have huniq : ∀ r ∈ Λ, ∀ a b : K, a • r = r → b • r = r → a ≠ 1 → b ≠ 1 → a = b := by
    intro r hr a b ha hb ha1 hb1
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : MulAction.stabilizer K r)).mp (hstab r hr)
    have e1 := hy ⟨a, MulAction.mem_stabilizer_iff.mpr ha⟩
      (fun h => ha1 (by simpa using congrArg Subtype.val h))
    have e2 := hy ⟨b, MulAction.mem_stabilizer_iff.mpr hb⟩
      (fun h => hb1 (by simpa using congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hex : ∀ r ∈ Λ, ∃ t : K, t • r = r ∧ t ≠ 1 := by
    intro r hr
    obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : MulAction.stabilizer K r)).mp (hstab r hr)
    exact ⟨y, MulAction.mem_stabilizer_iff.mp y.2, fun h => hy1 (Subtype.ext h)⟩
  have hinvol : ∀ r ∈ Λ, ∀ t : K, t • r = r → t * t = 1 := by
    intro r hr t ht
    by_contra hne
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hne (one_mul 1)
    have htt : (t * t) • r = r := by rw [mul_smul, ht, ht]
    have := huniq r hr (t * t) t htt ht hne ht1
    exact ht1 (mul_eq_left.mp this)
  refine ⟨?_, ?_⟩
  · intro r₁ hr₁ r₂ hr₂ _
    obtain ⟨g, hg⟩ := htr r₁ hr₁ r₂ hr₂
    obtain ⟨t, ht, ht1⟩ := hex r₁ hr₁
    have htt := hinvol r₁ hr₁ t ht
    have key : ∀ k : K, k * k = 1 → k • r₁ = r₂ → ∃ k : K, k • r₁ = r₂ ∧ k • r₂ = r₁ := by
      intro k hk hkr
      refine ⟨k, hkr, ?_⟩
      rw [← hkr, ← mul_smul, hk, one_smul]
    rcases burnsideF4k_pb_d10_sq_of e g t htt ht1 with h | h
    · exact key g h hg
    · exact key (g * t) h (by rw [mul_smul, ht, hg])
  · intro r₁ hr₁ r₂ hr₂ hne k hk1 hk2
    by_contra hk
    obtain ⟨g, hg⟩ := htr r₁ hr₁ r₂ hr₂
    have hkk := hinvol r₁ hr₁ k hk1
    have hc : (g * k * g⁻¹) • r₂ = r₂ := by
      rw [← hg, mul_smul, mul_smul, inv_smul_smul, hk1]
    have hc1 : g * k * g⁻¹ ≠ 1 := by
      intro h
      apply hk
      calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have heq := huniq r₂ hr₂ (g * k * g⁻¹) k hc hk2 hc1 hk
    have hcomm : g * k = k * g := by
      calc g * k = g * k * g⁻¹ * g := by group
        _ = k * g := by rw [heq]
    rcases burnsideF4k_pb_d10_cent_of e g k hkk hk hcomm with h | h
    · apply hne
      rw [← hg, h, one_smul]
    · apply hne
      rw [← hg, h, hk1]

end Dihedral

theorem burnsideF4k_grpD10 : burnsideF4k_GrpD10 := by
  intro G X _ _ H ⟨e⟩ Λ hinv htr hcard
  have hinv' : ∀ k : H, ∀ r ∈ Λ, k • r ∈ Λ := fun k r hr => hinv k k.2 r hr
  have htr' : ∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ k : H, k • r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨h, hh, hr⟩ := htr r₁ hr₁ r₂ hr₂
    exact ⟨⟨h, hh⟩, hr⟩
  obtain ⟨h1, h2⟩ := burnsideF4k_pb_d10_action e hinv' htr' hcard
  refine ⟨fun r₁ hr₁ r₂ hr₂ hne => ?_, fun r₁ hr₁ r₂ hr₂ hne h hh hh1 hh2 => ?_⟩
  · obtain ⟨k, hk1, hk2⟩ := h1 r₁ hr₁ r₂ hr₂ hne
    exact ⟨k, k.2, hk1, hk2⟩
  · have := h2 r₁ hr₁ r₂ hr₂ hne ⟨h, hh⟩ hh1 hh2
    exact congrArg Subtype.val this

theorem burnsideF4k_pb_z3_action {K X : Type*} [Group K] [MulAction K X]
    (e : K ≃* Multiplicative (ZMod 3)) {Λ : Set X} (hinv : ∀ k : K, ∀ r ∈ Λ, k • r ∈ Λ)
    (htr : ∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ k : K, k • r₁ = r₂) (hcard : Nat.card Λ = 3) :
    (∀ r ∈ Λ, ∀ k : K, k • r = r → k = 1) ∧
      (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, r₁ ≠ r₂ → ∀ k : K, k • r₁ = r₂ → k • r₂ = r₁ → False) := by
  have hK : Nat.card K = 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hfree : ∀ r ∈ Λ, ∀ k : K, k • r = r → k = 1 := by
    intro r hr k hk
    have h1 := burnsideF4k_pb_card_stab_mul hinv htr hr
    rw [hcard, hK] at h1
    have h2 : Nat.card (MulAction.stabilizer K r) = 1 := by omega
    have h3 := Subgroup.eq_bot_of_card_eq _ h2
    have h4 : k ∈ MulAction.stabilizer K r := MulAction.mem_stabilizer_iff.mpr hk
    rw [h3] at h4
    exact Subgroup.mem_bot.mp h4
  refine ⟨hfree, ?_⟩
  intro r₁ hr₁ r₂ hr₂ hne k hk1 hk2
  have hkk : (k * k) • r₁ = r₁ := by rw [mul_smul, hk1, hk2]
  have h2 := hfree r₁ hr₁ (k * k) hkk
  have h3 : k ^ 3 = 1 := by
    rw [← hK]
    exact pow_card_eq_one'
  have hk : k = 1 := by
    calc k = k ^ 3 * (k * k)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  apply hne
  rw [← hk1, hk, one_smul]

theorem burnsideF4k_grpZ3 : burnsideF4k_GrpZ3 := by
  intro G X _ _ H ⟨e⟩ Λ hinv htr hcard
  have hinv' : ∀ k : H, ∀ r ∈ Λ, k • r ∈ Λ := fun k r hr => hinv k k.2 r hr
  have htr' : ∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ k : H, k • r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨h, hh, hr⟩ := htr r₁ hr₁ r₂ hr₂
    exact ⟨⟨h, hh⟩, hr⟩
  obtain ⟨h1, h2⟩ := burnsideF4k_pb_z3_action e hinv' htr' hcard
  refine ⟨fun r hr h hh hh1 => ?_, fun r₁ hr₁ r₂ hr₂ hne h hh hh1 hh2 => ?_⟩
  · have := h1 r hr ⟨h, hh⟩ hh1
    exact congrArg Subtype.val this
  · exact h2 r₁ hr₁ r₂ hr₂ hne ⟨h, hh⟩ hh1 hh2

theorem burnsideF4k_grpTwoTrans : burnsideF4k_GrpTwoTrans := by
  intro G X _ _ H Λ _ hΛ h2 hinv htr
  obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ : ∃ r₁ ∈ Λ, ∃ r₂ ∈ Λ, r₁ ≠ r₂ := by
    by_contra hcon
    push Not at hcon
    have := (Set.ncard_le_one hΛ).mpr hcon
    rw [Nat.card_coe_set_eq] at h2
    omega
  have horb : MulAction.orbit H (r₁, r₂) = Λ.offDiag := by
    ext ⟨s₁, s₂⟩
    constructor
    · rintro ⟨k, hk⟩
      simp only [Prod.smul_mk, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      refine ⟨hinv k k.2 r₁ hr₁, hinv k k.2 r₂ hr₂, ?_⟩
      intro h
      exact hne (MulAction.injective k h)
    · rintro ⟨hs₁, hs₂, hs⟩
      obtain ⟨h, hh, h1, h2⟩ := htr r₁ hr₁ r₂ hr₂ hne s₁ hs₁ s₂ hs₂ hs
      exact ⟨⟨h, hh⟩, Prod.ext h1 h2⟩
  have hdvd := Subgroup.index_dvd_card (MulAction.stabilizer H (r₁, r₂))
  rw [MulAction.index_stabilizer, horb] at hdvd
  have hoff : Λ.offDiag.ncard = Λ.ncard * Λ.ncard - Λ.ncard := by
    rw [Set.ncard_eq_toFinset_card _ hΛ.offDiag, Set.Finite.toFinset_offDiag, Finset.offDiag_card,
      Set.ncard_eq_toFinset_card _ hΛ]
  rw [Nat.card_coe_set_eq, Nat.mul_sub_one, ← hoff]
  exact hdvd

end CFSG.ASVolI
