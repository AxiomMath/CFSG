module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U4
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section CenQ

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G} {ρ : G}

theorem rho_cen_Q (h : F55Ctx c R) (hr : RhoCtx c R ρ) (hρE : ρ ∉ Eg c)
    (hE : Nat.card ↥(Eg c) = 1440)
    (hall : ∀ u : G, u * u = 1 → u ≠ 1 → IsConj u z ∨ IsConj u (c.iso.toG fhB)) (qd : QData c) :
    ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), ρ * q = q * ρ :=
  (rho_dichotomy c h hr qd).elim id (fun h2 => (no_outer_central c h hr hρE hE hall qd h2).elim)

theorem z_not_cen_Q (qd : QData c) :
    ¬ ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), z * q = q * z := by
  intro hall
  have hQz : oddCl (cenOf (c.iso.toG fhB)) ≤ cenOf z := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.2 (hall q hq).symm
  have h3 := Subgroup.card_dvd_of_le hQz
  rw [qd.card_oddCl, c.cenOf_z, c.iso.card_M₁] at h3
  omega

theorem cen_Q_le_R (h : F55Ctx c R) (qd : QData c) {k : G}
    (hkX : k ∈ cenOf (c.iso.toG fhB))
    (hcen : ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), k * q = q * k) : k ∈ R := by
  have := qd.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥(cenOf (c.iso.toG fhB)) →* MulAut ↥qd.Q := MulAut.conjNormal with hφ
  set K := φ.ker with hK
  have hker : ∀ x ∈ K, ∀ q : ↥qd.Q, (x : ↥(cenOf (c.iso.toG fhB))) *
      (q : ↥(cenOf (c.iso.toG fhB))) * x⁻¹ = q := by
    intro x hx q
    have h1 : φ x = 1 := hx
    have h2 : ((φ x q : ↥qd.Q) : ↥(cenOf (c.iso.toG fhB))) =
        x * (q : ↥(cenOf (c.iso.toG fhB))) * x⁻¹ := rfl
    rw [← h2, h1]
    rfl
  have hKQ : ∀ x ∈ K, x ∈ qd.Q → x = 1 := by
    intro x hx hxQ
    have hxG : ((x : ↥(cenOf (c.iso.toG fhB))) : G) ∈ oddCl (cenOf (c.iso.toG fhB)) :=
      (qd.mem_oddCl_iff _).2 ⟨⟨x, hxQ⟩, rfl⟩
    have h1 : ((x : ↥(cenOf (c.iso.toG fhB))) : G) = 1 := by
      refine qd.center_trivial hxG fun q hq => ?_
      obtain ⟨q', rfl⟩ := (qd.mem_oddCl_iff q).1 hq
      have := congrArg Subtype.val (hker x hx q')
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      calc ((x : ↥(cenOf (c.iso.toG fhB))) : G) * ((q' : ↥qd.Q) : ↥(cenOf (c.iso.toG fhB)))
          = (((x : ↥(cenOf (c.iso.toG fhB))) : G) * ((q' : ↥qd.Q) : ↥(cenOf (c.iso.toG fhB))) *
              ((x : ↥(cenOf (c.iso.toG fhB))) : G)⁻¹) * ((x : ↥(cenOf (c.iso.toG fhB))) : G) := by
            group
        _ = _ := by rw [this]
    exact Subtype.ext h1
  have hKdvd : Nat.card ↥K ∣ 8 := by
    have hinj : Function.Injective ((QuotientGroup.mk' qd.Q).comp K.subtype) := by
      intro x y hxy
      have h1 : ((x : ↥(cenOf (c.iso.toG fhB)))⁻¹ * y) ∈ qd.Q := by
        have := QuotientGroup.eq.1 hxy
        simpa using this
      have h2 : (x : ↥(cenOf (c.iso.toG fhB)))⁻¹ * y ∈ K := K.mul_mem (K.inv_mem x.2) y.2
      have h3 : (x : ↥(cenOf (c.iso.toG fhB)))⁻¹ * y = 1 := hKQ _ h2 h1
      apply Subtype.ext
      calc (x : ↥(cenOf (c.iso.toG fhB))) = (x : ↥(cenOf (c.iso.toG fhB))) * 1 := by group
        _ = (x : ↥(cenOf (c.iso.toG fhB))) * ((x : ↥(cenOf (c.iso.toG fhB)))⁻¹ * y) := by
          rw [h3]
        _ = y := by group
    have := Subgroup.card_dvd_of_injective _ hinj
    have hq : Nat.card (↥(cenOf (c.iso.toG fhB)) ⧸ qd.Q) = 8 := by
      rw [← Subgroup.index_eq_card, qd.index_eq]
    rwa [hq] at this
  have hK2 : IsPGroup 2 ↥K := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card ↥K ∣ 2 ^ 3 by simpa using hKdvd)
    exact IsPGroup.of_card hm
  have hRX : R ≤ cenOf (c.iso.toG fhB) := h.hR.1
  have hcR : Nat.card ↥(R.subgroupOf (cenOf (c.iso.toG fhB))) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv, h.hR64]
    norm_num
  have hR2 : IsPGroup 2 ↥(R.subgroupOf (cenOf (c.iso.toG fhB))) :=
    IsPGroup.of_card (n := 6) (by rw [hcR]; norm_num)
  have hidx : ¬ 2 ∣ (R.subgroupOf (cenOf (c.iso.toG fhB))).index := h.hR.2.2
  have hKR : K ≤ R.subgroupOf (cenOf (c.iso.toG fhB)) :=
    IsPGroup.le_sylow_of_normal hK2 (hR2.toSylow hidx)
  have hkK : (⟨k, hkX⟩ : ↥(cenOf (c.iso.toG fhB))) ∈ K := by
    show φ ⟨k, hkX⟩ = 1
    ext q
    have hqG : (((q : ↥qd.Q) : ↥(cenOf (c.iso.toG fhB))) : G) ∈
        oddCl (cenOf (c.iso.toG fhB)) := (qd.mem_oddCl_iff _).2 ⟨q, rfl⟩
    have := hcen _ hqG
    show k * (((q : ↥qd.Q) : ↥(cenOf (c.iso.toG fhB))) : G) * k⁻¹ =
      (((q : ↥qd.Q) : ↥(cenOf (c.iso.toG fhB))) : G)
    calc k * (((q : ↥qd.Q) : ↥(cenOf (c.iso.toG fhB))) : G) * k⁻¹
        = (((q : ↥qd.Q) : ↥(cenOf (c.iso.toG fhB))) : G) * k * k⁻¹ := by rw [this]
      _ = _ := by group
  exact hKR hkK

theorem cen_Q_cases (h : F55Ctx c R) (hr : RhoCtx c R ρ) (hρE : ρ ∉ Eg c) (qd : QData c)
    {k : G} (hkE : k ∈ Eg c)
    (hcen : ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), k * q = q * k) :
    k = 1 ∨ k = c.iso.toG fhB := by
  set F := c.iso.toG fhB with hF
  have hF2 : F * F = 1 := F_sq c.iso
  have hFinv : F⁻¹ = F := inv_eq_of_mul_eq_one_right hF2
  have hz2 : z * z = 1 := by simpa [pow_two] using c.z2
  have hkX : k ∈ cenOf F := Eg_le_cen c hkE
  have hkR : k ∈ R := cen_Q_le_R c h qd hkX hcen
  have hkC : k ∈ C1G c R := by
    refine ⟨hkR, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact (hcen g (B1G_le_oddCl c hg)).symm
  have hFq : ∀ q ∈ oddCl (cenOf F), F * q = q * F := fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.1 (oddCl_le _ hq)).symm
  have hFE : F ∈ Eg c := F_mem_Eg c
  have hzE : z ∈ Eg c := z_mem_Eg c
  have hρFE : ρ * F ∉ Eg c := fun hm => hρE (by
    have := (Eg c).mul_mem hm ((Eg c).inv_mem hFE)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at this)
  have hnz : ∀ w : G, w = z ∨ w = z * F → (∀ q ∈ oddCl (cenOf F), w * q = q * w) → False := by
    intro w hw hwq
    apply z_not_cen_Q c qd
    intro q hq
    rcases hw with rfl | rfl
    · exact hwq q hq
    · have := hwq q hq
      calc z * q = z * (F * F) * q := by rw [hF2, mul_one]
        _ = (z * F) * (F * q) := by group
        _ = (z * F) * (q * F) := by rw [hFq q hq]
        _ = (z * F * q) * F := by group
        _ = (q * (z * F)) * F := by rw [this]
        _ = q * (z * F * F) := by group
        _ = q * z := by rw [mul_assoc, hF2, mul_one]
  rcases C1G_cases c h hr hρE hkC with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd (h1 ▸ hkE) hρE
  · exact Or.inr h1
  · exact absurd (h1 ▸ hkE) hρFE
  · exact (hnz k (Or.inl h1) hcen).elim
  · exfalso
    apply hρE
    have := (Eg c).mul_mem ((Eg c).inv_mem hzE) (h1 ▸ hkE)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · exact (hnz k (Or.inr h1) hcen).elim
  · exfalso
    apply hρFE
    have := (Eg c).mul_mem ((Eg c).inv_mem hzE) (h1 ▸ hkE)
    rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at this

end CenQ

end CFSG.Quasithin.H13.F431.U42Aut
