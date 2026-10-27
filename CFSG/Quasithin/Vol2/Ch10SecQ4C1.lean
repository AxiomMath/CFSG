module

public import CFSG.Quasithin.Vol2.Ch10SecFA7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

set_option maxRecDepth 100000 in
theorem alt5_involution_not_comm : ∀ g p : ↥(alternatingGroup (Fin 5)), g ^ 3 = 1 → g ≠ 1 →
    p ^ 2 = 1 → p ≠ 1 → p * g ≠ g * p := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem alt5_pow_four : ∀ g : ↥(alternatingGroup (Fin 5)), g ^ 4 = 1 → g ^ 2 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem alt5_center : ∀ g : ↥(alternatingGroup (Fin 5)),
    (∀ h : ↥(alternatingGroup (Fin 5)), g * h = h * g) → g = 1 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_pow_three_of_isPGroup {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q) {w : Q}
    (hw : w ^ 3 = 1) : w = 1 := by
  obtain ⟨n, hn⟩ := hQ w
  have h1 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw
  have h2 : orderOf w ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have h3 : orderOf w ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

omit [Finite G] in
theorem orderOf_alt_eq_three {L : Subgroup G} {α : ↥L →* ↥(alternatingGroup (Fin 5))}
    (hαk : α.ker = CFSG.pCore 2 ↥L) {z : ↥L} (hz : orderOf z = 3) : orderOf (α z) = 3 := by
  have hdvd : orderOf (α z) ∣ 3 := hz ▸ orderOf_map_dvd α z
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    rw [orderOf_eq_one_iff] at h
    have hz2 : z ∈ CFSG.pCore 2 ↥L := hαk ▸ MonoidHom.mem_ker.mpr h
    have hz3 : z ^ 3 = 1 := hz ▸ pow_orderOf_eq_one z
    have hz1 := eq_one_of_pow_three_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      (w := ⟨z, hz2⟩) (Subtype.ext (by simpa using hz3))
    have : z = 1 := congrArg Subtype.val hz1
    rw [this, orderOf_one] at hz
    omega
  · exact h

theorem mem_zpowers_of_isHat {J : Subgroup G}
    (hJ : IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)))
    {z₀ x z : G} (hz₀J : z₀ ∈ J) (hz₀C : z₀ ∈ Subgroup.centralizer (J : Set G))
    (hz₀ : orderOf z₀ = 3) (hx : x ∈ J) (hz : z ∈ J) (hxo : orderOf x = 5)
    (hzo : orderOf z = 3) (hxz : x * z = z * x) : z ∈ Subgroup.zpowers z₀ := by
  obtain ⟨-, hc3, ⟨ψ⟩⟩ := hJ
  set Q := CFSG.pCore 2 ↥J with hQ
  set π₁ : ↥J →* ↥J ⧸ Q := QuotientGroup.mk' Q with hπ₁
  set Zb := Subgroup.center (↥J ⧸ Q) with hZb
  have hπ₁s : Function.Surjective π₁ := QuotientGroup.mk'_surjective Q
  have ho₀ : orderOf (π₁ ⟨z₀, hz₀J⟩) = 3 := orderOf_mk_eq hz₀J Nat.prime_three (by norm_num) hz₀
  have hox : orderOf (π₁ ⟨x, hx⟩) = 5 := orderOf_mk_eq hx Nat.prime_five (by norm_num) hxo
  have hz₀Z : π₁ ⟨z₀, hz₀J⟩ ∈ Zb := by
    rw [hZb, Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hπ₁s g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz₀C y y.2)
  have hZeq : Subgroup.zpowers (π₁ ⟨z₀, hz₀J⟩) = Zb := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hz₀Z)
    rw [Nat.card_zpowers, ho₀, hc3]
  set π₂ : ↥J ⧸ Q →* ↥(alternatingGroup (Fin 7)) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' Zb) with hπ₂
  have hker : ∀ w : ↥J ⧸ Q, π₂ w = 1 → w ∈ Zb := by
    intro w hw
    have h1 : (QuotientGroup.mk' Zb w : (↥J ⧸ Q) ⧸ Zb) = 1 := by
      apply ψ.injective
      rw [map_one]
      exact hw
    exact (QuotientGroup.eq_one_iff w).mp h1
  have hπx : orderOf (π₂ (π₁ ⟨x, hx⟩)) = 5 := by
    have hdvd : orderOf (π₂ (π₁ ⟨x, hx⟩)) ∣ 5 := hox ▸ orderOf_map_dvd π₂ _
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      have hmem := hker _ h
      have h3 : orderOf (π₁ ⟨x, hx⟩) ∣ 3 := by
        rw [← hc3, ← Subgroup.orderOf_mk (π₁ ⟨x, hx⟩) hmem]
        exact orderOf_dvd_natCard _
      rw [hox] at h3
      norm_num at h3
    · exact h
  have hπz : π₂ (π₁ ⟨z, hz⟩) = 1 := by
    have hzo' : orderOf (⟨z, hz⟩ : ↥J) = 3 := by rw [Subgroup.orderOf_mk]; exact hzo
    have hdvd : orderOf (π₂ (π₁ ⟨z, hz⟩)) ∣ 3 := hzo' ▸ orderOf_map_dvd (π₂.comp π₁) _
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      have hc : (π₂ (π₁ ⟨z, hz⟩) : Equiv.Perm (Fin 7)) * (π₂ (π₁ ⟨x, hx⟩)) =
          (π₂ (π₁ ⟨x, hx⟩)) * (π₂ (π₁ ⟨z, hz⟩)) := by
        have hc' : (⟨z, hz⟩ : ↥J) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨z, hz⟩ := Subtype.ext hxz.symm
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← map_mul,
          ← map_mul, hc']
      exact perm_seven_orderOf_ne_three (by rw [Subgroup.orderOf_coe]; exact hπx) hc
        (by rw [Subgroup.orderOf_coe]; exact h)
  have hzZ : π₁ ⟨z, hz⟩ ∈ Subgroup.zpowers (π₁ ⟨z₀, hz₀J⟩) := hZeq ▸ hker _ hπz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzZ
  rw [← map_zpow] at hk
  have hw : ((⟨z₀, hz₀J⟩ : ↥J) ^ k)⁻¹ * ⟨z, hz⟩ ∈ Q := by
    rw [← QuotientGroup.eq]
    exact hk
  have hcomm : Commute ((⟨z₀, hz₀J⟩ : ↥J) ^ k)⁻¹ ⟨z, hz⟩ := by
    refine (Commute.zpow_left ?_ k).inv_left
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz₀C z hz).symm
  have hw3 : (((⟨z₀, hz₀J⟩ : ↥J) ^ k)⁻¹ * ⟨z, hz⟩) ^ 3 = 1 := by
    have h₀' : z₀ ^ 3 = 1 := hz₀ ▸ pow_orderOf_eq_one z₀
    have h₁' : z ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one z
    have h₀ : (⟨z₀, hz₀J⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simpa using h₀')
    have h₁ : (⟨z, hz⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simpa using h₁')
    rw [hcomm.mul_pow, h₁, mul_one, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, h₀, one_zpow, inv_one]
  have h1 := eq_one_of_pow_three_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
    (w := ⟨_, hw⟩) (Subtype.ext (by simpa using hw3))
  have h2 : ((⟨z₀, hz₀J⟩ : ↥J) ^ k)⁻¹ * ⟨z, hz⟩ = 1 := congrArg Subtype.val h1
  have h3 : (⟨z, hz⟩ : ↥J) = (⟨z₀, hz₀J⟩ : ↥J) ^ k := (inv_mul_eq_one.mp h2).symm
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val h3
  simpa using this.symm

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
