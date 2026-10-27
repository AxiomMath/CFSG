module

public import CFSG.GH74.Uniqueness.Statements

public section

namespace CFSG.StronglyEmbedded.UniqueCoset

open CFSG.GH74.Uniqueness

variable {G : Type*} [Group G]

theorem smul_coe_eq_iff (H : Subgroup G) (x g : G) :
    x • (g : G ⧸ H) = g ↔ g⁻¹ * x * g ∈ H := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, ← H.inv_mem_iff]
  have h : ((x * g)⁻¹ * g)⁻¹ = g⁻¹ * x * g := by group
  rw [h]

theorem existsUnique_fixed_conj {H : Subgroup G} {x : G} (a : G)
    (h : ∃! c : G ⧸ H, x • c = c) : ∃! c : G ⧸ H, (a * x * a⁻¹) • c = c := by
  obtain ⟨c, hc, huniq⟩ := h
  refine ⟨a • c, ?_, fun d (hd : (a * x * a⁻¹) • d = d) => ?_⟩
  · show (a * x * a⁻¹) • a • c = a • c
    rw [smul_smul, inv_mul_cancel_right, mul_smul, hc]
  · have hd' : x • (a⁻¹ • d) = a⁻¹ • d := by
      rw [smul_smul, show x * a⁻¹ = a⁻¹ * (a * x * a⁻¹) by group, mul_smul, hd]
    rw [← huniq _ hd', smul_inv_smul]

theorem existsUnique_fixed_of_isConj {H : Subgroup G} {x y : G} (hxy : IsConj x y)
    (h : ∃! c : G ⧸ H, x • c = c) : ∃! c : G ⧸ H, y • c = c := by
  obtain ⟨a, rfl⟩ := isConj_iff.1 hxy
  exact existsUnique_fixed_conj a h

theorem existsUnique_fixed_mul {H : Subgroup G} {z x y : G}
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    (hx : IsConj z x) (hy : IsConj z y) (hxy : x * y = y * x) (hne : x ≠ y) :
    ∃! c : G ⧸ H, (x * y) • c = c := by
  obtain ⟨a, rfl⟩ := isConj_iff.1 hx
  obtain ⟨b, rfl⟩ := isConj_iff.1 hy
  have hw : (b⁻¹ * a)⁻¹ * z * (b⁻¹ * a) = a⁻¹ * (b * z * b⁻¹) * a := by group
  have hne' : (b⁻¹ * a)⁻¹ * z * (b⁻¹ * a) ≠ z := by
    rw [hw]
    intro h
    apply hne
    calc a * z * a⁻¹ = a * (a⁻¹ * (b * z * b⁻¹) * a) * a⁻¹ := by rw [h]
      _ = b * z * b⁻¹ := by group
  have hcomm : z * ((b⁻¹ * a)⁻¹ * z * (b⁻¹ * a)) = (b⁻¹ * a)⁻¹ * z * (b⁻¹ * a) * z := by
    rw [hw]
    calc z * (a⁻¹ * (b * z * b⁻¹) * a) = a⁻¹ * (a * z * a⁻¹ * (b * z * b⁻¹)) * a := by group
      _ = a⁻¹ * (b * z * b⁻¹ * (a * z * a⁻¹)) * a := by rw [hxy]
      _ = a⁻¹ * (b * z * b⁻¹) * a * z := by group
  have key := existsUnique_fixed_conj a (h2 _ hne' hcomm)
  have heq : a * (z * ((b⁻¹ * a)⁻¹ * z * (b⁻¹ * a))) * a⁻¹ = a * z * a⁻¹ * (b * z * b⁻¹) := by
    rw [hw]
    group
  rwa [heq] at key

theorem isInvariantInvolutionSet {z : G} (hz : orderOf z = 2) :
    IsInvariantInvolutionSet (conjugatesOf z) := by
  refine ⟨fun x hx => ?_, fun x hx g => ?_⟩
  · obtain ⟨a, rfl⟩ := isConj_iff.1 hx
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
  · exact IsConj.trans hx (isConj_iff.2 ⟨g⁻¹, by group⟩)

theorem isProductDisconnected {H : Subgroup G} (hH : H ≠ ⊤) {z : G} (hz : orderOf z = 2)
    (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c) :
    IsProductDisconnected (conjugatesOf z) H := by
  refine ⟨hH, ?_, fun x hx hxH g => ?_, ?_⟩
  · obtain ⟨c, hc, -⟩ := h1
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    exact ⟨g⁻¹ * z * g, isConj_iff.2 ⟨g⁻¹, by group⟩, (smul_coe_eq_iff H z g).1 hc⟩
  · have hu := existsUnique_fixed_of_isConj hx h1
    have h1x : x • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) :=
      (smul_coe_eq_iff H x 1).2 (by simpa using hxH)
    constructor
    · intro hg
      have hgx : x • (g : G ⧸ H) = g := (smul_coe_eq_iff H x g).2 hg
      have h := QuotientGroup.eq.1 (hu.unique hgx h1x)
      simpa using h
    · intro hg
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg
  · rintro u ⟨hu2, x, hx, y, hy, hxy, rfl⟩ huH c hc
    have hx2 : orderOf x = 2 := (isInvariantInvolutionSet hz).1 x hx
    have hne : x ≠ y := by
      rintro rfl
      have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
      rw [hxx, orderOf_one] at hu2
      exact absurd hu2 (by norm_num)
    have hu := existsUnique_fixed_mul h2 hx hy hxy hne
    have h1u : (x * y) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) :=
      (smul_coe_eq_iff H _ 1).2 (by simpa using huH)
    have hcu : (x * y) • (c : G ⧸ H) = c := by
      refine (smul_coe_eq_iff H _ c).2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      have hconj : c⁻¹ * (x * y) * c = x * y := by
        rw [mul_assoc, ← hc]
        group
      rw [hconj]
      exact huH
    have h := QuotientGroup.eq.1 (hu.unique hcu h1u)
    simpa using h

theorem isStronglyEmbeddedOrder_of_involutions {X : Type*} [Group X] [Finite X]
    {M : Subgroup X} (hM : M ≠ ⊤) {t₀ : X} (ht₀ : t₀ ∈ M) (ht₀2 : orderOf t₀ = 2)
    (h : ∀ t ∈ M, orderOf t = 2 → ∀ g : X, g⁻¹ * t * g ∈ M → g ∈ M) :
    BenderSuzuki.IsStronglyEmbeddedOrder M := by
  refine ⟨hM, ?_, fun g hg => ?_⟩
  · have hord : orderOf (⟨t₀, ht₀⟩ : M) = 2 := by rw [Subgroup.orderOf_mk, ht₀2]
    rw [even_iff_two_dvd, ← hord]
    exact orderOf_dvd_natCard _
  · rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 heven)
    obtain ⟨htM, htg⟩ := Subgroup.mem_inf.1 t.2
    obtain ⟨m, hm, hmt⟩ := Subgroup.mem_map.1 htg
    have hconj : g⁻¹ * (t : X) * g = m := by
      rw [← hmt]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact hg (h _ htM (by rw [Subgroup.orderOf_coe, ht]) g (hconj ▸ hm))

end CFSG.StronglyEmbedded.UniqueCoset
