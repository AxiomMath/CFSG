module

public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.Sporadic.HNSchreier.Pointwise
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ComponentClassification.OuterAutomorphisms Equiv

@[expose] def autA12Hom
    (β : MulAut JH) (hβ : ∀ h, h ∈ HJ ↔ β h ∈ HJ) :
    alternatingGroup (Fin 12) →* alternatingGroup (Fin 12) where
  toFun σ := thetaJ ⟨β (iotaA σ), (hβ _).1 (iotaA_mem σ)⟩
  map_one' := by
    have : (⟨β (iotaA 1), (hβ _).1 (iotaA_mem 1)⟩ : HJ) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_one]
      show β (iotaA 1) = 1
      rw [map_one iotaA, map_one β]
    rw [this, map_one thetaJ]
  map_mul' σ τ := by
    have : (⟨β (iotaA (σ * τ)), (hβ _).1 (iotaA_mem _)⟩ : HJ) =
        ⟨β (iotaA σ), (hβ _).1 (iotaA_mem σ)⟩ * ⟨β (iotaA τ), (hβ _).1 (iotaA_mem τ)⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      show β (iotaA (σ * τ)) = β (iotaA σ) * β (iotaA τ)
      rw [map_mul iotaA, map_mul β]
    rw [this, map_mul thetaJ]

theorem autA12Hom_injective
    (β : MulAut JH) (hβ : ∀ h, h ∈ HJ ↔ β h ∈ HJ) :
    Function.Injective (autA12Hom β hβ) := fun _ _ h =>
  iotaA_injective (β.injective (congrArg Subtype.val (thetaJ.injective h)))

theorem thetaJ_iotaA
    (σ : alternatingGroup (Fin 12)) : thetaJ ⟨iotaA σ, iotaA_mem σ⟩ = σ := by
  have : (⟨iotaA σ, iotaA_mem σ⟩ : HJ) = thetaJ.symm σ := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem iotaA_autA12Hom
    (β : MulAut JH) (hβ : ∀ h, h ∈ HJ ↔ β h ∈ HJ) {h : JH} (hh : h ∈ HJ) :
    iotaA (autA12Hom β hβ (thetaJ ⟨h, hh⟩)) = β h := by
  show iotaA (thetaJ ⟨β (iotaA (thetaJ ⟨h, hh⟩)), _⟩) = β h
  rw [iotaA_theta]
  show β (iotaA (thetaJ ⟨h, hh⟩)) = β h
  rw [iotaA_theta]

theorem eq_conj_of_act
    (β : MulAut JH) (h0 : JH) (hact : ∀ h ∈ HJ, β h = h0 * h * h0⁻¹) :
    β = MulAut.conj h0 := by
  have h1 := eq_one_of_fix_HJ ((MulAut.conj h0)⁻¹ * β) fun h hh => by
    rw [MulAut.mul_apply, hact h hh, MulAut.conj_inv_apply]
    group
  exact (inv_mul_eq_one.1 h1).symm

theorem theta_conjC
    (x : JH) (hx : x ∈ HJ) :
    (thetaJ ⟨conjC x, conjC_mem_HJ hx⟩ : Perm (Fin 12)) =
      swap 0 1 * (thetaJ ⟨x, hx⟩ : Perm (Fin 12)) * swap 0 1 :=
  thetaJ_conjCH ⟨x, hx⟩

theorem normalizing_mem_range
    (β : MulAut JH) (hβ : ∀ h, h ∈ HJ ↔ β h ∈ HJ) :
    β ∈ conjR.range := by
  have hF := autA12Hom_injective β hβ
  obtain ⟨π, hπ⟩ := CFSG.Milestones.alternating_automorphism_permutation (n := 12)
    (Or.inr (by norm_num))
    (MulEquiv.ofBijective (autA12Hom β hβ) ⟨hF, Finite.injective_iff_surjective.1 hF⟩)
  have hF' : ∀ σ, (autA12Hom β hβ σ : Perm (Fin 12)) = π * σ * π⁻¹ := hπ
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
  ·
    set πA : alternatingGroup (Fin 12) := ⟨π, Equiv.Perm.mem_alternatingGroup.2 hs⟩
    have hact : ∀ h ∈ HJ, β h = iotaA πA * h * (iotaA πA)⁻¹ := by
      intro h hh
      rw [← iotaA_autA12Hom β hβ hh]
      have e : autA12Hom β hβ (thetaJ ⟨h, hh⟩) = πA * thetaJ ⟨h, hh⟩ * πA⁻¹ :=
        Subtype.ext (by rw [hF']; rfl)
      rw [e, map_mul, map_mul, map_inv, iotaA_theta]
    rw [eq_conj_of_act β _ hact]
    exact ⟨⟨iotaA πA, JH_le_RH (iotaA πA).2⟩, conjR_JH _⟩
  ·
    have hs' : Equiv.Perm.sign (swap (0 : Fin 12) 1 * π) = 1 := by
      rw [Equiv.Perm.sign_mul, hs, Equiv.Perm.sign_swap (by decide)]
      decide
    set πA : alternatingGroup (Fin 12) :=
      ⟨swap 0 1 * π, Equiv.Perm.mem_alternatingGroup.2 hs'⟩
    have hact : ∀ h ∈ HJ, (conjC * β) h = iotaA πA * h * (iotaA πA)⁻¹ := by
      intro h hh
      have hβh : β h ∈ HJ := (hβ h).1 hh
      have e1 : (thetaJ ⟨conjC (β h), conjC_mem_HJ hβh⟩ : Perm (Fin 12)) =
          ((πA * thetaJ ⟨h, hh⟩ * πA⁻¹ : alternatingGroup (Fin 12)) : Perm (Fin 12)) := by
        rw [theta_conjC _ hβh]
        have e2 : (thetaJ ⟨β h, hβh⟩ : Perm (Fin 12)) = π * thetaJ ⟨h, hh⟩ * π⁻¹ := by
          have : (⟨β h, hβh⟩ : HJ) =
              ⟨iotaA (autA12Hom β hβ (thetaJ ⟨h, hh⟩)), iotaA_mem _⟩ :=
            Subtype.ext (iotaA_autA12Hom β hβ hh).symm
          rw [this, thetaJ_iotaA, hF']
        rw [e2]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, πA, mul_inv_rev, Equiv.swap_inv]
        group
      have e3 : thetaJ ⟨conjC (β h), conjC_mem_HJ hβh⟩ = πA * thetaJ ⟨h, hh⟩ * πA⁻¹ :=
        Subtype.ext e1
      have e4 := congrArg iotaA e3
      rw [iotaA_theta, map_mul, map_mul, map_inv, iotaA_theta] at e4
      rw [MulAut.mul_apply]
      exact e4
    have hβ' : β = conjC * MulAut.conj (iotaA πA) := by
      rw [← eq_conj_of_act _ _ hact, ← mul_assoc, conjC_sq, one_mul]
    rw [hβ']
    refine ⟨⟨cU, cU_mem_RH⟩ * ⟨iotaA πA, JH_le_RH (iotaA πA).2⟩, ?_⟩
    rw [map_mul, conjR_cU, conjR_JH]

theorem conjR_surjective :
    Function.Surjective conjR := by
  intro α
  obtain ⟨g, β, rfl, hβ⟩ := aut_factor α
  obtain ⟨r, hr⟩ := normalizing_mem_range β hβ
  exact ⟨⟨g, JH_le_RH g.2⟩ * r, by rw [map_mul, conjR_JH, hr]⟩

theorem conjR_bijective :
    Function.Bijective conjR := ⟨conjR_injective, conjR_surjective⟩

theorem aut_eq_conj_or
    (α : MulAut JH) :
    ∃ g : JH, α = MulAut.conj g ∨ α = MulAut.conj g * conjC := by
  obtain ⟨r, rfl⟩ := conjR_surjective α
  rcases (mem_RH_iff r).1 r.2 with h | ⟨g, hg, he⟩
  · refine ⟨⟨r, h⟩, Or.inl ?_⟩
    rw [← conjR_JH]
  · refine ⟨⟨g, hg⟩, Or.inr ?_⟩
    have : r = ⟨((⟨g, hg⟩ : JH) : GL (Fin hnsData.d) (ZMod 5)), JH_le_RH hg⟩ *
        ⟨cU, cU_mem_RH⟩ := Subtype.ext he
    rw [this, map_mul, conjR_JH, conjR_cU]

theorem card_aut :
    Nat.card (MulAut JH) = 546061824000000 := by
  rw [← Nat.card_eq_of_bijective conjR conjR_bijective, card_RH]

theorem outer_eq
    (x : Outer JH) : x = 1 ∨ x = QuotientGroup.mk conjC := by
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, h | h⟩ := aut_eq_conj_or α
  · left
    rw [QuotientGroup.eq_one_iff, h]
    exact ⟨g, rfl⟩
  · right
    rw [QuotientGroup.eq, h, mul_inv_rev]
    have := (inner_normal JH).conj_mem _ (inv_mem (⟨g, rfl⟩ : MulAut.conj g ∈ inner JH)) conjC⁻¹
    rwa [inv_inv] at this

theorem outer_zpowers :
    Subgroup.zpowers (QuotientGroup.mk conjC : Outer JH) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rcases outer_eq x with rfl | rfl
  · exact one_mem _
  · exact Subgroup.mem_zpowers _

theorem card_outer :
    Nat.card (Outer JH) = 2 := by
  rw [← Subgroup.card_top, ← outer_zpowers, Nat.card_zpowers, orderOf_outer_conjC]

theorem inner_inf_zpowers :
    inner JH ⊓ Subgroup.zpowers conjC = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨hi, hz⟩ := Subgroup.mem_inf.1 hφ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [Subgroup.mem_bot]
  have hk : conjC ^ k = conjC ^ (k % 2) := by
    rw [← zpow_mod_orderOf, orderOf_conjC]
    norm_num
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [hk, h, zpow_zero]
  · rw [hk, h, zpow_one] at hi
    exact absurd hi conjC_not_mem_inner

theorem inner_sup_zpowers :
    inner JH ⊔ Subgroup.zpowers conjC = ⊤ := by
  rw [eq_top_iff]
  intro α _
  obtain ⟨g, h | h⟩ := aut_eq_conj_or α
  · rw [h]
    exact Subgroup.mem_sup_left ⟨g, rfl⟩
  · rw [h]
    exact Subgroup.mul_mem_sup ⟨g, rfl⟩ (Subgroup.mem_zpowers _)

theorem card_aut_HN :
    Nat.card (MulAut Blueprint.NativeSporadic.HN) = 546061824000000 := by
  rw [← Nat.card_congr hnAutCongr.toEquiv, card_aut]

theorem card_outer_HN :
    Nat.card (Outer Blueprint.NativeSporadic.HN) = 2 := by
  rw [← Nat.card_congr hnOuterEquiv.toEquiv, card_outer]

theorem outer_HN_zpowers :
    Subgroup.zpowers (QuotientGroup.mk hnOuterC : Outer Blueprint.NativeSporadic.HN) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := hnOuterEquiv.surjective x
  have hy : y ∈ Subgroup.zpowers (QuotientGroup.mk conjC : Outer JH) := by
    rw [outer_zpowers]
    trivial
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [map_zpow, hnOuterEquiv_mk]
  exact Subgroup.zpow_mem_zpowers _ _


theorem ctuc_hn_full_automorphism_group :
    Function.Bijective conjR ∧
    (∀ α : MulAut JH, ∃ g : JH, α = MulAut.conj g ∨ α = MulAut.conj g * conjC) ∧
    (inner JH).Normal ∧ inner JH ⊓ Subgroup.zpowers conjC = ⊥ ∧
    inner JH ⊔ Subgroup.zpowers conjC = ⊤ ∧ orderOf conjC = 2 ∧
    Nat.card (MulAut JH) = 546061824000000 ∧
    Nat.card (Outer JH) = 2 ∧ IsCyclic (Outer JH) ∧
    Subgroup.zpowers (QuotientGroup.mk conjC : Outer JH) = ⊤ ∧
    Nat.card (MulAut Blueprint.NativeSporadic.HN) = 546061824000000 ∧
    Nat.card (Outer Blueprint.NativeSporadic.HN) = 2 ∧
    IsCyclic (Outer Blueprint.NativeSporadic.HN) ∧
    Subgroup.zpowers (QuotientGroup.mk hnOuterC : Outer Blueprint.NativeSporadic.HN) = ⊤ :=
  ⟨conjR_bijective, aut_eq_conj_or, inner_normal JH, inner_inf_zpowers, inner_sup_zpowers,
    orderOf_conjC, card_aut, card_outer, ⟨⟨_, fun x => outer_zpowers ▸ Subgroup.mem_top x⟩⟩,
    outer_zpowers, card_aut_HN, card_outer_HN,
    ⟨⟨_, fun x => outer_HN_zpowers ▸ Subgroup.mem_top x⟩⟩, outer_HN_zpowers⟩

end CFSG.Sporadic.HNSchreier
