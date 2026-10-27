module

public import CFSG.RankThree.LocalRank.ElementaryTwoWeights
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.RankThree.GroupTheory

open CFSG.RankThree.LocalRank

theorem finrank_iSup_eq_sum_of_iSupIndep {k : Type*} [Field k] {V : Type*} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {ι : Type*} [Fintype ι] {W : ι → Submodule k V}
    (h : iSupIndep W) : Module.finrank k ↥(⨆ i, W i) = ∑ i, Module.finrank k (W i) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum,
    ← (LinearEquiv.ofInjective _ h.dfinsupp_lsum_injective).finrank_eq]
  exact Module.finrank_directSum (R := k) (fun i => ↥(W i))

theorem eq_bot_or_eq_top_of_isIrreducible {k : Type*} [Field k] {V : Type*} [AddCommGroup V]
    [Module k V] {G : Type*} [Monoid G] {ρ : Representation k G V} (hρ : ρ.IsIrreducible)
    (W : Submodule k V) (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  rcases hρ.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

theorem nontrivial_of_isIrreducible {k : Type*} [Field k] {V : Type*} [AddCommGroup V]
    [Module k V] {G : Type*} [Monoid G] {ρ : Representation k G V} (hρ : ρ.IsIrreducible) :
    Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (Submodule k V) := (Submodule.subsingleton_iff k).mpr h
  exact (bot_ne_top (α := Subrepresentation ρ))
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem semidirect_rep_mem {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} {ρ : Representation k (N ⋊[φ] G) V}
    {W : Submodule k V} (hN : ∀ n, ∀ v ∈ W, ρ (SemidirectProduct.inl n) v ∈ W)
    (hG : ∀ g, ∀ v ∈ W, ρ (SemidirectProduct.inr g) v ∈ W) : ∀ x, ∀ v ∈ W, ρ x v ∈ W := by
  intro x v hv
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, Module.End.mul_apply]
  exact hN _ _ (hG _ _ hv)

section DualAction

variable {R : Type*} [CommGroup R] [Module (ZMod 2) (Additive R)]

@[expose] def mulAutLinear (σ : MulAut R) : Additive R →ₗ[ZMod 2] Additive R :=
  (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap 2

theorem mulAutLinear_ofMul (σ : MulAut R) (a : R) :
    mulAutLinear σ (Additive.ofMul a) = Additive.ofMul (σ a) := rfl

@[expose] def dualAct (σ : MulAut R) :
    Module.Dual (ZMod 2) (Additive R) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive R) :=
  (mulAutLinear σ⁻¹).dualMap

theorem dualAct_ofMul (σ : MulAut R) (χ : Module.Dual (ZMod 2) (Additive R)) (a : R) :
    dualAct σ χ (Additive.ofMul a) = χ (Additive.ofMul (σ⁻¹ a)) := rfl

theorem dualAct_mul (σ τ : MulAut R) (χ : Module.Dual (ZMod 2) (Additive R)) :
    dualAct (σ * τ) χ = dualAct σ (dualAct τ χ) := rfl

theorem dualAct_one (χ : Module.Dual (ZMod 2) (Additive R)) : dualAct 1 χ = χ := rfl

theorem dualAct_inv_dualAct (σ : MulAut R) (χ : Module.Dual (ZMod 2) (Additive R)) :
    dualAct σ⁻¹ (dualAct σ χ) = χ := by
  rw [← dualAct_mul, inv_mul_cancel, dualAct_one]

@[expose] def dualStabilizer (χ : Module.Dual (ZMod 2) (Additive R)) : Subgroup (MulAut R) where
  carrier := {σ | dualAct σ χ = χ}
  mul_mem' {σ τ} hσ hτ := by
    change dualAct σ χ = χ at hσ
    change dualAct τ χ = χ at hτ
    change dualAct (σ * τ) χ = χ
    rw [dualAct_mul, hτ, hσ]
  one_mem' := dualAct_one χ
  inv_mem' {σ} hσ := by
    change dualAct σ χ = χ at hσ
    change dualAct σ⁻¹ χ = χ
    calc dualAct σ⁻¹ χ = dualAct σ⁻¹ (dualAct σ χ) := by rw [hσ]
      _ = χ := dualAct_inv_dualAct σ χ

theorem mem_dualStabilizer (χ : Module.Dual (ZMod 2) (Additive R)) (σ : MulAut R) :
    σ ∈ dualStabilizer χ ↔ dualAct σ χ = χ := Iff.rfl

end DualAction

section Semidirect

variable {R : Type*} [CommGroup R] [Module (ZMod 2) (Additive R)] {H : Type*} [Group H]
  {φ : H →* MulAut R} {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem rep_inl_mem_signWeightSpace (ρ : Representation k (R ⋊[φ] H) V) (a : R)
    {χ : Module.Dual (ZMod 2) (Additive R)} {v : V}
    (hv : v ∈ signWeightSpace (ρ.comp SemidirectProduct.inl) χ) :
    ρ (SemidirectProduct.inl a) v ∈ signWeightSpace (ρ.comp SemidirectProduct.inl) χ := by
  have h := (mem_signWeightSpace _ χ v).mp hv a
  rw [MonoidHom.comp_apply] at h
  rw [h]
  exact Submodule.smul_mem _ _ hv

theorem rep_inr_mem_signWeightSpace (ρ : Representation k (R ⋊[φ] H) V) (h : H)
    {χ : Module.Dual (ZMod 2) (Additive R)} {v : V}
    (hv : v ∈ signWeightSpace (ρ.comp SemidirectProduct.inl) χ) :
    ρ (SemidirectProduct.inr h) v ∈
      signWeightSpace (ρ.comp SemidirectProduct.inl) (dualAct (φ h) χ) := by
  rw [mem_signWeightSpace] at hv ⊢
  intro a
  have hconj : (SemidirectProduct.inl a : R ⋊[φ] H) * SemidirectProduct.inr h =
      SemidirectProduct.inr h * SemidirectProduct.inl ((φ h)⁻¹ a) := by
    rw [SemidirectProduct.inl_aut_inv, map_inv]
    group
  have hv' := hv ((φ h)⁻¹ a)
  simp only [MonoidHom.comp_apply] at hv' ⊢
  rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply, hv', map_smul,
    dualAct_ofMul]

omit [Module (ZMod 2) (Additive R)] in
theorem rep_inr_inv_apply_rep_inr (ρ : Representation k (R ⋊[φ] H) V) (h : H) (v : V) :
    ρ (SemidirectProduct.inr h⁻¹) (ρ (SemidirectProduct.inr h) v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
    Module.End.one_apply]

theorem signWeightSpace_dualAct_ne_bot (ρ : Representation k (R ⋊[φ] H) V) (h : H)
    {χ : Module.Dual (ZMod 2) (Additive R)}
    (hχ : signWeightSpace (ρ.comp SemidirectProduct.inl) χ ≠ ⊥) :
    signWeightSpace (ρ.comp SemidirectProduct.inl) (dualAct (φ h) χ) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  intro hbot
  have h1 := rep_inr_mem_signWeightSpace ρ h hv
  rw [hbot, Submodule.mem_bot] at h1
  apply hv0
  rw [← rep_inr_inv_apply_rep_inr ρ h v, h1, map_zero]

theorem finrank_signWeightSpace_dualAct [FiniteDimensional k V]
    (ρ : Representation k (R ⋊[φ] H) V) (h : H) (χ : Module.Dual (ZMod 2) (Additive R)) :
    Module.finrank k (signWeightSpace (ρ.comp SemidirectProduct.inl) (dualAct (φ h) χ)) =
      Module.finrank k (signWeightSpace (ρ.comp SemidirectProduct.inl) χ) := by
  set ρR := ρ.comp SemidirectProduct.inl
  have hinj : ∀ g : H, Function.Injective (ρ (SemidirectProduct.inr g)) := fun g v w hvw => by
    rw [← rep_inr_inv_apply_rep_inr ρ g v, hvw, rep_inr_inv_apply_rep_inr]
  have h1 : ∀ v ∈ signWeightSpace ρR χ, ρ (SemidirectProduct.inr h) v ∈
      signWeightSpace ρR (dualAct (φ h) χ) := fun v hv => rep_inr_mem_signWeightSpace ρ h hv
  have h2 : ∀ v ∈ signWeightSpace ρR (dualAct (φ h) χ), ρ (SemidirectProduct.inr h⁻¹) v ∈
      signWeightSpace ρR χ := fun v hv => by
    have h3 := rep_inr_mem_signWeightSpace ρ h⁻¹ hv
    rwa [map_inv, dualAct_inv_dualAct] at h3
  refine le_antisymm ?_ ?_
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := (ρ (SemidirectProduct.inr h⁻¹)).restrict h2) fun v w hvw =>
        Subtype.ext (hinj h⁻¹ (congrArg Subtype.val hvw))
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := (ρ (SemidirectProduct.inr h)).restrict h1) fun v w hvw =>
        Subtype.ext (hinj h (congrArg Subtype.val hvw))

theorem signWeightSpace_rep_mem_of_forall_dualAct (ρ : Representation k (R ⋊[φ] H) V)
    {χ : Module.Dual (ZMod 2) (Additive R)} (hχ : ∀ h, dualAct (φ h) χ = χ) :
    ∀ x, ∀ v ∈ signWeightSpace (ρ.comp SemidirectProduct.inl) χ,
      ρ x v ∈ signWeightSpace (ρ.comp SemidirectProduct.inl) χ := by
  refine semidirect_rep_mem (fun a v hv => rep_inl_mem_signWeightSpace ρ a hv) fun h v hv => ?_
  have h1 := rep_inr_mem_signWeightSpace ρ h hv
  rwa [hχ h] at h1

theorem card_le_two_of_signWeightSpace_eq_top [Finite R] (ρ : Representation k R V)
    (hinj : Function.Injective ρ) {χ : Module.Dual (ZMod 2) (Additive R)}
    (hχ : signWeightSpace ρ χ = ⊤) : Nat.card R ≤ 2 := by
  have hker : Function.Injective χ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ρ (Additive.toMul x) = 1 := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ signWeightSpace ρ χ := by rw [hχ]; exact Submodule.mem_top
      rw [(mem_signWeightSpace ρ χ v).mp hv, ofMul_toMul, hx, ZMod.val_zero, pow_zero, one_smul,
        Module.End.one_apply]
    have h2 : Additive.toMul x = 1 := hinj (h1.trans (map_one ρ).symm)
    rw [← ofMul_toMul x, h2, ofMul_one]
  have h := Nat.card_le_card_of_injective _ hker
  rwa [Nat.card_zmod, Nat.card_congr Additive.toMul] at h

end Semidirect

theorem prime_dimensional_irreducible_elementary_two_action_scalar_centralizer {p : ℕ}
    (hp : p.Prime) {R : Type*} [CommGroup R] [Finite R] [Module (ZMod 2) (Additive R)]
    (hR : 4 ≤ Nat.card R) {H : Type*} [Group H] {φ : H →* MulAut R}
    (hφ : Nat.card φ.range = p) {k : Type*} [Field k] (hk : (2 : k) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module k V] (hV : Module.finrank k V = p)
    (ρ : Representation k (R ⋊[φ] H) V) (hρ : ρ.IsIrreducible)
    (hinj : Function.Injective (ρ.comp SemidirectProduct.inl)) :
    ∀ T : LinearMap.GeneralLinearGroup k V,
      (∀ g, Commute (T : Module.End k V) (ρ g)) ↔
        ∃ c : k, c ≠ 0 ∧ (T : Module.End k V) = c • 1 := by
  classical
  have hp0 : 0 < Module.finrank k V := hV ▸ hp.pos
  have : FiniteDimensional k V := Module.finite_of_finrank_pos hp0
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hp0
  let := Fintype.ofFinite R
  have : Finite (Module.Dual (ZMod 2) (Additive R)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive R) => (f : Additive R → ZMod 2))
      DFunLike.coe_injective
  let := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive R))
  set ρR := ρ.comp SemidirectProduct.inl with hρR
  obtain ⟨χ, hχ⟩ : ∃ χ, signWeightSpace ρR χ ≠ ⊥ := by
    by_contra h
    push Not at h
    have htop := iSup_signWeightSpace_eq_top ρR hk
    simp only [h, iSup_bot] at htop
    exact bot_ne_top htop
  set Γ := φ.range
  have hmove : ∃ h : H, dualAct (φ h) χ ≠ χ := by
    by_contra hfix
    push Not at hfix
    rcases eq_bot_or_eq_top_of_isIrreducible hρ _
        (signWeightSpace_rep_mem_of_forall_dualAct ρ hfix) with h | h
    · exact hχ h
    · have := card_le_two_of_signWeightSpace_eq_top ρR hinj h
      omega
  have hstab : (dualStabilizer χ).subgroupOf Γ = ⊥ := by
    have hdvd := Subgroup.card_subgroup_dvd_card ((dualStabilizer χ).subgroupOf Γ)
    rw [hφ] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      rw [← hφ, Subgroup.card_eq_iff_eq_top] at h
      obtain ⟨h₀, hh₀⟩ := hmove
      have hmem : (⟨φ h₀, h₀, rfl⟩ : Γ) ∈ (dualStabilizer χ).subgroupOf Γ := by
        rw [h]
        exact Subgroup.mem_top _
      exact hh₀ hmem
  have horbinj : Function.Injective fun σ : Γ => dualAct (σ : MulAut R) χ := by
    intro σ τ hστ
    change dualAct (σ : MulAut R) χ = dualAct (τ : MulAut R) χ at hστ
    have hmem : τ⁻¹ * σ ∈ (dualStabilizer χ).subgroupOf Γ := by
      rw [Subgroup.mem_subgroupOf, mem_dualStabilizer]
      change dualAct ((τ : MulAut R)⁻¹ * (σ : MulAut R)) χ = χ
      rw [dualAct_mul, hστ, dualAct_inv_dualAct]
    rw [hstab, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  have hdim : ∀ σ : Γ, Module.finrank k (signWeightSpace ρR (dualAct (σ : MulAut R) χ)) =
      Module.finrank k (signWeightSpace ρR χ) := by
    rintro ⟨_, h, rfl⟩
    exact finrank_signWeightSpace_dualAct ρ h χ
  have hsum : ∑ ψ, Module.finrank k (signWeightSpace ρR ψ) = p := by
    rw [← finrank_iSup_eq_sum_of_iSupIndep (iSupIndep_signWeightSpace ρR hk),
      iSup_signWeightSpace_eq_top ρR hk, finrank_top, hV]
  let := Fintype.ofFinite Γ
  have hle : p * Module.finrank k (signWeightSpace ρR χ) ≤ p := by
    calc p * Module.finrank k (signWeightSpace ρR χ) =
          ∑ σ : Γ, Module.finrank k (signWeightSpace ρR (dualAct (σ : MulAut R) χ)) := by
          rw [Finset.sum_congr rfl fun σ _ => hdim σ, Finset.sum_const, Finset.card_univ,
            smul_eq_mul, ← Nat.card_eq_fintype_card, hφ]
      _ = ∑ ψ ∈ Finset.univ.image fun σ : Γ => dualAct (σ : MulAut R) χ,
            Module.finrank k (signWeightSpace ρR ψ) :=
          (Finset.sum_image (f := fun ψ => Module.finrank k (signWeightSpace ρR ψ))
            fun σ _ τ _ h => horbinj h).symm
      _ ≤ ∑ ψ, Module.finrank k (signWeightSpace ρR ψ) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = p := hsum
  have hpos : 0 < Module.finrank k (signWeightSpace ρR χ) :=
    Nat.pos_of_ne_zero fun h => hχ (Submodule.finrank_eq_zero.mp h)
  have hline : Module.finrank k (signWeightSpace ρR χ) = 1 := by
    have h1 : Module.finrank k (signWeightSpace ρR χ) ≤ 1 :=
      (Nat.mul_le_mul_left_iff hp.pos).mp (by rwa [mul_one])
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  intro T
  constructor
  · intro hT
    have hTv : (T : Module.End k V) v ∈ signWeightSpace ρR χ := by
      rw [mem_signWeightSpace] at hv ⊢
      intro a
      have hva : ρ (SemidirectProduct.inl a) v = _ := hv a
      change ρ (SemidirectProduct.inl a) ((T : Module.End k V) v) = _
      rw [← Module.End.mul_apply, ← (hT _).eq, Module.End.mul_apply, hva, map_smul]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : signWeightSpace ρR χ)
      fun h => hv0 (congrArg Subtype.val h)).mp hline ⟨_, hTv⟩
    have hcv : (T : Module.End k V) v = c • v := (congrArg Subtype.val hc).symm
    have hker : ∀ g, ∀ w ∈ LinearMap.ker ((T : Module.End k V) - c • 1),
        ρ g w ∈ LinearMap.ker ((T : Module.End k V) - c • 1) := by
      intro g w hw
      rw [LinearMap.mem_ker] at hw ⊢
      rw [LinearMap.sub_apply, ← Module.End.mul_apply, (hT g).eq, Module.End.mul_apply,
        LinearMap.smul_apply, Module.End.one_apply, ← map_smul, ← map_sub]
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hw
      rw [hw, map_zero]
    rcases eq_bot_or_eq_top_of_isIrreducible hρ _ hker with h | h
    · exfalso
      apply hv0
      have hvker : v ∈ LinearMap.ker ((T : Module.End k V) - c • 1) := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          hcv, sub_self]
      rw [h] at hvker
      exact (Submodule.mem_bot k).mp hvker
    · have hTc : (T : Module.End k V) = c • 1 := by
        rw [← sub_eq_zero]
        exact LinearMap.ker_eq_top.mp h
      refine ⟨c, fun hc0 => ?_, hTc⟩
      have h1 : (T : Module.End k V) * ↑T⁻¹ = 1 := T.mul_inv
      rw [hTc, hc0, zero_smul, zero_mul] at h1
      apply hv0
      calc v = (1 : Module.End k V) v := rfl
        _ = 0 := by rw [← h1, LinearMap.zero_apply]
  · rintro ⟨c, -, hc⟩ g
    rw [hc]
    exact (Commute.one_left _).smul_left c

end CFSG.RankThree.GroupTheory
