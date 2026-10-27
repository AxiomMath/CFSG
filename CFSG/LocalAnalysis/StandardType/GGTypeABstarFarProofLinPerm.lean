module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLin

public section

namespace CFSG.StandardType

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section PermRefl

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {α : Type*} [DecidableEq α] [Fintype α]

theorem linRefl_stab_fix (hp2 : p ≠ 2) (T : Equiv.Perm α →* (V ≃ₗ[ZMod p] V))
    (hinj : Function.Injective T) (hsw : ∀ x y, x ≠ y → IsLinRefl (T (Equiv.swap x y)))
    {a b : α} (hab : a ≠ b) {v : V} (hv : T (Equiv.swap a b) v = -v) :
    ∀ σ : Equiv.Perm α, σ a = a → σ b = b → T σ v = v := by
  intro σ
  suffices H : ∀ n : ℕ, ∀ σ : Equiv.Perm α, σ.support.card = n →
      σ a = a → σ b = b → T σ v = v by
    exact H σ.support.card σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hcard ha hb
    by_cases hσ : σ = 1
    · rw [hσ]
      simp
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
        by_contra h
        push Not at h
        exact hσ (Equiv.ext h)
      set y : α := σ x with hy
      have hxy : x ≠ y := by
        rw [hy]
        exact Ne.symm hx
      have hxa : x ≠ a := by
        intro h
        exact hx (by rw [hy, h, ha])
      have hxb : x ≠ b := by
        intro h
        exact hx (by rw [hy, h, hb])
      have hya : y ≠ a := by
        intro h
        apply hxa
        rw [hy] at h
        exact σ.injective (by rw [h, ha])
      have hyb : y ≠ b := by
        intro h
        apply hxb
        rw [hy] at h
        exact σ.injective (by rw [h, hb])
      set τ : Equiv.Perm α := Equiv.swap x y with hτ
      set σ' : Equiv.Perm α := τ * σ with hσ'
      have hσ'a : σ' a = a := by
        rw [hσ', hτ]
        simp [ha, Equiv.swap_apply_of_ne_of_ne hxa.symm hya.symm]
      have hσ'b : σ' b = b := by
        rw [hσ', hτ]
        simp [hb, Equiv.swap_apply_of_ne_of_ne hxb.symm hyb.symm]
      have hlt : σ'.support.card < n := by
        rw [← hcard]
        have hσ'_eq : σ' = Equiv.swap x (σ x) * σ := by
          rw [hσ', hτ, hy]
        rw [hσ'_eq]
        exact Equiv.Perm.card_support_swap_mul hx
      have hind : T σ' v = v := ih σ'.support.card hlt σ' rfl hσ'a hσ'b
      have hnodup : [x, y, a, b].Nodup := by
        simp [List.nodup_cons, hxy, hxa, hxb, hya, hyb, hab]
      have hdisj : Equiv.Perm.Disjoint (Equiv.swap x y) (Equiv.swap a b) :=
        Equiv.Perm.disjoint_swap_swap hnodup
      have hcomm : T (Equiv.swap x y) * T (Equiv.swap a b) =
          T (Equiv.swap a b) * T (Equiv.swap x y) := by
        rw [← map_mul, ← map_mul, hdisj.commute.eq]
      have hneτ : T (Equiv.swap a b) ≠ T (Equiv.swap x y) := by
        intro heq
        have hEq : Equiv.swap a b = Equiv.swap x y := hinj heq
        have hkey : Equiv.swap a b a = Equiv.swap x y a := by rw [hEq]
        rw [Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hxa.symm hya.symm] at hkey
        exact hab hkey.symm
      have hτv : T (Equiv.swap x y) v = v :=
        IsLinRefl.comm_fix hp2 (hsw a b hab) (hsw x y hxy) hcomm.symm hneτ hv
      have hστ : σ = τ * σ' := by
        rw [hσ', hτ, Equiv.swap_mul_self_mul]
      calc T σ v = T (τ * σ') v := by rw [hστ]
        _ = (T τ * T σ') v := by rw [map_mul]
        _ = T τ (T σ' v) := by rw [LinearEquiv.mul_apply]
        _ = T τ v := by rw [hind]
        _ = v := hτv

theorem isSwap_of_isLinRefl (hp2 : p ≠ 2) (T : Equiv.Perm α →* (V ≃ₗ[ZMod p] V))
    (hinj : Function.Injective T) (hsw : ∀ x y, x ≠ y → IsLinRefl (T (Equiv.swap x y)))
    {π : Equiv.Perm α} (h : IsLinRefl (T π)) : π.IsSwap := by
  by_contra hns
  have hsq : π * π = 1 := by
    apply hinj
    rw [map_mul, map_one]
    ext w
    simpa using IsLinRefl.apply_apply h w
  have hsq_apply : ∀ w, π (π w) = w := by
    intro w
    have h2 : (π * π) w = w := by rw [hsq]; rfl
    simpa using h2
  have hπ1 : π ≠ 1 := by
    intro h1
    exact IsLinRefl.ne_one hp2 h (by rw [h1, map_one])
  obtain ⟨a, ha⟩ : ∃ a, π a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hπ1 (Equiv.ext hcon)
  set b : α := π a with hb
  have hπb : π b = a := by
    simpa [hb] using hsq_apply a
  have hab : a ≠ b := by
    intro h'
    exact ha h'.symm
  have hne_sw : π ≠ Equiv.swap a b := by
    intro hEq
    exact hns ⟨a, b, hab, hEq⟩
  obtain ⟨c, hc⟩ : ∃ c, π c ≠ Equiv.swap a b c := by
    by_contra hcon
    push Not at hcon
    exact hne_sw (Equiv.ext hcon)
  have hca : c ≠ a := by
    rintro rfl
    exact hc (by rw [← hb, Equiv.swap_apply_left])
  have hcb : c ≠ b := by
    rintro rfl
    exact hc (by rw [hπb, Equiv.swap_apply_right])
  have hswapc : Equiv.swap a b c = c := Equiv.swap_apply_of_ne_of_ne hca hcb
  have hπc : π c ≠ c := by
    rw [hswapc] at hc
    exact hc
  set d : α := π c with hd
  have hdc : d ≠ c := by
    rw [hd]
    exact hπc
  have hπd : π d = c := by
    simpa [hd] using hsq_apply c
  have hda : d ≠ a := by
    intro h'
    apply hcb
    rw [← hπd, h', hb]
  have hdb : d ≠ b := by
    intro h'
    apply hca
    rw [← hπd, h', hπb]
  have hcd : c ≠ d := hdc.symm
  obtain ⟨v₁, hv₁ne, hv₁⟩ := IsLinRefl.exists_anti hp2 (hsw a b hab)
  have hρa : (Equiv.swap a b * π) a = a := by
    show Equiv.swap a b (π a) = a
    rw [← hb, Equiv.swap_apply_right]
  have hρb : (Equiv.swap a b * π) b = b := by
    show Equiv.swap a b (π b) = b
    rw [hπb, Equiv.swap_apply_left]
  have hρv₁ : T (Equiv.swap a b * π) v₁ = v₁ :=
    linRefl_stab_fix hp2 T hinj hsw hab hv₁ (Equiv.swap a b * π) hρa hρb
  have hTπv₁ : T π v₁ = -v₁ := by
    rw [show π = Equiv.swap a b * (Equiv.swap a b * π) from
      (Equiv.swap_mul_self_mul a b π).symm, map_mul]
    rw [LinearEquiv.mul_apply, hρv₁, hv₁]
  obtain ⟨v₂, hv₂ne, hv₂⟩ := IsLinRefl.exists_anti hp2 (hsw c d hcd)
  have hρ'a : (Equiv.swap c d * π) c = c := by
    show Equiv.swap c d (π c) = c
    rw [← hd, Equiv.swap_apply_right]
  have hρ'b : (Equiv.swap c d * π) d = d := by
    show Equiv.swap c d (π d) = d
    rw [hπd, Equiv.swap_apply_left]
  have hρ'v₂ : T (Equiv.swap c d * π) v₂ = v₂ :=
    linRefl_stab_fix hp2 T hinj hsw hcd hv₂ (Equiv.swap c d * π) hρ'a hρ'b
  have hTπv₂ : T π v₂ = -v₂ := by
    rw [show π = Equiv.swap c d * (Equiv.swap c d * π) from
      (Equiv.swap_mul_self_mul c d π).symm, map_mul]
    rw [LinearEquiv.mul_apply, hρ'v₂, hv₂]
  obtain ⟨s, hs⟩ := IsLinRefl.anti_eq_smul hp2 h hv₁ne hTπv₁ hTπv₂
  have hsne : s ≠ 0 := by
    intro h0
    apply hv₂ne
    rw [hs, h0, zero_smul]
  have hs' : v₁ = s⁻¹ • v₂ := by
    rw [hs, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  have hTcdv₁ : T (Equiv.swap c d) v₁ = -v₁ := by
    calc T (Equiv.swap c d) v₁ = T (Equiv.swap c d) (s⁻¹ • v₂) := by rw [hs']
      _ = s⁻¹ • T (Equiv.swap c d) v₂ := by rw [LinearEquiv.map_smul]
      _ = s⁻¹ • (-v₂) := by rw [hv₂]
      _ = -(s⁻¹ • v₂) := by rw [smul_neg]
      _ = -v₁ := by rw [← hs']
  have hnodup : [a, b, c, d].Nodup := by
    simp [List.nodup_cons, hab, hca, hcb, hda, hdb, hcd,
      hca.symm, hda.symm, hcb.symm, hdb.symm]
  have hdisj : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) :=
    Equiv.Perm.disjoint_swap_swap hnodup
  have hcomm : T (Equiv.swap a b) * T (Equiv.swap c d) =
      T (Equiv.swap c d) * T (Equiv.swap a b) := by
    rw [← map_mul, ← map_mul, hdisj.commute.eq]
  have hnew : T (Equiv.swap a b) ≠ T (Equiv.swap c d) := by
    intro heq
    have hEq : Equiv.swap a b = Equiv.swap c d := hinj heq
    have hkey : Equiv.swap a b a = Equiv.swap c d a := by rw [hEq]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca.symm hda.symm] at hkey
    exact hab hkey.symm
  have hfix : T (Equiv.swap c d) v₁ = v₁ :=
    IsLinRefl.comm_fix hp2 (hsw a b hab) (hsw c d hcd) hcomm hnew hv₁
  have hneg : -v₁ = v₁ := by
    rw [← hTcdv₁, hfix]
  have hsum : v₁ + v₁ = 0 := (neg_eq_iff_add_eq_zero).mp hneg
  have htwo : (2 : ZMod p) • v₁ = 0 := by
    rw [two_smul]
    exact hsum
  exact hv₁ne ((smul_eq_zero.mp htwo).resolve_left (zmod_two_ne_zero hp2))

end PermRefl

end CFSG.StandardType
