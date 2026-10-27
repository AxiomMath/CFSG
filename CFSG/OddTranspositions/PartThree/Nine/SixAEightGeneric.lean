module

public import CFSG.GH74.Uniqueness.SU.SU5A8

public section

namespace CFSG.OddTranspositions.PartThree.Nine

theorem isA8Type_sup_of_complement {X : Type*} [Group X] [Finite X] {U D₀ : Subgroup X}
    (hU2 : ∀ x ∈ U, x * x = 1) (hUcard : Nat.card U = 8) (hDcard : Nat.card D₀ = 8)
    (hDU : D₀ ≤ Subgroup.normalizer (U : Set X)) (hint : U ⊓ D₀ = ⊥)
    (hfaith : ∀ d ∈ D₀, (∀ x ∈ U, d * x * d⁻¹ = x) → d = 1)
    (hsign : ∀ d ∈ D₀, ∀ σ : Equiv.Perm U, (∀ x : U, (σ x : X) = d * x * d⁻¹) →
      ∀ ι : U ≃ Fin 8, Equiv.Perm.sign (ι.permCongr σ) = 1) :
    CFSG.GH74.Uniqueness.SU.SU5.IsA8Type ↥(U ⊔ D₀) := by
  classical
  have hUP : U ≤ U ⊔ D₀ := le_sup_left
  have hDP : D₀ ≤ U ⊔ D₀ := le_sup_right
  have hdecomp : ∀ g : ↥(U ⊔ D₀), ∃ u ∈ U, ∃ d ∈ D₀, (g : X) = u * d := by
    intro g
    have hg : (g : X) ∈ ((U ⊔ D₀ : Subgroup X) : Set X) := g.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U D₀ hDU] at hg
    obtain ⟨u, hu, d, hd, h⟩ := hg
    exact ⟨u, hu, d, hd, h.symm⟩
  have hUD1 : ∀ {x : X}, x ∈ U → x ∈ D₀ → x = 1 := by
    intro x hxU hxD
    have hx : x ∈ U ⊓ D₀ := ⟨hxU, hxD⟩
    rwa [hint, Subgroup.mem_bot] at hx
  set D' : Subgroup ↥(U ⊔ D₀) := D₀.subgroupOf (U ⊔ D₀) with hD'
  let β : ↥U → ↥(U ⊔ D₀) ⧸ D' := fun x => ((⟨x, hUP x.2⟩ : ↥(U ⊔ D₀)) : ↥(U ⊔ D₀) ⧸ D')
  have hβinj : Function.Injective β := by
    intro x y hxy
    have h : (x : X)⁻¹ * y ∈ D₀ := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hxy)
    exact Subtype.ext (inv_mul_eq_one.mp (hUD1 (U.mul_mem (U.inv_mem x.2) y.2) h))
  have hβsurj : Function.Surjective β := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨u, hu, d, hd, hg⟩ := hdecomp g
      refine ⟨⟨u, hu⟩, QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)⟩
      simpa [hg] using hd
  let βe : ↥U ≃ ↥(U ⊔ D₀) ⧸ D' := Equiv.ofBijective β ⟨hβinj, hβsurj⟩
  let ι : ↥U ≃ Fin 8 := Finite.equivFinOfCardEq hUcard
  let ι' : ↥(U ⊔ D₀) ⧸ D' ≃ Fin 8 := βe.symm.trans ι
  let ρ : ↥(U ⊔ D₀) →* Equiv.Perm (Fin 8) :=
    ι'.permCongrHom.toMonoidHom.comp (MulAction.toPermHom ↥(U ⊔ D₀) (↥(U ⊔ D₀) ⧸ D'))
  have hρ : ∀ g c, ρ g c = ι' (g • ι'.symm c) := fun g c => rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfix : ∀ c : ↥(U ⊔ D₀) ⧸ D', g • c = c := by
      intro c
      have h := congrArg (fun σ : Equiv.Perm (Fin 8) => σ (ι' c)) hg
      simp only [hρ, Equiv.Perm.one_apply, Equiv.symm_apply_apply] at h
      exact ι'.injective h
    have hgD : (g : X) ∈ D₀ := by
      have h := hfix ((1 : ↥(U ⊔ D₀)) : ↥(U ⊔ D₀) ⧸ D')
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h
      simpa using D₀.inv_mem (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h))
    have hcent : ∀ x ∈ U, (g : X) * x * (g : X)⁻¹ = x := by
      intro x hx
      have h := hfix ((⟨x, hUP hx⟩ : ↥(U ⊔ D₀)) : ↥(U ⊔ D₀) ⧸ D')
      rw [MulAction.Quotient.smul_mk] at h
      have h1 : ((g : X) * x)⁻¹ * x ∈ D₀ := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
      have h2 : x⁻¹ * ((g : X)⁻¹ * x * g) ∈ D₀ := by
        simpa [mul_assoc] using D₀.mul_mem h1 hgD
      have h3 : x⁻¹ * ((g : X)⁻¹ * x * g) ∈ U := by
        refine U.mul_mem (U.inv_mem hx) ?_
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDU hgD)) x).mp hx
      have h5 : (g : X)⁻¹ * x * g = x := by
        simpa [mul_assoc] using congrArg (fun y => x * y) (hUD1 h3 h2)
      calc (g : X) * x * (g : X)⁻¹ = (g : X) * ((g : X)⁻¹ * x * g) * (g : X)⁻¹ := by rw [h5]
        _ = x := by group
    exact Subtype.ext (hfaith g hgD hcent)
  have hsignU : ∀ x (hx : x ∈ U), Equiv.Perm.sign (ρ ⟨x, hUP hx⟩) = 1 := by
    intro x hx
    by_cases hx1 : x = 1
    · subst hx1
      rw [show (⟨1, hUP hx⟩ : ↥(U ⊔ D₀)) = 1 from rfl, map_one, map_one]
    have hσ2 : ρ ⟨x, hUP hx⟩ ^ 2 = 1 := by
      rw [pow_two, ← map_mul,
        show (⟨x, hUP hx⟩ : ↥(U ⊔ D₀)) * ⟨x, hUP hx⟩ = 1 from Subtype.ext (hU2 x hx), map_one]
    have hfp : Fintype.card (Function.fixedPoints (ρ ⟨x, hUP hx⟩)) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨c, hc⟩ => hx1 ?_⟩
      have hc' : ρ ⟨x, hUP hx⟩ c = c := hc
      rw [hρ] at hc'
      have h := ι'.injective (hc'.trans (ι'.apply_symm_apply c).symm)
      set y := ι.symm c with hy
      rw [show ι'.symm c = β y from rfl, MulAction.Quotient.smul_mk] at h
      have h1 : ((x : X) * y)⁻¹ * y ∈ D₀ := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
      have h3 := hUD1 (U.mul_mem (U.inv_mem (U.mul_mem hx y.2)) y.2) h1
      have h4 : (y : X)⁻¹ * x⁻¹ * y = 1 := by simpa [mul_assoc] using h3
      have h5 : x⁻¹ = 1 := by
        simpa [mul_assoc] using congrArg (fun z => (y : X) * z * (y : X)⁻¹) h4
      exact inv_eq_one.mp h5
    rw [Equiv.Perm.sign_of_pow_two_eq_one hσ2, hfp]
    decide
  have hsignD : ∀ d (hd : d ∈ D₀), Equiv.Perm.sign (ρ ⟨d, hDP hd⟩) = 1 := by
    intro d hd
    let σ : Equiv.Perm ↥U :=
      { toFun := fun x => ⟨d * x * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDU hd) x).mp x.2⟩
        invFun := fun x => ⟨d⁻¹ * x * d, by
          simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDU hd)) x).mp x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
    have hσ : ∀ x : ↥U, (σ x : X) = d * x * d⁻¹ := fun x => rfl
    have heq : ρ ⟨d, hDP hd⟩ = ι.permCongr σ := by
      refine Equiv.ext fun c => ?_
      show ι (βe.symm ((⟨d, hDP hd⟩ : ↥(U ⊔ D₀)) • β (ι.symm c))) = ι (σ (ι.symm c))
      congr 1
      apply βe.injective
      rw [Equiv.apply_symm_apply]
      show (⟨d, hDP hd⟩ : ↥(U ⊔ D₀)) • β (ι.symm c) = β (σ (ι.symm c))
      rw [MulAction.Quotient.smul_mk]
      refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
      simpa [hσ, mul_assoc] using D₀.inv_mem hd
    rw [heq]
    exact hsign d hd σ hσ ι
  have hsignρ : ∀ g, Equiv.Perm.sign (ρ g) = 1 := by
    intro g
    obtain ⟨u, hu, d, hd, hg⟩ := hdecomp g
    rw [show g = ⟨u, hUP hu⟩ * ⟨d, hDP hd⟩ from Subtype.ext hg, map_mul, map_mul, hsignU u hu,
      hsignD d hd, mul_one]
  have hcard : Nat.card ↥(U ⊔ D₀) = 64 := by
    have h1 := D'.card_mul_index
    have h2 : Nat.card D' = 8 := by
      rw [← hDcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv
    have h3 : D'.index = 8 := by
      rw [Subgroup.index, ← hUcard]
      exact (Nat.card_congr βe).symm
    rw [h2, h3] at h1
    omega
  have hle : ρ.range ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨g, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr (hsignρ g)
  have hcardA : Nat.card (ρ.range.subgroupOf (alternatingGroup (Fin 8))) =
      2 ^ (Nat.card (alternatingGroup (Fin 8))).factorization 2 := by
    rw [CFSG.GH74.Uniqueness.SU.SU5.J2Syl.card_A8_factorization,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv, hcard]
    norm_num
  exact ⟨Sylow.ofCard _ hcardA,
    ⟨(MonoidHom.ofInjective hρinj).trans (Subgroup.subgroupOfEquivOfLe hle).symm⟩⟩

end CFSG.OddTranspositions.PartThree.Nine
