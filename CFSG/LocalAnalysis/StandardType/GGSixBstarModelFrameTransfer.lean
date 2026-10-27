module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofCore

public section

namespace CFSG.StandardType

section Transfer

variable {G A : Type} [Group G] [Group A] {W V : Type} [Group W] [AddCommGroup V]

theorem GGBstarModelFrame.of_injective_hom {ρ : W →* Equiv.Perm V} {p : ℕ}
    {M Bs : Subgroup G} (hBsM : Bs ≤ M) (Φ : M →* A) (hΦ : Function.Injective Φ)
    (h : GGBstarModelFrame ρ p Φ.range ((Bs.subgroupOf M).map Φ)) :
    GGBstarModelFrame ρ p M Bs := by
  obtain ⟨ι', hι'inj, hι'range, hact⟩ := h
  have hmem : ∀ v, ι' v ∈ Φ.range := fun v => by
    have h1 : ι' v ∈ ι'.range := ⟨v, rfl⟩
    rw [hι'range] at h1
    obtain ⟨b, -, hb⟩ := h1
    exact ⟨b, hb⟩
  set e : M ≃* Φ.range := MonoidHom.ofInjective hΦ with he
  set ι'' : Multiplicative V →* Φ.range := ι'.codRestrict Φ.range hmem with hι''
  set j : Multiplicative V →* M := e.symm.toMonoidHom.comp ι'' with hj
  have hΦj : ∀ v, Φ (j v) = ι' v := fun v => by
    have h1 : e (j v) = ι'' v := by
      simp only [hj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    exact h2
  refine ⟨M.subtype.comp j, ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : j x = j y := Subtype.ext hxy
    exact hι'inj (by rw [← hΦj, ← hΦj, h1])
  · ext g
    constructor
    · rintro ⟨v, rfl⟩
      have h1 : ι' v ∈ ι'.range := ⟨v, rfl⟩
      rw [hι'range] at h1
      obtain ⟨b, hb, hbv⟩ := h1
      have h2 : b = j v := hΦ (by rw [hbv, hΦj])
      have h3 : (b : G) ∈ Bs := hb
      simpa [h2] using h3
    · intro hg
      have h1 : Φ ⟨g, hBsM hg⟩ ∈ (Bs.subgroupOf M).map Φ := ⟨⟨g, hBsM hg⟩, hg, rfl⟩
      rw [← hι'range] at h1
      obtain ⟨v, hv⟩ := h1
      refine ⟨v, ?_⟩
      have h2 : j v = ⟨g, hBsM hg⟩ := hΦ (by rw [hΦj, hv])
      simp [h2]
  · intro g hgM hgN hgp
    set γ : M := ⟨g, hgM⟩ with hγ
    have hγN : ∀ b : M, (b : G) ∈ Bs ↔ (γ * b * γ⁻¹ : M) ∈ Bs.subgroupOf M := fun b => by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp hgN b
    have hnorm : Φ γ ∈ Subgroup.normalizer (((Bs.subgroupOf M).map Φ : Subgroup A) : Set A) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨γ * b * γ⁻¹, (hγN b).mp hb, by simp⟩
      · rintro ⟨b, hb, hbs⟩
        refine ⟨γ⁻¹ * b * γ, ?_, ?_⟩
        · have e : γ * (γ⁻¹ * b * γ) * γ⁻¹ = b := by group
          exact (hγN (γ⁻¹ * b * γ)).mpr (by rw [e]; exact hb)
        · have h1 : Φ γ * s * (Φ γ)⁻¹ = Φ b := hbs.symm
          calc Φ (γ⁻¹ * b * γ) = (Φ γ)⁻¹ * (Φ γ * s * (Φ γ)⁻¹) * Φ γ := by
                rw [h1]; simp
            _ = s := by group
    have hγp : (Φ γ) ^ p = 1 := by
      rw [← map_pow]
      have : γ ^ p = 1 := Subtype.ext (by simpa using hgp)
      rw [this, map_one]
    obtain ⟨w, hw⟩ := hact (Φ γ) ⟨γ, rfl⟩ hnorm hγp
    refine ⟨w, fun v => ?_⟩
    have h1 : γ * j (Multiplicative.ofAdd v) * γ⁻¹ = j (Multiplicative.ofAdd (ρ w v)) :=
      hΦ (by rw [map_mul, map_mul, map_inv, hΦj, hΦj, hw v])
    have h2 := congrArg Subtype.val h1
    simpa using h2

theorem GGBstarModelFrame.of_conj {ρ : W →* Equiv.Perm V} {p : ℕ} {M Bs : Subgroup G} (c : G)
    (h : GGBstarModelFrame ρ p (M.map (MulAut.conj c).toMonoidHom)
      (Bs.map (MulAut.conj c).toMonoidHom)) :
    GGBstarModelFrame ρ p M Bs := by
  obtain ⟨ι', hι'inj, hι'range, hact⟩ := h
  refine ⟨(MulAut.conj c⁻¹).toMonoidHom.comp ι', ?_, ?_, ?_⟩
  · exact (MulAut.conj c⁻¹).injective.comp hι'inj
  · rw [MonoidHom.range_comp, hι'range, Subgroup.map_map]
    have : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id G := MonoidHom.ext fun x => by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  · intro g hgM hgN hgp
    have hcM : c * g * c⁻¹ ∈ M.map (MulAut.conj c).toMonoidHom :=
      ⟨g, hgM, by simp [MulAut.conj_apply]⟩
    have hcN : c * g * c⁻¹ ∈ Subgroup.normalizer
        (((Bs.map (MulAut.conj c).toMonoidHom : Subgroup G)) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN b).mp hb, by
          simp [MulAut.conj_apply, mul_assoc]⟩
      · rintro ⟨b, hb, hbx⟩
        refine ⟨g⁻¹ * b * g, ?_, ?_⟩
        · have e : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
          exact (Subgroup.mem_normalizer_iff.mp hgN (g⁻¹ * b * g)).mpr (by rw [e]; exact hb)
        · have h1 : c * g * c⁻¹ * x * (c * g * c⁻¹)⁻¹ = c * b * c⁻¹ := by
            rw [← hbx]; simp [MulAut.conj_apply, mul_assoc]
          calc (MulAut.conj c).toMonoidHom (g⁻¹ * b * g)
              = (c * g * c⁻¹)⁻¹ * (c * b * c⁻¹) * (c * g * c⁻¹) := by
                simp [MulAut.conj_apply]; group
            _ = (c * g * c⁻¹)⁻¹ * (c * g * c⁻¹ * x * (c * g * c⁻¹)⁻¹) * (c * g * c⁻¹) := by
                rw [h1]
            _ = x := by group
    have hcp : (c * g * c⁻¹) ^ p = 1 := by
      rw [conj_pow, hgp]; simp
    obtain ⟨w, hw⟩ := hact (c * g * c⁻¹) hcM hcN hcp
    refine ⟨w, fun v => ?_⟩
    have h1 := congrArg (MulAut.conj c⁻¹).toMonoidHom (hw v)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1 ⊢
    calc g * (c⁻¹ * ι' (Multiplicative.ofAdd v) * c⁻¹⁻¹) * g⁻¹
        = c⁻¹ * ((c * g * c⁻¹) * ι' (Multiplicative.ofAdd v) * (c * g * c⁻¹)⁻¹) * c⁻¹⁻¹ := by
          group
      _ = _ := h1

end Transfer

end CFSG.StandardType
