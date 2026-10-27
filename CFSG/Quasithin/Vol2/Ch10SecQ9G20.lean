module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G19
public import CFSG.Quasithin.Vol2.Ch10SecB3Five5
public import CFSG.Quasithin.Vol2.Ch10SecQ9G18

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] {L W : Subgroup G} {s : G}

@[expose] def conjL (hs : s ∈ Subgroup.normalizer (L : Set G)) : ↥L →* ↥L where
  toFun l := ⟨s * l * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs l).mp l.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp only [Subgroup.coe_mul]; group

theorem conjL_coe (hs : s ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    ((conjL hs l : ↥L) : G) = s * l * s⁻¹ := rfl

theorem conjL_surjective (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    Function.Surjective (conjL hs) := by
  intro l
  have h1 : s⁻¹ * l * s ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) l).mp l.2
    simpa using this
  exact ⟨⟨_, h1⟩, Subtype.ext (by rw [conjL_coe]; group)⟩

omit [Group G] in
theorem mem_centralizer_conj_iff {G : Type} [Group G] {W : Subgroup G} {s x : G} :
    s * x * s⁻¹ ∈ Subgroup.centralizer (W : Set G) ↔
      x ∈ Subgroup.centralizer (CFSG.conjugate W s : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, SecA.mem_conjugate_iff]
  constructor
  · intro h y hy
    have := h _ hy
    have e : s * (y * x) * s⁻¹ = s * (x * y) * s⁻¹ := by
      calc s * (y * x) * s⁻¹ = s * y * s⁻¹ * (s * x * s⁻¹) := by group
        _ = s * x * s⁻¹ * (s * y * s⁻¹) := this
        _ = s * (x * y) * s⁻¹ := by group
    simpa using e
  · intro h a ha
    have hy : s * (s⁻¹ * a * s) * s⁻¹ ∈ W := by
      rw [show s * (s⁻¹ * a * s) * s⁻¹ = a by group]; exact ha
    have := h _ hy
    calc a * (s * x * s⁻¹) = s * ((s⁻¹ * a * s) * x) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * a * s)) * s⁻¹ := by rw [this]
      _ = s * x * s⁻¹ * a := by group

@[expose] def NatData.conj (D : NatData L W) (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    NatData L (CFSG.conjugate W s) where
  ρ := D.ρ.comp (conjL hs)
  b x := D.b (s * x * s⁻¹)
  ρ_surj := D.ρ_surj.comp (conjL_surjective hs)
  ker_ρ l := by
    rw [MonoidHom.comp_apply, D.ker_ρ, conjL_coe]
    exact mem_centralizer_conj_iff
  b_mul a₁ h₁ a₂ h₂ := by
    rw [SecA.mem_conjugate_iff] at h₁ h₂
    rw [show s * (a₁ * a₂) * s⁻¹ = s * a₁ * s⁻¹ * (s * a₂ * s⁻¹) by group]
    exact D.b_mul _ h₁ _ h₂
  b_inj a₁ h₁ a₂ h₂ h := by
    rw [SecA.mem_conjugate_iff] at h₁ h₂
    have := D.b_inj _ h₁ _ h₂ h
    simpa using this
  b_surj x := by
    obtain ⟨a, ha, hax⟩ := D.b_surj x
    refine ⟨s⁻¹ * a * s, ?_, ?_⟩
    · rw [SecA.mem_conjugate_iff, show s * (s⁻¹ * a * s) * s⁻¹ = a by group]
      exact ha
    · show D.b (s * (s⁻¹ * a * s) * s⁻¹) = x
      rw [show s * (s⁻¹ * a * s) * s⁻¹ = a by group]
      exact hax
  equi l a ha := by
    rw [SecA.mem_conjugate_iff] at ha
    have h1 := D.equi (conjL hs l) _ ha
    rw [conjL_coe] at h1
    rw [MonoidHom.comp_apply, ← h1]
    congr 1
    group

theorem exists_twist {W' : Subgroup G} (D : NatData L W) (D' : NatData L W')
    (hker : ∀ l : ↥L, D.ρ l = 1 ↔ D'.ρ l = 1) :
    (∃ g : L3.Γ, ∀ l, D'.ρ l = g * D.ρ l * g⁻¹) ∨
      (∃ g : L3.Γ, ∀ l, D'.ρ l = g * τ3 (D.ρ l) * g⁻¹) := by
  have hkk : D.ρ.ker = D'.ρ.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact hker l
  set e1 := QuotientGroup.quotientKerEquivOfSurjective D.ρ D.ρ_surj
  set e2 := QuotientGroup.quotientKerEquivOfSurjective D'.ρ D'.ρ_surj
  set α : MulAut L3.Γ := e1.symm.trans ((QuotientGroup.quotientMulEquivOfEq hkk).trans e2) with hα
  have hαρ : ∀ l, α (D.ρ l) = D'.ρ l := by
    intro l
    have h1 : e1.symm (D.ρ l) = (l : ↥L ⧸ D.ρ.ker) :=
      e1.symm_apply_eq.mpr rfl
    rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    rfl
  rcases SecB.L32.aut_cases α with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact Or.inl ⟨g, fun l => by rw [← hαρ, hg, MulAut.conj_apply]⟩
  · exact Or.inr ⟨g, fun l => by rw [← hαρ, hg, MulAut.mul_apply, MulAut.conj_apply]⟩

theorem isXSectionIso_of_twist_inner [Finite G] (D : NatData L W)
    (hs : s ∈ Subgroup.normalizer (L : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hkerO : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (W : Set G) → (l : G) ∈ pCoreOf 2 L)
    {g : L3.Γ} (hg : ∀ l, (D.conj hs).ρ l = g * D.ρ l * g⁻¹) :
    IsXSectionIso L ⊥ W (CFSG.conjugate W s) := by
  obtain ⟨x₀, hx₀⟩ := D.ρ_surj g
  refine SecB.isXSectionIso_of_inner x₀.2 hLW hO fun x hx => ?_
  have h1 : D.ρ (conjL hs ⟨x, hx⟩ * (x₀ * ⟨x, hx⟩ * x₀⁻¹)⁻¹) = 1 := by
    have h2 := hg ⟨x, hx⟩
    simp only [NatData.conj, MonoidHom.comp_apply] at h2
    rw [map_mul, map_inv, h2, map_mul, map_mul, map_inv, hx₀]
    group
  have h3 := hkerO _ ((D.ker_ρ _).mp h1)
  simpa [conjL_coe] using h3

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
