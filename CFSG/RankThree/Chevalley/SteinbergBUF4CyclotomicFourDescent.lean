module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

section Frobenius

variable {K : Type} [Field K] [Fintype K] {Ω : Type} [Field Ω] [Algebra K Ω]

theorem exists_frob_restrict (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Fintype.card K)
    (K₄ : IntermediateField K Ω) [Finite K₄] :
    ∃ σ : K₄ ≃+* K₄, (∀ b, σ b = b ^ Fintype.card K) ∧
      ∀ b : K₄, F (algebraMap K₄ Ω b) = algebraMap K₄ Ω (σ b) := by
  let σ₀ : K₄ →+* K₄ :=
    { toFun := fun b => ⟨F (b : Ω), by rw [hF]; exact pow_mem b.2 _⟩
      map_one' := Subtype.ext (by
        change F ((1 : K₄) : Ω) = ((1 : K₄) : Ω)
        rw [IntermediateField.coe_one, map_one])
      map_mul' := fun a b => Subtype.ext (by
        change F ((a * b : K₄) : Ω) = F (a : Ω) * F (b : Ω)
        rw [IntermediateField.coe_mul, map_mul])
      map_zero' := Subtype.ext (by
        change F ((0 : K₄) : Ω) = ((0 : K₄) : Ω)
        rw [IntermediateField.coe_zero, map_zero])
      map_add' := fun a b => Subtype.ext (by
        change F ((a + b : K₄) : Ω) = F (a : Ω) + F (b : Ω)
        rw [IntermediateField.coe_add, map_add]) }
  have hσ₀ : ∀ b, σ₀ b = b ^ Fintype.card K := fun b => Subtype.ext (by
    change F (b : Ω) = ((b ^ Fintype.card K : K₄) : Ω)
    rw [hF, IntermediateField.coe_pow])
  have hinj : Function.Injective σ₀ := σ₀.injective
  have hbij : Function.Bijective σ₀ := ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨RingEquiv.ofBijective σ₀ hbij, fun b => hσ₀ b, fun b => ?_⟩
  rfl

end Frobenius

theorem entrywise_baseChangeGL_eq {τ : Tag} {L Ω : Type} [Field L] [Field Ω] (ι : L →+* Ω)
    (F : Ω →+* Ω) (σ : L →+* L) (h : ∀ b, F (ι b) = ι (σ b)) (g : ModGL τ L) :
    Units.map (entrywiseHom F) (baseChangeGL ι g) =
      baseChangeGL ι (Units.map (entrywiseHom σ) g) := by
  have e : F.comp ι = ι.comp σ := RingHom.ext fun b => h b
  rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, e]

theorem subsystemGroup_le_adjointGroup_of_any {τ : Tag} {L : Type} [Field L]
    (J : Set (Fin τ.rank)) : subsystemGroup τ L J ≤ adjointGroup τ L := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]

theorem torusGroup_le_adjointGroup_of_any {τ : Tag} {L : Type} [Field L] :
    torusGroup τ L ≤ adjointGroup τ L :=
  ((triangular_borel_structure.{0, 0} τ L).2.2.2.2.2.2.2.2.2.2.2 L).1 |>.trans' le_sup_left

section Image

variable {L Ω : Type} [Field L] [Field Ω] (ι : L →+* Ω)

theorem exists_of_mem_map_baseChangeGL {X : Subgroup (ModGL Tag.F4 L)} {g : ModGL Tag.F4 Ω}
    (hg : g ∈ X.map (baseChangeGL ι)) : ∃ g₀ ∈ X, baseChangeGL ι g₀ = g := by
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  exact ⟨g₀, hg₀, rfl⟩

theorem inf_centralizer_eq_map_fixed (F : Ω →+* Ω) (σ : L →+* L)
    (hFσ : ∀ b, F (ι b) = ι (σ b)) {Γ₁ : Subgroup (ModGL Tag.F4 Ω)} {m : ModGL Tag.F4 Ω}
    (hΓ₁ : ∀ g, g ∈ Γ₁ ↔ g ∈ (adjointGroup Tag.F4 L).map (baseChangeGL ι) ∧
      m * Units.map (entrywiseHom F) g * m⁻¹ = g)
    {m₀ : ModGL Tag.F4 L} (hm : baseChangeGL ι m₀ = m) {y₀ : ModGL Tag.F4 L}
    {L₀ : Subgroup (ModGL Tag.F4 L)}
    (hL₀ : adjointGroup Tag.F4 L ⊓ Subgroup.centralizer {y₀} = L₀) :
    Γ₁ ⊓ Subgroup.centralizer {baseChangeGL ι y₀} =
      (L₀ ⊓ ((MulAut.conj m₀).toMonoidHom.comp (Units.map (entrywiseHom σ))).eqLocus
        (MonoidHom.id _)).map (baseChangeGL ι) := by
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  ext g
  constructor
  · intro hg
    obtain ⟨hgΓ, hgc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgC, hfix⟩ := (hΓ₁ g).1 hgΓ
    obtain ⟨g₀, hg₀, rfl⟩ := exists_of_mem_map_baseChangeGL ι hgC
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    have hc₀ : g₀ * y₀ = y₀ * g₀ := hinj (by rw [map_mul, map_mul, hgc])
    have hg₀L : g₀ ∈ L₀ := by
      rw [← hL₀]
      exact Subgroup.mem_inf.2 ⟨hg₀, Subgroup.mem_centralizer_singleton_iff.2 hc₀⟩
    refine ⟨g₀, Subgroup.mem_inf.2 ⟨hg₀L, ?_⟩, rfl⟩
    change m₀ * Units.map (entrywiseHom σ) g₀ * m₀⁻¹ = g₀
    apply hinj
    rw [map_mul, map_mul, map_inv, hm, ← entrywise_baseChangeGL_eq ι F σ hFσ]
    exact hfix
  · rintro ⟨g₀, hg₀, rfl⟩
    obtain ⟨hg₀L, hfix⟩ := Subgroup.mem_inf.1 hg₀
    change m₀ * Units.map (entrywiseHom σ) g₀ * m₀⁻¹ = g₀ at hfix
    rw [← hL₀] at hg₀L
    obtain ⟨hg₀C, hg₀c⟩ := Subgroup.mem_inf.1 hg₀L
    rw [Subgroup.mem_centralizer_singleton_iff] at hg₀c
    refine Subgroup.mem_inf.2 ⟨(hΓ₁ _).2 ⟨⟨g₀, hg₀C, rfl⟩, ?_⟩,
      Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hg₀c])⟩
    rw [entrywise_baseChangeGL_eq ι F σ hFσ, ← hm, ← map_mul, ← map_inv, ← map_mul, hfix]

end Image

end CFSG.RankThree.Chevalley
