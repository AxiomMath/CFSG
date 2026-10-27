module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem ggRawFieldConj_adjoint {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hinner : InnerFieldTrivial τ K) :
    GGRawFieldConj p (LargeEvenCenterQuot (adjointGroup τ K))
      (markIDImage (IsRoot τ) K (adjointGroup τ K))
      (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) := by
  intro _ _ u hu f hfF huf hpow
  obtain ⟨w, hw⟩ := exists_inndiagConj_of_mem_markID hu
  obtain ⟨σ, hσ⟩ := exists_eq_entrywise_of_mem_closure_markField hfF
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply huf
    have hf1 : f = 1 :=
      (autEquiv τ K).injective (by rw [hσ, map_one, entrywiseAdjointAut_one])
    rw [hf1, mul_one]
    exact hu
  set X := MulAut.conj w * inndiagFieldAut τ K σ with hXdef
  have hX1 : ∀ h : adjointGroup τ K, (X ⟨h, adjointGroup_le_inndiagGroup h.2⟩ : ModGL τ K) =
      (autEquiv τ K (u * f) h : ModGL τ K) := by
    intro h
    have e1 : autEquiv τ K (u * f) = inndiagConj τ K w * entrywiseAdjointAut τ σ := by
      rw [map_mul, hw, hσ]
    rw [e1]
    rfl
  have hXk : ∀ (k : ℕ) (h : adjointGroup τ K),
      ((X ^ k) ⟨h, adjointGroup_le_inndiagGroup h.2⟩ : ModGL τ K) =
        ((autEquiv τ K (u * f) ^ k) h : ModGL τ K) := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply]
      have e1 : (X ^ k) ⟨h, adjointGroup_le_inndiagGroup h.2⟩ =
          ⟨((autEquiv τ K (u * f) ^ k) h : ModGL τ K),
            adjointGroup_le_inndiagGroup ((autEquiv τ K (u * f) ^ k) h).2⟩ :=
        Subtype.ext (ih h)
      rw [e1]
      exact hX1 _
  have hXp : ∀ (h : ModGL τ K) (hh : h ∈ adjointGroup τ K),
      (((X ^ p) ⟨h, adjointGroup_le_inndiagGroup hh⟩ : inndiagGroup τ K) : ModGL τ K) = h := by
    intro h hh
    rw [hXk p ⟨h, hh⟩, ← map_pow, hpow, map_one, MulAut.one_apply]
  obtain ⟨hord, g, hg⟩ := exists_inndiag_conj_of_pow_fix hf hK hp hinner σ hσ1 w hXp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨(autEquiv τ K).symm (entrywiseAdjointAut τ σ), markField_of_entrywise σ,
    (autEquiv τ K).symm (inndiagConj τ K g⁻¹), inndiagConj_mem_markID g⁻¹, ?_, ?_⟩
  ·
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ fun h1 => hσ1 (hinner σ 1 (one_mem _) fun h hh => ?_)
    · rw [← entrywiseAdjointAut_pow, ← hord, pow_orderOf_eq_one, entrywiseAdjointAut_one]
    · have e1 := coe_entrywiseAdjointAut τ σ ⟨h, hh⟩
      rw [h1, MulAut.one_apply] at e1
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
  ·
    have hX' : MulAut.conj w * inndiagFieldAut τ K σ =
        MulAut.conj g⁻¹ * inndiagFieldAut τ K σ * MulAut.conj g := by
      rw [map_inv]
      have e0 : MulAut.conj w * inndiagFieldAut τ K σ = (MulAut.conj g)⁻¹ * (MulAut.conj g *
          (MulAut.conj w * inndiagFieldAut τ K σ) * (MulAut.conj g)⁻¹) * MulAut.conj g := by group
      rw [e0, hg]
    have key : ∀ h : adjointGroup τ K, (w : ModGL τ K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (w : ModGL τ K)⁻¹ =
          (g : ModGL τ K)⁻¹ * Units.map (entrywiseHom σ.toRingHom)
            ((g : ModGL τ K) * (h : ModGL τ K) * (g : ModGL τ K)⁻¹) * (g : ModGL τ K) := by
      intro h
      have e2 := congrArg (fun φ : MulAut (inndiagGroup τ K) =>
        ((φ ⟨h, adjointGroup_le_inndiagGroup h.2⟩ : inndiagGroup τ K) : ModGL τ K)) hX'
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_inndiagFieldAut, inv_inv] at e2
      exact e2
    apply (autEquiv τ K).injective
    have hR : autEquiv τ K ((autEquiv τ K).symm (inndiagConj τ K g⁻¹) *
        (autEquiv τ K).symm (entrywiseAdjointAut τ σ) *
          ((autEquiv τ K).symm (inndiagConj τ K g⁻¹))⁻¹) =
        (inndiagConj τ K g)⁻¹ * entrywiseAdjointAut τ σ * inndiagConj τ K g := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
    rw [hR, map_mul, hw, hσ, ← map_inv]
    refine MulEquiv.ext fun h => Subtype.ext ?_
    simp only [MulAut.mul_apply, coe_inndiagConj, coe_entrywiseAdjointAut, Subgroup.coe_inv,
      inv_inv]
    exact key h

theorem chevConjOn_isRoot {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hinner : InnerFieldTrivial τ K) :
    ChevConjOn K τ (IsRoot τ) p := by
  unfold ChevConjOn
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K), H = adjointGroup τ K →
      GGRawFieldConj p (LargeEvenCenterQuot H) (markIDImage (IsRoot τ) K H)
        (RecipeFieldExcInn.markFieldImage (IsRoot τ) K H) from
    key _ (chevH_false_eq_adjointGroup K τ)
  intro H hH
  subst hH
  exact ggRawFieldConj_adjoint hf hK hp hinner

theorem ggRawFieldConj_chev {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hinner : InnerFieldTrivial τ K) :
    GGRawFieldConj p (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K _) (LargeEvenChevFieldImage τ.cartan K _) := by
  have h := (chevConjOn_isRoot hf hK hp hinner).of_eq (largeEvenIsRoot_eq_isRoot τ).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      GGRawFieldConj p (LargeEvenCenterQuot H) (LargeEvenChevIDImage τ.cartan K H)
        (LargeEvenChevFieldImage τ.cartan K H) from
    key _ (largeEvenChevH_eq τ.cartan K false)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h

theorem ggRawFieldConj_chev_two {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hp : p.Prime)
    (hinner : InnerFieldTrivial τ K) :
    GGRawFieldConj p (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K _) (LargeEvenChevFieldImage τ.cartan K _) := by
  have : CharP K 2 := charP_two_of_card hK
  exact ggRawFieldConj_chev (ℓ := 2) hn hK hp hinner

end RecipeExcLang

open RecipeExcLang

@[expose] def GGRecipeChevConjLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8

theorem ggRawFieldConjOn_chev :
    GGRawFieldConjOn fun _ lab => GGRecipeChevConjLabel lab := by
  intro p hp _ lab hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  rcases hS with ht | ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  · obtain ⟨-, hn2⟩ := hl
    exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldConj_chev_two hn hK hp (innerFieldTrivial_G2 hn2 hK)) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldConj_chev_two hn hK hp (innerFieldTrivial_F4 hn hK)) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldConj_chev_two (τ := TwistTag.E6.tag) hn hK hp innerFieldTrivial_E6) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldConj_chev_two hn hK hp (innerFieldTrivial_E7_E8 hn hK (Or.inl rfl))) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldConj_chev_two hn hK hp (innerFieldTrivial_E7_E8 hn hK (Or.inr rfl))) hQ

end CFSG.StandardType
