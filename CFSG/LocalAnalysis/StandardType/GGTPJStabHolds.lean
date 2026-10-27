module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGTPStabRefl
public import CFSG.LocalAnalysis.StandardType.GGTPReflInE6
public import CFSG.LocalAnalysis.StandardType.GGTPReflInTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_stab_of_refl
    {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hF : KGL.KGAutFrame A κ)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) {c : ↥A}
    (hκc : Multiplicative.toAdd (κ c) = KGL.kgExpVec β) {J : Subgroup L'}
    (hrefl : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → iform γ β = 0 →
      ∃ m ∈ J, MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
        ∀ a b : ↥A, (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
          Multiplicative.toAdd (κ b) = KGL.rootRefl γ (Multiplicative.toAdd (κ a))) :
    ∀ φ ∈ ggTorusAut A, φ c = c →
      φ ∈ ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A := by
  intro φ hφ hφc
  refine (Subgroup.closure_le (ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A)).2 ?_
    (ggTPStab_le_closure_refl hF hβ hκc φ hφ hφc)
  rintro ψ' ⟨γ, hγ, hγβ, hact⟩
  obtain ⟨m, hmJ, hmN, hm⟩ := hrefl γ hγ hγβ
  refine Subgroup.subset_closure ⟨MulAut.conj m, Subgroup.mem_map.2 ⟨m, hmJ, rfl⟩, hmN, ?_⟩
  intro a
  have hb : MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.1 hmN a).1 a.2
  have h1 := hm a ⟨_, hb⟩ rfl
  have h2 : ψ' a = ⟨_, hb⟩ := hF.injective (by
    apply Multiplicative.toAdd.injective
    rw [hact a, h1])
  rw [h2]

theorem ggTPJStabInput_holds
    : GGTPJStabInput := by
  intro lab hdep hΛ
  rcases hdep with ⟨htag, h3⟩ | ⟨htag, h3⟩
  ·
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag h3
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
    intro _ _ L' _ _ ψ A hTB hA hZ c hc J hJ φ hφ hφc
    obtain ⟨κ, β, hF, hβ, hκc, hrefl⟩ := ggTPReflIn_E6 hΛ.1 hK h3 ψ A hTB hA hc hJ
    exact ggTP_stab_of_refl hF hβ hκc hrefl φ hφ hφc
  ·
    refine TwE6Delta.labelAll (lab := lab) htag
      (Q := fun R _ I => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTPJStab R I) ?_
    intro K _ _ hK _ _ L' _ _ ψ A hTB hA hZ c hc J hJ φ hφ hφc
    obtain ⟨κ, β, hF, hβ, hκc, hrefl⟩ := ggTPReflIn_TwE6 hΛ.1 h3 hK ψ A hTB hA hc hJ
    exact ggTP_stab_of_refl hF hβ hκc hrefl φ hφ hφc

end CFSG.StandardType

end
