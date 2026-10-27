module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeSmall
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeCard
public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem KernelContext.large
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {S : LangSetup .E6 Ω 5} {B J : Subgroup (ModGL .E6 Ω)}
    {a : Fin 2 → Fin Tag.E6.rank → Ωˣ} (h : KernelContext S B J a) :
    6 < (familyKernel a).ncard := by
  by_contra hn
  have hsmall : (familyKernel a).ncard ≤ 6 := Nat.le_of_not_gt hn
  haveI : Finite S.D.model := S.finite
  haveI : Finite B := Finite.of_injective (Subgroup.inclusion h.B_model)
    (Subgroup.inclusion_injective _)
  have hgen : ∀ i, rootDiagUnit .E6 (a i) ∈ B := by
    intro i
    apply h.D_le
    rw [planeGroup]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have haT : ∀ i, rootDiagUnit .E6 (a i) ∈ S.D.torus := by
    intro i
    exact mem_twistedTorusOf.2 ⟨h.B_torus (hgen i), (h.B_model (hgen i)).2⟩
  rcases small_component_support S a haT h.pair_exp h.sign hsmall J h.J_component with
    ⟨α, _, hJ⟩ | ⟨α, β, hroots, hJ⟩
  · have hb := a1_centralizer_card B J h.B_torus h.B_exp α hJ
    rw [h.D_eq, h.D_card] at hb
    have h4 := h.B_card
    norm_num at hb h4
    omega
  · have hmem : ∀ γ ∈ a2roots α β, IsRoot .E6 γ := fun γ hγ =>
      (show γ ∈ familyKernel a by rw [hroots]; exact hγ).1
    have hα : IsRoot .E6 α := hmem α (by simp [a2roots])
    have hβ : IsRoot .E6 β := hmem β (by simp [a2roots])
    have hαβ : IsRoot .E6 (α + β) := hmem (α + β) (by simp [a2roots])
    rcases h.local_rank with h5 | ⟨γ, hγ, hz⟩
    · have hb := a2_centralizer_card B J h.B_torus h.B_exp α β hα hβ hαβ hJ
      rw [h.D_eq, h.D_card] at hb
      norm_num at hb h5
      omega
    · have hγk : γ ∈ familyKernel a := ⟨hγ, fun i => hz (a i) (hgen i)⟩
      have hb := a2_centralizer_card_of_root_zero B J h.B_torus h.B_exp α β hα hβ hαβ hJ
        ⟨γ, hroots ▸ hγk, hz⟩
      rw [h.D_eq, h.D_card] at hb
      have h4 := h.B_card
      norm_num at hb h4
      omega

end CFSG.StandardType
