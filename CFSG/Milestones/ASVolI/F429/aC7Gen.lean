module

public import CFSG.Milestones.ASVolI.F429.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem burnsideF429a_ctr_map {C : Type} [Group C] {φ : C →* G} (hφ : Function.Injective φ)
    (X : Subgroup C) : ctr (X.map φ) = (ctr X).map φ :=
  CFSG.Quasithin.H13.U4Par.centerOf_map_of_inj hφ X

theorem burnsideF429a_model_ctr {Gp M₁ M₂ : Subgroup G} {C : Type} [Group C] (Ψ : C ≃* ↥Gp)
    {P₁ P₂ : Subgroup C} (hP₁ : M₁.subgroupOf Gp = P₁.map Ψ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = P₂.map Ψ.toMonoidHom) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
        (ctr (pCoreOf 2 (P₁ ⊓ P₂))).map (Gp.subtype.comp Ψ.toMonoidHom) ∧
      ctr (oPPrime 2 (Gp ⊓ M₁)) = (ctr (oPPrime 2 P₁)).map (Gp.subtype.comp Ψ.toMonoidHom) ∧
      ctr (oPPrime 2 (Gp ⊓ M₂)) = (ctr (oPPrime 2 P₂)).map (Gp.subtype.comp Ψ.toMonoidHom) := by
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  have h1 := burnsideF429_inf_eq_map Ψ hP₁
  have h2 := burnsideF429_inf_eq_map Ψ hP₂
  have h12 : Gp ⊓ (M₁ ⊓ M₂) = (P₁ ⊓ P₂).map (Gp.subtype.comp Ψ.toMonoidHom) := by
    rw [Subgroup.map_inf_eq _ _ _ hφ, ← h1, ← h2]
    exact inf_inf_distrib_left _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [h12, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, burnsideF429a_ctr_map hφ]
  · rw [h1, burnsideF4gU4Inv_oPPrime_map hφ, burnsideF429a_ctr_map hφ]
  · rw [h2, burnsideF4gU4Inv_oPPrime_map hφ, burnsideF429a_ctr_map hφ]

theorem burnsideF429a_pCoreOf_eq_of_sylow [Finite G] {B U : Subgroup G}
    (hU : ChF.IsSylowOf 2 U B) (hnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) : pCoreOf 2 B = U := by
  refine burnsideF4f_pCoreOf_eq hU.1 hnorm hU.2.1 fun x hx k hxk => ?_
  have hz : IsPGroup 2 (Subgroup.zpowers x) :=
    CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow hxk
  obtain ⟨p, hp, hle⟩ :=
    F7.isSylowTwoOf_exists_conj_le hU ((Subgroup.zpowers_le (H := B)).mpr hx) hz
  have h1 : p⁻¹ * x * p ∈ U := mem_conjSub.1 (hle (Subgroup.mem_zpowers x))
  have h2 := hnorm p hp _ h1
  simpa [mul_assoc] using h2

theorem burnsideF429a_le_ctr_oPPrime [Finite G] {P U L : Subgroup G} (hU : ChF.IsSylowOf 2 U P)
    (hLU : L ≤ ctr U) (hPL : ∀ p ∈ P, ∀ l ∈ L, p * l * p⁻¹ ∈ L) : L ≤ ctr (oPPrime 2 P) := by
  have hcent : oPPrime 2 P ≤ Subgroup.centralizer (L : Set G) := by
    unfold oPPrime
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxP, k, hk⟩
    have hxk : x ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    have hz : IsPGroup 2 (Subgroup.zpowers x) :=
      CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow hxk
    obtain ⟨p, hp, hle⟩ :=
      F7.isSylowTwoOf_exists_conj_le hU ((Subgroup.zpowers_le (H := P)).mpr hxP) hz
    have hu : p⁻¹ * x * p ∈ U := mem_conjSub.1 (hle (Subgroup.mem_zpowers x))
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : p⁻¹ * l * p ∈ L := by simpa using hPL p⁻¹ (inv_mem hp) l hl
    have hc := Subgroup.mem_centralizer_iff.1 (hLU hl').2 (p⁻¹ * x * p) hu
    have e1 : x * l = p * ((p⁻¹ * x * p) * (p⁻¹ * l * p)) * p⁻¹ := by group
    have e2 : l * x = p * ((p⁻¹ * l * p) * (p⁻¹ * x * p)) * p⁻¹ := by group
    rw [e2, ← hc, ← e1]
  intro l hl
  refine ⟨?_, Subgroup.le_centralizer_iff.1 hcent hl⟩
  have hlU : l ∈ U := (hLU hl).1
  obtain ⟨k, hk⟩ := hU.2.1 ⟨l, hlU⟩
  exact burnsideF4gU4Inv_mem_oPPrime (hU.1 hlU) (k := k) (by simpa using congrArg Subtype.val hk)

end Generic

end CFSG.ASVolI
