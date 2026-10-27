module

public import CFSG.Quasithin.EmptyFaithful.T1531In66a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.Quasithin.T1531O4
open CFSG.LieType.BorelTits

namespace S1567

section Model

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem rbar_central (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)} (hT : IsSylowTwoOf T' X)
    {s₁ s₂ τ : MulAut W} {a₁ a₂ : W} (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) :
    s₁ * s₂ ∈ T' ∧ s₁ * s₂ ≠ 1 ∧ (s₁ * s₂) * (s₁ * s₂) = 1 ∧
      ∀ x ∈ T', x * (s₁ * s₂) = (s₁ * s₂) * x := by
  have hs₁T : s₁ ∈ T' := hF.sylow.s₁_mem_S.1
  have hs₂T : s₂ ∈ T' := hF.sylow.s₂_mem_S.1
  have hs₁sq : s₁ * s₁ = 1 := hF.s₁_sq
  have hs₂sq : s₂ * s₂ = 1 := hF.s₂_sq
  have hτT : τ ∈ T' := hF.τ_T
  have hτN : τ ∉ L₁ ⊔ L₂ := hF.τ_N
  have k₁ : τ * s₁ * τ⁻¹ = s₂ := hF.τs₁
  have k₂ : τ * s₂ * τ⁻¹ = s₁ := hF.τs₂
  have hSeq := hF.S_eq
  have hm1 : s₁ * s₂ ≠ 1 := hF.mul_ne
  have hc12 : s₁ * s₂ = s₂ * s₁ := hF.comm
  have hS4 := h.card_S hT
  have hT8 := h.card_T hT
  have hrel : (T' ⊓ (L₁ ⊔ L₂)).relIndex T' = 2 := by
    have h1 := Subgroup.relIndex_mul_card (T' ⊓ (L₁ ⊔ L₂)) T'
    rw [inf_eq_left.mpr (inf_le_left : T' ⊓ (L₁ ⊔ L₂) ≤ T'), hS4, hT8] at h1
    omega
  have hcos : ∀ x ∈ T', x ∈ T' ⊓ (L₁ ⊔ L₂) ∨ x * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := fun x hx =>
    coset_of_relIndex_two hrel hx hτT (fun hτS => hτN hτS.2)
  have e1 : s₁ * (s₁ * s₂) = s₂ := by rw [← mul_assoc, hs₁sq, one_mul]
  have e2 : (s₁ * s₂) * s₁ = s₂ := by rw [hc12, mul_assoc, hs₁sq, mul_one]
  have e3 : s₂ * (s₁ * s₂) = s₁ := by rw [hc12, ← mul_assoc, hs₂sq, one_mul]
  have e4 : (s₁ * s₂) * s₂ = s₁ := by rw [mul_assoc, hs₂sq, mul_one]
  have hrsq : (s₁ * s₂) * (s₁ * s₂) = 1 := by rw [← mul_assoc, e2, hs₂sq]
  have hτr : τ * (s₁ * s₂) * τ⁻¹ = s₁ * s₂ := by
    have : τ * (s₁ * s₂) * τ⁻¹ = (τ * s₁ * τ⁻¹) * (τ * s₂ * τ⁻¹) := by group
    rw [this, k₁, k₂, ← hc12]
  have hτr' : τ * (s₁ * s₂) = (s₁ * s₂) * τ := by
    calc τ * (s₁ * s₂) = (τ * (s₁ * s₂) * τ⁻¹) * τ := by group
      _ = (s₁ * s₂) * τ := by rw [hτr]
  have hCent : ∀ x ∈ T' ⊓ (L₁ ⊔ L₂), x * (s₁ * s₂) = (s₁ * s₂) * x := by
    intro x hx
    rcases (hSeq x).1 hx with h1 | h1 | h1 | h1
    · rw [h1]; simp
    · rw [h1, e1, e2]
    · rw [h1, e3, e4]
    · rw [h1]
  refine ⟨T'.mul_mem hs₁T hs₂T, hm1, hrsq, fun x hx => ?_⟩
  rcases hcos x hx with hxS | hxS
  · exact hCent x hxS
  · have hw := hCent _ hxS
    calc x * (s₁ * s₂) = (x * τ⁻¹) * (τ * (s₁ * s₂)) := by group
      _ = (x * τ⁻¹) * ((s₁ * s₂) * τ) := by rw [hτr']
      _ = ((x * τ⁻¹) * (s₁ * s₂)) * τ := by group
      _ = ((s₁ * s₂) * (x * τ⁻¹)) * τ := by rw [hw]
      _ = (s₁ * s₂) * x := by group

end Model

section Ambient

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem exists_central_move (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    {Q : Subgroup G} (hQT : Q ≤ T) (hQn : T ≤ Subgroup.normalizer (Q : Set G))
    (hQ : ¬ Q ≤ Subgroup.centralizer (VZ T M : Set G)) :
    ∃ q ∈ Q, q ∈ TE153 T E ∧ q * q ∈ Subgroup.centralizer (VZ T M : Set G) ∧
      ∃ e ∈ E, q * e * q⁻¹ ≠ e := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := c.decomp.model
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := c.hyp.le_normalizer
  have hTM : T ≤ M := c.hyp.T_le
  have hEV : E ≤ VZ T M := L.le_V
  have hTV : T ≤ Subgroup.normalizer (VZ T M : Set G) := hTM.trans hMN
  have hQV : Q ≤ Subgroup.normalizer (VZ T M : Set G) := hQT.trans hTV
  have hÊ : IsLine (commV L₁) (commV L₂) (modOf hV E) :=
    isLine_modOf hV hEV L.card_eq L.totSingular.2.1 L.totSingular.2.2
  have hT' : IsSylowTwoOf (autI hV T) (autI hV M) :=
    B2F.isSylowTwoOf_autI hV hMN c.hyp.isSylowTwoOf
  have hTE' : IsSylowTwoOf (autI hV T ⊓ stabSub (modOf hV E))
      (autI hV M ⊓ stabSub (modOf hV E)) := by
    have h1 := B2F.isSylowTwoOf_autI hV (H := M ⊓ Subgroup.normalizer (E : Set G))
      (T := T ⊓ Subgroup.normalizer (E : Set G)) (inf_le_left.trans hMN) L.sylow
    rwa [autI_inf_normalizer hV hEV, autI_inf_normalizer hV hEV] at h1
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hT'
  obtain ⟨hrT, hr1, hrr, hrc⟩ := rbar_central hS hT' hF
  have hmul : s₁ * s₂ ∈ stabSub (modOf hV E) := s₁s₂_mem_stab hS hT' hÊ hTE' hF
  obtain ⟨e, he, hne⟩ := exists_move hS hÊ hF
  have hQle : autI hV Q ≤ autI hV T := A4.autOn_mono hQT
  have hQne : autI hV Q ≠ ⊥ := by
    intro hbot
    apply hQ
    intro x hx
    have hxN := hQV hx
    have hx1 : convI hV ⟨x, hxN⟩ = 1 := by
      have hmem : convI hV ⟨x, hxN⟩ ∈ autI hV Q := convI_mem_autI hV hx hxN
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact (convI_eq_one_iff hV ⟨x, hxN⟩).1 hx1
  have hQnorm : autI hV T ≤ Subgroup.normalizer (autI hV Q : Set (MulAut (IntMod (VZ T M) hV))) :=
    autOn_le_normalizer_autOn hTV hQV hQn
  obtain ⟨z, hzQ, hz1, hzc⟩ :=
    exists_ne_one_mem_center_of_normalized hT'.2.1 hQle hQne hQnorm
  obtain ⟨r, hrT', hr1', hrr', hrc', hrz, hrinv⟩ := hS.exists_central hT'
  have hsr : s₁ * s₂ = r := (hrz (s₁ * s₂) hrT hrc).resolve_left hr1
  have hzr : z = r := (hrz z (hQle hzQ) hzc).resolve_left hz1
  have hzs : z = s₁ * s₂ := hzr.trans hsr.symm
  obtain ⟨g, hgQ, hg⟩ := (mem_autI hV).1 hzQ
  have hgE : (g : G) ∈ Subgroup.normalizer (E : Set G) :=
    (mem_normalizer_iff_stab hV hEV g.2).2 (hg ▸ hzs ▸ hmul)
  refine ⟨(g : G), hgQ, ⟨hQT hgQ, hgE⟩, ?_, e.val, he, fun h => hne ?_⟩
  · have hgg : convI hV (g * g) = 1 := by
      rw [map_mul, hg, hzs, hrr]
    exact (convI_eq_one_iff hV (g * g)).1 hgg
  · apply IntMod.val_injective
    have h1 : (convI hV g e).val = (g : G) * e.val * (g : G)⁻¹ := convI_apply_val hV g e
    rw [hg, hzs] at h1
    rw [h1]
    exact h

end Ambient

end S1567

end CFSG.Quasithin
