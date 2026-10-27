module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrKer
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Syl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrPsi

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace X1512

variable {G : Type} [Group G] [Finite G] {n : ℕ} {H U L N K F₁ F₂ X₁ X₂ : Subgroup G}

namespace WrStep

variable (P : WrStep H U L N K F₁ F₂ X₁ X₂)

include P

theorem sylow_img (hn : n = 3 ∨ n = 5) [(L.subgroupOf X₁).Normal] [(L.subgroupOf X₂).Normal]
    {Ψ₁ Ψ₂ : ↥K →* Equiv.Perm (Fin n)} {β₁ : ↥(G6.coreMod n) →* ↥X₁ ⧸ L.subgroupOf X₁}
    {β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂}
    (W : WrAll n P.F₁_le_K P.F₂_le_K Ψ₁ Ψ₂ β₁ β₂) {T : Subgroup G} (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf ((((T ⊓ K) ⊓ kerSub Ψ₂).subgroupOf K).map Ψ₁) ⊤ := by
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_forall P.K_normal
  have h1 : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hT P.K_le hHK
  have h2 : IsSylowTwoOf ((T ⊓ K) ⊓ kerSub Ψ₂) (kerSub Ψ₂) :=
    B6.isSylowTwoOf_inf_normal h1 (kerSub_le Ψ₂) (kerSub_normalizer Ψ₂)
  have h3 := sylow_subgroupOf_of_le h2 (kerSub_le Ψ₂)
  rw [subgroupOf_kerSub] at h3
  refine sylow_map_of_map_eq_top ?_ h3
  rw [eq_top_iff]
  intro σ _
  obtain ⟨f, hf, hfσ⟩ := W.onto₁ σ
  exact ⟨⟨f, P.F₁_le_K hf⟩, P.ψ₂_eq_one_of_mem_F₁ hn W.M₂ hf, hfσ⟩

theorem not_mem_of_closure (hn : n = 3 ∨ n = 5) [(L.subgroupOf X₁).Normal]
    [(L.subgroupOf X₂).Normal] {Ψ₁ Ψ₂ : ↥K →* Equiv.Perm (Fin n)}
    {β₁ : ↥(G6.coreMod n) →* ↥X₁ ⧸ L.subgroupOf X₁}
    {β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂}
    (W : WrAll n P.F₁_le_K P.F₂_le_K Ψ₁ Ψ₂ β₁ β₂)
    (hker : (Ψ₁.prod Ψ₂).ker = (cSecIn H L N).subgroupOf K) {T Pm : Subgroup G}
    (hmp : MinParabolic H T Pm) (hCP : cSecIn H L N ≤ Pm) {t : G} (htT : t ∈ T) (htK : t ∉ K)
    {x : G} (hxF : x ∈ F₁)
    (hcl : Subgroup.closure ({Ψ₁ ⟨x, P.F₁_le_K hxF⟩} ∪
      ((((T ⊓ K) ⊓ kerSub Ψ₂).subgroupOf K).map Ψ₁ : Set (Equiv.Perm (Fin n)))) = ⊤) :
    x ∉ Pm := by
  intro hxP
  have htH : t ∈ H := hmp.isSylow.1 htT
  have hK₂ : kerSub Ψ₂ ≤ Pm := by
    intro k hk
    obtain ⟨hkK, hk1⟩ := mem_kerSub.mp hk
    have hxK₂ : x ∈ kerSub Ψ₂ :=
      mem_kerSub.mpr ⟨P.F₁_le_K hxF, P.ψ₂_eq_one_of_mem_F₁ hn W.M₂ hxF⟩
    have hsub : ({Ψ₁ ⟨x, P.F₁_le_K hxF⟩} ∪
        ((((T ⊓ K) ⊓ kerSub Ψ₂).subgroupOf K).map Ψ₁ : Set (Equiv.Perm (Fin n)))) ⊆
        ((((Pm ⊓ kerSub Ψ₂).subgroupOf K).map Ψ₁ : Subgroup (Equiv.Perm (Fin n)))) := by
      rintro _ (rfl | ⟨q, hq, rfl⟩)
      · exact ⟨⟨x, P.F₁_le_K hxF⟩, Subgroup.mem_subgroupOf.mpr ⟨hxP, hxK₂⟩, rfl⟩
      · have hq' := Subgroup.mem_subgroupOf.mp hq
        exact ⟨q, Subgroup.mem_subgroupOf.mpr ⟨hmp.le hq'.1.1, hq'.2⟩, rfl⟩
    have hmem : Ψ₁ ⟨k, hkK⟩ ∈ (((Pm ⊓ kerSub Ψ₂).subgroupOf K).map Ψ₁ : Subgroup _) :=
      (Subgroup.closure_le _).mpr hsub (by rw [hcl]; exact Subgroup.mem_top _)
    obtain ⟨q, hq, hqk⟩ := hmem
    have hq' := Subgroup.mem_subgroupOf.mp hq
    obtain ⟨hqK₂, hq2⟩ := mem_kerSub.mp hq'.2
    have hkq : (⟨k, hkK⟩ : ↥K)⁻¹ * q ∈ (Ψ₁.prod Ψ₂).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one]
      refine ⟨?_, ?_⟩
      · rw [map_mul, map_inv, hqk, inv_mul_cancel]
      · rw [map_mul, map_inv, hk1, hq2]
        simp
    rw [hker, Subgroup.mem_subgroupOf] at hkq
    have e : k = (q : G) * (k⁻¹ * (q : G))⁻¹ := by group
    rw [e]
    exact Pm.mul_mem hq'.1 (Pm.inv_mem (hCP hkq))
  have hF₂ : F₂ ≤ Pm := by
    intro f hf
    have hfK : f ∈ K := P.F₂_le_K hf
    have hconj : t * f * t⁻¹ ∈ kerSub Ψ₂ := by
      refine mem_kerSub.mpr ⟨P.K_normal t htH f hfK, ?_⟩
      refine (W.M₂.ψ_eq_one_iff hn P.L_le₂ _).mpr ?_
      exact P.conj_centralizes' htH htK hfK fun x hx => P.F₂_triv f hf x hx
    have h1 := hK₂ hconj
    have e : f = t⁻¹ * (t * f * t⁻¹) * t := by group
    rw [e]
    exact Pm.mul_mem (Pm.mul_mem (Pm.inv_mem (hmp.le htT)) h1) (hmp.le htT)
  have hF₁ : F₁ ≤ Pm := fun f hf =>
    hK₂ (mem_kerSub.mpr ⟨P.F₁_le_K hf, P.ψ₂_eq_one_of_mem_F₁ hn W.M₂ hf⟩)
  have hKP : K ≤ Pm := by
    rw [← P.FFK]
    exact sup_le hF₁ hF₂
  have hHP : H ≤ Pm := by
    intro h hh
    rcases P.mem_K_or_mul_mem htH htK h hh with h1 | h1
    · exact hKP h1
    · have e : h = (h * t⁻¹) * t := by group
      rw [e]
      exact Pm.mul_mem (hKP h1) (hmp.le htT)
  exact lt_irrefl _ (lt_of_lt_of_le hmp.maximal.1 hHP)

end WrStep

end X1512

end CFSG.Quasithin
