module

public import CFSG.Quasithin.EmptyFaithful.S153E53C
public import CFSG.Quasithin.EmptyFaithful.S153E54B
public import CFSG.Quasithin.EmptyFaithful.S153E54F

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
  CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

section Ident

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem T_le_normalizer_YU (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer ((Y153 Mc M ⊔ UH153 T M V₁ Mc : Subgroup G) : Set G) := fun _ hx =>
  Subgroup.inf_normalizer_le_normalizer_sup (Y153 Mc M) (UH153 T M V₁ Mc)
    (Subgroup.mem_inf.2 ⟨(T_le_M cx).trans (le_normalizer_Y153 Mc M) hx,
      T_le_normalizer_U cx hx⟩)

theorem pCoreOf_YU_eq (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) :
    pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) =
      (Y153 Mc M ⊔ UH153 T M V₁ Mc) ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨S⟩ := nonempty_setup cx c
  have hIT : Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ Y153 Mc M ⊔ T := sup_le_sup_left (U_le_T cx) _
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 _) ?_
    have h1 : pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) ≤ pCoreOf 2 (Y153 Mc M ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hIT)
        (sup_le ((le_sup_left : Y153 Mc M ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc).trans
            (le_normalizer_pCoreOf 2 _))
          ((T_le_normalizer_YU cx).trans (normalizer_le_normalizer_pCoreOf 2 _)))
        (pCoreOf_isPGroup 2 _)
    rw [Hyp153.lemma_15_3_7_pCore h113 cx.c.hyp] at h1
    exact fun x hx => (h1 hx).2
  · have hNT : (Y153 Mc M ⊔ UH153 T M V₁ Mc) ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ T := by
      intro x hx
      exact mem_T_of_alpha_eq_one h113 cx S hx.1 ((S.ker ⟨x, hx.1⟩).2 hx.2)
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, B2F.le_normalizer_centralizer (YU_le_normalizer cx) hx⟩)
      (cx.hF.sylow_H.2.1.to_le hNT)

omit [Finite G] in
theorem autI_equiv_SL {V M' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M' ≤ Subgroup.normalizer (V : Set G)) (β : ↥M' →* SL(2, ZMod 2))
    (hβ : Function.Surjective β)
    (hker : ∀ x : ↥M', β x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G)) :
    Nonempty (↥(autI hV M') ≃* SL(2, ZMod 2)) := by
  have hk : (convHom hV M' hM).ker = β.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, convHom_apply, convI_eq_one_iff, hker]
  exact ⟨(MulEquiv.subgroupCongr (range_convHom hV M' hM).symm).trans
    ((QuotientGroup.quotientKerEquivRange (convHom hV M' hM)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective β hβ)))⟩

theorem eq_Ni_of_autOn_eq (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {M' : Subgroup G} {N : Subgroup (MulAut ↥(VZ T M))}
    (hSM : pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) ≤ M') (hMI : M' ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (h : autOn M' (VZ T M) = N) : M' = Ni153 T Mc M V₁ N := by
  have hV := cx.c.hyp.elemAbelian
  ext x
  constructor
  · intro hx
    have hN : x ∈ Subgroup.normalizer (VZ T M : Set G) := YU_le_normalizer cx (hMI hx)
    refine mem_preAut153.2 ⟨hMI hx, hN, ?_⟩
    have := convI_mem_autI hV hx hN
    rw [autI_eq_autOn, h] at this
    exact this
  · intro hx
    obtain ⟨hxI, hN, hxN⟩ := mem_preAut153.1 hx
    have hx' : convI hV ⟨x, hN⟩ ∈ autI hV M' := by
      rw [autI_eq_autOn, h]
      exact hxN
    obtain ⟨m, hmM, hm⟩ := (mem_autI hV).1 hx'
    have hmI : (m : G) ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := hMI hmM
    have hk : (x : G)⁻¹ * (m : G) ∈ Subgroup.centralizer (VZ T M : Set G) := by
      have h1 : convI hV (⟨x, hN⟩⁻¹ * m) = 1 := by
        rw [map_mul, map_inv, hm, inv_mul_cancel]
      have := (convI_eq_one_iff hV _).1 h1
      exact this
    have hkI : (x : G)⁻¹ * (m : G) ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
      (Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem ((Y153 Mc M ⊔ UH153 T M V₁ Mc).inv_mem hxI) hmI
    have hkS : (x : G)⁻¹ * (m : G) ∈ pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
      rw [pCoreOf_YU_eq h113 cx c]
      exact ⟨hkI, hk⟩
    have e : x = (m : G) * ((x : G)⁻¹ * (m : G))⁻¹ := by group
    rw [e]
    exact M'.mul_mem hmM (M'.inv_mem (hSM hkS))

theorem autOn_YU_eq (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    autOn (Y153 Mc M ⊔ UH153 T M V₁ Mc) (VZ T M) = N₁ ⊔ N₂ := by
  obtain ⟨Ω, -, hsup, hN⟩ := c.h53one.omega
  have hY : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (Y153_le Mc M).trans cx.c.hyp.le_normalizer
  show autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) = N₁ ⊔ N₂
  rw [autI_sup cx.c.hyp.elemAbelian hY (U_le_N cx), sup_comm, hN]
  exact hsup

theorem ident_decomp (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {M₁ M₂ : Subgroup G}
    (hSM₁ : pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) ≤ M₁)
    (hSM₂ : pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) ≤ M₂)
    (hM₁I : M₁ ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc) (hM₂I : M₂ ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (hsup : M₁ ⊔ M₂ = Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (hcomm : ⁅M₁, M₂⁆ ≤ pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc))
    (β₁ : ↥M₁ →* SL(2, ZMod 2)) (hβ₁ : Function.Surjective β₁)
    (hβ₁k : ∀ x : ↥M₁, β₁ x = 1 ↔ (x : G) ∈ pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc))
    (β₂ : ↥M₂ →* SL(2, ZMod 2)) (hβ₂ : Function.Surjective β₂)
    (hβ₂k : ∀ x : ↥M₂, β₂ x = 1 ↔ (x : G) ∈ pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc)) :
    (M₁ = Ni153 T Mc M V₁ N₁ ∧ M₂ = Ni153 T Mc M V₁ N₂) ∨
      (M₁ = Ni153 T Mc M V₁ N₂ ∧ M₂ = Ni153 T Mc M V₁ N₁) := by
  have hV := cx.c.hyp.elemAbelian
  have hS := pCoreOf_YU_eq h113 cx c
  have hN₁ : M₁ ≤ Subgroup.normalizer (VZ T M : Set G) := hM₁I.trans (YU_le_normalizer cx)
  have hN₂ : M₂ ≤ Subgroup.normalizer (VZ T M : Set G) := hM₂I.trans (YU_le_normalizer cx)
  have hk₁ : ∀ x : ↥M₁, β₁ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) := fun x => by
    rw [hβ₁k, hS]
    exact ⟨fun h => h.2, fun h => ⟨hM₁I x.2, h⟩⟩
  have hk₂ : ∀ x : ↥M₂, β₂ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) := fun x => by
    rw [hβ₂k, hS]
    exact ⟨fun h => h.2, fun h => ⟨hM₂I x.2, h⟩⟩
  obtain ⟨e₁⟩ := autI_equiv_SL hV hN₁ β₁ hβ₁ hk₁
  obtain ⟨e₂⟩ := autI_equiv_SL hV hN₂ β₂ hβ₂ hk₂
  obtain ⟨f₁⟩ := c.h53one.iso₁
  obtain ⟨f₂⟩ := c.h53one.iso₂
  have hLc : ∀ a ∈ autOn M₁ (VZ T M), ∀ b ∈ autOn M₂ (VZ T M), a * b = b * a := by
    intro a ha b hb
    obtain ⟨g₁, hg₁, rfl⟩ := (mem_autI hV).1 ha
    obtain ⟨g₂, hg₂, rfl⟩ := (mem_autI hV).1 hb
    have h1 : (g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹ ∈ pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) :=
      hcomm (Subgroup.commutator_mem_commutator hg₁ hg₂)
    rw [hS] at h1
    have h2 : convI hV (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := (convI_eq_one_iff hV _).2 h1.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc convI hV g₁ * convI hV g₂ = (convI hV g₁ * convI hV g₂ * (convI hV g₁)⁻¹ *
        (convI hV g₂)⁻¹) * (convI hV g₂ * convI hV g₁) := by group
      _ = convI hV g₂ * convI hV g₁ := by rw [h2, one_mul]
  have hsupΩ : N₁ ⊔ N₂ = autOn M₁ (VZ T M) ⊔ autOn M₂ (VZ T M) := by
    rw [← autOn_YU_eq cx c, ← hsup]
    exact autI_sup hV hN₁ hN₂
  have key := unique_decomp (K₁ := N₁) (K₂ := N₂) (L₁ := autOn M₁ (VZ T M))
    (L₂ := autOn M₂ (VZ T M)) c.h53one.inf c.h53one.comm hLc hsupΩ
    (f₁.trans S143.dihThreeEquivPerm.symm) (f₂.trans S143.dihThreeEquivPerm.symm)
    (e₁.trans dihSL.symm) (e₂.trans dihSL.symm)
  rcases key with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
  · exact Or.inl ⟨eq_Ni_of_autOn_eq h113 cx c hSM₁ hM₁I k₁, eq_Ni_of_autOn_eq h113 cx c hSM₂ hM₂I k₂⟩
  · exact Or.inr ⟨eq_Ni_of_autOn_eq h113 cx c hSM₁ hM₁I k₁, eq_Ni_of_autOn_eq h113 cx c hSM₂ hM₂I k₂⟩

end Ident

end S153E54

end CFSG.Quasithin
