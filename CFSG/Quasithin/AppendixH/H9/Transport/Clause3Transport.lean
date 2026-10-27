module

public import CFSG.Quasithin.AppendixH.H9.Transport.GenericClauses
public import CFSG.Quasithin.AppendixH.H9.Transport.LgInvariance

public section

namespace CFSG.ASVolI.ChH.Transport

open CFSG.Quasithin CFSG.Open

variable {V : Type*} [CommGroup V]

theorem clause3Gen_conj_aux {M L : Subgroup (MulAut V)} {V1 V2 : Subgroup V}
    {perp : Subgroup V → Subgroup V} {c : ℕ} {Q : Type*} [Group Q]
    {A : Type*} [CommGroup A] {Γ : Subgroup (MulAut A)}
    {l : MulAut V} (hL : conjAut l L = L) (hM : conjAut l M = M)
    (hV1 : l ∈ stabSub V1) (hV2 : l ∈ stabSub V2)
    (hperp : ∀ U : Subgroup V, perp (U.map (l : MulAut V).toMonoidHom) =
      (perp U).map (l : MulAut V).toMonoidHom)
    {T : Subgroup (MulAut V)} {v₁ : V}
    (h : Clause3Gen M L V1 V2 perp c Q Γ T v₁) :
    Clause3Gen M L V1 V2 perp c Q Γ (conjAut l T) (l v₁) := by
  obtain ⟨h1, ⟨E, hE1, hE2, hE3⟩, h3, h4, h5, h6, h7, h8⟩ := h
  have hV1' := map_eq_self_of_mem_stabSub hV1
  have hV2' := map_eq_self_of_mem_stabSub hV2
  have hK : M ⊓ centSub (Subgroup.zpowers (l v₁)) =
      conjAut l (M ⊓ centSub (Subgroup.zpowers v₁)) :=
    inf_centSub_zpowers_map_eq_conjAut hM v₁
  have hLc : L ⊓ centSub (Subgroup.zpowers (l v₁)) =
      conjAut l (L ⊓ centSub (Subgroup.zpowers v₁)) :=
    inf_centSub_zpowers_map_eq_conjAut hL v₁
  have hR : twoResidual (L ⊓ centSub (Subgroup.zpowers (l v₁))) =
      conjAut l (twoResidual (L ⊓ centSub (Subgroup.zpowers v₁))) := by
    rw [hLc, twoResidual_conjAut]
  have hC : centSub (Subgroup.zpowers (l v₁)) =
      conjAut l (centSub (Subgroup.zpowers v₁)) := by
    rw [conjAut_centSub, map_zpowers]
  have hV2p : V2 ⊓ perp (Subgroup.zpowers (l v₁)) =
      (V2 ⊓ perp (Subgroup.zpowers v₁)).map (l : MulAut V).toMonoidHom :=
    inf_map_eq_of_map_eq_self hV2' (by rw [← map_zpowers, hperp])
  have hTs : conjAut l T ⊓ stabSub V1 = conjAut l (T ⊓ stabSub V1) := conjAut_inf_stabSub hV1 T
  have hTc : conjAut l T ⊓ centSub (Subgroup.zpowers (l v₁)) =
      conjAut l (T ⊓ centSub (Subgroup.zpowers v₁)) := by
    rw [hC, conjAut_inf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK, hR, h1]
  · refine ⟨conjAut l E, (isElemAbelian_conjAut_iff 2 l E).2 hE1,
      (card_conjAut l E).trans hE2, ?_⟩
    rw [hK]
    exact (isExtOf_conjAut_iff l _ _ Q).2 hE3
  · rw [hR, commOn_conjAut_of_map_eq hV1', h3, hV1']
  · rw [hR, commOn_conjAut_of_map_eq hV2', h4, hV2p]
  · rw [hV2p]
    have h := relIndex_map_aut l (V2 ⊓ perp (Subgroup.zpowers v₁)) V2
    rw [hV2'] at h
    rw [h, h5]
  · rw [hR, commOn_conjAut_of_map_eq hV2']
    have h := (inducesOn_conjAut_iff l _ _ ⊥ A Γ).2 h6
    rwa [Subgroup.map_bot] at h
  · rw [hTs, hTc, h7]
  · rw [hK, hTs]
    exact (isSylowIn_conjAut_iff l _ _).2 h8

theorem clause3Gen_conj {M L : Subgroup (MulAut V)} {V1 V2 : Subgroup V}
    {perp : Subgroup V → Subgroup V} {c : ℕ} {Q : Type*} [Group Q]
    {A : Type*} [CommGroup A] {Γ : Subgroup (MulAut A)} {G : Subgroup (MulAut V)}
    (hL : ∀ g ∈ G, conjAut g L = L) (hM : ∀ g ∈ G, conjAut g M = M)
    (hV1 : G ≤ stabSub V1) (hV2 : G ≤ stabSub V2)
    (hperp : ∀ g ∈ G, ∀ U : Subgroup V, perp (U.map (g : MulAut V).toMonoidHom) =
      (perp U).map (g : MulAut V).toMonoidHom)
    {l : MulAut V} (hl : l ∈ G) (T : Subgroup (MulAut V)) (v₁ : V) :
    Clause3Gen M L V1 V2 perp c Q Γ T v₁ ↔
      Clause3Gen M L V1 V2 perp c Q Γ (conjAut l T) (l v₁) := by
  refine ⟨clause3Gen_conj_aux (hL l hl) (hM l hl) (hV1 hl) (hV2 hl) (hperp l hl), fun h => ?_⟩
  have hl' : l⁻¹ ∈ G := inv_mem hl
  have h' := clause3Gen_conj_aux (hL l⁻¹ hl') (hM l⁻¹ hl') (hV1 hl') (hV2 hl') (hperp l⁻¹ hl') h
  rwa [conjAut_inv_conjAut l T, inv_apply_apply l v₁] at h'

end CFSG.ASVolI.ChH.Transport
