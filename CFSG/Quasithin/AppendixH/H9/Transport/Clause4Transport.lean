module

public import CFSG.Quasithin.AppendixH.H9.Transport.GenericClauses
public import CFSG.Quasithin.AppendixH.H9.Transport.LgInvariance

public section

namespace CFSG.ASVolI.ChH.Transport

open CFSG.Quasithin CFSG.Open

variable {V : Type*} [CommGroup V]

theorem clause4Gen_conj_aux {M L : Subgroup (MulAut V)} {V1 V2 : Subgroup V}
    {perp : Subgroup V → Subgroup V} {polar : V → V → ZMod 2} {Orb : Set V}
    {X : Type*} [Group X] {A : Type*} [CommGroup A] {Γ : Subgroup (MulAut A)}
    {l : MulAut V} (hL : conjAut l L = L) (hM : conjAut l M = M)
    (hV1 : l ∈ stabSub V1) (hV2 : l ∈ stabSub V2)
    (hperp : ∀ U : Subgroup V, perp (U.map (l : MulAut V).toMonoidHom) =
      (perp U).map (l : MulAut V).toMonoidHom)
    (hpolar : ∀ x y : V, polar (l x) (l y) = polar x y) (hOrb : ∀ x : V, l x ∈ Orb ↔ x ∈ Orb)
    {T : Subgroup (MulAut V)} {v₁ v₂ : V}
    (h : Clause4Gen M L V1 V2 perp polar Orb X Γ T v₁ v₂) :
    Clause4Gen M L V1 V2 perp polar Orb X Γ (conjAut l T) (l v₁) (l v₂) := by
  obtain ⟨hO, ⟨S, hS1, hS2, t, htS, htL, ht2, ht3, ht4, hCvt, hGL, hRW, hRT⟩,
    ⟨hc1, hc2, hc3, hc4⟩, hind, hpol1, hpol2⟩ := h
  have hV1' := map_eq_self_of_mem_stabSub hV1
  have hV2' := map_eq_self_of_mem_stabSub hV2
  have hmul : l v₁ * l v₂ = l (v₁ * v₂) := (map_mul l v₁ v₂).symm
  have hCv : M ⊓ centSub (Subgroup.zpowers (l (v₁ * v₂))) =
      conjAut l (M ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) :=
    inf_centSub_zpowers_map_eq_conjAut hM _
  have hLv : L ⊓ centSub (Subgroup.zpowers (l (v₁ * v₂))) =
      conjAut l (L ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) :=
    inf_centSub_zpowers_map_eq_conjAut hL _
  have hRv : twoResidual (L ⊓ centSub (Subgroup.zpowers (l (v₁ * v₂)))) =
      conjAut l (twoResidual (L ⊓ centSub (Subgroup.zpowers (v₁ * v₂)))) := by
    rw [hLv, twoResidual_conjAut]
  have hCW : M ⊓ centSub (Subgroup.zpowers (l v₁) ⊔ Subgroup.zpowers (l v₂)) =
      conjAut l (M ⊓ centSub (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) :=
    inf_centSub_zpowers_sup_map_eq_conjAut hM v₁ v₂
  have hW : (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂).map (l : MulAut V).toMonoidHom =
      Subgroup.zpowers (l v₁) ⊔ Subgroup.zpowers (l v₂) := map_zpowers_sup_zpowers_aut l v₁ v₂
  have hP1 : V1 ⊓ perp (Subgroup.zpowers (l v₁) ⊔ Subgroup.zpowers (l v₂)) =
      (V1 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)).map (l : MulAut V).toMonoidHom :=
    inf_map_eq_of_map_eq_self hV1' (by rw [← hW, hperp])
  have hP2 : V2 ⊓ perp (Subgroup.zpowers (l v₁) ⊔ Subgroup.zpowers (l v₂)) =
      (V2 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)).map (l : MulAut V).toMonoidHom :=
    inf_map_eq_of_map_eq_self hV2' (by rw [← hW, hperp])
  have hTc : conjAut l T ⊓ centSub (Subgroup.zpowers (l (v₁ * v₂))) =
      conjAut l (T ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) := by
    rw [conjAut_inf, conjAut_centSub, map_zpowers]
  unfold Clause4Gen
  rw [hmul]
  refine ⟨?_, ⟨conjAut l S, ?_, ?_, l * t * l⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hOrb _).2 hO
  · rw [hCv]; exact (isSylowIn_conjAut_iff l S _).2 hS1
  · rw [hTc, ← hS2, conjAut_inf, hL]
  · exact conj_mem_conjAut htS
  · intro hmem
    apply htL
    rw [← hL, mem_conjAut] at hmem
    simpa [mul_assoc] using hmem
  · rw [conj_pow, ht2]; simp
  · show l (t ((l⁻¹ : MulAut V) (l v₁))) = l v₂
    rw [inv_apply_apply, ht3]
  · show l (t ((l⁻¹ : MulAut V) (l v₂))) = l v₁
    rw [inv_apply_apply, ht4]
  · rw [hCv, hRv, ← conjAut_zpowers, ← conjAut_sup, hCvt]
  · rw [hCv]; exact (nonempty_mulEquiv_conjAut_iff l _ X).2 hGL
  · rw [hRv, hCW, twoResidual_conjAut, hRW]
  · rw [hRv, hTc]; exact (isSylowIn_conjAut_iff l _ _).2 hRT
  · rw [hP1]
    have h := congrArg (Subgroup.map (l : MulAut V).toMonoidHom) hc1
    rw [map_sup_subgroup, map_zpowers, hV1'] at h
    exact h
  · rw [hP1]
    have h := congrArg (Subgroup.map (l : MulAut V).toMonoidHom) hc2
    rw [map_inf_subgroup, map_zpowers, Subgroup.map_bot] at h
    exact h
  · rw [hP2]
    have h := congrArg (Subgroup.map (l : MulAut V).toMonoidHom) hc3
    rw [map_sup_subgroup, map_zpowers, hV2'] at h
    exact h
  · rw [hP2]
    have h := congrArg (Subgroup.map (l : MulAut V).toMonoidHom) hc4
    rw [map_inf_subgroup, map_zpowers, Subgroup.map_bot] at h
    exact h
  · rw [hRv, hP1]
    have h := (inducesOn_conjAut_iff l _ _ ⊥ A Γ).2 hind
    rwa [Subgroup.map_bot] at h
  · intro w hw hw1
    rw [hP1] at hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
    have hu1 : u ≠ 1 := fun h => hw1 (by simp [h])
    obtain ⟨u', hu', hne⟩ := hpol1 u hu hu1
    refine ⟨l u', ?_, ?_⟩
    · rw [hP2]; exact Subgroup.mem_map_of_mem _ hu'
    · exact fun h => hne ((hpolar _ _).symm.trans h)
  · intro w' hw' hw1
    rw [hP2] at hw'
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hw'
    have hu1 : u' ≠ 1 := fun h => hw1 (by simp [h])
    obtain ⟨u, hu, hne⟩ := hpol2 u' hu' hu1
    refine ⟨l u, ?_, ?_⟩
    · rw [hP1]; exact Subgroup.mem_map_of_mem _ hu
    · exact fun h => hne ((hpolar _ _).symm.trans h)

theorem clause4Gen_conj {M L : Subgroup (MulAut V)} {V1 V2 : Subgroup V}
    {perp : Subgroup V → Subgroup V} {polar : V → V → ZMod 2} {Orb : Set V}
    {X : Type*} [Group X] {A : Type*} [CommGroup A] {Γ : Subgroup (MulAut A)}
    {G : Subgroup (MulAut V)}
    (hL : ∀ g ∈ G, conjAut g L = L) (hM : ∀ g ∈ G, conjAut g M = M)
    (hV1 : G ≤ stabSub V1) (hV2 : G ≤ stabSub V2)
    (hperp : ∀ g ∈ G, ∀ U : Subgroup V, perp (U.map (g : MulAut V).toMonoidHom) =
      (perp U).map (g : MulAut V).toMonoidHom)
    (hpolar : ∀ g ∈ G, ∀ x y : V, polar (g x) (g y) = polar x y)
    (hOrb : ∀ g ∈ G, ∀ x : V, g x ∈ Orb ↔ x ∈ Orb)
    {l : MulAut V} (hl : l ∈ G) (T : Subgroup (MulAut V)) (v₁ v₂ : V) :
    Clause4Gen M L V1 V2 perp polar Orb X Γ T v₁ v₂ ↔
      Clause4Gen M L V1 V2 perp polar Orb X Γ (conjAut l T) (l v₁) (l v₂) := by
  refine ⟨clause4Gen_conj_aux (hL l hl) (hM l hl) (hV1 hl) (hV2 hl) (hperp l hl)
    (hpolar l hl) (hOrb l hl), fun h => ?_⟩
  have hl' : l⁻¹ ∈ G := inv_mem hl
  have h' := clause4Gen_conj_aux (hL l⁻¹ hl') (hM l⁻¹ hl') (hV1 hl') (hV2 hl') (hperp l⁻¹ hl')
    (hpolar l⁻¹ hl') (hOrb l⁻¹ hl') h
  rwa [conjAut_inv_conjAut l T, inv_apply_apply l v₁, inv_apply_apply l v₂] at h'

end CFSG.ASVolI.ChH.Transport
