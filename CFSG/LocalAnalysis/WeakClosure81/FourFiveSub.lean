module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveWhole

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

private theorem fourFive_isElemAbelian_of_map_inj {G : Type*} [Group G] {G' : Type*}
    [Group G'] {p : ℕ} {f : G →* G'} (hf : Function.Injective f) {A : Subgroup G}
    (h : IsElemAbelian p (A.map f)) : IsElemAbelian p A := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have := E1.commute_of_isElemAbelian h (Subgroup.mem_map_of_mem f x.2)
      (Subgroup.mem_map_of_mem f y.2)
    exact hf (by simpa [map_mul] using this)
  · exact hf (by simpa [map_pow] using h.2 (f x) (Subgroup.mem_map_of_mem f hx))

theorem fourFive_whole_subgroup {G : Type} [Group G] [Finite G] {j : ℕ} (hj : 1 ≤ j)
    {H S : Subgroup G} (hS : IsSylowIn 2 S H) {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hQ : fourFiveQuotCompFAS j ↥H (S.subgroupOf H)) :
    (H : Set G) = ((E1.eGen j H S Ω : Subgroup G) : Set G) *
      ((H ⊓ Subgroup.normalizer (E1.weakClosure S Ω : Set G) : Subgroup G) : Set G) := by
  have hSH : S ≤ H := hS.1
  set T : Subgroup ↥H := S.subgroupOf H with hTdef
  set Ω' : Set (Subgroup ↥H) := {A' : Subgroup ↥H | A'.map H.subtype ∈ Ω} with hΩ'def
  have hT : IsSylowIn 2 T ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (H := H) hSH le_rfl).mpr hS
    rwa [Subgroup.subgroupOf_self] at h
  have hΩ' : E1.IsInvColl (⊤ : Subgroup ↥H) Ω' := by
    refine ⟨fun _ _ => le_top, fun A' hA' => ?_, fun A' hA' x _ => ?_⟩
    · exact fourFive_isElemAbelian_of_map_inj H.subtype_injective
        (hΩ.isElemAbelian (A'.map H.subtype) hA')
    · show (CFSG.Quasithin.A1b.conjSub x A').map H.subtype ∈ Ω
      rw [E1.map_conjSub]
      exact hΩ.conj _ hA' _ x.2
  have himg : Subgroup.map H.subtype '' Ω' = Ω := by
    ext A
    refine ⟨by rintro ⟨A', hA', rfl⟩; exact hA', fun hA => ⟨A.subgroupOf H, ?_,
      Subgroup.map_subgroupOf_eq_of_le (hΩ.le A hA)⟩⟩
    show (A.subgroupOf H).map H.subtype ∈ Ω
    rwa [Subgroup.map_subgroupOf_eq_of_le (hΩ.le A hA)]
  have hmapT : T.map H.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSH
  have hE : (E1.eGen j ⊤ T Ω').map H.subtype = E1.eGen j H S Ω := by
    rw [← E1.eGen_map_subtype, hmapT, himg]
  have hW : (E1.weakClosure T Ω').map H.subtype = E1.weakClosure S Ω := by
    rw [← E1.weakClosure_map_image_of_injective H.subtype_injective, hmapT, himg]
  have hN : (Subgroup.normalizer (E1.weakClosure T Ω' : Set ↥H)).map H.subtype =
      H ⊓ Subgroup.normalizer (E1.weakClosure S Ω : Set G) := by
    rw [← hW]
    have h := Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le (E1.weakClosure T Ω'))
    have hsub : ((E1.weakClosure T Ω').map H.subtype).subgroupOf H = E1.weakClosure T Ω' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [hsub] at h
    rw [← h, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hrange : Set.range ⇑H.subtype = (H : Set G) := by
    rw [← MonoidHom.coe_range, Subgroup.range_subtype]
  have hwhole := fourFive_whole hj hT hQ hΩ'
  have himage := congrArg (Set.image H.subtype) hwhole
  rw [Set.image_mul, Set.image_univ, hrange, ← Subgroup.coe_map, ← Subgroup.coe_map, hE, hN]
    at himage
  exact himage.symm

end CFSG.LocalAnalysis.WeakClosure81
