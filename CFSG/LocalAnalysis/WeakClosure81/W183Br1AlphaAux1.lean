module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

variable {W : Type} [Group W]

theorem w183_conjSubgroup_map_subgroupOf {Y P : Subgroup W} (hPY : P ≤ Y)
    {x : W} (hx : x ∈ Y) :
    (conjSubgroup (P.subgroupOf Y) (⟨x, hx⟩ : ↥Y)).map Y.subtype = conjSubgroup P x := by
  ext w
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_conjSubgroup_iff] at hv ⊢
    exact hv
  · intro hw
    rw [mem_conjSubgroup_iff] at hw
    have hxinv : x⁻¹ ∈ Y := Y.inv_mem hx
    have hwY : w ∈ Y := by
      have h : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      rw [← h]
      exact Y.mul_mem (Y.mul_mem hxinv (hPY hw)) hx
    refine ⟨⟨w, hwY⟩, ?_, rfl⟩
    rw [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
    exact hw

theorem w183_dynkin_subgroupOf {Y L : Subgroup W} (hLY : L ≤ Y)
    {τ : W} (hτ : τ ∈ Y) (h : ActsOnDynkinMod ⊥ L τ) :
    ActsOnDynkinMod ⊥ (L.subgroupOf Y) (⟨τ, hτ⟩ : ↥Y) := by
  obtain ⟨hτnorm, P, hP, hconj⟩ := h
  obtain ⟨-, hPLt, hPmax, S, -, hSL, hSpow, hSidx, hSnorm⟩ := hP
  have hPL : P ≤ L := le_of_lt hPLt
  have hPY : P ≤ Y := hPL.trans hLY
  have hSY : S ≤ Y := hSL.trans hLY
  refine ⟨?_, P.subgroupOf Y, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hτnorm ⊢
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hτnorm (x : W)
  · refine ⟨bot_le, ?_, ?_, S.subgroupOf Y, bot_le, Subgroup.subgroupOf_mono Y hSL,
      ?_, ?_, ?_⟩
    · have hle : P.subgroupOf Y ≤ L.subgroupOf Y := Subgroup.subgroupOf_mono Y hPL
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hm := congrArg (Subgroup.map Y.subtype) heq
      rw [Subgroup.map_subgroupOf_eq_of_le hPY,
        Subgroup.map_subgroupOf_eq_of_le hLY] at hm
      exact hPLt.ne hm
    · intro X' hPX' hX'L'
      let XX : Subgroup W := X'.map Y.subtype
      have hP_lt_XX : P < XX := by
        refine lt_of_le_of_ne ?_ ?_
        · have hPmap : P = (P.subgroupOf Y).map Y.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hPY).symm
          rw [hPmap]
          exact Subgroup.map_mono hPX'.le
        · intro heq
          have hmap_inj := Subgroup.map_injective (f := Y.subtype) Subtype.val_injective
          have hEq' : P.subgroupOf Y = X' := by
            apply hmap_inj
            rw [Subgroup.map_subgroupOf_eq_of_le hPY, heq]
          exact hPX'.ne hEq'
      have hXX_L : XX ≤ L := by
        have hle : XX ≤ (L.subgroupOf Y).map Y.subtype := Subgroup.map_mono hX'L'
        rwa [Subgroup.map_subgroupOf_eq_of_le hLY] at hle
      have hXXeq : XX = L := hPmax XX hP_lt_XX hXX_L
      have hX'eq : X' = L.subgroupOf Y := by
        apply Subgroup.map_injective (f := Y.subtype) Subtype.val_injective
        rw [Subgroup.map_subgroupOf_eq_of_le hLY]
        exact hXXeq
      exact hX'eq
    · intro s hs
      obtain ⟨k, hk⟩ := hSpow s.1 (Subgroup.mem_subgroupOf.mp hs)
      refine ⟨k, ?_⟩
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      simpa using hk
    · have hrel := Subgroup.relIndex_comap (H := S) (f := Y.subtype) (K := L.subgroupOf Y)
      rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hLY] at hrel
      rwa [hrel]
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxL', hxnorm⟩ := hx
      rw [Subgroup.mem_subgroupOf]
      refine hSnorm ⟨Subgroup.mem_subgroupOf.mp hxL', ?_⟩
      change (x : W) ∈ Subgroup.normalizer (S : Set W)
      rw [Subgroup.mem_normalizer_iff] at hxnorm ⊢
      intro s
      constructor
      · intro hs
        have hsY : s ∈ Y := hSY hs
        have hs' : (⟨s, hsY⟩ : ↥Y) ∈ S.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hs
        exact Subgroup.mem_subgroupOf.mp ((hxnorm ⟨s, hsY⟩).mp hs')
      · intro hs
        have hsY : s ∈ Y := by
          have h : (x : W)⁻¹ * ((x : W) * s * (x : W)⁻¹) * (x : W) = s := by
            group
          rw [← h]
          exact Y.mul_mem (Y.mul_mem (Y.inv_mem x.2) (hSY hs)) x.2
        have hs' : (⟨s, hsY⟩ : ↥Y) ∈ S.subgroupOf Y := by
          rw [Subgroup.mem_subgroupOf]
          exact (hxnorm ⟨s, hsY⟩).mpr (Subgroup.mem_subgroupOf.mpr hs)
        exact Subgroup.mem_subgroupOf.mp hs'
  · intro l' hl'
    intro hEq
    let u : ↥Y := (⟨τ, hτ⟩ : ↥Y)⁻¹ * l'
    have hmap := congrArg (Subgroup.map Y.subtype) hEq
    rw [w183_conjSubgroup_map_subgroupOf hPY u.2,
      Subgroup.map_subgroupOf_eq_of_le hPY] at hmap
    exact hconj l'.1 hl' hmap

end CFSG.LocalAnalysis.WeakClosure81

end
