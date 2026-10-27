module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

namespace CFSG.Glauberman

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The Sylow-conjugation core of step (IV) in Glauberman's Theorems 5.1 and 5.2.
For a `p`-subgroup `W ≤ S`, one can conjugate `W` to a subgroup `V ≤ S` whose
centralizer in `S` is a Sylow `p`-subgroup of its ambient centralizer.  The chosen
conjugator is returned together with the exact identity `V^x = W`, which is the
form needed to apply a special case twice, to `x` and to `xg`. -/
public theorem exists_conjugate_with_sylow_centralizer
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (S : Sylow p G) (W : Subgroup G) (hWp : IsPGroup p W)
    (_hWleS : W ≤ (S : Subgroup G)) :
    ∃ x : G, ∃ V : Subgroup G,
      V = conjSubgroup x⁻¹ W ∧
      V ≤ (S : Subgroup G) ∧
      IsPGroup p V ∧
      conjSubgroup x V = W ∧
      ∃ P : Sylow p ↥(Subgroup.centralizer (V : Set G)),
        (P : Subgroup ↥(Subgroup.centralizer (V : Set G))).map
            (Subgroup.centralizer (V : Set G)).subtype =
          Subgroup.centralizer (V : Set G) ⊓ (S : Subgroup G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (W : Set G)
  have hW_le_N : W ≤ N := Subgroup.le_normalizer
  let W' : Subgroup ↥N := W.subgroupOf N
  have hW'p : IsPGroup p W' :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := W) (K := N) hW_le_N).symm
  obtain ⟨T, hW'_le_T⟩ := IsPGroup.exists_le_sylow (G := ↥N) (p := p) hW'p
  let T₁ : Subgroup G := T.map N.subtype
  have hT₁p : IsPGroup p T₁ := IsPGroup.map (H := T) T.isPGroup' N.subtype
  obtain ⟨S₁, hT₁_le_S₁⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hT₁p
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G S S₁
  let x : G := (y : G)⁻¹
  have hS1 : conjSubgroup x (S : Subgroup G) = (S₁ : Subgroup G) := by
    have hy' : (S : Subgroup G).map (MulAut.conj y).toMonoidHom = (S₁ : Subgroup G) := by
      simpa [sylow_smul_subgroup_eq_map_conj] using
        congrArg (fun Q : Sylow p G => (Q : Subgroup G)) hy
    simpa [x, conjSubgroup] using hy'
  let V : Subgroup G := conjSubgroup x⁻¹ W
  have hV : V = W.map (MulAut.conj x).toMonoidHom := by
    simp [V, conjSubgroup]
  have hV_le_S : V ≤ (S : Subgroup G) := by
    intro v hv
    rw [hV] at hv
    rcases Subgroup.mem_map.mp hv with ⟨w, hw, rfl⟩
    have hw' : w ∈ (conjSubgroup x (S : Subgroup G) : Set G) := by
      have hwT : w ∈ T₁ := by
        exact Subgroup.mem_map.mpr ⟨⟨w, hW_le_N hw⟩,
          hW'_le_T (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
      rw [hS1]
      exact hT₁_le_S₁ hwT
    rcases Subgroup.mem_map.mp hw' with ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hs
  have hVp : IsPGroup p V := by
    rw [hV]
    exact IsPGroup.map (H := W) hWp (MulAut.conj x).toMonoidHom
  have hVx : conjSubgroup x V = W := by
    change conjSubgroup x (conjSubgroup x⁻¹ W) = W
    rw [conjSubgroup_comp, inv_mul_cancel]
    ext w
    simp [conjSubgroup]
  refine ⟨x, V, rfl, hV_le_S, hVp, hVx, ?_⟩
  let NV : Subgroup G := Subgroup.normalizer (V : Set G)
  have hNV : N.map (MulAut.conj x).toMonoidHom = NV := by
    change N.map (MulAut.conj x).toMonoidHom =
      Subgroup.normalizer (conjSubgroup x⁻¹ W : Set G)
    rw [normalizer_conjSubgroup]
    simp [conjSubgroup, N]
  have hN_S1 : ((S₁ : Subgroup G) ⊓ N) = T₁ := by
    have hT1_le : T₁ ≤ (S₁ : Subgroup G) ⊓ N := by
      refine le_inf hT₁_le_S₁ ?_
      intro t ht
      rcases Subgroup.mem_map.mp ht with ⟨n, hn, rfl⟩
      exact n.2
    have hQp : IsPGroup p (((S₁ : Subgroup G) ⊓ N).subgroupOf N) := by
      have hS1p : IsPGroup p (↥((S₁ : Subgroup G) ⊓ N)) :=
        S₁.isPGroup'.to_inf_left
      exact hS1p.of_equiv (Subgroup.subgroupOfEquivOfLe
        (H := (S₁ : Subgroup G) ⊓ N) (K := N) inf_le_right).symm
    have hT_subgroupOf : T ≤ ((S₁ : Subgroup G) ⊓ N).subgroupOf N := by
      intro t ht
      exact Subgroup.mem_subgroupOf.mpr
        (hT1_le (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩))
    have hQ_eq_T : ((S₁ : Subgroup G) ⊓ N).subgroupOf N = T :=
      T.is_maximal' hQp hT_subgroupOf
    have h := congrArg (fun Q : Subgroup ↥N => Q.map N.subtype) hQ_eq_T
    simpa [T₁] using h
  let e : ↥N ≃* ↥NV :=
    (MulEquiv.subgroupMap (MulAut.conj x) N).trans (MulEquiv.subgroupCongr hNV)
  let NSV : Sylow p ↥NV :=
    Sylow.mapSurjective (f := e.toMonoidHom) (hf := e.surjective) T
  have hNSV_map : (NSV : Subgroup ↥NV).map NV.subtype =
      (S : Subgroup G) ⊓ NV := by
    have h1 : (NSV : Subgroup ↥NV).map NV.subtype =
        T₁.map (MulAut.conj x).toMonoidHom := by
      simp [NSV, T₁, Sylow.coe_mapSurjective, Subgroup.map_map]
      apply congrArg (fun f : ↥N →* G => T.map f)
      ext t
      simp [e, MulAut.conj_apply]
    have h2 : (S : Subgroup G) ⊓ NV =
        T₁.map (MulAut.conj x).toMonoidHom := by
      rw [← hNV]
      have h3 : ((S₁ : Subgroup G) ⊓ N).map (MulAut.conj x).toMonoidHom =
          (S : Subgroup G) ⊓ N.map (MulAut.conj x).toMonoidHom := by
        rw [Subgroup.map_inf (H := (S₁ : Subgroup G)) (K := N)
          (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective]
        congr 1
        rw [← hS1]
        simp [conjSubgroup]
        rw [Subgroup.map_map]
        ext u
        simp [MulAut.conj_apply, mul_assoc]
      rw [← h3, hN_S1]
    exact h1.trans h2.symm
  let C : Subgroup G := Subgroup.centralizer (V : Set G)
  let C' : Subgroup ↥NV := C.subgroupOf NV
  have hC_le_NV : C ≤ NV := Subgroup.centralizer_le_normalizer (V : Set G)
  have : C'.Normal := Subgroup.normal_subgroupOf_centralizer_normalizer (V : Set G)
  obtain ⟨P₀, hP₀⟩ := sylow_inf_normal (G := ↥NV) (p := p) (S := NSV) (N := C')
  let e₁ : ↥C ≃* ↥C' :=
    (Subgroup.subgroupOfEquivOfLe (H := C) (K := NV) hC_le_NV).symm
  let P : Sylow p ↥C :=
    Sylow.mapSurjective (f := e₁.symm.toMonoidHom) (hf := e₁.symm.surjective) P₀
  refine ⟨P, ?_⟩
  have hP_coe : (P : Subgroup ↥C) = P₀.map e₁.symm.toMonoidHom := by
    simp [P]
  calc
    (P : Subgroup ↥C).map C.subtype
        = (P₀.map e₁.symm.toMonoidHom).map C.subtype := by rw [hP_coe]
    _ = P₀.map (C.subtype.comp e₁.symm.toMonoidHom) := by rw [Subgroup.map_map]
    _ = P₀.map (NV.subtype.comp C'.subtype) := by
          apply congrArg (fun f : ↥C' →* G => P₀.map f)
          rfl
    _ = (P₀.map C'.subtype).map NV.subtype := by rw [Subgroup.map_map]
    _ = (NSV : Subgroup ↥NV).map NV.subtype ⊓ C'.map NV.subtype := by
          rw [hP₀]
          rw [Subgroup.map_subgroupOf_eq_of_le
            (H := (NSV : Subgroup ↥NV) ⊓ C') (K := C') inf_le_right]
          rw [Subgroup.map_inf (H := (NSV : Subgroup ↥NV)) (K := C')
            (f := NV.subtype) NV.subtype_injective]
    _ = (S : Subgroup G) ⊓ NV ⊓ C := by
          rw [hNSV_map, map_subgroupOf_eq_of_le' hC_le_NV]
    _ = C ⊓ (S : Subgroup G) := by
          rw [inf_assoc, inf_eq_right.2 hC_le_NV, inf_comm]

end CFSG.Glauberman
