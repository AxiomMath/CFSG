module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma7_2

namespace CFSG
end CFSG
open CFSG

/-!
# Isomorphism invariance of p-stability

This module provides the lower, acyclic home of `pStable_iso`.  The local
condition is transported by `pStableLocal_congr`; the private helpers below
transport `M_p)-membership and subgroup p-cores.
-/

namespace CFSG.Glauberman

/-- The `p`-core of a subgroup is transported along an isomorphism of the ambient group:
for `e : G ≃* G'` and a subgroup `M` of `G`, `O_p(↥M)` maps onto `O_p(↥(M.map e))`. -/
private theorem pCore_subgroup_map {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G]
    [Group G'] (e : G ≃* G') (M : Subgroup G) :
    (pCore p (↥M)).map (M.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      pCore p (↥(M.map e.toMonoidHom)) := by
  exact pCore_map_iso (G := ↥M) (G' := ↥(M.map e.toMonoidHom)) (p := p)
    (f := M.equivMapOfInjective e.toMonoidHom e.injective)

/-- Forward direction of `MpSet_map_iff`: membership in `M_p` is transported along a group
isomorphism (the `p`-core of a subgroup maps onto the `p`-core of its image, and
maximality is transported by pulling back). -/
private theorem MpSet_map_forward {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G]
    [Group G'] (e : G ≃* G') (M : Subgroup G) :
    M ∈ MpSet p G → M.map e.toMonoidHom ∈ MpSet p G' := by
  intro hM
  let M' : Subgroup G' := M.map e.toMonoidHom
  let eM : ↥M ≃* ↥M' := M.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨?_, ?_⟩
  · intro hbot
    have hcoreM : pCore p (↥M) = ⊥ := by
      apply Subgroup.map_injective (f := eM.toMonoidHom) eM.injective
      calc
        (pCore p (↥M)).map eM.toMonoidHom = pCore p (↥M') := by
          simpa [M', eM] using (pCore_subgroup_map (p := p) (e := e) M)
        _ = ⊥ := hbot
        _ = (⊥ : Subgroup ↥M).map eM.toMonoidHom := by
          simp
    exact hM.1 hcoreM
  · intro K hKc hMK
    let K0 : Subgroup G := K.map e.symm.toMonoidHom
    have hK0map : K0.map e.toMonoidHom = K := by
      dsimp [K0]
      rw [Subgroup.map_map]
      have hcomp : (e.toMonoidHom.comp e.symm.toMonoidHom : G' →* G') = MonoidHom.id G' := by
        ext y
        simp
      simp
    have hmap0 : (pCore p (↥K0)).map
          (K0.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
        pCore p (↥(K0.map e.toMonoidHom)) :=
      pCore_subgroup_map (p := p) (e := e) K0
    have hK0c : pCore p (↥K0) ≠ ⊥ := by
      intro hbot
      have hcoreK' : pCore p (↥(K0.map e.toMonoidHom)) = ⊥ := by
        rw [← hmap0, hbot]
        exact (Subgroup.map_bot (f := (K0.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom))
      -- transport along the type equality `↥(K0.map e) = ↥K` given by `hK0map`
      have hcoreK : pCore p (↥K) = ⊥ := hK0map ▸ hcoreK'
      exact hKc hcoreK
    have hMleK0 : M ≤ K0 := by
      -- `M' ≤ K` implies `M = M'.map e.symm ≤ K.map e.symm = K0`
      have hM'leK : M.map e.toMonoidHom ≤ K := hMK
      intro y hy
      have hmk : e y ∈ K := hM'leK (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      refine ⟨e y, hmk, ?_⟩
      dsimp [K0]
      -- `e.symm (e y) = y`
      exact (e.symm_apply_apply y)
    have hKeq : K0 = M := hM.2 K0 hK0c hMleK0
    calc
      K = K0.map e.toMonoidHom := hK0map.symm
      _ = M.map e.toMonoidHom := by rw [hKeq]
      _ = M' := rfl

/-- Membership in `MpSet` is transported along a group isomorphism. -/
private theorem MpSet_map_iff {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (M : Subgroup G) :
    M ∈ MpSet p G ↔ M.map e.toMonoidHom ∈ MpSet p G' := by
  constructor
  · exact MpSet_map_forward e M
  · intro hM'
    -- apply the forward direction to `e.symm` on the image of `M`
    have hback : (M.map e.toMonoidHom).map e.symm.toMonoidHom ∈ MpSet p G :=
      MpSet_map_forward (e := e.symm) (M := M.map e.toMonoidHom) hM'
    have hMMap : (M.map e.toMonoidHom).map e.symm.toMonoidHom = M := by
      rw [Subgroup.map_map]
      have hcomp : (e.symm.toMonoidHom.comp e.toMonoidHom : G →* G) = MonoidHom.id G := by
        ext x
        simp
      simp
    exact hMMap ▸ hback

/-- Forward direction of `pStable_iso`: `pStable p G` implies `pStable p G'` along a
group isomorphism `e : G ≃* G'`.  `M_p` membership transports (`MpSet_map_iff`), the
element is `M = M'.map e.symm`, and `pStableLocal` transports along the induced
isomorphism `↥M ≃* ↥M'` (`pStableLocal_iso`). -/
private theorem pStable_iso_forward {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G]
    [Group G'] (e : G ≃* G') : pStable p G → pStable p G' := by
  intro hstab M' hM'
  let M : Subgroup G := M'.map e.symm.toMonoidHom
  let eM : ↥M ≃* ↥M' := (M'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  have hMmem : M ∈ MpSet p G := by
    -- `M'.map e.symm = M` is in `MpSet p G` iff `M' ∈ MpSet p G'` (transport along `e`)
    have hiff := MpSet_map_iff (p := p) (e := e.symm) M'
    -- hiff : M' ∈ MpSet p G' ↔ M'.map e.symm.toMonoidHom ∈ MpSet p G
    have hback : M'.map e.symm.toMonoidHom ∈ MpSet p G := hiff.1 hM'
    simpa [M] using hback
  have hlocM : pStableLocal p (G := ↥M) := hstab M hMmem
  exact (pStableLocal_congr (p := p) (e := eM)).1 hlocM

/-- `pStable` (Definition 2.3) is invariant under group isomorphism. -/
public theorem pStable_iso {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') : pStable p G ↔ pStable p G' := by
  constructor
  · exact pStable_iso_forward e
  · exact pStable_iso_forward e.symm

end CFSG.Glauberman

