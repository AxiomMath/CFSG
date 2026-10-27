module

public import CFSG.Timmesfeld.Bridge.Asc72Defs

import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.OddTranspositions.PartThree.Ten.SetupPerfect

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

theorem widthOne_image_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {S : Set X}
    (h : WidthOne S) : WidthOne (e '' S) := by
  intro T
  let Q : Sylow 2 X := T.comapOfInjective (e : X →* Y) e.injective
    (by rw [MonoidHom.range_eq_top_of_surjective (e : X →* Y) e.surjective]; exact le_top)
  have hQT : (Q : Subgroup X).map (e : X →* Y) = (T : Subgroup Y) := by
    dsimp only [Q]
    rw [Sylow.coe_comapOfInjective]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨e.symm y, by
        change e (e.symm y) ∈ (T : Subgroup Y)
        simpa using hy, by simp⟩
  have hQTset : e '' (Q : Set X) = (T : Set Y) := by
    have h := congrArg (fun K : Subgroup Y => (K : Set Y)) hQT
    simpa [Subgroup.coe_map] using h
  have hInter : e '' (S ∩ (Q : Set X)) = (e '' S) ∩ (T : Set Y) := by
    rw [Set.image_inter e.injective, hQTset]
  calc
    ((e '' S) ∩ (T : Set Y)).ncard = (e '' (S ∩ (Q : Set X))).ncard := by rw [hInter]
    _ = (S ∩ (Q : Set X)).ncard := Set.ncard_image_of_injective _ e.injective
    _ = 1 := h Q

theorem widthOne_mk_image_mulEquiv {X Y : Type*} [Group X] [Group Y]
    {M : Subgroup X} [hMN : M.Normal] {M' : Subgroup Y} [hM'N : M'.Normal]
    (e : X ≃* Y) (he : M.map (e : X →* Y) = M') {E : Set X}
    (h : WidthOne (QuotientGroup.mk' M '' E)) :
    WidthOne (QuotientGroup.mk' M' '' (e '' E)) := by
  let QM : (X ⧸ M) ≃* (Y ⧸ M') := QuotientGroup.congr M M' e he
  have hQ : QM '' (QuotientGroup.mk' M '' E) = QuotientGroup.mk' M' '' (e '' E) := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, (QuotientGroup.congr_mk' M M' e he x).symm⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk' M x, ⟨x, hx, rfl⟩, QuotientGroup.congr_mk' M M' e he x⟩
  rw [← hQ]
  exact widthOne_image_mulEquiv QM h

theorem isOddTranspClass_conjSet_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {M : Subgroup X} {u : X} (h : IsOddTranspClass (conjSet M u)) :
    IsOddTranspClass (conjSet (M.map (e : X →* Y)) (e u)) := by
  classical
  let A : Subgroup X := M ⊔ Subgroup.zpowers u
  let B : Subgroup Y := M.map (e : X →* Y) ⊔ Subgroup.zpowers (e u)
  have hmap : A.map (e : X →* Y) = B := by
    change (M ⊔ Subgroup.zpowers u).map (e : X →* Y) =
      M.map (e : X →* Y) ⊔ Subgroup.zpowers (e u)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  let φ : A ≃* B := (MulEquiv.subgroupMap e A).trans (MulEquiv.subgroupCongr hmap)
  have hφ : ∀ x : A, ((φ.toMonoidHom x : B) : Y) = e (x : X) := by
    intro x
    change (MulEquiv.subgroupCongr hmap (MulEquiv.subgroupMap e A x) : Y) = e (x : X)
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply]
  have hset : (φ.toMonoidHom : A →* B) '' conjSet M u =
      conjSet (M.map (e : X →* Y)) (e u) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      simp only [conjSet] at hk ⊢
      obtain ⟨m, hm, hk⟩ := hk
      refine ⟨e m, Subgroup.mem_map_of_mem (e : X →* Y) hm, ?_⟩
      rw [hφ k, hk]
      simp only [map_mul, map_inv]
    · rintro ⟨m', hm', hy⟩
      simp only [Subgroup.mem_map] at hm' hy
      obtain ⟨m, hm, rfl⟩ := hm'
      refine ⟨⟨m * u * m⁻¹, ?_⟩, ⟨m, hm, rfl⟩, ?_⟩
      · have huA : u ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
        have hmA : m ∈ A := Subgroup.mem_sup_left hm
        exact A.mul_mem (A.mul_mem hmA huA) (A.inv_mem hmA)
      · apply Subtype.ext
        rw [hφ]
        simp only [map_mul, map_inv]
        exact hy.symm
  have hne : ∀ c ∈ conjSet M u, φ.toMonoidHom c ≠ 1 := by
    intro c hc hc1
    have hc2 : orderOf c = 2 := h.2.1.1 c hc
    have hc1' : c = 1 := φ.injective (by simpa using hc1)
    rw [hc1', orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hclass := CFSG.OddTranspositions.PartThree.isOddTranspClass_map
    φ.toMonoidHom φ.surjective h hne
  rwa [hset] at hclass

theorem AlmostSimpleCase.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {E : Set X}
    (h : AlmostSimpleCase X E) : AlmostSimpleCase Y (e '' E) := by
  classical
  obtain ⟨M, hMnorm, hmin, huniq, hsimple, hcent, hindex, hwidth, hodd⟩ := h
  let M' : Subgroup Y := M.map (e : X →* Y)
  have hM'norm : M'.Normal := hMnorm.map (e : X →* Y) e.surjective
  have hmin' : CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal M' := by
    change CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal (M.map e.toMonoidHom)
    rw [Subgroup.map_equiv_eq_comap_symm' e M]
    exact CFSG.OddTranspositions.IsMinimalNormal.comap_mulEquiv e.symm hmin
  have huniq' : ∀ N : Subgroup Y,
      CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal N → N = M' := by
    intro N hN
    have hN' : CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal (N.comap (e : X →* Y)) :=
      CFSG.OddTranspositions.IsMinimalNormal.comap_mulEquiv e hN
    have hNM : N.comap (e : X →* Y) = M := huniq _ hN'
    calc
      N = (N.comap (e : X →* Y)).map (e : X →* Y) :=
        (Subgroup.map_comap_eq_self_of_surjective e.surjective N).symm
      _ = M' := by rw [hNM]
  have hsimple' : IsSimpleGroup M' := by
    simpa [M'] using (MulEquiv.isSimpleGroup_congr (e.subgroupMap M)).mp hsimple
  have hcent' : Subgroup.centralizer (M' : Set Y) = ⊥ := by
    have h := CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e (M : Set X)
    rw [hcent, Subgroup.map_bot] at h
    simpa [M', Subgroup.coe_map] using h.symm
  have hindex' : 2 < M'.index := by
    change 2 < (M.map (e : X →* Y)).index
    rw [Subgroup.index_map_equiv M e]
    exact hindex
  have hodd' : ∀ u ∈ e '' E, IsOddTranspClass (conjSet M' u) := by
    rintro u ⟨u₀, hu₀, rfl⟩
    simpa [M'] using isOddTranspClass_conjSet_map e (hodd u₀ hu₀)
  exact ⟨M', hM'norm, hmin', huniq', hsimple', hcent', hindex',
    widthOne_mk_image_mulEquiv (M := M) (M' := M') (hMN := hMnorm)
      (hM'N := hM'norm) e rfl hwidth, hodd'⟩

end CFSG.Timmesfeld.Bridge.Asc72

end
