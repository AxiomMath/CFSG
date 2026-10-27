module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImages

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore map_centralizerPerfectCore)

section Swap

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} {e : L ≃* unitaryPSU h n} {t : G}
  {X : Subgroup G} {N : Finset (Fin n)}

namespace SwapNeighbourParam

theorem map_prod_eq_map_prod [Finite G] {X' : Subgroup G} {N' : Finset (Fin n)}
    (P : SwapNeighbourParam e t X N) (P' : SwapNeighbourParam e t X' N')
    {I : Finset (Fin n)} (hIN : I ⊆ N) (hIN' : I ⊆ N') (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (hXI' : X' ≤ modelToG e (unitaryBlockTorus h I)) :
    (((unitaryBlock h I).subgroupOf (unitaryBlock h N)).prod
        ((unitaryBlock h I).subgroupOf (unitaryBlock h N))).map P.Ψ =
      (((unitaryBlock h I).subgroupOf (unitaryBlock h N')).prod
        ((unitaryBlock h I).subgroupOf (unitaryBlock h N'))).map P'.Ψ := by
  rw [← P.pieceCore_eq_map hIN hI2 hIc hperf hXI, ← P'.pieceCore_eq_map hIN' hI2 hIc hperf hXI']

theorem map_prod_eq_map_prod_rootTorus [Finite G] {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (P : SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab)) ({a, b}ᶜ : Finset (Fin n)))
    (P' : SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hcd)) ({c, d}ᶜ : Finset (Fin n)))
    {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) (hI' : I ⊆ {c, d}ᶜ) (hI2 : 2 ≤ I.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I) :
    (((unitaryBlock h I).subgroupOf (unitaryBlock h {a, b}ᶜ)).prod
        ((unitaryBlock h I).subgroupOf (unitaryBlock h {a, b}ᶜ))).map P.Ψ =
      (((unitaryBlock h I).subgroupOf (unitaryBlock h {c, d}ᶜ)).prod
        ((unitaryBlock h I).subgroupOf (unitaryBlock h {c, d}ᶜ))).map P'.Ψ := by
  rw [← P.pieceCore_eq_map_rootTorus hab hI hI2 hperf,
    ← P'.pieceCore_eq_map_rootTorus hcd hI' hI2 hperf]

theorem conj [Finite G] (P : SwapNeighbourParam e t X N) (htC : t ∈ centralizer (L : Set G))
    (ρ : Equiv.Perm (Fin n)) :
    Nonempty (SwapNeighbourParam e t
      (X.map (MulAut.conj ((e.symm (unitaryProj h n (permSU h ρ.symm)) : L) : G)).toMonoidHom)
      (N.map ρ.toEmbedding)) := by
  set w₀ : unitarySU 2 f K n := permSU h ρ.symm with hw₀
  set w : G := ((e.symm (unitaryProj h n w₀) : L) : G) with hw
  have hmap : (unitaryBlock h N).map (MulAut.conj w₀).toMonoidHom =
      unitaryBlock h (N.map ρ.toEmbedding) :=
    map_conj_permSU_unitaryBlock h ρ N
  let β : unitaryBlock h N ≃* unitaryBlock h (N.map ρ.toEmbedding) :=
    ((unitaryBlock h N).equivMapOfInjective (MulAut.conj w₀).toMonoidHom
      (MulEquiv.injective _)).trans (MulEquiv.subgroupCongr hmap)
  have hβ : ∀ x, ((β x : unitaryBlock h (N.map ρ.toEmbedding)) : unitarySU 2 f K n) =
      w₀ * x * w₀⁻¹ := fun x => rfl
  set γ := β.symm with hγ
  have hγβ : ∀ y, w₀ * ((γ y : unitaryBlock h N) : unitarySU 2 f K n) * w₀⁻¹ = y := fun y => by
    rw [← hβ, hγ, MulEquiv.apply_symm_apply]
  let γγ := MulEquiv.prodCongr γ γ
  let Ψ' : unitaryBlock h (N.map ρ.toEmbedding) × unitaryBlock h (N.map ρ.toEmbedding) →* G :=
    (MulAut.conj w).toMonoidHom.comp (P.Ψ.comp γγ.toMonoidHom)
  have hΨ' : ∀ x y, Ψ' (x, y) = w * P.Ψ (γ x, γ y) * w⁻¹ := fun x y => rfl
  have hconj : ∀ y : unitarySU 2 f K n,
      w * ((e.symm (unitaryProj h n y) : L) : G) * w⁻¹ =
        ((e.symm (unitaryProj h n (w₀ * y * w₀⁻¹)) : L) : G) := fun y => by
    simp only [hw, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨⟨Ψ', ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    have hs : (P.Ψ.comp γγ.toMonoidHom).range = P.Ψ.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective γγ),
        ← MonoidHom.range_eq_map]
    rw [MonoidHom.range_comp, hs, P.range_eq, map_centralizerPerfectCore]
  ·
    intro y hy
    have h1 : P.Ψ (γγ y) = 1 := (MulEquiv.map_eq_one_iff (MulAut.conj w)).1 hy
    have hz := P.ker_le h1
    rw [mem_center_iff] at hz ⊢
    intro z
    apply γγ.injective
    rw [map_mul, map_mul, hz (γγ z)]
  ·
    intro x
    rw [hΨ', P.diag, hconj, hγβ]
  ·
    intro c _ x
    obtain ⟨x₁, x₂⟩ := x
    set c' := unitaryPermParam h ρ.symm c with hc'
    have hcc : unitaryPermParam h ρ c' = c := unitaryPermParam_unitaryPermParam_symm h ρ c
    have hd : w₀ * torusDiagSU h c' * w₀⁻¹ = torusDiagSU h c := by
      rw [hw₀, permSU_mul_torusDiagSU, hcc]
    have hβγ : ∀ z, β (γ z) = z := fun z => β.apply_symm_apply z
    have hγc : ∀ y, γ (conjTorusSU h (N.map ρ.toEmbedding) c y) = conjTorusSU h N c' (γ y) := by
      intro y
      apply β.injective
      rw [hβγ]
      apply Subtype.ext
      rw [hβ, coe_conjTorusSU_apply, coe_conjTorusSU_apply, ← hd]
      conv_lhs => rw [← hγβ y]
      group
    have hw' : w * ((e.symm (unitaryProj h n (torusDiagSU h c')) : L) : G) * w⁻¹ =
        ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) := by
      rw [hconj, hd]
    show Ψ' (conjTorusSU h (N.map ρ.toEmbedding) c x₁, conjTorusSU h (N.map ρ.toEmbedding) c x₂) =
      ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) * Ψ' (x₁, x₂) *
        ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G)⁻¹
    have hN2 := P.N2 c' c'.2 (γ x₁, γ x₂)
    rw [hΨ', hΨ', hγc, hγc]
    change w * P.Ψ (conjTorusSU h N c' (γ x₁, γ x₂).1, conjTorusSU h N c' (γ x₁, γ x₂).2) * w⁻¹ = _
    rw [hN2, ← hw']
    group
  ·
    intro x y
    have htw : t * w = w * t := (mem_centralizer_iff.1 htC w (e.symm _).2).symm
    rw [hΨ', hΨ']
    calc t * (w * P.Ψ (γ x, γ y) * w⁻¹) * t⁻¹ = (t * w) * P.Ψ (γ x, γ y) * (t * w)⁻¹ := by group
      _ = (w * t) * P.Ψ (γ x, γ y) * (w * t)⁻¹ := by rw [htw]
      _ = w * (t * P.Ψ (γ x, γ y) * t⁻¹) * w⁻¹ := by group
      _ = w * P.Ψ (γ y, γ x) * w⁻¹ := by rw [P.swap]

end SwapNeighbourParam

theorem nonempty_swapNeighbourParam_rootTorus_of_nonempty [Finite G]
    (htC : t ∈ centralizer (L : Set G)) {a b : Fin n} (hab : a ≠ b)
    (hP : Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n))))
    {a' b' : Fin n} (hab' : a' ≠ b') :
    Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab'))
      ({a', b'}ᶜ : Finset (Fin n))) := by
  obtain ⟨P⟩ := hP
  obtain ⟨ρ, rfl, rfl⟩ := LinearPilot.exists_perm_apply_eq_apply_eq hab hab'
  have hX : (modelToG e (unitaryRootTorus h hab)).map
      (MulAut.conj ((e.symm (unitaryProj h n (permSU h ρ.symm)) : L) : G)).toMonoidHom =
        modelToG e (unitaryRootTorus h hab') := by
    rw [← modelToG_map_conj, map_conj_unitaryRootTorus h ρ hab]
  have hP' := P.conj htC ρ
  rw [hX, map_compl_pair] at hP'
  exact hP'

end Swap

end CFSG.SeitzReduction.UnitaryPilot
