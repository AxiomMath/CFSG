module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommPrincipalLayersCore

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace PrincipalLayers

open Subgroup TorusLayer CFSG.RankThree.PartOne.KCRootAxis
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedSU StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped MatrixGroups

variable {F : Type} [Group F] [Finite F] {K : Type} [Field K] {n : ℕ}
  {S J Y V U : Subgroup F} {t : F} {hk : SL₂ K → F}

set_option quotPrecheck false in
local notation "𝐑" => CFSG.Open.standardComponentOddCore F
set_option quotPrecheck false in
local notation "θ" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)
set_option quotPrecheck false in
local notation "𝐃" => normalClosure ((S.map (QuotientGroup.mk'
  (CFSG.Open.standardComponentOddCore F)) : Subgroup (F ⧸ CFSG.Open.standardComponentOddCore F)) :
    Set (F ⧸ CFSG.Open.standardComponentOddCore F))

namespace AxisData

theorem comp_restrict_eq_iff (h : AxisData F K n S J Y V U t hk) {P : Type*} [Group P]
    (η : ↥𝐃 ≃* P) (y : Y) (z : P) :
    θ (y : F) = (η.symm z : F ⧸ 𝐑) ↔ (η.toMonoidHom.comp (restrictTo θ h.map_Y)) y = z := by
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MulEquiv.eq_symm_apply, Subtype.ext_iff,
    coe_restrictTo]

theorem comp_restrict_facts (h : AxisData F K n S J Y V U t hk) {P : Type*} [Group P]
    (η : ↥𝐃 ≃* P) :
    Function.Surjective (η.toMonoidHom.comp (restrictTo θ h.map_Y)) ∧
      (η.toMonoidHom.comp (restrictTo θ h.map_Y)).ker = center ↥Y ∧
      (η.toMonoidHom.comp (restrictTo θ h.map_Y)).ker ≤ center ↥Y ∧
      Odd (Nat.card (η.toMonoidHom.comp (restrictTo θ h.map_Y)).ker) := by
  have hk' : (η.toMonoidHom.comp (restrictTo θ h.map_Y)).ker = center ↥Y := by
    rw [MonoidHom.ker_comp_of_injective (restrictTo θ h.map_Y) η.toMonoidHom η.injective,
      h.ker_restrict]
  exact ⟨η.surjective.comp (restrictTo_surjective h.map_Y), hk', hk'.le,
    hk' ▸ h.odd_card_center⟩

theorem cover_linear
    (h : AxisData F K n S J Y V U t hk) {m : ℕ} {F' : Type}
    [Field F'] [Finite F'] (hF' : Nat.card F' = 2 ^ m) (η : ↥𝐃 ≃* StatedProj (StatedSL 3 F')) :
    let Z := (StatedScalars (Fin 3) F').subgroupOf (StatedSL 3 F')
    let π : ↥(StatedSL 3 F') →* StatedProj (StatedSL 3 F') := QuotientGroup.mk' Z
    ∃ γ : ↥(StatedSL 3 F') →* ↥Y, (∀ x, θ (γ x : F) = (η.symm (π x) : F ⧸ 𝐑)) ∧
      (∀ γ' : ↥(StatedSL 3 F') →* ↥Y, (∀ x, θ (γ' x : F) = (η.symm (π x) : F ⧸ 𝐑)) →
        γ' = γ) ∧
      Function.Surjective γ ∧ γ.ker ≤ Z ∧ Z.map γ = center ↥Y ∧
      (∃ e : ↥(StatedSL 3 F') ⧸ γ.ker ≃* ↥Y, ∀ x, e (QuotientGroup.mk x) = γ x) ∧
      IsCyclic (center ↥Y) ∧ Nat.card (center ↥Y) ∣ Nat.gcd 3 (Nat.card F' - 1) := by
  intro Z π
  have : CharP F' 2 := charP_two_of_card hF'
  have : Group.IsPerfect ↥Y := h.perfect
  obtain ⟨hρs, hρk, hcen, hodd⟩ := h.comp_restrict_facts η
  set ρ := η.toMonoidHom.comp (restrictTo θ h.map_Y)
  obtain ⟨hZc, hZd⟩ := scalars_statedSL_three (F := F')
  have hπk : π.ker = Z := QuotientGroup.ker_mk' Z
  have : IsCyclic (QuotientGroup.mk' Z).ker := by rw [QuotientGroup.ker_mk']; exact hZc
  have hZd' : Nat.card (QuotientGroup.mk' Z).ker ∣ Nat.gcd 3 (Nat.card F' - 1) := by
    rw [QuotientGroup.ker_mk']; exact hZd
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (σ : E →* ↥(StatedSL 3 F')),
      Function.Surjective σ → σ.ker ≤ center E → Odd (Nat.card σ.ker) →
        ∃! s : ↥(StatedSL 3 F') →* E, ∀ x, σ (s x) = x := by
    intro E _ _ σ hσ hσc hσo
    obtain ⟨s, hs, hu⟩ :=
      CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated (n := 3)
        (by norm_num) hσ hσc hσo
    exact ⟨s, hs, fun τ hτ => hu τ hτ⟩
  obtain ⟨γ, hγ, huniq, hsurj, hker, hmap, ⟨e, he⟩, hcyc, -, hdvd⟩ :=
    CFSG.ShultStronglyClosedTI.PerfectOddCover.perfect_odd_cover_of_split hsplit
      (QuotientGroup.mk'_surjective Z) hZd' hρs hcen hodd
  have key : ∀ γ' : ↥(StatedSL 3 F') →* ↥Y,
      (∀ x, θ (γ' x : F) = (η.symm (π x) : F ⧸ 𝐑)) ↔ ρ.comp γ' = π := fun γ' =>
    ⟨fun h1 => MonoidHom.ext fun x => (h.comp_restrict_eq_iff η _ _).mp (h1 x),
      fun h1 x => (h.comp_restrict_eq_iff η _ _).mpr (DFunLike.congr_fun h1 x)⟩
  refine ⟨γ, (key γ).mpr hγ, fun γ' hγ' => huniq γ' ((key γ').mp hγ'), hsurj, hπk ▸ hker, ?_,
    ⟨e, fun x => (he x).1⟩, hρk ▸ hcyc, hρk ▸ hdvd⟩
  rw [← hπk, hmap, hρk]

theorem cover_unitary
    (h : AxisData F K n S J Y V U t hk) {F' : Type} [Field F']
    (hF' : UnitaryFieldData 2 n F') (η : ↥𝐃 ≃* StatedProj (StatedSU 3 (2 ^ n) F')) :
    let Z := (StatedScalars (Fin 3) F').subgroupOf (StatedSU 3 (2 ^ n) F')
    let π : ↥(StatedSU 3 (2 ^ n) F') →* StatedProj (StatedSU 3 (2 ^ n) F') :=
      QuotientGroup.mk' Z
    ∃ γ : ↥(StatedSU 3 (2 ^ n) F') →* ↥Y, (∀ x, θ (γ x : F) = (η.symm (π x) : F ⧸ 𝐑)) ∧
      (∀ γ' : ↥(StatedSU 3 (2 ^ n) F') →* ↥Y,
        (∀ x, θ (γ' x : F) = (η.symm (π x) : F ⧸ 𝐑)) → γ' = γ) ∧
      Function.Surjective γ ∧ γ.ker ≤ Z ∧ Z.map γ = center ↥Y ∧
      (∃ e : ↥(StatedSU 3 (2 ^ n) F') ⧸ γ.ker ≃* ↥Y, ∀ x, e (QuotientGroup.mk x) = γ x) ∧
      IsCyclic (center ↥Y) ∧ Nat.card (center ↥Y) ∣ Nat.gcd 3 (2 ^ n + 1) := by
  intro Z π
  have := hF'.finite
  have : Group.IsPerfect ↥Y := h.perfect
  obtain ⟨hρs, hρk, hcen, hodd⟩ := h.comp_restrict_facts η
  set ρ := η.toMonoidHom.comp (restrictTo θ h.map_Y)
  obtain ⟨-, γ, hγ, huniq, hsurj, hker, hmap, ⟨e, he⟩, hcyc, -, hdvd, -⟩ :=
    CFSG.ShultStronglyClosedTI.PerfectOddCover.perfect_odd_cover_unitary_scalarQuotient
      (K := F') n h.two_le hF'.card (L := ↥Y) ρ hρs hcen hodd
  have key : ∀ γ' : ↥(StatedSU 3 (2 ^ n) F') →* ↥Y,
      (∀ x, θ (γ' x : F) = (η.symm (π x) : F ⧸ 𝐑)) ↔ ρ.comp γ' = π := fun γ' =>
    ⟨fun h1 => MonoidHom.ext fun x => (h.comp_restrict_eq_iff η _ _).mp (h1 x),
      fun h1 x => (h.comp_restrict_eq_iff η _ _).mpr (DFunLike.congr_fun h1 x)⟩
  refine ⟨γ, (key γ).mpr hγ, fun γ' hγ' => huniq γ' ((key γ').mp hγ'), hsurj, hker, ?_,
    ⟨e, fun x => (he x).1⟩, hρk ▸ hcyc, hρk ▸ hdvd⟩
  exact hmap.trans hρk

theorem nontrivialAxisConclusion
    (h : AxisData F K n S J Y V U t hk) {W : Subgroup F}
    (hWV : W ≤ V) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hUW : U ≤ W)
    (hWU : ∀ w ∈ W, w * w ∈ U) (hW1 : ∃ w ∈ W, w * w ≠ 1) (hV3 : Nat.card V = (2 ^ n) ^ 3) :
    NontrivialAxisConclusion F K n S Y V t := by
  obtain ⟨hodd, heven⟩ := h.not_psl_two_of_nontrivial hWV hWc hUW hWU hW1
  refine ⟨hodd, heven, h.three_of_nontrivial hV3, ⟨fun y => h.mem_center_iff.symm,
    h.facts.2.2.2.2.2.2.2.1, h.facts.2.2.2.2.2.2.2.2.1⟩, fun m F' _ _ hF' η => ?_,
    fun m F' _ hF' η => ?_⟩
  · intro Z π
    obtain ⟨hmn, hSb, -, hH, -⟩ := h.linear_three hF' η
    obtain ⟨γ, hγ1, hγ2, hγ3, hγ4, hγ5, hγ6, hγ7, hγ8⟩ := h.cover_linear hF' η
    rw [hF', hmn] at hγ8
    exact ⟨hmn, hSb, hH, γ, hγ1, hγ2, hγ3, hγ4, hγ5, hγ6, hγ7, hγ8⟩
  · intro Z π
    obtain ⟨hmn, hSb, -, hH, -⟩ := h.unitary_three hF' η
    subst hmn
    obtain ⟨γ, hγ1, hγ2, hγ3, hγ4, hγ5, hγ6, hγ7, hγ8⟩ := h.cover_unitary hF' η
    exact ⟨rfl, hSb, hH, γ, hγ1, hγ2, hγ3, hγ4, hγ5, hγ6, hγ7, hγ8⟩

end AxisData

end PrincipalLayers

end CFSG.LocalAnalysis.SymplecticFourStandard
