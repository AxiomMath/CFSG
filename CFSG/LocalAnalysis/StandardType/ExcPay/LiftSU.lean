module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.StandardType.ExcPay.LiftRefl
import CFSG.LieType.Steinberg.CentralExt.SUOddCover
import CFSG.LocalAnalysis.StandardType.GGFixedTwoKernelTransport
import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
import CFSG.ClassicalInvolution.RouteD.LocalPair
import CFSG.RankThree.PartOne.CTP.Phan5Cent
import CFSG.ClassicalInvolution.Phan.Assembly
import CFSG.ClassicalInvolution.Phan.Universal
import CFSG.ClassicalInvolution.WeakCT.SpPair
import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartOne.CTP.ExtPhan

public section

namespace CFSG.StandardType.ExcPay

open CFSG.ClassicalInvolution.Phan CFSG.StandardType CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg


private theorem excPayU_block_eq {G H : Type} [Group G] [Group H] [Finite G]
    {X : Subgroup G} (η : ↥X →* H) (hker : η.ker ≤ Subgroup.center ↥X)
    (hodd : Odd (Nat.card η.ker)) {C P : Subgroup ↥X} (hP : P ≤ ⁅P, P⁆)
    (hmap : P.map η = (ggOTwoPrime C).map η) : P = ggOTwoPrime C := by
  refine le_antisymm ?_ ?_
  · have hle : P ≤ ggOTwoPrime C ⊔ η.ker := by
      intro p hp
      have hp' : η p ∈ P.map η := Subgroup.mem_map_of_mem η hp
      rw [hmap] at hp'
      have hpc : p ∈ ((ggOTwoPrime C).map η).comap η := hp'
      rwa [Subgroup.comap_map_eq] at hpc
    exact CFSG.ClassicalInvolution.RouteD.le_of_perfect_of_le_sup_center hker hP hle
  · exact CFSG.StandardType.ggOTwoPrime_le_of_map_le_map_of_central_odd_kernel
      η hker hodd C P hmap.ge

private theorem excPayU_ggOTwoPrime_subgroupOf {G : Type} [Group G]
    {X Y : Subgroup G} (hY : Y ≤ X) :
    (ggOTwoPrime Y).subgroupOf X = ggOTwoPrime (Y.subgroupOf X) := by
  apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
  calc
    ((ggOTwoPrime Y).subgroupOf X).map X.subtype = ggOTwoPrime Y ⊓ X :=
      Subgroup.subgroupOf_map_subtype _ _
    _ = ggOTwoPrime Y := inf_eq_left.mpr ((ggOTwoPrime_le Y).trans hY)
    _ = ggOTwoPrime (Y ⊓ X) := by rw [inf_eq_left.mpr hY]
    _ = ggOTwoPrime ((Y.subgroupOf X).map X.subtype) := by
      rw [Subgroup.subgroupOf_map_subtype]
    _ = (ggOTwoPrime (Y.subgroupOf X)).map X.subtype :=
      (CFSG.StandardType.ggOTwoPrime_map_of_injective (H := ↥X) (G := G)
        X.subtype X.subtype_injective (Y.subgroupOf X)).symm

private theorem excPayU_pi_kernel {G H : Type} [Group G] [Group H] [Finite G]
    {X : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (η : ↥X →* H) (hker : η.ker ≤ Subgroup.center ↥X)
    (hodd : Odd (Nat.card η.ker)) {W : Subgroup ↥X} {π : W →* Su F 2 f 3}
    (hπker : π.ker = η.ker.comap W.subtype) :
    π.ker ≤ Subgroup.center W ∧ Odd (Nat.card π.ker) := by
  constructor
  · intro w hw
    rw [Subgroup.mem_center_iff]
    intro v
    have hwη : (w : ↥X) ∈ η.ker := by
      rw [hπker] at hw
      exact Subgroup.mem_comap.mp hw
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hwη) (v : ↥X))
  · rw [hπker]
    exact hodd.of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective η.ker W.subtype W.subtype_injective)

private theorem excPayU_section_to_X {G H : Type} [Group G] [Group H]
    {X : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (η : ↥X →* H) {θY : Su F 2 f 3 →* H} {W : Subgroup ↥X}
    (ηW : W →* θY.range) (eθ : Su F 2 f 3 ≃* θY.range)
    (hηW : ∀ w, (ηW w : H) = η (w : ↥X))
    (hθYe : ∀ g, (eθ g : H) = θY g) (s0 : Su F 2 f 3 →* W)
    (hs0 : ∀ g, eθ.symm (ηW (s0 g)) = g) :
    ∃ s' : Su F 2 f 3 →* ↥X, ∀ g, η (s' g) = θY g := by
  let s' : Su F 2 f 3 →* ↥X := W.subtype.comp s0
  refine ⟨s', ?_⟩
  intro g
  have h2 : ηW (s0 g) = eθ g := by
    apply eθ.symm.injective
    rw [hs0 g]
    exact (eθ.symm_apply_apply g).symm
  calc
    η (s' g) = (ηW (s0 g) : H) := (hηW (s0 g)).symm
    _ = (eθ g : H) := congrArg Subtype.val h2
    _ = θY g := hθYe g

private theorem excPayU_section {G H : Type} [Group G] [Group H] [Finite G]
    {X : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (η : ↥X →* H)
    (hη : Function.Surjective η) (hker : η.ker ≤ Subgroup.center ↥X)
    (hodd : Odd (Nat.card η.ker)) (θY : Su F 2 f 3 →* H)
    (hθY : Function.Injective θY)
    (e : Su F 2 f 3 ≃* SU (unitaryInvolution F 2 f) 3) :
    ∃ s' : Su F 2 f 3 →* ↥X, ∀ g, η (s' g) = θY g := by
  let W : Subgroup ↥X := (θY.range).comap η
  let ηW : W →* θY.range := (η.comp W.subtype).codRestrict θY.range fun w => w.2
  have hηW : Function.Surjective ηW := by
    intro y
    obtain ⟨x, hx⟩ := hη (y : H)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    rw [Subgroup.mem_comap, hx]
    exact y.2
  let eθ : Su F 2 f 3 ≃* θY.range := MonoidHom.ofInjective hθY
  let π : W →* Su F 2 f 3 := eθ.symm.toMonoidHom.comp ηW
  have hπ : Function.Surjective π := eθ.symm.surjective.comp hηW
  have hπker : π.ker = η.ker.comap W.subtype := by
    rw [show π = eθ.symm.toMonoidHom.comp ηW from rfl,
      MonoidHom.ker_comp_of_injective ηW eθ.symm.toMonoidHom eθ.symm.injective]
    change ((η.comp W.subtype).codRestrict θY.range (fun w => w.2)).ker
      = η.ker.comap W.subtype
    calc
      ((η.comp W.subtype).codRestrict θY.range (fun w => w.2)).ker
          = (η.comp W.subtype).ker := MonoidHom.ker_codRestrict _ _ _
      _ = η.ker.comap W.subtype := (MonoidHom.comap_ker η W.subtype).symm
  obtain ⟨hkerπ, hoddπ⟩ := excPayU_pi_kernel η hker hodd hπker
  let π' : W →* SU (unitaryInvolution F 2 f) 3 := e.toMonoidHom.comp π
  have hπ' : Function.Surjective π' := e.surjective.comp hπ
  have hkerπ' : π'.ker = π.ker := MonoidHom.ker_mulEquiv_comp π e
  have hcen' : π'.ker ≤ Subgroup.center W := by
    rw [hkerπ']
    exact hkerπ
  have hodd' : Odd (Nat.card π'.ker) := by
    rw [hkerπ']
    exact hoddπ
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUOdd.su_three_even_exists_section_of_odd
      (F := F) (f := f) hF hf hπ' hcen' hodd'
  let s0 : Su F 2 f 3 →* W := s.comp e.toMonoidHom
  have hs0 : ∀ g, eθ.symm (ηW (s0 g)) = g := by
    intro g
    change π (s0 g) = g
    exact e.injective (by simpa [s0, π'] using hs (e g))
  exact excPayU_section_to_X η ηW eθ (fun w => rfl) (fun g => rfl) s0 hs0

private theorem excPayU_blocks_perfect {G : Type} [Group G] {F : Type} [Field F]
    [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (s' : Su F 2 f 3 →* G) :
    (B12 F 2 f).map s' ≤ ⁅(B12 F 2 f).map s', (B12 F 2 f).map s'⁆ ∧
      (B23 F 2 f).map s' ≤ ⁅(B23 F 2 f).map s', (B23 F 2 f).map s'⁆ := by
  have hsu2 : Group.IsPerfect (Su F 2 f 2) :=
    CFSG.RankThree.PartOne.CTP.isPerfect_su_two (K := F) (f := f) hF hf
  have hperf : ∀ φ : Su F 2 f 2 →* G, φ.range ≤ ⁅φ.range, φ.range⁆ := by
    intro φ
    exact (Subgroup.isPerfect_iff.mp
      (@Group.IsPerfect.range (Su F 2 f 2) G _ _ φ hsu2)).ge
  constructor
  · have h := hperf (s'.comp (embSUid (unitaryInvolution F 2 f) 2))
    simpa [B12, MonoidHom.range_comp] using h
  · have h := hperf (s'.comp (embSUid (unitaryInvolution F 2 f) 0))
    simpa [B23, MonoidHom.range_comp] using h

private theorem excPayU_map_eq_of_block {G H : Type} [Group G] [Group H]
    {X : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {η : ↥X →* H} {θY : Su F 2 f 3 →* H} {s' : Su F 2 f 3 →* ↥X}
    (hθYs' : θY = η.comp s') {C : Subgroup (Su F 2 f 3)} {Y : Subgroup G}
    (hY : Y ≤ X) (h : C.map θY = ((ggOTwoPrime Y).subgroupOf X).map η) :
    (C.map s').map η = (ggOTwoPrime (Y.subgroupOf X)).map η := by
  rw [Subgroup.map_map, ← hθYs', h, excPayU_ggOTwoPrime_subgroupOf hY]

private theorem excPayU_map_block_eq {G : Type} [Group G] {X : Subgroup G}
    {Y : Subgroup G} (hY : Y ≤ X) {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (C : Subgroup (Su F 2 f 3)) (s' : Su F 2 f 3 →* ↥X)
    (hblock : C.map s' = ggOTwoPrime (Y.subgroupOf X)) :
    C.map (X.subtype.comp s') = ggOTwoPrime Y := by
  rw [← Subgroup.map_map, hblock, ← excPayU_ggOTwoPrime_subgroupOf hY,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr ((ggOTwoPrime_le Y).trans hY)]

theorem excPayL_lift_su3 {G H : Type} [Group G] [Group H] [Finite G] {X : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) (η : ↥X →* H) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center ↥X) (hodd : Odd (Nat.card η.ker))
    {Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X)
    (θY : Su F 2 f 3 →* H) (hθY : Function.Injective θY)
    (h12 : (B12 F 2 f).map θY = ((ggOTwoPrime Y).subgroupOf X).map η)
    (h23 : (B23 F 2 f).map θY = ((ggOTwoPrime Y').subgroupOf X).map η) :
    ∃ θG : Su F 2 f 3 →* G, Function.Injective θG ∧ θG.range ≤ X ∧
      (B12 F 2 f).map θG = ggOTwoPrime Y ∧ (B23 F 2 f).map θG = ggOTwoPrime Y' := by
  classical
  let e : Su F 2 f 3 ≃* SU (unitaryInvolution F 2 f) 3 :=
    (MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) hF 3)).trans
      (CFSG.LieType.Universal.Unitary.equivStatedSU (p := 2) hF 3).symm
  obtain ⟨s', hηs'⟩ := excPayU_section hF hf η hη hker hodd θY hθY e
  let θG : Su F 2 f 3 →* G := X.subtype.comp s'
  have hθGinj : Function.Injective θG := by
    intro g h hgh
    have h1 : s' g = s' h := Subtype.ext hgh
    have h2 : η (s' g) = η (s' h) := congrArg η h1
    rw [hηs' g, hηs' h] at h2
    exact hθY h2
  have hθGX : θG.range ≤ X := by
    rintro _ ⟨g, rfl⟩
    exact (s' g).2
  obtain ⟨hP12, hP23⟩ := excPayU_blocks_perfect hF hf s'
  have hθYs' : θY = η.comp s' := MonoidHom.ext fun g => (hηs' g).symm
  have hmap12 := excPayU_map_eq_of_block hθYs' hY h12
  have hmap23 := excPayU_map_eq_of_block hθYs' hY' h23
  have hblock12 : (B12 F 2 f).map s' = ggOTwoPrime (Y.subgroupOf X) :=
    excPayU_block_eq η hker hodd hP12 hmap12
  have hblock23 : (B23 F 2 f).map s' = ggOTwoPrime (Y'.subgroupOf X) :=
    excPayU_block_eq η hker hodd hP23 hmap23
  exact ⟨θG, hθGinj, hθGX,
    excPayU_map_block_eq hY (B12 F 2 f) s' hblock12,
    excPayU_map_block_eq hY' (B23 F 2 f) s' hblock23⟩

end CFSG.StandardType.ExcPay
