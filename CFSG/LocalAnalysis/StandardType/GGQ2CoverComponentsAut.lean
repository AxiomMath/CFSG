module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRealizationStatements
import CFSG.LocalAnalysis.StandardType.GGQ2CoverComponents

public section

namespace CFSG.StandardType.GGQ2Frame.CoverComponents

open CFSG CFSG.Assembly CFSG.StandardType
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private theorem gcca_mulAut_fixes_comap_commutator {G : Type} [Group G]
    {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* MulAut R)
    (hker : π.ker ≤ Subgroup.center ↥H) (hEq : EquivariantAut hAN π ρ)
    {Y : Subgroup R} (hYle : Y ≤ fixedSub ρ)
    (a : ↥A) {z : ↥H} (hz : z ∈ ⁅Y.comap π, Y.comap π⁆) :
    H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ z = z := by
  refine mulAut_fixes_commutator (H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩)
    (Y.comap π) ?_ z hz
  intro q hq
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  have hqY : π q ∈ Y := Subgroup.mem_comap.mp hq
  have hc : ρ a (π q) = π q := (mem_fixedSub.mp (hYle hqY)) a
  have hφq : π (H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ q) = π q := by
    rw [hEq a q, hc]
  rw [hφq, mul_inv_cancel]

theorem mapCentralizerEqAut_holds :
    ∀ {G : Type} [Group G] [Finite G] {H A : Subgroup G} {R : Type} [Group R]
      (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* MulAut R),
      IsPGroup 3 A → Function.Surjective π → ¬ 3 ∣ Nat.card π.ker → EquivariantAut hAN π ρ →
      ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H).map π = fixedSub ρ := by
  intro G _ _ H A R _ hAN π ρ hA hπ hker hEq
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨h, hh, rfl⟩ := hy
    rw [mem_fixedSub]
    intro a
    have hhA : (h : G) ∈ Subgroup.centralizer (A : Set G) :=
      (Subgroup.mem_subgroupOf.mp hh).2
    have hacomm : (a : G) * (h : G) = (h : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hhA a a.2
    have hconj : H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ h = h := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe, hacomm]
      group
    rw [← hEq a h, hconj]
  · intro y hy
    rw [mem_fixedSub] at hy
    obtain ⟨h₀, hh₀⟩ := hπ y
    let fiber := {h : ↥H // π h = y}
    let φ : ↥A →* MulAut ↥H := H.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
    have hφ_apply : ∀ (a : ↥A) (h : ↥H),
        φ a h = H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ h := fun _ _ => rfl
    have hφ_coe : ∀ (a : ↥A) (h : ↥H),
        ((φ a h : ↥H) : G) = (a : G) * (h : G) * (a : G)⁻¹ := by
      intro a h
      rw [hφ_apply a h, normalizerMonoidHom_coe]
    have hact_mem : ∀ (a : ↥A) {h : ↥H}, π h = y → π (φ a h) = y := by
      intro a h hh
      rw [hφ_apply a h, hEq a h, hh]
      exact hy a
    let fiberAction : MulAction ↥A fiber :=
      { smul := fun a h => ⟨φ a h.1, hact_mem a h.2⟩
        one_smul := by
          intro h
          apply Subtype.ext
          show φ 1 h.1 = h.1
          rw [map_one]
          rfl
        mul_smul := by
          intro a b h
          apply Subtype.ext
          show φ (a * b) h.1 = φ a (φ b h.1)
          rw [map_mul]
          rfl }
    have hcard : Nat.card fiber = Nat.card π.ker := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun h => ⟨h₀⁻¹ * h.1, ?_⟩
          invFun := fun k => ⟨h₀ * k.1, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hh₀, h.2]
        group
      · rw [map_mul, hh₀, MonoidHom.mem_ker.mp k.2, mul_one]
      · intro h
        apply Subtype.ext
        show h₀ * (h₀⁻¹ * h.1) = h.1
        group
      · intro k
        apply Subtype.ext
        show h₀⁻¹ * (h₀ * k.1) = k.1
        group
    have hcard3 : ¬ 3 ∣ Nat.card fiber := by rw [hcard]; exact hker
    obtain ⟨h, hhfix⟩ :=
      IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hA fiber hcard3
    refine Subgroup.mem_map.mpr ⟨h.1, ?_, h.2⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨h.1.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro g hg
    let a : ↥A := ⟨g, hg⟩
    have hfixa : φ a h.1 = h.1 := congrArg Subtype.val (hhfix a)
    have hcoe : (a : G) * (h.1 : G) = (h.1 : G) * (a : G) := by
      have hc := hφ_coe a h.1
      rw [hfixa] at hc
      exact mul_inv_eq_iff_eq_mul.mp hc.symm
    simpa using hcoe

private theorem gcca_exists_component_of_isComponentOf {G : Type} [Group G] [Finite G]
    {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* MulAut R)
    (hA : IsPGroup 3 A) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (_hHperf : commutator H = ⊤) (hEq : EquivariantAut hAN π ρ)
    {X : Subgroup G} (hX : IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G))) :
    ∃ Y : Subgroup R, IsComponentOf Y (fixedSub ρ) ∧
        X = (⁅Y.comap π, Y.comap π⁆).map H.subtype := by
  obtain ⟨hXle, hXsub, hXq⟩ := hX
  have hXH : X ≤ H := hXle.trans inf_le_left
  let X' : Subgroup ↥H := X.subgroupOf H
  let Y : Subgroup R := X'.map π
  have hmapC : ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H).map π = fixedSub ρ :=
    mapCentralizerEqAut_holds hAN π ρ hA hπ hker3 hEq
  have hXnat : CFSG.IsQuasisimple ↥X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥X).mp hXq
  have hX'nat : CFSG.IsQuasisimple ↥X' :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hXH)).mpr hXnat
  have : Group.IsPerfect ↥X' := hX'nat.1
  have hX'le : X' ≤ Y.comap π := Subgroup.map_le_iff_le_comap.mp le_rfl
  have hZeq : ⁅Y.comap π, Y.comap π⁆ = X' := by
    rw [commutator_comap_eq π hker (le_rfl : Y ≤ X'.map π),
      inf_eq_right.mpr hX'le, Subgroup.commutator_eq_self]
  refine ⟨Y, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hmapC]
    exact Subgroup.map_mono (fun x hx => by
      rw [Subgroup.mem_subgroupOf]; exact hXle hx)
  · have hsub' : IsSubnormal X'
        ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H) := by
      simpa only [X', Subgroup.comap_subtype] using
        IsSubnormal.comap H.subtype hXsub
    have h := IsSubnormal.map π hsub'
    rwa [hmapC] at h
  · have hnot : ¬ X' ≤ π.ker := by
      intro hle
      have : Nontrivial (↥X' ⧸ Subgroup.center ↥X') := hX'nat.2.1.toNontrivial
      have : Nontrivial ↥X' := (QuotientGroup.mk'_surjective (Subgroup.center ↥X')).nontrivial
      have : IsMulCommutative ↥X' :=
        IsMulCommutative.of_comm fun (a b : ↥X') =>
          Subtype.ext_iff.mpr (by
            rw [Subgroup.coe_mul, Subgroup.coe_mul]
            exact (Subgroup.mem_center_iff.mp (hker (hle a.2)) (b : ↥H)).symm)
      exact Group.IsPerfect.not_isMulCommutative (G := ↥X') inferInstance
    have hYnat : CFSG.IsQuasisimple ↥Y :=
      CFSG.LocalCores.isQuasisimple_map hX'nat π hnot
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Y).mpr hYnat
  · rw [hZeq, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show X ≤ H from hXH)]

private theorem gcca_isComponentOf_commutator_comap {G : Type} [Group G] [Finite G]
    {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* MulAut R)
    (hA : IsPGroup 3 A) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (_hHperf : commutator H = ⊤) (hEq : EquivariantAut hAN π ρ)
    {Y : Subgroup R} (hY : IsComponentOf Y (fixedSub ρ)) :
    IsComponentOf ((⁅Y.comap π, Y.comap π⁆).map H.subtype)
      (H ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨hYle, hYsub, hYq⟩ := hY
  have hYnat : CFSG.IsQuasisimple ↥Y :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Y).mp hYq
  let C : Subgroup G := H ⊓ Subgroup.centralizer (A : Set G)
  let C' : Subgroup ↥H := C.subgroupOf H
  have hC'map : C'.map π = fixedSub ρ :=
    mapCentralizerEqAut_holds hAN π ρ hA hπ hker3 hEq
  have hYC' : Y ≤ C'.map π := by rw [hC'map]; exact hYle
  let Z : Subgroup ↥H := ⁅Y.comap π, Y.comap π⁆
  have hZeq : Z = ⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆ :=
    commutator_comap_eq π hker hYC'
  have hZnat : CFSG.IsQuasisimple ↥Z := by
    rw [hZeq]
    exact isQuasisimple_commutator_comap π hker hYC' hYnat
  have hZsub' : IsSubnormal (⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆) C' :=
    isSubnormal_commutator_comap π hker hC'map hYle hYsub
  have hZsub : IsSubnormal Z C' := by rw [hZeq]; exact hZsub'
  have hXsub : IsSubnormal (Z.map H.subtype) C := by
    have h := IsSubnormal.map H.subtype hZsub
    rwa [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show C ≤ H from inf_le_left)] at h
  have hXle : Z.map H.subtype ≤ C := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro g hg
    let a : ↥A := ⟨g, hg⟩
    have hfix := gcca_mulAut_fixes_comap_commutator hAN π ρ hker hEq hYle a hz
    have hc : ((H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ z : ↥H) : G)
        = (a : G) * (z : G) * (a : G)⁻¹ := by
      rw [normalizerMonoidHom_coe]
    have hcoe : (a : G) * (z : G) * (a : G)⁻¹ = (z : G) := by rw [← hc, hfix]
    exact mul_inv_eq_iff_eq_mul.mp hcoe
  have hXq : CFSG.Open.IsQuasisimple ↥(Z.map H.subtype) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      ↥(Z.map H.subtype)).mpr
      (isQuasisimple_map_injective H.subtype H.subtype_injective hZnat)
  exact ⟨hXle, hXsub, hXq⟩

theorem isComponentOfCoverIffAut_holds : IsComponentOfCoverIffAut := by
  intro G _ _ H A R _ hAN π ρ hA hπ hker hker3 hHperf hEq X
  constructor
  · intro hX
    exact gcca_exists_component_of_isComponentOf hAN π ρ hA hπ hker hker3 hHperf hEq hX
  · rintro ⟨Y, hY, rfl⟩
    exact gcca_isComponentOf_commutator_comap hAN π ρ hA hπ hker hker3 hHperf hEq hY

theorem commuteCoverIffAut_holds : CommuteCoverIffAut := by
  intro G _ _ H A R _ hAN π ρ hker hEq X hXperf e
  constructor
  · intro hXe y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hconj : H.normalizerMonoidHom ⟨(e : G), hAN e.2⟩ x = x := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe, hXe x hx]
      group
    rw [← hEq e x, hconj]
  · intro hcomm x hx
    have : Group.IsPerfect ↥X := ⟨hXperf⟩
    let φ : MulAut ↥H := H.normalizerMonoidHom ⟨(e : G), hAN e.2⟩
    have hφfix : ∀ z ∈ ⁅X, X⁆, φ z = z := by
      apply mulAut_fixes_commutator
      intro q hq
      apply hker
      rw [MonoidHom.mem_ker]
      show π (φ q * q⁻¹) = 1
      rw [map_mul, map_inv]
      have hqmap : π q ∈ X.map π := Subgroup.mem_map_of_mem π hq
      have hcq := hcomm (π q) hqmap
      have hφq : π (φ q) = π q := by
        show π (H.normalizerMonoidHom ⟨(e : G), hAN e.2⟩ q) = π q
        rw [hEq e q, hcq]
      rw [hφq, mul_inv_cancel]
    have hperf : φ (x : ↥H) = (x : ↥H) :=
      hφfix (x : ↥H) (by rw [Subgroup.commutator_eq_self]; exact hx)
    have hc : ((φ (x : ↥H) : ↥H) : G) = (e : G) * (x : G) * (e : G)⁻¹ := by
      rw [show φ (x : ↥H) = H.normalizerMonoidHom ⟨(e : G), hAN e.2⟩ (x : ↥H) from rfl,
        normalizerMonoidHom_coe]
    have hcoe : (e : G) * (x : G) * (e : G)⁻¹ = (x : G) := by
      rw [← hc, congrArg Subtype.val hperf]
    exact mul_inv_eq_iff_eq_mul.mp hcoe

end

end CFSG.StandardType.GGQ2Frame.CoverComponents
