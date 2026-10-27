module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs

import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.GroupTheory.AutomorphismAction.CentralDeviation
import CFSG.GroupTheory.ConjQuot
import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open scoped commutatorElement

theorem aut_pow_three_eq_one_of_trivial_mod_center {R : Type} [Group R] [Finite R]
    (hR : IsExtraspecialExpP 3 1 R) (α : MulAut R) (hα : ∀ x : R, x⁻¹ * α x ∈ center R) :
    α ^ 3 = 1 := by
  unfold IsExtraspecialExpP at hR
  obtain ⟨-, hexp, hcomm, -⟩ := hR
  have hquot : ∀ x : R, α x * x⁻¹ ∈ center R := by
    intro x
    have hx := hα x
    have hxx := Subgroup.mem_center_iff.mp hx x
    have heq : α x * x⁻¹ = x⁻¹ * α x := by
      calc α x * x⁻¹ = x * (x⁻¹ * α x) * x⁻¹ := by group
        _ = ((x⁻¹ * α x) * x) * x⁻¹ := by rw [hxx]
        _ = x⁻¹ * α x := by group
    rw [heq]
    exact hx
  have hcenter : ∀ z ∈ center R, α z = z :=
    CFSG.GroupTheory.AutomorphismAction.fixes_center_of_derived_eq α hquot hcomm
  have hexp3 : ∀ x : R, x ^ 3 = 1 := fun x => by
    simpa [hexp] using Monoid.pow_exponent_eq_one x
  exact CFSG.GroupTheory.AutomorphismAction.pow_eq_one_of_exponent_of_fixes_center hexp3 α
    hcenter hquot

private theorem g211s_card_R {G : Type} [Group G] {R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) : Nat.card ↥R = 27 := by
  have h := hR.1
  norm_num at h
  exact h

private theorem g211s_isPGroup_R {G : Type} [Group G] {R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) : IsPGroup 3 ↥R :=
  IsPGroup.of_card (n := 3) (by rw [g211s_card_R hR]; norm_num)

private theorem g211s_card_ker {G : Type} [Group G] {X : Subgroup G}
    {φ : Bar2 X →* QuaternionGroup 2} (hK : IsExtraspecialExpP 3 1 ↥φ.ker) :
    Nat.card ↥φ.ker = 27 := by
  have h := hK.1
  norm_num at h
  exact h

private theorem g211s_card_bar2 {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {φ : Bar2 X →* QuaternionGroup 2} (hφ : Function.Surjective φ)
    (hK : IsExtraspecialExpP 3 1 ↥φ.ker) : Nat.card (Bar2 X) = 216 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.ker)
  have hquot : Nat.card (Bar2 X ⧸ φ.ker) = 8 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [h, hquot, g211s_card_ker hK]

private theorem g211s_card_X {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {φ : Bar2 X →* QuaternionGroup 2} (hφ : Function.Surjective φ)
    (hK : IsExtraspecialExpP 3 1 ↥φ.ker) :
    ∃ a : ℕ, Nat.card ↥X = 2 ^ (a + 3) * 27 := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
  have hbar : Nat.card (Bar2 X) = 216 := g211s_card_bar2 hφ hK
  refine ⟨a, ?_⟩
  have hcard : Nat.card ↥X = 2 ^ a * 216 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup U
    have hb : Nat.card (↥X ⧸ U) = 216 := hbar
    rw [h, hb, ha, mul_comm]
  rw [hcard, pow_add]
  norm_num
  ring

private theorem g211s_sylow {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R) (hSU : R891SU32 (Bar2 X)) :
    IsSylowOf 3 R X := by
  obtain ⟨φ, hφ, hK, _⟩ := hSU
  obtain ⟨a, ha⟩ := g211s_card_X hφ hK
  have hrel : R.relIndex X = 2 ^ (a + 3) := by
    have h := Subgroup.relIndex_mul_card R X
    rw [inf_eq_left.mpr hRX, g211s_card_R hR, ha] at h
    exact Nat.mul_right_cancel (by norm_num) h
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hRX, g211s_isPGroup_R hR, ?_⟩
  rw [hrel]
  intro hdvd
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h32

private theorem g211s_solvable {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hSU : R891SU32 (Bar2 X)) : IsSolvable ↥X := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  obtain ⟨φ, hφ, hK, _⟩ := hSU
  have hKp : IsPGroup 3 ↥φ.ker :=
    IsPGroup.of_card (n := 3) (by rw [g211s_card_ker hK]; norm_num)
  have hKsol : IsSolvable ↥φ.ker :=
    @IsNilpotent.to_isSolvable ↥φ.ker _ (IsPGroup.isNilpotent hKp)
  have hQ8sol : IsSolvable (QuaternionGroup 2) := by
    have hp : IsPGroup 2 (QuaternionGroup 2) :=
      IsPGroup.of_card (n := 3) (by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
        norm_num)
    exact @IsNilpotent.to_isSolvable (QuaternionGroup 2) _ (IsPGroup.isNilpotent hp)
  have hquotsol : IsSolvable (Bar2 X ⧸ φ.ker) :=
    @Group.isSolvable_of_surjective (QuaternionGroup 2) (Bar2 X ⧸ φ.ker) _ _
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.surjective hQ8sol
  have hBarsol : IsSolvable (Bar2 X) :=
    @Group.isSolvable_of_subgroup_quotient (Bar2 X) _ φ.ker _ hKsol hquotsol
  have hUsol : IsSolvable ↥U :=
    @IsNilpotent.to_isSolvable ↥U _ (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).isNilpotent
  exact @Group.isSolvable_of_subgroup_quotient (↥X) _ U _ hUsol hBarsol

private theorem g211s_zof_eq {G : Type} [Group G] (R : Subgroup G) :
    ZOf R = (Subgroup.center ↥R).map R.subtype := by
  ext x
  constructor
  · rintro ⟨hxR, hxc⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hxR⟩, Subgroup.mem_center_iff.mpr (fun y => by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxc y y.2), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun z hz =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩))

private theorem g211s_zof_of_commutator {G : Type} [Group G] {R : Subgroup G}
    (hcomm : commutator ↥R = Subgroup.center ↥R) {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y * x⁻¹ * y⁻¹ ∈ ZOf R := by
  have hc : ⁅(⟨x, hx⟩ : ↥R), (⟨y, hy⟩ : ↥R)⁆ ∈ Subgroup.center ↥R := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [g211s_zof_eq]
  exact Subgroup.mem_map.mpr ⟨_, hc, rfl⟩

private theorem g211s_q8_cube_one : ∀ q : QuaternionGroup 2, q ^ 3 = 1 → q = 1 := by
  decide

private theorem g211s_phi_pi_R {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) (φ : Bar2 X →* QuaternionGroup 2) :
    ∀ x ∈ R.subgroupOf X, φ (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x) = 1 := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let UR : Subgroup ↥X := R.subgroupOf X
  have h3 : IsPGroup 3 ↥(Subgroup.map (φ.comp π) UR) :=
    (g211s_isPGroup_R hR).comap_subtype.map (φ.comp π)
  have h2 : IsPGroup 2 (⊤ : Subgroup (QuaternionGroup 2)) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Subgroup.card_top, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hbot : Subgroup.map (φ.comp π) UR = ⊥ := by
    have hdisj := IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ ⊤ h3 h2
    simpa using hdisj.eq_bot
  intro x hx
  have hxmem : (φ.comp π) x ∈ Subgroup.map (φ.comp π) UR :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hbot] at hxmem
  exact hxmem

private theorem g211s_pi_inj {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) :
    ∀ a b : ↥X, a ∈ R.subgroupOf X → b ∈ R.subgroupOf X →
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) a = QuotientGroup.mk' (CFSG.pCore 2 ↥X) b →
      a = b := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let UR : Subgroup ↥X := R.subgroupOf X
  intro a b ha hb hab
  have hdisj : Disjoint UR U :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) UR U
      ((g211s_isPGroup_R hR).comap_subtype) (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
  have hmemU : a * b⁻¹ ∈ U := by
    have h1 : π (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : a * b⁻¹ ∈ π.ker := MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at h2
  have hmemUR : a * b⁻¹ ∈ UR := UR.mul_mem ha (UR.inv_mem hb)
  have h1 : a * b⁻¹ = 1 := by
    have hmem : a * b⁻¹ ∈ UR ⊓ U := Subgroup.mem_inf.mpr ⟨hmemUR, hmemU⟩
    rw [hdisj.eq_bot] at hmem
    simpa using hmem
  exact mul_inv_eq_one.mp h1

private theorem g211s_map_pi_UR {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R)
    {φ : Bar2 X →* QuaternionGroup 2} (hK : IsExtraspecialExpP 3 1 ↥φ.ker) :
    Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (R.subgroupOf X) = φ.ker := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let UR : Subgroup ↥X := R.subgroupOf X
  have hle : Subgroup.map π UR ≤ φ.ker := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact MonoidHom.mem_ker.mpr (g211s_phi_pi_R hR φ x hx)
  have hURcard : Nat.card ↥UR = 27 := by
    have hc : Nat.card ↥UR = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
    rw [hc, g211s_card_R hR]
  have hmapcard : Nat.card ↥(Subgroup.map π UR) = Nat.card ↥UR := by
    have hmap_eq : Subgroup.map (π.comp UR.subtype) ⊤ = Subgroup.map π UR := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    have hinj : Function.Injective (π.comp UR.subtype) := by
      intro a b hab
      apply Subtype.ext
      exact g211s_pi_inj hR a.1 b.1 a.2 b.2 hab
    rw [← hmap_eq, Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_top
  refine Subgroup.eq_of_le_of_card_ge hle (by
    rw [g211s_card_ker hK, hmapcard, hURcard])

private theorem g211s_comap_eq_sup {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R)
    {φ : Bar2 X →* QuaternionGroup 2} (hK : IsExtraspecialExpP 3 1 ↥φ.ker) :
    φ.ker.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) =
      CFSG.pCore 2 ↥X ⊔ R.subgroupOf X := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let UR : Subgroup ↥X := R.subgroupOf X
  have hπR : Subgroup.map π UR = φ.ker := g211s_map_pi_UR hRX hR hK
  apply le_antisymm
  · intro x hx
    have hxK : π x ∈ φ.ker := Subgroup.mem_comap.mp hx
    rw [← hπR] at hxK
    obtain ⟨r, hr, hpr⟩ := Subgroup.mem_map.mp hxK
    have hu : x * r⁻¹ ∈ U := by
      have h1 : π (x * r⁻¹) = 1 := by rw [map_mul, map_inv, hpr, mul_inv_cancel]
      have h2 : x * r⁻¹ ∈ π.ker := MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at h2
    have hxeq : x = (x * r⁻¹) * r := by group
    rw [hxeq]
    exact Subgroup.mul_mem (U ⊔ UR)
      ((le_sup_left : U ≤ U ⊔ UR) hu) ((le_sup_right : UR ≤ U ⊔ UR) hr)
  · refine sup_le ?_ ?_
    · intro u hu
      rw [Subgroup.mem_comap]
      have h2 : u ∈ π.ker := by rwa [QuotientGroup.ker_mk']
      rw [MonoidHom.mem_ker.mp h2]
      exact φ.ker.one_mem
    · intro r hr
      rw [Subgroup.mem_comap, ← hπR]
      exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩

private theorem g211s_frattini {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R)
    {φ : Bar2 X →* QuaternionGroup 2} (hK : IsExtraspecialExpP 3 1 ↥φ.ker) :
    Subgroup.normalizer (R.subgroupOf X) ⊔
        φ.ker.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) = ⊤ := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let UR : Subgroup ↥X := R.subgroupOf X
  let N : Subgroup ↥X := φ.ker.comap π
  have hNdef : N = U ⊔ UR := g211s_comap_eq_sup hRX hR hK
  have hNnorm : N.Normal := inferInstance
  have hURN : UR ≤ N := by rw [hNdef]; exact le_sup_right
  have hdisj : Disjoint U UR :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) U UR
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ((g211s_isPGroup_R hR).comap_subtype)
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
  have hURcard : Nat.card ↥UR = 27 := by
    have hc : Nat.card ↥UR = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
    rw [hc, g211s_card_R hR]
  have hNcard : Nat.card ↥N = 2 ^ a * 27 := by
    rw [hNdef,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U UR ?_ hdisj,
      ha, hURcard]
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hrel : UR.relIndex N = 2 ^ a := by
    have h := Subgroup.relIndex_mul_card UR N
    rw [inf_eq_left.mpr hURN, hURcard, hNcard] at h
    exact Nat.mul_right_cancel (by norm_num) h
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 UR N :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hURN, (g211s_isPGroup_R hR).comap_subtype, by
      rw [hrel]
      intro hdvd
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      norm_num at h32⟩
  obtain ⟨P, hP⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hfr := Sylow.normalizer_sup_eq_top (N := N) P
  rw [hP, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hURN] at hfr
  exact hfr

private theorem g211s_T0_subgroupOf {G : Type} [Group G] {X R : Subgroup G} (hRX : R ≤ X) :
    (X ⊓ Subgroup.normalizer (R : Set G)).subgroupOf X =
      Subgroup.normalizer (R.subgroupOf X) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, hyR⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hyR (h : G)
  · intro hy
    refine ⟨y.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgX : (⟨g, hRX hg⟩ : ↥X) ∈ R.subgroupOf X := Subgroup.mem_subgroupOf.mpr hg
      have h := (Subgroup.mem_normalizer_iff.mp hy (⟨g, hRX hg⟩ : ↥X)).mp hgX
      exact Subgroup.mem_subgroupOf.mp h
    · intro hg
      have hgX : g ∈ X := by
        have h : g = (y : G)⁻¹ * ((y : G) * g * (y : G)⁻¹) * (y : G) := by group
        rw [h]
        exact X.mul_mem (X.mul_mem (X.inv_mem y.2) (hRX hg)) y.2
      have hmem : y * (⟨g, hgX⟩ : ↥X) * y⁻¹ ∈ R.subgroupOf X := by
        rw [Subgroup.mem_subgroupOf]
        exact hg
      exact Subgroup.mem_subgroupOf.mp
        ((Subgroup.mem_normalizer_iff.mp hy (⟨g, hgX⟩ : ↥X)).mpr hmem)

private theorem g211s_pi_surj {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R)
    {φ : Bar2 X →* QuaternionGroup 2} (hK : IsExtraspecialExpP 3 1 ↥φ.ker) :
    Function.Surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp
        (Subgroup.inclusion (inf_le_left : X ⊓ Subgroup.normalizer (R : Set G) ≤ X))) := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let UR : Subgroup ↥X := R.subgroupOf X
  let N : Subgroup ↥X := φ.ker.comap π
  let T0 : Subgroup G := X ⊓ Subgroup.normalizer (R : Set G)
  intro b
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective U b
  have hfr : Subgroup.normalizer UR ⊔ N = ⊤ := g211s_frattini hRX hR hK
  have hNnorm : N.Normal := inferInstance
  have hxsup : x ∈ Subgroup.normalizer UR ⊔ N := by rw [hfr]; exact Subgroup.mem_top x
  obtain ⟨y, hy, n, hn, hyn⟩ :=
    (@Subgroup.mem_sup_of_normal_right (↥X) _ (Subgroup.normalizer UR) N hNnorm x).mp hxsup
  have hπR : Subgroup.map π UR = φ.ker := g211s_map_pi_UR hRX hR hK
  have hnK : π n ∈ φ.ker := hn
  rw [← hπR] at hnK
  obtain ⟨r, hr, hrn⟩ := Subgroup.mem_map.mp hnK
  let tH : ↥X := y * r
  have htH : tH ∈ Subgroup.normalizer UR := Subgroup.mul_mem _ hy (Subgroup.le_normalizer hr)
  have htG : (tH : G) ∈ T0 := by
    have h : tH ∈ T0.subgroupOf X := by
      rw [g211s_T0_subgroupOf hRX]
      exact htH
    exact Subgroup.mem_subgroupOf.mp h
  refine ⟨⟨(tH : G), htG⟩, ?_⟩
  have hco : ((Subgroup.inclusion (inf_le_left : T0 ≤ X)) ⟨(tH : G), htG⟩ : ↥X) = tH := by
    apply Subtype.ext
    rfl
  rw [MonoidHom.comp_apply, hco]
  calc π tH = π (y * r) := rfl
    _ = π y * π r := map_mul _ _ _
    _ = π y * π n := by rw [hrn]
    _ = π (y * n) := by rw [map_mul]
    _ = π x := by rw [hyn]
    _ = b := hx

private theorem g211s_forward_fix {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R)
    (hAut : ∀ (K : Type) [Group K] [Finite K], IsExtraspecialExpP 3 1 K → ∀ α : MulAut K,
      (∀ x : K, x⁻¹ * α x ∈ Subgroup.center K) → α ^ 3 = 1)
    (t : ↥(X ⊓ Subgroup.normalizer (R : Set G)))
    (hcomm : ∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R) :
    ∀ r : ↥R, (t : G) ^ 3 * (r : G) * ((t : G) ^ 3)⁻¹ = (r : G) := by
  let α : MulAut ↥R := R.normalizerMonoidHom ⟨(t : G), t.2.2⟩
  have hα : ∀ y : ↥R, y⁻¹ * α y ∈ Subgroup.center ↥R := by
    intro y
    have hc : (t : G) * (y : G) * (t : G)⁻¹ * (y : G)⁻¹ ∈ ZOf R := hcomm y y.2
    rw [g211s_zof_eq] at hc
    obtain ⟨c, hc_center, hc_val⟩ := Subgroup.mem_map.mp hc
    have hc_val' : (c : G) = (t : G) * (y : G) * (t : G)⁻¹ * (y : G)⁻¹ := hc_val
    have hαy : α y = c * y := by
      apply Subtype.ext
      have h1 : (α y : G) = (t : G) * (y : G) * (t : G)⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe R ⟨(t : G), t.2.2⟩ y
      have h2 : ((c * y : ↥R) : G) = (c : G) * (y : G) := Subgroup.coe_mul R c y
      rw [h1, h2, hc_val']
      group
    have hyα : y⁻¹ * α y = c := by
      rw [hαy, ← mul_assoc, Subgroup.mem_center_iff.mp hc_center y⁻¹, mul_assoc,
        inv_mul_cancel, mul_one]
    rw [hyα]
    exact hc_center
  have hα3 : α ^ 3 = 1 := hAut ↥R hR α hα
  have htriv : R.normalizerMonoidHom (⟨(t : G), t.2.2⟩ ^ 3) = 1 := by
    rw [map_pow]
    simpa [α] using hα3
  intro r
  have h := congrArg (fun f : MulAut ↥R => ((f r : ↥R) : G)) htriv
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_pow] using h

private theorem g211s_kernel_forward {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R)
    {φ : Bar2 X →* QuaternionGroup 2} (hK : IsExtraspecialExpP 3 1 ↥φ.ker)
    (hC : Subgroup.centralizer (φ.ker : Set (Bar2 X)) ≤ φ.ker)
    (hAut : ∀ (K : Type) [Group K] [Finite K], IsExtraspecialExpP 3 1 K → ∀ α : MulAut K,
      (∀ x : K, x⁻¹ * α x ∈ Subgroup.center K) → α ^ 3 = 1)
    (t : ↥(X ⊓ Subgroup.normalizer (R : Set G)))
    (hcomm : ∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R) :
    (φ.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp
      (Subgroup.inclusion (inf_le_left : X ⊓ Subgroup.normalizer (R : Set G) ≤ X)))) t = 1 := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let UR : Subgroup ↥X := R.subgroupOf X
  let x : ↥X := Subgroup.inclusion inf_le_left t
  have hxG : (x : G) = (t : G) := Subgroup.coe_inclusion _ t
  have hfix := g211s_forward_fix hR hAut t hcomm
  have hcent : π (x ^ 3) ∈ Subgroup.centralizer (φ.ker : Set (Bar2 X)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [← g211s_map_pi_UR hRX hR hK] at hk
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hk
    rw [← map_mul, ← map_mul]
    congr 1
    have hf := hfix ⟨(r : G), Subgroup.mem_subgroupOf.mp hr⟩
    rw [← hxG] at hf
    have hcomm3 : (x : G) ^ 3 * (r : G) = (r : G) * (x : G) ^ 3 := by
      calc (x : G) ^ 3 * (r : G) =
          ((x : G) ^ 3 * (r : G) * ((x : G) ^ 3)⁻¹) * (x : G) ^ 3 := by group
        _ = (r : G) * (x : G) ^ 3 := by rw [hf]
    exact Subtype.ext hcomm3.symm
  have hmemK : π (x ^ 3) ∈ φ.ker := hC hcent
  have hcube : (φ (π x)) ^ 3 = 1 := by
    calc (φ (π x)) ^ 3 = φ ((π x) ^ 3) := by rw [map_pow]
      _ = φ (π (x ^ 3)) := by rw [map_pow π x 3]
      _ = 1 := MonoidHom.mem_ker.mp hmemK
  have hq : φ (π x) = 1 := g211s_q8_cube_one _ hcube
  change φ (π x) = 1
  exact hq

private theorem g211s_kernel_backward {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R)
    {φ : Bar2 X →* QuaternionGroup 2} (hK : IsExtraspecialExpP 3 1 ↥φ.ker)
    (t : ↥(X ⊓ Subgroup.normalizer (R : Set G)))
    (hψ : (φ.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp
      (Subgroup.inclusion (inf_le_left : X ⊓ Subgroup.normalizer (R : Set G) ≤ X)))) t = 1) :
    ∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let UR : Subgroup ↥X := R.subgroupOf X
  let x : ↥X := Subgroup.inclusion inf_le_left t
  have hxG : (x : G) = (t : G) := Subgroup.coe_inclusion _ t
  have hxN : x ∈ Subgroup.normalizer UR := by
    have h : x ∈ (X ⊓ Subgroup.normalizer (R : Set G)).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr t.2
    rwa [g211s_T0_subgroupOf hRX] at h
  have hmemK : π x ∈ φ.ker := by
    have h1 : φ (π x) = 1 := hψ
    exact MonoidHom.mem_ker.mpr h1
  rw [← g211s_map_pi_UR hRX hR hK] at hmemK
  obtain ⟨r₀, hr₀, hr₀eq⟩ := Subgroup.mem_map.mp hmemK
  let u : ↥X := x * r₀⁻¹
  have huπ : π u = 1 := by
    have hu_def : u = x * r₀⁻¹ := rfl
    rw [hu_def, map_mul, map_inv, hr₀eq, mul_inv_cancel]
  have huN : u ∈ Subgroup.normalizer UR :=
    Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ (Subgroup.le_normalizer hr₀))
  have hu_cent : ∀ s : ↥UR, u * (s : ↥X) * u⁻¹ = (s : ↥X) := by
    intro s
    have hmem : u * (s : ↥X) * u⁻¹ ∈ UR := by
      exact ((Subgroup.mem_normalizer_iff.mp huN) (s : ↥X)).mp s.2
    have hπs : π (u * (s : ↥X) * u⁻¹) = π (s : ↥X) := by
      rw [map_mul, map_mul, map_inv, huπ, one_mul, inv_one, mul_one]
    exact g211s_pi_inj hR _ _ hmem s.2 hπs
  intro r hr
  have hrR : (r₀ : G) ∈ R := Subgroup.mem_subgroupOf.mp hr₀
  have hsUR : (r₀ * (⟨r, hRX hr⟩ : ↥X) * r₀⁻¹) ∈ UR :=
    UR.mul_mem (UR.mul_mem hr₀ (Subgroup.mem_subgroupOf.mpr hr)) (UR.inv_mem hr₀)
  have hu_s : (u : G) * ((r₀ : G) * r * (r₀ : G)⁻¹) * (u : G)⁻¹ =
      (r₀ : G) * r * (r₀ : G)⁻¹ := by
    have h := congrArg Subtype.val (hu_cent ⟨r₀ * (⟨r, hRX hr⟩ : ↥X) * r₀⁻¹, hsUR⟩)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hx_eq : (x : G) = (u : G) * (r₀ : G) := by
    have hu_def : u = x * r₀⁻¹ := rfl
    rw [hu_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hmain : (t : G) * r * (t : G)⁻¹ * r⁻¹ =
      (r₀ : G) * r * (r₀ : G)⁻¹ * r⁻¹ := by
    rw [← hxG, hx_eq]
    calc ((u : G) * (r₀ : G)) * r * ((u : G) * (r₀ : G))⁻¹ * r⁻¹ =
        (u : G) * ((r₀ : G) * r * (r₀ : G)⁻¹) * (u : G)⁻¹ * r⁻¹ := by group
      _ = ((r₀ : G) * r * (r₀ : G)⁻¹) * r⁻¹ := by rw [hu_s]
      _ = (r₀ : G) * r * (r₀ : G)⁻¹ * r⁻¹ := by group
  rw [hmain]
  simpa [commutatorElement_def] using
    g211s_zof_of_commutator hR.2.2.1 hrR (hr : (r : G) ∈ R)

private theorem g211s_shape {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R) (hSU : R891SU32 (Bar2 X))
    (hAut : ∀ (K : Type) [Group K] [Finite K], IsExtraspecialExpP 3 1 K → ∀ α : MulAut K,
      (∀ x : K, x⁻¹ * α x ∈ Subgroup.center K) → α ^ 3 = 1) :
    ∃ (T0 : Subgroup G) (ψ : ↥T0 →* QuaternionGroup 2),
      T0 ≤ X ∧ T0 ≤ Subgroup.normalizer (R : Set G) ∧ Function.Surjective ψ ∧
      ∀ t : ↥T0, (∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R) ↔ ψ t = 1 := by
  let U : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' U
  let T0 : Subgroup G := X ⊓ Subgroup.normalizer (R : Set G)
  let iT : ↥T0 →* ↥X := Subgroup.inclusion (inf_le_left : T0 ≤ X)
  obtain ⟨φ, hφ, hK, hC⟩ := hSU
  let ψ : ↥T0 →* QuaternionGroup 2 := φ.comp (π.comp iT)
  refine ⟨T0, ψ, inf_le_left, inf_le_right, ?_, ?_⟩
  · exact hφ.comp (g211s_pi_surj hRX hR hK)
  · intro t
    exact ⟨g211s_kernel_forward hRX hR hK hC hAut t,
      g211s_kernel_backward hRX hR hK t⟩

theorem r891g211_su32_action {G : Type} [Group G] [Finite G] {X R : Subgroup G}
    (hRX : R ≤ X) (hR : IsExtraspecialExpP 3 1 ↥R) (hSU : R891SU32 (Bar2 X))
    (hAut : ∀ (K : Type) [Group K] [Finite K], IsExtraspecialExpP 3 1 K →
      ∀ α : MulAut K, (∀ x : K, x⁻¹ * α x ∈ center K) → α ^ 3 = 1) :
    IsSylowOf 3 R X ∧ IsSolvable ↥X ∧
      ∃ (T0 : Subgroup G) (ψ : ↥T0 →* QuaternionGroup 2),
        T0 ≤ X ∧ T0 ≤ normalizer (R : Set G) ∧ Function.Surjective ψ ∧
        ∀ t : ↥T0, (∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R) ↔ ψ t = 1 := by
  refine ⟨g211s_sylow hRX hR hSU, g211s_solvable hSU, ?_⟩
  exact g211s_shape hRX hR hSU hAut

private theorem g211q1_quotient_card_three {G : Type} [Group G] [Finite G]
    {A B : Subgroup G} (hAB : A ≤ B) (hcard : Nat.card B = 3 * Nat.card A) :
    Nat.card (↥B ⧸ A.subgroupOf B) = 3 := by
  have hA'card : Nat.card ↥(A.subgroupOf B) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ↥B) (A.subgroupOf B)
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hmain : 3 * Nat.card A = Nat.card (↥B ⧸ A.subgroupOf B) * Nat.card A := by
    rw [← hcard, ← hA'card, ← hq]
  exact (Nat.eq_of_mul_eq_mul_right hApos hmain).symm

private theorem g211q1_conjQuotAut_sq_eq_one {G : Type} [Group G] [Finite G]
    {A B : Subgroup G} (hAB : A ≤ B) (hcard : Nat.card B = 3 * Nat.card A) {g : G}
    (hgA : g ∈ normalizer (A : Set G)) (hgB : g ∈ normalizer (B : Set G))
    [hNj : (A.subgroupOf B).Normal] :
    CFSG.GroupTheory.conjQuotAut
        (Subgroup.pow_mem (normalizer (B : Set G)) hgB 2)
        (Subgroup.pow_mem (normalizer (A : Set G)) hgA 2) = 1 := by
  let τ : MulAut (↥B ⧸ A.subgroupOf B) := CFSG.GroupTheory.conjQuotAut hgB hgA
  have hτ'eq : CFSG.GroupTheory.conjQuotAut
      (Subgroup.pow_mem (normalizer (B : Set G)) hgB 2)
      (Subgroup.pow_mem (normalizer (A : Set G)) hgA 2) = τ * τ := by
    ext x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [τ, pow_two, MulAut.mul_apply, CFSG.GroupTheory.conjQuotAut_mk]
    congr 1
    apply Subtype.ext
    group
  rw [hτ'eq]
  exact CFSG.LocalAnalysis.WeakClosure81.mulAut_sq_eq_one_of_card_three
    (g211q1_quotient_card_three hAB hcard) τ

private theorem g211q_sq_trivial_of_index_three {G : Type} [Group G] [Finite G]
    {A B : Subgroup G} (hAB : A ≤ B) (hAn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    (hcard : Nat.card B = 3 * Nat.card A) {g : G}
    (hgA : g ∈ normalizer (A : Set G)) (hgB : g ∈ normalizer (B : Set G)) :
    ∀ b ∈ B, g ^ 2 * b * (g ^ 2)⁻¹ * b⁻¹ ∈ A := by
  have hN : (A.subgroupOf B).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn b
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hAn (b : G) b.2 n hn
  have key : ∀ [hNj : (A.subgroupOf B).Normal],
      ∀ b ∈ B, g ^ 2 * b * (g ^ 2)⁻¹ * b⁻¹ ∈ A := by
    intro hNj
    let H := ↥B ⧸ A.subgroupOf B
    intro b hb
    have hτ' := g211q1_conjQuotAut_sq_eq_one hAB hcard hgA hgB
    have hX : g ^ 2 * b * (g ^ 2)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp
        (Subgroup.pow_mem (normalizer (B : Set G)) hgB 2) b).mp hb
    have hEq : ((⟨g ^ 2 * b * (g ^ 2)⁻¹, hX⟩ : ↥B) : H) = ((⟨b, hb⟩ : ↥B) : H) := by
      have h := congrArg (fun φ : MulAut H => φ ((⟨b, hb⟩ : ↥B) : H)) hτ'
      simpa [H, CFSG.GroupTheory.conjQuotAut_mk, MulAut.one_apply] using h
    have hdiv : ((⟨g ^ 2 * b * (g ^ 2)⁻¹, hX⟩ : ↥B) / (⟨b, hb⟩ : ↥B)) ∈ A.subgroupOf B :=
      (QuotientGroup.eq_iff_div_mem).mp hEq
    have hA := Subgroup.mem_subgroupOf.mp hdiv
    simpa [Subgroup.coe_div, div_eq_mul_inv] using hA
  exact key (hNj := hN)

private theorem g211q1_mem_center_of_sq_conj {G : Type} [Group G] {R Z W : Subgroup G}
    {g : G} (hWR : W ≤ R) (h3 : ∀ r ∈ R, r ^ 3 = 1)
    (hL1W : ∀ w ∈ W, g ^ 2 * w * (g ^ 2)⁻¹ * w⁻¹ ∈ Z)
    (hL1R : ∀ r ∈ R, g ^ 2 * r * (g ^ 2)⁻¹ * r⁻¹ ∈ W)
    (h4 : ∀ r ∈ R, g ^ 4 * r * (g ^ 4)⁻¹ * r⁻¹ ∈ Z) :
    ∀ r ∈ R, g ^ 2 * r * (g ^ 2)⁻¹ * r⁻¹ ∈ Z := by
  intro r hr
  let w := g ^ 2 * r * (g ^ 2)⁻¹ * r⁻¹
  have hwW : w ∈ W := hL1R r hr
  let z := g ^ 2 * w * (g ^ 2)⁻¹ * w⁻¹
  have hzZ : z ∈ Z := hL1W w hwW
  have hqr : g ^ 2 * r * (g ^ 2)⁻¹ = w * r := by
    dsimp only [w]
    group
  have hqw : g ^ 2 * w * (g ^ 2)⁻¹ = z * w := by
    dsimp only [z]
    group
  have hword : g ^ 4 * r * (g ^ 4)⁻¹ * r⁻¹ = z * w ^ 2 := by
    calc g ^ 4 * r * (g ^ 4)⁻¹ * r⁻¹
        = g ^ 2 * (g ^ 2 * r * (g ^ 2)⁻¹) * (g ^ 2)⁻¹ * r⁻¹ := by group
      _ = g ^ 2 * (w * r) * (g ^ 2)⁻¹ * r⁻¹ := by rw [hqr]
      _ = (g ^ 2 * w * (g ^ 2)⁻¹) * (g ^ 2 * r * (g ^ 2)⁻¹) * r⁻¹ := by group
      _ = (z * w) * (w * r) * r⁻¹ := by rw [hqw, hqr]
      _ = z * w ^ 2 := by rw [pow_two]; group
  have h4r : z * w ^ 2 ∈ Z := by
    have h := h4 r hr
    rwa [hword] at h
  have hw2Z : w ^ 2 ∈ Z := by
    have hmem : z⁻¹ * (z * w ^ 2) ∈ Z :=
      Subgroup.mul_mem Z (Subgroup.inv_mem Z hzZ) h4r
    have heq : z⁻¹ * (z * w ^ 2) = w ^ 2 := by group
    rwa [heq] at hmem
  have h3w : w ^ 3 = 1 := h3 w (hWR hwW)
  have hw4 : w ^ 4 = w := by
    calc w ^ 4 = w ^ 3 * w := by group
      _ = 1 * w := by rw [h3w]
      _ = w := one_mul w
  have hwZ : w ∈ Z := by
    have hmem : (w ^ 2) ^ 2 ∈ Z := Subgroup.pow_mem Z hw2Z 2
    have heq : (w ^ 2) ^ 2 = w := by
      rw [← pow_mul]
      norm_num
      exact hw4
    rwa [heq] at hmem
  exact hwZ

private theorem g211q1_sq_conj_mem_center_of_card_nine {G : Type} [Group G] [Finite G]
    {R Z W : Subgroup G}
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) (h3 : ∀ r ∈ R, r ^ 3 = 1)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ Z) (hR27 : Nat.card R = 27)
    (hZ3 : Nat.card Z = 3) {g : G} (hgR : g ∈ normalizer (R : Set G))
    (hgZ : g ∈ normalizer (Z : Set G))
    (h4 : ∀ r ∈ R, g ^ 4 * r * (g ^ 4)⁻¹ * r⁻¹ ∈ Z)
    (hZW : Z ≤ W) (hWR : W ≤ R) (hgW : g ∈ normalizer (W : Set G))
    (hW9 : Nat.card W = 9) :
    ∀ r ∈ R, g ^ 2 * r * (g ^ 2)⁻¹ * r⁻¹ ∈ Z := by
  have hL1W : ∀ w ∈ W, g ^ 2 * w * (g ^ 2)⁻¹ * w⁻¹ ∈ Z := by
    refine g211q_sq_trivial_of_index_three hZW ?_ ?_ hgZ hgW
    · intro b hb a ha
      have hcab : a * b = b * a := hZc a ha b (hWR hb)
      have heq : b * a * b⁻¹ = a := by
        calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [← hcab]
          _ = a := by group
      rw [heq]
      exact ha
    · rw [hW9, hZ3]
  have hL1R : ∀ r ∈ R, g ^ 2 * r * (g ^ 2)⁻¹ * r⁻¹ ∈ W := by
    refine g211q_sq_trivial_of_index_three hWR ?_ ?_ hgW hgR
    · intro r hr w hw
      have hc : r * w * r⁻¹ * w⁻¹ ∈ Z := hcomm r hr w (hWR hw)
      have heq : r * w * r⁻¹ = (r * w * r⁻¹ * w⁻¹) * w := by group
      rw [heq]
      exact Subgroup.mul_mem W (hZW hc) hw
    · rw [hR27, hW9]
  exact g211q1_mem_center_of_sq_conj hWR h3 hL1W hL1R h4

private theorem g211q_eq_or_eq {G : Type} [Group G] [Finite G] {R Z W : Subgroup G}
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) (h3 : ∀ r ∈ R, r ^ 3 = 1)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ Z) (hR27 : Nat.card R = 27)
    (hZ3 : Nat.card Z = 3) {g : G} (hgR : g ∈ normalizer (R : Set G))
    (hgZ : g ∈ normalizer (Z : Set G))
    (h4 : ∀ r ∈ R, g ^ 4 * r * (g ^ 4)⁻¹ * r⁻¹ ∈ Z)
    (h2 : ¬ ∀ r ∈ R, g ^ 2 * r * (g ^ 2)⁻¹ * r⁻¹ ∈ Z)
    (hZW : Z ≤ W) (hWR : W ≤ R) (hgW : g ∈ normalizer (W : Set G)) :
    W = Z ∨ W = R := by
  have hWR27 : Nat.card W ∣ 27 := by
    have h := Subgroup.card_dvd_of_le hWR
    simpa [hR27] using h
  have h3W : 3 ≤ Nat.card W := by
    have h := Subgroup.card_le_of_le hZW
    omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card W = n := ⟨_, rfl⟩
  have h3n : 3 ≤ n := by omega
  have hn27 : n ≤ 27 := by
    have h := Subgroup.card_le_of_le hWR
    omega
  have hdvd : n ∣ 27 := by simpa [hn] using hWR27
  have hn_cases : n = 3 ∨ n = 9 ∨ n = 27 := by
    obtain ⟨k, hk3, hk⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 3) Nat.prime_three).mp (by simpa using hdvd)
    have hkpos : k ≠ 0 := by
      intro hk0
      rw [hk, hk0, pow_zero] at h3n
      omega
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk_cases with rfl | rfl | rfl
    · left
      rw [hk]
      norm_num
    · right; left
      rw [hk]
      norm_num
    · right; right
      rw [hk]
      norm_num
  rcases hn_cases with h3n' | h9n | h27n
  · left
    have hcardle : Nat.card W ≤ Nat.card Z := by omega
    exact (Subgroup.eq_of_le_of_card_ge hZW hcardle).symm
  · exfalso
    have hW9 : Nat.card W = 9 := by omega
    exact h2 (g211q1_sq_conj_mem_center_of_card_nine hZc h3 hcomm hR27 hZ3 hgR hgZ
      h4 hZW hWR hgW hW9)
  · right
    have hcardle : Nat.card R ≤ Nat.card W := by omega
    exact Subgroup.eq_of_le_of_card_ge hWR hcardle

private theorem g211q_inverts {G : Type} [Group G] {R Z : Subgroup G}
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ Z) {t : G}
    (htR : t ∈ normalizer (R : Set G))
    (h2 : ∀ r ∈ R, t ^ 2 * r * (t ^ 2)⁻¹ * r⁻¹ ∈ Z)
    (hC : ∀ w ∈ R, t * w * t⁻¹ * w⁻¹ ∈ Z → w ∈ Z) :
    ∀ r ∈ R, t * r * t⁻¹ * r ∈ Z := by
  intro r hr
  let s : G := t * r * t⁻¹
  let z : G := t ^ 2 * r * (t ^ 2)⁻¹ * r⁻¹
  let w : G := r * s
  have hs : s ∈ R := (Subgroup.mem_normalizer_iff.mp htR r).mp hr
  have hz : z ∈ Z := h2 r hr
  have hw : w ∈ R := R.mul_mem hr hs
  have hsz : s * z = z * s := (hZc z hz s hs).symm
  have hts : t * s * t⁻¹ = z * r := by
    simp only [s, z, pow_two]
    group
  have hkey : t * (r * s) * t⁻¹ = s * (z * r) := by
    calc t * (r * s) * t⁻¹ = (t * r * t⁻¹) * (t * s * t⁻¹) := by group
      _ = s * (z * r) := by rw [hts]
  have hconj : t * w * t⁻¹ * w⁻¹ = z * (s * r * s⁻¹ * r⁻¹) := by
    calc t * w * t⁻¹ * w⁻¹
        = (t * (r * s) * t⁻¹) * (r * s)⁻¹ := by simp only [w]
      _ = (s * (z * r)) * (r * s)⁻¹ := by rw [hkey]
      _ = s * z * r * s⁻¹ * r⁻¹ := by group
      _ = z * s * r * s⁻¹ * r⁻¹ := by rw [hsz]
      _ = z * (s * r * s⁻¹ * r⁻¹) := by group
  have hmem : t * w * t⁻¹ * w⁻¹ ∈ Z := by
    rw [hconj]
    exact Z.mul_mem hz (hcomm s hs r hr)
  have hwZ : w ∈ Z := hC w hw hmem
  have hfin : t * r * t⁻¹ * r = w := by
    calc t * r * t⁻¹ * r = s * r := by simp only [s]
      _ = r⁻¹ * (w * r) := by simp only [w]; group
      _ = r⁻¹ * (r * w) := by rw [hZc w hwZ r hr]
      _ = w := by group
  rw [hfin]
  exact hwZ

private theorem g211q3_zof_comm {G : Type} [Group G] {R : Subgroup G} :
    ∀ z ∈ ZOf R, ∀ r ∈ R, z * r = r * z := by
  intro z hz r hr
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 r hr).symm

private theorem g211q3_pow_three {G : Type} [Group G] {R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) : ∀ r ∈ R, r ^ 3 = 1 := by
  unfold IsExtraspecialExpP at hR
  obtain ⟨-, hexp, -, -⟩ := hR
  intro r hr
  have h : ((⟨r, hr⟩ : ↥R) ^ 3 : ↥R) = 1 := by
    simpa [hexp] using Monoid.pow_exponent_eq_one (⟨r, hr⟩ : ↥R)
  simpa using congrArg (fun x : ↥R => (x : G)) h

private theorem g211q3_comm {G : Type} [Group G] {R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) :
    ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ ZOf R := by
  intro r hr s hs
  exact g211s_zof_of_commutator hR.2.2.1 hr hs

private theorem g211q3_zof_card {G : Type} [Group G] {R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) : Nat.card (ZOf R) = 3 := by
  rw [g211s_zof_eq R, Subgroup.card_map_of_injective R.subtype_injective]
  exact hR.2.2.2

private theorem g211q3_norm_zof {G : Type} [Group G] {R : Subgroup G} {g : G}
    (hgR : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer (ZOf R : Set G) := by
  have hconj : ∀ {h x : G}, h ∈ Subgroup.normalizer (R : Set G) →
      x ∈ Subgroup.centralizer (R : Set G) →
      h * x * h⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
    intro h x hh hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro r hr
    have hh' : h⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.normalizer (R : Set G)).inv_mem hh
    have hr' : h⁻¹ * r * h ∈ R := by
      simpa using (Subgroup.mem_normalizer_iff.mp hh' r).mp hr
    calc r * (h * x * h⁻¹) = h * ((h⁻¹ * r * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * r * h)) * h⁻¹ := by rw [hx (h⁻¹ * r * h) hr']
      _ = (h * x * h⁻¹) * r := by group
  rw [Subgroup.mem_normalizer_iff] at hgR ⊢
  intro z
  rw [ZOf, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hzR, hzc⟩
    exact ⟨(hgR z).mp hzR, hconj hgR hzc⟩
  · rintro ⟨hzR, hzc⟩
    have hg' : g⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.normalizer (R : Set G)).inv_mem hgR
    have hz : z ∈ Subgroup.centralizer (R : Set G) := by
      have h := hconj hg' hzc
      have heq : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
      rwa [heq] at h
    exact ⟨(hgR z).mpr hzR, hz⟩

private theorem g211q3_irred {G : Type} [Group G] [Finite G] {R T0 : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) (hTN : T0 ≤ Subgroup.normalizer (R : Set G))
    {ψ : ↥T0 →* QuaternionGroup 2}
    (hker : ∀ t : ↥T0,
      (∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R) ↔ ψ t = 1)
    {i : ↥T0} (hi : ψ i = QuaternionGroup.a 1) :
    ∀ W : Subgroup G, ZOf R ≤ W → W ≤ R → (i : G) ∈ Subgroup.normalizer (W : Set G) →
      W = ZOf R ∨ W = R := by
  have h4 : ∀ r ∈ R, (i : G) ^ 4 * r * ((i : G) ^ 4)⁻¹ * r⁻¹ ∈ ZOf R := by
    have hpsi : ψ (i ^ 4) = 1 := by
      rw [map_pow, hi]
      decide
    intro r hr
    simpa [Subgroup.coe_pow] using (hker (i ^ 4)).mpr hpsi r hr
  have h2 : ¬ ∀ r ∈ R, (i : G) ^ 2 * r * ((i : G) ^ 2)⁻¹ * r⁻¹ ∈ ZOf R := by
    intro h
    have hpsi : ψ (i ^ 2) = 1 :=
      (hker (i ^ 2)).mp (by
        intro r hr
        simpa [Subgroup.coe_pow] using h r hr)
    have hne : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
    exact hne (by simpa [map_pow, hi] using hpsi)
  intro W hZW hWR hiW
  exact g211q_eq_or_eq (g211q3_zof_comm (R := R)) (g211q3_pow_three hR)
    (g211q3_comm hR) (g211s_card_R hR) (g211q3_zof_card hR)
    (hTN i.2) (g211q3_norm_zof (hTN i.2)) h4 h2 hZW hWR hiW

private theorem g211q3_C {G : Type} [Group G] {R Z : Subgroup G} {t : G}
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) :
    ∃ C : Subgroup G, ∀ w, w ∈ C ↔ w ∈ R ∧ t * w * t⁻¹ * w⁻¹ ∈ Z := by
  let C : Subgroup G :=
    { carrier := {w | w ∈ R ∧ t * w * t⁻¹ * w⁻¹ ∈ Z}
      one_mem' := ⟨R.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haR, haZ⟩ ⟨hbR, hbZ⟩
        refine ⟨R.mul_mem haR hbR, ?_⟩
        have hz : a * (t * b * t⁻¹ * b⁻¹) = (t * b * t⁻¹ * b⁻¹) * a :=
          (hZc _ hbZ a haR).symm
        have h1 : t * (a * b) * t⁻¹ * (a * b)⁻¹ =
            (t * a * t⁻¹ * a⁻¹) * (a * (t * b * t⁻¹ * b⁻¹) * a⁻¹) := by group
        have h2 : a * (t * b * t⁻¹ * b⁻¹) * a⁻¹ = t * b * t⁻¹ * b⁻¹ := by
          rw [hz]
          group
        rw [h1, h2]
        exact Z.mul_mem haZ hbZ
      inv_mem' := by
        rintro a ⟨haR, haZ⟩
        refine ⟨R.inv_mem haR, ?_⟩
        have h1 : t * a * t⁻¹ = a * (t * a * t⁻¹ * a⁻¹) := by
          calc t * a * t⁻¹ = (t * a * t⁻¹ * a⁻¹) * a := by group
            _ = a * (t * a * t⁻¹ * a⁻¹) := hZc _ haZ a haR
        have h2 : t * a⁻¹ * t⁻¹ * (a⁻¹)⁻¹ = (t * a * t⁻¹ * a⁻¹)⁻¹ := by
          calc t * a⁻¹ * t⁻¹ * (a⁻¹)⁻¹ = (t * a * t⁻¹)⁻¹ * a := by group
            _ = (a * (t * a * t⁻¹ * a⁻¹))⁻¹ * a := by
              conv_lhs => rw [h1]
            _ = (t * a * t⁻¹ * a⁻¹)⁻¹ := by group
        rw [h2]
        exact Z.inv_mem haZ }
  exact ⟨C, fun w => Iff.rfl⟩

private theorem g211q3_normC {G : Type} [Group G] [Finite G] {R Z C : Subgroup G} {t i : G}
    (hiR : i ∈ Subgroup.normalizer (R : Set G))
    (hiZ : i ∈ Subgroup.normalizer (Z : Set G))
    (htR : t ∈ Subgroup.normalizer (R : Set G))
    (hC : ∀ w, w ∈ C ↔ w ∈ R ∧ t * w * t⁻¹ * w⁻¹ ∈ Z)
    (hu : ∀ r ∈ R,
      (i * t * i⁻¹ * t⁻¹) * r * (i * t * i⁻¹ * t⁻¹)⁻¹ * r⁻¹ ∈ Z) :
    i ∈ Subgroup.normalizer (C : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap_le : C.map (MulAut.conj i).toMonoidHom ≤ C := by
    rintro w ⟨v, hvC, rfl⟩
    change (MulAut.conj i) v ∈ C
    rw [MulAut.conj_apply, hC]
    have hvR : v ∈ R := ((hC v).mp hvC).1
    have hvZ : t * v * t⁻¹ * v⁻¹ ∈ Z := ((hC v).mp hvC).2
    have hv'R : i * v * i⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hiR v).mp hvR
    refine ⟨hv'R, ?_⟩
    have hyR : t * (i * v * i⁻¹) * t⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp htR (i * v * i⁻¹)).mp hv'R
    have hz : (i * t * i⁻¹ * t⁻¹) * (t * (i * v * i⁻¹) * t⁻¹) *
        (i * t * i⁻¹ * t⁻¹)⁻¹ * (t * (i * v * i⁻¹) * t⁻¹)⁻¹ ∈ Z := hu _ hyR
    have hiA : i * (t * v * t⁻¹ * v⁻¹) * i⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp hiZ (t * v * t⁻¹ * v⁻¹)).mp hvZ
    have h_eq : i * (t * v * t⁻¹ * v⁻¹) * i⁻¹ =
        ((i * t * i⁻¹ * t⁻¹) * (t * (i * v * i⁻¹) * t⁻¹) *
          (i * t * i⁻¹ * t⁻¹)⁻¹ * (t * (i * v * i⁻¹) * t⁻¹)⁻¹) *
        (t * (i * v * i⁻¹) * t⁻¹ * (i * v * i⁻¹)⁻¹) := by group
    rw [h_eq] at hiA
    have hB : t * (i * v * i⁻¹) * t⁻¹ * (i * v * i⁻¹)⁻¹ ∈ Z := by
      have h := Z.mul_mem (Z.inv_mem hz) hiA
      simpa [mul_assoc] using h
    exact hB
  have hinj : Function.Injective (MulAut.conj i).toMonoidHom := (MulAut.conj i).injective
  have hcard : Nat.card ↥C ≤ Nat.card ↥(C.map (MulAut.conj i).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective hinj]
  exact Subgroup.eq_of_le_of_card_ge hmap_le hcard

private theorem g211q3_first {G : Type} [Group G] [Finite G] {R T0 : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) (hTN : T0 ≤ Subgroup.normalizer (R : Set G))
    (ψ : ↥T0 →* QuaternionGroup 2) (hψ : Function.Surjective ψ)
    (hker : ∀ t : ↥T0,
      (∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R) ↔ ψ t = 1) :
    ∀ W : Subgroup G, ZOf R ≤ W → W ≤ R → T0 ≤ Subgroup.normalizer (W : Set G) →
      W = ZOf R ∨ W = R := by
  obtain ⟨i, hi⟩ := hψ (QuaternionGroup.a 1)
  intro W hZW hWR hTW
  exact g211q3_irred hR hTN hker hi W hZW hWR (hTW i.2)

private theorem g211q3_second {G : Type} [Group G] [Finite G] {R T0 : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) (hTN : T0 ≤ Subgroup.normalizer (R : Set G))
    (ψ : ↥T0 →* QuaternionGroup 2) (hψ : Function.Surjective ψ)
    (hker : ∀ t : ↥T0,
      (∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R) ↔ ψ t = 1) :
    ∃ t ∈ ⁅T0, T0⁆, ∀ r ∈ R, t * r * t⁻¹ * r ∈ ZOf R := by
  obtain ⟨i, hi⟩ := hψ (QuaternionGroup.a 1)
  obtain ⟨j, hj⟩ := hψ (QuaternionGroup.xa 0)
  let c : ↥T0 := ⁅i, j⁆
  let t : G := c
  have hψc : ψ c = QuaternionGroup.a 2 := by
    change ψ ⁅i, j⁆ = _
    rw [map_commutatorElement, hi, hj]; decide
  have hψc_ne : ψ c ≠ 1 := by rw [hψc]; decide
  have hψc2 : ψ (c ^ 2) = 1 := by rw [map_pow, hψc]; decide
  have hψu : ψ (i * c * i⁻¹ * c⁻¹) = 1 := by
    have h : ψ ⁅i, c⁆ = 1 := by
      rw [map_commutatorElement, hi, hψc]; decide
    simpa [commutatorElement_def] using h
  have htR : t ∈ Subgroup.normalizer (R : Set G) := by simpa [t] using hTN c.2
  have h2c : ∀ r ∈ R, t ^ 2 * r * (t ^ 2)⁻¹ * r⁻¹ ∈ ZOf R := by
    intro r hr
    simpa [t, Subgroup.coe_pow] using (hker (c ^ 2)).mpr hψc2 r hr
  have hu : ∀ r ∈ R,
      (i * t * i⁻¹ * t⁻¹) * r * (i * t * i⁻¹ * t⁻¹)⁻¹ * r⁻¹ ∈ ZOf R := by
    intro r hr
    simpa [t, Subgroup.coe_mul, Subgroup.coe_inv] using
      (hker (i * c * i⁻¹ * c⁻¹)).mpr hψu r hr
  obtain ⟨C, hC⟩ := g211q3_C (R := R) (Z := ZOf R) (t := t)
    (g211q3_zof_comm (R := R))
  have hZC : ZOf R ≤ C := by
    intro z hz
    refine (hC z).mpr ⟨(Subgroup.mem_inf.mp hz).1, ?_⟩
    have hz' : t * z * t⁻¹ ∈ ZOf R :=
      (Subgroup.mem_normalizer_iff.mp (g211q3_norm_zof htR) z).mp hz
    exact (ZOf R).mul_mem hz' ((ZOf R).inv_mem hz)
  have hCR : C ≤ R := fun w hw => ((hC w).mp hw).1
  have hiC : (i : G) ∈ Subgroup.normalizer (C : Set G) :=
    g211q3_normC (hTN i.2) (g211q3_norm_zof (hTN i.2)) htR hC hu
  have hCZ : C = ZOf R := by
    rcases g211q3_irred hR hTN hker hi C hZC hCR hiC with h | h
    · exact h
    · exfalso
      have htriv : ∀ r ∈ R, t * r * t⁻¹ * r⁻¹ ∈ ZOf R := by
        intro r hr
        have hrC : r ∈ C := by rw [h]; exact hr
        exact ((hC r).mp hrC).2
      have hpsi : ψ c = 1 := (hker c).mp (by simpa [t] using htriv)
      exact hψc_ne hpsi
  have hCinv : ∀ w ∈ R, t * w * t⁻¹ * w⁻¹ ∈ ZOf R → w ∈ ZOf R := by
    intro w hw hwZ
    have hwC : w ∈ C := (hC w).mpr ⟨hw, hwZ⟩
    rwa [hCZ] at hwC
  have htcomm : t ∈ ⁅T0, T0⁆ := by
    have h := Subgroup.commutator_mem_commutator i.2 j.2
    have heq : t = ⁅(i : G), (j : G)⁆ := by
      simp [t, c, commutatorElement_def, Subgroup.coe_mul]
    rwa [heq]
  exact ⟨t, htcomm, g211q_inverts (g211q3_zof_comm (R := R)) (g211q3_comm hR)
    htR h2c hCinv⟩

theorem q8_extraspecial_irreducible_inverting {G : Type} [Group G] [Finite G] {R T0 : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) (hTN : T0 ≤ normalizer (R : Set G))
    (ψ : ↥T0 →* QuaternionGroup 2) (hψ : Function.Surjective ψ)
    (hker : ∀ t : ↥T0, (∀ r ∈ R, (t : G) * r * (t : G)⁻¹ * r⁻¹ ∈ ZOf R) ↔ ψ t = 1) :
    (∀ W : Subgroup G, ZOf R ≤ W → W ≤ R → T0 ≤ normalizer (W : Set G) →
      W = ZOf R ∨ W = R) ∧
    ∃ t ∈ ⁅T0, T0⁆, ∀ r ∈ R, t * r * t⁻¹ * r ∈ ZOf R := by
  exact ⟨g211q3_first hR hTN ψ hψ hker, g211q3_second hR hTN ψ hψ hker⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
