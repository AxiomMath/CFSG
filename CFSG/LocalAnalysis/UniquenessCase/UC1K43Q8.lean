module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.LocalAnalysis.UniquenessCase.UC1K43Ext
public import CFSG.Quasithin.EmptyFaithful.S143VQ8
public import CFSG.Quasithin.EmptyFaithful.S143UA
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCIndexTwoDichotomy
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K43

open Subgroup
open scoped MatrixGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Basics

variable {T : Type} [Group T]

theorem sq_mem_center (hT : CFSG.IsExtraspecial 2 T) (x : T) : x ^ 2 ∈ center T := by
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    hT.quotient_elementary_abelian.exponent_dvd_p
    (QuotientGroup.mk x : T ⧸ center T)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  exact h

theorem commutator_mem_center (hT : CFSG.IsExtraspecial 2 T) (x y : T) :
    ⁅x, y⁆ ∈ center T := by
  have hcomm : IsMulCommutative (T ⧸ center T) :=
    hT.quotient_elementary_abelian.toIsMulCommutative
  have h : (QuotientGroup.mk x : T ⧸ center T) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x := IsMulCommutative.is_comm.comm _ _
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' (center T) ⁅x, y⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  simpa using h

theorem center_card_two (hT : CFSG.IsExtraspecial 2 T) :
    ∃ z₀ : T, z₀ ∈ center T ∧ z₀ ≠ 1 ∧ z₀ ^ 2 = 1 ∧
      ∀ a : T, a ∈ center T → a = 1 ∨ a = z₀ := by
  have hcard : Nat.card (center T) = 2 := hT.center_order_p
  have huniq : ∃! y : center T, y ≠ 1 := (Nat.card_eq_two_iff' (1 : center T)).mp hcard
  obtain ⟨y, hyne, hyuniq⟩ := huniq
  refine ⟨y.1, y.2, fun h => hyne (Subtype.ext h), ?_, ?_⟩
  · by_contra hsq
    have hy2mem : y.1 ^ 2 ∈ center T := (center T).pow_mem y.2 2
    have hy2ne : (⟨y.1 ^ 2, hy2mem⟩ : center T) ≠ 1 := fun h => hsq (Subtype.ext_iff.mp h)
    have h2 : (⟨y.1 ^ 2, hy2mem⟩ : center T) = y := hyuniq _ hy2ne
    have hsqy : y.1 ^ 2 = y.1 := congrArg Subtype.val h2
    have h1 : y.1 = 1 := by
      have hh := congrArg (fun t : T => t * y.1⁻¹) hsqy
      simpa [pow_two, mul_assoc] using hh
    exact hyne (Subtype.ext h1)
  · intro a ha
    by_cases h1 : a = 1
    · exact Or.inl h1
    · exact Or.inr (congrArg Subtype.val (hyuniq ⟨a, ha⟩ (fun h => h1 (Subtype.ext_iff.mp h))))

theorem centralizer_index_le_two [Finite T] (hT : CFSG.IsExtraspecial 2 T) (x : T) :
    (Subgroup.centralizer ({x} : Set T)).index ≤ 2 := by
  let f : T →* center T :=
    { toFun := fun t => ⟨⁅t, x⁆, commutator_mem_center hT t x⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        change ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆
        have hb := Subgroup.mem_center_iff.mp (commutator_mem_center hT b x) a
        have hcomm := Subgroup.mem_center_iff.mp (commutator_mem_center hT a x) ⁅b, x⁆
        rw [commutatorElement_mul_left_eq_conj_mul, hb]
        rw [show ⁅b, x⁆ * a * a⁻¹ = ⁅b, x⁆ by group]
        exact hcomm }
  have hker : f.ker = Subgroup.centralizer ({x} : Set T) := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h),
      fun h => Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr h)⟩
  rw [← hker, Subgroup.index_ker f]
  calc Nat.card f.range ≤ Nat.card (center T) :=
        Nat.card_le_card_of_injective (fun y : f.range => (y.1 : center T))
          (fun a b h => Subtype.ext h)
    _ = 2 := hT.center_order_p

theorem centralizer_index_two_of_not_mem_center [Finite T] (hT : CFSG.IsExtraspecial 2 T)
    {x : T} (hx : x ∉ center T) : (Subgroup.centralizer ({x} : Set T)).index = 2 := by
  have hle := centralizer_index_le_two hT x
  have hne1 : (Subgroup.centralizer ({x} : Set T)).index ≠ 1 := by
    intro h1
    apply hx
    have htop := Subgroup.index_eq_one.mp h1
    rw [Subgroup.mem_center_iff]
    intro u
    have hu : u ∈ Subgroup.centralizer ({x} : Set T) := by rw [htop]; trivial
    exact (Subgroup.mem_centralizer_singleton_iff (G := T)).mp hu
  have hne0 : (Subgroup.centralizer ({x} : Set T)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  omega

end Basics

section FixedPoint

variable {T D : Subgroup G}

theorem not_index_two_ker_of_commutator_eq_top [Subgroup.Normalizes D T]
    {φ : ↥T →* Subgroup.center ↥T} (hDT : ⁅D, T⁆ = T)
    (hDinv : ∀ (d : ↥D) (s : ↥T), d • s ∈ φ.ker ↔ s ∈ φ.ker) (hindex2 : φ.ker.index = 2) :
    False := by
  have hmem : ∀ (d : G) (hd : d ∈ D) (s : G) (hs : s ∈ T),
      (⟨⁅d, s⁆, hDT ▸ Subgroup.commutator_mem_commutator hd hs⟩ : ↥T) ∈ φ.ker := by
    intro d hd s hs
    let dd : ↥D := ⟨d, hd⟩
    let sT : ↥T := ⟨s, hs⟩
    have heq : (⟨⁅d, s⁆, hDT ▸ Subgroup.commutator_mem_commutator hd hs⟩ : ↥T)
        = dd • sT * sT⁻¹ := rfl
    rw [heq, Subgroup.mul_mem_iff_of_index_two hindex2, hDinv dd sT]
    exact ⟨fun h => (φ.ker).inv_mem h, fun h => by simpa using (φ.ker).inv_mem h⟩
  have hle : ⁅D, T⁆ ≤ (φ.ker).map T.subtype := by
    rw [Subgroup.commutator_le]
    intro d hd s hs
    exact Subgroup.mem_map_of_mem T.subtype (hmem d hd s hs)
  have hmaple : (φ.ker).map T.subtype ≤ T := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨u, -, rfl⟩
    exact u.2
  have hTle : T ≤ (φ.ker).map T.subtype := by
    intro y hy
    exact hle (by rwa [hDT])
  have hrel : ((φ.ker).map T.subtype).relIndex T = 2 := by
    have hsub : ((φ.ker).map T.subtype).subgroupOf T = φ.ker := by
      ext u
      simp [Subgroup.mem_subgroupOf]
    rw [Subgroup.relIndex, hsub]
    exact hindex2
  have hone : ((φ.ker).map T.subtype).relIndex T = 1 := by
    have heq : (φ.ker).map T.subtype = T := le_antisymm hmaple hTle
    rw [heq, Subgroup.relIndex_self]
  omega

theorem smul_mem_centralizer_singleton_iff_of_fixed [Subgroup.Normalizes D T] {xT : ↥T}
    (hxfix : ∀ d : ↥D, d • xT = xT) (d : ↥D) (s : ↥T) :
    d • s ∈ Subgroup.centralizer ({xT} : Set ↥T) ↔
      s ∈ Subgroup.centralizer ({xT} : Set ↥T) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (fun z : ↥T => d⁻¹ • z) h
    simpa [smul_mul', smul_smul, hxfix] using h'
  · intro h
    have h' := congrArg (fun z : ↥T => d • z) h
    simpa [smul_mul', smul_smul, hxfix] using h'

theorem mem_center_of_mem_centralizer (hT : CFSG.IsExtraspecial 2 ↥T)
    (hN : D ≤ Subgroup.normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T)
    {x : G} (hx : x ∈ T) (hxD : x ∈ Subgroup.centralizer (D : Set G)) :
    (⟨x, hx⟩ : ↥T) ∈ Subgroup.center ↥T := by
  classical
  by_contra hxZ
  let xT : ↥T := ⟨x, hx⟩
  let φ : ↥T →* Subgroup.center ↥T :=
    { toFun := fun u => ⟨⁅u, xT⁆, commutator_mem_center hT u xT⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        change ⁅a * b, xT⁆ = ⁅a, xT⁆ * ⁅b, xT⁆
        have hb := Subgroup.mem_center_iff.mp (commutator_mem_center hT b xT) a
        have hc := Subgroup.mem_center_iff.mp (commutator_mem_center hT a xT) ⁅b, xT⁆
        rw [commutatorElement_mul_left_eq_conj_mul, hb]
        rw [show ⁅b, xT⁆ * a * a⁻¹ = ⁅b, xT⁆ by group]
        exact hc }
  have hphi : φ.ker = Subgroup.centralizer ({xT} : Set ↥T) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h),
      fun h => Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr h)⟩
  have hindex2 : φ.ker.index = 2 := by
    rw [hphi]
    exact centralizer_index_two_of_not_mem_center hT hxZ
  letI : Subgroup.Normalizes D T := ⟨hN⟩
  letI : MulDistribMulAction ↥D ↥T := Subgroup.conjMulDistribMulActionOfLeNormalizer D T hN
  have hxfix : ∀ d : ↥D, d • xT = xT := by
    intro d
    apply Subtype.ext
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have h := Subgroup.mem_centralizer_iff.mp hxD (d : G) d.2
    show (d : G) * x * (d : G)⁻¹ = x
    rw [h]
    group
  have hDinv : ∀ (d : ↥D) (s : ↥T), d • s ∈ φ.ker ↔ s ∈ φ.ker := by
    intro d s
    rw [hphi]
    exact smul_mem_centralizer_singleton_iff_of_fixed hxfix d s
  exact not_index_two_ker_of_commutator_eq_top hDT hDinv hindex2

end FixedPoint

section ConjCenter

theorem conj_fixes_center {T : Subgroup G} (hT : CFSG.IsExtraspecial 2 ↥T)
    {a z : G} (ha : a ∈ Subgroup.normalizer (T : Set G)) (hzT : z ∈ T)
    (hz : (⟨z, hzT⟩ : ↥T) ∈ Subgroup.center ↥T) : a * z * a⁻¹ = z := by
  obtain ⟨z₀, -, hz₀ne, -, hz₀uniq⟩ := center_card_two hT
  have hazT : a * z * a⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp ha z).mp hzT
  have haz : (⟨a * z * a⁻¹, hazT⟩ : ↥T) ∈ Subgroup.center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    have hwT : a⁻¹ * (u : G) * a ∈ T := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem (H := Subgroup.normalizer (T : Set G)) ha) (u : G)).mp u.2
    have hzw : (a⁻¹ * (u : G) * a) * z = z * (a⁻¹ * (u : G) * a) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a⁻¹ * (u : G) * a, hwT⟩)
    calc (u : G) * (a * z * a⁻¹)
        = a * ((a⁻¹ * (u : G) * a) * z) * a⁻¹ := by group
      _ = a * (z * (a⁻¹ * (u : G) * a)) * a⁻¹ := by rw [hzw]
      _ = (a * z * a⁻¹) * (u : G) := by group
  rcases hz₀uniq ⟨z, hzT⟩ hz with h | h
  · have hz1 : z = 1 := congrArg Subtype.val h
    rw [hz1]; group
  · have hzz₀ : z = (z₀ : G) := congrArg Subtype.val h
    rcases hz₀uniq ⟨a * z * a⁻¹, hazT⟩ haz with h2 | h2
    · have h2' : a * z * a⁻¹ = 1 := congrArg Subtype.val h2
      exfalso
      have hz1 : z = 1 := by
        have hc := congrArg (fun w : G => a⁻¹ * w * a) h2'
        have hcz : a⁻¹ * (a * z * a⁻¹) * a = z := by group
        rw [hcz] at hc
        simpa using hc
      exact hz₀ne (Subtype.ext (hzz₀ ▸ hz1))
    · have h2' : a * z * a⁻¹ = (z₀ : G) := congrArg Subtype.val h2
      exact h2'.trans hzz₀.symm

theorem exists_generator_of_card_three {D : Subgroup G} (hD : Nat.card D = 3) :
    ∃ d ∈ D, orderOf d = 3 ∧ D = Subgroup.zpowers d := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥D := isCyclic_of_prime_card (α := ↥D) (by simpa using hD)
  obtain ⟨a, ha⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := ↥D)).mp hcyc
  have hordA : orderOf a = 3 := by
    rw [← Nat.card_zpowers a, ha, Subgroup.card_top]
    simpa using hD
  refine ⟨(a : G), a.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hordA
  · refine le_antisymm ?_ (Subgroup.zpowers_le.mpr a.2)
    intro x hx
    rw [Subgroup.mem_zpowers_iff]
    have hmem : (⟨x, hx⟩ : ↥D) ∈ Subgroup.zpowers a := by rw [ha]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem center_sq_eq_one {T : Subgroup G} (hT : CFSG.IsExtraspecial 2 ↥T)
    {z : G} (hzT : z ∈ T) (hz : (⟨z, hzT⟩ : ↥T) ∈ Subgroup.center ↥T) : z ^ 2 = 1 := by
  obtain ⟨z₀, -, -, hz₀sq, hz₀uniq⟩ := center_card_two hT
  rcases hz₀uniq ⟨z, hzT⟩ hz with h | h
  · have hz1 : z = 1 := congrArg Subtype.val h
    rw [hz1]; simp
  · have hzz : z = (z₀ : G) := congrArg Subtype.val h
    have hz₀sq' : (z₀ : G) ^ 2 = 1 := congrArg Subtype.val hz₀sq
    rw [hzz, hz₀sq']

theorem mem_center_of_conj_eq_mul {T D : Subgroup G} {d c z : G}
    (hT : CFSG.IsExtraspecial 2 ↥T) (hN : D ≤ Subgroup.normalizer (T : Set G))
    (hDgen : D = Subgroup.zpowers d) (hd3 : d ^ 3 = 1) (hDT : ⁅D, T⁆ = T)
    (hcT : c ∈ T) (hzT : z ∈ T) (hz : (⟨z, hzT⟩ : ↥T) ∈ Subgroup.center ↥T)
    (hconj : d * c * d⁻¹ = z * c) :
    (⟨c, hcT⟩ : ↥T) ∈ Subgroup.center ↥T := by
  have hdN : d ∈ Subgroup.normalizer (T : Set G) :=
    hN (by rw [hDgen]; exact Subgroup.mem_zpowers d)
  have hfix : d * z * d⁻¹ = z := conj_fixes_center hT hdN hzT hz
  have hz2 : z ^ 2 = 1 := center_sq_eq_one hT hzT hz
  have hz2' : z * z = 1 := by rw [← pow_two]; exact hz2
  have hd3' : d * d * d = 1 := by rw [← pow_three']; exact hd3
  have hd3inv : d⁻¹ * d⁻¹ * d⁻¹ = 1 := by
    have h := congrArg Inv.inv hd3'
    simpa [mul_inv_rev, mul_assoc] using h
  have hd2c : d * d * c * (d⁻¹ * d⁻¹) = c := by
    calc d * d * c * (d⁻¹ * d⁻¹) = d * (d * c * d⁻¹) * d⁻¹ := by group
      _ = d * (z * c) * d⁻¹ := by rw [hconj]
      _ = (d * z * d⁻¹) * (d * c * d⁻¹) := by group
      _ = z * (z * c) := by rw [hfix, hconj]
      _ = z * z * c := by group
      _ = c := by rw [hz2', one_mul]
  have hc_eq : d * c * d⁻¹ = c := by
    have hconj2 := congrArg (fun w : G => d * w * d⁻¹) hd2c
    have hL : d * (d * d * c * (d⁻¹ * d⁻¹)) * d⁻¹ = c := by
      have h2 : d * (d * d * c * (d⁻¹ * d⁻¹)) * d⁻¹
          = d * d * d * c * (d⁻¹ * d⁻¹ * d⁻¹) := by group
      rw [h2, hd3', hd3inv]
      group
    rw [hL] at hconj2
    exact hconj2.symm
  have hdc' : d * c * d⁻¹ = c := hc_eq
  have hdc : d * c = c * d := by
    calc d * c = (d * c * d⁻¹) * d := by group
      _ = c * d := by rw [hdc']
  have hcD : c ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hle : Subgroup.zpowers d ≤ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hdc)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hDgen ▸ ha))
  exact mem_center_of_mem_centralizer hT hN hDT hcT hcD

theorem conj_d_orbit_product {d x : G} (hd3 : d ^ 3 = 1) :
    d * (x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)) * d⁻¹
      = (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) * x := by
  have hd3' : d * d * d = 1 := by rw [← pow_three']; exact hd3
  have hd3inv : d⁻¹ * d⁻¹ * d⁻¹ = 1 := by
    have h := congrArg Inv.inv hd3'
    simpa [mul_inv_rev, mul_assoc] using h
  have hdx2 : d * (d * (d * x * d⁻¹) * d⁻¹) * d⁻¹ = x := by
    rw [show d * (d * (d * x * d⁻¹) * d⁻¹) * d⁻¹
        = d * d * d * x * (d⁻¹ * d⁻¹ * d⁻¹) by group, hd3', hd3inv]
    group
  rw [show d * (x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)) * d⁻¹
      = (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)
          * (d * (d * (d * x * d⁻¹) * d⁻¹) * d⁻¹) by group, hdx2]

theorem conj_x_orbit_product {d x : G} (hx2 : x * x = 1) :
    x * (x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)) * x
      = (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) * x := by
  rw [show x * (x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)) * x
      = (x * x) * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) * x by group, hx2, one_mul]

theorem d_orbit_product_comm {D T : Subgroup G} {d x : G}
    (hT : CFSG.IsExtraspecial 2 ↥T) (hN : D ≤ Subgroup.normalizer (T : Set G))
    (hDgen : D = Subgroup.zpowers d) (hd3 : d ^ 3 = 1) (hDT : ⁅D, T⁆ = T)
    (hxT : x ∈ T) (hx2 : x * x = 1) :
    ∀ y ∈ T, (x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)) * y =
      y * (x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)) := by
  have hdN : d ∈ Subgroup.normalizer (T : Set G) :=
    hN (by rw [hDgen]; exact Subgroup.mem_zpowers d)
  have hx1T : d * x * d⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hdN x).mp hxT
  have hx2T : d * (d * x * d⁻¹) * d⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hdN (d * x * d⁻¹)).mp hx1T
  let cG : G := x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)
  have hcT : cG ∈ T := T.mul_mem (T.mul_mem hxT hx1T) hx2T
  let w : ↥T := ⁅(⟨x, hxT⟩ : ↥T), (⟨cG, hcT⟩ : ↥T)⁆
  have hw_center : w ∈ Subgroup.center ↥T :=
    commutator_mem_center hT (⟨x, hxT⟩ : ↥T) (⟨cG, hcT⟩ : ↥T)
  have hzT : (w : G) ∈ T := w.2
  have hconj : d * cG * d⁻¹ = (w : G) * cG := by
    have hval : (w : G) = ⁅x, cG⁆ := by
      rw [show w = ⁅(⟨x, hxT⟩ : ↥T), (⟨cG, hcT⟩ : ↥T)⁆ from rfl]
      exact map_commutatorElement (Subgroup.subtype T) _ _
    calc d * cG * d⁻¹
        = (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) * x := by
          simpa only [cG] using conj_d_orbit_product hd3
      _ = x * cG * x := by simpa only [cG] using (conj_x_orbit_product hx2).symm
      _ = ⁅x, cG⁆ * cG := by
        rw [commutatorElement_def, show x⁻¹ = x from inv_eq_of_mul_eq_one_right hx2]
        group
      _ = (w : G) * cG := by rw [hval]
  have hcZ : (⟨cG, hcT⟩ : ↥T) ∈ Subgroup.center ↥T :=
    mem_center_of_conj_eq_mul hT hN hDgen hd3 hDT hcT hzT hw_center hconj
  intro y hy
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨y, hy⟩)).symm

theorem commute_mul_of_commute_mul_right {c x₁ x : G} (h1 : c * x₁ = x₁ * c)
    (hx : c * x = x * c) : Commute (x₁ * x) c := by
  show (x₁ * x) * c = c * (x₁ * x)
  calc (x₁ * x) * c = x₁ * (x * c) := by group
    _ = x₁ * (c * x) := by rw [hx]
    _ = (x₁ * c) * x := by group
    _ = (c * x₁) * x := by rw [h1]
    _ = c * (x₁ * x) := by group

theorem commute_conj_of_involution {D T : Subgroup G} {d x : G}
    (hT : CFSG.IsExtraspecial 2 ↥T) (hN : D ≤ Subgroup.normalizer (T : Set G))
    (hDgen : D = Subgroup.zpowers d) (hd3 : d ^ 3 = 1) (hDT : ⁅D, T⁆ = T)
    (hxT : x ∈ T) (hx2 : x * x = 1) :
    (d * x * d⁻¹) * x = x * (d * x * d⁻¹) := by
  have hdN : d ∈ Subgroup.normalizer (T : Set G) :=
    hN (by rw [hDgen]; exact Subgroup.mem_zpowers d)
  have hx1T : d * x * d⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hdN x).mp hxT
  have hx2T : d * (d * x * d⁻¹) * d⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hdN (d * x * d⁻¹)).mp hx1T
  let cG : G := x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)
  have hcT : cG ∈ T := T.mul_mem (T.mul_mem hxT hx1T) hx2T
  have hx1sq : (d * x * d⁻¹) * (d * x * d⁻¹) = 1 := by
    rw [show (d * x * d⁻¹) * (d * x * d⁻¹) = d * (x * x) * d⁻¹ by group, hx2]
    group
  have hc_comm : ∀ y ∈ T, cG * y = y * cG := by
    intro y hy
    simpa only [cG] using d_orbit_product_comm hT hN hDgen hd3 hDT hxT hx2 y hy
  have hcZ : (⟨cG, hcT⟩ : ↥T) ∈ Subgroup.center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (hc_comm (y : ↥T) y.2).symm
  have hc2 : cG * cG = 1 := by
    have h := center_sq_eq_one hT hcT hcZ
    rwa [pow_two] at h
  have hx2eq : d * (d * x * d⁻¹) * d⁻¹ = (d * x * d⁻¹) * x * cG := by
    have hce : cG = x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) := rfl
    rw [hce]
    rw [show (d * x * d⁻¹) * x * (x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹))
        = (d * x * d⁻¹) * ((x * x) * (d * x * d⁻¹)) * (d * (d * x * d⁻¹) * d⁻¹) by group,
      hx2, one_mul, hx1sq, one_mul]
  have hcG_comm : ∀ y ∈ T, cG * y = y * cG := hc_comm
  have hcomm : Commute ((d * x * d⁻¹) * x) cG :=
    commute_mul_of_commute_mul_right (hcG_comm _ hx1T) (hcG_comm _ hxT)
  have hx2sq : (d * (d * x * d⁻¹) * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) = 1 := by
    rw [show (d * (d * x * d⁻¹) * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)
        = d * ((d * x * d⁻¹) * (d * x * d⁻¹)) * d⁻¹ by group, hx1sq]
    group
  have hsq : ((d * x * d⁻¹) * x) * ((d * x * d⁻¹) * x) = 1 := by
    have h := hx2sq
    rw [hx2eq] at h
    have hc2pow : cG ^ 2 = 1 := by rw [pow_two]; exact hc2
    rw [show ((d * x * d⁻¹) * x * cG) * ((d * x * d⁻¹) * x * cG)
        = (((d * x * d⁻¹) * x) * cG) ^ 2 by rw [pow_two],
      hcomm.mul_pow 2, hc2pow, mul_one] at h
    rwa [pow_two] at h
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hx1inv : (d * x * d⁻¹)⁻¹ = d * x * d⁻¹ :=
    inv_eq_of_mul_eq_one_right hx1sq
  calc (d * x * d⁻¹) * x = ((d * x * d⁻¹) * x)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    _ = x⁻¹ * (d * x * d⁻¹)⁻¹ := by rw [mul_inv_rev]
    _ = x * (d * x * d⁻¹) := by rw [hxinv, hx1inv]

end ConjCenter

section Helpers

theorem center_ne_top {T : Subgroup G} (hT : CFSG.IsExtraspecial 2 ↥T) :
    Subgroup.center ↥T ≠ ⊤ := fun h =>
  (not_subsingleton_iff_nontrivial.mpr hT.quotient_nontrivial)
    (QuotientGroup.subsingleton_iff.mpr h)

theorem abelian_of_forall_mul_self_eq_one {A : Type*} [Group A]
    (h : ∀ y : A, y * y = 1) : IsMulCommutative A := by
  refine IsMulCommutative.of_comm fun a b => ?_
  have ha := h a
  have hb := h b
  have hab := h (a * b)
  calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by
      rw [show a⁻¹ = a from inv_eq_of_mul_eq_one_right ha,
        show b⁻¹ = b from inv_eq_of_mul_eq_one_right hb]

theorem d_conj_three {d x : G} (hd3 : d ^ 3 = 1) :
    d * (d * (d * x * d⁻¹) * d⁻¹) * d⁻¹ = x := by
  have hd3' : d * d * d = 1 := by rw [← pow_three']; exact hd3
  have hd3inv : d⁻¹ * d⁻¹ * d⁻¹ = 1 := by
    have h := congrArg Inv.inv hd3'
    simpa [mul_inv_rev, mul_assoc] using h
  rw [show d * (d * (d * x * d⁻¹) * d⁻¹) * d⁻¹
      = d * d * d * x * (d⁻¹ * d⁻¹ * d⁻¹) by group, hd3', hd3inv]
  group

theorem exists_conj_ne {D T : Subgroup G} {d : G} (hDgen : D = Subgroup.zpowers d)
    (hDT : ⁅D, T⁆ = T) (hT0 : T ≠ ⊥) : ∃ b ∈ T, d * b * d⁻¹ ≠ b := by
  by_contra hcon
  push Not at hcon
  have hdt : ∀ b ∈ T, d * b = b * d := fun b hb => by
    have h := hcon b hb
    calc d * b = (d * b * d⁻¹) * d := by group
      _ = b * d := by rw [h]
  have hDle : D ≤ Subgroup.centralizer (T : Set G) := by
    rw [hDgen]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hdt b hb).symm)
  have hbot : ⁅D, T⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDle
  exact hT0 (hDT ▸ hbot)

theorem eight_le_card {T : Subgroup G} (hT : CFSG.IsExtraspecial 2 ↥T) :
    8 ≤ Nat.card T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := IsExtraspecial.isPGroup 2 ↥T
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
  have h2lt : 2 < Nat.card T := by
    have hmul : Nat.card (Subgroup.center ↥T) * (Subgroup.center ↥T).index = Nat.card ↥T :=
      Subgroup.card_mul_index _
    have hidx : (Subgroup.center ↥T).index ≠ 1 := fun h =>
      center_ne_top hT (Subgroup.index_eq_one.mp h)
    have hidx2 : 2 ≤ (Subgroup.center ↥T).index := by
      have hpos := Subgroup.index_ne_zero_of_finite (H := Subgroup.center ↥T)
      omega
    have hc := hT.center_order_p
    rw [hc] at hmul
    omega
  have hn3 : 3 ≤ n := by
    rw [hn] at h2lt
    by_contra h
    have hn2 : n ≤ 2 := by omega
    interval_cases n
    · norm_num at h2lt
    · norm_num at h2lt
    · have hcard : Nat.card ↥T = 4 := by rw [hn]; norm_num
      have hcomm : IsMulCommutative ↥T :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hcard]; norm_num)
      exact center_ne_top hT (eq_top_iff.mpr fun a _ =>
        Subgroup.mem_center_iff.mpr fun b => (IsMulCommutative.is_comm.comm a b).symm)
  rw [hn]
  simpa using Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hn3

theorem commute_orbit_closure_generators {d x z : G}
    (hc01 : Commute x (d * x * d⁻¹))
    (hc12 : Commute (d * x * d⁻¹) (d * (d * x * d⁻¹) * d⁻¹))
    (hc02 : Commute x (d * (d * x * d⁻¹) * d⁻¹))
    (hc0z : Commute x z) (hc1z : Commute (d * x * d⁻¹) z)
    (hc2z : Commute (d * (d * x * d⁻¹) * d⁻¹) z) :
    ∀ a ∈ ({x, d * x * d⁻¹, d * (d * x * d⁻¹) * d⁻¹, z} : Set G),
      ∀ b ∈ ({x, d * x * d⁻¹, d * (d * x * d⁻¹) * d⁻¹, z} : Set G),
        a ≠ b → Commute a b := by
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  · exact absurd rfl hab
  · exact hc01
  · exact hc02
  · exact hc0z
  · exact hc01.symm
  · exact absurd rfl hab
  · exact hc12
  · exact hc1z
  · exact hc02.symm
  · exact hc12.symm
  · exact absurd rfl hab
  · exact hc2z
  · exact hc0z.symm
  · exact hc1z.symm
  · exact hc2z.symm
  · exact absurd rfl hab

theorem orbit_closure_abelian {D T : Subgroup G} {d x z : G}
    (hT : CFSG.IsExtraspecial 2 ↥T) (hN : D ≤ Subgroup.normalizer (T : Set G))
    (hDgen : D = Subgroup.zpowers d) (hd3 : d ^ 3 = 1) (hDT : ⁅D, T⁆ = T)
    (hxT : x ∈ T) (hx2 : x * x = 1)
    {hzT : z ∈ T} (hz : (⟨z, hzT⟩ : ↥T) ∈ Subgroup.center ↥T) :
    IsMulCommutative ↥(Subgroup.closure ({x, d * x * d⁻¹,
      d * (d * x * d⁻¹) * d⁻¹, z} : Set G)) := by
  let xg : G := x
  let x1 : G := d * xg * d⁻¹
  let x2 : G := d * x1 * d⁻¹
  let zg : G := z
  change IsMulCommutative ↥(Subgroup.closure ({xg, x1, x2, zg} : Set G))
  have hdN : d ∈ Subgroup.normalizer (T : Set G) :=
    hN (by rw [hDgen]; exact Subgroup.mem_zpowers d)
  have hxT' : xg ∈ T := hxT
  have hx2' : xg * xg = 1 := hx2
  have hx1T : x1 ∈ T := (Subgroup.mem_normalizer_iff.mp hdN xg).mp hxT'
  have hx2T : x2 ∈ T := (Subgroup.mem_normalizer_iff.mp hdN x1).mp hx1T
  have hx1sq : x1 * x1 = 1 := by
    rw [show x1 * x1 = d * (xg * xg) * d⁻¹ by simp only [x1]; group, hx2']
    group
  have hx2sq : x2 * x2 = 1 := by
    rw [show x2 * x2 = d * (x1 * x1) * d⁻¹ by simp only [x2]; group, hx1sq]
    group
  have hdx2 : d * x2 * d⁻¹ = xg := by
    simp only [x2, x1, xg]
    exact d_conj_three hd3
  have hc01 : Commute xg x1 :=
    (commute_conj_of_involution hT hN hDgen hd3 hDT hxT' hx2').symm
  have hc12 : Commute x1 x2 :=
    (commute_conj_of_involution hT hN hDgen hd3 hDT hx1T hx1sq).symm
  have hc02 : Commute xg x2 := by
    have h := commute_conj_of_involution hT hN hDgen hd3 hDT hx2T hx2sq
    rwa [hdx2] at h
  have hzg : ∀ y ∈ T, Commute zg y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩).symm
  have hc0z : Commute xg zg := (hzg xg hxT').symm
  have hc1z : Commute x1 zg := (hzg x1 hx1T).symm
  have hc2z : Commute x2 zg := (hzg x2 hx2T).symm
  refine Subgroup.isMulCommutative_closure ?_
  intro a ha b hb hab
  exact commute_orbit_closure_generators hc01 hc12 hc02 hc0z hc1z hc2z a ha b hb hab

theorem le_normalizer_orbit_closure {D T : Subgroup G} {d x z : G}
    (hT : CFSG.IsExtraspecial 2 ↥T) (hN : D ≤ Subgroup.normalizer (T : Set G))
    (hDgen : D = Subgroup.zpowers d) (hd3 : d ^ 3 = 1) (hDT : ⁅D, T⁆ = T)
    (hxT : x ∈ T) {hzT : z ∈ T} (hz : (⟨z, hzT⟩ : ↥T) ∈ Subgroup.center ↥T) :
    D ≤ Subgroup.normalizer (Subgroup.closure ({x, d * x * d⁻¹,
      d * (d * x * d⁻¹) * d⁻¹, z} : Set G) : Set G) := by
  let xg : G := x
  let x1 : G := d * xg * d⁻¹
  let x2 : G := d * x1 * d⁻¹
  let zg : G := z
  change D ≤ Subgroup.normalizer (Subgroup.closure ({xg, x1, x2, zg} : Set G) : Set G)
  have hdN : d ∈ Subgroup.normalizer (T : Set G) :=
    hN (by rw [hDgen]; exact Subgroup.mem_zpowers d)
  have hdz : d * zg * d⁻¹ = zg := by
    simp only [zg]
    exact conj_fixes_center hT hdN hzT hz
  have hdx0 : d * xg * d⁻¹ = x1 := rfl
  have hdx1 : d * x1 * d⁻¹ = x2 := rfl
  have hdx2 : d * x2 * d⁻¹ = xg := by
    simp only [x2, x1, xg]
    exact d_conj_three hd3
  have hdset : d ∈ Subgroup.normalizer ({xg, x1, x2, zg} : Set G) := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, (rfl | rfl | rfl | rfl), rfl⟩
      · exact Or.inr (Or.inl hdx0)
      · exact Or.inr (Or.inr (Or.inl hdx1))
      · exact Or.inl hdx2
      · exact Or.inr (Or.inr (Or.inr hdz))
    · intro hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨x2, Or.inr (Or.inr (Or.inl rfl)), hdx2⟩
      · exact ⟨xg, Or.inl rfl, hdx0⟩
      · exact ⟨x1, Or.inr (Or.inl rfl), hdx1⟩
      · exact ⟨zg, Or.inr (Or.inr (Or.inr rfl)), hdz⟩
  have hdNA := Subgroup.normalizer_le_normalizer_closure _ hdset
  rw [hDgen]
  exact Subgroup.zpowers_le.mpr hdNA

theorem not_isPGroup_mulAut {D T : Subgroup G} (hD : Nat.card D = 3)
    (hN : D ≤ Subgroup.normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T) (hT0 : T ≠ ⊥) :
    ¬ IsPGroup 2 (MulAut ↥T) := by
  obtain ⟨d, hdD, hdord, hDgen⟩ := exists_generator_of_card_three hD
  obtain ⟨b, hb, hbne⟩ := exists_conj_ne hDgen hDT hT0
  intro hP
  letI : Subgroup.Normalizes D T := ⟨hN⟩
  letI : MulDistribMulAction ↥D ↥T := Subgroup.conjMulDistribMulActionOfLeNormalizer D T hN
  let ψ : ↥D →* MulAut ↥T := MulDistribMulAction.toMulAut (G := ↥D) (M := ↥T)
  have hne : ψ.range ≠ ⊥ := by
    intro hbot
    apply hbne
    have h1 : ψ ⟨d, hdD⟩ = 1 := by
      have hmem : ψ ⟨d, hdD⟩ ∈ ψ.range := ⟨⟨d, hdD⟩, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    have h2 : (⟨d, hdD⟩ : ↥D) • (⟨b, hb⟩ : ↥T) = ⟨b, hb⟩ := by
      have := congrArg (fun f : MulAut ↥T => f ⟨b, hb⟩) h1
      simpa [ψ] using this
    have h3 : d * b * d⁻¹ = b := by
      have := congrArg Subtype.val h2
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using this
    rwa [h3]
  have hdvd : Nat.card ψ.range ∣ Nat.card ↥D := Subgroup.card_range_dvd ψ
  rw [show Nat.card ↥D = 3 from by simpa using hD] at hdvd
  have hne1 : Nat.card ψ.range ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have hrange3 : Nat.card ψ.range = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have h3dvd : 3 ∣ Nat.card (MulAut ↥T) := by
    rw [← hrange3]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk] at h3dvd
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3dvd
  norm_num at h32

theorem exists_orderOf_eq_four {T : Subgroup G} (hcard : Nat.card T = 8)
    (hnonab : ∃ a b : ↥T, a * b ≠ b * a) : ∃ x : ↥T, orderOf x = 4 := by
  have hcard8 : Nat.card ↥T = 8 := by simpa using hcard
  obtain ⟨x, hxne⟩ : ∃ x : ↥T, x * x ≠ 1 := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative ↥T := abelian_of_forall_mul_self_eq_one h
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsMulCommutative.is_comm.comm a b)
  refine ⟨x, ?_⟩
  have hdvd : orderOf x ∣ 8 := by
    rw [← hcard8]; exact orderOf_dvd_natCard x
  have hmem : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [hdiv8] at hmem
  have hne2 : orderOf x ≠ 2 := fun h => hxne (by
    rw [← pow_two, ← h]; exact pow_orderOf_eq_one x)
  have hne1 : orderOf x ≠ 1 := fun h => hxne (by
    rw [orderOf_eq_one_iff.mp h]; exact one_mul 1)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd h hne1
  · exact absurd h hne2
  · exact h
  · exfalso
    have htop : Subgroup.zpowers x = ⊤ :=
      Subgroup.eq_top_of_card_eq (H := Subgroup.zpowers x)
        (by rw [Nat.card_zpowers, h, hcard8])
    haveI : IsCyclic ↥T := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, htop⟩
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsMulCommutative.is_comm.comm a b)

end Helpers

theorem exists_mem_centralizer_inf_not_mem_center {T : Type} [Group T] [Finite T]
    (hT : CFSG.IsExtraspecial 2 T) (hcard : 16 ≤ Nat.card T) :
    ∃ x y u : T, x ∉ center T ∧ y ∉ center T ∧ x * y ≠ y * x ∧
      u * x = x * u ∧ u * y = y * u ∧ u ∉ center T := by
  classical
  have hnt : Nontrivial (T ⧸ center T) := hT.quotient_nontrivial
  have hsub : ¬ Subsingleton (T ⧸ center T) :=
    fun hs => not_nontrivial_iff_subsingleton.mpr hs hnt
  have hne_top : center T ≠ ⊤ := fun h => hsub (QuotientGroup.subsingleton_iff.mpr h)
  obtain ⟨x, hx⟩ : ∃ x : T, x ∉ center T := by
    by_contra h
    push Not at h
    exact hne_top (le_antisymm le_top fun a _ => h a)
  obtain ⟨y, hxy⟩ : ∃ y : T, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hx (Subgroup.mem_center_iff.mpr fun z => (h z).symm)
  have hy : y ∉ center T := fun hy => hxy (Subgroup.mem_center_iff.mp hy x)
  let C : Subgroup T := Subgroup.centralizer ({x} : Set T) ⊓ Subgroup.centralizer ({y} : Set T)
  have hCindex : C.index ≤ 4 := by
    calc C.index ≤ (Subgroup.centralizer ({x} : Set T)).index *
          (Subgroup.centralizer ({y} : Set T)).index := Subgroup.index_inf_le
      _ ≤ 2 * 2 := Nat.mul_le_mul (centralizer_index_le_two hT x) (centralizer_index_le_two hT y)
      _ = 4 := by norm_num
  have hCcard : 4 ≤ Nat.card C := by
    have hmul : Nat.card C * C.index = Nat.card T := Subgroup.card_mul_index C
    have hle : Nat.card T ≤ Nat.card C * 4 := by
      rw [← hmul]
      exact Nat.mul_le_mul_left _ hCindex
    omega
  have hnotle : ¬ C ≤ center T := by
    intro hle
    have hcardC : Nat.card C ≤ Nat.card (center T) :=
      Nat.card_le_card_of_injective (fun c : C => (⟨c.1, hle c.2⟩ : center T))
        (fun a b h => Subtype.ext (congrArg (fun z : center T => (z : T)) h))
    have hZcard : Nat.card (center T) = 2 := hT.center_order_p
    omega
  obtain ⟨u, huC, huZ⟩ := Set.not_subset.mp hnotle
  have huCx : u * x = x * u :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp huC).1
  have huCy : u * y = y * u :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp huC).2
  exact ⟨x, y, u, hx, hy, hxy, huCx, huCy, huZ⟩

theorem noncentral_involution {T : Type} [Group T] [Finite T] (hT : CFSG.IsExtraspecial 2 T)
    (hcard : 16 ≤ Nat.card T) : ∃ x : T, x ∉ center T ∧ x ^ 2 = 1 := by
  classical
  obtain ⟨x, y, u, hx, hy, hxy, huCx, huCy, huZ⟩ :=
    exists_mem_centralizer_inf_not_mem_center hT hcard
  obtain ⟨z₀, -, -, hz₀sq, hz₀uniq⟩ := center_card_two hT
  by_cases hx2 : x ^ 2 = 1
  · exact ⟨x, hx, hx2⟩
  by_cases hy2 : y ^ 2 = 1
  · exact ⟨y, hy, hy2⟩
  by_cases hu2 : u ^ 2 = 1
  · exact ⟨u, huZ, hu2⟩
  have hx2z : x ^ 2 = z₀ := (hz₀uniq (x ^ 2) (sq_mem_center hT x)).resolve_left hx2
  have hu2z : u ^ 2 = z₀ := (hz₀uniq (u ^ 2) (sq_mem_center hT u)).resolve_left hu2
  refine ⟨x * u, ?_, ?_⟩
  · intro hxu
    apply hxy
    have h1 : (x * u) * y = y * (x * u) := (Subgroup.mem_center_iff.mp hxu y).symm
    have h2 : (x * y) * u = (y * x) * u := by
      calc (x * y) * u = x * (y * u) := by group
        _ = x * (u * y) := by rw [← huCy]
        _ = (x * u) * y := by group
        _ = y * (x * u) := h1
        _ = (y * x) * u := by group
    exact mul_right_cancel h2
  · rw [pow_two]
    calc x * u * (x * u) = x * (u * x) * u := by group
      _ = x * (x * u) * u := by rw [huCx]
      _ = x ^ 2 * u ^ 2 := by rw [pow_two, pow_two]; group
      _ = z₀ * z₀ := by rw [hx2z, hu2z]
      _ = 1 := by rw [← pow_two, hz₀sq]

theorem not_sixteen_le_card {D T : Subgroup G} (hD : Nat.card D = 3)
    (hT : CFSG.IsExtraspecial 2 ↥T) (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T)
    (hNo : ∀ A : Subgroup G, IsPGroup 2 A → A ≠ ⊥ → IsMulCommutative ↥A →
      D ≤ normalizer (A : Set G) → ⁅D, A⁆ = A → False) :
    ¬ 16 ≤ Nat.card T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := IsExtraspecial.isPGroup 2 ↥T
  intro h16
  obtain ⟨xs, hxsZ, hxs2⟩ := noncentral_involution hT h16
  obtain ⟨d, hdD, hdord, hDgen⟩ := exists_generator_of_card_three hD
  have hd3 : d ^ 3 = 1 := by rw [← hdord]; exact pow_orderOf_eq_one d
  obtain ⟨zT, hzTcenter, -, -, -⟩ := center_card_two hT
  let xg : G := (xs : G)
  let zg : G := (zT : G)
  have hxT : xg ∈ T := xs.2
  have hzT : zg ∈ T := zT.2
  have hx2 : xg * xg = 1 := by
    show (xs : G) * (xs : G) = 1
    rw [← Subgroup.coe_mul, ← pow_two]
    exact congrArg Subtype.val hxs2
  let A : Subgroup G := Subgroup.closure ({xg, d * xg * d⁻¹,
    d * (d * xg * d⁻¹) * d⁻¹, zg} : Set G)
  have hAcomm : IsMulCommutative ↥A := by
    rw [show A = Subgroup.closure ({xg, d * xg * d⁻¹,
      d * (d * xg * d⁻¹) * d⁻¹, zg} : Set G) from rfl]
    exact orbit_closure_abelian hT hN hDgen hd3 hDT hxT hx2 hzTcenter
  have hAle : A ≤ T := by
    rw [show A = Subgroup.closure ({xg, d * xg * d⁻¹,
      d * (d * xg * d⁻¹) * d⁻¹, zg} : Set G) from rfl]
    exact (Subgroup.closure_le (K := T)).mpr (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      exacts [hxT, (Subgroup.mem_normalizer_iff.mp (hN hdD) xg).mp hxT,
        (Subgroup.mem_normalizer_iff.mp (hN hdD) (d * xg * d⁻¹)).mp
          ((Subgroup.mem_normalizer_iff.mp (hN hdD) xg).mp hxT),
        hzT])
  have hA2 : IsPGroup 2 A :=
    hT2.of_injective (Subgroup.inclusion hAle) (Subgroup.inclusion_injective hAle)
  have hDA : D ≤ Subgroup.normalizer (A : Set G) := by
    rw [show A = Subgroup.closure ({xg, d * xg * d⁻¹,
      d * (d * xg * d⁻¹) * d⁻¹, zg} : Set G) from rfl]
    exact le_normalizer_orbit_closure hT hN hDgen hd3 hDT hxT hzTcenter
  have hcent := NoAbelianD.centralizes_abelian (show NoAbelianD D from hNo)
    hD hA2 hAcomm hDA
  have hxd : xg ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcent a ha xg (Subgroup.subset_closure (Or.inl rfl))
  exact hxsZ (by simpa only [xg] using mem_center_of_mem_centralizer hT hN hDT hxT hxd)

theorem order_eight {D T : Subgroup G} (hD : Nat.card D = 3)
    (hT : CFSG.IsExtraspecial 2 ↥T) (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T)
    (hNo : ∀ A : Subgroup G, IsPGroup 2 A → A ≠ ⊥ → IsMulCommutative ↥A →
      D ≤ normalizer (A : Set G) → ⁅D, A⁆ = A → False) :
    Nat.card T = 8 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := IsExtraspecial.isPGroup 2 ↥T
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
  have hge8 : 8 ≤ Nat.card T := eight_le_card hT
  have hlt16 : ¬ 16 ≤ Nat.card T := not_sixteen_le_card hD hT hN hDT hNo
  rw [hn] at hge8 hlt16
  have hnlt4 : ¬ 4 ≤ n := fun hn4 =>
    hlt16 (by simpa using Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hn4)
  have h3n : 3 ≤ n := by
    by_contra h
    have hn2 : n ≤ 2 := by omega
    have hle : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hn2
    omega
  have : n = 3 := by omega
  rw [hn, this]
  norm_num

theorem sq_eq_center_of_order_eight {T : Subgroup G} {zT : ↥T}
    (hT : CFSG.IsExtraspecial 2 ↥T) (hzTcenter : zT ∈ Subgroup.center ↥T)
    (hzTuniq : ∀ g ∈ Subgroup.center ↥T, g = 1 ∨ g = zT)
    (hord4 : ∀ y : ↥T, y ∉ Subgroup.center ↥T → orderOf y = 4)
    (b : ↥T) (hb1 : b ≠ 1) (hbz : b ≠ zT) : b ^ 2 = zT := by
  have hbZ : b ∉ Subgroup.center ↥T := by
    intro hbc
    rcases hzTuniq b hbc with h | h
    · exact hb1 h
    · exact hbz h
  have hbord : orderOf b = 4 := hord4 b hbZ
  have h2 : b ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf b ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr h
    rw [hbord] at hdvd
    norm_num at hdvd
  rcases hzTuniq (b ^ 2) (sq_mem_center hT b) with h | h
  · exact absurd h h2
  · exact h

theorem quaternion {D T : Subgroup G} (hD : Nat.card D = 3) (hT : CFSG.IsExtraspecial 2 ↥T)
    (hcard : Nat.card T = 8) (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T) :
    Nonempty (↥T ≃* QuaternionGroup 2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := IsExtraspecial.isPGroup 2 ↥T
  have hcard8 : Nat.card ↥T = 8 := by simpa using hcard
  have hcenter_ne_top := center_ne_top hT
  have hnonab : ∃ a b : ↥T, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hcenter_ne_top (eq_top_iff.mpr fun a _ =>
      Subgroup.mem_center_iff.mpr fun b => (h a b).symm)
  have h2le : 2 ≤ Nat.card ↥T := by
    have hle : Nat.card (Subgroup.center ↥T) ≤ Nat.card ↥T := by
      simpa [Subgroup.card_top] using Nat.card_le_card_of_injective
        (Subgroup.inclusion (le_top : Subgroup.center ↥T ≤ ⊤))
        (Subgroup.inclusion_injective _)
    rw [hT.center_order_p] at hle
    exact hle
  have hT0 : T ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h2le
    omega
  have hnotP := not_isPGroup_mulAut hD hN hDT hT0
  obtain ⟨x, hxord⟩ := exists_orderOf_eq_four hcard hnonab
  let A : Subgroup ↥T := Subgroup.zpowers x
  haveI : IsCyclic A := inferInstance
  have hAidx : A.index ≤ 2 := by
    have hcardA : Nat.card A = 4 := by
      rw [show A = Subgroup.zpowers x from rfl, Nat.card_zpowers, hxord]
    have hmul := Subgroup.card_mul_index A
    rw [hcardA, hcard8] at hmul
    omega
  have hB : IsExtraspecialPGroup 2 ↥T ∧ Nat.card ↥T = 8 ∧
      ∀ y : ↥T, y ∉ Subgroup.center ↥T → orderOf y = 4 := by
    rcases (CFSG.LocalAnalysis.GorensteinLyons.cyclic_index_two_odd_automorphism_dichotomy
      (P := ↥T) hT2 (A := A) hAidx hnotP).1 with ⟨hE4, -⟩ | hB
    · exfalso
      rw [hcard8] at hE4
      exact (by norm_num : (8 : ℕ) ≠ 4) hE4.2
    · exact hB.1
  obtain ⟨zT, hzTcenter, hzTne, -, hzTuniq⟩ := center_card_two hT
  refine CFSG.Quasithin.S143V.nonempty_mulEquiv_quaternion hcard8 hzTne
    (fun b => Subgroup.mem_center_iff.mp hzTcenter b) ?_
  intro b hb1 hbz
  exact sq_eq_center_of_order_eight hT hzTcenter hzTuniq hB.2.2 b hb1 hbz

theorem sl23 {D T : Subgroup G} (hD : Nat.card D = 3)
    (hQ : Nonempty (↥T ≃* QuaternionGroup 2)) (hN : D ≤ normalizer (T : Set G))
    (hDT : ⁅D, T⁆ = T) : Nonempty (↥(T ⊔ D) ≃* SL(2, ZMod 3)) := by
  obtain ⟨d, hdD, hdord, hDgen⟩ := exists_generator_of_card_three hD
  have hT0 : T ≠ ⊥ := by
    intro h
    obtain ⟨e⟩ := hQ
    have hcardT : Nat.card ↥T = 8 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [h, Subgroup.card_bot] at hcardT
    norm_num at hcardT
  have hnt := exists_conj_ne hDgen hDT hT0
  have hres := CFSG.Quasithin.S143.SL23.nonempty_mulEquiv_sl23 (B := T) (ω := d) hQ hdord
    (fun b hb => (Subgroup.mem_normalizer_iff.mp (hN hdD) b).mp hb) hnt
  rw [hDgen]
  exact hres

end CFSG.LocalAnalysis.UniquenessCase.UCK.K43
