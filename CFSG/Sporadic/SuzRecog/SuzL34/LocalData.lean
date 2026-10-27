module

public import CFSG.Sporadic.SuzRecog.SuzL34.Facts

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34

open Subgroup CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.ABGLocalTools
  CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.Open

open scoped Pointwise

structure LocalData (G : Type) [Group G] (z : G) where
  σ : ↥(centralizer ({z} : Set G)) ≃* ↥(invE 1)
  map_z : ((σ ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(invE 1)) :
    Equiv.Perm (Fin 1782)) = permC 1782 tTab
  isConj_iff : ∀ t : ↥(centralizer ({z} : Set G)), t * t = 1 → t ≠ 1 →
    (IsConj (t : G) z ↔ fixedCard ((σ t : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 54)
  not_isConj_iff : ∀ t : ↥(centralizer ({z} : Set G)), t * t = 1 → t ≠ 1 →
    (¬ IsConj (t : G) z ↔ fixedCard ((σ t : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 42)
  isSylowOf_inf : ∀ t ∈ centralizer ({z} : Set G), t * t = 1 → t ≠ 1 → ¬ IsConj t z →
    IsSylowOf 2 (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))
      (centralizer ({t} : Set G))
  card_inf : ∀ t ∈ centralizer ({z} : Set G), t * t = 1 → t ≠ 1 → ¬ IsConj t z →
    Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) = 512
  isConj_of_not_isConj : ∀ t r : ↥(centralizer ({z} : Set G)), t * t = 1 → t ≠ 1 →
    r * r = 1 → r ≠ 1 → ¬ IsConj (t : G) z → ¬ IsConj (r : G) z → IsConj t r
  card_invE : Nat.card ↥(invE 1) = 3317760
  decPerm_mem : ∀ d : Dec, (∀ k ∈ d.1, k < 10) → decPerm d ∈ invE 1
  w0_mem : permC 1782 w0T ∈ invE 1
  w0_mul_self : permC 1782 w0T * permC 1782 w0T = 1
  w0_ne_one : permC 1782 w0T ≠ 1
  tabSubgroup_v0Tabs : tabSubgroup v0Tabs = centralizer {permC 1782 w0T} ⊓ invE 1
  tabSubgroup_t0Tabs_le : tabSubgroup t0Tabs ≤ tabSubgroup v0Tabs
  tabSubgroup_c0Tabs : tabSubgroup c0Tabs =
    centralizer (tabSubgroup t0Tabs : Set (Equiv.Perm (Fin 1782))) ⊓ tabSubgroup v0Tabs
  tabSubgroup_ct0Tabs : tabSubgroup ct0Tabs =
    centralizer (tabSubgroup t0Tabs : Set (Equiv.Perm (Fin 1782))) ⊓ invE 1
  card_T0 : Nat.card ↥(tabSubgroup t0Tabs) = 64

namespace LocalData

variable {G : Type} [Group G] {z : G} (D : LocalData G z)

noncomputable def elt (x : Equiv.Perm (Fin 1782)) (hx : x ∈ invE 1) : G :=
  (D.σ.symm ⟨x, hx⟩ : G)

theorem elt_mem_centralizer (x) (hx) : D.elt x hx ∈ centralizer ({z} : Set G) :=
  (D.σ.symm ⟨x, hx⟩).2

theorem coe_σ_elt (x) (hx) : ((D.σ ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
    ↥(invE 1)) : Equiv.Perm (Fin 1782)) = x := by
  have h : (⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
      ↥(centralizer ({z} : Set G))) = D.σ.symm ⟨x, hx⟩ := Subtype.ext rfl
  rw [h, D.σ.apply_symm_apply]

theorem elt_coe_σ (g : ↥(centralizer ({z} : Set G))) :
    D.elt (D.σ g) (D.σ g).2 = g := by
  simpa [elt] using congrArg Subtype.val (D.σ.symm_apply_apply g)

theorem elt_mul (x y) (hx) (hy) :
    D.elt (x * y) (mul_mem hx hy) = D.elt x hx * D.elt y hy := by
  have h : (⟨x * y, mul_mem hx hy⟩ : ↥(invE 1)) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
  rw [elt, h, map_mul]
  rfl

theorem elt_one : D.elt 1 (one_mem _) = 1 := by
  have h : (⟨1, one_mem (invE 1)⟩ : ↥(invE 1)) = 1 := Subtype.ext rfl
  rw [elt, h, map_one]
  rfl

theorem elt_inv (x) (hx) : D.elt x⁻¹ (inv_mem hx) = (D.elt x hx)⁻¹ := by
  have h : (⟨x⁻¹, inv_mem hx⟩ : ↥(invE 1)) = (⟨x, hx⟩ : ↥(invE 1))⁻¹ := Subtype.ext rfl
  rw [elt, h, map_inv]
  rfl

theorem elt_injective {x y} {hx hy} (h : D.elt x hx = D.elt y hy) : x = y := by
  have h' : D.σ.symm ⟨x, hx⟩ = D.σ.symm ⟨y, hy⟩ := Subtype.ext h
  exact congrArg Subtype.val (D.σ.symm.injective h')

noncomputable def pull (H : Subgroup (Equiv.Perm (Fin 1782))) : Subgroup G :=
  ((H.subgroupOf (invE 1)).map D.σ.symm.toMonoidHom).map
    (centralizer ({z} : Set G)).subtype

theorem mem_pull {H} {g : G} : g ∈ D.pull H ↔ ∃ hg : g ∈ centralizer ({z} : Set G),
    ((D.σ ⟨g, hg⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ H := by
  rw [pull, Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Subgroup.mem_map] at hm
    obtain ⟨y, hy, hmy⟩ := hm
    rw [Subgroup.mem_subgroupOf] at hy
    refine ⟨m.2, ?_⟩
    have h1 : (⟨(m : G), m.2⟩ : ↥(centralizer ({z} : Set G))) = m := Subtype.ext rfl
    have hmy' : D.σ.symm y = m := hmy
    have h2 : D.σ (⟨(m : G), m.2⟩ : ↥(centralizer ({z} : Set G))) = y := by
      rw [h1, ← hmy', D.σ.apply_symm_apply]
    change ((D.σ (⟨(m : G), m.2⟩ : ↥(centralizer ({z} : Set G))) :
      ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ H
    rw [h2]
    exact hy
  · rintro ⟨hg, hH⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [Subgroup.mem_map]
    refine ⟨⟨D.σ ⟨g, hg⟩, (D.σ ⟨g, hg⟩).2⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hH
    · exact D.σ.symm_apply_apply ⟨g, hg⟩

theorem coe_mem_pull_iff {H} (g : ↥(centralizer ({z} : Set G))) :
    (g : G) ∈ D.pull H ↔ ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ H := by
  rw [mem_pull]
  constructor
  · rintro ⟨hg, h⟩
    have h1 : (⟨(g : G), hg⟩ : ↥(centralizer ({z} : Set G))) = g := Subtype.ext rfl
    rwa [h1] at h
  · intro h
    exact ⟨g.2, h⟩

theorem elt_mem_pull_iff {H} {x} (hx : x ∈ invE 1) : D.elt x hx ∈ D.pull H ↔ x ∈ H := by
  rw [mem_pull]
  constructor
  · rintro ⟨hg, h⟩
    have h1 : (⟨D.elt x hx, hg⟩ : ↥(centralizer ({z} : Set G))) =
        ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ := Subtype.ext rfl
    rw [h1, D.coe_σ_elt x hx] at h
    exact h
  · intro h
    refine ⟨D.elt_mem_centralizer x hx, ?_⟩
    rwa [D.coe_σ_elt x hx]

theorem pull_le_centralizer (H) : D.pull H ≤ centralizer ({z} : Set G) :=
  fun _ hg => (D.mem_pull.mp hg).1

theorem pull_mono {H K} (h : H ≤ K) : D.pull H ≤ D.pull K := by
  intro g hg
  rw [mem_pull] at hg ⊢
  exact ⟨hg.1, h hg.2⟩

theorem pull_le_pull_iff {H K} (hH : H ≤ invE 1) : D.pull H ≤ D.pull K ↔ H ≤ K := by
  constructor
  · intro h x hx
    have hx' : x ∈ invE 1 := hH hx
    have h1 : D.elt x hx' ∈ D.pull H := (D.elt_mem_pull_iff hx').mpr hx
    exact (D.elt_mem_pull_iff hx').mp (h h1)
  · intro h
    exact D.pull_mono h

theorem pull_inf (H K) : D.pull (H ⊓ K) = D.pull H ⊓ D.pull K := by
  ext g
  rw [mem_pull, Subgroup.mem_inf, mem_pull, mem_pull]
  constructor
  · rintro ⟨hg, hH, hK⟩
    exact ⟨⟨hg, hH⟩, ⟨hg, hK⟩⟩
  · rintro ⟨⟨hgH, hH⟩, ⟨hgK, hK⟩⟩
    refine ⟨hgH, hH, ?_⟩
    have h : (⟨g, hgK⟩ : ↥(centralizer ({z} : Set G))) = ⟨g, hgH⟩ := Subtype.ext rfl
    rwa [h] at hK

theorem pull_conj {x} (hx : x ∈ invE 1) {H} (hH : H ≤ invE 1) :
    D.pull (MulAut.conj x • H) = MulAut.conj (D.elt x hx) • D.pull H := by
  ext g
  rw [mem_pull]
  constructor
  · rintro ⟨hg, hgH⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgH
    have hgH' : x⁻¹ * ((D.σ ⟨g, hg⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        x ∈ H := by
      simpa [MulAut.conj_apply] using hgH
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (D.elt x hx)⁻¹ * g * D.elt x hx ∈ D.pull H
    rw [mem_pull]
    have hM : (D.elt x hx)⁻¹ * g * D.elt x hx ∈ centralizer ({z} : Set G) :=
      mul_mem (mul_mem (inv_mem (D.elt_mem_centralizer x hx)) hg)
        (D.elt_mem_centralizer x hx)
    refine ⟨hM, ?_⟩
    have hσ : ((D.σ ⟨(D.elt x hx)⁻¹ * g * D.elt x hx, hM⟩ :
        ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
        x⁻¹ * ((D.σ ⟨g, hg⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * x := by
      have h : (⟨(D.elt x hx)⁻¹ * g * D.elt x hx, hM⟩ :
          ↥(centralizer ({z} : Set G))) =
          (⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
            ↥(centralizer ({z} : Set G)))⁻¹ * ⟨g, hg⟩ *
          ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ := Subtype.ext rfl
      rw [h, map_mul, map_mul, map_inv]
      have h1 : D.σ ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ =
          (⟨x, hx⟩ : ↥(invE 1)) := Subtype.ext (D.coe_σ_elt x hx)
      rw [h1]
      rfl
    rw [hσ]
    exact hgH'
  · rintro hgH
    have hgH' : (D.elt x hx)⁻¹ * g * D.elt x hx ∈ D.pull H := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgH
      simpa [MulAut.conj_apply] using hgH
    rw [mem_pull] at hgH'
    obtain ⟨hM, hH'⟩ := hgH'
    have hg : g ∈ centralizer ({z} : Set G) := by
      have hgEq : g = D.elt x hx * ((D.elt x hx)⁻¹ * g * D.elt x hx) *
          (D.elt x hx)⁻¹ := by group
      rw [hgEq]
      exact mul_mem (mul_mem (D.elt_mem_centralizer x hx) hM)
        (inv_mem (D.elt_mem_centralizer x hx))
    refine ⟨hg, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change x⁻¹ * ((D.σ ⟨g, hg⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * x ∈ H
    have hσ : ((D.σ ⟨(D.elt x hx)⁻¹ * g * D.elt x hx, hM⟩ :
        ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
        x⁻¹ * ((D.σ ⟨g, hg⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * x := by
      have h : (⟨(D.elt x hx)⁻¹ * g * D.elt x hx, hM⟩ :
          ↥(centralizer ({z} : Set G))) =
          (⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
            ↥(centralizer ({z} : Set G)))⁻¹ * ⟨g, hg⟩ *
          ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ := Subtype.ext rfl
      rw [h, map_mul, map_mul, map_inv]
      have h1 : D.σ ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ =
          (⟨x, hx⟩ : ↥(invE 1)) := Subtype.ext (D.coe_σ_elt x hx)
      rw [h1]
      rfl
    rw [← hσ]
    exact hH'

theorem pull_centralizer {X : Subgroup (Equiv.Perm (Fin 1782))} (hX : X ≤ invE 1) :
    D.pull (centralizer (X : Set (Equiv.Perm (Fin 1782)))) =
      centralizer (D.pull X : Set G) ⊓ centralizer ({z} : Set G) := by
  ext g
  rw [mem_pull, Subgroup.mem_inf]
  constructor
  · rintro ⟨hgM, hgX⟩
    have hgX' : ∀ x ∈ X, x * ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) :
        Equiv.Perm (Fin 1782)) = ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) :
          Equiv.Perm (Fin 1782)) * x := mem_centralizer_iff.mp hgX
    refine ⟨mem_centralizer_iff.mpr ?_, hgM⟩
    intro y hy
    change y ∈ D.pull X at hy
    rw [mem_pull] at hy
    obtain ⟨hyM, hyX⟩ := hy
    have hc : ((D.σ ⟨y, hyM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
        ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
          ((D.σ ⟨y, hyM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) :=
      hgX' _ hyX
    have hc' : (⟨y, hyM⟩ : ↥(centralizer ({z} : Set G))) * ⟨g, hgM⟩ =
        ⟨g, hgM⟩ * ⟨y, hyM⟩ := by
      apply D.σ.injective
      rw [map_mul, map_mul]
      exact Subtype.ext hc
    simpa using congrArg Subtype.val hc'
  · rintro ⟨hgCent, hgz⟩
    have hgM : g ∈ centralizer ({z} : Set G) := hgz
    have hgCent' : ∀ y ∈ D.pull X, y * g = g * y := mem_centralizer_iff.mp hgCent
    refine ⟨hgM, mem_centralizer_iff.mpr ?_⟩
    intro x hx
    have hxE : x ∈ invE 1 := hX hx
    have h1 : D.elt x hxE * g = g * D.elt x hxE :=
      hgCent' _ ((D.elt_mem_pull_iff hxE).mpr hx)
    have h1' : (⟨D.elt x hxE, D.elt_mem_centralizer x hxE⟩ :
        ↥(centralizer ({z} : Set G))) * ⟨g, hgM⟩ =
        ⟨g, hgM⟩ * ⟨D.elt x hxE, D.elt_mem_centralizer x hxE⟩ := by
      apply Subtype.ext
      simpa using h1
    have h2 := congrArg (fun t : ↥(centralizer ({z} : Set G)) => D.σ t) h1'
    rw [map_mul, map_mul] at h2
    have h3 : D.σ ⟨D.elt x hxE, D.elt_mem_centralizer x hxE⟩ = ⟨x, hxE⟩ := by
      apply Subtype.ext
      exact D.coe_σ_elt x hxE
    rw [h3] at h2
    simpa using congrArg Subtype.val h2

theorem pull_centralizer_singleton {x} (hx : x ∈ invE 1) :
    D.pull (centralizer {x}) = centralizer {D.elt x hx} ⊓ centralizer ({z} : Set G) := by
  ext g
  rw [mem_pull, Subgroup.mem_inf]
  constructor
  · rintro ⟨hgM, hgX⟩
    have hgX' : ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * x =
        x * ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) :=
      mem_centralizer_singleton_iff.mp hgX
    refine ⟨?_, hgM⟩
    rw [mem_centralizer_singleton_iff]
    have hcomm : (⟨g, hgM⟩ : ↥(centralizer ({z} : Set G))) *
        (⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
          ↥(centralizer ({z} : Set G))) =
        (⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
          ↥(centralizer ({z} : Set G))) * ⟨g, hgM⟩ := by
      apply D.σ.injective
      rw [map_mul, map_mul]
      have h3 : D.σ ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ = ⟨x, hx⟩ := by
        apply Subtype.ext
        exact D.coe_σ_elt x hx
      rw [h3]
      exact Subtype.ext hgX'
    simpa using congrArg Subtype.val hcomm
  · rintro ⟨hgCent, hgz⟩
    have hgM : g ∈ centralizer ({z} : Set G) := hgz
    refine ⟨hgM, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hgCent' : g * D.elt x hx = D.elt x hx * g :=
      mem_centralizer_singleton_iff.mp hgCent
    have hcomm : (⟨g, hgM⟩ : ↥(centralizer ({z} : Set G))) *
        (⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
          ↥(centralizer ({z} : Set G))) =
        (⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
          ↥(centralizer ({z} : Set G))) * ⟨g, hgM⟩ := by
      apply Subtype.ext
      simpa using hgCent'
    have h2 := congrArg (fun t : ↥(centralizer ({z} : Set G)) => D.σ t) hcomm
    rw [map_mul, map_mul] at h2
    have h3 : D.σ ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ = ⟨x, hx⟩ := by
      apply Subtype.ext
      exact D.coe_σ_elt x hx
    rw [h3] at h2
    simpa using congrArg Subtype.val h2

private theorem coe_σ_conj (a b : ↥(centralizer ({z} : Set G))) :
    ((D.σ (a * b * a⁻¹) : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
      ((D.σ a : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        ((D.σ b : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        ((D.σ a : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  rfl

private theorem coe_σ_conj_inv (a b : ↥(centralizer ({z} : Set G))) :
    ((D.σ (a⁻¹ * b * a) : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
      ((D.σ a : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ *
        ((D.σ b : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        ((D.σ a : ↥(invE 1)) : Equiv.Perm (Fin 1782)) := by
  have h : a⁻¹ * b * a = a⁻¹ * b * (a⁻¹)⁻¹ := by rw [inv_inv]
  rw [h, D.coe_σ_conj, map_inv]
  simp only [Subgroup.coe_inv, inv_inv]

theorem pull_normalizer {X : Subgroup (Equiv.Perm (Fin 1782))} (hX : X ≤ invE 1) :
    D.pull (normalizer (X : Set (Equiv.Perm (Fin 1782)))) =
      normalizer (D.pull X : Set G) ⊓ centralizer ({z} : Set G) := by
  ext g
  rw [mem_pull, Subgroup.mem_inf]
  constructor
  · rintro ⟨hgM, hnorm⟩
    have hnorm' : ∀ n : Equiv.Perm (Fin 1782),
        n ∈ X ↔ ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * n *
          ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ ∈ X :=
      mem_normalizer_iff.mp hnorm
    refine ⟨mem_normalizer_iff.mpr ?_, hgM⟩
    intro y
    constructor
    · intro hy
      change y ∈ D.pull X at hy
      rw [mem_pull] at hy
      obtain ⟨hyM, hyX⟩ := hy
      have hgy : g * y * g⁻¹ ∈ centralizer ({z} : Set G) :=
        mul_mem (mul_mem hgM hyM) (inv_mem hgM)
      refine (D.mem_pull).mpr ⟨hgy, ?_⟩
      have harg : (⟨g * y * g⁻¹, hgy⟩ : ↥(centralizer ({z} : Set G))) =
          ⟨g, hgM⟩ * ⟨y, hyM⟩ * ⟨g, hgM⟩⁻¹ := Subtype.ext rfl
      have hσ : ((D.σ ⟨g * y * g⁻¹, hgy⟩ : ↥(invE 1)) :
          Equiv.Perm (Fin 1782)) =
          ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
            ((D.σ ⟨y, hyM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
            ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ := by
        rw [harg, D.coe_σ_conj]
      rw [hσ]
      exact (hnorm' ((D.σ ⟨y, hyM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))).mp hyX
    · intro hy
      change g * y * g⁻¹ ∈ D.pull X at hy
      rw [mem_pull] at hy
      obtain ⟨hgyM, hyX⟩ := hy
      have hyM : y ∈ centralizer ({z} : Set G) := by
        have hyEq : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [hyEq]
        exact mul_mem (mul_mem (inv_mem hgM) hgyM) hgM
      have hn : ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ *
          ((D.σ ⟨g * y * g⁻¹, hgyM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
          ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ X := by
        refine (hnorm' _).mpr ?_
        have hgrp : ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
            (((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ *
              ((D.σ ⟨g * y * g⁻¹, hgyM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
              ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))) *
            ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ =
            ((D.σ ⟨g * y * g⁻¹, hgyM⟩ : ↥(invE 1)) :
              Equiv.Perm (Fin 1782)) := by group
        rw [hgrp]
        exact hyX
      refine (D.mem_pull).mpr ⟨hyM, ?_⟩
      have harg : (⟨y, hyM⟩ : ↥(centralizer ({z} : Set G))) =
          ⟨g, hgM⟩⁻¹ * ⟨g * y * g⁻¹, hgyM⟩ * ⟨g, hgM⟩ := by
        apply Subtype.ext
        change y = g⁻¹ * (g * y * g⁻¹) * g
        group
      rw [harg, D.coe_σ_conj_inv]
      exact hn
  · rintro ⟨hcent, hgz⟩
    have hgM : g ∈ centralizer ({z} : Set G) := hgz
    have hcent' : ∀ y : G, y ∈ D.pull X ↔ g * y * g⁻¹ ∈ D.pull X :=
      mem_normalizer_iff.mp hcent
    refine ⟨hgM, mem_normalizer_iff.mpr ?_⟩
    intro n
    constructor
    · intro hn
      have hnE : n ∈ invE 1 := hX hn
      have hy := hcent' (D.elt n hnE)
      have hy' : g * D.elt n hnE * g⁻¹ ∈ D.pull X :=
        hy.mp ((D.elt_mem_pull_iff hnE).mpr hn)
      change g * D.elt n hnE * g⁻¹ ∈ D.pull X at hy'
      rw [mem_pull] at hy'
      obtain ⟨hgyM, hyX⟩ := hy'
      have harg : (⟨g * D.elt n hnE * g⁻¹, hgyM⟩ :
          ↥(centralizer ({z} : Set G))) =
          ⟨g, hgM⟩ * ⟨D.elt n hnE, D.elt_mem_centralizer n hnE⟩ *
            ⟨g, hgM⟩⁻¹ := Subtype.ext rfl
      rw [harg, D.coe_σ_conj] at hyX
      have h3 : D.σ ⟨D.elt n hnE, D.elt_mem_centralizer n hnE⟩ =
          (⟨n, hnE⟩ : ↥(invE 1)) := Subtype.ext (D.coe_σ_elt n hnE)
      rwa [h3] at hyX
    · intro hn
      have hnE : n ∈ invE 1 := by
        by_contra hnE
        have h : ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * n *
            ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ ∈ invE 1 :=
          hX hn
        apply hnE
        have hnEq : n = ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) :
            Equiv.Perm (Fin 1782))⁻¹ *
            (((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * n *
              ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹) *
            ((D.σ ⟨g, hgM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) := by group
        rw [hnEq]
        exact mul_mem (mul_mem (inv_mem (D.σ ⟨g, hgM⟩).2) h)
          (D.σ ⟨g, hgM⟩).2
      have hy' : g * D.elt n hnE * g⁻¹ ∈ D.pull X := by
        refine (D.mem_pull).mpr ⟨?_, ?_⟩
        · exact mul_mem (mul_mem hgM (D.elt_mem_centralizer n hnE)) (inv_mem hgM)
        · have harg : (⟨g * D.elt n hnE * g⁻¹, _⟩ :
              ↥(centralizer ({z} : Set G))) =
              ⟨g, hgM⟩ * ⟨D.elt n hnE, D.elt_mem_centralizer n hnE⟩ *
                ⟨g, hgM⟩⁻¹ := Subtype.ext rfl
          rw [harg, D.coe_σ_conj]
          have h3 : D.σ ⟨D.elt n hnE, D.elt_mem_centralizer n hnE⟩ =
              (⟨n, hnE⟩ : ↥(invE 1)) := Subtype.ext (D.coe_σ_elt n hnE)
          rwa [h3]
      exact (D.elt_mem_pull_iff hnE).mp ((hcent' (D.elt n hnE)).mpr hy')

theorem pull_sup {H K} (hH : H ≤ invE 1) (hK : K ≤ invE 1) :
    D.pull (H ⊔ K) = D.pull H ⊔ D.pull K := by
  rw [pull, pull, pull, Subgroup.subgroupOf_sup hH hK, Subgroup.map_sup,
    Subgroup.map_sup]

@[expose] noncomputable def pullEquiv {H} (hH : H ≤ invE 1) : ↥(D.pull H) ≃* ↥H where
  toFun g := ⟨(D.σ ⟨g, D.pull_le_centralizer H g.2⟩ : ↥(invE 1)), by
    have hg := g.2
    rw [D.mem_pull] at hg
    obtain ⟨hgM, hH'⟩ := hg
    have h1 : (⟨(g : G), D.pull_le_centralizer H g.2⟩ :
        ↥(centralizer ({z} : Set G))) = ⟨(g : G), hgM⟩ := Subtype.ext rfl
    rwa [← h1] at hH'⟩
  invFun x := ⟨D.elt x (hH x.2), (D.elt_mem_pull_iff (hH x.2)).mpr x.2⟩
  left_inv g := by
    apply Subtype.ext
    exact D.elt_coe_σ ⟨g, D.pull_le_centralizer H g.2⟩
  right_inv x := by
    apply Subtype.ext
    exact D.coe_σ_elt x (hH x.2)
  map_mul' g h := by
    apply Subtype.ext
    change ((D.σ (⟨(g * h : ↥(D.pull H)),
        D.pull_le_centralizer H (g * h).2⟩ : ↥(centralizer ({z} : Set G))) :
        ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
      ((D.σ (⟨g, D.pull_le_centralizer H g.2⟩ :
        ↥(centralizer ({z} : Set G))) : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      ((D.σ (⟨h, D.pull_le_centralizer H h.2⟩ :
        ↥(centralizer ({z} : Set G))) : ↥(invE 1)) : Equiv.Perm (Fin 1782))
    have h1 : (⟨(g * h : ↥(D.pull H)), D.pull_le_centralizer H (g * h).2⟩ :
        ↥(centralizer ({z} : Set G))) =
        ⟨g, D.pull_le_centralizer H g.2⟩ * ⟨h, D.pull_le_centralizer H h.2⟩ :=
      Subtype.ext rfl
    rw [h1, map_mul]
    rfl

theorem coe_pullEquiv {H} (hH : H ≤ invE 1) (g : ↥(D.pull H)) :
    ((D.pullEquiv hH g : ↥H) : Equiv.Perm (Fin 1782)) =
      ((D.σ ⟨g, D.pull_le_centralizer H g.2⟩ : ↥(invE 1)) :
        Equiv.Perm (Fin 1782)) := by
  simp [pullEquiv]

theorem card_pull {H} (hH : H ≤ invE 1) : Nat.card ↥(D.pull H) = Nat.card ↥H :=
  Nat.card_congr (D.pullEquiv hH).toEquiv

theorem isPGroup_pull_iff {p : ℕ} {H} (hH : H ≤ invE 1) :
    IsPGroup p (D.pull H) ↔ IsPGroup p H := by
  constructor
  · intro h
    exact h.of_equiv (D.pullEquiv hH)
  · intro h
    exact h.of_equiv (D.pullEquiv hH).symm

theorem isElemAbelian_pull_iff {H} (hH : H ≤ invE 1) :
    IsElemAbelian 2 (D.pull H) ↔ IsElemAbelian 2 H := by
  constructor
  · intro h
    refine ⟨(D.pullEquiv hH).surjective.isMulCommutative h.1, ?_⟩
    intro x hx
    obtain ⟨y, hy⟩ := (D.pullEquiv hH).surjective ⟨x, hx⟩
    have hval : x = ((D.pullEquiv hH y : ↥H) : Equiv.Perm (Fin 1782)) :=
      (congrArg Subtype.val hy).symm
    rw [hval]
    have hy2 : y ^ 2 = 1 := Subtype.ext (h.2 (y : G) y.2)
    have hpow : (((D.pullEquiv hH (y ^ 2) : ↥H) : Equiv.Perm (Fin 1782))) =
        (((D.pullEquiv hH y : ↥H) : Equiv.Perm (Fin 1782))) ^ 2 := by
      simpa using congrArg Subtype.val (map_pow (D.pullEquiv hH) y 2)
    rw [← hpow, hy2, map_one]
    rfl
  · intro h
    refine ⟨(D.pullEquiv hH).symm.surjective.isMulCommutative h.1, ?_⟩
    intro x hx
    obtain ⟨y, hy⟩ := (D.pullEquiv hH).symm.surjective ⟨x, hx⟩
    have hval : x = (((D.pullEquiv hH).symm y : ↥(D.pull H)) : G) :=
      (congrArg Subtype.val hy).symm
    rw [hval]
    have hy2 : y ^ 2 = 1 := Subtype.ext (h.2 (y : Equiv.Perm (Fin 1782)) y.2)
    have hpow : (((D.pullEquiv hH).symm (y ^ 2) : ↥(D.pull H)) : G) =
        (((D.pullEquiv hH).symm y : ↥(D.pull H)) : G) ^ 2 := by
      simpa using congrArg Subtype.val (map_pow (D.pullEquiv hH).symm y 2)
    rw [← hpow, hy2, map_one]
    rfl

theorem pull_invE : D.pull (invE 1) = centralizer ({z} : Set G) := by
  ext g
  rw [mem_pull]
  constructor
  · rintro ⟨hg, -⟩
    exact hg
  · intro hg
    exact ⟨hg, (D.σ ⟨g, hg⟩).2⟩

theorem isConj_elt_iff {x} (hx : x ∈ invE 1) (h2 : x * x = 1) (h1 : x ≠ 1) :
    IsConj (D.elt x hx) z ↔ fixedCard x = 54 := by
  let g : ↥(centralizer ({z} : Set G)) :=
    ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩
  have hg2 : g * g = 1 := by
    apply D.σ.injective
    rw [map_mul, map_one]
    have h : D.σ g = ⟨x, hx⟩ := by
      apply Subtype.ext
      exact D.coe_σ_elt x hx
    have hsq : (⟨x, hx⟩ : ↥(invE 1)) * ⟨x, hx⟩ = 1 := Subtype.ext h2
    rw [h, hsq]
  have hg1 : g ≠ 1 := by
    intro h
    apply h1
    have hx' : x = 1 := by
      have := congrArg (fun t : ↥(centralizer ({z} : Set G)) => D.σ t) h
      simpa [g, D.coe_σ_elt x hx] using congrArg Subtype.val this
    exact hx'
  have := D.isConj_iff g hg2 hg1
  simpa [g, D.coe_σ_elt x hx] using this

theorem not_isConj_elt_iff {x} (hx : x ∈ invE 1) (h2 : x * x = 1) (h1 : x ≠ 1) :
    ¬ IsConj (D.elt x hx) z ↔ fixedCard x = 42 := by
  let g : ↥(centralizer ({z} : Set G)) :=
    ⟨D.elt x hx, D.elt_mem_centralizer x hx⟩
  have hg2 : g * g = 1 := by
    apply D.σ.injective
    rw [map_mul, map_one]
    have h : D.σ g = ⟨x, hx⟩ := by
      apply Subtype.ext
      exact D.coe_σ_elt x hx
    have hsq : (⟨x, hx⟩ : ↥(invE 1)) * ⟨x, hx⟩ = 1 := Subtype.ext h2
    rw [h, hsq]
  have hg1 : g ≠ 1 := by
    intro h
    apply h1
    have hx' : x = 1 := by
      have := congrArg (fun t : ↥(centralizer ({z} : Set G)) => D.σ t) h
      simpa [g, D.coe_σ_elt x hx] using congrArg Subtype.val this
    exact hx'
  have := D.not_isConj_iff g hg2 hg1
  simpa [g, D.coe_σ_elt x hx] using this

end LocalData

end CFSG.Sporadic.SuzRecog.SuzL34
