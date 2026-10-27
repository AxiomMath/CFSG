module

public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.GH74.Uniqueness.Bender.Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

section General

variable {G : Type*} [Group G] [Finite G]

theorem not_isPGroup_closure_of_map {K : Subgroup G} {X : Type*} [Group X] (φ : ↥K →* X)
    {d e : ↥K} (hnp : ¬ IsPGroup 2 ↥(Subgroup.closure ({φ d, φ e} : Set X))) :
    ¬ IsPGroup 2 ↥(Subgroup.closure ({(d : G), (e : G)} : Set G)) := by
  intro hP
  have hmap : (Subgroup.closure ({d, e} : Set ↥K)).map K.subtype =
      Subgroup.closure ({(d : G), (e : G)} : Set G) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have h2 : IsPGroup 2 ↥(Subgroup.closure ({d, e} : Set ↥K)) :=
    IsPGroup.of_equiv (hmap ▸ hP)
      (Subgroup.equivMapOfInjective (Subgroup.closure ({d, e} : Set ↥K)) K.subtype
        K.subtype_injective).symm
  refine hnp ?_
  have h3 := h2.map φ
  rwa [MonoidHom.map_closure, Set.image_pair] at h3

end General

section Lift

variable {G : Type} [Group G] [Finite G]
variable {V H E J : Subgroup G}

theorem odd_orderOf_mul_of_not_isPGroup (h : Hyp73 V H E J) {X : Type*} [Group X]
    {φ : ↥(kSub V H E) →* X} {U W : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hW : W ∈ omegaSet V H E) {d e : ↥(kSub V H E)} (hd : (d : G) ∈ U) (he : (e : G) ∈ W)
    (hnp : ¬ IsPGroup 2 ↥(Subgroup.closure ({φ d, φ e} : Set X))) : Odd (orderOf (d * e)) := by
  have h' : Odd (orderOf ((d : G) * (e : G))) :=
    seven_three_A h.elemAbelian h.ti h.abelian hU hW hd he
      (not_isPGroup_closure_of_map φ hnp)
  rw [← Subgroup.orderOf_coe (d * e), Subgroup.coe_mul]
  exact h'

private lemma mul_self_eq_one_of_mem_omegaSet (h : Hyp73 V H E J) {A : Subgroup G}
    (hA : A ∈ omegaSet V H E) {d : ↥(kSub V H E)} (hd : (d : G) ∈ A) : d * d = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  have hd2 := (isElemAbelian_of_mem_omegaSet (V := V) (H := H) (E := E) h.elemAbelian hA).2
    (d : G) hd
  rwa [pow_two] at hd2

private lemma odd_orderOf_mul_swap {v w : ↥(kSub V H E)} (hv : v * v = 1) (hw : w * w = 1)
    (hodd : Odd (orderOf (v * w))) : Odd (orderOf (w * v)) := by
  rw [show w * v = (v * w)⁻¹ by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hw], orderOf_inv]
  exact hodd

private lemma closure_pair_subgroupOf_le {X₀ : Subgroup G} {a b : ↥(kSub V H E)}
    (ha : (a : G) ∈ X₀) (hb : (b : G) ∈ X₀) :
    Subgroup.closure ({a, b} : Set ↥(kSub V H E)) ≤ X₀.subgroupOf (kSub V H E) := by
  refine (Subgroup.closure_le (X₀.subgroupOf (kSub V H E))).2 ?_
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact Subgroup.mem_subgroupOf.mpr ha
  · exact Subgroup.mem_subgroupOf.mpr hb

private lemma conj_mem_omegaSet_and_mem (h : Hyp73 V H E J) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) {x v : ↥(kSub V H E)} (hvU : (v : G) ∈ U) :
    conjSubgroup U (x : G) ∈ omegaSet V H E ∧
      ((x⁻¹ * v * x : ↥(kSub V H E)) : G) ∈ conjSubgroup U (x : G) := by
  refine ⟨conjSubgroup_mem_omegaSet (V := V) (H := H) (E := E) (W := U) h.le h.normal hU
    (kSub_le_of_forall_le h.omega_le x.2), ?_⟩
  rw [mem_conjSubgroup_iff, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    show (x : G) * ((x : G)⁻¹ * (v : G) * (x : G)) * (x : G)⁻¹ = (v : G) from by group]
  exact hvU

private lemma map_conj_mul_self_eq {X : Type*} [Group X] {φ : ↥(kSub V H E) →* X}
    {x v : ↥(kSub V H E)} (hx : φ x * φ x = φ v) : φ (x⁻¹ * v * x) = φ v := by
  rw [map_mul, map_mul, map_inv, ← hx]
  group

private lemma exists_mul_inv_mul_eq_of_odd {u v w : ↥(kSub V H E)} (hu : u * u = 1)
    (hw : w * w = 1) (hv : v * v = 1) (huw : Odd (orderOf (u * w)))
    (hwv : Odd (orderOf (w * v))) :
    ∃ y₁ ∈ Subgroup.closure ({u, w} : Set ↥(kSub V H E)),
      ∃ y₂ ∈ Subgroup.closure ({w, v} : Set ↥(kSub V H E)),
        (y₁ * y₂)⁻¹ * u * (y₁ * y₂) = v := by
  obtain ⟨y₁, hy₁mem, hy₁⟩ := exists_conj_inv_mul_of_involutions_odd hu hw huw
  obtain ⟨y₂, hy₂mem, hy₂⟩ := exists_conj_inv_mul_of_involutions_odd hw hv hwv
  refine ⟨y₁, hy₁mem, y₂, hy₂mem, ?_⟩
  rw [mul_inv_rev,
    show (y₂⁻¹ * y₁⁻¹) * u * (y₁ * y₂) = y₂⁻¹ * (y₁⁻¹ * u * y₁) * y₂ from by group, hy₁, hy₂]

private lemma map_eq_one_or_eq_map_of_conj_eq {X : Type*} [Group X]
    {φ : ↥(kSub V H E) →* X} {u v w y₁ y₂ : ↥(kSub V H E)} (hv : v * v = 1) (hw : w * w = 1)
    (hφu : φ u = φ v) (hodd : Odd (orderOf (v * w)))
    (hy₁ : y₁ ∈ Subgroup.closure ({u, w} : Set ↥(kSub V H E)))
    (hy₂ : y₂ ∈ Subgroup.closure ({w, v} : Set ↥(kSub V H E)))
    (hy : (y₁ * y₂)⁻¹ * u * (y₁ * y₂) = v) :
    φ (y₁ * y₂) = 1 ∨ φ (y₁ * y₂) = φ v := by
  have hvφ : φ v * φ v = 1 := by rw [← map_mul, hv, map_one]
  have hwφ : φ w * φ w = 1 := by rw [← map_mul, hw, map_one]
  have hoddφ : Odd (orderOf (φ v * φ w)) := by
    have h := hodd.of_dvd_nat (orderOf_map_dvd φ (v * w))
    rwa [map_mul] at h
  have hmem : φ (y₁ * y₂) ∈ Subgroup.closure ({φ v, φ w} : Set X) := by
    have h₁ : φ y₁ ∈ Subgroup.closure ({φ v, φ w} : Set X) := by
      have h : φ y₁ ∈ (Subgroup.closure ({u, w} : Set ↥(kSub V H E))).map φ := ⟨y₁, hy₁, rfl⟩
      rwa [MonoidHom.map_closure, Set.image_pair, hφu] at h
    have h₂ : φ y₂ ∈ Subgroup.closure ({φ v, φ w} : Set X) := by
      have h : φ y₂ ∈ (Subgroup.closure ({w, v} : Set ↥(kSub V H E))).map φ := ⟨y₂, hy₂, rfl⟩
      rwa [MonoidHom.map_closure, Set.image_pair, Set.pair_comm] at h
    rw [map_mul]
    exact Subgroup.mul_mem _ h₁ h₂
  have hcomm : (φ (y₁ * y₂))⁻¹ * φ v * φ (y₁ * y₂) = φ v := by
    have h := congrArg φ hy
    rwa [map_mul, map_mul, map_inv, hφu] at h
  have hzp : φ (y₁ * y₂) ∈ Subgroup.zpowers (φ v) := by
    have h := mem_sup_zpowers_of_conj_mem_isPGroup hvφ hwφ hoddφ (J := ⊥) IsPGroup.of_bot
      hmem (by rw [Subgroup.mem_bot, hcomm]; group)
    rwa [sup_bot_eq] at h
  exact CFSG.GH74.Uniqueness.Bender.eq_one_or_eq_of_mem_zpowers hvφ hzp

private lemma conj_mul_eq_of_conj {v x y : ↥(kSub V H E)}
    (hy : y⁻¹ * (x⁻¹ * v * x) * y = v) :
    ((x * y : ↥(kSub V H E)) : G)⁻¹ * (v : G) * ((x * y : ↥(kSub V H E)) : G) = (v : G) := by
  have h : (x * y)⁻¹ * v * (x * y) = v := by
    rw [mul_inv_rev,
      show (y⁻¹ * x⁻¹) * v * (x * y) = y⁻¹ * (x⁻¹ * v * x) * y from by group, hy]
  have := congrArg (Subtype.val) h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

private lemma conj_mul_mul_eq_of_conj {v x y : ↥(kSub V H E)}
    (hy : y⁻¹ * (x⁻¹ * v * x) * y = v) (hv : v * v = 1) :
    ((x * y * v : ↥(kSub V H E)) : G)⁻¹ * (v : G) * ((x * y * v : ↥(kSub V H E)) : G) =
      (v : G) := by
  have h : (x * y)⁻¹ * v * (x * y) = v := by
    rw [mul_inv_rev,
      show (y⁻¹ * x⁻¹) * v * (x * y) = y⁻¹ * (x⁻¹ * v * x) * y from by group, hy]
  have h2 : ((x * y) * v)⁻¹ * v * ((x * y) * v) = v := by
    rw [mul_inv_rev,
      show (v⁻¹ * (x * y)⁻¹) * v * ((x * y) * v) =
        v⁻¹ * ((x * y)⁻¹ * v * (x * y)) * v from by group, h,
      inv_eq_of_mul_eq_one_right hv, mul_assoc, hv, mul_one]
  have := congrArg (Subtype.val) h2
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem exists_centralizing_mul_self_eq (h : Hyp73 V H E J) {X : Type*} [Group X]
    {φ : ↥(kSub V H E) →* X} {U W X₀ : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hW : W ∈ omegaSet V H E) {v w x : ↥(kSub V H E)} (hvU : (v : G) ∈ U)
    (hwW : (w : G) ∈ W) (hvX : (v : G) ∈ X₀) (hwX : (w : G) ∈ X₀) (hxX : (x : G) ∈ X₀)
    (hx : φ x * φ x = φ v)
    (hnp : ¬ IsPGroup 2 ↥(Subgroup.closure ({φ v, φ w} : Set X))) :
    ∃ g : ↥(kSub V H E), (g : G) ∈ X₀ ∧ (g : G)⁻¹ * v * g = v ∧ φ g * φ g = φ v := by
  classical
  have hv2 : v * v = 1 := mul_self_eq_one_of_mem_omegaSet h hU hvU
  have hw2 : w * w = 1 := mul_self_eq_one_of_mem_omegaSet h hW hwW
  obtain ⟨hUx, hu_mem⟩ := conj_mem_omegaSet_and_mem h hU hvU
  have hu2 : (x⁻¹ * v * x) * (x⁻¹ * v * x) = 1 :=
    mul_self_eq_one_of_mem_omegaSet h hUx hu_mem
  have huX₀ : ((x⁻¹ * v * x : ↥(kSub V H E)) : G) ∈ X₀ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact X₀.mul_mem (X₀.mul_mem (X₀.inv_mem hxX) hvX) hxX
  have hφu : φ (x⁻¹ * v * x) = φ v := map_conj_mul_self_eq hx
  have hodd_uw : Odd (orderOf ((x⁻¹ * v * x) * w)) :=
    odd_orderOf_mul_of_not_isPGroup (X := X) (φ := φ) h hUx hW hu_mem hwW
      (by rw [hφu]; exact hnp)
  have hodd_vw : Odd (orderOf (v * w)) :=
    odd_orderOf_mul_of_not_isPGroup (X := X) (φ := φ) h hU hW hvU hwW hnp
  have hodd_wv : Odd (orderOf (w * v)) := odd_orderOf_mul_swap hv2 hw2 hodd_vw
  obtain ⟨y₁, hy₁mem, y₂, hy₂mem, hy⟩ :=
    exists_mul_inv_mul_eq_of_odd hu2 hw2 hv2 hodd_uw hodd_wv
  have hxK : x ∈ X₀.subgroupOf (kSub V H E) := Subgroup.mem_subgroupOf.mpr hxX
  have hvK : v ∈ X₀.subgroupOf (kSub V H E) := Subgroup.mem_subgroupOf.mpr hvX
  have hyK : y₁ * y₂ ∈ X₀.subgroupOf (kSub V H E) :=
    Subgroup.mul_mem _ (closure_pair_subgroupOf_le huX₀ hwX hy₁mem)
      (closure_pair_subgroupOf_le hwX hvX hy₂mem)
  have hφy : φ (y₁ * y₂) = 1 ∨ φ (y₁ * y₂) = φ v :=
    map_eq_one_or_eq_map_of_conj_eq hv2 hw2 hφu hodd_vw hy₁mem hy₂mem hy
  have hvφ : φ v * φ v = 1 := by rw [← map_mul, hv2, map_one]
  rcases hφy with h1 | h1
  · refine ⟨x * (y₁ * y₂), Subgroup.mem_subgroupOf.mp (Subgroup.mul_mem _ hxK hyK),
      conj_mul_eq_of_conj hy, ?_⟩
    have hφg : φ (x * (y₁ * y₂)) = φ x := by rw [map_mul, h1, mul_one]
    rw [hφg]
    exact hx
  · refine ⟨x * (y₁ * y₂) * v, Subgroup.mem_subgroupOf.mp (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hxK hyK) hvK), conj_mul_mul_eq_of_conj hy hv2, ?_⟩
    have hφg : φ (x * (y₁ * y₂) * v) = φ x := by
      rw [map_mul, map_mul, h1, mul_assoc, hvφ, mul_one]
    rw [hφg]
    exact hx

end Lift

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
