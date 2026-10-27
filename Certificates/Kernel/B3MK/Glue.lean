module

public import Certificates.Kernel.B3MK.Checks
public import Certificates.Kernel.WEMK.Glue
public import CFSG.Certificates.Kernel.B3MKSound
public import CFSG.LocalAnalysis.StandardType.GGWitExcModelTransfer

public section

namespace CFSG.StandardType.ZS.B3MK

open Certificates.ExcModel Certificates.WEMK Certificates.B3MK CFSG.StandardType.ZS.WEMK CFSG.StandardType.ZS

theorem orderOf_conj {G : Type*} [Group G] (a x : G) : orderOf (a * x * a⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using
    (orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).toEquiv.injective x)

theorem orderOf_conj' {G : Type*} [Group G] (a x : G) : orderOf (a⁻¹ * x * a) = orderOf x := by
  simpa using orderOf_conj a⁻¹ x

theorem mem_closure_four_conj_iff {G : Type*} [Group G] (a r₁ r₂ r₃ r₄ t : G) :
    t ∈ Subgroup.closure ({r₁, r₂, r₃, r₄} : Set G) ↔
    a⁻¹ * t * a ∈
      Subgroup.closure ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a, a⁻¹ * r₄ * a} : Set G) := by
  have hset : (MulAut.conj a⁻¹) '' ({r₁, r₂, r₃, r₄} : Set G) =
      ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a, a⁻¹ * r₄ * a} : Set G) := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨r₁, by simp, by simp⟩
      · exact ⟨r₂, by simp, by simp⟩
      · exact ⟨r₃, by simp, by simp⟩
      · exact ⟨r₄, by simp, by simp⟩
  have hmap : Subgroup.closure
      ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a, a⁻¹ * r₄ * a} : Set G) =
      Subgroup.map (MulAut.conj a⁻¹).toMonoidHom
        (Subgroup.closure ({r₁, r₂, r₃, r₄} : Set G)) := by
    rw [MonoidHom.map_closure]
    exact congrArg Subgroup.closure hset.symm
  rw [hmap]
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · intro ht
    exact ⟨t, ht, by simp [mul_assoc]⟩
  · rintro ⟨x, hx, hxt⟩
    have hxt' : x = t := by
      calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
        _ = a * (a⁻¹ * t * a) * a⁻¹ := by rw [hxt]
        _ = t := by group
    rwa [hxt'] at hx

theorem card_closure_four_conj {G : Type*} [Group G] (a r₁ r₂ r₃ r₄ : G) :
    Nat.card (Subgroup.closure ({r₁, r₂, r₃, r₄} : Set G)) =
    Nat.card (Subgroup.closure
      ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a, a⁻¹ * r₄ * a} : Set G)) := by
  have hset : (MulAut.conj a⁻¹) '' ({r₁, r₂, r₃, r₄} : Set G) =
      ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a, a⁻¹ * r₄ * a} : Set G) := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨r₁, by simp, by simp⟩
      · exact ⟨r₂, by simp, by simp⟩
      · exact ⟨r₃, by simp, by simp⟩
      · exact ⟨r₄, by simp, by simp⟩
  have hmap : Subgroup.map (MulAut.conj a⁻¹).toMonoidHom
      (Subgroup.closure ({r₁, r₂, r₃, r₄} : Set G)) =
      Subgroup.closure ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a, a⁻¹ * r₄ * a} : Set G) := by
    rw [MonoidHom.map_closure]
    exact congrArg Subgroup.closure hset
  rw [← hmap]
  exact Nat.card_congr ((Subgroup.closure ({r₁, r₂, r₃, r₄} : Set G)).equivMapOfInjective
    (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective)

theorem mem_closure_three_conj_iff {G : Type*} [Group G] (a r₁ r₂ r₃ t : G) :
    t ∈ Subgroup.closure ({r₁, r₂, r₃} : Set G) ↔
    a⁻¹ * t * a ∈ Subgroup.closure ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a} : Set G) := by
  have hset : (MulAut.conj a⁻¹) '' ({r₁, r₂, r₃} : Set G) =
      ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a} : Set G) := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨r₁, by simp, by simp⟩
      · exact ⟨r₂, by simp, by simp⟩
      · exact ⟨r₃, by simp, by simp⟩
  have hmap : Subgroup.closure ({a⁻¹ * r₁ * a, a⁻¹ * r₂ * a, a⁻¹ * r₃ * a} : Set G) =
      Subgroup.map (MulAut.conj a⁻¹).toMonoidHom (Subgroup.closure ({r₁, r₂, r₃} : Set G)) := by
    rw [MonoidHom.map_closure]
    exact congrArg Subgroup.closure hset.symm
  rw [hmap]
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · intro ht
    exact ⟨t, ht, by simp [mul_assoc]⟩
  · rintro ⟨x, hx, hxt⟩
    have hx' : x = t := by
      calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
        _ = a * (a⁻¹ * t * a) * a⁻¹ := by rw [hxt]
        _ = t := by group
    rwa [hx'] at hx

theorem card_closure_coe {G : Type*} [Group G] {A : Subgroup G} (s : Set ↥A) :
    Nat.card (Subgroup.closure (Subtype.val '' s)) = Nat.card (Subgroup.closure s) := by
  have hmap : Subgroup.closure (Subtype.val '' s) = Subgroup.map A.subtype (Subgroup.closure s) := by
    rw [MonoidHom.map_closure]
    rfl
  rw [hmap]
  exact Nat.card_congr ((Subgroup.closure s).equivMapOfInjective A.subtype A.subtype_injective).symm

theorem mem_closure_coe_iff {G : Type*} [Group G] {A : Subgroup G} (s : Set ↥A) (x : ↥A) :
    (x : G) ∈ Subgroup.closure (Subtype.val '' s) ↔ x ∈ Subgroup.closure s := by
  have hmap : Subgroup.closure (Subtype.val '' s) = Subgroup.map A.subtype (Subgroup.closure s) := by
    rw [MonoidHom.map_closure]
    rfl
  rw [hmap]
  exact Subgroup.mem_map_iff_mem A.subtype_injective

theorem orderOf_psi_mul {n : ℕ} {gens : Set (Mat n)} {p : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (f : ↥(glClosure gens) ≃* ↥A)
    (r₁ r₂ : U ≃ₗ[ZMod p] U) (h₁ : r₁ ∈ A) (h₂ : r₂ ∈ A) (k : ℕ)
    (h : orderOf (r₁ * r₂) = k) :
    orderOf (((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₁, h₁⟩ *
             ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₂, h₂⟩) = k := by
  let Ψ := (glClosure gens).subtype.comp f.symm.toMonoidHom
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    apply f.symm.injective
    exact Subtype.ext hxy
  have h_order : orderOf (⟨r₁ * r₂, mul_mem h₁ h₂⟩ : ↥A) = k := by
    simpa using h
  have h_eq : Ψ ⟨r₁, h₁⟩ * Ψ ⟨r₂, h₂⟩ = Ψ (⟨r₁ * r₂, mul_mem h₁ h₂⟩ : ↥A) := by
    rw [← map_mul]
    rfl
  rw [h_eq, orderOf_injective Ψ hΨinj, h_order]

theorem card_closure_four_psi {n : ℕ} {gens : Set (Mat n)} {p : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (f : ↥(glClosure gens) ≃* ↥A)
    (r₁ r₂ r₃ r₄ : U ≃ₗ[ZMod p] U) (h₁ : r₁ ∈ A) (h₂ : r₂ ∈ A) (h₃ : r₃ ∈ A) (h₄ : r₄ ∈ A) :
    Nat.card (Subgroup.closure ({r₁, r₂, r₃, r₄} : Set (U ≃ₗ[ZMod p] U))) =
    Nat.card (Subgroup.closure
      ({((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₁, h₁⟩,
        ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₂, h₂⟩,
        ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₃, h₃⟩,
        ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₄, h₄⟩} : Set (owEm_GL n))) := by
  let Ψ := (glClosure gens).subtype.comp f.symm.toMonoidHom
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    apply f.symm.injective
    exact Subtype.ext hxy
  let sA : Set ↥A := {⟨r₁, h₁⟩, ⟨r₂, h₂⟩, ⟨r₃, h₃⟩, ⟨r₄, h₄⟩}
  have hset : ({r₁, r₂, r₃, r₄} : Set (U ≃ₗ[ZMod p] U)) = Subtype.val '' sA := by
    ext x
    simp [sA]
  have hsetΨ : Ψ '' sA =
      ({Ψ ⟨r₁, h₁⟩, Ψ ⟨r₂, h₂⟩, Ψ ⟨r₃, h₃⟩, Ψ ⟨r₄, h₄⟩} : Set (owEm_GL n)) := by
    ext x
    simp [sA]
  rw [hset, card_closure_coe sA, ← hsetΨ]
  exact (owEm_card_closure_map Ψ hΨinj sA).symm

theorem mem_closure_four_psi_iff {n : ℕ} {gens : Set (Mat n)} {p : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (f : ↥(glClosure gens) ≃* ↥A)
    (r₁ r₂ r₃ r₄ t : U ≃ₗ[ZMod p] U) (h₁ : r₁ ∈ A) (h₂ : r₂ ∈ A) (h₃ : r₃ ∈ A) (h₄ : r₄ ∈ A)
    (ht : t ∈ A) :
    t ∈ Subgroup.closure ({r₁, r₂, r₃, r₄} : Set (U ≃ₗ[ZMod p] U)) ↔
    ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨t, ht⟩ ∈
    Subgroup.closure
      ({((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₁, h₁⟩,
        ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₂, h₂⟩,
        ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₃, h₃⟩,
        ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₄, h₄⟩} : Set (owEm_GL n)) := by
  let Ψ := (glClosure gens).subtype.comp f.symm.toMonoidHom
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    apply f.symm.injective
    exact Subtype.ext hxy
  let sA : Set ↥A := {⟨r₁, h₁⟩, ⟨r₂, h₂⟩, ⟨r₃, h₃⟩, ⟨r₄, h₄⟩}
  have hset : ({r₁, r₂, r₃, r₄} : Set (U ≃ₗ[ZMod p] U)) = Subtype.val '' sA := by
    ext x
    simp [sA]
  have hsetΨ : Ψ '' sA =
      ({Ψ ⟨r₁, h₁⟩, Ψ ⟨r₂, h₂⟩, Ψ ⟨r₃, h₃⟩, Ψ ⟨r₄, h₄⟩} : Set (owEm_GL n)) := by
    ext x
    simp [sA]
  have hmemA : t ∈ Subgroup.closure ({r₁, r₂, r₃, r₄} : Set (U ≃ₗ[ZMod p] U)) ↔
      ⟨t, ht⟩ ∈ Subgroup.closure sA := by
    rw [hset]
    exact mem_closure_coe_iff sA ⟨t, ht⟩
  have hmemΨ : Ψ ⟨t, ht⟩ ∈ Subgroup.closure
      ({Ψ ⟨r₁, h₁⟩, Ψ ⟨r₂, h₂⟩, Ψ ⟨r₃, h₃⟩, Ψ ⟨r₄, h₄⟩} : Set (owEm_GL n)) ↔
      ⟨t, ht⟩ ∈ Subgroup.closure sA := by
    have hmap : Subgroup.closure
        ({Ψ ⟨r₁, h₁⟩, Ψ ⟨r₂, h₂⟩, Ψ ⟨r₃, h₃⟩, Ψ ⟨r₄, h₄⟩} : Set (owEm_GL n)) =
        Subgroup.map Ψ (Subgroup.closure sA) := by
      rw [MonoidHom.map_closure]
      exact congrArg Subgroup.closure hsetΨ.symm
    rw [hmap]
    exact Subgroup.mem_map_iff_mem hΨinj
  exact hmemA.trans hmemΨ.symm

theorem mem_closure_three_psi_iff {n : ℕ} {gens : Set (Mat n)} {p : ℕ} {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (f : ↥(glClosure gens) ≃* ↥A) (r₁ r₂ r₃ t : U ≃ₗ[ZMod p] U)
    (h₁ : r₁ ∈ A) (h₂ : r₂ ∈ A) (h₃ : r₃ ∈ A) (ht : t ∈ A) :
    t ∈ Subgroup.closure ({r₁, r₂, r₃} : Set (U ≃ₗ[ZMod p] U)) ↔
    ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨t, ht⟩ ∈
      Subgroup.closure ({((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₁, h₁⟩,
        ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₂, h₂⟩,
        ((glClosure gens).subtype.comp f.symm.toMonoidHom) ⟨r₃, h₃⟩} : Set (owEm_GL n)) := by
  let Ψ := (glClosure gens).subtype.comp f.symm.toMonoidHom
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    apply f.symm.injective
    exact Subtype.ext hxy
  let sA : Set ↥A := {⟨r₁, h₁⟩, ⟨r₂, h₂⟩, ⟨r₃, h₃⟩}
  have hset : ({r₁, r₂, r₃} : Set (U ≃ₗ[ZMod p] U)) = Subtype.val '' sA := by
    ext x
    simp [sA]
  have hsetΨ : Ψ '' sA =
      ({Ψ ⟨r₁, h₁⟩, Ψ ⟨r₂, h₂⟩, Ψ ⟨r₃, h₃⟩} : Set (owEm_GL n)) := by
    ext x
    simp [sA]
  have hmemA : t ∈ Subgroup.closure ({r₁, r₂, r₃} : Set (U ≃ₗ[ZMod p] U)) ↔
      ⟨t, ht⟩ ∈ Subgroup.closure sA := by
    rw [hset]
    exact mem_closure_coe_iff sA ⟨t, ht⟩
  have hmemΨ : Ψ ⟨t, ht⟩ ∈ Subgroup.closure
      ({Ψ ⟨r₁, h₁⟩, Ψ ⟨r₂, h₂⟩, Ψ ⟨r₃, h₃⟩} : Set (owEm_GL n)) ↔
      ⟨t, ht⟩ ∈ Subgroup.closure sA := by
    have hmap : Subgroup.closure
        ({Ψ ⟨r₁, h₁⟩, Ψ ⟨r₂, h₂⟩, Ψ ⟨r₃, h₃⟩} : Set (owEm_GL n)) =
        Subgroup.map Ψ (Subgroup.closure sA) := by
      rw [MonoidHom.map_closure]
      exact congrArg Subgroup.closure hsetΨ.symm
    rw [hmap]
    exact Subgroup.mem_map_iff_mem hΨinj
  exact hmemA.trans hmemΨ.symm

theorem prod_mem_of (K : Subgroup (owEm_GL 4)) :
    ∀ L : List (Mat 4), (∀ x ∈ L, ∃ g ∈ K, (g : Mat 4) = x) → ∃ g ∈ K, (g : Mat 4) = L.prod
  | [], _ => ⟨1, one_mem _, by simp⟩
  | x :: L, h => by
    obtain ⟨g, hg, rfl⟩ := h x (by simp)
    obtain ⟨g', hg', e⟩ := prod_mem_of K L (fun y hy => h y (by simp [hy]))
    exact ⟨g * g', mul_mem hg hg', by rw [Units.val_mul, e, List.prod_cons]⟩

theorem ord2_facts {G : Type*} [Group G] {y : G} (h : orderOf y = 2) : y ≠ 1 ∧ y ^ 2 = 1 := by
  refine ⟨fun e => ?_, by rw [← h]; exact pow_orderOf_eq_one y⟩
  rw [e, orderOf_one] at h
  exact absurd h (by norm_num)

theorem ord4_facts {G : Type*} [Group G] {y : G} (h : orderOf y = 4) : y ^ 2 ≠ 1 ∧ y ^ 4 = 1 := by
  refine ⟨fun e => ?_, by rw [← h]; exact pow_orderOf_eq_one y⟩
  have := orderOf_dvd_of_pow_eq_one e
  rw [h] at this
  exact absurd this (by norm_num)

theorem o2W_units {a b : ℕ} {x y : owEm_GL 4} (ha : wfW a = true) (hb : wfW b = true)
    (hx : (x : Mat 4) = decW a) (hy : (y : Mat 4) = decW b) (h : orderOf (x * y) = 2) : o2W a b = true := by
  obtain ⟨h1, h2⟩ := ord2_facts h
  apply o2W_of ha hb
  · rw [← hx, ← hy, ← Units.val_mul]
    exact fun e => h1 (Units.ext (by rw [e, Units.val_one]))
  · rw [← hx, ← hy, ← Units.val_mul, ← Units.val_pow_eq_pow_val, h2, Units.val_one]

theorem o4W_units {a b : ℕ} {x y : owEm_GL 4} (ha : wfW a = true) (hb : wfW b = true)
    (hx : (x : Mat 4) = decW a) (hy : (y : Mat 4) = decW b) (h : orderOf (x * y) = 4) : o4W a b = true := by
  obtain ⟨h1, h2⟩ := ord4_facts h
  apply o4W_of ha hb
  · rw [← hx, ← hy, ← Units.val_mul, ← Units.val_pow_eq_pow_val]
    exact fun e => h1 (Units.ext (by rw [e, Units.val_one]))
  · rw [← hx, ← hy, ← Units.val_mul, ← Units.val_pow_eq_pow_val, h2, Units.val_one]

theorem forall_mem_of_getD {P : ℕ → Prop} {l : List ℕ} (h : ∀ c < l.length, P (l.getD c 0)) : ∀ x ∈ l, P x := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hx
  have := h c hc
  rwa [List.getD_eq_getElem _ _ hc] at this

structure RowData (M : Subgroup (owEm_GL 4)) (VW : List ℕ) (x0 : ℕ) (r0 : owEm_GL 4) : Prop where
  mem : r0 ∈ M
  val : (r0 : Mat 4) = decW (VW.getD 0 0)
  inv : r0 * r0 = 1
  refl : IsReflMat r0
  len : 0 < VW.length
  wf : ∀ i < VW.length, wfW (VW.getD i 0) = true
  x0lt : x0 < VW.length
  conj : ∀ i < VW.length, ∃ m ∈ M, ((m * r0 * m⁻¹ : owEm_GL 4) : Mat 4) = decW (VW.getD i 0)
  cls : ∀ m ∈ M, ∃ i < VW.length, ((m * r0 * m⁻¹ : owEm_GL 4) : Mat 4) = decW (VW.getD i 0)
  one : ∀ x ∈ M, IsReflMat x → ∃ m ∈ M, x = m * r0 * m⁻¹
  fix : ∀ x ∈ M, IsReflMat x → orderOf (r0 * x) = 3 →
    ∃ b ∈ M, b * r0 * b⁻¹ = r0 ∧ ((b * x * b⁻¹ : owEm_GL 4) : Mat 4) = decW (VW.getD x0 0)

theorem RowData.refl_cls {M : Subgroup (owEm_GL 4)} {VW : List ℕ} {x0 : ℕ} {r0 : owEm_GL 4}
    (hd : RowData M VW x0 r0) {x : owEm_GL 4} (hx : x ∈ M) (hr : IsReflMat x) :
    ∃ i < VW.length, (x : Mat 4) = decW (VW.getD i 0) := by
  obtain ⟨m, hm, rfl⟩ := hd.one x hx hr
  exact hd.cls m hm

theorem vw_bridge {V : List KPair} {VW : List ℕ} (h : ((V.map fun q => toW (mat 4 q)) == VW) = true) :
    VW.length = V.length ∧ ∀ i < V.length, wfW (VW.getD i 0) = true ∧ decW (VW.getD i 0) = Lm 4 V i := by
  have e := eq_of_beq h
  subst e
  refine ⟨by simp, fun i hi => ?_⟩
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, Lm, List.getD_eq_getElem _ _ hi]
  exact decW_toW_mat _

theorem rowData_of {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (S : List NMat) (V : List KPair) (tab : List (List ℕ)) (par : List (ℕ × ℕ)) (wd : List (List ℕ))
    (x0 t0 : ℕ) (tr : List (ℕ × ℕ)) (ord : List ℕ) (h : kCore 4 S V tab par wd x0 t0 tr ord = true)
    (hS0 : 0 < S.length) (gens : Set (Mat 4)) (hSg : ∀ s < S.length, toM 4 (S.getD s []) ∈ gens)
    (hgX : ∀ g ∈ gens, ∃ i < V.length, Lm 4 V i = g)
    (hrefl : ∀ g : owEm_GL 4, (g : Mat 4) = toM 4 (S.getD 0 []) → (g : Mat 4) * g = 1 → IsReflMat g)
    (f : ↥(glClosure gens) ≃* ↥A)
    (hf : ∀ g : ↥(glClosure gens), IsReflMat (g : owEm_GL 4) ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) {VW : List ℕ} (hlen : VW.length = V.length)
    (hVW : ∀ i < V.length, wfW (VW.getD i 0) = true ∧ decW (VW.getD i 0) = Lm 4 V i) :
    ∃ r0, RowData (glClosure gens) VW x0 r0 := by
  simp only [kCore, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf, hinv⟩, hV0⟩, h0⟩, htab⟩, hpar⟩, hwit⟩, -⟩ := h
  rw [decide_eq_true_eq] at hV0 h0
  have hSf : ∀ s ∈ S, WF 4 s ∧ toM 4 s * toM 4 s = 1 := by
    intro s hs
    have w := List.all_eq_true.mp hwf s hs
    simp only [wfM, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at w
    have i := List.all_eq_true.mp hinv s hs
    simp only [isOneN, decide_eq_true_eq] at i
    refine ⟨⟨w.1, w.2⟩, ?_⟩
    rw [← toM_nmul 4 s s w.1 ⟨w.1, w.2⟩, i, idN_spec]
  have hSi : ∀ s < S.length, toM 4 (S.getD s []) * toM 4 (S.getD s []) = 1 := fun s hs =>
    (hSf _ (by rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem hs)).2
  let gu : ℕ → owEm_GL 4 := fun s => if hs : s < S.length then owEm_unit _ (hSi s hs) else 1
  let H : Subgroup (owEm_GL 4) := Subgroup.closure {g | ∃ s < S.length, g = gu s}
  have hguv : ∀ s < S.length, (gu s : Mat 4) = toM 4 (S.getD s []) := fun s hs => by simp [gu, hs, owEm_unit]
  have hgu : ∀ s < S.length, gu s ∈ H ∧ (gu s)⁻¹ = gu s := fun s hs =>
    ⟨Subgroup.subset_closure ⟨s, hs, rfl⟩, by simp only [gu, hs, dif_pos, owEm_unit_inv]⟩
  have htab' : ∀ i < V.length, ∀ s < S.length, (tab.getD i []).getD s 0 < V.length ∧
      (gu s : Mat 4) * Lm 4 V i * (gu s : Mat 4) = Lm 4 V ((tab.getD i []).getD s 0) := by
    intro i hi s hs
    rw [hguv s hs]
    exact tab_sound htab hSf hi hs
  let r0 := gu 0
  have hr0 : (r0 : Mat 4) = Lm 4 V 0 := by
    change (gu 0 : Mat 4) = _
    rw [hguv 0 hS0, Lm, h0]
  have hr0H : r0 ∈ H := (hgu 0 hS0).1
  have hconj := par_conj H gu S.length V.length (Lm 4 V) tab par r0 hr0 hgu htab' (par_sound hpar)
  have hM : glClosure gens = H := by
    apply le_antisymm
    · unfold glClosure
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨i, hi, hig⟩ := hgX _ hg
      obtain ⟨m, hm, e⟩ := hconj i hi
      have : g = m * r0 * m⁻¹ := Units.ext (by rw [e, hig])
      rw [this]
      exact mul_mem (mul_mem hm hr0H) (inv_mem hm)
    · unfold glClosure
      rw [Subgroup.closure_le]
      rintro g ⟨s, hs, rfl⟩
      apply Subgroup.subset_closure
      change (gu s : Mat 4) ∈ gens
      rw [hguv s hs]
      exact hSg s hs
  let X : Set (owEm_GL 4) := {x | ∃ i < V.length, (x : Mat 4) = Lm 4 V i}
  have hgen : ∀ s < S.length, ∀ x ∈ X, gu s * x * gu s ∈ X := by
    rintro s hs x ⟨i, hi, hx⟩
    obtain ⟨hj, e⟩ := htab' i hi s hs
    exact ⟨_, hj, by rw [← e, ← hx]; simp only [Units.val_mul]⟩
  have hcl : ∀ m ∈ H, ∀ x ∈ X, m * x * m⁻¹ ∈ X ∧ m⁻¹ * x * m ∈ X := by
    intro m hm
    induction hm using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨s, hs, rfl⟩ := hg
      intro x hx
      rw [(hgu s hs).2]
      exact ⟨hgen s hs x hx, hgen s hs x hx⟩
    | one => intro x hx; simpa using hx
    | mul a b _ _ iha ihb =>
      intro x hx
      refine ⟨?_, ?_⟩
      · have := (iha _ (ihb x hx).1).1
        simpa [mul_assoc] using this
      · have := (ihb _ (iha x hx).2).2
        simpa [mul_assoc] using this
    | inv a _ iha =>
      intro x hx
      have := iha x hx
      rw [inv_inv]
      exact ⟨this.2, this.1⟩
  obtain ⟨hx0, hwd⟩ := wit_sound hwit
  have hr0M : r0 ∈ glClosure gens := by rw [hM]; exact hr0H
  have hrr : r0 * r0 = 1 := by
    have e : r0⁻¹ = r0 := (hgu 0 hS0).2
    calc r0 * r0 = r0 * r0⁻¹ := by rw [e]
      _ = 1 := mul_inv_cancel r0
  have hrefl0 : IsReflMat r0 := hrefl r0 (hguv 0 hS0) (by rw [← Units.val_mul, hrr, Units.val_one])
  have hcls : ∀ m ∈ glClosure gens, ∃ i < V.length, ((m * r0 * m⁻¹ : owEm_GL 4) : Mat 4) = Lm 4 V i := by
    intro m hm
    exact (hcl m (by rw [← hM]; exact hm) r0 ⟨0, hV0, hr0⟩).1
  have hone' : ∀ x ∈ glClosure gens, IsReflMat x → ∃ m ∈ glClosure gens, x = m * r0 * m⁻¹ := by
    intro x hx hxr
    have hA0 := (hf ⟨r0, hr0M⟩).mp hrefl0
    have hAx := (hf ⟨x, hx⟩).mp hxr
    obtain ⟨g, hg, hge⟩ := hone _ (f ⟨r0, hr0M⟩).2 _ (f ⟨x, hx⟩).2 hA0 hAx
    have e : f ⟨x, hx⟩ = ⟨g, hg⟩ * f ⟨r0, hr0M⟩ * ⟨g, hg⟩⁻¹ := Subtype.ext hge
    have e2 : (⟨x, hx⟩ : ↥(glClosure gens)) = f.symm ⟨g, hg⟩ * ⟨r0, hr0M⟩ * (f.symm ⟨g, hg⟩)⁻¹ := by
      apply f.injective
      rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    refine ⟨(f.symm ⟨g, hg⟩ : owEm_GL 4), (f.symm ⟨g, hg⟩).2, ?_⟩
    have := congrArg Subtype.val e2
    simpa using this
  refine ⟨r0, ⟨hr0M, by rw [hr0, (hVW 0 hV0).2], hrr, hrefl0, by omega, fun i hi => (hVW i (by omega)).1,
    by omega, fun i hi => ?_, fun m hm => ?_, hone', ?_⟩⟩
  · obtain ⟨m, hm, e⟩ := hconj i (by omega)
    exact ⟨m, by rw [hM]; exact hm, by rw [e, (hVW i (by omega)).2]⟩
  · obtain ⟨i, hi, e⟩ := hcls m hm
    exact ⟨i, by omega, by rw [e, (hVW i hi).2]⟩
  · intro x hx hxr hord
    obtain ⟨m0, hm0, hxe0⟩ := hone' x hx hxr
    obtain ⟨i, hi, hxi⟩ := hcls m0 hm0
    rw [← hxe0] at hxi
    have h1 : r0 * x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    have h3 : (r0 * x) ^ 3 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    have h1' : (r0 : Mat 4) * x ≠ 1 := fun h' => h1 (Units.ext (by simpa using h'))
    have h3' : (r0 : Mat 4) * x * ((r0 : Mat 4) * x) * ((r0 : Mat 4) * x) = 1 := by
      have := congrArg (fun u : owEm_GL 4 => (u : Mat 4)) h3
      simpa [pow_succ, mul_assoc] using this
    rw [hr0, hxi] at h1' h3'
    have ha := a2N_of 4 _ _ (wf_mat 4 _) (wf_mat 4 _) h1' h3'
    obtain ⟨hw, hwalk⟩ := hwd i hi ha
    obtain ⟨m, hm, em0, emx⟩ := walk_sound H gu S.length V.length (Lm 4 V) tab hgu htab' (wd.getD i []) 0 x0
      hV0 hx0 hw
    rw [hwalk] at em0 emx
    obtain ⟨m1, hm1, e1⟩ := hconj x0 hx0
    generalize hx0d : m1 * r0 * m1⁻¹ = x0' at e1
    have hfix : m * r0 * m⁻¹ = r0 := Units.ext (by simp only [Units.val_mul]; rw [hr0, em0])
    have hxe : m * x0' * m⁻¹ = x := Units.ext (by simp only [Units.val_mul]; rw [e1, emx, hxi])
    refine ⟨m⁻¹, inv_mem (by rw [hM]; exact hm), ?_, ?_⟩
    · rw [inv_inv]
      conv_lhs => rw [← hfix]
      group
    · have : m⁻¹ * x * m⁻¹⁻¹ = x0' := by rw [← hxe]; group
      rw [this, e1, (hVW x0 hx0).2]

theorem norm_chain {M : Subgroup (owEm_GL 4)} {VW : List ℕ} {x0 : ℕ} {r0 : owEm_GL 4} (hd : RowData M VW x0 r0)
    {J : List ℕ} (hch : chainsOK (VW.getD 0 0) (VW.getD x0 0) J VW = true) {r₁ r₂ r₃ : owEm_GL 4}
    (h₁ : r₁ ∈ M) (h₂ : r₂ ∈ M) (h₃ : r₃ ∈ M) (hr₁ : IsReflMat r₁) (hr₂ : IsReflMat r₂) (hr₃ : IsReflMat r₃)
    (h12 : orderOf (r₁ * r₂) = 3) (h23 : orderOf (r₂ * r₃) = 4) (h13 : orderOf (r₁ * r₃) = 2) :
    ∃ b ∈ M, ∃ R2 R3 : owEm_GL 4, R2 ∈ M ∧ R3 ∈ M ∧ IsReflMat R2 ∧ IsReflMat R3 ∧
      b⁻¹ * r₁ * b = r0 ∧ b⁻¹ * r₂ * b = R2 ∧ b⁻¹ * r₃ * b = R3 ∧ (R2 : Mat 4) = decW (VW.getD x0 0) ∧
      ∃ j ∈ J, j < VW.length ∧ (R3 : Mat 4) = decW (VW.getD j 0) := by
  obtain ⟨a, ha, e1⟩ := hd.one r₁ h₁ hr₁
  have h2' : a⁻¹ * r₂ * a ∈ M := mul_mem (mul_mem (inv_mem ha) h₂) ha
  have hr2' : IsReflMat (a⁻¹ * r₂ * a) := by simpa using owEm_isReflMat_conj r₂ a⁻¹ hr₂
  have ho : orderOf (r0 * (a⁻¹ * r₂ * a)) = 3 := by
    have : r0 * (a⁻¹ * r₂ * a) = a⁻¹ * (r₁ * r₂) * a := by rw [e1]; group
    rw [this, orderOf_conj', h12]
  obtain ⟨c, hc, hcr0, hcv⟩ := hd.fix _ h2' hr2' ho
  have hbM : a * c⁻¹ ∈ M := mul_mem ha (inv_mem hc)
  have c1 : (a * c⁻¹)⁻¹ * r₁ * (a * c⁻¹) = r0 := by
    have : (a * c⁻¹)⁻¹ * r₁ * (a * c⁻¹) = c * r0 * c⁻¹ := by rw [e1]; group
    rw [this, hcr0]
  have c2 : (a * c⁻¹)⁻¹ * r₂ * (a * c⁻¹) = c * (a⁻¹ * r₂ * a) * c⁻¹ := by group
  have h3M : (a * c⁻¹)⁻¹ * r₃ * (a * c⁻¹) ∈ M := mul_mem (mul_mem (inv_mem hbM) h₃) hbM
  have h3r : IsReflMat ((a * c⁻¹)⁻¹ * r₃ * (a * c⁻¹)) := by
    simpa using owEm_isReflMat_conj r₃ (a * c⁻¹)⁻¹ hr₃
  obtain ⟨j, hj, hjv⟩ := hd.refl_cls h3M h3r
  have hR2v : ((c * (a⁻¹ * r₂ * a) * c⁻¹ : owEm_GL 4) : Mat 4) = decW (VW.getD x0 0) := hcv
  have ho2 : orderOf (r0 * ((a * c⁻¹)⁻¹ * r₃ * (a * c⁻¹))) = 2 := by
    rw [← c1]
    have : (a * c⁻¹)⁻¹ * r₁ * (a * c⁻¹) * ((a * c⁻¹)⁻¹ * r₃ * (a * c⁻¹)) =
        (a * c⁻¹)⁻¹ * (r₁ * r₃) * (a * c⁻¹) := by group
    rw [this, orderOf_conj', h13]
  have ho4 : orderOf (c * (a⁻¹ * r₂ * a) * c⁻¹ * ((a * c⁻¹)⁻¹ * r₃ * (a * c⁻¹))) = 4 := by
    rw [← c2]
    have : (a * c⁻¹)⁻¹ * r₂ * (a * c⁻¹) * ((a * c⁻¹)⁻¹ * r₃ * (a * c⁻¹)) =
        (a * c⁻¹)⁻¹ * (r₂ * r₃) * (a * c⁻¹) := by group
    rw [this, orderOf_conj', h23]
  have hjJ : j ∈ J := chainsOK_sound hch j hj
    (o2W_units (hd.wf 0 hd.len) (hd.wf j hj) hd.val hjv ho2)
    (o4W_units (hd.wf x0 hd.x0lt) (hd.wf j hj) hR2v hjv ho4)
  refine ⟨a * c⁻¹, hbM, c * (a⁻¹ * r₂ * a) * c⁻¹, (a * c⁻¹)⁻¹ * r₃ * (a * c⁻¹),
    mul_mem (mul_mem hc h2') (inv_mem hc), h3M, owEm_isReflMat_conj _ c hr2', h3r, c1, c2, rfl, hR2v,
    j, hjJ, hj, hjv⟩

section N4

open CFSG.KD.B3MK

theorem n4_facts : N4.VW.length = 40 ∧ N4.x0 = CFSG.KD.WEMK.N4.x0 ∧ N4.J = [27] ∧ N4.u0 < 40 ∧
    N4.r0 = N4.VW.getD 0 0 ∧ N4.r2 = N4.VW.getD N4.x0 0 ∧ N4.r3 = N4.VW.getD 27 0 ∧ N4.u = N4.VW.getD N4.u0 0 ∧
    N4.E.length = 384 ∧ N4.par.length = 384 ∧ N4.i0 < 384 ∧ getE N4.Ep N4.i0 = idW := by
  have g := n4_gens
  have l := n4_len
  have v := n4_vw
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, Nat.blt_eq, lenL_eq, List.cons.injEq, and_true] at g l v
  obtain ⟨⟨⟨hJ, hu0⟩, hlen⟩, er0, er2, er3, eu⟩ := g
  obtain ⟨⟨⟨hE, hp⟩, hi0⟩, hid⟩ := l
  exact ⟨hlen, v.2, hJ, hu0, er0, er2, er3, eu, hE, hp, hi0, hid⟩

theorem n4_core {M : Subgroup (owEm_GL 4)} {r0 : owEm_GL 4} (hd : RowData M N4.VW N4.x0 r0)
    {R2 R3 v w : owEm_GL 4} (hvM : v ∈ M) (hwM : w ∈ M) (h2r : IsReflMat R2) (h3r : IsReflMat R3)
    (h2 : (R2 : Mat 4) = decW (N4.VW.getD N4.x0 0)) (h3 : (R3 : Mat 4) = decW (N4.VW.getD 27 0))
    (hv : IsReflMat v) (hw : IsReflMat w)
    (hcard : Nat.card (Subgroup.closure ({r0, R2, R3, v} : Set (owEm_GL 4))) = 384)
    (hle : Nat.card (Subgroup.closure ({r0, R2, R3, w} : Set (owEm_GL 4))) ≤ 384) :
    w ∈ Subgroup.closure ({r0, R2, R3, v} : Set (owEm_GL 4)) := by
  obtain ⟨hlen, -, -, hu0, er0, er2, er3, eu, hEl, hpl, hi0, hid⟩ := n4_facts
  obtain ⟨m, hm, hmv⟩ := hd.conj N4.u0 (by omega)
  have hUr : IsReflMat (m * r0 * m⁻¹) := owEm_isReflMat_conj r0 m hd.refl
  have hgs : ∀ c < [N4.r0, N4.r2, N4.r3, N4.u].length, wfW ([N4.r0, N4.r2, N4.r3, N4.u].getD c 0) = true := by
    intro c hc
    rw [er0, er2, er3, eu]
    match c, hc with
    | 0, _ => exact hd.wf 0 (by omega)
    | 1, _ => exact hd.wf N4.x0 hd.x0lt
    | 2, _ => exact hd.wf 27 (by omega)
    | 3, _ => exact hd.wf N4.u0 (by omega)
  have hS : ∀ x ∈ ({r0, R2, R3, m * r0 * m⁻¹} : Set (owEm_GL 4)), x * x = 1 ∧
      ∃ c < [N4.r0, N4.r2, N4.r3, N4.u].length, (x : Mat 4) = decW ([N4.r0, N4.r2, N4.r3, N4.u].getD c 0) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [er0, er2, er3, eu]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨hd.inv, 0, by simp, hd.val⟩
    · exact ⟨h2r.1, 1, by simp, h2⟩
    · exact ⟨h3r.1, 2, by simp, h3⟩
    · exact ⟨hUr.1, 3, by simp, hmv⟩
  have hS' : ∀ c < [N4.r0, N4.r2, N4.r3, N4.u].length, ∃ x ∈ ({r0, R2, R3, m * r0 * m⁻¹} : Set (owEm_GL 4)),
      (x : Mat 4) = decW ([N4.r0, N4.r2, N4.r3, N4.u].getD c 0) := by
    intro c hc
    rw [er0, er2, er3, eu]
    match c, hc with
    | 0, _ => exact ⟨r0, by simp, hd.val⟩
    | 1, _ => exact ⟨R2, by simp, h2⟩
    | 2, _ => exact ⟨R3, by simp, h3⟩
    | 3, _ => exact ⟨m * r0 * m⁻¹, by simp, hmv⟩
  have hgs' := forall_mem_of_getD (P := fun x => wfW x = true) hgs
  have hT : ∀ x ∈ ({r0, R2, R3, m * r0 * m⁻¹} : Set (owEm_GL 4)),
      ∃ c < [N4.r0, N4.r2, N4.r3, N4.u].length, (x : Mat 4) = decW ([N4.r0, N4.r2, N4.r3, N4.u].getD c 0) :=
    fun x hx => (hS x hx).2
  have hW2 := elems_sub_closure n4_close n4_tree (hpl.trans hEl.symm) hEl.symm.le hid hgs' le_rfl hS'
  have hWc : Nat.card (Subgroup.closure ({r0, R2, R3, m * r0 * m⁻¹} : Set (owEm_GL 4))) = 384 :=
    (card_closure_elems n4_close n4_tree n4_incr (hpl.trans hEl.symm) hEl.symm.le (by omega) hid hgs' le_rfl hT
      hS').trans hEl
  have key : ∀ x ∈ M, IsReflMat x → x ∈ Subgroup.closure ({r0, R2, R3, m * r0 * m⁻¹} : Set (owEm_GL 4)) ∨
      m * r0 * m⁻¹ ∈ Subgroup.closure ({r0, R2, R3, x} : Set (owEm_GL 4)) := by
    intro x hxM hxr
    obtain ⟨k, hk, hxk⟩ := hd.refl_cls hxM hxr
    obtain ⟨-, hmw⟩ := mwOK_sound n4_mw
    rcases hmw k hk with ⟨hlt, hget⟩ | hev
    · left
      obtain ⟨y, hy, hyv⟩ := hW2 (N4.mw.getD k (0, [])).1 (by omega)
      rw [((elemsOK_sound n4_close).2 (N4.mw.getD k (0, [])).1 (by omega)).1] at hget
      have : y = x := Units.ext (by rw [hyv, hxk, hget])
      exact this ▸ hy
    · right
      have hwfs : ∀ y ∈ [N4.r0, N4.r2, N4.r3, N4.VW.getD k 0, idW], wfW y = true := by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl
        · rw [er0]; exact hd.wf 0 (by omega)
        · rw [er2]; exact hd.wf N4.x0 hd.x0lt
        · rw [er3]; exact hd.wf 27 (by omega)
        · exact hd.wf k hk
        · rw [← hid, ((elemsOK_sound n4_close).2 N4.i0 (by omega)).1]
          exact (elemsOK_sound n4_close).1 _ (getD_mem_of_lt (by omega))
      obtain ⟨-, hev'⟩ := evalW_spec _ _ _ _ (N4.mw.getD k (0, [])).2 _ hwfs
      rw [hev, decW_idW, mul_one] at hev'
      obtain ⟨g, hg, hgv⟩ := prod_mem_of (Subgroup.closure ({r0, R2, R3, x} : Set (owEm_GL 4)))
        ((N4.mw.getD k (0, [])).2.map fun l => decW (pick4 N4.r0 N4.r2 N4.r3 (N4.VW.getD k 0) l)).reverse (by
        intro y hy
        rw [List.mem_reverse] at hy
        obtain ⟨l, -, rfl⟩ := List.mem_map.mp hy
        rcases pick4_mem N4.r0 N4.r2 N4.r3 (N4.VW.getD k 0) l with e | e | e | e <;> rw [e]
        · exact ⟨r0, Subgroup.subset_closure (by simp), by rw [hd.val, er0]⟩
        · exact ⟨R2, Subgroup.subset_closure (by simp), by rw [h2, er2]⟩
        · exact ⟨R3, Subgroup.subset_closure (by simp), by rw [h3, er3]⟩
        · exact ⟨x, Subgroup.subset_closure (by simp), hxk⟩)
      have : g = m * r0 * m⁻¹ := Units.ext (by rw [hgv, ← hev', hmv, eu])
      exact this ▸ hg
  have inW : ∀ x ∈ M, IsReflMat x → Nat.card (Subgroup.closure ({r0, R2, R3, x} : Set (owEm_GL 4))) ≤ 384 →
      x ∈ Subgroup.closure ({r0, R2, R3, m * r0 * m⁻¹} : Set (owEm_GL 4)) := by
    intro x hxM hxr hc
    rcases key x hxM hxr with h | h
    · exact h
    · have hle' : Subgroup.closure ({r0, R2, R3, m * r0 * m⁻¹} : Set (owEm_GL 4)) ≤
          Subgroup.closure ({r0, R2, R3, x} : Set (owEm_GL 4)) := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact h
      rw [Subgroup.eq_of_le_of_card_ge hle' (by rw [hWc]; exact hc)]
      exact Subgroup.subset_closure (by simp)
  have hvW := inW v hvM hv (le_of_eq hcard)
  have hKv : Subgroup.closure ({r0, R2, R3, v} : Set (owEm_GL 4)) =
      Subgroup.closure ({r0, R2, R3, m * r0 * m⁻¹} : Set (owEm_GL 4)) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact hvW
    · rw [hcard, hWc]
  rw [hKv]
  exact inW w hwM hw hle

theorem n4_model {M : Subgroup (owEm_GL 4)} {r0 : owEm_GL 4} (hd : RowData M N4.VW N4.x0 r0)
    {r₁ r₂ r₃ r₄ t : owEm_GL 4} (h₁ : r₁ ∈ M) (h₂ : r₂ ∈ M) (h₃ : r₃ ∈ M) (h₄ : r₄ ∈ M) (ht : t ∈ M)
    (hr₁ : IsReflMat r₁) (hr₂ : IsReflMat r₂) (hr₃ : IsReflMat r₃) (hr₄ : IsReflMat r₄) (hrt : IsReflMat t)
    (h12 : orderOf (r₁ * r₂) = 3) (h23 : orderOf (r₂ * r₃) = 4) (h13 : orderOf (r₁ * r₃) = 2)
    (hW : Nat.card (Subgroup.closure ({r₁, r₂, r₃, r₄} : Set (owEm_GL 4))) = 384)
    (hle : Nat.card (Subgroup.closure ({r₁, r₂, r₃, t} : Set (owEm_GL 4))) ≤ 384) :
    t ∈ Subgroup.closure ({r₁, r₂, r₃, r₄} : Set (owEm_GL 4)) := by
  obtain ⟨-, -, hJ, -, er0, er2, -⟩ := n4_facts
  have hch : chainsOK (N4.VW.getD 0 0) (N4.VW.getD N4.x0 0) [27] N4.VW = true := by
    have := n4_chains
    rwa [er0, er2, hJ] at this
  obtain ⟨b, hb, R2, R3, -, -, h2r, h3r, c1, c2, c3, h2v, j, hj, -, h3v⟩ :=
    norm_chain hd hch h₁ h₂ h₃ hr₁ hr₂ hr₃ h12 h23 h13
  rw [List.mem_singleton] at hj
  subst hj
  have hcard := card_closure_four_conj b r₁ r₂ r₃ r₄
  have hcardt := card_closure_four_conj b r₁ r₂ r₃ t
  rw [c1, c2, c3] at hcard hcardt
  have hmem := mem_closure_four_conj_iff b r₁ r₂ r₃ r₄ t
  rw [c1, c2, c3] at hmem
  refine hmem.mpr (n4_core hd (mul_mem (mul_mem (inv_mem hb) h₄) hb) (mul_mem (mul_mem (inv_mem hb) ht) hb) h2r h3r
    h2v h3v (by simpa using owEm_isReflMat_conj r₄ b⁻¹ hr₄) (by simpa using owEm_isReflMat_conj t b⁻¹ hrt)
    (hcard.symm.trans hW) (hcardt ▸ hle))

theorem rowData_n4 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (f : ↥(glClosure n4Gens) ≃* ↥A)
    (hf : ∀ g : ↥(glClosure n4Gens), IsReflMat (g : owEm_GL 4) ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) : ∃ r0, RowData (glClosure n4Gens) N4.VW N4.x0 r0 := by
  have h := Bool.and_eq_true_iff.mp CFSG.KD.WEMK.n4_ok
  obtain ⟨hSg, hgX, h0⟩ := covN_gens (n4S ()) n4Gens (by
      intro s hs
      simp only [n4S, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [n4Gens, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hs with rfl | rfl | rfl | rfl <;> simp [owEm_strict]) (by
      intro g hg
      simp only [n4Gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact ⟨strict (piMat 0 1 1), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 1 2 1), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 0 1 5), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict aMat, by simp [n4S], owEm_strict _⟩) h.2
  have hb := vw_bridge (Bool.and_eq_true_iff.mp n4_vw).1
  rw [n4_facts.2.1]
  refine rowData_of CFSG.KD.WEMK.N4.S CFSG.KD.WEMK.N4.V CFSG.KD.WEMK.N4.tab CFSG.KD.WEMK.N4.par
    CFSG.KD.WEMK.N4.wd CFSG.KD.WEMK.N4.x0 CFSG.KD.WEMK.N4.t0 CFSG.KD.WEMK.N4.tr CFSG.KD.WEMK.N4.ord h.1
    (by decide +kernel) n4Gens hSg hgX ?_ f hf hone hb.1 hb.2
  intro g hg hgg
  have hg' : (g : Mat 4) = piMat 0 1 1 := by rw [hg, h0 (strict (piMat 0 1 1)) (by simp [n4S]), owEm_strict]
  exact owEm_isReflMat_of_outer g hgg ![1, -1, 0, 0] ![-1, 1, 0, 0] (by decide) (by decide)
    (by rw [hg']; exact owEm_piMat_sub_one)

end N4

theorem b3_n4 : ∀ {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)},
    OneClass p A → ModelIso p .N4 A → ∀ {r₁ r₂ r₃ r₄ t : U ≃ₗ[ZMod p] U}, r₁ ∈ A → r₂ ∈ A → r₃ ∈ A → r₄ ∈ A →
    t ∈ A → IsRefl p r₁ → IsRefl p r₂ → IsRefl p r₃ → IsRefl p r₄ → IsRefl p t →
    orderOf (r₁ * r₂) = 3 → orderOf (r₂ * r₃) = 4 → orderOf (r₁ * r₃) = 2 →
    Nat.card (Subgroup.closure {r₁, r₂, r₃, r₄}) = 384 → Nat.card (Subgroup.closure {r₁, r₂, r₃, t}) ≤ 384 →
    t ∈ Subgroup.closure {r₁, r₂, r₃, r₄} := by
  intro p U _ _ A hone hmod r₁ r₂ r₃ r₄ t h₁ h₂ h₃ h₄ ht hr₁ hr₂ hr₃ hr₄ hrt h12 h23 h13 hW hle
  obtain ⟨f, hf⟩ := hmod
  obtain ⟨r0, hd⟩ := rowData_n4 f hf hone
  have hR : ∀ (r : U ≃ₗ[ZMod p] U) (hr : r ∈ A), IsRefl p r →
      IsReflMat (((glClosure n4Gens).subtype.comp f.symm.toMonoidHom) ⟨r, hr⟩) := fun r hr h =>
    (hf (f.symm ⟨r, hr⟩)).mpr (by rw [MulEquiv.apply_symm_apply]; exact h)
  refine (mem_closure_four_psi_iff f r₁ r₂ r₃ r₄ t h₁ h₂ h₃ h₄ ht).mpr
    (n4_model hd (f.symm _).2 (f.symm _).2 (f.symm _).2 (f.symm _).2 (f.symm _).2 (hR _ h₁ hr₁) (hR _ h₂ hr₂)
      (hR _ h₃ hr₃) (hR _ h₄ hr₄) (hR _ ht hrt) (orderOf_psi_mul f r₁ r₂ h₁ h₂ 3 h12)
      (orderOf_psi_mul f r₂ r₃ h₂ h₃ 4 h23) (orderOf_psi_mul f r₁ r₃ h₁ h₃ 2 h13) ?_ ?_)
  · exact (card_closure_four_psi f r₁ r₂ r₃ r₄ h₁ h₂ h₃ h₄).symm.trans hW
  · exact (card_closure_four_psi f r₁ r₂ r₃ t h₁ h₂ h₃ ht).symm.trans_le hle

theorem ck51_core {M : Subgroup (owEm_GL 4)} {VW : List ℕ} {x0 : ℕ} {r0 : owEm_GL 4} (hd : RowData M VW x0 r0)
    {r3 Hp Tp i0 ia ib : ℕ} {H : List ℕ}
    (h : ck51 (VW.getD 0 0) (VW.getD x0 0) r3 H Hp Tp i0 (VW.getD ia 0) (VW.getD ib 0) = true)
    (hia : ia < VW.length) (hib : ib < VW.length) (hr3 : wfW r3 = true) {R2 R3 : owEm_GL 4}
    (h2r : IsReflMat R2) (h3r : IsReflMat R3)
    (h2 : (R2 : Mat 4) = decW (VW.getD x0 0)) (h3 : (R3 : Mat 4) = decW r3) :
    ∃ s₁ ∈ M, ∃ s₂ ∈ M, s₁ ≠ s₂ ∧ IsReflMat s₁ ∧ IsReflMat s₂ ∧
      Commute s₁ ((r0 * R2 * R3) ^ 3) ∧ Commute s₂ ((r0 * R2 * R3) ^ 3) ∧
      s₁ ∉ Subgroup.closure ({r0, R2, R3} : Set (owEm_GL 4)) ∧
      s₂ ∉ Subgroup.closure ({r0, R2, R3} : Set (owEm_GL 4)) := by
  obtain ⟨hi0, hid, hel, hne, hca, hcb, hna, hnb⟩ := ck51_sound h
  have w0 := hd.wf 0 hd.len
  have w2 := hd.wf x0 hd.x0lt
  have hgs : ∀ c < [VW.getD 0 0, VW.getD x0 0, r3].length, wfW ([VW.getD 0 0, VW.getD x0 0, r3].getD c 0) = true := by
    intro c hc
    match c, hc with
    | 0, _ => exact w0
    | 1, _ => exact w2
    | 2, _ => exact hr3
  have hS : ∀ x ∈ ({r0, R2, R3} : Set (owEm_GL 4)), x * x = 1 ∧
      ∃ c < [VW.getD 0 0, VW.getD x0 0, r3].length, (x : Mat 4) = decW ([VW.getD 0 0, VW.getD x0 0, r3].getD c 0) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hd.inv, 0, by simp, hd.val⟩
    · exact ⟨h2r.1, 1, by simp, h2⟩
    · exact ⟨h3r.1, 2, by simp, h3⟩
  have hsub := closure_sub_elems hel le_rfl hi0 hid (forall_mem_of_getD (P := fun x => wfW x = true) hgs) fun x hx => (hS x hx).2
  have hwfH := (elemsOK_sound hel).1
  have notin : ∀ (s : owEm_GL 4) (i : ℕ), i < VW.length → (s : Mat 4) = decW (VW.getD i 0) → VW.getD i 0 ∉ H →
      s ∉ Subgroup.closure ({r0, R2, R3} : Set (owEm_GL 4)) := by
    intro s i hi hs hn hmem
    obtain ⟨k, hk, hkv⟩ := hsub s hmem
    apply hn
    rw [wfW_inj (hd.wf i hi) (hwfH _ (getD_mem_of_lt hk)) (hs.symm.trans hkv)]
    exact getD_mem_of_lt hk
  obtain ⟨wq, eq⟩ := lmul_spec w2 hr3
  obtain ⟨ww, ew⟩ := lmul_spec w0 wq
  obtain ⟨ww2, ew2⟩ := lmul_spec ww ww
  obtain ⟨wz, ez⟩ := lmul_spec ww ww2
  have hz0 : zOf (VW.getD 0 0) (VW.getD x0 0) r3 = lmul (lmul (VW.getD 0 0) (lmul (VW.getD x0 0) r3))
      (lmul (lmul (VW.getD 0 0) (lmul (VW.getD x0 0) r3)) (lmul (VW.getD 0 0) (lmul (VW.getD x0 0) r3))) := rfl
  have hzv : (((r0 * R2 * R3) ^ 3 : owEm_GL 4) : Mat 4) = decW (zOf (VW.getD 0 0) (VW.getD x0 0) r3) := by
    rw [hz0, ez, ew2, ew, eq, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mul, hd.val, h2, h3, pow_three]
    simp only [mul_assoc]
  have hz : ∀ (s : owEm_GL 4) (i : ℕ), i < VW.length → (s : Mat 4) = decW (VW.getD i 0) →
      commZ (VW.getD i 0) (zOf (VW.getD 0 0) (VW.getD x0 0) r3) = true → Commute s ((r0 * R2 * R3) ^ 3) := by
    intro s i hi hs hc
    have hc' := Nat.eq_of_beq_eq_true hc
    have wz' : wfW (zOf (VW.getD 0 0) (VW.getD x0 0) r3) = true := by rw [hz0]; exact wz
    obtain ⟨-, e1⟩ := lmul_spec (hd.wf i hi) wz'
    obtain ⟨-, e2⟩ := lmul_spec wz' (hd.wf i hi)
    have : s * (r0 * R2 * R3) ^ 3 = (r0 * R2 * R3) ^ 3 * s :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, hs, hzv, ← e1, ← e2, hc'])
    exact this
  obtain ⟨ma, hma, hmav⟩ := hd.conj ia hia
  obtain ⟨mb, hmb, hmbv⟩ := hd.conj ib hib
  refine ⟨ma * r0 * ma⁻¹, mul_mem (mul_mem hma hd.mem) (inv_mem hma), mb * r0 * mb⁻¹,
    mul_mem (mul_mem hmb hd.mem) (inv_mem hmb), ?_, owEm_isReflMat_conj r0 ma hd.refl,
    owEm_isReflMat_conj r0 mb hd.refl, hz _ ia hia hmav hca, hz _ ib hib hmbv hcb, notin _ ia hia hmav hna,
    notin _ ib hib hmbv hnb⟩
  intro e
  apply hne
  exact wfW_inj (hd.wf ia hia) (hd.wf ib hib) (by rw [← hmav, ← hmbv, e])

section EN4

open CFSG.KD.B3MK

theorem en4_facts : EN4.VW.length = 60 ∧ EN4.x0 = CFSG.KD.WEMK.EN4.x0 ∧ EN4.J = [36, 47, 55] ∧
    EN4.r0 = EN4.VW.getD 0 0 ∧ EN4.r2 = EN4.VW.getD EN4.x0 0 ∧
    EN4.r3s = [EN4.VW.getD 36 0, EN4.VW.getD 47 0, EN4.VW.getD 55 0] ∧
    EN4.sas = [EN4.VW.getD 19 0, EN4.VW.getD 10 0, EN4.VW.getD 4 0] ∧
    EN4.sbs = [EN4.VW.getD 24 0, EN4.VW.getD 15 0, EN4.VW.getD 7 0] := by
  have g := en4_gens
  have v := en4_vw
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, lenL_eq, List.cons.injEq, and_true] at g v
  obtain ⟨⟨⟨⟨⟨⟨hJ, hw⟩, hl⟩, er0, er2⟩, e3⟩, ea⟩, eb⟩ := g
  rw [hJ] at e3
  rw [hw] at ea eb
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at e3 ea eb
  exact ⟨hl, v.2, hJ, er0, er2, e3, ea, eb⟩

theorem en4_model {M : Subgroup (owEm_GL 4)} {r0 : owEm_GL 4} (hd : RowData M EN4.VW EN4.x0 r0)
    {r₁ r₂ r₃ : owEm_GL 4} (h₁ : r₁ ∈ M) (h₂ : r₂ ∈ M) (h₃ : r₃ ∈ M)
    (hr₁ : IsReflMat r₁) (hr₂ : IsReflMat r₂) (hr₃ : IsReflMat r₃)
    (h12 : orderOf (r₁ * r₂) = 3) (h23 : orderOf (r₂ * r₃) = 4) (h13 : orderOf (r₁ * r₃) = 2) :
    ∃ s₁ ∈ M, ∃ s₂ ∈ M, s₁ ≠ s₂ ∧ IsReflMat s₁ ∧ IsReflMat s₂ ∧
      Commute s₁ ((r₁ * r₂ * r₃) ^ 3) ∧ Commute s₂ ((r₁ * r₂ * r₃) ^ 3) ∧
      s₁ ∉ Subgroup.closure ({r₁, r₂, r₃} : Set (owEm_GL 4)) ∧
      s₂ ∉ Subgroup.closure ({r₁, r₂, r₃} : Set (owEm_GL 4)) := by
  obtain ⟨hlen, -, hJ, er0, er2, e3, ea, eb⟩ := en4_facts
  have hch : chainsOK (EN4.VW.getD 0 0) (EN4.VW.getD EN4.x0 0) EN4.J EN4.VW = true := by
    have := en4_chains
    rwa [er0, er2] at this
  obtain ⟨b, hb, R2, R3, -, -, h2r, h3r, c1, c2, c3, h2v, j, hj, -, h3v⟩ :=
    norm_chain hd hch h₁ h₂ h₃ hr₁ hr₂ hr₃ h12 h23 h13
  have hcore : ∃ s₁ ∈ M, ∃ s₂ ∈ M, s₁ ≠ s₂ ∧ IsReflMat s₁ ∧ IsReflMat s₂ ∧
      Commute s₁ ((r0 * R2 * R3) ^ 3) ∧ Commute s₂ ((r0 * R2 * R3) ^ 3) ∧
      s₁ ∉ Subgroup.closure ({r0, R2, R3} : Set (owEm_GL 4)) ∧
      s₂ ∉ Subgroup.closure ({r0, R2, R3} : Set (owEm_GL 4)) := by
    rw [hJ] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · have h := en4_c0
      rw [er0, er2, e3, ea, eb] at h
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h
      exact ck51_core hd h (by omega) (by omega) (hd.wf _ (by omega)) h2r h3r h2v h3v
    · have h := en4_c1
      rw [er0, er2, e3, ea, eb] at h
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h
      exact ck51_core hd h (by omega) (by omega) (hd.wf _ (by omega)) h2r h3r h2v h3v
    · have h := en4_c2
      rw [er0, er2, e3, ea, eb] at h
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h
      exact ck51_core hd h (by omega) (by omega) (hd.wf _ (by omega)) h2r h3r h2v h3v
  obtain ⟨s₁, hs₁, s₂, hs₂, hne, hr1, hr2, hc1, hc2, hn1, hn2⟩ := hcore
  have hb3 : r₁ * r₂ * r₃ = b * (r0 * R2 * R3) * b⁻¹ := by rw [← c1, ← c2, ← c3]; group
  have hzc : (r₁ * r₂ * r₃) ^ 3 = b * (r0 * R2 * R3) ^ 3 * b⁻¹ := by rw [hb3, conj_pow]
  have hmem := fun s => mem_closure_three_conj_iff b r₁ r₂ r₃ (b * s * b⁻¹)
  refine ⟨b * s₁ * b⁻¹, mul_mem (mul_mem hb hs₁) (inv_mem hb), b * s₂ * b⁻¹, mul_mem (mul_mem hb hs₂) (inv_mem hb),
    ?_, owEm_isReflMat_conj s₁ b hr1, owEm_isReflMat_conj s₂ b hr2, ?_, ?_, ?_, ?_⟩
  · intro e
    apply hne
    calc s₁ = b⁻¹ * (b * s₁ * b⁻¹) * b := by group
      _ = b⁻¹ * (b * s₂ * b⁻¹) * b := by rw [e]
      _ = s₂ := by group
  · rw [hzc]
    exact (Commute.conj_iff b).mpr hc1
  · rw [hzc]
    exact (Commute.conj_iff b).mpr hc2
  · intro hm
    apply hn1
    have := (hmem s₁).mp hm
    have es : b⁻¹ * (b * s₁ * b⁻¹) * b = s₁ := by group
    rwa [c1, c2, c3, es] at this
  · intro hm
    apply hn2
    have := (hmem s₂).mp hm
    have es : b⁻¹ * (b * s₂ * b⁻¹) * b = s₂ := by group
    rwa [c1, c2, c3, es] at this

theorem rowData_en4 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (f : ↥(glClosure en4Gens) ≃* ↥A)
    (hf : ∀ g : ↥(glClosure en4Gens), IsReflMat (g : owEm_GL 4) ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) : ∃ r0, RowData (glClosure en4Gens) EN4.VW EN4.x0 r0 := by
  have h := Bool.and_eq_true_iff.mp CFSG.KD.WEMK.en4_ok
  obtain ⟨hSg, hgX, h0⟩ := covN_gens (en4S ()) en4Gens (by
      intro s hs
      simp only [en4S, n4S, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [en4Gens, n4Gens, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hs with (rfl | rfl | rfl | rfl) | rfl
      · exact Or.inl (Or.inl (owEm_strict _))
      · exact Or.inl (Or.inr (Or.inl (owEm_strict _)))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (owEm_strict _))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (owEm_strict _))))
      · exact Or.inr (owEm_strict _)) (by
      intro g hg
      simp only [en4Gens, n4Gens, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with (rfl | rfl | rfl | rfl) | rfl
      · exact ⟨strict (piMat 0 1 1), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 1 2 1), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 0 1 5), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict aMat, by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (Matrix.diagonal fun i => if i = 3 then -1 else 1),
          by unfold en4S; exact List.mem_append_right _ (List.mem_singleton_self _), owEm_strict _⟩) h.2
  have hb := vw_bridge (Bool.and_eq_true_iff.mp en4_vw).1
  rw [en4_facts.2.1]
  refine rowData_of CFSG.KD.WEMK.EN4.S CFSG.KD.WEMK.EN4.V CFSG.KD.WEMK.EN4.tab CFSG.KD.WEMK.EN4.par
    CFSG.KD.WEMK.EN4.wd CFSG.KD.WEMK.EN4.x0 CFSG.KD.WEMK.EN4.t0 CFSG.KD.WEMK.EN4.tr CFSG.KD.WEMK.EN4.ord h.1
    (by decide +kernel) en4Gens hSg hgX ?_ f hf hone hb.1 hb.2
  intro g hg hgg
  have hg' : (g : Mat 4) = piMat 0 1 1 := by
    rw [hg, h0 (strict (piMat 0 1 1)) (by simp [en4S, n4S]), owEm_strict]
  exact owEm_isReflMat_of_outer g hgg ![1, -1, 0, 0] ![-1, 1, 0, 0] (by decide) (by decide)
    (by rw [hg']; exact owEm_piMat_sub_one)

end EN4

theorem b3_en4 : ∀ {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)},
    OneClass p A → ModelIso p .EN4 A → ∀ {r₁ r₂ r₃ : U ≃ₗ[ZMod p] U}, r₁ ∈ A → r₂ ∈ A → r₃ ∈ A →
    IsRefl p r₁ → IsRefl p r₂ → IsRefl p r₃ → orderOf (r₁ * r₂) = 3 → orderOf (r₂ * r₃) = 4 →
    orderOf (r₁ * r₃) = 2 →
    ∃ s₁ ∈ A, ∃ s₂ ∈ A, s₁ ≠ s₂ ∧ IsRefl p s₁ ∧ IsRefl p s₂ ∧
      Commute s₁ ((r₁ * r₂ * r₃) ^ 3) ∧ Commute s₂ ((r₁ * r₂ * r₃) ^ 3) ∧
      s₁ ∉ Subgroup.closure {r₁, r₂, r₃} ∧ s₂ ∉ Subgroup.closure {r₁, r₂, r₃} := by
  intro p U _ _ A hone hmod r₁ r₂ r₃ h₁ h₂ h₃ hr₁ hr₂ hr₃ h12 h23 h13
  obtain ⟨f, hf⟩ : ∃ f : ↥(glClosure en4Gens) ≃* ↥A,
      ∀ g : ↥(glClosure en4Gens), IsReflMat g.1 ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U) := hmod
  obtain ⟨r0, hd⟩ := rowData_en4 f hf hone
  have hR : ∀ (r : U ≃ₗ[ZMod p] U) (hr : r ∈ A), IsRefl p r →
      IsReflMat ((f.symm ⟨r, hr⟩ : ↥(glClosure en4Gens)) : owEm_GL 4) := fun r hr h =>
    (hf (f.symm ⟨r, hr⟩)).mpr (by rw [MulEquiv.apply_symm_apply]; exact h)
  obtain ⟨s₁, hs₁, s₂, hs₂, hne, hr1, hr2, hc1, hc2, hn1, hn2⟩ :=
    en4_model hd (f.symm ⟨r₁, h₁⟩).2 (f.symm ⟨r₂, h₂⟩).2 (f.symm ⟨r₃, h₃⟩).2 (hR _ h₁ hr₁) (hR _ h₂ hr₂)
      (hR _ h₃ hr₃) (orderOf_psi_mul f r₁ r₂ h₁ h₂ 3 h12) (orderOf_psi_mul f r₂ r₃ h₂ h₃ 4 h23)
      (orderOf_psi_mul f r₁ r₃ h₁ h₃ 2 h13)
  have hcomm : ∀ (s : owEm_GL 4) (hs : s ∈ glClosure en4Gens),
      Commute s ((((f.symm ⟨r₁, h₁⟩ : ↥(glClosure en4Gens)) : owEm_GL 4) *
        ((f.symm ⟨r₂, h₂⟩ : ↥(glClosure en4Gens)) : owEm_GL 4) *
        ((f.symm ⟨r₃, h₃⟩ : ↥(glClosure en4Gens)) : owEm_GL 4)) ^ 3) →
      Commute (f ⟨s, hs⟩ : U ≃ₗ[ZMod p] U) ((r₁ * r₂ * r₃) ^ 3) := by
    intro s hs hc
    let c : ↥A := ⟨(r₁ * r₂ * r₃) ^ 3, pow_mem (mul_mem (mul_mem h₁ h₂) h₃) 3⟩
    have hc3 : c = (⟨r₁, h₁⟩ * ⟨r₂, h₂⟩ * ⟨r₃, h₃⟩) ^ 3 := Subtype.ext (by simp [c])
    have e3 : ((f.symm c : ↥(glClosure en4Gens)) : owEm_GL 4) =
        (((f.symm ⟨r₁, h₁⟩ : ↥(glClosure en4Gens)) : owEm_GL 4) *
          ((f.symm ⟨r₂, h₂⟩ : ↥(glClosure en4Gens)) : owEm_GL 4) *
          ((f.symm ⟨r₃, h₃⟩ : ↥(glClosure en4Gens)) : owEm_GL 4)) ^ 3 := by
      rw [hc3, map_pow, map_mul, map_mul]
      rfl
    have hM : Commute (⟨s, hs⟩ : ↥(glClosure en4Gens)) (f.symm c) := Subtype.ext (by
      change s * ((f.symm c : ↥(glClosure en4Gens)) : owEm_GL 4) =
        ((f.symm c : ↥(glClosure en4Gens)) : owEm_GL 4) * s
      rw [e3]
      exact hc)
    have hA : Commute (f ⟨s, hs⟩) c := by simpa using hM.map f.toMonoidHom
    simpa [c] using hA.map A.subtype
  have hnot : ∀ (s : owEm_GL 4) (hs : s ∈ glClosure en4Gens),
      s ∉ Subgroup.closure ({((f.symm ⟨r₁, h₁⟩ : ↥(glClosure en4Gens)) : owEm_GL 4),
        ((f.symm ⟨r₂, h₂⟩ : ↥(glClosure en4Gens)) : owEm_GL 4),
        ((f.symm ⟨r₃, h₃⟩ : ↥(glClosure en4Gens)) : owEm_GL 4)} : Set (owEm_GL 4)) →
      (f ⟨s, hs⟩ : U ≃ₗ[ZMod p] U) ∉ Subgroup.closure ({r₁, r₂, r₃} : Set (U ≃ₗ[ZMod p] U)) := by
    intro s hs hn hm
    apply hn
    have := (mem_closure_three_psi_iff f r₁ r₂ r₃ _ h₁ h₂ h₃ (f ⟨s, hs⟩).2).mp hm
    have e : ((glClosure en4Gens).subtype.comp f.symm.toMonoidHom)
        ⟨(f ⟨s, hs⟩ : U ≃ₗ[ZMod p] U), (f ⟨s, hs⟩).2⟩ = s := by simp
    rw [e] at this
    exact this
  refine ⟨f ⟨s₁, hs₁⟩, (f ⟨s₁, hs₁⟩).2, f ⟨s₂, hs₂⟩, (f ⟨s₂, hs₂⟩).2, ?_, (hf _).mp hr1, (hf _).mp hr2,
    hcomm s₁ hs₁ hc1, hcomm s₂ hs₂ hc2, hnot s₁ hs₁ hn1, hnot s₂ hs₂ hn2⟩
  intro e
  apply hne
  exact congrArg Subtype.val (f.injective (Subtype.ext e))

end CFSG.StandardType.ZS.B3MK

end
