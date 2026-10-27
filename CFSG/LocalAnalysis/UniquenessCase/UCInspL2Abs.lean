module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open CFSG.Open Subgroup
open scoped commutatorElement

section Klein

variable {H : Type*} [Group H]

@[expose] def kleinSub (x y : H) (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    Subgroup H where
  carrier := {1, x, y, x * y}
  mul_mem' := by
    have h1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
    have h2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
    have h3 : (x * y) * x = y := by rw [mul_assoc, ← hxy, ← mul_assoc, hx, one_mul]
    have h4 : (x * y) * y = x := by rw [mul_assoc, hy, mul_one]
    have h5 : (x * y) * (x * y) = 1 := by rw [mul_assoc, h2, hx]
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [hx, hy, hxy.symm, h1, h2, h3, h4, h5]
  one_mem' := Or.inl rfl
  inv_mem' := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · simp [hxi]
    · simp [hyi]
    · simp [mul_inv_rev, hxi, hyi, hxy]

theorem mem_kleinSub {x y : H} {hx : x * x = 1} {hy : y * y = 1} {hxy : x * y = y * x} {a : H} :
    a ∈ kleinSub x y hx hy hxy ↔ a = 1 ∨ a = x ∨ a = y ∨ a = x * y := Iff.rfl

theorem card_kleinSub {x y : H} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) : Nat.card (kleinSub x y hx hy hxy) = 4 := by
  classical
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hxy1 : x * y ≠ 1 := fun h => hne (by
    have : y = x⁻¹ := (eq_inv_of_mul_eq_one_right h)
    rw [this, hxi])
  have hxxy : x ≠ x * y := fun h => hy1 (by
    have := congrArg (fun z => x⁻¹ * z) h
    simpa using this.symm)
  have hyxy : y ≠ x * y := fun h => hx1 (by
    have := congrArg (fun z => z * y⁻¹) h
    simpa using this.symm)
  have hcoe : ((kleinSub x y hx hy hxy : Subgroup H) : Set H) =
      ↑({1, x, y, x * y} : Finset H) := by
    ext a
    simp [mem_kleinSub]
  rw [show Nat.card (kleinSub x y hx hy hxy) =
      Nat.card ((kleinSub x y hx hy hxy : Subgroup H) : Set H) from rfl, hcoe,
    Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simpa using hyxy
  · simp [hne, hxxy]
  · simp [hx1.symm, hy1.symm, hxy1.symm]

theorem isElemAbelian_kleinSub {x y : H} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : IsElemAbelian 2 (kleinSub x y hx hy hxy) := by
  have h1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have h2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
  have h3 : (x * y) * x = y := by rw [mul_assoc, ← hxy, ← mul_assoc, hx, one_mul]
  have h4 : (x * y) * y = x := by rw [mul_assoc, hy, mul_one]
  have h5 : (x * y) * (x * y) = 1 := by rw [mul_assoc, h2, hx]
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    rw [mem_kleinSub] at ha hb
    show a * b = b * a
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [hx, hy, hxy.symm, h1, h2, h3, h4, h5]
  · rw [mem_kleinSub] at ha
    rw [pow_two]
    rcases ha with rfl | rfl | rfl | rfl <;> simp [hx, hy, h5]

theorem exists_klein_of_triple {d x y : H} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) (hdx : d * x * d⁻¹ = x * y)
    (hdy : d * y * d⁻¹ = x) :
    ∃ S : Subgroup H, IsElemAbelian 2 S ∧ Nat.card S = 4 ∧ zpowers d ≤ normalizer (S : Set H) ∧
      ⁅zpowers d, S⁆ = S := by
  set S := kleinSub x y hx hy hxy with hS
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
  have h3 : (x * y) * x = y := by rw [mul_assoc, ← hxy, ← mul_assoc, hx, one_mul]
  have hxS : x ∈ S := mem_kleinSub.2 (Or.inr (Or.inl rfl))
  have hyS : y ∈ S := mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl)))
  have hxyS : x * y ∈ S := mem_kleinSub.2 (Or.inr (Or.inr (Or.inr rfl)))
  have hdxy : d * (x * y) * d⁻¹ = y := by
    have : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
    rw [this, hdx, hdy, h3]
  have hconj1 : d⁻¹ * x * d = y := by rw [← hdy]; group
  have hconj12 : d⁻¹ * (x * y) * d = x := by rw [← hdx]; group
  have hsplit : d⁻¹ * (x * y) * d = (d⁻¹ * x * d) * (d⁻¹ * y * d) := by group
  have hconj2 : d⁻¹ * y * d = x * y := by
    have h : (d⁻¹ * x * d) * (d⁻¹ * y * d) = x := by rw [← hsplit, hconj12]
    rw [hconj1] at h
    calc d⁻¹ * y * d = y * (y * (d⁻¹ * y * d)) := by rw [← mul_assoc, hy, one_mul]
      _ = y * x := by rw [h]
      _ = x * y := hxy.symm
  have hconj : ∀ s ∈ S, d * s * d⁻¹ ∈ S := by
    intro s hs
    rw [mem_kleinSub] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · simpa using S.one_mem
    · rw [hdx]; exact hxyS
    · rw [hdy]; exact hxS
    · rw [hdxy]; exact hyS
  have hconj' : ∀ s ∈ S, d⁻¹ * s * d ∈ S := by
    intro s hs
    rw [mem_kleinSub] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · simpa using S.one_mem
    · rw [hconj1]; exact hyS
    · rw [hconj2]; exact hxyS
    · rw [hconj12]; exact hxS
  have hd : d ∈ normalizer (S : Set H) := by
    refine mem_normalizer_iff.2 fun h => ⟨fun hh => hconj h hh, fun hh => ?_⟩
    have := hconj' _ hh
    have e : d⁻¹ * (d * h * d⁻¹) * d = h := by group
    rwa [e] at this
  have hzp : zpowers d ≤ normalizer (S : Set H) := (Subgroup.zpowers_le).2 hd
  refine ⟨S, isElemAbelian_kleinSub hx hy hxy, card_kleinSub hx hy hxy hx1 hy1 hne, hzp,
    le_antisymm ?_ ?_⟩
  · rw [Subgroup.commutator_le]
    intro g hg s hs
    rw [commutatorElement_def]
    exact S.mul_mem ((mem_normalizer_iff.1 (hzp hg) s).1 hs) (S.inv_mem hs)
  · have hd_mem : d ∈ zpowers d := mem_zpowers d
    have e1 : ⁅d, x⁆ = y := by rw [commutatorElement_def, hdx, hxi, h3]
    have e2 : ⁅d, y⁆ = x * y := by rw [commutatorElement_def, hdy, hyi]
    have hcx : y ∈ ⁅zpowers d, S⁆ := e1 ▸ Subgroup.commutator_mem_commutator hd_mem hxS
    have hcy : x * y ∈ ⁅zpowers d, S⁆ := e2 ▸ Subgroup.commutator_mem_commutator hd_mem hyS
    intro a ha
    rw [mem_kleinSub] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact one_mem _
    · have := mul_mem hcy (inv_mem hcx)
      rwa [hyi, mul_assoc, hy, mul_one] at this
    · exact hcx
    · exact hcy

end Klein

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem inspL2Core_of_mulEquiv (e : G ≃* H)
    (hH : ∀ D : Subgroup H, Nat.card D = 3 → ∃ S : Subgroup H, IsElemAbelian 2 S ∧
      Nat.card S = 4 ∧ D ≤ normalizer (S : Set H) ∧ ⁅D, S⁆ = S) :
    ∀ D : Subgroup G, Nat.card D = 3 → ∃ S : Subgroup G, IsElemAbelian 2 S ∧
      Nat.card S = 4 ∧ D ≤ normalizer (S : Set G) ∧ ⁅D, S⁆ = S := by
  intro D hD
  obtain ⟨S', hS'a, hS'c, hS'n, hS'c'⟩ := hH (D.map e.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective e.injective, hD])
  refine ⟨S'.map e.symm.toMonoidHom, isElemAbelian_map e.symm.toMonoidHom hS'a, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hS'c]
  · intro x hx
    rw [mem_normalizer_iff]
    intro h
    have hx' : e x ∈ normalizer (S' : Set H) := hS'n ⟨x, hx, rfl⟩
    have key := mem_normalizer_iff.1 hx' (e h)
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨y, hy, hyh⟩
      refine ⟨e (x * h * x⁻¹), ?_, by simp⟩
      rw [map_mul, map_mul, map_inv]
      have : e h ∈ S' := by
        have h1 : y = e h := by rw [← hyh]; simp
        rwa [← h1]
      exact (key.1 this)
    · rintro ⟨y, hy, hyh⟩
      refine ⟨e h, ?_, by simp⟩
      have h1 : y = e (x * h * x⁻¹) := by rw [← hyh]; simp
      rw [h1, map_mul, map_mul, map_inv] at hy
      exact key.2 hy
  · have hDe : (D.map e.toMonoidHom).map e.symm.toMonoidHom = D := by
      rw [Subgroup.map_map]
      have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
        ext x; simp
      rw [this, Subgroup.map_id]
    calc ⁅D, S'.map e.symm.toMonoidHom⁆
        = ⁅(D.map e.toMonoidHom).map e.symm.toMonoidHom, S'.map e.symm.toMonoidHom⁆ := by
          rw [hDe]
      _ = (⁅D.map e.toMonoidHom, S'⁆).map e.symm.toMonoidHom :=
          (Subgroup.map_commutator _ _ _).symm
      _ = S'.map e.symm.toMonoidHom := by rw [hS'c']

end Transport

theorem exists_gen_of_card_three {G : Type*} [Group G] (D : Subgroup G) (hD : Nat.card D = 3) :
    ∃ d : G, D = Subgroup.zpowers d ∧ d ^ 3 = 1 ∧ d ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic D := isCyclic_of_prime_card hD
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
  refine ⟨(g : G), ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact g.2
  · have h := pow_card_eq_one' (G := D) (x := g)
    rw [hD] at h
    simpa using congrArg Subtype.val h
  · intro h1
    have hg1 : g = 1 := Subtype.ext h1
    haveI : Subsingleton D := ⟨fun a b => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
      rw [← hi, ← hj, hg1]
      simp⟩
    have := Nat.card_of_subsingleton (1 : D)
    omega

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
