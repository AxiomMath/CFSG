module

public import CFSG.Timmesfeld.RankOne.Basic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.Timmesfeld

variable {X : Type*} [Group X]

namespace RankOne

@[ext] structure Point (A : Subgroup X) where
  val : Subgroup X
  exists_eq : ∃ g : X, val = A.map (MulAut.conj g).toMonoidHom

namespace Point

variable {A : Subgroup X}

instance : MulAction X (Point A) where
  smul g C := ⟨C.val.map (MulAut.conj g).toMonoidHom, by
    obtain ⟨g', hg'⟩ := C.exists_eq
    exact ⟨g * g', by rw [hg', map_conj_mul]⟩⟩
  one_smul C := Point.ext (map_conj_one _)
  mul_smul g g' C := Point.ext (map_conj_mul _ _ _)

@[simp] theorem val_smul (g : X) (C : Point A) :
    (g • C).val = C.val.map (MulAut.conj g).toMonoidHom := rfl

@[expose] def base (A : Subgroup X) : Point A := ⟨A, 1, (map_conj_one A).symm⟩

@[simp] theorem val_base : (base A).val = A := rfl

theorem val_smul_base (g : X) : (g • base A).val = A.map (MulAut.conj g).toMonoidHom := rfl

theorem exists_smul_base (C : Point A) : ∃ g : X, g • base A = C := by
  obtain ⟨g, hg⟩ := C.exists_eq
  exact ⟨g, Point.ext hg.symm⟩

instance : MulAction.IsPretransitive X (Point A) where
  exists_smul_eq C D := by
    obtain ⟨g, rfl⟩ := exists_smul_base C
    obtain ⟨g', rfl⟩ := exists_smul_base D
    exact ⟨g' * g⁻¹, by rw [smul_smul, inv_mul_cancel_right]⟩

instance [Finite X] : Finite (Point A) :=
  Finite.of_injective Point.val fun _ _ => Point.ext

theorem stabilizer_base :
    MulAction.stabilizer X (base A) = Subgroup.normalizer (A : Set X) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← map_conj_eq_self_iff]
  constructor
  · intro hg
    exact congrArg Point.val hg
  · intro hg
    exact Point.ext hg

end Point

end RankOne

open RankOne

namespace IsElemAbRankOne

variable {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

@[expose] def pt (a : X) : Point A :=
  ⟨B.map (MulAut.conj a).toMonoidHom, by
    obtain ⟨g, hg⟩ := h.exists_eq_map_conj
    exact ⟨a * g, by rw [hg, map_conj_mul]⟩⟩

@[simp] theorem val_pt (a : X) : (h.pt a).val = B.map (MulAut.conj a).toMonoidHom := rfl

theorem pt_ne_base {a : X} (ha : a ∈ A) : h.pt a ≠ Point.base A := by
  intro heq
  exact h.map_conj_ne ha (congrArg Point.val heq)

theorem pt_injOn {a a' : X} (ha : a ∈ A) (ha' : a' ∈ A) (heq : h.pt a = h.pt a') : a = a' :=
  h.map_conj_injOn ha ha' (congrArg Point.val heq)

theorem exists_pt {C : Point A} (hC : C ≠ Point.base A) : ∃ a ∈ A, C = h.pt a := by
  obtain ⟨g, rfl⟩ := Point.exists_smul_base C
  have hne : A.map (MulAut.conj g).toMonoidHom ≠ A := fun heq => hC (Point.ext heq)
  obtain ⟨a, ha, haeq⟩ := h.exists_eq_of_map_conj_ne hne
  exact ⟨a, ha, Point.ext haeq⟩

theorem smul_pt (x a : X) : x • h.pt a = h.pt (x * a) :=
  Point.ext (map_conj_mul B x a).symm

omit h in
theorem smul_base_of_mem {a : X} (ha : a ∈ A) : a • Point.base A = Point.base A :=
  Point.ext (map_conj_of_mem ha)

theorem stabilizer_pt_one : MulAction.stabilizer X (h.pt 1) =
    Subgroup.normalizer (B : Set X) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← map_conj_eq_self_iff]
  constructor
  · intro hg
    have := congrArg Point.val hg
    simp only [Point.val_smul, val_pt, map_conj_one] at this
    exact this
  · intro hg
    refine Point.ext ?_
    simp only [Point.val_smul, val_pt, map_conj_one]
    exact hg

theorem eq_base_of_smul_eq {a : X} (ha : a ∈ A) (ha1 : a ≠ 1) {C : Point A}
    (hC : a • C = C) : C = Point.base A := by
  obtain ⟨g, rfl⟩ := Point.exists_smul_base C
  exact Point.ext (h.eq_of_map_conj_eq ha ha1 (congrArg Point.val hC))

theorem isMultiplyPretransitive : MulAction.IsMultiplyPretransitive X (Point A) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  have key : ∀ C D : Point A, C ≠ Point.base A → D ≠ Point.base A →
      ∃ a ∈ A, a • C = D := by
    intro C D hC hD
    obtain ⟨c, hc, rfl⟩ := h.exists_pt hC
    obtain ⟨d, hd, rfl⟩ := h.exists_pt hD
    exact ⟨d * c⁻¹, A.mul_mem hd (A.inv_mem hc), by rw [smul_pt, inv_mul_cancel_right]⟩
  intro C₁ C₂ D₁ D₂ hC hD
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X C₁ (Point.base A)
  obtain ⟨g', hg'⟩ := MulAction.exists_smul_eq X D₁ (Point.base A)
  have hC' : g • C₂ ≠ Point.base A := by
    rw [← hg]
    exact fun heq => hC (smul_left_cancel g heq).symm
  have hD' : g' • D₂ ≠ Point.base A := by
    rw [← hg']
    exact fun heq => hD (smul_left_cancel g' heq).symm
  obtain ⟨a, ha, haeq⟩ := key _ _ hC' hD'
  refine ⟨g'⁻¹ * a * g, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hg, smul_base_of_mem ha, ← hg', inv_smul_smul]
  · rw [mul_smul, mul_smul, haeq, inv_smul_smul]

theorem card_point [Finite X] : Nat.card (Point A) = Nat.card A + 1 := by
  classical
  let f : Option A → Point A := fun o => o.elim (Point.base A) fun a => h.pt a
  have hf : Function.Bijective f := by
    constructor
    · rintro (_ | a) (_ | a') heq
      · rfl
      · exact absurd heq.symm (h.pt_ne_base a'.2)
      · exact absurd heq (h.pt_ne_base a.2)
      · exact congrArg some (Subtype.ext (h.pt_injOn a.2 a'.2 heq))
    · intro C
      by_cases hC : C = Point.base A
      · exact ⟨none, hC.symm⟩
      · obtain ⟨a, ha, rfl⟩ := h.exists_pt hC
        exact ⟨some ⟨a, ha⟩, rfl⟩
  have : Fintype A := Fintype.ofFinite A
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Fintype.card_option, Nat.card_eq_fintype_card]

theorem card_eq_card_point_mul [Finite X] :
    Nat.card X = (Nat.card A + 1) * Nat.card (Subgroup.normalizer (A : Set X)) := by
  rw [← h.card_point, ← MulAction.index_stabilizer_of_transitive X (Point.base A),
    Point.stabilizer_base, mul_comm, Subgroup.card_mul_index]

theorem card_normalizer [Finite X] :
    Nat.card (Subgroup.normalizer (A : Set X)) = Nat.card A *
      Nat.card (Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) :
        Subgroup X) := by
  classical
  set H : Subgroup X := Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X)
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (A : Set X) := fun a ha =>
    map_conj_eq_self_iff.1 (map_conj_of_mem ha)
  let f : A × H → Subgroup.normalizer (A : Set X) := fun p =>
    ⟨p.1 * p.2, Subgroup.mul_mem _ (hAN _ p.1.2) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, k⟩ ⟨a', k'⟩ heq
      have heq' : (a : X) * k = a' * k' := congrArg Subtype.val heq
      have hk : (a' : X)⁻¹ * a = k' * (k : X)⁻¹ :=
        calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * k) * (k : X)⁻¹ := by group
          _ = (a' : X)⁻¹ * (a' * k') * (k : X)⁻¹ := by rw [heq']
          _ = k' * (k : X)⁻¹ := by group
      have hmemA : (a' : X)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem a'.2) a.2
      have hmemB : (a' : X)⁻¹ * a ∈ Subgroup.normalizer (B : Set X) := by
        rw [hk]
        exact Subgroup.mul_mem _ (Subgroup.mem_inf.1 k'.2).2
          (Subgroup.inv_mem _ (Subgroup.mem_inf.1 k.2).2)
      have h1 : (a' : X)⁻¹ * a = 1 :=
        h.eq_one_of_map_conj_eq hmemA (map_conj_eq_self_iff.2 hmemB)
      have haa : (a : X) = a' := by
        rw [inv_mul_eq_one] at h1
        exact h1.symm
      have hkk : (k : X) = k' := by
        rw [haa] at heq'
        exact mul_left_cancel heq'
      exact Prod.ext (Subtype.ext haa) (Subtype.ext hkk)
    · rintro ⟨g, hg⟩
      obtain ⟨a, ha, k, hk, rfl⟩ := h.exists_mul_of_mem_normalizer hg
      exact ⟨(⟨a, ha⟩, ⟨k, hk⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem card_eq [Finite X] :
    Nat.card X = (Nat.card A + 1) * (Nat.card A *
      Nat.card (Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) :
        Subgroup X)) := by
  rw [h.card_eq_card_point_mul, h.card_normalizer]

end IsElemAbRankOne

end CFSG.Timmesfeld
