module

public import CFSG.Quasithin.Background.RonanG51Basic
public import CFSG.Quasithin.H13.A6G5

public section

namespace CFSG.Quasithin.RonanG51

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6

private instance decMemG5G1 (σ : Equiv.Perm (Fin 6)) : Decidable (σ ∈ g5G1) :=
  (inferInstance : Decidable (Equiv.Perm.sign σ = 1 ∧
    ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4))))

private instance decMemCA6 (σ : Equiv.Perm (Fin 6)) : Decidable (σ ∈ cA6) :=
  (inferInstance : Decidable (σ * iota0 = iota0 * σ ∧ Equiv.Perm.sign σ = 1))

abbrev predLine4a (x : Fin 4 → ZMod 2) : Prop :=
  x = 0 ∨ x = ![1, 0, 0, 0] ∨ x = ![0, 0, 1, 0] ∨ x = ![1, 0, 1, 0]

abbrev predLine4b (x : Fin 4 → ZMod 2) : Prop :=
  x = 0 ∨ x = ![1, 0, 0, 0] ∨ x = ![0, 0, 1, 1] ∨ x = ![1, 0, 1, 1]

theorem predLine4a_add : ∀ a b : Fin 4 → ZMod 2,
    predLine4a a → predLine4a b → predLine4a (a + b) := by
  decide +kernel

theorem predLine4a_neg : ∀ a : Fin 4 → ZMod 2, predLine4a a → predLine4a (-a) := by
  decide +kernel

theorem predLine4b_add : ∀ a b : Fin 4 → ZMod 2,
    predLine4b a → predLine4b b → predLine4b (a + b) := by
  decide +kernel

theorem predLine4b_neg : ∀ a : Fin 4 → ZMod 2, predLine4b a → predLine4b (-a) := by
  decide +kernel

def line4a : AddSubgroup (Fin 4 → ZMod 2) where
  carrier := {x | predLine4a x}
  add_mem' := by
    intro a b ha hb
    exact predLine4a_add a b ha hb
  zero_mem' := by
    show predLine4a 0
    exact Or.inl rfl
  neg_mem' := by
    intro a ha
    exact predLine4a_neg a ha

def line4b : AddSubgroup (Fin 4 → ZMod 2) where
  carrier := {x | predLine4b x}
  add_mem' := by
    intro a b ha hb
    exact predLine4b_add a b ha hb
  zero_mem' := by
    show predLine4b 0
    exact Or.inl rfl
  neg_mem' := by
    intro a ha
    exact predLine4b_neg a ha

theorem mem_line4a (x : Fin 4 → ZMod 2) : x ∈ line4a ↔ predLine4a x := Iff.rfl

theorem mem_line4b (x : Fin 4 → ZMod 2) : x ∈ line4b ↔ predLine4b x := Iff.rfl

theorem card_line4a : Nat.card line4a = 4 := by
  show Nat.card {x : Fin 4 → ZMod 2 // predLine4a x} = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_line4b : Nat.card line4b = 4 := by
  show Nat.card {x : Fin 4 → ZMod 2 // predLine4b x} = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem fix4a_of_mem_g5G1 : ∀ σ : Equiv.Perm (Fin 6), σ ∈ g5G1 →
    Matrix.mulVec (heartHom σ) ![1, 0, 1, 0] = ![1, 0, 1, 0] := by
  decide +kernel

theorem stab4a_of_mem_cA6 : ∀ σ : Equiv.Perm (Fin 6), σ ∈ cA6 →
    ∀ x : Fin 4 → ZMod 2, predLine4a x → predLine4a (Matrix.mulVec (heartHom σ) x) := by
  decide +kernel

theorem fix4b_of_mem_cA6 : ∀ σ : Equiv.Perm (Fin 6), σ ∈ cA6 →
    Matrix.mulVec (heartHom (totalPermHom σ)) ![1, 0, 0, 0] = ![1, 0, 0, 0] := by
  decide +kernel

theorem stab4b_of_mem_g5G1 : ∀ σ : Equiv.Perm (Fin 6), σ ∈ g5G1 →
    ∀ x : Fin 4 → ZMod 2, predLine4b x →
      predLine4b (Matrix.mulVec (heartHom (totalPermHom σ)) x) := by
  decide +kernel

theorem a6BinaryRep_one_apply (g : ↥(alternatingGroup (Fin 6)))
    (x : D 1) : a6BinaryRep 1 g x = Matrix.mulVec (heartHom (g : Equiv.Perm (Fin 6))) x :=
  rfl

theorem a6BinaryRep_two_apply (g : ↥(alternatingGroup (Fin 6)))
    (x : D 2) :
    a6BinaryRep 2 g x = Matrix.mulVec (heartHom (totalPermHom (g : Equiv.Perm (Fin 6)))) x :=
  rfl

theorem ne_zero_1010 : (![1, 0, 1, 0] : Fin 4 → ZMod 2) ≠ 0 := by
  decide +kernel

theorem ne_zero_1000 : (![1, 0, 0, 0] : Fin 4 → ZMod 2) ≠ 0 := by
  decide +kernel

theorem a6_4a_fixesPoint :
    ∃ v : D 1, v ≠ 0 ∧ ∀ g : ↥(alternatingGroup (Fin 6)), (g : Equiv.Perm (Fin 6)) ∈ g5G1 →
      a6BinaryRep 1 g v = v := by
  refine ⟨![1, 0, 1, 0], ne_zero_1010, fun g hg => ?_⟩
  exact (a6BinaryRep_one_apply g _).trans (fix4a_of_mem_g5G1 _ hg)

theorem a6_4a_fixesLine :
    ∃ L : AddSubgroup (D 1), Nat.card L = 4 ∧
      ∀ g : ↥(alternatingGroup (Fin 6)), (g : Equiv.Perm (Fin 6)) ∈ cA6 →
        ∀ l ∈ L, a6BinaryRep 1 g l ∈ L := by
  refine ⟨line4a, card_line4a, fun g hg l hl => ?_⟩
  have h1 : Matrix.mulVec (heartHom (g : Equiv.Perm (Fin 6))) l ∈ line4a :=
    (mem_line4a _).mpr (stab4a_of_mem_cA6 _ hg _ ((mem_line4a _).mp hl))
  exact (congrArg (fun y => y ∈ line4a) (a6BinaryRep_one_apply g l)).mpr h1

theorem a6_4b_fixesPoint :
    ∃ v : D 2, v ≠ 0 ∧ ∀ g : ↥(alternatingGroup (Fin 6)), (g : Equiv.Perm (Fin 6)) ∈ cA6 →
      a6BinaryRep 2 g v = v := by
  refine ⟨![1, 0, 0, 0], ne_zero_1000, fun g hg => ?_⟩
  exact (a6BinaryRep_two_apply g _).trans (fix4b_of_mem_cA6 _ hg)

theorem a6_4b_fixesLine :
    ∃ L : AddSubgroup (D 2), Nat.card L = 4 ∧
      ∀ g : ↥(alternatingGroup (Fin 6)), (g : Equiv.Perm (Fin 6)) ∈ g5G1 →
        ∀ l ∈ L, a6BinaryRep 2 g l ∈ L := by
  refine ⟨line4b, card_line4b, fun g hg l hl => ?_⟩
  have h1 : Matrix.mulVec (heartHom (totalPermHom (g : Equiv.Perm (Fin 6)))) l ∈ line4b :=
    (mem_line4b _).mpr (stab4b_of_mem_g5G1 _ hg _ ((mem_line4b _).mp hl))
  exact (congrArg (fun y => y ∈ line4b) (a6BinaryRep_two_apply g l)).mpr h1

theorem fixesPoint_conj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (↥(alternatingGroup (Fin 6))) V)
    (c : ↥(alternatingGroup (Fin 6))) (H G : Set ↥(alternatingGroup (Fin 6)))
    (hH : ∀ g, g ∈ H ↔ c * g * c⁻¹ ∈ G) (v : V) (hv : v ≠ 0) (hfix : ∀ g ∈ G, ρ g v = v) :
    ∃ v' : V, v' ≠ 0 ∧ ∀ g ∈ H, ρ g v' = v' := by
  have key : ∀ (x y : ↥(alternatingGroup (Fin 6))) (z : V), ρ x (ρ y z) = ρ (x * y) z := by
    intro x y z
    rw [map_mul, Module.End.mul_apply]
  have hinv : ∀ z : V, ρ c (ρ c⁻¹ z) = z := by
    intro z
    rw [key, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ⟨ρ c⁻¹ v, ?_, ?_⟩
  · intro h
    apply hv
    rw [← hinv v, h, map_zero]
  · intro g hg
    have h1 : ρ (c * g * c⁻¹) v = v := hfix _ ((hH g).mp hg)
    calc ρ g (ρ c⁻¹ v) = ρ (g * c⁻¹) v := key g c⁻¹ v
      _ = ρ (c⁻¹ * (c * g * c⁻¹)) v := by
          rw [show g * c⁻¹ = c⁻¹ * (c * g * c⁻¹) by group]
      _ = ρ c⁻¹ (ρ (c * g * c⁻¹) v) := (key c⁻¹ _ v).symm
      _ = ρ c⁻¹ v := by rw [h1]

theorem fixesLine_conj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (↥(alternatingGroup (Fin 6))) V)
    (c : ↥(alternatingGroup (Fin 6))) (H G : Set ↥(alternatingGroup (Fin 6)))
    (hH : ∀ g, g ∈ H ↔ c * g * c⁻¹ ∈ G) (L : AddSubgroup V) (hL : Nat.card L = 4)
    (hst : ∀ g ∈ G, ∀ l ∈ L, ρ g l ∈ L) :
    ∃ L' : AddSubgroup V, Nat.card L' = 4 ∧ ∀ g ∈ H, ∀ l ∈ L', ρ g l ∈ L' := by
  have key : ∀ (x y : ↥(alternatingGroup (Fin 6))) (z : V), ρ x (ρ y z) = ρ (x * y) z := by
    intro x y z
    rw [map_mul, Module.End.mul_apply]
  have hinv : ∀ z : V, ρ c (ρ c⁻¹ z) = z := by
    intro z
    rw [key, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨f, hf⟩ : ∃ f : V →+ V, ∀ z, f z = ρ c⁻¹ z :=
    ⟨(ρ c⁻¹).toAddMonoidHom, fun z => rfl⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    rw [hf, hf] at hab
    have h1 := congrArg (ρ c) hab
    rwa [hinv, hinv] at h1
  refine ⟨L.map f, ?_, ?_⟩
  · rw [AddSubgroup.card_map_of_injective hfinj]
    exact hL
  · intro g hg l hl
    obtain ⟨l0, hl0, rfl⟩ := AddSubgroup.mem_map.mp hl
    refine AddSubgroup.mem_map.mpr ⟨ρ (c * g * c⁻¹) l0, hst _ ((hH g).mp hg) l0 hl0, ?_⟩
    simp only [hf]
    rw [key, key, show c⁻¹ * (c * g * c⁻¹) = g * c⁻¹ by group]

end CFSG.Quasithin.RonanG51
