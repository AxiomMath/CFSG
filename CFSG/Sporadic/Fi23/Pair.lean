module

public import CFSG.Sporadic.Fi23.Transposition
public import CFSG.Blueprint.FischerDefs

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem orderOf_d : orderOf d = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact d_sq) d_ne_one

theorem orderOf_of_isConj
    {x : J} (hx : IsConj d x) : orderOf x = 2 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  rw [orderOf_conj, orderOf_d]

theorem pair_J :
    CFSG.Blueprint.Fischer.Pair J {x : J | IsConj d x} :=
  ⟨inferInstance, ⟨d, rfl⟩, fun _ he => orderOf_of_isConj he,
    fun _ he _ hf => by
      rcases orderOf_mul_of_isConj he hf with h | h | h <;> simp [h],
    closure_conjugates⟩

theorem isConj_symm_iff {X Y : Type*} [Group X] [Group Y] (e : X ≃ Y)
    (he : ∀ a b, e (a * b) = e a * e b) (y : Y) (x : X) :
    IsConj (e.symm y) x ↔ IsConj y (e x) := by
  let f : X ≃* Y := { e with map_mul' := he }
  have hf : ∀ x, f x = e x := fun _ => rfl
  have hfs : ∀ y, f.symm y = e.symm y := fun _ => rfl
  rw [← hfs, ← hf, isConj_iff, isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨f c, by simp⟩
  · rintro ⟨c, hc⟩
    refine ⟨f.symm c, f.injective ?_⟩
    simp [hc]

theorem pair_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃ Y)
    (he : ∀ a b, e (a * b) = e a * e b) (y : Y)
    (h : CFSG.Blueprint.Fischer.Pair Y {z | IsConj y z}) :
    CFSG.Blueprint.Fischer.Pair X {x | IsConj (e.symm y) x} := by
  let f : X ≃* Y := { e with map_mul' := he }
  have hf : ∀ x, f x = e x := fun _ => rfl
  have hfs : ∀ y, f.symm y = e.symm y := fun _ => rfl
  have hc : ∀ x, IsConj (e.symm y) x ↔ IsConj y (f x) := fun x => by
    rw [hf]; exact isConj_symm_iff e he y x
  obtain ⟨hfin, -, h2, h3, h4⟩ := h
  refine ⟨Finite.of_equiv _ e.symm, ⟨_, rfl⟩, fun x hx => ?_, fun x hx z hz => ?_, ?_⟩
  · rw [← MulEquiv.orderOf_eq f]
    exact h2 _ ((hc x).1 hx)
  · rw [← MulEquiv.orderOf_eq f, map_mul]
    exact h3 _ ((hc x).1 hx) _ ((hc z).1 hz)
  · have e1 : {x | IsConj (e.symm y) x} = f.symm.toMonoidHom '' {z | IsConj y z} := by
      ext x
      simp only [Set.mem_image, MulEquiv.coe_toMonoidHom]
      constructor
      · intro hx
        exact ⟨f x, (hc x).1 hx, f.symm_apply_apply x⟩
      · rintro ⟨z, hz, rfl⟩
        exact (hc _).2 (by simpa using hz)
    rw [e1, ← MonoidHom.map_closure, h4]
    exact Subgroup.map_top_of_surjective _ f.symm.surjective

@[expose] noncomputable def dFi23 :
    Blueprint.NativeSporadic.Fi23 := fi23EquivJ.toEquiv.symm d

theorem pair_Fi23 :
    CFSG.Blueprint.Fischer.Pair Blueprint.NativeSporadic.Fi23 {x | IsConj dFi23 x} :=
  pair_of_equiv fi23EquivJ.toEquiv (map_mul fi23EquivJ) d pair_J

theorem card_class_dFi23 :
    Nat.card {x : Blueprint.NativeSporadic.Fi23 // IsConj dFi23 x} = 31671 := by
  rw [← card_class_d]
  exact Nat.card_congr (fi23EquivJ.toEquiv.subtypeEquiv fun x =>
    isConj_symm_iff fi23EquivJ.toEquiv (map_mul fi23EquivJ) d x)

theorem card_centralizer_dFi23 :
    Nat.card (Subgroup.centralizer ({dFi23} : Set Blueprint.NativeSporadic.Fi23)) =
      129123503308800 := by
  rw [← card_centralizer_d]
  refine Nat.card_congr (fi23EquivJ.toEquiv.subtypeEquiv fun x => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hd : fi23EquivJ.toEquiv dFi23 = d := fi23EquivJ.toEquiv.apply_symm_apply d
  have h1 : fi23EquivJ.toEquiv (x * dFi23) = fi23EquivJ.toEquiv x * d := by
    rw [← hd]; exact map_mul fi23EquivJ x dFi23
  have h2 : fi23EquivJ.toEquiv (dFi23 * x) = d * fi23EquivJ.toEquiv x := by
    rw [← hd]; exact map_mul fi23EquivJ dFi23 x
  rw [← h1, ← h2]
  exact fi23EquivJ.toEquiv.injective.eq_iff.symm

end CFSG.Sporadic.Fi23
