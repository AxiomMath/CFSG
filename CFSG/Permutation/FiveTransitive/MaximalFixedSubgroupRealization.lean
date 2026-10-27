module

public import CFSG.Permutation.FiveTransitive.LocalSylowFixedMaximal
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitDescent

public section

namespace CFSG

namespace FiveTransitive.MaximalFixedSubgroupRealization

open MulAction OyamaMinimalOrbitDescent

theorem exists_minimal_orbit
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    {p k : ℕ} [Fact p.Prime]
    (U : Subgroup G) (hU : IsPGroup p U)
    (hfixU : k + 1 ≤ Nat.card (fixedPoints U X))
    (hmax : ∀ T : Subgroup G, IsPGroup p T → k + 1 ≤ Nat.card (fixedPoints T X) →
      Nat.card T ≤ Nat.card U) :
    ∃ (a : Fin k ↪ X) (P : Sylow p (stabilizer G a)) (x : X),
      Set.range a ⊆ fixedPoints U X ∧ x ∈ fixedPoints U X ∧ x ∉ Set.range a ∧
      U ≤ ambientSylow a P ∧
      (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype = U ∧
      (∀ y : X, y ∉ Set.range a →
        Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) := by
  let v : Fin (k + 1) ↪ fixedPoints U X := (Fin.castLEEmb hfixU).trans
    (Finite.equivFin (fixedPoints U X)).symm.toEmbedding
  let e : Fin (k + 1) ↪ X := v.trans (Function.Embedding.subtype _)
  let a : Fin k ↪ X := Fin.Embedding.init e
  let x : X := e (Fin.last k)
  have ha : Set.range a ⊆ fixedPoints U X := by
    rintro _ ⟨i, rfl⟩
    exact (v i.castSucc).property
  have hxU : x ∈ fixedPoints U X := (v (Fin.last k)).property
  have hxa : x ∉ Set.range a := by
    rintro ⟨i, hi⟩
    exact Fin.castSucc_ne_last i (e.injective hi)
  have hUa : U ≤ stabilizer G a := by
    intro u hu
    apply Function.Embedding.ext
    intro i
    exact mem_fixedPoints.mp (ha ⟨i, rfl⟩) ⟨u, hu⟩
  obtain ⟨P, hUP⟩ := LocalSylowFixedMaximal.exists_sylow_containing (stabilizer G a) U hU hUa
  let A := ambientSylow a P
  have hA : IsPGroup p A := P.isPGroup'.map (stabilizer G a).subtype
  have hAa : A ≤ stabilizer G a := by
    rintro g ⟨u, _, rfl⟩
    exact u.property
  let T : X → Subgroup G := fun y => (stabilizer A y).map A.subtype
  have hT (y : X) : IsPGroup p (T y) := (hA.to_subgroup (stabilizer A y)).map A.subtype
  have hTy (y : X) (hy : y ∉ Set.range a) : k + 1 ≤ Nat.card (fixedPoints (T y) X) := by
    have hsub : insert y (Set.range a) ⊆ fixedPoints (T y) X := by
      intro z hz q
      obtain ⟨r, hr, he⟩ := q.property
      change q.val • z = z
      change r.val = q.val at he
      rw [← he]
      rcases hz with rfl | ⟨i, rfl⟩
      · exact hr
      · exact DFunLike.congr_fun (hAa r.property) i
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hy, Set.ncard_range_of_injective a.injective,
      Nat.card_fin, ← Nat.card_coe_set_eq] at hle
    exact hle
  have hUT : U ≤ T x := by
    intro u hu
    exact ⟨⟨u, hUP hu⟩, mem_fixedPoints.mp hxU ⟨u, hu⟩, rfl⟩
  have hTx : T x = U := (Subgroup.eq_of_le_of_card_ge hUT (hmax (T x) (hT x) (hTy x hxa))).symm
  refine ⟨a, P, x, ha, hxU, hxa, hUP, hTx, ?_⟩
  intro y hy
  have hle := hmax (T y) (hT y) (hTy y hy)
  rw [← hTx, Subgroup.card_map_of_injective A.subtype_injective,
    Subgroup.card_map_of_injective A.subtype_injective] at hle
  have hxcard := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer A X x
  have hycard := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer A X y
  have hm := Nat.mul_le_mul_left (Nat.card (orbit A y)) hle
  rw [hycard, ← hxcard] at hm
  exact Nat.le_of_mul_le_mul_right hm Nat.card_pos

end FiveTransitive.MaximalFixedSubgroupRealization

end CFSG
