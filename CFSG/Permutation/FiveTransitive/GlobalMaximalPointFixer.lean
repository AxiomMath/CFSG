module

public import CFSG.Permutation.FiveTransitive.LocalSylowFixedMaximal
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitDescent

public section

namespace CFSG

namespace FiveTransitive.GlobalMaximalPointFixer

open MulAction OyamaMinimalOrbitDescent

private theorem exists_conjugate_placement
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    {p k : ℕ} [Fact p.Prime] (hk : IsMultiplyPretransitive G X k)
    (a : Fin k ↪ X) (P : Sylow p (stabilizer G a))
    (T : Subgroup G) (hT : IsPGroup p T)
    (hfixT : k + 1 ≤ Nat.card (fixedPoints T X)) :
    ∃ (g : G) (y : X), y ∉ Set.range a ∧
      T.map (MulAut.conj g).toMonoidHom ≤
        (stabilizer (ambientSylow a P) y).map (ambientSylow a P).subtype := by
  let v : Fin (k + 1) ↪ fixedPoints T X := (Fin.castLEEmb hfixT).trans
    (Finite.equivFin (fixedPoints T X)).symm.toEmbedding
  let e : Fin (k + 1) ↪ X := v.trans (Function.Embedding.subtype _)
  let b : Fin k ↪ X := Fin.Embedding.init e
  have hTb : T ≤ stabilizer G b := by
    intro t ht
    apply Function.Embedding.ext
    intro i
    exact mem_fixedPoints.mp (v i.castSucc).property ⟨t, ht⟩
  obtain ⟨R, hTR⟩ := LocalSylowFixedMaximal.exists_sylow_containing (stabilizer G b) T hT hTb
  obtain ⟨g, hga, hgR⟩ := StabilizerSylowConjugacy.exists_conjugating_transporter
    b a (hk.exists_smul_eq b a) R P
  let y : X := g • e (Fin.last k)
  have hy : y ∉ Set.range a := by
    rintro ⟨i, hi⟩
    have hgi : g • e i.castSucc = a i := DFunLike.congr_fun hga i
    have he : e i.castSucc = e (Fin.last k) := (MulAction.injective g) (hgi.trans hi)
    exact Fin.castSucc_ne_last i (e.injective he)
  change _ = ambientSylow a P at hgR
  have hTA : T.map (MulAut.conj g).toMonoidHom ≤ ambientSylow a P := by
    rw [← hgR]
    exact Subgroup.map_mono hTR
  refine ⟨g, y, hy, ?_⟩
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
  have huA : (MulAut.conj g) u ∈ ambientSylow a P :=
    hTA (Subgroup.mem_map_of_mem _ hu)
  refine ⟨⟨(MulAut.conj g) u, huA⟩, ?_, rfl⟩
  change (g * u * g⁻¹) • (g • e (Fin.last k)) = g • e (Fin.last k)
  rw [mul_smul, mul_smul, inv_smul_smul]
  exact congrArg (fun z : X => g • z) (mem_fixedPoints.mp (v (Fin.last k)).property ⟨u, hu⟩)

theorem order_bound
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    {p k : ℕ} [Fact p.Prime] (hk : IsMultiplyPretransitive G X k)
    (a : Fin k ↪ X) (P : Sylow p (stabilizer G a))
    (hfixed : fixedPoints (ambientSylow a P) X = Set.range a)
    (x : X) (_hx : x ∉ Set.range a)
    (hmin : ∀ y : X, y ∉ Set.range a →
      Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y))
    (T : Subgroup G) (hT : IsPGroup p T)
    (hfixT : k + 1 ≤ Nat.card (fixedPoints T X)) :
    Nat.card T ≤ Nat.card ((stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype) := by
  obtain ⟨g, y, hy, hplace⟩ := exists_conjugate_placement hk a P T hT hfixT
  let A := ambientSylow a P
  have hle : Nat.card T ≤ Nat.card (stabilizer A y) := by
    have hi := Nat.card_le_card_of_injective (Subgroup.inclusion hplace)
      (Subgroup.inclusion_injective hplace)
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective A.subtype_injective] at hi
  have hminFix : ∀ z : X, z ∉ fixedPoints A X →
      Nat.card (orbit A x) ≤ Nat.card (orbit A z) := by
    simpa only [A, hfixed] using hmin
  have hyFix : y ∉ fixedPoints A X := by rwa [hfixed]
  have hxcard := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer A X x
  have hycard := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer A X y
  have hm := Nat.mul_le_mul_right (Nat.card (stabilizer A y)) (hminFix y hyFix)
  rw [hycard, ← hxcard] at hm
  have : Nonempty (orbit A x) := ⟨⟨x, mem_orbit_self x⟩⟩
  have hsy : Nat.card (stabilizer A y) ≤ Nat.card (stabilizer A x) :=
    Nat.le_of_mul_le_mul_left hm Nat.card_pos
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact hle.trans hsy

end FiveTransitive.GlobalMaximalPointFixer

end CFSG
