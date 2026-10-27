module

public import CFSG.Permutation.FiveTransitive.ChosenMinimalOrbitInduced
public import CFSG.Permutation.FiveTransitive.ActionImageStabilizerSylow

public section

namespace CFSG

namespace FiveTransitive.ChosenTupleMinimalOrbitInduced

open MulAction FixedNormalizerAction FixedNormalizerImage OyamaMinimalOrbitDescent

theorem local_geometry
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    {p : ℕ} [Fact p.Prime] (k : ℕ)
    (hk : IsMultiplyPretransitive G X k) (a : Fin k ↪ X)
    (P : Sylow p (stabilizer G a)) (x : X)
    (hx : x ∉ fixedPoints (ambientSylow a P) X)
    (hmin : ∀ y : X, y ∉ fixedPoints (ambientSylow a P) X →
      Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) :
    let Q := (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype
    Q < ambientSylow a P ∧ fixedPoints (ambientSylow a P) X ⊂ fixedPoints Q X ∧
    ∀ (b : Fin k ↪ Fixed (X := X) Q)
      (S : Sylow p (stabilizer (Image (X := X) Q) b)),
    let T := (S : Subgroup (stabilizer (Image (X := X) Q) b)).map
      (stabilizer (Image (X := X) Q) b).subtype
    T ≠ ⊥ ∧ Nat.card (fixedPoints T (Fixed (X := X) Q)) =
      Nat.card (fixedPoints (ambientSylow a P) X) ∧
      ∀ t : Image (X := X) Q, t ∈ T → t ≠ 1 →
        ∀ z : Fixed (X := X) Q, z ∉ fixedPoints T (Fixed (X := X) Q) → t • z ≠ z := by
  let Q := (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype
  obtain ⟨hQA, hstrict, hcard⟩ := ChosenMinimalOrbitInduced.point_fixer_data (ambientSylow a P) x hx
  refine ⟨hQA, hstrict, ?_⟩
  intro b S
  obtain ⟨R, hR⟩ := ActionImageStabilizerSylow.preimage_sylow_tuple_stabilizer
    (Normalizer Q) (Fixed (X := X) Q) k b S
  obtain ⟨U, hU⟩ := sylow_localFixer_image Q b R
  have hQb : Q ≤ stabilizer G (ambientEmbedding b) := by
    intro q hq
    apply Function.Embedding.ext
    intro i
    have hi : (b i).val ∈ fixedPoints Q X := by
      simpa only [fixed_eq] using (b i).property
    exact mem_fixedPoints.mp hi ⟨q, hq⟩
  obtain ⟨hQU, hfixed, hmove, _, hsemi⟩ := local_sylow_descent a (ambientEmbedding b)
    (hk.exists_smul_eq a (ambientEmbedding b)) P x Q hmin hQA hcard hstrict hQb U
  let B := (R : Subgroup (stabilizer (Normalizer Q) b)).map
    (stabilizer (Normalizer Q) b).subtype
  change (U : Subgroup ↥(Normalizer Q ⊓ stabilizer G (ambientEmbedding b))).map
    (Normalizer Q ⊓ stabilizer G (ambientEmbedding b)).subtype = Ambient B at hU
  have hQB : Q ≤ Ambient B := by rw [← hU]; exact hQU.le
  have hfixedB : Nat.card (fixedPoints (Ambient B) X) =
      Nat.card (fixedPoints (ambientSylow a P) X) := by rwa [← hU]
  have hmoveB : ∃ r : G, r ∈ Ambient B ∧ ∃ z ∈ fixedPoints Q X, r • z ≠ z := by
    rwa [← hU]
  have hsemiB : ∀ r : G, r ∈ Ambient B → r ∉ Q → ∀ z ∈ fixedPoints Q X,
      z ∉ fixedPoints (Ambient B) X → r • z ≠ z := by rwa [← hU]
  dsimp only
  rw [hR]
  exact ⟨nontrivial_of_moves B hmoveB,
    (Nat.card_congr (fixedEquiv B hQB)).trans hfixedB, semiregular B hsemiB⟩

theorem exists_local_geometry
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    {p : ℕ} [Fact p.Prime] (k : ℕ)
    (hk : IsMultiplyPretransitive G X k) (a : Fin k ↪ X)
    (P : Sylow p (stabilizer G a)) (hP : (P : Subgroup (stabilizer G a)) ≠ ⊥) :
    ∃ x : X, x ∉ fixedPoints (ambientSylow a P) X ∧
      (∀ y : X, y ∉ fixedPoints (ambientSylow a P) X →
        Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) ∧
      let Q := (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype
      Q < ambientSylow a P ∧ fixedPoints (ambientSylow a P) X ⊂ fixedPoints Q X ∧
      ∀ (b : Fin k ↪ Fixed (X := X) Q)
        (S : Sylow p (stabilizer (Image (X := X) Q) b)),
      let T := (S : Subgroup (stabilizer (Image (X := X) Q) b)).map
        (stabilizer (Image (X := X) Q) b).subtype
      T ≠ ⊥ ∧ Nat.card (fixedPoints T (Fixed (X := X) Q)) =
        Nat.card (fixedPoints (ambientSylow a P) X) ∧
        ∀ t : Image (X := X) Q, t ∈ T → t ≠ 1 →
          ∀ z : Fixed (X := X) Q, z ∉ fixedPoints T (Fixed (X := X) Q) → t • z ≠ z := by
  have : Nontrivial P := (P : Subgroup (stabilizer G a)).nontrivial_iff_ne_bot.mpr hP
  obtain ⟨u, hu⟩ := exists_ne (1 : P)
  have huG : u.val.val ≠ 1 := by
    intro he
    exact hu (Subtype.ext (Subtype.ext he))
  have hex : ∃ x : X, u.val.val • x ≠ x := by
    by_contra! h
    apply huG
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    simpa only [one_smul] using h x
  obtain ⟨x, hx⟩ := hex
  let uA : ambientSylow a P := ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩
  obtain ⟨t, ht, hmin, _, _⟩ := MinimalOrbitStabilizer.exists_minimal_orbit_stabilizer
    (ambientSylow a P) X ⟨uA, x, hx⟩
  exact ⟨t, ht, hmin, local_geometry k hk a P t ht hmin⟩

end FiveTransitive.ChosenTupleMinimalOrbitInduced

end CFSG
