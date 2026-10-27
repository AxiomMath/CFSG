module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character

namespace CFSG
end CFSG
open CFSG

/-!
# The class-sum-character formula (Gorenstein 4.2.12)

For a conjugacy class `C` of a finite group `G` the number of pairs
`(x, y) ∈ C × C` with `x·y = g` equals
`|C|² · |G|⁻¹ · Σ_{χ ∈ Irr G} (χ(t)²/χ(1))·χ(g)` (for `t ∈ C`); the paper
(Bender--Glauberman, Lemma 2.2) uses the single-class form for an involution
`t` (where `χ(t)` is real, so no conjugation appears) and the two-class form
for the classes `t_i^H × t_j^H` of a subgroup.  This is Gorenstein,
*Finite Groups*, Theorem 4.2.12, extracted for the `lemma_2_2` proof.

The group-algebra machinery (`classSumComplex`, the class-sum scalar, the
trace extraction) is re-derived locally since `Theory.Character.Divisibility`
keeps its own copies private.
-/

namespace CFSG.Theory.Character

open _root_.Representation
open Theory.Representation

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

variable {G V : Type*} [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-! ## Local class-sum machinery (mirrors the private pieces of `Divisibility.lean`) -/

private noncomputable def classSet (c : ConjClasses G) : Finset G :=
  letI : DecidableEq (ConjClasses G) := Classical.decEq (ConjClasses G)
  Finset.univ.filter fun g : G => ConjClasses.mk g = c

private lemma mem_classSet_iff {c : ConjClasses G} {g : G} :
    g ∈ classSet (G := G) c ↔ ConjClasses.mk g = c := by
  classical
  simp [classSet]

private noncomputable def classSumComplex (c : ConjClasses G) : MonoidAlgebra ℂ G :=
  ∑ g ∈ classSet (G := G) c, MonoidAlgebra.single g (1 : ℂ)

private lemma classSumComplex_coeff [DecidableEq (ConjClasses G)] (c : ConjClasses G) (x : G) :
    (classSumComplex (G := G) c).coeff x =
      if ConjClasses.mk x = c then 1 else 0 := by
  rw [classSumComplex]
  simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]
  rw [Finset.sum_apply']
  by_cases hx : ConjClasses.mk x = c
  · rw [if_pos hx]
    have hxmem : x ∈ classSet (G := G) c := (mem_classSet_iff (G := G)).2 hx
    rw [Finset.sum_eq_single x]
    · simp
    · intro y hy hyx
      simp [hyx]
    · intro hxnot
      exact False.elim (hxnot hxmem)
  · rw [if_neg hx]
    refine Finset.sum_eq_zero ?_
    intro y hy
    have hyx : y ≠ x := by
      intro hyx
      apply hx
      simpa [hyx] using (mem_classSet_iff (G := G)).1 hy
    simp [hyx]

private lemma classSumComplex_comm (c : ConjClasses G) (a : MonoidAlgebra ℂ G) :
    a * classSumComplex (G := G) c =
      classSumComplex (G := G) c * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      have hconj :
          ConjClasses.mk (g⁻¹ * x) = ConjClasses.mk (x * g⁻¹) := by
        rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
        exact ⟨g, by group⟩
      simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
        classSumComplex_coeff]
      rw [hconj, mul_comm]

private noncomputable def centralElementIntertwiner
    (ρ : Representation ℂ G V) (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    Representation.IntertwiningMap ρ ρ where
  toLinearMap := ρ.asAlgebraHom z
  isIntertwining' g := by
    rw [← Representation.asAlgebraHom_single_one (ρ := ρ) g]
    change ρ.asAlgebraHom z * ρ.asAlgebraHom
        (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ G) =
      ρ.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ G) *
        ρ.asAlgebraHom z
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.asAlgebraHom (hz (MonoidAlgebra.single g (1 : ℂ))).symm

private lemma centralElementIntertwiner_eq_scalar
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (z : MonoidAlgebra ℂ G) (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    ∃ a : ℂ, ρ.asAlgebraHom z = a • (1 : Module.End ℂ V) := by
  classical
  have hfin :
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 :=
    (irreducible_iff_end_dimension_one (ρ := ρ)).1 inferInstance
  have : Nontrivial V := irreducible_nontrivial (ρ := ρ)
  have hone_ne_zero : (1 : Representation.IntertwiningMap ρ ρ) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvzero : v = 0 := by
      simpa using congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
    exact hv hvzero
  obtain ⟨a, ha⟩ :
      ∃ a : ℂ, a • (1 : Representation.IntertwiningMap ρ ρ) =
        centralElementIntertwiner (ρ := ρ) z hz :=
    (finrank_eq_one_iff_of_nonzero'
      (K := ℂ) (V := Representation.IntertwiningMap ρ ρ)
      (1 : Representation.IntertwiningMap ρ ρ) hone_ne_zero).mp hfin
      (centralElementIntertwiner (ρ := ρ) z hz)
  refine ⟨a, ?_⟩
  ext v
  simpa [centralElementIntertwiner] using
    (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) ha).symm

omit [FiniteDimensional ℂ V] in
private lemma classSumComplex_trace
    (ρ : Representation ℂ G V) (c : ConjClasses G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSumComplex (G := G) c)) =
      ∑ g ∈ classSet (G := G) c, ρ.character g := by
  classical
  simp [classSumComplex, Representation.character, map_sum]

private lemma classSet_card_eq_carrier_card (c : ConjClasses G) :
    (classSet (G := G) c).card = Nat.card c.carrier := by
  classical
  have hcard :
      (classSet (G := G) c).card =
        Fintype.card {g : G // g ∈ classSet (G := G) c} := by
    rw [Fintype.card_coe]
  rw [hcard, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun g : G =>
    by
      rw [mem_classSet_iff]
      exact (ConjClasses.mem_carrier_iff_mk_eq (a := g) (b := c)).symm))

omit [FiniteDimensional ℂ V] in
private lemma classSumComplex_trace_eq_card_mul
    (ρ : Representation ℂ G V) {c : ConjClasses G} {x : G}
    (hx : ConjClasses.mk x = c) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSumComplex (G := G) c)) =
      (Nat.card c.carrier : ℂ) * ρ.character x := by
  classical
  rw [classSumComplex_trace]
  have hconst :
      ∀ g ∈ classSet (G := G) c, ρ.character g = ρ.character x := by
    intro g hg
    have hmk : ConjClasses.mk g = ConjClasses.mk x := by
      rw [(mem_classSet_iff (G := G)).1 hg, hx]
    rw [ConjClasses.mk_eq_mk_iff_isConj] at hmk
    rcases isConj_iff.mp hmk with ⟨y, rfl⟩
    simp
  calc
    ∑ g ∈ classSet (G := G) c, ρ.character g
        = ∑ g ∈ classSet (G := G) c, ρ.character x := by
            refine Finset.sum_congr rfl ?_
            intro g hg
            exact hconst g hg
    _ = (Nat.card c.carrier : ℂ) * ρ.character x := by
            rw [Finset.sum_const, classSet_card_eq_carrier_card]
            simp [nsmul_eq_mul]

private lemma classSum_scalar_mul_finrank
    (ρ : Representation ℂ G V) (c : ConjClasses G) {x : G}
    (hx : ConjClasses.mk x = c) {a : ℂ}
    (ha : ρ.asAlgebraHom (classSumComplex (G := G) c) = a • (1 : Module.End ℂ V)) :
    a * (Module.finrank ℂ V : ℂ) =
      (Nat.card c.carrier : ℂ) * ρ.character x := by
  classical
  have htrace₁ :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSumComplex (G := G) c)) =
        (Nat.card c.carrier : ℂ) * ρ.character x :=
    classSumComplex_trace_eq_card_mul (ρ := ρ) hx
  have htrace₂ :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSumComplex (G := G) c)) =
        a * (Module.finrank ℂ V : ℂ) := by
    rw [ha, map_smul]
    simp
  exact htrace₂.symm.trans htrace₁

private noncomputable def classSumScalarLocal
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) : ℂ :=
  Classical.choose (centralElementIntertwiner_eq_scalar (ρ := ρ)
    (classSumComplex (G := G) c) (classSumComplex_comm (G := G) c))

private lemma classSumScalarLocal_spec
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    ρ.asAlgebraHom (classSumComplex (G := G) c) =
      classSumScalarLocal (ρ := ρ) c • (1 : Module.End ℂ V) :=
  Classical.choose_spec (centralElementIntertwiner_eq_scalar (ρ := ρ)
    (classSumComplex (G := G) c) (classSumComplex_comm (G := G) c))

private lemma classSumScalarLocal_eq_card_mul_character_div
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) {x : G} (hx : x ∈ c.carrier) :
    classSumScalarLocal (ρ := ρ) c =
      (Nat.card c.carrier : ℂ) * ρ.character x / ρ.character 1 := by
  classical
  have : Nontrivial V := irreducible_nontrivial (ρ := ρ)
  have hdim_pos : 0 < Module.finrank ℂ V :=
    (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
  have hdim_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdim_pos
  have hxmk : ConjClasses.mk x = c := (ConjClasses.mem_carrier_iff_mk_eq).1 hx
  have hscalar :
      classSumScalarLocal (ρ := ρ) c * (Module.finrank ℂ V : ℂ) =
        (Nat.card c.carrier : ℂ) * ρ.character x :=
    classSum_scalar_mul_finrank (ρ := ρ) c hxmk
      (classSumScalarLocal_spec (ρ := ρ) c)
  have hdegree : ρ.character 1 = (Module.finrank ℂ V : ℂ) := by
    simp [Representation.character]
  rw [hdegree]
  field_simp [hdim_ne]
  simpa [mul_comm] using hscalar

/-! ## The class-sum-character formula (Gorenstein 4.2.12) -/

/-- The number of pairs `(x, y)` with `x ∈ ci.carrier`, `y ∈ cj.carrier` and `x·y = g`. -/
public noncomputable def classSumPairCountMul (ci cj : ConjClasses G) (g : G) : ℕ :=
  Nat.card {p : ci.carrier × cj.carrier // p.1.1 * p.2.1 = g}

/-- The number of pairs `(x, y)` with `x, y ∈ c.carrier` and `x·y = g`. -/
public noncomputable def classSumPairCount (c : ConjClasses G) (g : G) : ℕ :=
  classSumPairCountMul c c g

omit [Finite G] in
private lemma carrier_conj_mem {c : ConjClasses G} {x a : G} (hx : x ∈ c.carrier) :
    a * x * a⁻¹ ∈ c.carrier := by
  classical
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hx ⊢
  rw [← hx]
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  exact ⟨a⁻¹, by group⟩

omit [Finite G] in
private lemma classSumPairCountMul_conj (ci cj : ConjClasses G) (g h : G) :
    classSumPairCountMul ci cj (h * g * h⁻¹) = classSumPairCountMul ci cj g := by
  classical
  unfold classSumPairCountMul
  apply Nat.card_congr
  refine
    { toFun := fun p =>
        ⟨(⟨h⁻¹ * p.1.1.1 * h, by simpa using carrier_conj_mem (a := h⁻¹) p.1.1.2⟩,
          ⟨h⁻¹ * p.1.2.1 * h, by simpa using carrier_conj_mem (a := h⁻¹) p.1.2.2⟩),
          by
            calc
              (h⁻¹ * p.1.1.1 * h) * (h⁻¹ * p.1.2.1 * h) = h⁻¹ * (p.1.1.1 * p.1.2.1) * h := by group
              _ = h⁻¹ * (h * g * h⁻¹) * h := by rw [p.2]
              _ = g := by group⟩
      invFun := fun p =>
        ⟨(⟨h * p.1.1.1 * h⁻¹, carrier_conj_mem (a := h) p.1.1.2⟩,
          ⟨h * p.1.2.1 * h⁻¹, carrier_conj_mem (a := h) p.1.2.2⟩),
          by
            calc
              (h * p.1.1.1 * h⁻¹) * (h * p.1.2.1 * h⁻¹) = h * (p.1.1.1 * p.1.2.1) * h⁻¹ := by group
              _ = h * g * h⁻¹ := by rw [p.2]⟩
      left_inv := by
        intro p
        rcases p with ⟨p, hp⟩
        rcases p with ⟨x, y⟩
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          group
        · apply Subtype.ext
          group
      right_inv := by
        intro p
        rcases p with ⟨p, hp⟩
        rcases p with ⟨x, y⟩
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          group
        · apply Subtype.ext
          group }

omit [Finite G] in
/-- The pair count `classSumPairCountMul ci cj` is a class function of `g`. -/
public lemma classSumPairCountMul_isClassFunction (ci cj : ConjClasses G) :
    IsClassFunction (fun g : G => (classSumPairCountMul ci cj g : ℂ)) := by
  intro x g
  exact congrArg (fun n : ℕ => (n : ℂ)) (classSumPairCountMul_conj ci cj x g)

omit [FiniteDimensional ℂ V] in
private lemma classSumComplex_mul_trace
    (ρ : Representation ℂ G V) (ci cj : ConjClasses G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSumComplex (G := G) ci * classSumComplex (G := G) cj)) =
      ∑ x ∈ classSet (G := G) ci, ∑ y ∈ classSet (G := G) cj, ρ.character (x * y) := by
  classical
  have hsum (c : ConjClasses G) :
      (∑ x ∈ classSet (G := G) c, ρ x) = ρ.asAlgebraHom (classSumComplex (G := G) c) := by
    rw [classSumComplex]
    rw [map_sum]
    simp
  calc
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSumComplex (G := G) ci * classSumComplex (G := G) cj))
        = LinearMap.trace ℂ V (ρ.asAlgebraHom (classSumComplex (G := G) ci) *
            ρ.asAlgebraHom (classSumComplex (G := G) cj)) := by
            rw [map_mul]
    _ = LinearMap.trace ℂ V ((∑ x ∈ classSet (G := G) ci, ρ x) *
            (∑ y ∈ classSet (G := G) cj, ρ y)) := by
            rw [← hsum ci, ← hsum cj]
    _ = LinearMap.trace ℂ V
            (∑ x ∈ classSet (G := G) ci, ∑ y ∈ classSet (G := G) cj, ρ x * ρ y) := by
            rw [Finset.sum_mul_sum]
    _ = ∑ x ∈ classSet (G := G) ci, ∑ y ∈ classSet (G := G) cj,
            LinearMap.trace ℂ V (ρ x * ρ y) := by
            simp only [map_sum]
    _ = ∑ x ∈ classSet (G := G) ci, ∑ y ∈ classSet (G := G) cj,
            LinearMap.trace ℂ V (ρ (x * y)) := by
            simp only [← map_mul (f := ρ)]
    _ = ∑ x ∈ classSet (G := G) ci, ∑ y ∈ classSet (G := G) cj, ρ.character (x * y) := by
            simp [Representation.character]

private lemma classSumComplex_mul_trace_eq_scalar_mul
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] (ci cj : ConjClasses G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSumComplex (G := G) ci * classSumComplex (G := G) cj)) =
      classSumScalarLocal (ρ := ρ) ci * classSumScalarLocal (ρ := ρ) cj *
        (Module.finrank ℂ V : ℂ) := by
  classical
  rw [map_mul]
  rw [classSumScalarLocal_spec (ρ := ρ) ci, classSumScalarLocal_spec (ρ := ρ) cj]
  have htr (a b : ℂ) :
      LinearMap.trace ℂ V ((a • (1 : Module.End ℂ V)) * (b • (1 : Module.End ℂ V))) =
        a * b * (Module.finrank ℂ V : ℂ) := by
    rw [Algebra.smul_mul_assoc]
    rw [one_mul]
    rw [smul_smul]
    simp
  exact htr (classSumScalarLocal (ρ := ρ) ci) (classSumScalarLocal (ρ := ρ) cj)

/-- The scalar product of the pair count with an irreducible character equals the
character-value expression (trace extraction for Gorenstein 4.2.12). -/
public lemma scalarProduct_classSumPairCountMul_irreducible
    (ci cj : ConjClasses G) (ti tj : G) (hti : ti ∈ ci.carrier) (htj : tj ∈ cj.carrier)
    (χ : ConjClassFunction G) (hχ : IsIrreducibleConjCharacter χ) :
    scalarProduct G (fun g : G => (classSumPairCountMul ci cj g : ℂ)) (ofConjClassFunction χ) =
      ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
        star (χ (ConjClasses.mk ti) * χ (ConjClasses.mk tj) / χ (ConjClasses.mk 1)) := by
  classical
  rcases hχ.1 with ⟨n, ρ, hρ⟩
  have : Representation.IsIrreducible ρ := by
    apply (irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using hχ.2
  let F : ClassFunction G := fun g : G => (classSumPairCountMul ci cj g : ℂ)
  have hdeg : ρ.character 1 = (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    simp [Representation.character]
  have : Nontrivial (Fin n → ℂ) := irreducible_nontrivial (ρ := ρ)
  have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) := by
    exact (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
  have hdim_ne : (Module.finrank ℂ (Fin n → ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdim_pos
  have hstarfree :
      (Nat.card G : ℂ)⁻¹ *
          (classSumScalarLocal (ρ := ρ) ci * classSumScalarLocal (ρ := ρ) cj *
            (Module.finrank ℂ (Fin n → ℂ) : ℂ)) =
        ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
          (ρ.character ti * ρ.character tj / ρ.character 1) := by
    rw [classSumScalarLocal_eq_card_mul_character_div (ρ := ρ) ci hti,
      classSumScalarLocal_eq_card_mul_character_div (ρ := ρ) cj htj]
    rw [hdeg]
    field_simp [hdim_ne]
  have hstar1 :
      star ((Nat.card G : ℂ)⁻¹ *
          (classSumScalarLocal (ρ := ρ) ci * classSumScalarLocal (ρ := ρ) cj *
            (Module.finrank ℂ (Fin n → ℂ) : ℂ))) =
        (Nat.card G : ℂ)⁻¹ *
          star (classSumScalarLocal (ρ := ρ) ci * classSumScalarLocal (ρ := ρ) cj *
            (Module.finrank ℂ (Fin n → ℂ) : ℂ)) := by
    rw [star_mul, star_inv₀]
    simp
    ring
  have hstar2 :
      star (((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
          (ρ.character ti * ρ.character tj / ρ.character 1)) =
        ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
          star (ρ.character ti * ρ.character tj / ρ.character 1) := by
    rw [star_mul, star_div₀, star_mul]
    simp
    ring
  have hstarfree' :
      star ((Nat.card G : ℂ)⁻¹ *
          (classSumScalarLocal (ρ := ρ) ci * classSumScalarLocal (ρ := ρ) cj *
            (Module.finrank ℂ (Fin n → ℂ) : ℂ))) =
        star (((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
          (ρ.character ti * ρ.character tj / ρ.character 1)) := by
    rw [hstarfree]
  have hfinal :
      (Nat.card G : ℂ)⁻¹ *
          star (classSumScalarLocal (ρ := ρ) ci * classSumScalarLocal (ρ := ρ) cj *
            (Module.finrank ℂ (Fin n → ℂ) : ℂ)) =
        ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
          star (ρ.character ti * ρ.character tj / ρ.character 1) := by
    rw [← hstar1, ← hstar2]
    exact hstarfree'
  have hsum_boole (g : G) :
      (classSumPairCountMul ci cj g : ℂ) =
        ∑ p : ci.carrier × cj.carrier, if p.1.1 * p.2.1 = g then (1 : ℂ) else 0 := by
    unfold classSumPairCountMul
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.sum_boole (p := fun p : ci.carrier × cj.carrier => p.1.1 * p.2.1 = g)
      (s := (Finset.univ : Finset (ci.carrier × cj.carrier))) (R := ℂ)]
  have hpair :
      (∑ p : ci.carrier × cj.carrier, ρ.character (p.1.1 * p.2.1)) =
        ∑ x ∈ classSet (G := G) ci, ∑ y ∈ classSet (G := G) cj, ρ.character (x * y) := by
    let eci : ci.carrier ≃ {x : G // x ∈ classSet (G := G) ci} :=
      Equiv.subtypeEquivRight (fun x : G => by
        rw [ConjClasses.mem_carrier_iff_mk_eq (a := x) (b := ci), mem_classSet_iff (G := G)])
    let ecj : cj.carrier ≃ {y : G // y ∈ classSet (G := G) cj} :=
      Equiv.subtypeEquivRight (fun y : G => by
        rw [ConjClasses.mem_carrier_iff_mk_eq (a := y) (b := cj), mem_classSet_iff (G := G)])
    let e : ci.carrier × cj.carrier ≃
        {x : G // x ∈ classSet (G := G) ci} × {y : G // y ∈ classSet (G := G) cj} :=
      eci.prodCongr ecj
    let g : {x : G // x ∈ classSet (G := G) ci} × {i : G // i ∈ classSet (G := G) cj} → ℂ :=
      fun q => ρ.character (q.1.1 * q.2.1)
    rw [← Finset.sum_coe_sort (classSet (G := G) ci)]
    simp only [← Finset.sum_coe_sort (classSet (G := G) cj)]
    change (∑ p : ci.carrier × cj.carrier, ρ.character (p.1.1 * p.2.1)) =
      ∑ x : {x : G // x ∈ classSet (G := G) ci},
        ∑ i : {i : G // i ∈ classSet (G := G) cj}, g (x, i)
    rw [← Finset.sum_product, Finset.univ_product_univ]
    exact Fintype.sum_equiv e (fun p : ci.carrier × cj.carrier =>
      ρ.character (p.1.1 * p.2.1))
      (fun q : {x : G // x ∈ classSet (G := G) ci} × {y : G // y ∈ classSet (G := G) cj} =>
        ρ.character (q.1.1 * q.2.1)) (by
          intro p
          rfl)
  calc
    scalarProduct G F (ofConjClassFunction χ)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, F g * star (χ (ConjClasses.mk g)) := by rfl
    _ = (Nat.card G : ℂ)⁻¹ *
            ∑ g : G,
              (∑ p : ci.carrier × cj.carrier, if p.1.1 * p.2.1 = g then (1 : ℂ) else 0) *
                star (χ (ConjClasses.mk g)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            dsimp [F]
            rw [hsum_boole g]
    _ = (Nat.card G : ℂ)⁻¹ *
            ∑ g : G, ∑ p : ci.carrier × cj.carrier,
              (if p.1.1 * p.2.1 = g then (1 : ℂ) else 0) * star (χ (ConjClasses.mk g)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            rw [Finset.sum_mul]
    _ = (Nat.card G : ℂ)⁻¹ *
            ∑ p : ci.carrier × cj.carrier, ∑ g : G,
              (if p.1.1 * p.2.1 = g then (1 : ℂ) else 0) * star (χ (ConjClasses.mk g)) := by
            congr 1
            rw [Finset.sum_comm]
    _ = (Nat.card G : ℂ)⁻¹ *
            ∑ p : ci.carrier × cj.carrier, star (χ (ConjClasses.mk (p.1.1 * p.2.1))) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro p hp
            rw [Finset.sum_eq_single (p.1.1 * p.2.1)]
            · simp
            · intro g hg hne
              rw [if_neg hne.symm]
              simp
            · intro hnot
              exact (hnot (Finset.mem_univ (p.1.1 * p.2.1))).elim
    _ = (Nat.card G : ℂ)⁻¹ *
            ∑ p : ci.carrier × cj.carrier, star (ρ.character (p.1.1 * p.2.1)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro p hp
            congr 1
            rw [hρ]
            rfl
    _ = (Nat.card G : ℂ)⁻¹ *
            star (∑ p : ci.carrier × cj.carrier, ρ.character (p.1.1 * p.2.1)) := by
            rw [star_sum]
    _ = (Nat.card G : ℂ)⁻¹ *
            star (∑ x ∈ classSet (G := G) ci, ∑ y ∈ classSet (G := G) cj,
              ρ.character (x * y)) := by
            rw [hpair]
    _ = (Nat.card G : ℂ)⁻¹ *
            star (LinearMap.trace ℂ (Fin n → ℂ)
              (ρ.asAlgebraHom (classSumComplex (G := G) ci * classSumComplex (G := G) cj))) := by
            rw [← classSumComplex_mul_trace (ρ := ρ) ci cj]
    _ = (Nat.card G : ℂ)⁻¹ *
            star (classSumScalarLocal (ρ := ρ) ci * classSumScalarLocal (ρ := ρ) cj *
              (Module.finrank ℂ (Fin n → ℂ) : ℂ)) := by
            rw [← classSumComplex_mul_trace_eq_scalar_mul (ρ := ρ) ci cj]
    _ = ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
            star (ρ.character ti * ρ.character tj / ρ.character 1) := hfinal
    _ = ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
            star (χ (ConjClasses.mk ti) * χ (ConjClasses.mk tj) / χ (ConjClasses.mk 1)) := by
            rw [hρ]
            rfl

/-- Gorenstein 4.2.12: the Fourier expansion of the pair count `#{(x,y) ∈ Cᵢ × Cⱼ : x·y = g}`
over a complete family of irreducible characters. -/
public theorem classSum_expansion_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ci cj : ConjClasses G) (ti tj : G) (hti : ti ∈ ci.carrier) (htj : tj ∈ cj.carrier)
    (χ : ι → ConjClassFunction G) (hχ : IsCompleteIrreducibleCharacterFamily χ) (g : G) :
    (classSumPairCountMul ci cj g : ℂ) =
      ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
        ∑ i : ι,
          star (χ i (ConjClasses.mk ti) * χ i (ConjClasses.mk tj) / χ i (ConjClasses.mk 1)) *
            χ i (ConjClasses.mk g) := by
  classical
  let F : ClassFunction G := fun g : G => (classSumPairCountMul ci cj g : ℂ)
  have hFclass : IsClassFunction F := classSumPairCountMul_isClassFunction ci cj
  have hF := completeFamily_apply_eq_sum_inner (G := G) hχ
    (toConjClassFunction F hFclass) (ConjClasses.mk g)
  have hin (i : ι) :
      classFunctionInner (toConjClassFunction F hFclass) (χ i) =
        ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
          star (χ i (ConjClasses.mk ti) * χ i (ConjClasses.mk tj) / χ i (ConjClasses.mk 1)) := by
    rw [classFunctionInner_toConjClassFunction_right F hFclass (χ i)]
    exact scalarProduct_classSumPairCountMul_irreducible ci cj ti tj hti htj (χ i) (hχ.1 i)
  calc
    (classSumPairCountMul ci cj g : ℂ)
        = toConjClassFunction F hFclass (ConjClasses.mk g) := by
            rw [toConjClassFunction_apply F hFclass g]
    _ = ∑ i : ι, classFunctionInner (toConjClassFunction F hFclass) (χ i) *
          χ i (ConjClasses.mk g) := hF
    _ = ∑ i : ι,
          (((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
            star (χ i (ConjClasses.mk ti) * χ i (ConjClasses.mk tj) / χ i (ConjClasses.mk 1))) *
              χ i (ConjClasses.mk g) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hin i]
    _ = ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
          ∑ i : ι,
            star (χ i (ConjClasses.mk ti) * χ i (ConjClasses.mk tj) / χ i (ConjClasses.mk 1)) *
              χ i (ConjClasses.mk g) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [mul_assoc]

/-- Gorenstein 4.2.12 for one class: `#{(x,y) ∈ C × C : x·y = g}`. -/
public theorem classSum_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ConjClasses G) (t : G) (ht : t ∈ c.carrier)
    (χ : ι → ConjClassFunction G) (hχ : IsCompleteIrreducibleCharacterFamily χ) (g : G) :
    (classSumPairCount c g : ℂ) =
      ((Nat.card c.carrier : ℂ) ^ 2 / (Nat.card G : ℂ)) *
        ∑ i : ι, star (χ i (ConjClasses.mk t) ^ 2 / χ i (ConjClasses.mk 1)) *
          χ i (ConjClasses.mk g) := by
  classical
  simpa [classSumPairCount, pow_two] using
    classSum_expansion_mul c c t t ht ht χ hχ g

/-- For an irreducible class-function character, `star (χ (mk g)) = χ (mk g⁻¹)`. -/
public lemma star_conjChar_apply_inv {χ : ConjClassFunction G} (hχ : IsConjCharacter χ) (g : G) :
    star (χ (ConjClasses.mk g)) = χ (ConjClasses.mk g⁻¹) := by
  rcases hχ with ⟨n, ρ, hρ⟩
  subst hρ
  change star (ρ.character g) = ρ.character g⁻¹
  exact (representation_character_inv_eq_star_character ρ g).symm

private lemma star_involution_value {χ : ConjClassFunction G} (hχ : IsConjCharacter χ)
    (t : G) (ht2 : t * t = 1) :
    star (χ (ConjClasses.mk t)) = χ (ConjClasses.mk t) := by
  have htinv : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht2).symm
  rw [star_conjChar_apply_inv hχ t, htinv]

private lemma star_sq_div_of_involution {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) (t : G) (ht2 : t * t = 1) :
    star (χ (ConjClasses.mk t) ^ 2 / χ (ConjClasses.mk 1)) =
      χ (ConjClasses.mk t) ^ 2 / χ (ConjClasses.mk 1) := by
  rw [star_div₀, star_pow]
  rw [star_involution_value hχ.1 t ht2, star_involution_value hχ.1 1 (by simp)]

private lemma star_mul_div_of_involutions {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) (ti tj : G) (hti2 : ti * ti = 1) (htj2 : tj * tj = 1) :
    star (χ (ConjClasses.mk ti) * χ (ConjClasses.mk tj) / χ (ConjClasses.mk 1)) =
      χ (ConjClasses.mk ti) * χ (ConjClasses.mk tj) / χ (ConjClasses.mk 1) := by
  rw [star_div₀, star_mul]
  rw [star_involution_value hχ.1 ti hti2, star_involution_value hχ.1 tj htj2,
    star_involution_value hχ.1 1 (by simp)]
  ring

/-- Gorenstein 4.2.12 for one class of an involution `t`, in the paper's form
(`χ(t)` is real for an involution, so the star disappears). -/
public theorem classSum_expansion_of_involution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ConjClasses G) (t : G) (ht : t ∈ c.carrier) (ht2 : t * t = 1)
    (χ : ι → ConjClassFunction G) (hχ : IsCompleteIrreducibleCharacterFamily χ) (g : G) :
    (classSumPairCount c g : ℂ) =
      ((Nat.card c.carrier : ℂ) ^ 2 / (Nat.card G : ℂ)) *
        ∑ i : ι, (χ i (ConjClasses.mk t) ^ 2 / χ i (ConjClasses.mk 1)) *
          χ i (ConjClasses.mk g) := by
  classical
  rw [classSum_expansion c t ht χ hχ g]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_sq_div_of_involution (hχ.1 i) t ht2]

/-- Gorenstein 4.2.12 for two classes of involutions, in the paper's form. -/
public theorem classSum_expansion_mul_of_involutions
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ci cj : ConjClasses G) (ti tj : G) (hti : ti ∈ ci.carrier) (htj : tj ∈ cj.carrier)
    (hti2 : ti * ti = 1) (htj2 : tj * tj = 1)
    (χ : ι → ConjClassFunction G) (hχ : IsCompleteIrreducibleCharacterFamily χ) (g : G) :
    (classSumPairCountMul ci cj g : ℂ) =
      ((Nat.card ci.carrier : ℂ) * (Nat.card cj.carrier : ℂ) / (Nat.card G : ℂ)) *
        ∑ i : ι, (χ i (ConjClasses.mk ti) * χ i (ConjClasses.mk tj) / χ i (ConjClasses.mk 1)) *
          χ i (ConjClasses.mk g) := by
  classical
  rw [classSum_expansion_mul ci cj ti tj hti htj χ hχ g]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_mul_div_of_involutions (hχ.1 i) ti tj hti2 htj2]

end

end CFSG.Theory.Character
