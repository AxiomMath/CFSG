module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Induction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality
public import Mathlib.Algebra.Central.End
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.NumberTheory.Niven
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.Theory.Character

open _root_.Representation
open Theory.Representation

open Theory.Character

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

variable {G V : Type*} [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private abbrev IntegralGroupAlgebra (G : Type*) [Group G] := MonoidAlgebra ℤ G


private noncomputable def classSet (c : ConjClasses G) : Finset G :=
  letI : DecidableEq (ConjClasses G) := Classical.decEq (ConjClasses G)
  Finset.univ.filter fun g : G => ConjClasses.mk g = c

private noncomputable def conjClassFinset : Finset (ConjClasses G) :=
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  Finset.univ

private lemma mem_conjClassFinset (c : ConjClasses G) :
    c ∈ conjClassFinset (G := G) := by
  classical
  simp [conjClassFinset]

private lemma mem_classSet_iff {c : ConjClasses G} {g : G} :
    g ∈ classSet (G := G) c ↔ ConjClasses.mk g = c := by
  classical
  simp [classSet]

private noncomputable def classSumInt (c : ConjClasses G) : MonoidAlgebra ℤ G :=
  ∑ g ∈ classSet (G := G) c, MonoidAlgebra.single g (1 : ℤ)

private noncomputable def classSumComplex (c : ConjClasses G) : MonoidAlgebra ℂ G :=
  ∑ g ∈ classSet (G := G) c, MonoidAlgebra.single g (1 : ℂ)

private instance integralGroupAlgebra_moduleFinite :
    Module.Finite ℤ (IntegralGroupAlgebra G) := by
  classical
  exact Module.Finite.of_basis (MonoidAlgebra.basis G ℤ)

private lemma classSumInt_isIntegral (c : ConjClasses G) :
    IsIntegral ℤ (classSumInt (G := G) c) := by
  classical
  have hfin : Module.Finite ℤ (MonoidAlgebra ℤ G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G ℤ)
  exact @IsIntegral.of_finite ℤ (MonoidAlgebra ℤ G) _ _ _ hfin (classSumInt (G := G) c)

private lemma classSumComplex_isIntegral (c : ConjClasses G) :
    IsIntegral ℤ (classSumComplex (G := G) c) := by
  classical
  let φ : MonoidAlgebra ℤ G →+* MonoidAlgebra ℂ G :=
    MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)
  have hmap :
      φ (classSumInt (G := G) c) = classSumComplex (G := G) c := by
    simp [φ, classSumInt, classSumComplex]
  rw [← hmap]
  exact map_isIntegral_int φ (classSumInt_isIntegral (G := G) c)

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

omit [Finite G] [FiniteDimensional ℂ V] in
public theorem irreducible_nontrivial
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    Nontrivial V := by
  classical
  by_contra hV
  have hsub : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top :
      (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    change (⊥ : Submodule ℂ V) = ⊤
    rw [eq_top_iff]
    intro v _hv
    simp [hsub.elim v 0]
  exact IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ) hbot_top

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

omit [FiniteDimensional ℂ V] in
private lemma isIntegral_scalar_of_isIntegral_smul_one
    [Nontrivial V] (a : ℂ) (h : IsIntegral ℤ (a • (1 : Module.End ℂ V))) :
    IsIntegral ℤ a := by
  have h' : IsIntegral ℤ (algebraMap ℂ (Module.End ℂ V) a) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact h
  let f : ℂ →ₐ[ℤ] Module.End ℂ V := IsScalarTower.toAlgHom ℤ ℂ (Module.End ℂ V)
  exact (isIntegral_algHom_iff f
    (FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V))).mp h'

private lemma classSum_scalar_isIntegral
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    ∃ a : ℂ,
      IsIntegral ℤ a ∧
        ρ.asAlgebraHom (classSumComplex (G := G) c) = a • (1 : Module.End ℂ V) := by
  classical
  obtain ⟨a, ha⟩ := centralElementIntertwiner_eq_scalar
    (ρ := ρ) (classSumComplex (G := G) c) (classSumComplex_comm (G := G) c)
  refine ⟨a, ?_, ha⟩
  have hzint : IsIntegral ℤ (classSumComplex (G := G) c) :=
    classSumComplex_isIntegral (G := G) c
  have hend : IsIntegral ℤ (ρ.asAlgebraHom (classSumComplex (G := G) c)) := by
    exact IsIntegral.map (ρ.asAlgebraHom) hzint
  have : Nontrivial V := irreducible_nontrivial (ρ := ρ)
  exact isIntegral_scalar_of_isIntegral_smul_one (V := V) a (by simpa [ha] using hend)

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

public lemma trace_of_finite_order_isIntegral
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace ℂ V f) := by
  classical
  change IsIntegral ℤ (LinearMap.trace ℂ V (f ^ 1))
  rw [trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow]
  refine IsIntegral.sum (s := Finset.univ) (fun μ : f.Eigenvalues =>
    ((μ : ℂ) ^ 1 * (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℂ))) ?_
  intro μ _hμ
  have hμpow : (μ : ℂ) ^ n = 1 :=
    eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
  have hμint : IsIntegral ℤ (μ : ℂ) := by
    exact IsIntegral.of_pow (Nat.pos_of_ne_zero hn)
      (by simpa [hμpow] using (isIntegral_one : IsIntegral ℤ (1 : ℂ)))
  have hrank_int :
      IsIntegral ℤ ((Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℂ)) :=
    isIntegral_algebraMap
  simpa using hμint.mul hrank_int

public lemma representation_character_isIntegral
    (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (ρ.character g) := by
  classical
  let n := orderOf g
  have hn : n ≠ 0 := Nat.ne_of_gt (orderOf_pos g)
  have hpow : (ρ g) ^ n = 1 := by
    subst n
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  exact trace_of_finite_order_isIntegral (f := ρ g) hn hpow

private noncomputable def classRep (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.exists_rep c)

omit [Finite G] in
private lemma classRep_spec (c : ConjClasses G) :
    ConjClasses.mk (classRep (G := G) c) = c :=
  Classical.choose_spec (ConjClasses.exists_rep c)

omit [Finite G] [FiniteDimensional ℂ V] in
private lemma character_eq_of_mk_eq
    (ρ : Representation ℂ G V) {g x : G}
    (h : ConjClasses.mk g = ConjClasses.mk x) :
    ρ.character g = ρ.character x := by
  rw [ConjClasses.mk_eq_mk_iff_isConj] at h
  rcases isConj_iff.mp h with ⟨y, rfl⟩
  simp

omit [FiniteDimensional ℂ V] in
private lemma sum_character_norm_by_conjClasses
    (ρ : Representation ℂ G V) :
    (∑ g : G, ρ.character g * star (ρ.character g)) =
      ∑ c ∈ conjClassFinset (G := G),
        (Nat.card c.carrier : ℂ) * ρ.character (classRep (G := G) c) *
          star (ρ.character (classRep (G := G) c)) := by
  classical
  calc
    (∑ g : G, ρ.character g * star (ρ.character g))
        = ∑ c ∈ conjClassFinset (G := G),
            ∑ g ∈ classSet (G := G) c, ρ.character g * star (ρ.character g) := by
            rw [← Finset.sum_fiberwise_of_maps_to
              (s := (Finset.univ : Finset G))
              (t := conjClassFinset (G := G))
              (g := ConjClasses.mk)
              (fun x _ => mem_conjClassFinset (G := G) (ConjClasses.mk x))
              (fun g : G => ρ.character g * star (ρ.character g))]
            refine Finset.sum_congr rfl ?_
            intro c _hc
            congr 1
            ext g
            simp [classSet]
    _ = ∑ c ∈ conjClassFinset (G := G),
        (Nat.card c.carrier : ℂ) * ρ.character (classRep (G := G) c) *
          star (ρ.character (classRep (G := G) c)) := by
        refine Finset.sum_congr rfl ?_
        intro c _hc
        calc
          (∑ g ∈ classSet (G := G) c, ρ.character g * star (ρ.character g))
              = ∑ _g ∈ classSet (G := G) c,
                  ρ.character (classRep (G := G) c) *
                    star (ρ.character (classRep (G := G) c)) := by
              refine Finset.sum_congr rfl ?_
              intro g hg
              have hgmk : ConjClasses.mk g = c := (mem_classSet_iff (G := G)).1 hg
              have hχ :
                  ρ.character g = ρ.character (classRep (G := G) c) :=
                character_eq_of_mk_eq (ρ := ρ) (by
                  rw [hgmk, classRep_spec (G := G) c])
              rw [hχ]
          _ = (Nat.card c.carrier : ℂ) * ρ.character (classRep (G := G) c) *
                star (ρ.character (classRep (G := G) c)) := by
              rw [Finset.sum_const, classSet_card_eq_carrier_card (G := G) c]
              simp [nsmul_eq_mul, mul_assoc]

public noncomputable def classSumScalar
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) : ℂ :=
  Classical.choose (classSum_scalar_isIntegral (ρ := ρ) c)

public theorem classSumScalar_isIntegral
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    IsIntegral ℤ (classSumScalar (ρ := ρ) c) :=
  (Classical.choose_spec (classSum_scalar_isIntegral (ρ := ρ) c)).1

private lemma classSumScalar_spec
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    ρ.asAlgebraHom (classSumComplex (G := G) c) =
      classSumScalar (ρ := ρ) c • (1 : Module.End ℂ V) :=
  (Classical.choose_spec (classSum_scalar_isIntegral (ρ := ρ) c)).2

public theorem classSumScalar_eq_card_mul_character_div
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) {x : G} (hx : x ∈ c.carrier) :
    classSumScalar (ρ := ρ) c =
      (Nat.card c.carrier : ℂ) * ρ.character x / ρ.character 1 := by
  classical
  have : Nontrivial V := irreducible_nontrivial (ρ := ρ)
  have hdim_pos : 0 < Module.finrank ℂ V :=
    (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
  have hdim_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdim_pos
  have hxmk : ConjClasses.mk x = c := (ConjClasses.mem_carrier_iff_mk_eq).1 hx
  have hscalar :
      classSumScalar (ρ := ρ) c * (Module.finrank ℂ V : ℂ) =
        (Nat.card c.carrier : ℂ) * ρ.character x :=
    classSum_scalar_mul_finrank (ρ := ρ) c hxmk
      (classSumScalar_spec (ρ := ρ) c)
  have hdegree : ρ.character 1 = (Module.finrank ℂ V : ℂ) := by
    simp [Representation.character]
  rw [hdegree]
  field_simp [hdim_ne]
  simpa [mul_comm] using hscalar

private theorem classSumComplex_mul_eq_sum_of_coefficients
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ)
    (hdata : ∀ i j s : ConjClasses G, ∀ x : G, x ∈ s.carrier →
      a i j s =
        Nat.card {p : i.carrier × j.carrier // p.1.1 * p.2.1 = x})
    (i j : ConjClasses G) :
    classSumComplex (G := G) i * classSumComplex (G := G) j =
      ∑ s : ConjClasses G, (a i j s : ℂ) • classSumComplex (G := G) s := by
  classical
  ext x
  rw [MonoidAlgebra.coeff_mul]
  have hinner (u : G) :
      Finsupp.sum (classSumComplex (G := G) j).coeff
        (fun v r => if u * v = x then (classSumComplex (G := G) i).coeff u * r else 0) =
        ∑ v : G, if u * v = x then
          (classSumComplex (G := G) i).coeff u *
            (classSumComplex (G := G) j).coeff v else 0 := by
    rw [Finsupp.sum_of_support_subset (classSumComplex (G := G) j).coeff
      (s := Finset.univ) (by intro y hy; simp)
      (fun v r => if u * v = x then (classSumComplex (G := G) i).coeff u * r else 0)
      (by intro y hy; by_cases h : u * y = x <;> simp [h])]
  have hleft :
      (Finsupp.sum (classSumComplex (G := G) i).coeff fun u r =>
        Finsupp.sum (classSumComplex (G := G) j).coeff fun v t =>
          if u * v = x then r * t else 0) =
      ∑ u : G, ∑ v : G, if u * v = x then
        (classSumComplex (G := G) i).coeff u *
          (classSumComplex (G := G) j).coeff v else 0 := by
    rw [Finsupp.sum_of_support_subset (classSumComplex (G := G) i).coeff
      (s := Finset.univ) (by intro y hy; simp)
      (fun u r => Finsupp.sum (classSumComplex (G := G) j).coeff fun v t =>
        if u * v = x then r * t else 0)
      (by intro y hy; simp)]
    apply Finset.sum_congr rfl
    intro u _hu
    exact hinner u
  have hindicator :
      (∑ u : G, ∑ v : G, if u * v = x then
        (classSumComplex (G := G) i).coeff u *
          (classSumComplex (G := G) j).coeff v else 0) =
      ∑ u : G, ∑ v : G,
        if u ∈ i.carrier ∧ v ∈ j.carrier ∧ u * v = x then (1 : ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro u _hu
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases hiu : u ∈ i.carrier
    · by_cases hjv : v ∈ j.carrier
      · by_cases huv : u * v = x
        · simp [classSumComplex_coeff, ConjClasses.mem_carrier_iff_mk_eq.mp hiu,
            ConjClasses.mem_carrier_iff_mk_eq.mp hjv, huv, hiu, hjv]
        · simp [huv]
      · have hjmk : ConjClasses.mk v ≠ j := by
          intro h
          exact hjv ((ConjClasses.mem_carrier_iff_mk_eq).2 h)
        by_cases huv : u * v = x
        · simp [classSumComplex_coeff, ConjClasses.mem_carrier_iff_mk_eq.mp hiu,
            hjmk, huv, hiu, hjv]
        · simp [huv]
    · have himk : ConjClasses.mk u ≠ i := by
        intro h
        exact hiu ((ConjClasses.mem_carrier_iff_mk_eq).2 h)
      by_cases huv : u * v = x
      · simp [classSumComplex_coeff, himk, huv, hiu]
      · simp [huv]
  have hdouble :
      (∑ u : G, ∑ v : G,
        if u ∈ i.carrier ∧ v ∈ j.carrier ∧ u * v = x then (1 : ℂ) else 0) =
      (Nat.card {uv : G × G //
        uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 = x} : ℂ) := by
    let pset : G × G → Prop := fun uv =>
      uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 = x
    have hsum := Finset.sum_boole
      (p := pset)
      (s := (Finset.univ : Finset (G × G))) (R := ℂ)
    have hcard :
        (Finset.univ.filter pset).card =
          Nat.card {uv : G × G //
            uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 = x} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← hcard]
    rw [← hsum]
    change ((Finset.univ : Finset G).sum fun u =>
      (Finset.univ : Finset G).sum fun v =>
        if u ∈ i.carrier ∧ v ∈ j.carrier ∧ u * v = x then (1 : ℂ) else 0) =
        (Finset.univ : Finset (G × G)).sum fun uv =>
          if pset uv then (1 : ℂ) else 0
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  have hpairEquiv :
      {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 = x} ≃
        {p : i.carrier × j.carrier // p.1.1 * p.2.1 = x} := by
    refine
      { toFun := fun uv =>
          ⟨(⟨uv.1.1, uv.2.1⟩, ⟨uv.1.2, uv.2.2.1⟩), uv.2.2.2⟩
        invFun := fun p =>
          ⟨((p.1.1 : G), (p.1.2 : G)), ⟨p.1.1.2, p.1.2.2, p.2⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro uv
      rcases uv with ⟨⟨u, v⟩, hu, hv, huv⟩
      rfl
    · intro p
      rcases p with ⟨p, hp⟩
      rcases p with ⟨u, v⟩
      rcases u with ⟨u, hu⟩
      rcases v with ⟨v, hv⟩
      rfl
  have hxmem : x ∈ (ConjClasses.mk x).carrier :=
    (ConjClasses.mem_carrier_iff_mk_eq).2 rfl
  have hcoeff :
      (Nat.card {uv : G × G //
        uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 = x} : ℂ) =
        (a i j (ConjClasses.mk x) : ℂ) := by
    rw [Nat.card_congr hpairEquiv]
    exact_mod_cast (hdata i j (ConjClasses.mk x) x hxmem).symm
  have hright :
      ((@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum fun s =>
        (a i j s : ℂ) • classSumComplex (G := G) s).coeff x =
        (a i j (ConjClasses.mk x) : ℂ) := by
    simp [classSumComplex_coeff]
  exact hleft.trans (hindicator.trans (hdouble.trans (hcoeff.trans hright.symm)))

public theorem classSumScalar_mul_eq_sum_of_coefficients
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ)
    (hdata : ∀ i j s : ConjClasses G, ∀ x : G, x ∈ s.carrier →
      a i j s =
        Nat.card {p : i.carrier × j.carrier // p.1.1 * p.2.1 = x})
    (i j : ConjClasses G) :
    classSumScalar (ρ := ρ) i * classSumScalar (ρ := ρ) j =
      (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
        (fun s => (a i j s : ℂ) * classSumScalar (ρ := ρ) s) := by
  classical
  let C : Finset (ConjClasses G) :=
    @Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))
  have hprod := congrArg ρ.asAlgebraHom
    (classSumComplex_mul_eq_sum_of_coefficients (G := G) a hdata i j)
  have hend :
      (classSumScalar (ρ := ρ) i * classSumScalar (ρ := ρ) j) •
          (1 : Module.End ℂ V) =
        (C.sum fun s => (a i j s : ℂ) * classSumScalar (ρ := ρ) s) •
          (1 : Module.End ℂ V) := by
    rw [map_mul] at hprod
    rw [classSumScalar_spec (ρ := ρ) i, classSumScalar_spec (ρ := ρ) j] at hprod
    rw [map_sum] at hprod
    simp only [map_smul, classSumScalar_spec] at hprod
    dsimp [C] at hprod ⊢
    calc
      (classSumScalar (ρ := ρ) i * classSumScalar (ρ := ρ) j) •
          (1 : Module.End ℂ V) =
        classSumScalar (ρ := ρ) i • (1 : Module.End ℂ V) *
          classSumScalar (ρ := ρ) j • (1 : Module.End ℂ V) := by
            simp only [Algebra.smul_mul_assoc, one_mul, smul_smul]
      _ = (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
          (fun s => (a i j s : ℂ) • classSumScalar (ρ := ρ) s •
            (1 : Module.End ℂ V)) := hprod
      _ = (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
          (fun s => ((a i j s : ℂ) * classSumScalar (ρ := ρ) s) •
            (1 : Module.End ℂ V)) := by
            refine Finset.sum_congr rfl ?_
            intro s _hs
            rw [smul_smul]
      _ = ((@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
          (fun s => (a i j s : ℂ) * classSumScalar (ρ := ρ) s)) •
            (1 : Module.End ℂ V) := by
            rw [Finset.sum_smul]
  have : Nontrivial V := irreducible_nontrivial (ρ := ρ)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hvend := congrArg (fun f : Module.End ℂ V => f v) hend
  exact (smul_left_injective ℂ hv) (by simpa [C] using hvend)

/-- For an irreducible complex representation of a finite group, the dimension divides the group order. -/
public theorem irreducible_dimension_dvd_group_order
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    Module.finrank ℂ V ∣ Nat.card G := by
  classical
  have : Nontrivial V := irreducible_nontrivial (ρ := ρ)
  let d : ℕ := Module.finrank ℂ V
  let dℂ : ℂ := (d : ℂ)
  let z : ℂ :=
    ∑ c ∈ conjClassFinset (G := G),
      classSumScalar (ρ := ρ) c * star (ρ.character (classRep (G := G) c))
  have hd_pos : 0 < d := by
    exact (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
  have hd_ne : d ≠ 0 := Nat.ne_of_gt hd_pos
  have hdℂ_ne : dℂ ≠ 0 := by
    dsimp [dℂ]
    exact_mod_cast hd_ne
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hnorm :
      (Nat.card G : ℂ)⁻¹ *
          ∑ g : G, ρ.character g * star (ρ.character g) = 1 := by
    have hnorm' := (irreducible_iff_character_norm_one (ρ := ρ)).1 inferInstance
    unfold classFunctionInner at hnorm'
    have hcharacter (g : G) :
        characterClassFunction ρ (ConjClasses.mk g) = ρ.character g := rfl
    simpa only [hcharacter] using hnorm'
  have hsumG :
      (∑ g : G, ρ.character g * star (ρ.character g)) = (Nat.card G : ℂ) := by
    calc
      (∑ g : G, ρ.character g * star (ρ.character g))
          = (Nat.card G : ℂ) *
              ((Nat.card G : ℂ)⁻¹ *
                ∑ g : G, ρ.character g * star (ρ.character g)) := by
              rw [← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul]
      _ = (Nat.card G : ℂ) * 1 := by rw [hnorm]
      _ = (Nat.card G : ℂ) := by rw [mul_one]
  have hclassSum :
      (Nat.card G : ℂ) =
        ∑ c ∈ conjClassFinset (G := G),
          (Nat.card c.carrier : ℂ) * ρ.character (classRep (G := G) c) *
            star (ρ.character (classRep (G := G) c)) := by
    exact hsumG.symm.trans (sum_character_norm_by_conjClasses (ρ := ρ))
  have hscalar (c : ConjClasses G) :
      classSumScalar (ρ := ρ) c * dℂ =
        (Nat.card c.carrier : ℂ) * ρ.character (classRep (G := G) c) := by
    simpa [d, dℂ] using
      classSum_scalar_mul_finrank (ρ := ρ) c (classRep_spec (G := G) c)
        (classSumScalar_spec (ρ := ρ) c)
  have hcard_eq_mul_z : (Nat.card G : ℂ) = dℂ * z := by
    calc
      (Nat.card G : ℂ)
          = ∑ c ∈ conjClassFinset (G := G),
              (Nat.card c.carrier : ℂ) * ρ.character (classRep (G := G) c) *
                star (ρ.character (classRep (G := G) c)) := hclassSum
      _ = ∑ c ∈ conjClassFinset (G := G),
              (classSumScalar (ρ := ρ) c * dℂ) *
                star (ρ.character (classRep (G := G) c)) := by
            refine Finset.sum_congr rfl ?_
            intro c _hc
            rw [hscalar c]
      _ = dℂ * z := by
            simp [z]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro c _hc
            ring
  have hz_int : IsIntegral ℤ z := by
    dsimp [z]
    refine IsIntegral.sum (s := conjClassFinset (G := G))
      (fun c : ConjClasses G =>
        classSumScalar (ρ := ρ) c * star (ρ.character (classRep (G := G) c))) ?_
    intro c _hc
    have hstar : IsIntegral ℤ (star (ρ.character (classRep (G := G) c))) := by
      rw [(representation_character_inv_eq_star_character ρ
        (classRep (G := G) c)).symm]
      exact representation_character_isIntegral (ρ := ρ) ((classRep (G := G) c)⁻¹)
    exact (classSumScalar_isIntegral (ρ := ρ) c).mul hstar
  have hquot_eq_z : (Nat.card G : ℂ) / dℂ = z := by
    rw [hcard_eq_mul_z]
    field_simp [hdℂ_ne]
  have hquot_int : IsIntegral ℤ ((Nat.card G : ℂ) / dℂ) := by
    rw [hquot_eq_z]
    exact hz_int
  have hquot_rat :
      ∃ q : ℚ, (Nat.card G : ℂ) / dℂ = (q : ℂ) := by
    refine ⟨(Nat.card G : ℚ) / (d : ℚ), ?_⟩
    simp [dℂ]
  obtain ⟨k, hk⟩ := (hquot_int.exists_int_iff_exists_rat).1 hquot_rat
  have hrat_eq_int : (Nat.card G : ℚ) / (d : ℚ) = (k : ℚ) := by
    apply Rat.cast_injective (α := ℂ)
    simpa [dℂ] using hk
  have hden :
      ((Nat.card G : ℚ) / (d : ℚ)).den = 1 := by
    rw [hrat_eq_int]
    simp
  exact (Rat.den_div_natCast_eq_one_iff (Nat.card G) d hd_ne).1 hden

end

end CFSG.Theory.Character
