module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeCardSubgroupIntersection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (11): the aligned-conjugate product family

This module formalizes the abstract half of Bender's equation (11)
(`refs/bender-dihedral-sylow.tex`, page 227): the ambient direct-product
region `P × E` contains `(p₁ - 1) · q · k'` distinct conjugates of `P`
different from `P`.

## Setting

* `P` and `P0` are commuting order-`p` subgroups with `P ⊓ P0 = ⊥`
  (so `A = P ⊔ P0` is of type `(p, p)`, the "plane" of lines);
* `P0 ≤ E` with `P ⊓ E = ⊥` and `E ≤ C_G(P)` (the external product
  geometry: `P ⊔ E = P × E`);
* the **lines** `secondCase_linesIn G P P0` are the ambient conjugates of
  `P` inside `A` different from `P` (there are `p₁ - 1` of them);
* the **tori** `secondCase_toriOf G P0 E` are the `E`-conjugates of `P0`.

## The pair map

For each torus `R = P0^e` (with the chosen `E`-conjugator `e(R)`) and each
line `X`, the map sends `(X, R)` to `X^{e(R)}`.  Since `e(R) ∈ E`
centralizes `P`, this fixes `P` and moves the plane `A = P ⊔ P0` to
`P ⊔ R`; the image lies in `P ⊔ E`, is a conjugate of `P`, and differs
from `P`.

## Injectivity (the recovery)

From the image `Y = X^{e(R)}` the torus is recovered as the intersection
`R = (Y ⊔ P) ∩ E` (because `Y ⊔ P = (X ⊔ P)^{e(R)} = (P ⊔ P0)^{e(R)} =
P ⊔ R` and `(P ⊔ R) ∩ E = R` under the external-product geometry), and
then the line is recovered by conjugating back by `e(R)⁻¹`.  Hence the
pair map is injective.

The main theorem `secondCase_linearEquation11_product_family_conjugate_card`
accepts an **injective family** `τ : B → secondCase_toriOf G P0 E` indexed
by a type `B` of cardinal `q · k'` (e.g. the quotient orbit of the tori,
lifting through `E → E/Z(E)` — no centerless or `p`-coprime-center
hypothesis is needed), together with the exact line count `p₁ - 1`, and
concludes

```lean
(p1 - 1) * q * k' ≤ Nat.card (secondCase_familyIn G P E)
```

i.e. `P ⊔ E` contains at least `(p₁ - 1) · q · k'` distinct ambient
conjugates of `P` other than `P`.  The convenience corollary
`secondCase_linearEquation11_product_family_conjugate_card_of_tori`
specializes to the exact torus-orbit count.  The source-specific region
counting (equation (11)'s downstream use) is owned by
`SecondCaseLinearEquationElevenData`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## 0. Generic group-theory helpers -/

/-- Every element of the join `H ⊔ K` of two pointwise-commuting subgroups
is a product `h · k` with `h ∈ H`, `k ∈ K`. -/
private lemma mem_mul_of_mem_sup_of_commute {G : Type u} [Group G]
    {H K : Subgroup G} (hcomm : ∀ h : H, ∀ k : K, (h : G) * (k : G) = (k : G) * (h : G))
    {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h : H, ∃ k : K, (h : G) * (k : G) = x := by
  classical
  let HK : Subgroup G :=
    { carrier := {x | ∃ h : H, ∃ k : K, (h : G) * (k : G) = x}
      one_mem' := ⟨1, 1, by simp⟩
      mul_mem' := by
        rintro x y ⟨h1, k1, rfl⟩ ⟨h2, k2, rfl⟩
        refine ⟨h1 * h2, k1 * k2, ?_⟩
        calc
          ((h1 * h2 : H) : G) * ((k1 * k2 : K) : G) =
              ((h1 : G) * (h2 : G)) * ((k1 : G) * (k2 : G)) := by simp
          _ = (h1 : G) * ((h2 : G) * (k1 : G)) * (k2 : G) := by group
          _ = (h1 : G) * ((k1 : G) * (h2 : G)) * (k2 : G) := by rw [← hcomm h2 k1]
          _ = ((h1 : G) * (k1 : G)) * ((h2 : G) * (k2 : G)) := by group
      inv_mem' := by
        rintro x ⟨h, k, rfl⟩
        refine ⟨h⁻¹, k⁻¹, ?_⟩
        calc
          ((h⁻¹ : H) : G) * ((k⁻¹ : K) : G) = ((k⁻¹ : K) : G) * ((h⁻¹ : H) : G) := hcomm h⁻¹ k⁻¹
          _ = ((h : G) * (k : G))⁻¹ := by simp }
  have hH : H ≤ HK := by
    intro h hh
    exact ⟨⟨h, hh⟩, 1, by simp⟩
  have hK : K ≤ HK := by
    intro k hk
    exact ⟨1, ⟨k, hk⟩, by simp⟩
  exact (sup_le hH hK) hx

/-- The cardinality of the join of two pointwise-commuting subgroups with
trivial intersection is the product of the cardinalities. -/
public lemma subgroup_card_sup_of_commute {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G}
    (hcomm : ∀ h : H, ∀ k : K, (h : G) * (k : G) = (k : G) * (h : G))
    (hdisj : Disjoint H K) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  classical
  let e : H × K → (H ⊔ K : Subgroup G) := fun x =>
    ⟨(x.1 : G) * (x.2 : G),
      Subgroup.mul_mem (H ⊔ K) ((le_sup_left : H ≤ H ⊔ K) x.1.2)
        ((le_sup_right : K ≤ H ⊔ K) x.2.2)⟩
  have hinj : Function.Injective e := by
    intro a b hab
    have habG : (a.1 : G) * (a.2 : G) = (b.1 : G) * (b.2 : G) := congrArg Subtype.val hab
    have hEq : (b.1 : G)⁻¹ * (a.1 : G) = (b.2 : G) * (a.2 : G)⁻¹ := by
      calc
        (b.1 : G)⁻¹ * (a.1 : G) =
            (b.1 : G)⁻¹ * ((a.1 : G) * (a.2 : G)) * (a.2 : G)⁻¹ := by group
        _ = (b.1 : G)⁻¹ * ((b.1 : G) * (b.2 : G)) * (a.2 : G)⁻¹ := by rw [habG]
        _ = (b.2 : G) * (a.2 : G)⁻¹ := by group
    have hbot : (b.1 : G)⁻¹ * (a.1 : G) = 1 := by
      have hmem : (b.1 : G)⁻¹ * (a.1 : G) ∈ H ⊓ K :=
        Subgroup.mem_inf.mpr
          ⟨Subgroup.mul_mem H (Subgroup.inv_mem H b.1.2) a.1.2, by
            simpa [hEq] using (Subgroup.mul_mem K b.2.2 (Subgroup.inv_mem K a.2.2))⟩
      have hmem' : (b.1 : G)⁻¹ * (a.1 : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisj.eq_bot] using hmem
      exact Subgroup.mem_bot.mp hmem'
    have ha1 : a.1 = b.1 := by
      apply Subtype.ext
      calc
        (a.1 : G) = (b.1 : G) * ((b.1 : G)⁻¹ * (a.1 : G)) := by group
        _ = (b.1 : G) * 1 := by rw [hbot]
        _ = (b.1 : G) := by simp
    have h1k : (b.2 : G) * (a.2 : G)⁻¹ = 1 := by
      simpa [hbot] using hEq.symm
    have ha2 : a.2 = b.2 := by
      apply Subtype.ext
      have h1k' : (a.2 : G) * (b.2 : G)⁻¹ = 1 := by
        have hi := congrArg (fun z : G => z⁻¹) h1k
        simpa using hi
      calc
        (a.2 : G) = (a.2 : G) * ((b.2 : G)⁻¹ * (b.2 : G)) := by group
        _ = (a.2 : G) * (b.2 : G)⁻¹ * (b.2 : G) := by group
        _ = 1 * (b.2 : G) := by rw [h1k']
        _ = (b.2 : G) := by simp
    exact Prod.ext ha1 ha2
  have hsurj : Function.Surjective e := by
    intro x
    rcases mem_mul_of_mem_sup_of_commute (H := H) (K := K) hcomm x.2 with ⟨h, k, hx⟩
    refine ⟨(h, k), ?_⟩
    apply Subtype.ext
    exact hx
  calc
    Nat.card (H ⊔ K : Subgroup G) = Nat.card (H × K) :=
      (Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj⟩)).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod H K

/-- Conjugation by an element of `E ≤ C_G(P)` fixes `P`. -/
private theorem conj_fix_of_mem_centralizer {G : Type u} [Group G]
    {P E : Subgroup G} (hEcentP : E ≤ Subgroup.centralizer (P : Set G)) (e : E) :
    P.map (MulAut.conj (e : G)).toMonoidHom = P := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, hpx⟩
    rw [← hpx]
    have hcomm : (p : G) * (e : G) = (e : G) * (p : G) :=
      (Subgroup.mem_centralizer_iff.mp (hEcentP e.2)) p hp
    have hc : (MulAut.conj (e : G)) (p : G) = (p : G) := by
      rw [MulAut.conj_apply]
      rw [← hcomm]
      simp
    change (MulAut.conj (e : G)) (p : G) ∈ P
    rwa [hc]
  · intro hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    have hcomm : (x : G) * (e : G) = (e : G) * (x : G) :=
      (Subgroup.mem_centralizer_iff.mp (hEcentP e.2)) x hx
    change (MulAut.conj (e : G)) (x : G) = (x : G)
    rw [MulAut.conj_apply]
    rw [← hcomm]
    simp

/-- The plane `P ⊔ P0` of two commuting prime-order subgroups is abelian. -/
private theorem sup_comm_of_commute {G : Type u} [Group G]
    {P P0 : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hP0comm : ∀ h : P, ∀ k : P0, (h : G) * (k : G) = (k : G) * (h : G)) :
    ∀ h : (P ⊔ P0 : Subgroup G), ∀ k : (P ⊔ P0 : Subgroup G),
      (h : G) * (k : G) = (k : G) * (h : G) := by
  classical
  have : IsCyclic (↥P) := isCyclic_of_prime_card (p := p) hPcard
  have : IsCyclic (↥P0) := isCyclic_of_prime_card (p := p) hP0card
  intro h k
  rcases mem_mul_of_mem_sup_of_commute (H := P) (K := P0) hP0comm h.2 with ⟨p1, q1, hpq1⟩
  rcases mem_mul_of_mem_sup_of_commute (H := P) (K := P0) hP0comm k.2 with ⟨p2, q2, hpq2⟩
  rw [← hpq1, ← hpq2]
  have hPcomm' : ∀ a b : P, a * b = b * a :=
    (isMulCommutative_iff (M := ↥P)).mp inferInstance
  have hP0comm' : ∀ a b : P0, a * b = b * a :=
    (isMulCommutative_iff (M := ↥P0)).mp inferInstance
  have hp : (p1 : G) * (p2 : G) = (p2 : G) * (p1 : G) := by
    change (↑(p1 * p2) : G) = (↑(p2 * p1) : G)
    exact congrArg (fun z : P => (z : G)) (hPcomm' p1 p2)
  have hq : (q1 : G) * (q2 : G) = (q2 : G) * (q1 : G) := by
    change (↑(q1 * q2) : G) = (↑(q2 * q1) : G)
    exact congrArg (fun z : P0 => (z : G)) (hP0comm' q1 q2)
  calc
    ((p1 : G) * (q1 : G)) * ((p2 : G) * (q2 : G)) =
        (p1 : G) * ((q1 : G) * (p2 : G)) * (q2 : G) := by group
    _ = (p1 : G) * ((p2 : G) * (q1 : G)) * (q2 : G) := by rw [← hP0comm p2 q1]
    _ = (p1 : G) * (p2 : G) * ((q1 : G) * (q2 : G)) := by group
    _ = (p2 : G) * (p1 : G) * ((q2 : G) * (q1 : G)) := by rw [hp, hq]
    _ = (p2 : G) * ((p1 : G) * (q2 : G)) * (q1 : G) := by group
    _ = (p2 : G) * ((q2 : G) * (p1 : G)) * (q1 : G) := by rw [hP0comm p1 q2]
    _ = (p2 : G) * (q2 : G) * ((p1 : G) * (q1 : G)) := by group

/-! ## 1. The families -/

/-- The ambient conjugacy family of a subgroup `P`: all `P^g`. -/
public abbrev secondCase_conjugatesOf (G : Type u) [Group G] (P : Subgroup G) : Type u :=
  {Y : Subgroup G // ∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom}

/-- The lines: ambient conjugates of `P` inside the plane `A = P ⊔ P0`
different from `P`. -/
public abbrev secondCase_linesIn (G : Type u) [Group G] (P P0 : Subgroup G) : Type u :=
  {X : Subgroup G // X ≤ P ⊔ P0 ∧ X ≠ P ∧ ∃ g : G, X = P.map (MulAut.conj g).toMonoidHom}

/-- The tori: the `E`-conjugates of the internal order-`p` subgroup
`P0 ≤ E`. -/
public abbrev secondCase_toriOf (G : Type u) [Group G] (P0 E : Subgroup G) : Type u :=
  {R : Subgroup G // ∃ e : E, R = P0.map (MulAut.conj (e : G)).toMonoidHom}

/-- The family: ambient conjugates of `P` inside `P ⊔ E` different from
`P`. -/
public abbrev secondCase_familyIn (G : Type u) [Group G] (P E : Subgroup G) : Type u :=
  {Y : Subgroup G // Y ≤ P ⊔ E ∧ Y ≠ P ∧ ∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom}

/-- For each torus `R`, the chosen `E`-conjugator with `P0^e = R`. -/
public noncomputable def secondCase_toriConjugator {G : Type u} [Group G]
    (P0 E : Subgroup G) (R : secondCase_toriOf G P0 E) : E :=
  Classical.choose R.2

/-- The pair map `(X, R) ↦ X^{e(R)}` with `e(R) ∈ E` the chosen
conjugator: conjugating the line `X ≤ P ⊔ P0` by `e(R)` fixes `P` and
sends `P0` to `R`. -/
@[expose] public noncomputable def secondCase_linearEquation11_familyMap
    {G : Type u} [Group G] (P P0 E : Subgroup G) :
    secondCase_linesIn G P P0 × secondCase_toriOf G P0 E → Subgroup G :=
  fun x => x.1.1.map (MulAut.conj ((secondCase_toriConjugator P0 E x.2 : E) : G)).toMonoidHom

private theorem familyMap_mem_family {G : Type u} [Group G]
    {P P0 E : Subgroup G} (hP0leE : P0 ≤ E)
    (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    (X : secondCase_linesIn G P P0) (R : secondCase_toriOf G P0 E) :
    (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X, R⟩) ≤ P ⊔ E ∧
    secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X, R⟩ ≠ P ∧
    ∃ g : G, secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X, R⟩ =
      P.map (MulAut.conj g).toMonoidHom := by
  classical
  let e : E := secondCase_toriConjugator P0 E R
  change X.1.map (MulAut.conj (e : G)).toMonoidHom ≤ P ⊔ E ∧
    X.1.map (MulAut.conj (e : G)).toMonoidHom ≠ P ∧
    ∃ g : G, X.1.map (MulAut.conj (e : G)).toMonoidHom = P.map (MulAut.conj g).toMonoidHom
  have hRe : R.1 = P0.map (MulAut.conj (e : G)).toMonoidHom := Classical.choose_spec R.2
  have hRleE : R.1 ≤ E := by
    rw [hRe]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p0, hp0, rfl⟩
    have hp0E : (p0 : G) ∈ E := hP0leE hp0
    have heE : (e : G) ∈ E := e.2
    exact Subgroup.mul_mem E (Subgroup.mul_mem E heE hp0E) (Subgroup.inv_mem E heE)
  constructor
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have haA : (a : G) ∈ P ⊔ P0 := X.2.1 ha
    have hxAE : (MulAut.conj (e : G)) (a : G) ∈
        (P ⊔ P0).map (MulAut.conj (e : G)).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, haA, rfl⟩
    have hAe : (P ⊔ P0).map (MulAut.conj (e : G)).toMonoidHom = P ⊔ R.1 := by
      rw [Subgroup.map_sup P P0 (MulAut.conj (e : G)).toMonoidHom]
      rw [conj_fix_of_mem_centralizer hEcentP e]
      rw [hRe]
    rw [hAe] at hxAE
    exact (sup_le (le_sup_left : P ≤ P ⊔ E) (hRleE.trans (le_sup_right : E ≤ P ⊔ E))) hxAE
  constructor
  · intro hY
    apply X.2.2.1
    have hback : (X.1.map (MulAut.conj (e : G)).toMonoidHom).map
        (MulAut.conj ((e : E)⁻¹ : G)).toMonoidHom = X.1 := by
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj ((e : E)⁻¹ : G)).toMonoidHom.comp
          (MulAut.conj (e : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp]
      simp
    calc
      X.1 = (X.1.map (MulAut.conj (e : G)).toMonoidHom).map
          (MulAut.conj ((e : E)⁻¹ : G)).toMonoidHom := hback.symm
      _ = P.map (MulAut.conj ((e : E)⁻¹ : G)).toMonoidHom := by rw [hY]
      _ = P := conj_fix_of_mem_centralizer hEcentP (e : E)⁻¹
  · rcases X.2.2.2 with ⟨g, hg⟩
    refine ⟨(e : G) * g, ?_⟩
    rw [hg]
    rw [Subgroup.map_map]
    exact congrArg (fun f : G →* G => P.map f) (by
      ext x
      simp [MulAut.conj_apply, mul_assoc])

/-! ## 2. The torus recovery and the injectivity of the pair map -/

/-- The torus is recovered from the image `Y = X^{e(R)}` as the
intersection `(Y ⊔ P) ∩ E = R`. -/
private theorem torus_recover_of_familyMap {G : Type u} [Group G] [Finite G]
    {P P0 E : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hP0interP : P ⊓ P0 = ⊥)
    (hP0leE : P0 ≤ E) (hPinterE : P ⊓ E = ⊥)
    (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    (hP0comm : ∀ h : P, ∀ k : P0, (h : G) * (k : G) = (k : G) * (h : G))
    (X : secondCase_linesIn G P P0) (R : secondCase_toriOf G P0 E) :
    (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X, R⟩ ⊔ P) ⊓ E = R.1 := by
  classical
  let e : E := secondCase_toriConjugator P0 E R
  change (X.1.map (MulAut.conj (e : G)).toMonoidHom ⊔ P) ⊓ E = R.1
  have hRe : R.1 = P0.map (MulAut.conj (e : G)).toMonoidHom := Classical.choose_spec R.2
  have hXcard : Nat.card X.1 = p := by
    rcases X.2.2.2 with ⟨g, hg⟩
    rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcard]
  have hXnotle : ¬ P ≤ X.1 := by
    intro hPleX
    apply X.2.2.1
    exact (Subgroup.eq_of_le_of_card_ge (H := P) (K := X.1) hPleX (by rw [hPcard, hXcard])).symm
  have hXinter : X.1 ⊓ P = ⊥ :=
    inf_eq_bot_of_not_le_of_prime_card (H := X.1) (P := P)
      (hPcard ▸ (Fact.out : p.Prime)) hXnotle
  have hAcomm : ∀ h : (P ⊔ P0 : Subgroup G), ∀ k : (P ⊔ P0 : Subgroup G),
      (h : G) * (k : G) = (k : G) * (h : G) :=
    sup_comm_of_commute hPcard hP0card hP0comm
  have hXcomm : ∀ h : X.1, ∀ k : P, (h : G) * (k : G) = (k : G) * (h : G) := by
    intro h k
    exact hAcomm ⟨(h : G), X.2.1 h.2⟩ ⟨(k : G), (le_sup_left : P ≤ P ⊔ P0) k.2⟩
  have hA : X.1 ⊔ P = P ⊔ P0 := by
    have hle : X.1 ⊔ P ≤ P ⊔ P0 := sup_le X.2.1 le_sup_left
    have hcX : Nat.card (X.1 ⊔ P : Subgroup G) = p * p := by
      rw [subgroup_card_sup_of_commute hXcomm (disjoint_iff.mpr hXinter)]
      rw [hXcard, hPcard]
    have hcA : Nat.card (P ⊔ P0 : Subgroup G) = p * p := by
      rw [subgroup_card_sup_of_commute hP0comm (disjoint_iff.mpr hP0interP)]
      rw [hPcard, hP0card]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcA, hcX])
  have hAsup : (X.1 ⊔ P).map (MulAut.conj (e : G)).toMonoidHom = P ⊔ R.1 := by
    rw [hA]
    rw [Subgroup.map_sup P P0 (MulAut.conj (e : G)).toMonoidHom]
    rw [conj_fix_of_mem_centralizer hEcentP e]
    rw [hRe]
  have hXsup : (X.1 ⊔ P).map (MulAut.conj (e : G)).toMonoidHom =
      X.1.map (MulAut.conj (e : G)).toMonoidHom ⊔ P := by
    rw [Subgroup.map_sup X.1 P (MulAut.conj (e : G)).toMonoidHom]
    rw [conj_fix_of_mem_centralizer hEcentP e]
  have hYsup : X.1.map (MulAut.conj (e : G)).toMonoidHom ⊔ P = P ⊔ R.1 := by
    rw [← hXsup, hAsup]
  have hRleE : R.1 ≤ E := by
    rw [hRe]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p0, hp0, rfl⟩
    have hp0E : (p0 : G) ∈ E := hP0leE hp0
    have heE : (e : G) ∈ E := e.2
    exact Subgroup.mul_mem E (Subgroup.mul_mem E heE hp0E) (Subgroup.inv_mem E heE)
  have hPRcomm : ∀ h : P, ∀ k : R.1, (h : G) * (k : G) = (k : G) * (h : G) := by
    intro h k
    have hkC : (k : G) ∈ Subgroup.centralizer (P : Set G) := hEcentP (hRleE k.2)
    exact (Subgroup.mem_centralizer_iff.mp hkC) (h : G) h.2
  have hinter : (P ⊔ R.1) ⊓ E = R.1 := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxPR, hxE⟩
      rcases mem_mul_of_mem_sup_of_commute (H := P) (K := R.1) hPRcomm hxPR with ⟨p, r, rfl⟩
      have hprE : (p : G) * (r : G) ∈ E := hxE
      have hrE : (r : G) ∈ E := hRleE r.2
      have hpE : (p : G) ∈ E := by
        have hstep : (p : G) = ((p : G) * (r : G)) * (r : G)⁻¹ := by group
        rw [hstep]
        exact Subgroup.mul_mem E hprE (Subgroup.inv_mem E hrE)
      have hp1 : (p : G) = 1 := by
        have hmem : (p : G) ∈ P ⊓ E := Subgroup.mem_inf.mpr ⟨p.2, hpE⟩
        have hmem' : (p : G) ∈ (⊥ : Subgroup G) := by simpa [hPinterE] using hmem
        exact Subgroup.mem_bot.mp hmem'
      simp [hp1]
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(le_sup_right : R.1 ≤ P ⊔ R.1) hx, hRleE hx⟩
  rw [hYsup]
  exact hinter

/-- The pair map `(X, R) ↦ X^{e(R)}` is injective: from the image the
torus is recovered by `R = (Y ⊔ P) ∩ E`, and then the line by
conjugating back by `e(R)⁻¹`. -/
public theorem secondCase_linearEquation11_familyMap_injective
    {G : Type u} [Group G] [Finite G]
    {P P0 E : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hP0interP : P ⊓ P0 = ⊥)
    (hP0leE : P0 ≤ E) (hPinterE : P ⊓ E = ⊥)
    (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    (hP0comm : ∀ h : P, ∀ k : P0, (h : G) * (k : G) = (k : G) * (h : G)) :
    Function.Injective (fun x : secondCase_linesIn G P P0 × secondCase_toriOf G P0 E =>
      secondCase_linearEquation11_familyMap (G := G) P P0 E x) := by
  classical
  intro a b hab
  rcases a with ⟨X1, R1⟩
  rcases b with ⟨X2, R2⟩
  let e1 : E := secondCase_toriConjugator P0 E R1
  let e2 : E := secondCase_toriConjugator P0 E R2
  have hR1 : R1.1 =
      (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X1, R1⟩ ⊔ P) ⊓ E :=
    (torus_recover_of_familyMap hPcard hP0card hP0interP hP0leE hPinterE hEcentP hP0comm X1 R1).symm
  have hR2 : R2.1 =
      (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X2, R2⟩ ⊔ P) ⊓ E :=
    (torus_recover_of_familyMap hPcard hP0card hP0interP hP0leE hPinterE hEcentP hP0comm X2 R2).symm
  have hR : R1 = R2 := by
    apply Subtype.ext
    calc
      R1.1 = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X1, R1⟩ ⊔ P) ⊓ E := hR1
      _ = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X2, R2⟩ ⊔ P) ⊓ E := by
            change secondCase_linearEquation11_familyMap (G := G) P P0 E (X1, R1) =
              secondCase_linearEquation11_familyMap (G := G) P P0 E (X2, R2) at hab
            rw [hab]
      _ = R2.1 := hR2.symm
  have he : e1 = e2 := by
    dsimp [e1, e2]
    rw [hR]
  have hY : secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X1, R1⟩ =
      secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X2, R2⟩ := by
    change secondCase_linearEquation11_familyMap (G := G) P P0 E (X1, R1) =
      secondCase_linearEquation11_familyMap (G := G) P P0 E (X2, R2) at hab
    exact hab
  have hback1 : X1.1 = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X1, R1⟩).map
      (MulAut.conj ((e1 : E)⁻¹ : G)).toMonoidHom := by
    change X1.1 = (X1.1.map (MulAut.conj (e1 : G)).toMonoidHom).map
        (MulAut.conj ((e1 : E)⁻¹ : G)).toMonoidHom
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj ((e1 : E)⁻¹ : G)).toMonoidHom.comp
        (MulAut.conj (e1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp]
    simp
  have hback2 : X2.1 = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X2, R2⟩).map
      (MulAut.conj ((e2 : E)⁻¹ : G)).toMonoidHom := by
    change X2.1 = (X2.1.map (MulAut.conj (e2 : G)).toMonoidHom).map
        (MulAut.conj ((e2 : E)⁻¹ : G)).toMonoidHom
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj ((e2 : E)⁻¹ : G)).toMonoidHom.comp
        (MulAut.conj (e2 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp]
    simp
  have hX : X1 = X2 := by
    apply Subtype.ext
    have heG : ((e1 : E)⁻¹ : G) = ((e2 : E)⁻¹ : G) := by rw [he]
    calc
      X1.1 = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X1, R1⟩).map
          (MulAut.conj ((e1 : E)⁻¹ : G)).toMonoidHom := hback1
      _ = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X2, R2⟩).map
          (MulAut.conj ((e1 : E)⁻¹ : G)).toMonoidHom := by rw [hY]
      _ = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨X2, R2⟩).map
          (MulAut.conj ((e2 : E)⁻¹ : G)).toMonoidHom := by rw [heG]
      _ = X2.1 := hback2.symm
  exact Prod.ext hX hR

/-! ## 3. The product-family count (equation (11)) -/

/-- The ambient region `P ⊔ E` contains at least `(p₁ - 1) · q · k'`
distinct conjugates of `P` different from `P`.

`τ : B → secondCase_toriOf G P0 E` is an injective family of internal
tori indexed by a type of cardinal `q · k'` (e.g. the quotient orbit of
the tori, lifting `E`-conjugators through `E → E/Z(E)`; distinct quotient
images give distinct actual conjugates, so no centerless or `p`-coprime
hypothesis is needed). -/
public theorem secondCase_linearEquation11_product_family_conjugate_card
    {G : Type u} [Group G] [Finite G]
    {P P0 E : Subgroup G} {p p1 q k' : ℕ} [Fact p.Prime]
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hP0interP : P ⊓ P0 = ⊥)
    (hP0leE : P0 ≤ E) (hPinterE : P ⊓ E = ⊥)
    (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    (hP0comm : ∀ h : P, ∀ k : P0, (h : G) * (k : G) = (k : G) * (h : G))
    (hLines : Nat.card (secondCase_linesIn G P P0) = p1 - 1)
    {B : Type u} [Finite B] (τ : B → secondCase_toriOf G P0 E) (hτ : Function.Injective τ)
    (hB : Nat.card B = q * k') :
    (p1 - 1) * q * k' ≤ Nat.card (secondCase_familyIn G P E) := by
  classical
  have : Finite (secondCase_linesIn G P P0) := by
    dsimp [secondCase_linesIn]
    infer_instance
  have : Finite (secondCase_familyIn G P E) := by
    dsimp [secondCase_familyIn]
    infer_instance
  let fm : secondCase_linesIn G P P0 × B → secondCase_familyIn G P E :=
    fun x => ⟨secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨x.1, τ x.2⟩,
      familyMap_mem_family (P := P) (P0 := P0) (E := E) hP0leE hEcentP x.1 (τ x.2)⟩
  have hfinj : Function.Injective fm := by
    intro a b hab
    have hfm : secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨a.1, τ a.2⟩ =
        secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨b.1, τ b.2⟩ :=
      congrArg Subtype.val hab
    have hR : τ a.2 = τ b.2 := by
      apply Subtype.ext
      have h1 : (τ a.2).1 =
          (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨a.1, τ a.2⟩ ⊔ P) ⊓ E :=
        (torus_recover_of_familyMap hPcard hP0card hP0interP hP0leE hPinterE hEcentP hP0comm
          a.1 (τ a.2)).symm
      have h2 : (τ b.2).1 =
          (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨b.1, τ b.2⟩ ⊔ P) ⊓ E :=
        (torus_recover_of_familyMap hPcard hP0card hP0interP hP0leE hPinterE hEcentP hP0comm
          b.1 (τ b.2)).symm
      calc
        (τ a.2).1 = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨a.1, τ a.2⟩ ⊔ P) ⊓ E := h1
        _ = (secondCase_linearEquation11_familyMap (G := G) P P0 E ⟨b.1, τ b.2⟩ ⊔ P) ⊓ E := by
              rw [hfm]
        _ = (τ b.2).1 := h2.symm
    have hb : a.2 = b.2 := hτ hR
    have hX : a.1 = b.1 := by
      have hinj' := secondCase_linearEquation11_familyMap_injective (G := G) (P := P) (P0 := P0)
        (E := E) (p := p) hPcard hP0card hP0interP hP0leE hPinterE hEcentP hP0comm
      have hpair : (a.1, τ a.2) = (b.1, τ b.2) := hinj' hfm
      simpa using (congrArg Prod.fst hpair)
    exact Prod.ext hX hb
  have hcard : Nat.card (secondCase_linesIn G P P0) * Nat.card B ≤
      Nat.card (secondCase_familyIn G P E) := by
    simpa [Nat.card_prod] using Nat.card_le_card_of_injective fm hfinj
  simpa [hLines, hB, Nat.mul_assoc] using hcard

/-- The convenience form with the exact torus-orbit count
`q · k'` (e.g. from `secondCase_linearEquation11_orbit_card_of_component`):
then `P ⊔ E` contains at least `(p₁ - 1) · q · k'` conjugates of `P`. -/
public theorem secondCase_linearEquation11_product_family_conjugate_card_of_tori
    {G : Type u} [Group G] [Finite G]
    {P P0 E : Subgroup G} {p p1 q k' : ℕ} [Fact p.Prime]
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hP0interP : P ⊓ P0 = ⊥)
    (hP0leE : P0 ≤ E) (hPinterE : P ⊓ E = ⊥)
    (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    (hP0comm : ∀ h : P, ∀ k : P0, (h : G) * (k : G) = (k : G) * (h : G))
    (hLines : Nat.card (secondCase_linesIn G P P0) = p1 - 1)
    (hTori : Nat.card (secondCase_toriOf G P0 E) = q * k') :
    (p1 - 1) * q * k' ≤ Nat.card (secondCase_familyIn G P E) := by
  classical
  have : Finite (secondCase_toriOf G P0 E) := by
    dsimp [secondCase_toriOf]
    infer_instance
  exact secondCase_linearEquation11_product_family_conjugate_card
    (G := G) (P := P) (P0 := P0) (E := E) (p := p) (p1 := p1) (q := q) (k' := k')
    hPcard hP0card hP0interP hP0leE hPinterE hEcentP hP0comm hLines
    (B := secondCase_toriOf G P0 E) (fun R => R)
    (by intro a b h; exact h) hTori

end CFSG.GorensteinWalter
