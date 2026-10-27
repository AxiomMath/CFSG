module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingFixedPartCardDvd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: shared data and infrastructure for the linear equation-(8)

This module owns the shared vocabulary of the linear equation-(8) package
(`refs/bender-dihedral-sylow.tex`, lines 708--735):

* the parameter definitions `normalizerIn` (`N_U(H)`), `IsConjugateSubgroup`
  and `conjugateCount` (the paper's `p1` convention);
* the generic group-theoretic helpers: conjugation of subgroups by coset
  representatives, prime-order subgroups fixed by normalizers of cyclic
  subgroups, and the `p + 1` counting lemmas behind `p1 ≤ p + 1` and the
  strict-branch `u ≤ p + 1`;
* the shared data structure `SecondCaseLinearOmegaData` carrying the
  equation-(1)--(7) package, the choices `P`, `P0`, `A = P ⊔ P0`, and the
  omega subgroup `Q` (with the `Ω₁(Z₂(O_p(U)))` upper-central-series
  containment, non-cyclicity, exponent `p`, and characteristicity);
* the derived identities `F ⊓ K0 = ⊥`, `p` odd, `Q ≤ F(U)`,
  `N_U(P) = U ∩ M` and `N_U(P) ≤ N_U(A)`.

The per-branch modules (`SecondCaseLinearOmegaTrichotomy`,
`SecondCaseLinearOmegaEqualityIndex`, `SecondCaseLinearOmegaStrictIndex`,
`SecondCaseLinearOmegaInversionEndpoint`) consume `SecondCaseLinearOmegaData`
and prove the trichotomy and the equation-(8) consequences; the owner module
`SecondCaseLinearEquationEight` assembles the final structure.
-/

noncomputable section

open scoped Finset

namespace CFSG.GorensteinWalter

universe u

/-! ## Parameter definitions -/

/-- The normalizer of `H` inside `U`, as an ambient subgroup. -/
@[expose] public def normalizerIn {G : Type u} [Group G]
    (U H : Subgroup G) : Subgroup G :=
  U ⊓ Subgroup.normalizer (H : Set G)

/-- `X` is a conjugate of `P` in the ambient group. -/
@[expose] public def IsConjugateSubgroup {G : Type u} [Group G]
    (P X : Subgroup G) : Prop :=
  ∃ g : G, conjugateSubgroup P g = X

/-- The number of `G`-conjugates of `P` contained in `A`. -/
@[expose] public def conjugateCount {G : Type u} [Group G]
    (P A : Subgroup G) : ℕ :=
  Nat.card {X : Subgroup G // X ≤ A ∧ IsConjugateSubgroup P X}

/-! ## Generic group-theoretic helpers -/

/-- Finite sets with equal cardinality and one contained in the other are
equal. -/
private lemma set_eq_of_subset_of_card_eq {α : Type u} [Finite α]
    {A B : Set α} (hAB : A ⊆ B)
    (hcard : Nat.card {x : α // x ∈ A} = Nat.card {x : α // x ∈ B}) :
    A = B := by
  classical
  have hA : A.ncard = B.ncard := by
    rw [Set.ncard_def, Set.ncard_def]
    exact hcard
  exact Set.eq_of_subset_of_ncard_le hAB (le_of_eq hA.symm)

/-- Conjugating `P` by `a` and by `b` gives the same subgroup whenever
`a⁻¹b` normalizes `P`. -/
public theorem conjugate_subgroup_eq_of_left_inv_mem_normalizer
    {G : Type u} [Group G] {P : Subgroup G} {a b : G}
    (hab : a⁻¹ * b ∈ Subgroup.normalizer (P : Set G)) :
    conjugateSubgroup P a = conjugateSubgroup P b := by
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hba : b⁻¹ * a ∈ Subgroup.normalizer (P : Set G) := by
      simpa using ((Subgroup.normalizer (P : Set G)).inv_mem hab)
    have hq : b⁻¹ * a * p * a⁻¹ * b ∈ P := by
      have hp' : b⁻¹ * a * p * a⁻¹ * b = (b⁻¹ * a) * p * (b⁻¹ * a)⁻¹ := by group
      rw [hp']
      exact (Subgroup.mem_normalizer_iff.mp hba p).1 hp
    exact Subgroup.mem_map.mpr ⟨b⁻¹ * a * p * a⁻¹ * b, hq, by
      simp [MulAut.conj_apply]
      group⟩
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hq : a⁻¹ * b * p * b⁻¹ * a ∈ P := by
      have hp' : a⁻¹ * b * p * b⁻¹ * a = (a⁻¹ * b) * p * (a⁻¹ * b)⁻¹ := by group
      rw [hp']
      exact (Subgroup.mem_normalizer_iff.mp hab p).1 hp
    exact Subgroup.mem_map.mpr ⟨a⁻¹ * b * p * b⁻¹ * a, hq, by
      simp [MulAut.conj_apply]
      group⟩

/-- If conjugating `P` by `a` and by `b` agrees, then `a⁻¹b` normalizes
`P`. -/
public theorem left_inv_mem_normalizer_of_conjugate_subgroup_eq
    {G : Type u} [Group G] {P : Subgroup G} {a b : G}
    (hab : conjugateSubgroup P a = conjugateSubgroup P b) :
    a⁻¹ * b ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hbxb : b * x * b⁻¹ ∈ conjugateSubgroup P b :=
      Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hx
    have hbxa : b * x * b⁻¹ ∈ conjugateSubgroup P a := by rwa [hab]
    rcases Subgroup.mem_map.mp hbxa with ⟨p, hp, hEq'⟩
    have hqeq : a⁻¹ * b * x * b⁻¹ * a = p := by
      calc
        a⁻¹ * b * x * b⁻¹ * a = a⁻¹ * (b * x * b⁻¹) * a := by group
        _ = a⁻¹ * (a * p * a⁻¹) * a := by
          rw [← hEq']
          simp [MulAut.conj_apply]
        _ = p := by group
    have hx' : a⁻¹ * b * x * (a⁻¹ * b)⁻¹ = a⁻¹ * b * x * b⁻¹ * a := by group
    rw [hx', hqeq]
    exact hp
  · intro hxconj
    have hfwd_ba : ∀ y : G, y ∈ P → b⁻¹ * a * y * a⁻¹ * b ∈ P := by
      intro y hy
      have haya : a * y * a⁻¹ ∈ conjugateSubgroup P a :=
        Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hy
      have hayb : a * y * a⁻¹ ∈ conjugateSubgroup P b := by rwa [← hab]
      rcases Subgroup.mem_map.mp hayb with ⟨p, hp, hEq'⟩
      have hqeq : b⁻¹ * a * y * a⁻¹ * b = p := by
        calc
          b⁻¹ * a * y * a⁻¹ * b = b⁻¹ * (a * y * a⁻¹) * b := by group
          _ = b⁻¹ * (b * p * b⁻¹) * b := by
            rw [← hEq']
            simp [MulAut.conj_apply]
          _ = p := by group
      rwa [← hqeq] at hp
    have hxconj' : a⁻¹ * b * x * b⁻¹ * a ∈ P := by
      have hxeq' : a⁻¹ * b * x * b⁻¹ * a = a⁻¹ * b * x * (a⁻¹ * b)⁻¹ := by group
      rwa [← hxeq'] at hxconj
    have hxP : b⁻¹ * a * (a⁻¹ * b * x * b⁻¹ * a) * a⁻¹ * b ∈ P :=
      hfwd_ba (a⁻¹ * b * x * b⁻¹ * a) hxconj'
    have hxeq : b⁻¹ * a * (a⁻¹ * b * x * b⁻¹ * a) * a⁻¹ * b = x := by group
    rwa [hxeq] at hxP

/-- A prime-order subgroup of a cyclic subgroup is fixed by every element
normalizing the cyclic subgroup. -/
public theorem prime_order_subgroup_fixed_by_normalizer_of_cyclic
    {G : Type u} [Group G] [Finite G]
    {C P : Subgroup G} (hCcyc : IsCyclic C) (hPleC : P ≤ C)
    {p : ℕ} (hp : p.Prime) (hPcard : Nat.card P = p)
    {u : G} (huC : u ∈ Subgroup.normalizer (C : Set G)) :
    u ∈ Subgroup.normalizer (P : Set G) := by
  classical
  let S : Set G := {x : G | x ∈ C ∧ x ^ p = 1}
  have hp_pos : 0 < p := hp.pos
  have hPsubS : (P : Set G) ⊆ S := by
    intro x hx
    exact ⟨hPleC hx,
      (orderOf_dvd_iff_pow_eq_one (x := x) (n := p)).mp (by
        simpa [hPcard] using (Subgroup.orderOf_dvd_natCard P hx))⟩
  have hScard : Nat.card {x : G // x ∈ S} = p := by
    classical
    let : Fintype ↥C := Fintype.ofFinite _
    let : Fintype {x : G // x ∈ S} := Fintype.ofFinite _
    let : Fintype {a : ↥C // a ^ p = 1} := Fintype.ofFinite _
    apply le_antisymm
    · let e : {x : G // x ∈ S} ≃ {a : ↥C // a ^ p = 1} :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            apply Subtype.ext
            have hpow : ((⟨x.1, x.2.1⟩ ^ p : ↥C) : G) = x.1 ^ p := by
              simpa using (map_pow (C.subtype) (⟨x.1, x.2.1⟩ : ↥C) p)
            simpa [hpow] using x.2.2⟩
          invFun := fun a => ⟨(a.1 : G), ⟨a.1.2, by
            have hpow : ((a.1 ^ p : ↥C) : G) = (a.1 : G) ^ p := by
              simpa using (map_pow (C.subtype) a.1 p)
            have h1 : ((a.1 ^ p : ↥C) : G) = 1 := by
              simpa using congrArg (fun z : ↥C => (z : G)) a.2
            rw [← hpow]
            exact h1⟩⟩
          left_inv := by
            intro x
            apply Subtype.ext
            rfl
          right_inv := by
            intro a
            apply Subtype.ext
            rfl }
      calc
        Nat.card {x : G // x ∈ S} = Nat.card {a : ↥C // a ^ p = 1} :=
          Nat.card_congr e
        _ ≤ p := by
          simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using
            (IsCyclic.card_pow_eq_one_le (α := ↥C) (n := p) hp_pos)
    · have hle : Nat.card P ≤ Nat.card {x : G // x ∈ S} :=
        Nat.card_le_card_of_injective (fun x : P => ⟨(x : G), hPsubS x.2⟩) (by
          intro a b h
          exact Subtype.ext (congrArg (fun z : {x : G // x ∈ S} => (z : G)) h))
      simpa [hPcard] using hle
  have hP_eq_S : (P : Set G) = S := by
    have hcard : Nat.card {x : G // x ∈ (P : Set G)} = Nat.card {x : G // x ∈ S} := by
      calc
        Nat.card {x : G // x ∈ (P : Set G)} = Nat.card P := rfl
        _ = p := hPcard
        _ = Nat.card {x : G // x ∈ S} := hScard.symm
    exact set_eq_of_subset_of_card_eq hPsubS hcard
  have hconj_pow (v x : G) : (v * x * v⁻¹) ^ p = v * (x ^ p) * v⁻¹ := by
    calc
      (v * x * v⁻¹) ^ p = (MulAut.conj v) (x ^ p) := by
        simpa [MulAut.conj_apply] using (map_pow (MulAut.conj v).toMonoidHom x p)
      _ = v * (x ^ p) * v⁻¹ := by rfl
  have hSinv (v : G) (hv : v ∈ Subgroup.normalizer (C : Set G)) :
      ∀ x : G, x ∈ S → v * x * v⁻¹ ∈ S := by
    intro x hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp hv x).1 hx.1,
      by calc
        (v * x * v⁻¹) ^ p = v * (x ^ p) * v⁻¹ := hconj_pow v x
        _ = v * 1 * v⁻¹ := by rw [hx.2]
        _ = 1 := by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxS : x ∈ S := by
      rw [← hP_eq_S]
      exact hx
    have huxS : u * x * u⁻¹ ∈ S := hSinv u huC x hxS
    change u * x * u⁻¹ ∈ (P : Set G)
    rw [hP_eq_S]
    exact huxS
  · intro hux
    have huxS : u * x * u⁻¹ ∈ S := by
      rw [← hP_eq_S]
      exact hux
    have hxS : x ∈ S := by
      have hux' : u⁻¹ * (u * x * u⁻¹) * u ∈ S := by
        simpa using hSinv u⁻¹ ((Subgroup.normalizer (C : Set G)).inv_mem huC) (u * x * u⁻¹) huxS
      have hx' : u⁻¹ * (u * x * u⁻¹) * u = x := by group
      rwa [hx'] at hux'
    change x ∈ (P : Set G)
    rw [hP_eq_S]
    exact hxS

/-- In a finite group of order `p^2` and exponent `p`, the number of
subgroups of order `p` is `p + 1`. -/
public theorem order_p_subgroups_card_of_order_p_sq_exponent_p
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card Q = p ^ 2) (hexp : Monoid.exponent Q = p) :
    Nat.card {X : Subgroup Q // Nat.card X = p} = p + 1 := by
  classical
  let S : Type u := {X : Subgroup Q // Nat.card X = p}
  let A : Type u := {x : Q // x ≠ 1}
  have hord (x : Q) (hx : x ≠ 1) : orderOf x = p := by
    exact orderOf_eq_prime (x := x) (p := p)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [hexp]) x) hx
  have hAcard : Nat.card A = p ^ 2 - 1 := by
    let e : (Option A) ≃ Q :=
      { toFun := fun s => match s with
          | none => 1
          | some x => x.1
        invFun := fun x => if h : x = 1 then none else some ⟨x, h⟩
        left_inv := by
          intro s
          cases s with
          | none => simp
          | some x => simp [x.2]
        right_inv := by
          intro x
          by_cases h : x = 1
          · simp [h]
          · simp [h] }
    have hsum : Nat.card (Option A) = Nat.card A + 1 := by
      simp
    have hsum' : Nat.card A + 1 = p ^ 2 := by
      calc
        Nat.card A + 1 = Nat.card (Option A) := hsum.symm
        _ = Nat.card Q := Nat.card_congr e
        _ = p ^ 2 := hcard
    omega
  let f : A → S := fun x => ⟨Subgroup.zpowers (x : Q), by
    rw [Nat.card_zpowers]
    exact hord (x : Q) x.2⟩
  have hfib (X : S) : Nat.card {x : A // f x = X} = p - 1 := by
    let e : {x : A // f x = X} ≃ {x : Q // x ∈ (X : Subgroup Q) ∧ x ≠ 1} :=
      { toFun := fun x => ⟨x.1.1, by
            refine ⟨?_, x.1.2⟩
            have hfx : Subgroup.zpowers (x.1.1) = X := by
              simpa [f] using congrArg Subtype.val x.2
            rw [← hfx]
            exact Subgroup.mem_zpowers (x.1.1)⟩
        invFun := fun x => ⟨⟨(x.1 : Q), x.2.2⟩, by
            apply Subtype.ext
            have hxX : (x.1 : Q) ∈ (X : Subgroup Q) := x.2.1
            have hle : Subgroup.zpowers (x.1 : Q) ≤ X := Subgroup.zpowers_le.mpr hxX
            have hcardz : Nat.card (Subgroup.zpowers (x.1 : Q)) = p := by
              rw [Nat.card_zpowers]
              exact hord (x.1 : Q) x.2.2
            exact Subgroup.eq_of_le_of_card_ge hle (by rw [X.2, hcardz])⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro x
          apply Subtype.ext
          rfl }
    have hX1 : Nat.card {x : Q // x ∈ (X : Subgroup Q) ∧ x ≠ 1} + 1 = p := by
      let e2 : Option {x : Q // x ∈ (X : Subgroup Q) ∧ x ≠ 1} ≃ ↥(X : Subgroup Q) :=
        { toFun := fun s => match s with
            | none => 1
            | some x => ⟨x.1, x.2.1⟩
          invFun := fun x => if h : (x.1 : Q) = 1 then none else
            some ⟨x.1, ⟨x.2, h⟩⟩
          left_inv := by
            intro s
            cases s with
            | none => simp
            | some x => simp [x.2.2]
          right_inv := by
            intro x
            by_cases h : (x.1 : Q) = 1
            · simpa [h] using (Subtype.ext h.symm)
            · simp [h] }
      have hsum : Nat.card (Option {x : Q // x ∈ (X : Subgroup Q) ∧ x ≠ 1}) =
          Nat.card {x : Q // x ∈ (X : Subgroup Q) ∧ x ≠ 1} + 1 := by
        simp
      calc
        Nat.card {x : Q // x ∈ (X : Subgroup Q) ∧ x ≠ 1} + 1 =
            Nat.card (Option {x : Q // x ∈ (X : Subgroup Q) ∧ x ≠ 1}) := hsum.symm
        _ = Nat.card (↥(X : Subgroup Q)) := Nat.card_congr e2
        _ = p := X.2
    calc
      Nat.card {x : A // f x = X} = Nat.card {x : Q // x ∈ (X : Subgroup Q) ∧ x ≠ 1} :=
        Nat.card_congr e
      _ = p - 1 := by omega
  have hmain : Nat.card (Σ X : S, {x : A // f x = X}) = Nat.card S * (p - 1) := by
    classical
    let : Fintype S := Fintype.ofFinite _
    rw [Nat.card_sigma (α := S) (β := fun X => {x : A // f x = X})]
    calc
      (∑ X : S, Nat.card {x : A // f x = X}) = (∑ X : S, (p - 1)) := by
        refine Finset.sum_congr rfl ?_
        intro X hX
        exact hfib X
      _ = Nat.card S * (p - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card]
        simpa [Finset.card_univ]
  have hbij : Nat.card (Σ X : S, {x : A // f x = X}) = Nat.card A := by
    let e : (Σ X : S, {x : A // f x = X}) ≃ A :=
      { toFun := fun z => ⟨z.2.1.1, z.2.1.2⟩
        invFun := fun x => ⟨f x, ⟨x, rfl⟩⟩
        left_inv := by
          intro z
          rcases z with ⟨X, x, hx⟩
          subst hx
          simp
        right_inv := by
          intro x
          rfl }
    exact Nat.card_congr e
  have hmul : Nat.card S * (p - 1) = p ^ 2 - 1 := by
    rw [← hmain, hbij, hAcard]
  have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    rw [← Nat.sq_sub_sq p 1]
  have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 0 < p - 1 := by omega
  have hmul' : Nat.card S * (p - 1) = (p + 1) * (p - 1) := by
    rw [hmul, hsq]
  simpa [S] using (Nat.eq_of_mul_eq_mul_right hp1 hmul')

/-- If `U` normalizes an extraspecial-order group `Q` and `A` is a
type-`(p,p)` subgroup of `Q` containing its center, then the number of
`U`-conjugates of `A` (the index `|U : N_U(A)|`) is at most `p + 1`. -/
public theorem conjugate_orbit_le_p_add_one
    {G : Type u} [Group G] [Finite G]
    {U Q A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hAQ : A ≤ Q) (hQnormalU : IsNormalIn Q U)
    (hAcard : Nat.card A = p ^ 2) (hQcard : Nat.card Q = p ^ 3)
    (hZcard : Nat.card ((Subgroup.center Q).map Q.subtype) = p)
    (hAZ : (Subgroup.center Q).map Q.subtype ≤ A) :
    (normalizerIn U A).relIndex U ≤ p + 1 := by
  classical
  let ZQ : Subgroup G := (Subgroup.center Q).map Q.subtype
  let C : Type u := ↥U ⧸ ((normalizerIn U A).subgroupOf U)
  have hQpg : IsPGroup p (↥Q) := by
    exact IsPGroup.of_card (n := 3) hQcard
  have hUleNQ : U ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_of_isNormalIn hQnormalU
  have hAconj (u : ↥U) : conjugateSubgroup A (u : G) ≤ Q := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hUleNQ u.2) a).1 (hAQ ha)
  have hZQ_fwd (v : ↥U) : ∀ x : G, x ∈ ZQ → v * x * v⁻¹ ∈ ZQ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    have hconj_mem : (v : G) * (z : G) * (v : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hUleNQ v.2) (z : G)).1 (z : ↥Q).2
    have hconj_center : (⟨(v : G) * (z : G) * (v : G)⁻¹, hconj_mem⟩ : ↥Q) ∈
        Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hback : (v : G)⁻¹ * (w : G) * (v : G) ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hUleNQ v.2) ((v : G)⁻¹ * (w : G) * (v : G))).2 (by
          have hw' : (v : G) * ((v : G)⁻¹ * (w : G) * (v : G)) * (v : G)⁻¹ = (w : G) := by group
          simpa [hw'] using w.2)
      have hc_comm : (z : G) * ((v : G)⁻¹ * (w : G) * (v : G)) =
          ((v : G)⁻¹ * (w : G) * (v : G)) * (z : G) := by
        have h := Subgroup.mem_center_iff.mp hz
          (⟨(v : G)⁻¹ * (w : G) * (v : G), hback⟩ : ↥Q)
        exact (congrArg Subtype.val h).symm
      apply Subtype.ext
      change (w : G) * ((v : G) * (z : G) * (v : G)⁻¹) =
        ((v : G) * (z : G) * (v : G)⁻¹) * (w : G)
      calc
        (w : G) * ((v : G) * (z : G) * (v : G)⁻¹) =
            (v : G) * (((v : G)⁻¹ * (w : G) * (v : G)) * (z : G)) * (v : G)⁻¹ := by group
        _ = (v : G) * ((z : G) * ((v : G)⁻¹ * (w : G) * (v : G))) * (v : G)⁻¹ := by
          rw [← hc_comm]
        _ = ((v : G) * (z : G) * (v : G)⁻¹) * (w : G) := by group
    exact Subgroup.mem_map.mpr
      ⟨⟨(v : G) * (z : G) * (v : G)⁻¹, hconj_mem⟩, hconj_center, rfl⟩
  have hZQconj (u : ↥U) : conjugateSubgroup ZQ (u : G) = ZQ := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      exact hZQ_fwd u (z : G) hz
    · intro x hx
      have hx' : u⁻¹ * x * u ∈ ZQ := by
        simpa using hZQ_fwd u⁻¹ x hx
      exact Subgroup.mem_map.mpr ⟨u⁻¹ * x * u, hx', by
        simp [MulAut.conj_apply]
        group⟩
  let f : C → {X : Subgroup G // X ≤ Q ∧ Nat.card X = p ^ 2} :=
    Quotient.lift (s := QuotientGroup.leftRel ((normalizerIn U A).subgroupOf U))
      (fun u : ↥U => ⟨conjugateSubgroup A (u : G), ⟨hAconj u, by
        calc
          Nat.card (conjugateSubgroup A (u : G)) = Nat.card A := by
            exact (Nat.card_congr (Subgroup.equivMapOfInjective A
              (MulAut.conj (u : G)).toMonoidHom (MulAut.conj (u : G)).injective).toEquiv).symm
          _ = p ^ 2 := hAcard⟩⟩)
      (by
        intro a b hab
        apply Subtype.ext
        exact conjugate_subgroup_eq_of_left_inv_mem_normalizer (P := A) (a := (a : G)) (b := (b : G)) (by
          exact (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)).2))
  have hf_inj : Function.Injective f := by
    intro c₁ c₂ hc
    revert hc
    refine Quotient.inductionOn₂ c₁ c₂ ?_
    intro a b hf
    have hEq : conjugateSubgroup A (a : G) = conjugateSubgroup A (b : G) := by
      simpa [f] using
        (congrArg (fun z : {X : Subgroup G // X ≤ Q ∧ Nat.card X = p ^ 2} => z.1) hf)
    have habN : (a : G)⁻¹ * (b : G) ∈ normalizerIn U A := by
      refine ⟨U.mul_mem (U.inv_mem a.2) b.2, ?_⟩
      exact left_inv_mem_normalizer_of_conjugate_subgroup_eq (P := A) (a := (a : G)) (b := (b : G)) hEq
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (Subgroup.mem_subgroupOf.mpr habN))
  have hpair_fact (c₁ c₂ : C) (hne : c₁ ≠ c₂) :
      (f c₁).1 ⊓ (f c₂).1 = ZQ := by
    revert hne
    refine Quotient.inductionOn₂ c₁ c₂ ?_
    intro a b hab
    have hdist : (a : G)⁻¹ * (b : G) ∉ normalizerIn U A := by
      intro hmem
      have hrel : QuotientGroup.leftRel ((normalizerIn U A).subgroupOf U) a b :=
        QuotientGroup.leftRel_apply.mpr (Subgroup.mem_subgroupOf.mpr hmem)
      exact (hab (Quotient.sound hrel))
    have hconj_ne : conjugateSubgroup A (a : G) ≠ conjugateSubgroup A (b : G) := by
      intro heq
      have hN : (a : G)⁻¹ * (b : G) ∈ Subgroup.normalizer (A : Set G) :=
        left_inv_mem_normalizer_of_conjugate_subgroup_eq (P := A) (a := (a : G)) (b := (b : G)) heq
      exact hdist ⟨U.mul_mem (U.inv_mem a.2) b.2, hN⟩
    let A1 : Subgroup G := conjugateSubgroup A (a : G)
    let A2 : Subgroup G := conjugateSubgroup A (b : G)
    have hZle1 : ZQ ≤ A1 := by
      have hZconj : conjugateSubgroup ZQ (a : G) = ZQ := hZQconj a
      have hle : conjugateSubgroup ZQ (a : G) ≤ conjugateSubgroup A (a : G) :=
        Subgroup.map_mono hAZ
      rwa [hZconj] at hle
    have hZle2 : ZQ ≤ A2 := by
      have hZconj : conjugateSubgroup ZQ (b : G) = ZQ := hZQconj b
      have hle : conjugateSubgroup ZQ (b : G) ≤ conjugateSubgroup A (b : G) :=
        Subgroup.map_mono hAZ
      rwa [hZconj] at hle
    have hA1card : Nat.card A1 = p ^ 2 := by
      calc
        Nat.card A1 = Nat.card A := by
          exact (Nat.card_congr (Subgroup.equivMapOfInjective A
            (MulAut.conj (a : G)).toMonoidHom (MulAut.conj (a : G)).injective).toEquiv).symm
        _ = p ^ 2 := hAcard
    have hA2card : Nat.card A2 = p ^ 2 := by
      calc
        Nat.card A2 = Nat.card A := by
          exact (Nat.card_congr (Subgroup.equivMapOfInjective A
            (MulAut.conj (b : G)).toMonoidHom (MulAut.conj (b : G)).injective).toEquiv).symm
        _ = p ^ 2 := hAcard
    have hcap : Nat.card (A1 ⊓ A2 : Subgroup G) = p := by
      have hcap_ge : p ≤ Nat.card (A1 ⊓ A2 : Subgroup G) := by
        calc
          p = Nat.card ZQ := by simpa [ZQ] using hZcard.symm
          _ ≤ Nat.card (A1 ⊓ A2 : Subgroup G) :=
            Subgroup.card_le_of_le (le_inf hZle1 hZle2)
      have hcap_ne : Nat.card (A1 ⊓ A2 : Subgroup G) ≠ p ^ 2 := by
        intro hcap2
        have h_eq : A1 ⊓ A2 = A1 :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcap2, hA1card])
        have hle12 : A1 ≤ A2 := by
          rw [← h_eq]
          exact inf_le_right
        exact hconj_ne
          (Subgroup.eq_of_le_of_card_ge hle12 (by rw [hA1card, hA2card]))
      have hdvd : Nat.card (A1 ⊓ A2 : Subgroup G) ∣ p ^ 2 := by
        rw [← hA1card]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨n, hnle, hn⟩ :=
        (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
      have hncases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hncases with rfl | rfl | rfl
      · rw [hn, pow_zero] at hcap_ge
        have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
        omega
      · simpa using hn
      · exact (hcap_ne (by simpa using hn)).elim
    have hEq : ZQ = A1 ⊓ A2 :=
      Subgroup.eq_of_le_of_card_ge (le_inf hZle1 hZle2) (by rw [hcap, hZcard])
    simpa [f, A1, A2] using hEq.symm
  have hnotZ : Nat.card {x : ↥Q // (x : G) ∉ ZQ} = p ^ 3 - p := by
    have hZleQ : ZQ ≤ Q := hAZ.trans hAQ
    let eZ : {x : ↥Q // (x : G) ∈ ZQ} ≃ ↥ZQ :=
      { toFun := fun x => ⟨(x : G), x.2⟩
        invFun := fun x => ⟨⟨(x : G), hZleQ x.2⟩, x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have hcard1 : Nat.card {x : ↥Q // (x : G) ∈ ZQ} = p := by
      calc
        Nat.card {x : ↥Q // (x : G) ∈ ZQ} = Nat.card (↥ZQ) := Nat.card_congr eZ
        _ = p := hZcard
    let e : ({x : ↥Q // (x : G) ∈ ZQ} ⊕ {x : ↥Q // (x : G) ∉ ZQ}) ≃ ↥Q :=
      { toFun := fun s => match s with
          | Sum.inl x => x.1
          | Sum.inr x => x.1
        invFun := fun x => if h : (x : G) ∈ ZQ then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, h⟩
        left_inv := by
          intro s
          cases s with
          | inl x => simp [x.2]
          | inr x => simp [x.2]
        right_inv := by
          intro x
          by_cases h : (x : G) ∈ ZQ
          · simp [h]
          · simp [h] }
    have hsum : Nat.card ({x : ↥Q // (x : G) ∈ ZQ} ⊕ {x : ↥Q // (x : G) ∉ ZQ}) =
        Nat.card {x : ↥Q // (x : G) ∈ ZQ} + Nat.card {x : ↥Q // (x : G) ∉ ZQ} := by
      rw [Nat.card_sum]
    have hsum' : Nat.card {x : ↥Q // (x : G) ∉ ZQ} + p = p ^ 3 := by
      calc
        Nat.card {x : ↥Q // (x : G) ∉ ZQ} + p =
            Nat.card {x : ↥Q // (x : G) ∈ ZQ} + Nat.card {x : ↥Q // (x : G) ∉ ZQ} := by
          rw [hcard1, Nat.add_comm]
        _ = Nat.card ({x : ↥Q // (x : G) ∈ ZQ} ⊕ {x : ↥Q // (x : G) ∉ ZQ}) := hsum.symm
        _ = Nat.card (↥Q) := Nat.card_congr e
        _ = p ^ 3 := hQcard
    omega
  let fiber : C → Type u := fun c => {x : ↥Q // (x : G) ∈ (f c).1 ∧ (x : G) ∉ ZQ}
  have hfib (c : C) : Nat.card (fiber c) = p ^ 2 - p := by
    refine Quotient.inductionOn c ?_
    intro u
    change Nat.card {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G) ∧ (x : G) ∉ ZQ} =
      p ^ 2 - p
    have hZle : ZQ ≤ conjugateSubgroup A (u : G) := by
      have hZconj : conjugateSubgroup ZQ (u : G) = ZQ := hZQconj u
      have hle : conjugateSubgroup ZQ (u : G) ≤ conjugateSubgroup A (u : G) :=
        Subgroup.map_mono hAZ
      rwa [hZconj] at hle
    have hAuQ : conjugateSubgroup A (u : G) ≤ Q := hAconj u
    let eA : {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G)} ≃
        ↥(conjugateSubgroup A (u : G)) :=
      { toFun := fun x => ⟨(x : G), x.2⟩
        invFun := fun x => ⟨⟨(x : G), hAuQ x.2⟩, x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have hcardAu : Nat.card {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G)} = p ^ 2 := by
      calc
        Nat.card {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G)} =
            Nat.card (↥(conjugateSubgroup A (u : G))) := Nat.card_congr eA
        _ = p ^ 2 := by
          calc
            Nat.card (↥(conjugateSubgroup A (u : G))) = Nat.card A := by
              exact (Nat.card_congr (Subgroup.equivMapOfInjective A
                (MulAut.conj (u : G)).toMonoidHom (MulAut.conj (u : G)).injective).toEquiv).symm
            _ = p ^ 2 := hAcard
    have hcardZ : Nat.card {x : ↥Q // (x : G) ∈ ZQ} = p := by
      have hZleQ : ZQ ≤ Q := hAZ.trans hAQ
      let eZ : {x : ↥Q // (x : G) ∈ ZQ} ≃ ↥ZQ :=
        { toFun := fun x => ⟨(x : G), x.2⟩
          invFun := fun x => ⟨⟨(x : G), hZleQ x.2⟩, x.2⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      calc
        Nat.card {x : ↥Q // (x : G) ∈ ZQ} = Nat.card (↥ZQ) := Nat.card_congr eZ
        _ = p := hZcard
    let e : ({x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G) ∧ (x : G) ∉ ZQ} ⊕
        {x : ↥Q // (x : G) ∈ ZQ}) ≃ {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G)} :=
      { toFun := fun s => match s with
          | Sum.inl x => ⟨x.1, x.2.1⟩
          | Sum.inr x => ⟨x.1, hZle x.2⟩
        invFun := fun x => if h : (x.1 : G) ∈ ZQ then Sum.inr ⟨x.1, h⟩ else Sum.inl ⟨x.1, ⟨x.2, h⟩⟩
        left_inv := by
          intro s
          cases s with
          | inl x => simp [x.2.2]
          | inr x => simp [x.2]
        right_inv := by
          intro x
          by_cases h : (x.1 : G) ∈ ZQ
          · simp [h]
          · simp [h] }
    have hsum' : Nat.card {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G) ∧ (x : G) ∉ ZQ} + p =
        p ^ 2 := by
      calc
        Nat.card {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G) ∧ (x : G) ∉ ZQ} + p =
            Nat.card {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G) ∧ (x : G) ∉ ZQ} +
              Nat.card {x : ↥Q // (x : G) ∈ ZQ} := by rw [hcardZ]
        _ = Nat.card ({x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G) ∧ (x : G) ∉ ZQ} ⊕
            {x : ↥Q // (x : G) ∈ ZQ}) := by rw [Nat.card_sum]
        _ = Nat.card {x : ↥Q // (x : G) ∈ conjugateSubgroup A (u : G)} := Nat.card_congr e
        _ = p ^ 2 := hcardAu
    omega
  let φ : (Σ c : C, fiber c) → {x : ↥Q // (x : G) ∉ ZQ} := fun z => ⟨z.2.1, z.2.2.2⟩
  have hφ_inj : Function.Injective φ := by
    intro z₁ z₂ hz
    cases z₁ with
    | mk c₁ x₁ =>
      cases z₂ with
      | mk c₂ x₂ =>
        have hx : (x₁.1 : G) = (x₂.1 : G) :=
          congrArg (fun y : {x : ↥Q // (x : G) ∉ ZQ} => (y.1 : G)) hz
        have hc : c₁ = c₂ := by
          by_contra hne
          have hp := hpair_fact c₁ c₂ hne
          have hx1 : (x₁.1 : G) ∈ (f c₁).1 := x₁.2.1
          have hx2 : (x₁.1 : G) ∈ (f c₂).1 := by
            rw [hx]
            exact x₂.2.1
          have hxcap : (x₁.1 : G) ∈ (f c₁).1 ⊓ (f c₂).1 := Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
          have hxZ : (x₁.1 : G) ∈ ZQ := by
            rwa [hp] at hxcap
          exact x₁.2.2 hxZ
        subst c₂
        congr 1
        apply Subtype.ext
        exact Subtype.ext hx
  have hCcard : Nat.card C = (normalizerIn U A).relIndex U := by rfl
  let : Fintype C := Fintype.ofFinite C
  have hsum : Nat.card (Σ c : C, fiber c) = Nat.card C * (p ^ 2 - p) := by
    rw [Nat.card_sigma (α := C) (β := fiber)]
    calc
      (∑ c : C, Nat.card (fiber c)) = (∑ _c : C, (p ^ 2 - p)) := by
        apply Finset.sum_congr rfl
        intro c _hc
        exact hfib c
      _ = Nat.card C * (p ^ 2 - p) := by
        simp [Nat.card_eq_fintype_card]
  have hle : Nat.card C * (p ^ 2 - p) ≤ p ^ 3 - p := by
    calc
      Nat.card C * (p ^ 2 - p) = Nat.card (Σ c : C, fiber c) := hsum.symm
      _ ≤ Nat.card {x : ↥Q // (x : G) ∉ ZQ} := Nat.card_le_card_of_injective φ hφ_inj
      _ = p ^ 3 - p := hnotZ
  have hp2 : p ^ 2 - p = p * (p - 1) := by
    calc
      p ^ 2 - p = p * p - p := by rw [pow_two]
      _ = p * p - p * 1 := by simp
      _ = p * (p - 1) := (Nat.mul_sub_left_distrib p p 1).symm
  have hp3 : p ^ 3 - p = p * (p ^ 2 - 1) := by
    calc
      p ^ 3 - p = p * p ^ 2 - p := by congr 1 <;> ring
      _ = p * p ^ 2 - p * 1 := by simp
      _ = p * (p ^ 2 - 1) := (Nat.mul_sub_left_distrib p (p ^ 2) 1).symm
  have hle2 : p * (Nat.card C * (p - 1)) ≤ p * (p ^ 2 - 1) := by
    rw [hp2, hp3] at hle
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hle
  have hle3 : Nat.card C * (p - 1) ≤ p ^ 2 - 1 :=
    Nat.le_of_mul_le_mul_left hle2 (Fact.out : p.Prime).pos
  have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    rw [← Nat.sq_sub_sq p 1]
  have hle4 : Nat.card C * (p - 1) ≤ (p + 1) * (p - 1) := by
    rwa [hsq] at hle3
  have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hle5 : Nat.card C ≤ p + 1 :=
    Nat.le_of_mul_le_mul_right hle4 (by omega : 0 < p - 1)
  rw [← hCcard]
  exact hle5

/-! ## The shared linear omega data -/

/-- The synchronized equation-(1)--(7) data, the choices `P`, `P0`,
`A = P ⊔ P0`, and the characteristic omega subgroup `Q`, shared by the
trichotomy and the three equation-(8) branch modules. -/
public structure SecondCaseLinearOmegaData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) where
  p : ℕ
  hp_prime : p.Prime
  K : Subgroup G
  B : Subgroup G
  F : Subgroup G
  s : d.E
  s_involution : IsInvolution (s : G)
  s_mem_H : (s : G) ∈ c.H
  K_inverted : (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G)
  B_fixed : B = centralizerIn (c.U ⊓ w.M) (s : G)
  U_inter_M_eq : K ⊔ B = c.U ⊓ w.M
  K_cyclic : IsCyclic K
  K_le_E : K ≤ d.E
  K0 : Subgroup G
  K0_eq : K0 = c.FU ⊓ K
  F_fixed : F = centralizerIn (c.FU ⊓ w.M) (s : G)
  FU_inter_M_eq : K0 ⊔ F = c.FU ⊓ w.M
  F_normal_M : IsNormalIn F w.M
  F_centralizes_E : F ≤ Subgroup.centralizer (d.E : Set G)
  F_cyclic : IsCyclic F
  F_normalizer : Subgroup.normalizer (F : Set G) = w.M
  F_TI : ∀ g : G, g ∉ w.M → F ⊓ conjugateSubgroup F g = ⊥
  F_card_dvd_K0 : Nat.card F ∣ Nat.card K0
  P : Subgroup G
  P_le_F : P ≤ F
  P_card : Nat.card P = p
  P0 : Subgroup G
  P0_le_K0 : P0 ≤ K0
  P0_card : Nat.card P0 = p
  A : Subgroup G
  A_eq : A = P ⊔ P0
  A_card : Nat.card A = p ^ 2
  A_elem_abelian : IsElementaryAbelian p A
  A_le_FU : A ≤ c.FU
  Q : Subgroup c.U
  Q_le_upperCentralSeries_two : Q ≤
    (Subgroup.upperCentralSeries (pCore p (↥c.U)) 2).map (pCore p (↥c.U)).subtype
  Q_not_cyclic : ¬ IsCyclic Q
  Q_exponent : Monoid.exponent Q = p
  Q_characteristic : Q.Characteristic

/-! ## Derived identities -/

/-- The inverted and fixed parts of `F(U) ∩ M` intersect trivially. -/
public theorem secondCase_linear_omega_F_cap_K0
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    od.F ⊓ od.K0 = ⊥ := by
  classical
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  apply le_bot_iff.mp
  intro x hx
  have hFleFU : od.F ≤ c.FU := by
    intro f hf
    rw [od.F_fixed] at hf
    exact hf.1.1
  have hxfix : (od.s : G) * x * (od.s : G)⁻¹ = x := by
    have hxmem : x ∈ centralizerIn (c.FU ⊓ w.M) (od.s : G) := by
      rw [← od.F_fixed]
      exact hx.1
    have hxcent : x ∈ Subgroup.centralizer ({(od.s : G)} : Set G) := hxmem.2
    have hcomm : (od.s : G) * x = x * (od.s : G) :=
      (Subgroup.mem_centralizer_iff.mp hxcent) (od.s : G) (by simp)
    calc
      (od.s : G) * x * (od.s : G)⁻¹ = x * (od.s : G) * (od.s : G)⁻¹ := by rw [hcomm]
      _ = x := by simp
  have hxinv : (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹ := by
    have hxK : x ∈ od.K := by
      rw [od.K0_eq] at hx
      exact hx.2.2
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
      rw [← od.K_inverted]
      exact hxK
    exact hxI.2
  have hx2 : x ^ 2 = 1 := by
    have hxeq : x = x⁻¹ := hxfix.symm.trans hxinv
    calc
      x ^ 2 = x * x := by rw [pow_two]
      _ = x * x⁻¹ := congrArg (fun y : G => x * y) hxeq
      _ = 1 := by simp
  have hxU : x ∈ c.U := (fittingSubgroupOf_le c.U) (hFleFU hx.1)
  have hdiv2 : orderOf x ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).mpr hx2
  have hdivU : orderOf x ∣ Nat.card (↥c.U) := Subgroup.orderOf_dvd_natCard c.U hxU
  have hcop : Nat.Coprime 2 (Nat.card (↥c.U)) := Nat.coprime_two_left.mpr hUodd
  have hdvd1 : orderOf x ∣ Nat.gcd 2 (Nat.card (↥c.U)) := Nat.dvd_gcd hdiv2 hdivU
  have hord1 : orderOf x ∣ 1 := by
    simpa [hcop.gcd_eq_one] using hdvd1
  have hxone : x = 1 :=
    (orderOf_eq_one_iff (x := x)).mp (Nat.dvd_one.mp hord1)
  exact Subgroup.mem_bot.mpr hxone

/-- The prime `p` is odd: `|P| = p` divides `|U|` and `U` has odd order. -/
public theorem secondCase_linear_omega_p_odd
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    Odd od.p := by
  have hFleFU : od.F ≤ c.FU := by
    intro f hf
    rw [od.F_fixed] at hf
    exact hf.1.1
  have hPleU : od.P ≤ c.U := od.P_le_F.trans (hFleFU.trans (fittingSubgroupOf_le c.U))
  have hpdvd : od.p ∣ Nat.card (↥c.U) := by
    have hdvd1 : Nat.card od.P ∣ Nat.card (↥c.U) := Subgroup.card_dvd_of_le hPleU
    simpa [od.P_card] using hdvd1
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  exact Odd.of_dvd_nat hUodd hpdvd

/-- `Q` lies in `F(U)`: `Z₂(O_p(U)) ≤ O_p(U) ≤ F(U)`. -/
public theorem secondCase_linear_omega_QG_le_FU
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    od.Q.map c.U.subtype ≤ c.FU := by
  classical
  let : Fact od.p.Prime := ⟨od.hp_prime⟩
  let P0 : Subgroup (↥c.U) := pCore od.p (↥c.U)
  have hZ2le : od.Q ≤ (Subgroup.upperCentralSeries P0 2).map P0.subtype :=
    od.Q_le_upperCentralSeries_two
  have hleP0 : (Subgroup.upperCentralSeries P0 2).map P0.subtype ≤ P0 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    exact z.2
  have hP0leF : P0 ≤ fittingSubgroup (↥c.U) :=
    pCore_le_fitting (G := ↥c.U) od.p
  have hQleF : od.Q ≤ fittingSubgroup (↥c.U) :=
    hZ2le.trans (hleP0.trans hP0leF)
  intro q hq
  rcases Subgroup.mem_map.mp hq with ⟨q0, hq0, rfl⟩
  exact Subgroup.mem_map.mpr ⟨q0, hQleF hq0, rfl⟩

/-- `N_U(P) = U ∩ M` from equations (5)--(6): `F` is cyclic and normal in
`M`, `N_G(F) = M`, and outside conjugates of `F` meet trivially. -/
public theorem secondCase_linear_omega_NU_P_eq_U_inter_M
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    normalizerIn c.U od.P = c.U ⊓ w.M := by
  classical
  apply le_antisymm
  · intro u hu
    refine ⟨hu.1, ?_⟩
    by_contra hnotM
    have hPu : od.P ≤ conjugateSubgroup od.F u := by
      intro p hp
      have huinvP : u⁻¹ * p * u ∈ od.P := by
        have huinv : u⁻¹ ∈ Subgroup.normalizer (od.P : Set G) :=
          (Subgroup.normalizer (od.P : Set G)).inv_mem hu.2
        simpa using ((Subgroup.mem_normalizer_iff.mp huinv p).1 hp)
      exact Subgroup.mem_map.mpr ⟨u⁻¹ * p * u, od.P_le_F huinvP, by
        simp [MulAut.conj_apply]
        group⟩
    have hPleFcap : od.P ≤ od.F ⊓ conjugateSubgroup od.F u :=
      le_inf od.P_le_F hPu
    have hne : od.F ⊓ conjugateSubgroup od.F u ≠ ⊥ := by
      intro hbot
      have hPleBot : od.P ≤ ⊥ := by simpa [hbot] using hPleFcap
      have hPbot : od.P = ⊥ := le_bot_iff.mp hPleBot
      have hcard1 : Nat.card od.P = 1 := by rw [hPbot]; simp
      have hp1 : od.p = 1 := od.P_card.symm.trans hcard1
      exact od.hp_prime.ne_one hp1
    exact hne (od.F_TI u hnotM)
  · intro u hu
    refine ⟨hu.1, ?_⟩
    have huF : u ∈ Subgroup.normalizer (od.F : Set G) :=
      (le_normalizer_of_isNormalIn od.F_normal_M) hu.2
    exact prime_order_subgroup_fixed_by_normalizer_of_cyclic od.F_cyclic od.P_le_F
      od.hp_prime od.P_card huF

/-- `N_U(P) ≤ N_U(A)`: every element of `U` normalizing the prime-order
subgroup `P` fixes the inverted prime-order part `P0` (via the cyclic
factor `K0`) and hence normalizes `A = P ⊔ P0`. -/
public theorem secondCase_linear_omega_NU_P_le_NU_A
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    normalizerIn c.U od.P ≤ normalizerIn c.U od.A := by
  classical
  let : Fact od.p.Prime := ⟨od.hp_prime⟩
  have hK0leK : od.K0 ≤ od.K := by
    rw [od.K0_eq]
    exact inf_le_right
  let : IsCyclic od.K := od.K_cyclic
  have hK0cyc : IsCyclic od.K0 := Subgroup.isCyclic_of_le hK0leK
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hUleH : c.U ≤ c.H := (centralizerSetup_U_isNormalIn_H c).1
  have hsM : (od.s : G) ∈ w.M := d.E_component.1 od.s.2
  have hsX : ∀ x : G, x ∈ c.U ⊓ w.M →
      (od.s : G) * x * (od.s : G)⁻¹ ∈ c.U ⊓ w.M := by
    intro x hx
    exact ⟨(centralizerSetup_U_isNormalIn_H c).2
        (od.s : G) od.s_mem_H x hx.1,
      w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)⟩
  have hcopX : Nat.Coprime 2 (Nat.card (↥(c.U ⊓ w.M))) :=
    Nat.coprime_two_left.mpr
      (Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left))
  have hK_normal_X : IsNormalIn od.K (c.U ⊓ w.M) :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal
      (X := c.U ⊓ w.M) (s := (od.s : G)) od.s_involution hcopX hsX
      (I := od.K) od.K_inverted).2.1
  intro v hv
  refine ⟨hv.1, ?_⟩
  have hvX : v ∈ c.U ⊓ w.M := by
    rw [← secondCase_linear_omega_NU_P_eq_U_inter_M c w d od]
    exact hv
  have hvFU : v ∈ Subgroup.normalizer (c.FU : Set G) :=
    (le_normalizer_of_isNormalIn (centralizerSetup_FU_isNormalIn_H c))
      (hUleH hvX.1)
  have hvK : v ∈ Subgroup.normalizer (od.K : Set G) :=
    (le_normalizer_of_isNormalIn hK_normal_X) hvX
  have hvK0 : v ∈ Subgroup.normalizer (od.K0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [od.K0_eq] at hx ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp hvFU x).1 hx.1,
        (Subgroup.mem_normalizer_iff.mp hvK x).1 hx.2⟩
    · intro hx
      rw [od.K0_eq] at hx ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp hvFU x).2 hx.1,
        (Subgroup.mem_normalizer_iff.mp hvK x).2 hx.2⟩
  have hvP0 : v ∈ Subgroup.normalizer (od.P0 : Set G) :=
    prime_order_subgroup_fixed_by_normalizer_of_cyclic hK0cyc od.P0_le_K0
      od.hp_prime od.P0_card hvK0
  have hvJoin : v ∈ Subgroup.normalizer ((od.P ⊔ od.P0 : Subgroup G) : Set G) :=
    Subgroup.normalizer_inf_normalizer_le_normalizer_sup od.P od.P0 ⟨hv.2, hvP0⟩
  simpa [od.A_eq] using hvJoin

end CFSG.GorensteinWalter
