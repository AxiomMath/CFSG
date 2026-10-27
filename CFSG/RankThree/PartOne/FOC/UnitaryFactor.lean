module

public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne
open scoped commutatorElement

universe u

section Powers

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]

theorem pow_apply_eq_of_apply_eq {W : Submodule K V} {u u' : LinearMap.GeneralLinearGroup K V}
    (hu' : ∀ w ∈ W, ((u' : LinearMap.GeneralLinearGroup K V) : Module.End K V) w ∈ W)
    (h : ∀ w ∈ W, ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) w =
      ((u' : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) :
    ∀ k : ℕ, ∀ v ∈ W, (((u ^ k : LinearMap.GeneralLinearGroup K V)) : Module.End K V) v =
      (((u' ^ k : LinearMap.GeneralLinearGroup K V)) : Module.End K V) v := by
  intro k
  induction k with
  | zero => intro v _; rfl
  | succ k ih =>
    intro v hv
    have hw : (((u' ^ k : LinearMap.GeneralLinearGroup K V)) : Module.End K V) v ∈ W := by
      clear ih
      induction k generalizing v with
      | zero => exact hv
      | succ k ihk =>
        rw [pow_succ', Units.val_mul, Module.End.mul_apply]
        exact hu' _ (ihk v hv)
    rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih v hv, pow_succ', Units.val_mul,
      Module.End.mul_apply]
    exact h _ hw

theorem pow_apply_eq_self {W : Submodule K V} {u : LinearMap.GeneralLinearGroup K V}
    (h : ∀ w ∈ W, ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) w = w) :
    ∀ k : ℕ, ∀ v ∈ W, (((u ^ k : LinearMap.GeneralLinearGroup K V)) : Module.End K V) v = v := by
  intro k
  induction k with
  | zero => intro v _; rfl
  | succ k ih =>
    intro v hv
    rw [pow_succ, Units.val_mul, Module.End.mul_apply, h v hv, ih v hv]

theorem inv_apply_eq_self {u : LinearMap.GeneralLinearGroup K V} {v : V}
    (h : ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v) :
    ((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
  calc ((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v
      = ((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) := by rw [h]
    _ = v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]; rfl

end Powers

section Orbits

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

variable (H : UnitaryPrimaryData hK.bar B x)
include H

theorem orbit_closed (a : primaryFactors (x : Module.End K V)) :
    ∀ b ∈ primaryFactors (x : Module.End K V),
      b ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) →
        dualPoly hK.bar b ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) := by
  intro b hb hbO
  rcases hbO with rfl | hbO
  · exact Or.inr rfl
  · rw [Set.mem_singleton_iff] at hbO
    subst hbO
    exact Or.inl (dualPoly_dualPoly_of_mem H a.2)

theorem commute_of_commute_supported {O : Set K[X]}
    (hO : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O → dualPoly hK.bar b ∈ O)
    {z : LinearMap.GeneralLinearGroup K V} (hz : z ∈ supportedUnitary B x O)
    (hc : ∀ g ∈ supportedUnitary B x O, Commute z g)
    {m : LinearMap.GeneralLinearGroup K V} (hm : m ∈ unitaryCentralizer B x) : Commute z m := by
  obtain ⟨mO, hmO, hmeq⟩ := exists_component H hO hm
  have hm' : mO⁻¹ * m ∈ supportedUnitary B x {c | c ∉ O} := by
    refine ⟨mul_mem (inv_mem hmO.1) hm, fun b hb hbS v hv => ?_⟩
    have hbO : b ∈ O := by simpa using hbS
    rw [Units.val_mul, Module.End.mul_apply, ← hmeq b hb hbO v hv, ← Module.End.mul_apply,
      ← Units.val_mul, inv_mul_cancel]
    rfl
  have hd : Disjoint O {c | c ∉ O} := Set.disjoint_left.mpr fun c hc hc' => hc' hc
  have h1 : Commute z (mO⁻¹ * m) := commute_of_disjoint H hd hz hm'
  have h2 : Commute z mO := hc mO hmO
  have : m = mO * (mO⁻¹ * m) := by simp
  rw [this]
  exact h2.mul_right h1

theorem component_pow_eq_one {O : Set K[X]} {g gO : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ unitaryCentralizer B x) (hgO : gO ∈ supportedUnitary B x O)
    (hgeq : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
        (gO : Module.End K V) v = (g : Module.End K V) v)
    {p : ℕ} (hgp : g ^ p = 1) : gO ^ p = 1 := by
  refine eq_one_of_forall_apply_eq H.squarefree fun b hb v hv => ?_
  by_cases hbO : b ∈ O
  · have hgc : Commute (g : Module.End K V) (x : Module.End K V) :=
      (mem_unitaryCentralizer.mp hg).2
    have := pow_apply_eq_of_apply_eq (W := primaryComponent (x : Module.End K V) b) (u := gO)
      (u' := g) (fun w hw => apply_mem_primaryComponent hgc hw)
      (fun w hw => hgeq b hb hbO w hw) p v hv
    rw [this, hgp]
    rfl
  · exact pow_apply_eq_self (W := primaryComponent (x : Module.End K V) b) (u := gO)
      (fun w hw => hgO.2 b hb hbO w hw) p v hv

omit [FiniteDimensional K V] H in
theorem peel_component {O : Set K[X]} {g gO : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ unitaryCentralizer B x) (hgO : gO ∈ supportedUnitary B x O)
    (hgeq : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
        (gO : Module.End K V) v = (g : Module.End K V) v) :
    (∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
        ((gO⁻¹ * g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v) ∧
    (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
        ((gO⁻¹ * g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
          (g : Module.End K V) v) := by
  have hgc : Commute (g : Module.End K V) (x : Module.End K V) := (mem_unitaryCentralizer.mp hg).2
  constructor
  · intro b hb hbO v hv
    rw [Units.val_mul, Module.End.mul_apply, ← hgeq b hb hbO v hv, ← Module.End.mul_apply,
      ← Units.val_mul, inv_mul_cancel]
    rfl
  · intro b hb hbO v hv
    have hgv : (g : Module.End K V) v ∈ primaryComponent (x : Module.End K V) b :=
      apply_mem_primaryComponent hgc hv
    rw [Units.val_mul, Module.End.mul_apply]
    exact inv_apply_eq_self (hgO.2 b hb hbO _ hgv)

end Orbits

section Factor

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

@[expose] def GoodSplit (hK : UnitaryFieldData ℓ f K) (B : V →ₛₗ[hK.bar] V →ₗ[K] K)
    (x : LinearMap.GeneralLinearGroup K V) (p : ℕ) : Prop :=
  ∀ a : primaryFactors (x : Module.End K V), IsGoodBlock hK x a →
    ∀ g ∈ orbitFactor B x (a : K[X]), g ^ p = 1 →
      ∃ z ∈ orbitFactor B x (a : K[X]),
        (∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
          ((z : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
            ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)) ∧
        z⁻¹ * g ∈ specialBlock B x (a : K[X])

variable (H : UnitaryPrimaryData hK.bar B x)
include H

theorem exists_factor_orbit (hq : 2 ≤ ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hobs : GoodSplit hK B x p) (a : primaryFactors (x : Module.End K V))
    {gO : LinearMap.GeneralLinearGroup K V} (hgO : gO ∈ orbitFactor B x (a : K[X]))
    (hgOp : gO ^ p = 1) :
    ∃ z ∈ unitaryCentralizer B x, (∀ m ∈ unitaryCentralizer B x, Commute z m) ∧
      ∃ k ∈ (⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
        specialBlock B x (a : K[X])), gO = z * k := by
  by_cases hgood : IsGoodBlock hK x a
  · obtain ⟨z, hz, hscal, hk⟩ := hobs a hgood gO hgO hgOp
    refine ⟨z, orbitFactor_le_unitaryCentralizer hz, fun m hm =>
      commute_of_commute_supported H (orbit_closed H a) hz (fun g hg =>
        commute_orbitFactor_of_scalar H a (orbitFactor_le_unitaryCentralizer hz) hscal hg) hm,
      z⁻¹ * gO, ?_, by simp⟩
    exact le_iSup (fun a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a} =>
      specialBlock B x (a : K[X])) ⟨a, hgood⟩ hk
  · by_cases hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])
    ·
      have hself : dualPoly hK.bar (a : K[X]) = a := by
        by_contra hne
        exact hgood ⟨hm, fun h => absurd h hne⟩
      have hbad : (primaryMultiplicity (x : Module.End K V) (a : K[X]),
          ℓ ^ (f * (a : K[X]).natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
        by_contra hnot
        exact hgood ⟨hm, fun _ => hnot⟩
      have hgM : gO ∈ unitaryCentralizer B x := orbitFactor_le_unitaryCentralizer hgO
      have hg1 : gO = 1 := by
        refine eq_one_of_forall_apply_eq H.squarefree fun c hc v hv => ?_
        by_cases hca : c = (a : K[X])
        · subst hca
          exact apply_eq_of_exceptional H hp hp3 hgM hgOp a hself hbad v hv
        · refine hgO.2 c hc ?_ v hv
          intro hcO
          rcases hcO with h | h
          · exact hca h
          · rw [hself] at h
            exact hca h
      exact ⟨1, one_mem _, fun m _ => Commute.one_left m, 1, one_mem _, by rw [hg1]; simp⟩
    ·
      have hm1 : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1 := by omega
      have hF : SpecialBlockFacts B x a := by
        by_cases hself : dualPoly hK.bar (a : K[X]) = a
        · exact specialBlockFacts_of_selfDual hq a hself (selfDualPrimaryBlock H a hself)
            (fun h => absurd h (by omega))
        · exact specialBlockFacts_of_paired hq a (pairedPrimaryBlock H a (Ne.symm hself))
      refine ⟨gO, orbitFactor_le_unitaryCentralizer hgO, fun m hm' =>
        commute_of_commute_supported H (orbit_closed H a) hgO (fun g hg =>
          hF.abelian hm1 gO hgO g hg) hm', 1, one_mem _, by simp⟩

theorem exists_central_factor (hq : 2 ≤ ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hobs : GoodSplit hK B x p) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ unitaryCentralizer B x) (hgp : g ^ p = 1) :
    ∃ z ∈ unitaryCentralizer B x, (∀ m ∈ unitaryCentralizer B x, Commute z m) ∧
      ∃ k ∈ (⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
        specialBlock B x (a : K[X])), g = z * k := by
  classical
  suffices key : ∀ F : Finset K[X], ∀ g ∈ unitaryCentralizer B x, g ^ p = 1 →
      (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ F →
        ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v) →
      ∃ z ∈ unitaryCentralizer B x, (∀ m ∈ unitaryCentralizer B x, Commute z m) ∧
        ∃ k ∈ (⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
          specialBlock B x (a : K[X])), g = z * k by
    exact key (primaryFactors (x : Module.End K V)) g hg hgp fun b hb hbn => absurd hb hbn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro g hg hgp h
    have : g = 1 := eq_one_of_forall_apply_eq H.squarefree fun b hb v hv => h b hb (by simp) v hv
    exact ⟨1, one_mem _, fun m _ => Commute.one_left m, 1, one_mem _, by rw [this]; simp⟩
  | insert b F hbF ih =>
    intro g hg hgp h
    by_cases hbΦ : b ∈ primaryFactors (x : Module.End K V)
    · set a : primaryFactors (x : Module.End K V) := ⟨b, hbΦ⟩ with ha
      set O : Set K[X] := {(a : K[X]), dualPoly hK.bar (a : K[X])} with hOdef
      obtain ⟨gO, hgO, hgOeq⟩ := exists_component H (orbit_closed H a) hg
      have hgOp : gO ^ p = 1 := component_pow_eq_one H hg hgO hgOeq hgp
      obtain ⟨hin, hout⟩ := peel_component hg hgO hgOeq
      have hg' : gO⁻¹ * g ∈ unitaryCentralizer B x :=
        mul_mem (inv_mem hgO.1) hg
      have hg'p : (gO⁻¹ * g) ^ p = 1 := by
        refine eq_one_of_forall_apply_eq H.squarefree fun c hc v hv => ?_
        by_cases hcO : c ∈ O
        · exact pow_apply_eq_self (W := primaryComponent (x : Module.End K V) c)
            (u := gO⁻¹ * g) (fun w hw => hin c hc hcO w hw) p v hv
        · have hgc : Commute (g : Module.End K V) (x : Module.End K V) :=
            (mem_unitaryCentralizer.mp hg).2
          have := pow_apply_eq_of_apply_eq (W := primaryComponent (x : Module.End K V) c)
            (u := gO⁻¹ * g) (u' := g) (fun w hw => apply_mem_primaryComponent hgc hw)
            (fun w hw => hout c hc hcO w hw) p v hv
          rw [this, hgp]
          rfl
      have hg'tr : ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ F →
          ∀ v ∈ primaryComponent (x : Module.End K V) c,
            ((gO⁻¹ * g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
        intro c hc hcF v hv
        by_cases hcO : c ∈ O
        · exact hin c hc hcO v hv
        · rw [hout c hc hcO v hv]
          refine h c hc ?_ v hv
          simp only [Finset.mem_insert, not_or]
          refine ⟨fun hcb => hcO ?_, hcF⟩
          rw [hcb]
          exact Or.inl rfl
      obtain ⟨z', hz', hz'c, k', hk', hg'eq⟩ := ih (gO⁻¹ * g) hg' hg'p hg'tr
      obtain ⟨z₀, hz₀, hz₀c, k₀, hk₀, hgOeq'⟩ := exists_factor_orbit H hq hp hp3 hobs a hgO hgOp
      have hk₀M : k₀ ∈ unitaryCentralizer B x :=
        (iSup_le (fun a' : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a} =>
          specialBlock_le_unitaryCentralizer) : (⨆ a : {a : primaryFactors (x : Module.End K V) //
            IsGoodBlock hK x a}, specialBlock B x (a : K[X])) ≤ unitaryCentralizer B x) hk₀
      refine ⟨z₀ * z', mul_mem hz₀ hz', fun m hm => (hz₀c m hm).mul_left (hz'c m hm),
        k₀ * k', mul_mem hk₀ hk', ?_⟩
      have h1 : g = gO * (gO⁻¹ * g) := by simp
      rw [h1, hg'eq, hgOeq']
      have hc : z' * k₀ = k₀ * z' := (hz'c k₀ hk₀M).eq
      calc z₀ * k₀ * (z' * k') = z₀ * (k₀ * z') * k' := by group
        _ = z₀ * (z' * k₀) * k' := by rw [hc]
        _ = z₀ * z' * (k₀ * k') := by group
    · refine ih g hg hgp fun c hc hcF v hv => h c hc ?_ v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun hcb => hbΦ (hcb ▸ hc), hcF⟩

end Factor

end CFSG.RankThree.PartOne.FOC
