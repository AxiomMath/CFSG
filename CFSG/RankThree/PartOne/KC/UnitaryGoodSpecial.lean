module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne
open scoped commutatorElement

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

@[expose] def IsGoodBlock (hK : UnitaryFieldData ℓ f K) (x : LinearMap.GeneralLinearGroup K V)
    (a : primaryFactors (x : Module.End K V)) : Prop :=
  2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) ∧
    (dualPoly hK.bar (a : K[X]) = a →
      (primaryMultiplicity (x : Module.End K V) (a : K[X]), ℓ ^ (f * (a : K[X]).natDegree)) ∉
        ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)))

section Good

variable {hK : UnitaryFieldData ℓ f K} {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem isGoodBlock_numeric (hq : 2 ≤ ℓ ^ f) {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (ha : IsGoodBlock hK x a) :
    (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 →
      4 ≤ ℓ ^ (f * (a : K[X]).natDegree)) ∧
    (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 3 →
      3 ≤ ℓ ^ (f * (a : K[X]).natDegree)) := by
  have hQ2 : 2 ≤ ℓ ^ (f * (a : K[X]).natDegree) := hq.trans (le_pow_natDegree hK a)
  have h := ha.2 hself
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  generalize primaryMultiplicity (x : Module.End K V) (a : K[X]) = m at h1 h2 h3 ⊢
  generalize ℓ ^ (f * (a : K[X]).natDegree) = Q at h1 h2 h3 hQ2 ⊢
  constructor
  · intro hm
    subst hm
    by_contra hlt
    exact (by omega : False)
  · intro hm
    subst hm
    by_contra hlt
    exact (by omega : False)

theorem specialBlockFacts_of_good (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ ℓ ^ f)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a) :
    SpecialBlockFacts B x a := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact specialBlockFacts_of_selfDual hq a hself (selfDualPrimaryBlock H a hself)
      (fun _ => isGoodBlock_numeric hq hself ha)
  · exact specialBlockFacts_of_paired hq a (pairedPrimaryBlock H a (Ne.symm hself))

theorem specialBlock_le_sesqSpecialUnitaryGroup_of_good (H : UnitaryPrimaryData hK.bar B x)
    (hq : 2 ≤ ℓ ^ f) (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a) :
    specialBlock B x (a : K[X]) ≤ sesqSpecialUnitaryGroup B := by
  intro g hg
  refine mem_sesqSpecialUnitaryGroup.mpr ⟨?_, (specialBlockFacts_of_good H hq a ha).detK g hg⟩
  exact (specialBlock_le_unitaryCentralizer hg).1

end Good

section Scalars

variable {hK : UnitaryFieldData ℓ f K} {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

omit [FiniteDimensional K V] in
theorem apply_smul_primaryComponent {a : K[X]} {r : Module.End K V}
    (hr : Commute r (x : Module.End K V)) (c : AdjoinRoot a)
    (v : primaryComponent (x : Module.End K V) a) :
    r (((c • v : primaryComponent (x : Module.End K V) a)) : V) =
      ((c • (⟨r (v : V), apply_mem_primaryComponent hr v.2⟩ :
        primaryComponent (x : Module.End K V) a) : primaryComponent (x : Module.End K V) a) :
          V) := by
  have h := map_smul (commutantRestrict (x := (x : Module.End K V)) a
    ⟨r, (mem_commutant _).mpr hr⟩) c v
  exact congrArg Subtype.val h

theorem commute_orbitFactor_of_scalar (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) {Y g : LinearMap.GeneralLinearGroup K V}
    (hY : Y ∈ unitaryCentralizer B x)
    (hscal : ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
      (Y : Module.End K V) (v : V) =
        ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V))
    (hg : g ∈ orbitFactor B x (a : K[X])) : Commute Y g := by
  have hsq := H.squarefree
  set O : Set K[X] := {(a : K[X]), dualPoly hK.bar (a : K[X])} with hOdef
  have hO : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O → dualPoly hK.bar b ∈ O := by
    intro b hb hbO
    rcases hbO with rfl | hbO
    · exact Or.inr rfl
    · rw [Set.mem_singleton_iff] at hbO
      subst hbO
      exact Or.inl (dualPoly_dualPoly_of_mem H a.2)
  obtain ⟨Y₀, hY₀, hYY₀⟩ := exists_component H hO hY
  have hgO : g ∈ supportedUnitary B x O := hg
  obtain ⟨c, hc⟩ := hscal
  have hgc : Commute (g : Module.End K V) (x : Module.End K V) :=
    (mem_unitaryCentralizer.mp hg.1).2
  have hYc : Commute (Y : Module.End K V) (x : Module.End K V) :=
    (mem_unitaryCentralizer.mp hY).2
  have hY₀g : Y₀ * g = g * Y₀ := by
    have hκ : (g * Y₀)⁻¹ * (Y₀ * g) ∈ supportedUnitary B x O :=
      mul_mem (inv_mem (mul_mem hgO hY₀)) (mul_mem hY₀ hgO)
    have h1 : ∀ v ∈ primaryComponent (x : Module.End K V) (a : K[X]),
        (((g * Y₀)⁻¹ * (Y₀ * g) : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
      intro v hv
      have hgv : (g : Module.End K V) v ∈ primaryComponent (x : Module.End K V) (a : K[X]) :=
        apply_mem_primaryComponent hgc hv
      have e1 : (((Y₀ * g : LinearMap.GeneralLinearGroup K V) : Module.End K V)) v =
          (((g * Y₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V)) v := by
        change (Y₀ : Module.End K V) ((g : Module.End K V) v) =
          (g : Module.End K V) ((Y₀ : Module.End K V) v)
        rw [hYY₀ (a : K[X]) a.2 (Or.inl rfl) _ hgv, hYY₀ (a : K[X]) a.2 (Or.inl rfl) v hv]
        have e2 := hc ⟨(g : Module.End K V) v, hgv⟩
        have e3 := hc ⟨v, hv⟩
        have e4 := apply_smul_primaryComponent (a := (a : K[X])) hgc c ⟨v, hv⟩
        change (Y : Module.End K V) ((g : Module.End K V) v) = _ at e2
        change (Y : Module.End K V) v = _ at e3
        rw [e2, e3, e4]
      rw [Units.val_mul, Module.End.mul_apply, e1, ← Module.End.mul_apply, ← Units.val_mul,
        inv_mul_cancel]
      rfl
    have h2 := eq_one_of_paired H a.2 hκ h1
    exact (inv_mul_eq_one.mp h2).symm
  refine Units.ext (ext_primaryComponent hsq fun b hb v hv => ?_)
  change (Y : Module.End K V) ((g : Module.End K V) v) =
    (g : Module.End K V) ((Y : Module.End K V) v)
  by_cases hbO : b ∈ O
  · have hgv : (g : Module.End K V) v ∈ primaryComponent (x : Module.End K V) b :=
      apply_mem_primaryComponent hgc hv
    rw [← hYY₀ b hb hbO _ hgv, ← hYY₀ b hb hbO v hv]
    exact congrArg (fun T : LinearMap.GeneralLinearGroup K V => (T : Module.End K V) v) hY₀g
  · have hgv1 : (g : Module.End K V) v = v := hg.2 b hb hbO v hv
    have hYv : (Y : Module.End K V) v ∈ primaryComponent (x : Module.End K V) b :=
      apply_mem_primaryComponent hYc hv
    rw [hgv1, hg.2 b hb hbO _ hYv]

theorem commute_specialBlock_iff_scalar (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ ℓ ^ f)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    {Y : LinearMap.GeneralLinearGroup K V} (hY : Y ∈ unitaryCentralizer B x) :
    (∀ g ∈ specialBlock B x (a : K[X]), Commute Y g) ↔
      ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        (Y : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  constructor
  · intro h
    exact (specialBlockFacts_of_good H hq a ha).scalar Y hY (fun _ g hg => h g hg)
  · intro hscal g hg
    exact commute_orbitFactor_of_scalar H a hY hscal (specialBlock_le_orbitFactor hg)

end Scalars

section Exceptional

variable {hK : UnitaryFieldData ℓ f K} {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

omit [FiniteDimensional K V] in
theorem orbitFactor_eq_supportedUnitary_of_selfDual {a : K[X]} (hself : dualPoly hK.bar a = a) :
    orbitFactor B x a = supportedUnitary B x {a} := by
  unfold orbitFactor
  rw [hself, Set.pair_eq_singleton]

theorem one_le_primaryMultiplicity (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) :
    1 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := by
  have hne := primaryComponent_ne_bot H.squarefree a.2
  have : Nontrivial ↥(primaryComponent (x : Module.End K V) (a : K[X])) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  exact Module.finrank_pos

theorem card_orbitFactor_selfDual (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a) :
    (Nat.card (orbitFactor B x (a : K[X])) : ℤ) =
      ((ℓ ^ (f * (a : K[X]).natDegree) : ℕ) : ℤ) ^
          (primaryMultiplicity (x : Module.End K V) (a : K[X]) *
            (primaryMultiplicity (x : Module.End K V) (a : K[X]) - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 (primaryMultiplicity (x : Module.End K V) (a : K[X])),
          (((ℓ ^ (f * (a : K[X]).natDegree) : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  obtain ⟨hE, Hf, hHf, hHfl, φ, -, -⟩ := exists_selfDualFactor hself
    (selfDualPrimaryBlock H a hself)
  have h1 := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := primaryMultiplicity (x : Module.End K V) (a : K[X])) rfl
    (one_le_primaryMultiplicity H a)).1
  rw [Nat.card_congr φ.toEquiv]
  exact h1

theorem card_orbitFactor_exceptional (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a) :
    (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 →
      ℓ ^ (f * (a : K[X]).natDegree) = 2 → Nat.card (orbitFactor B x (a : K[X])) = 18) ∧
    (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 →
      ℓ ^ (f * (a : K[X]).natDegree) = 3 → Nat.card (orbitFactor B x (a : K[X])) = 96) ∧
    (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 3 →
      ℓ ^ (f * (a : K[X]).natDegree) = 2 → Nat.card (orbitFactor B x (a : K[X])) = 648) := by
  have h := card_orbitFactor_selfDual H a hself
  refine ⟨fun hm hQ => ?_, fun hm hQ => ?_, fun hm hQ => ?_⟩
  · rw [hm, hQ] at h
    have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
    exact_mod_cast h.trans e
  · rw [hm, hQ] at h
    have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by decide +kernel
    exact_mod_cast h.trans e
  · rw [hm, hQ] at h
    have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
    exact_mod_cast h.trans e

theorem not_dvd_exceptional {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ p ∣ 18 ∧ ¬ p ∣ 96 ∧ ¬ p ∣ 648 := by
  have h2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : p ∣ 2 * 3 ^ 2 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp this with h' | h'
    · exact h2 h'
    · exact h3 (hp.dvd_of_dvd_pow h')
  · intro h
    have : p ∣ 2 ^ 5 * 3 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp this with h' | h'
    · exact h2 (hp.dvd_of_dvd_pow h')
    · exact h3 h'
  · intro h
    have : p ∣ 2 ^ 3 * 3 ^ 4 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp this with h' | h'
    · exact h2 (hp.dvd_of_dvd_pow h')
    · exact h3 (hp.dvd_of_dvd_pow h')

theorem not_dvd_card_orbitFactor_exceptional (H : UnitaryPrimaryData hK.bar B x) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (a : primaryFactors (x : Module.End K V))
    (hself : dualPoly hK.bar (a : K[X]) = a)
    (hbad : (primaryMultiplicity (x : Module.End K V) (a : K[X]),
      ℓ ^ (f * (a : K[X]).natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))) :
    ¬ p ∣ Nat.card (orbitFactor B x (a : K[X])) := by
  obtain ⟨h1, h2, h3⟩ := card_orbitFactor_exceptional H a hself
  obtain ⟨n1, n2, n3⟩ := not_dvd_exceptional hp hp3
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hbad
  rcases hbad with ⟨hm, hQ⟩ | ⟨hm, hQ⟩ | ⟨hm, hQ⟩
  · rw [h1 hm hQ]
    exact n1
  · rw [h2 hm hQ]
    exact n2
  · rw [h3 hm hQ]
    exact n3

theorem apply_eq_of_exceptional (H : UnitaryPrimaryData hK.bar B x) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {b : LinearMap.GeneralLinearGroup K V} (hb : b ∈ unitaryCentralizer B x)
    (hbp : b ^ p = 1) (a : primaryFactors (x : Module.End K V))
    (hself : dualPoly hK.bar (a : K[X]) = a)
    (hbad : (primaryMultiplicity (x : Module.End K V) (a : K[X]),
      ℓ ^ (f * (a : K[X]).natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)))
    (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])) :
    (b : Module.End K V) v = v := by
  have hsq := H.squarefree
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} :=
    orbitFactor_eq_supportedUnitary_of_selfDual hself
  have hO : ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ ({(a : K[X])} : Set K[X]) →
      dualPoly hK.bar c ∈ ({(a : K[X])} : Set K[X]) := by
    intro c _ hcO
    rw [Set.mem_singleton_iff] at hcO
    subst hcO
    rw [hself]
    exact Set.mem_singleton _
  obtain ⟨g, hg, hgb⟩ := exists_component H hO hb
  have hbc : Commute (b : Module.End K V) (x : Module.End K V) := (mem_unitaryCentralizer.mp hb).2
  have hpowa : ∀ k : ℕ, ∀ w ∈ primaryComponent (x : Module.End K V) (a : K[X]),
      ((g ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V) w =
        ((b ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V) w := by
    intro k
    induction k with
    | zero => intro w hw; rfl
    | succ k ih =>
      intro w hw
      have hbw : ((b ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V) w ∈
          primaryComponent (x : Module.End K V) (a : K[X]) := by
        have hck : Commute (((b ^ k : LinearMap.GeneralLinearGroup K V)) : Module.End K V)
            (x : Module.End K V) := by
          rw [Units.val_pow_eq_pow_val]
          exact hbc.pow_left k
        exact apply_mem_primaryComponent hck hw
      rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih w hw, pow_succ', Units.val_mul,
        Module.End.mul_apply]
      exact hgb (a : K[X]) a.2 rfl _ hbw
  have hpowo : ∀ k : ℕ, ∀ c ∈ primaryFactors (x : Module.End K V), c ≠ (a : K[X]) →
      ∀ w ∈ primaryComponent (x : Module.End K V) c,
        ((g ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V) w = w := by
    intro k
    induction k with
    | zero => intro c _ _ w _; rfl
    | succ k ih =>
      intro c hc hca w hw
      rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih c hc hca w hw]
      exact hg.2 c hc (fun h => hca (Set.mem_singleton_iff.mp h)) w hw
  have hgp : g ^ p = 1 := by
    refine eq_one_of_forall_apply_eq hsq fun c hc w hw => ?_
    by_cases hca : c = (a : K[X])
    · subst hca
      rw [hpowa p w hw, hbp]
      rfl
    · exact hpowo p c hc hca w hw
  have hgsub : (⟨g, hg⟩ : supportedUnitary B x {(a : K[X])}) ^ p = 1 :=
    Subtype.ext (by simpa using hgp)
  have hcard := not_dvd_card_orbitFactor_exceptional H hp hp3 a hself hbad
  rw [hsupp] at hcard
  have hord : orderOf (⟨g, hg⟩ : supportedUnitary B x {(a : K[X])}) = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hgsub
    have h2 := orderOf_dvd_natCard (⟨g, hg⟩ : supportedUnitary B x {(a : K[X])})
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hcard
  have hg1 : g = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hord)
  rw [← hgb (a : K[X]) a.2 rfl v hv, hg1]
  rfl

theorem commute_of_scalar_on_good (H : UnitaryPrimaryData hK.bar B x) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {Y b : LinearMap.GeneralLinearGroup K V} (hY : Y ∈ unitaryCentralizer B x)
    (hb : b ∈ unitaryCentralizer B x) (hbp : b ^ p = 1)
    (hscal : ∀ a : primaryFactors (x : Module.End K V), IsGoodBlock hK x a →
      ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        (Y : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)) :
    Commute Y b := by
  have hsq := H.squarefree
  have hYc : Commute (Y : Module.End K V) (x : Module.End K V) := (mem_unitaryCentralizer.mp hY).2
  have hbc : Commute (b : Module.End K V) (x : Module.End K V) := (mem_unitaryCentralizer.mp hb).2
  refine Units.ext (ext_primaryComponent hsq fun c hc v hv => ?_)
  change (Y : Module.End K V) ((b : Module.End K V) v) =
    (b : Module.End K V) ((Y : Module.End K V) v)
  set ca : primaryFactors (x : Module.End K V) := ⟨c, hc⟩ with hca
  have hbv : (b : Module.End K V) v ∈ primaryComponent (x : Module.End K V) c :=
    apply_mem_primaryComponent hbc hv
  by_cases hgood : IsGoodBlock hK x ca
  · obtain ⟨cs, hcs⟩ := hscal ca hgood
    have e1 := hcs ⟨(b : Module.End K V) v, hbv⟩
    have e2 := hcs ⟨v, hv⟩
    have e3 := apply_smul_primaryComponent (a := c) hbc cs ⟨v, hv⟩
    change (Y : Module.End K V) ((b : Module.End K V) v) = _ at e1
    change (Y : Module.End K V) v = _ at e2
    rw [e1, e2, e3]
  · by_cases hm : 2 ≤ primaryMultiplicity (x : Module.End K V) c
    ·
      have hself : dualPoly hK.bar c = c := by
        by_contra hne
        exact hgood ⟨hm, fun h => absurd h hne⟩
      have hbad : (primaryMultiplicity (x : Module.End K V) c, ℓ ^ (f * c.natDegree)) ∈
          ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
        by_contra hnot
        exact hgood ⟨hm, fun _ => hnot⟩
      have hbtriv := apply_eq_of_exceptional H hp hp3 hb hbp ca hself hbad v hv
      have hYv : (Y : Module.End K V) v ∈ primaryComponent (x : Module.End K V) c :=
        apply_mem_primaryComponent hYc hv
      have hbtriv' := apply_eq_of_exceptional H hp hp3 hb hbp ca hself hbad _ hYv
      rw [hbtriv, hbtriv']
    · have hm1 : primaryMultiplicity (x : Module.End K V) c ≤ 1 := by omega
      have : Fact (Irreducible c) := ⟨irreducible_of_mem_primaryFactors hc⟩
      have hYr : (Y : Module.End K V) ∈ commutant (x : Module.End K V) := (mem_commutant _).mpr hYc
      have hbr : (b : Module.End K V) ∈ commutant (x : Module.End K V) := (mem_commutant _).mpr hbc
      have hcomm := End_commute_of_finrank_le_one (E := AdjoinRoot c)
        (W := primaryComponent (x : Module.End K V) c) hm1
        (commutantRestrict c ⟨Y, hYr⟩) (commutantRestrict c ⟨b, hbr⟩)
      exact congrArg (fun T : Module.End (AdjoinRoot c) (primaryComponent (x : Module.End K V) c) =>
        ((T ⟨v, hv⟩ : primaryComponent (x : Module.End K V) c) : V)) hcomm.eq

end Exceptional

section Fixed

theorem reverse_X_sub_C_one : (X - C (1 : K) : K[X]).reverse = 1 - X := by
  have h : (X - C (1 : K) : K[X]) = X + C (-1) := by simp [sub_eq_add_neg]
  have hX : (X : K[X]).reverse = 1 := by
    have h1 := Polynomial.reverse_mul_X (1 : K[X])
    rw [one_mul] at h1
    rw [h1]
    simpa using Polynomial.reverse_C (1 : K)
  rw [h, Polynomial.reverse_add_C, hX]
  simp [sub_eq_add_neg]

theorem dualPoly_X_sub_C_one (σ : K →+* K) : dualPoly σ (X - C (1 : K) : K[X]) = X - C 1 := by
  unfold dualPoly
  have h1 : ((X - C (1 : K) : K[X]).map σ) = X - C 1 := by simp
  have h2 : (X - C (1 : K) : K[X]).coeff 0 = -1 := by simp
  rw [h1, h2, reverse_X_sub_C_one, map_neg, map_one, inv_neg, inv_one]
  simp [sub_eq_add_neg, add_comm]

omit [FiniteDimensional K V] in
theorem primaryComponent_X_sub_C_one (x : Module.End K V) :
    primaryComponent x (X - C (1 : K)) = LinearMap.ker (x - 1) := by
  unfold primaryComponent
  simp

theorem primaryMultiplicity_X_sub_C_one (x : Module.End K V) :
    primaryMultiplicity x (X - C (1 : K)) =
      Module.finrank K (primaryComponent x (X - C (1 : K))) := by
  have : Fact (Irreducible (X - C (1 : K))) := ⟨irreducible_X_sub_C 1⟩
  have h := finrank_primaryComponent x (X - C (1 : K))
  rw [natDegree_X_sub_C, one_mul] at h
  exact h.symm

omit [FiniteDimensional K V] in
theorem isGoodBlock_X_sub_C_one {hK : UnitaryFieldData ℓ f K}
    {x : LinearMap.GeneralLinearGroup K V}
    (hmem : (X - C (1 : K) : K[X]) ∈ primaryFactors (x : Module.End K V))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (X - C (1 : K)))
    (hexc : (primaryMultiplicity (x : Module.End K V) (X - C (1 : K)), ℓ ^ f) ∉
      ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))) :
    IsGoodBlock hK x ⟨X - C (1 : K), hmem⟩ := by
  refine ⟨hm, fun _ => ?_⟩
  have hd : (X - C (1 : K) : K[X]).natDegree = 1 := natDegree_X_sub_C 1
  show (primaryMultiplicity (x : Module.End K V) (X - C (1 : K)),
    ℓ ^ (f * (X - C (1 : K) : K[X]).natDegree)) ∉ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))
  rw [hd, mul_one]
  exact hexc

end Fixed

end CFSG.RankThree.PartOne.KCUnitary
