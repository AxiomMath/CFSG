module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec11.R2No

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

abbrev V2 : Type := Multiplicative (Fin 2 → ZMod 3)

@[expose] def SwP (P : Mat2) : Prop :=
  (P * P) 0 0 = 0 ∧ (P * P) 1 1 = 0 ∧ (P * P) 0 1 ≠ 0 ∧ (P * P) 1 0 ≠ 0

instance : DecidablePred SwP := fun P =>
  inferInstanceAs
    (Decidable ((P * P) 0 0 = 0 ∧ (P * P) 1 1 = 0 ∧ (P * P) 0 1 ≠ 0 ∧ (P * P) 1 0 ≠ 0))

theorem anticomm : ∀ P Φ : Mat2, SwP P → Φ * P = -(P * Φ) → Φ = 0 := by decide +kernel

theorem span_pair : ∀ (P : Mat2) (v w : Fin 2 → ZMod 3), SwP P → v ≠ 0 →
    ∃ a b : ZMod 3, w = a • v + b • P.mulVec v := by decide +kernel

theorem invariant_subgroup {P : Mat2} (hP : SwP P) (S : Subgroup V2)
    (hS : ∀ v ∈ S, Multiplicative.ofAdd (P.mulVec (Multiplicative.toAdd v)) ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvS, hv1⟩ : ∃ v ∈ S, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((Subgroup.eq_bot_iff_forall S).mpr hcon)
  rw [eq_top_iff]
  intro w _
  have hv0 : Multiplicative.toAdd v ≠ 0 := fun h => hv1 (by
    have := congrArg Multiplicative.ofAdd h
    simpa using this)
  obtain ⟨a, b, hab⟩ := span_pair P (Multiplicative.toAdd v) (Multiplicative.toAdd w) hP hv0
  have hPv := hS v hvS
  have hsm : ∀ (c : ZMod 3) (x : Fin 2 → ZMod 3),
      Multiplicative.ofAdd (c • x) = (Multiplicative.ofAdd x) ^ c.val := fun c x => by
    rw [← ofAdd_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  have hw : w = v ^ a.val * (Multiplicative.ofAdd (P.mulVec (Multiplicative.toAdd v))) ^ b.val := by
    have h1 : w = Multiplicative.ofAdd (Multiplicative.toAdd w) := rfl
    rw [h1, hab, ofAdd_add, hsm, hsm]
    rfl
  rw [hw]
  exact S.mul_mem (S.pow_mem hvS _) (S.pow_mem hPv _)

theorem exists_matrix (φ : V2 →* V2) :
    ∃ Φ : Mat2, ∀ v : Fin 2 → ZMod 3,
      Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) = Φ.mulVec v := by
  let f : (Fin 2 → ZMod 3) →+ (Fin 2 → ZMod 3) :=
    { toFun := fun v => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun v w => by simp [ofAdd_add] }
  refine ⟨LinearMap.toMatrix' (f.toZModLinearMap 3), fun v => ?_⟩
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem mat_ext {M N : Mat2} (h : ∀ v : Fin 2 → ZMod 3, M.mulVec v = N.mulVec v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem V2_pow_three (v : V2) : v ^ 3 = 1 := by
  rw [← ofAdd_toAdd v, ← ofAdd_nsmul]
  have : (3 : ℕ) • (Multiplicative.toAdd v) = 0 := by
    funext i
    simp [Pi.smul_apply]
    decide +revert
  rw [this]
  rfl

theorem V2prod_pow_three (v : V2 × V2) : v ^ 3 = 1 := by
  ext <;> simp [V2_pow_three]

theorem card_range_le {R : Type} [Group R] [Finite R] (β π : R →* V2)
    (hgen : ∃ z c r : R, ∀ x : R, ∃ s t i : ℕ, x = z ^ s * c ^ t * r ^ i) :
    Nat.card (β.prod π).range ≤ 27 := by
  obtain ⟨z, c, r, hx⟩ := hgen
  let φ := β.prod π
  let f : Fin 3 × Fin 3 × Fin 3 → φ.range := fun p =>
    ⟨φ z ^ (p.1 : ℕ) * φ c ^ (p.2.1 : ℕ) * φ r ^ (p.2.2 : ℕ),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (MonoidHom.mem_range.mpr ⟨z, rfl⟩) _)
        (Subgroup.pow_mem _ (MonoidHom.mem_range.mpr ⟨c, rfl⟩) _)) (Subgroup.pow_mem _ (MonoidHom.mem_range.mpr ⟨r, rfl⟩) _)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨w, x, rfl⟩
    obtain ⟨s, t, i, rfl⟩ := hx x
    refine ⟨(⟨s % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨t % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    simp only [f, map_mul, map_pow]
    rw [← pow_eq_pow_mod s (V2prod_pow_three (φ z)), ← pow_eq_pow_mod t (V2prod_pow_three (φ c)),
      ← pow_eq_pow_mod i (V2prod_pow_three (φ r))]
  calc Nat.card φ.range ≤ Nat.card (Fin 3 × Fin 3 × Fin 3) := Nat.card_le_card_of_surjective f hsurj
    _ = 27 := by simp

theorem card_V2 : Nat.card V2 = 9 := by
  rw [Nat.card_eq_fintype_card]
  simp [V2]

theorem card_V2prod : Nat.card (V2 × V2) = 81 := by
  rw [Nat.card_prod, card_V2]

theorem range_pi_eq_top {R : Type} [Group R] {P : Mat2} (hP : SwP P) (π : R →* V2)
    (hπ : ∃ x, π x ≠ 1) (σ : R → R)
    (hσπ : ∀ x, π (σ x) = Multiplicative.ofAdd (P.mulVec (Multiplicative.toAdd (π x)))) :
    π.range = ⊤ := by
  rcases invariant_subgroup hP π.range (by
    rintro v ⟨x, rfl⟩
    exact ⟨σ x, hσπ x⟩) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := hπ
    have : π x ∈ π.range := ⟨x, rfl⟩
    rw [h] at this
    exact hx (Subgroup.mem_bot.mp this)
  · exact h

theorem factor_through {R : Type} [Group R] [Finite R] {P : Mat2} (hP : SwP P)
    (β π : R →* V2) (hπ : ∃ x, π x ≠ 1) (σ : R → R)
    (hσπ : ∀ x, π (σ x) = Multiplicative.ofAdd (P.mulVec (Multiplicative.toAdd (π x))))
    (hσβ : ∀ x, β (σ x) = Multiplicative.ofAdd (-(P.mulVec (Multiplicative.toAdd (β x)))))
    (hgen : ∃ z c r : R, ∀ x : R, ∃ s t i : ℕ, x = z ^ s * c ^ t * r ^ i) :
    ∀ x y, π x = π y → β x = β y := by
  set I : Subgroup (V2 × V2) := (β.prod π).range with hI
  set I1 : Subgroup V2 := I.comap (MonoidHom.inl V2 V2) with hI1
  have hmemI1 : ∀ u : V2, u ∈ I1 ↔ ∃ x, β x = u ∧ π x = 1 := by
    intro u
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    · rintro ⟨x, h1, h2⟩
      exact ⟨x, by simp [h1, h2]⟩
  have hinv : ∀ v ∈ I1, Multiplicative.ofAdd (P.mulVec (Multiplicative.toAdd v)) ∈ I1 := by
    intro v hv
    obtain ⟨x, h1, h2⟩ := (hmemI1 v).mp hv
    have h3 : Multiplicative.ofAdd (-(P.mulVec (Multiplicative.toAdd v))) ∈ I1 := by
      refine (hmemI1 _).mpr ⟨σ x, ?_, ?_⟩
      · rw [hσβ, h1]
      · rw [hσπ, h2]
        simp
    rw [ofAdd_neg] at h3
    exact (Subgroup.inv_mem_iff I1).mp h3
  have hI1' : I1 = ⊥ := by
    rcases invariant_subgroup hP I1 hinv with h | h
    · exact h
    · exfalso
      have hπtop := range_pi_eq_top hP π hπ σ hσπ
      have hItop : I = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨u, v⟩ -
        have hv : v ∈ π.range := hπtop ▸ Subgroup.mem_top v
        obtain ⟨x, rfl⟩ := hv
        have hu : u * (β x)⁻¹ ∈ I1 := h ▸ Subgroup.mem_top _
        obtain ⟨y, hy1, hy2⟩ := (hmemI1 _).mp hu
        refine ⟨y * x, ?_⟩
        simp [hy1, hy2]
      have h81 : Nat.card I = 81 := by
        rw [hItop, Nat.card_congr Subgroup.topEquiv.toEquiv, card_V2prod]
      have := card_range_le β π hgen
      rw [← hI] at this
      omega
  intro x y hxy
  have h5 : β (x * y⁻¹) ∈ I1 := (hmemI1 _).mpr ⟨x * y⁻¹, rfl, by simp [hxy]⟩
  rw [hI1', Subgroup.mem_bot, map_mul, map_inv, mul_inv_eq_one] at h5
  exact h5

theorem core_false {R : Type} [Group R] [Finite R] {P : Mat2} (hP : SwP P)
    (β π : R →* V2) (hβ : ∃ x, β x ≠ 1) (hπ : ∃ x, π x ≠ 1) (σ : R → R)
    (hσπ : ∀ x, π (σ x) = Multiplicative.ofAdd (P.mulVec (Multiplicative.toAdd (π x))))
    (hσβ : ∀ x, β (σ x) = Multiplicative.ofAdd (-(P.mulVec (Multiplicative.toAdd (β x)))))
    (hgen : ∃ z c r : R, ∀ x : R, ∃ s t i : ℕ, x = z ^ s * c ^ t * r ^ i) : False := by
  classical
  have hfac := factor_through hP β π hπ σ hσπ hσβ hgen
  have hsurj : ∀ v : V2, ∃ x, π x = v := fun v => by
    have : v ∈ π.range := range_pi_eq_top hP π hπ σ hσπ ▸ Subgroup.mem_top v
    exact this
  obtain ⟨g, hg⟩ : ∃ g : V2 →* V2, ∀ x, g (π x) = β x := by
    let s : V2 → R := fun v => Classical.choose (hsurj v)
    have hs : ∀ v, π (s v) = v := fun v => Classical.choose_spec (hsurj v)
    refine ⟨{ toFun := fun v => β (s v), map_one' := ?_, map_mul' := ?_ }, ?_⟩
    · have := hfac (s 1) 1 (by rw [hs, map_one])
      simpa using this
    · intro v w
      have := hfac (s (v * w)) (s v * s w) (by rw [hs, map_mul, hs, hs])
      simpa using this
    · intro x
      exact hfac _ _ (hs (π x))
  obtain ⟨Φ, hΦ⟩ := exists_matrix g
  have hβΦ : ∀ x, Multiplicative.toAdd (β x) = Φ.mulVec (Multiplicative.toAdd (π x)) := by
    intro x
    rw [← hg x, ← hΦ]
    simp
  have hanti : Φ * P = -(P * Φ) := by
    apply mat_ext
    intro v
    obtain ⟨x, hx⟩ := hsurj (Multiplicative.ofAdd v)
    have hv : Multiplicative.toAdd (π x) = v := by rw [hx]; rfl
    have h1 := hβΦ (σ x)
    rw [hσβ, hσπ, hv] at h1
    simp only [toAdd_ofAdd] at h1
    have h2 : Multiplicative.toAdd (β x) = Φ.mulVec v := by rw [hβΦ x, hv]
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← h2]
    exact h1.symm
  have hΦ0 := anticomm P Φ hP hanti
  obtain ⟨x, hx⟩ := hβ
  apply hx
  have := hβΦ x
  rw [hΦ0] at this
  simp at this
  exact Multiplicative.toAdd.injective this

theorem exists_equiv_V2 {B : Type} [Group B] (hB : ∀ x y : B, x * y = y * x) {c d : B}
    (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hdc : d ∉ Subgroup.zpowers c)
    (hgenB : ∀ b : B, ∃ i j : ℕ, b = c ^ i * d ^ j) :
    ∃ E : V2 ≃* B, E (Multiplicative.ofAdd (Pi.single 0 1)) = c ∧
      E (Multiplicative.ofAdd (Pi.single 1 1)) = d := by
  have hmm : ∀ a b x y : B, a * b * (x * y) = a * x * (b * y) := by
    intro a b x y
    simp only [mul_assoc]
    rw [← mul_assoc b, hB b x, mul_assoc]
  have hA : ∀ x : B, x ^ 3 = 1 → x ^ 2 = 1 → x = 1 := by
    intro x h3 h2
    have e3 : x ^ 3 = x ^ 2 * x := pow_succ x 2
    rw [h3, h2, one_mul] at e3
    exact e3.symm
  have key : ∀ i j : ℕ, c ^ i * d ^ j = 1 → i % 3 = 0 ∧ j % 3 = 0 := by
    intro i j h
    have hj : j % 3 = 0 := by
      by_contra hne
      have hjj : (j * j) % 3 = 1 := by
        rcases (show j % 3 = 1 ∨ j % 3 = 2 by omega) with h1 | h1 <;>
          simp [Nat.mul_mod, h1]
      have hmem : d ^ j ∈ Subgroup.zpowers c := by
        rw [eq_inv_of_mul_eq_one_right h]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i)
      have hdd : d ∈ Subgroup.zpowers c := by
        have h2 := Subgroup.pow_mem _ hmem j
        rw [← pow_mul, pow_eq_pow_mod (j * j) hd3, hjj, pow_one] at h2
        exact h2
      exact hdc hdd
    have hdj : d ^ j = 1 := by rw [pow_eq_pow_mod j hd3, hj, pow_zero]
    rw [hdj, mul_one] at h
    have hi : i % 3 = 0 := by
      by_contra hne
      apply hc1
      rcases (show i % 3 = 1 ∨ i % 3 = 2 by omega) with h1 | h1
      · have hci : c ^ i = c := by rw [pow_eq_pow_mod i hc3, h1, pow_one]
        rw [hci] at h
        exact h
      · have hci : c ^ i = c ^ 2 := by rw [pow_eq_pow_mod i hc3, h1]
        rw [hci] at h
        exact hA c hc3 h
    exact ⟨hi, hj⟩
  let e : V2 →* B :=
    { toFun := fun v => c ^ (Multiplicative.toAdd v 0).val * d ^ (Multiplicative.toAdd v 1).val
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply, ZMod.val_add]
        rw [← pow_eq_pow_mod _ hc3, ← pow_eq_pow_mod _ hd3, pow_add, pow_add]
        exact hmm _ _ _ _ }
  have he : ∀ v : V2,
      e v = c ^ (Multiplicative.toAdd v 0).val * d ^ (Multiplicative.toAdd v 1).val :=
    fun v => rfl
  have hinj : Function.Injective e := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [he] at hv
    obtain ⟨h0, h1⟩ := key _ _ hv
    have ha : (Multiplicative.toAdd v) 0 = 0 :=
      (ZMod.val_eq_zero _).mp (by have := ZMod.val_lt ((Multiplicative.toAdd v) 0); omega)
    have hb : (Multiplicative.toAdd v) 1 = 0 :=
      (ZMod.val_eq_zero _).mp (by have := ZMod.val_lt ((Multiplicative.toAdd v) 1); omega)
    have hk : ∀ k : Fin 2, (Multiplicative.toAdd v) k = 0 := Fin.forall_fin_two.2 ⟨ha, hb⟩
    have hv0 : Multiplicative.toAdd v = 0 := funext hk
    exact Multiplicative.toAdd.injective (hv0.trans rfl)
  have hsurj : Function.Surjective e := by
    intro b
    obtain ⟨i, j, rfl⟩ := hgenB b
    refine ⟨Multiplicative.ofAdd ![(i : ZMod 3), (j : ZMod 3)], ?_⟩
    rw [he]
    simp only [toAdd_ofAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      ZMod.val_natCast]
    rw [pow_eq_pow_mod i hc3, pow_eq_pow_mod j hd3]
  have hv1 : ZMod.val (1 : ZMod 3) = 1 := rfl
  refine ⟨MulEquiv.ofBijective e ⟨hinj, hsurj⟩, ?_, ?_⟩
  · show e (Multiplicative.ofAdd (Pi.single 0 1)) = c
    rw [he]
    simp [hv1]
  · show e (Multiplicative.ofAdd (Pi.single 1 1)) = d
    rw [he]
    simp [hv1]

theorem zpow_ne_one_of_cast {B : Type} [Group B] {d : B} (hd3 : d ^ 3 = 1) {k : ℤ}
    (h : d ^ k ≠ 1) : (k : ZMod 3) ≠ 0 := by
  intro hk
  apply h
  have h3 : (3 : ℤ) ∣ k := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mp hk
    exact_mod_cast this
  obtain ⟨m, rfl⟩ := h3
  rw [_root_.zpow_mul]
  have : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd3
  rw [this, _root_.one_zpow]

theorem core_false_abs {R B : Type} [Group R] [Finite R] [Group B]
    (hB : ∀ x y : B, x * y = y * x)
    {c d : B} (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hdc : d ∉ Subgroup.zpowers c) (hgenB : ∀ b : B, ∃ i j : ℕ, b = c ^ i * d ^ j)
    (τ : B →* B) (hτc : τ (τ c) ∈ Subgroup.zpowers d) (hτc1 : τ (τ c) ≠ 1)
    (hτd : τ (τ d) ∈ Subgroup.zpowers c) (hτd1 : τ (τ d) ≠ 1)
    (β π : R →* B) (hβ : ∃ x, β x ≠ 1) (hπ : ∃ x, π x ≠ 1) (σ : R → R)
    (hσπ : ∀ x, π (σ x) = τ (π x)) (hσβ : ∀ x, β (σ x) = (τ (β x))⁻¹)
    (hgen : ∃ z c' r : R, ∀ x : R, ∃ s t i : ℕ, x = z ^ s * c' ^ t * r ^ i) : False := by
  obtain ⟨E, hEc, hEd⟩ := exists_equiv_V2 hB hc1 hc3 hd3 hdc hgenB
  let τ' : V2 →* V2 := E.symm.toMonoidHom.comp (τ.comp E.toMonoidHom)
  obtain ⟨P, hP⟩ := exists_matrix τ'
  have hτ' : ∀ v : V2, τ' v = Multiplicative.ofAdd (P.mulVec (Multiplicative.toAdd v)) := by
    intro v
    have h := hP (Multiplicative.toAdd v)
    rw [ofAdd_toAdd] at h
    rw [← h, ofAdd_toAdd]
  have hτ'E : ∀ y : B, τ' (E.symm y) = E.symm (τ y) := by
    intro y
    simp [τ']
  have hsq : ∀ v : Fin 2 → ZMod 3, Multiplicative.toAdd (τ' (τ' (Multiplicative.ofAdd v))) =
      (P * P).mulVec v := by
    intro v
    rw [hτ', toAdd_ofAdd, hτ', toAdd_ofAdd, Matrix.mulVec_mulVec]
    rfl
  have hE0 : E.symm c = Multiplicative.ofAdd (Pi.single 0 1) := by
    rw [← hEc, MulEquiv.symm_apply_apply]
  have hE1 : E.symm d = Multiplicative.ofAdd (Pi.single 1 1) := by
    rw [← hEd, MulEquiv.symm_apply_apply]
  have hτ'0 : τ' (Multiplicative.ofAdd (Pi.single 0 1)) = E.symm (τ c) := by
    rw [← hE0, hτ'E]
  have hτ'1 : τ' (Multiplicative.ofAdd (Pi.single 1 1)) = E.symm (τ d) := by
    rw [← hE1, hτ'E]
  have hcolmat : ∀ (M : Mat2) (j : Fin 2) (i : Fin 2), (M.mulVec (Pi.single j 1)) i = M i j := by
    intro M j i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  have hS0 : (P * P) 0 0 = 0 ∧ (P * P) 1 0 ≠ 0 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hτc
    have h1 : τ' (τ' (Multiplicative.ofAdd (Pi.single 0 1))) =
        Multiplicative.ofAdd (k • (Pi.single 1 1 : Fin 2 → ZMod 3)) := by
      rw [hτ'0, hτ'E, ← hk, map_zpow, hE1, ofAdd_zsmul]
    have h2 := hsq (Pi.single 0 1)
    rw [h1, toAdd_ofAdd] at h2
    have h3 := congrFun h2 0
    have h4 := congrFun h2 1
    rw [hcolmat] at h3 h4
    refine ⟨by rw [← h3]; simp, ?_⟩
    rw [← h4]
    have hk1 : d ^ k ≠ 1 := by rw [hk]; exact hτc1
    have := zpow_ne_one_of_cast hd3 hk1
    simpa using this
  have hS1 : (P * P) 1 1 = 0 ∧ (P * P) 0 1 ≠ 0 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hτd
    have h1 : τ' (τ' (Multiplicative.ofAdd (Pi.single 1 1))) =
        Multiplicative.ofAdd (k • (Pi.single 0 1 : Fin 2 → ZMod 3)) := by
      rw [hτ'1, hτ'E, ← hk, map_zpow, hE0, ofAdd_zsmul]
    have h2 := hsq (Pi.single 1 1)
    rw [h1, toAdd_ofAdd] at h2
    have h3 := congrFun h2 0
    have h4 := congrFun h2 1
    rw [hcolmat] at h3 h4
    refine ⟨by rw [← h4]; simp, ?_⟩
    rw [← h3]
    have hk1 : c ^ k ≠ 1 := by rw [hk]; exact hτd1
    have := zpow_ne_one_of_cast hc3 hk1
    simpa using this
  have hP' : SwP P := ⟨hS0.1, hS1.1, hS1.2, hS0.2⟩
  refine core_false hP' (E.symm.toMonoidHom.comp β) (E.symm.toMonoidHom.comp π) ?_ ?_ σ ?_ ?_ hgen
  · obtain ⟨x, hx⟩ := hβ
    exact ⟨x, fun h => hx (E.symm.injective (by simpa using h))⟩
  · obtain ⟨x, hx⟩ := hπ
    exact ⟨x, fun h => hx (E.symm.injective (by simpa using h))⟩
  · intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hσπ, ← hτ', hτ'E]
  · intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hσβ, map_inv, ← hτ'E, hτ', ofAdd_neg]

end CFSG.RankThree.PartTwo.Sec11.R2No
