module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup
open scoped Pointwise

section KleinFour

variable {C : Type*} [Group C]

private def kleinFour {z t : C} (hz2 : z ^ 2 = 1) (ht2 : t ^ 2 = 1) (hzt : z * t = t * z) :
    Subgroup C where
  carrier := {1, z, t, z * t}
  one_mem' := by simp
  mul_mem' := by
    have i₁ : z * z = 1 := by rwa [← pow_two]
    have i₂ : t * t = 1 := by rwa [← pow_two]
    have e1 : z * (z * t) = t := by rw [← mul_assoc, i₁, one_mul]
    have e3 : z * t * z = t := by rw [hzt, mul_assoc, i₁, mul_one]
    have e4 : z * t * t = z := by rw [mul_assoc, i₂, mul_one]
    have e2 : t * (z * t) = z := by
      calc t * (z * t) = (t * z) * t := (mul_assoc _ _ _).symm
        _ = (z * t) * t := by rw [← hzt]
        _ = z := e4
    have e5 : z * t * (z * t) = 1 := by
      calc z * t * (z * t) = (z * t * z) * t := (mul_assoc _ _ _).symm
        _ = t * t := by rw [e3]
        _ = 1 := i₂
    have f1 : t * z = z * t := hzt.symm
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, i₁, i₂, e1, e2, e3,
        e4, e5, f1, true_or, or_true]
  inv_mem' := by
    have i₁ : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    have i₂ : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    rintro a (rfl | rfl | rfl | rfl)
    · simp
    · simp [i₁]
    · simp [i₂]
    · show (z * t)⁻¹ ∈ ({1, z, t, z * t} : Set C)
      rw [mul_inv_rev, i₁, i₂]
      exact Or.inr (Or.inr (Or.inr hzt.symm))

private theorem mem_kleinFour {z t : C} (hz2 : z ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hzt : z * t = t * z) {x : C} :
    x ∈ kleinFour hz2 ht2 hzt ↔ x = 1 ∨ x = z ∨ x = t ∨ x = z * t := Iff.rfl

private theorem card_kleinFour {z t : C} (hz2 : z ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hzt : z * t = t * z) (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hne : z ≠ t) :
    Nat.card (kleinFour hz2 ht2 hzt) = 4 := by
  have hzz : z * z = 1 := by rwa [← pow_two]
  have hztne1 : z * t ≠ 1 := fun h => hne (by
    have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact (inv_eq_of_mul_eq_one_right hzz).symm)
  have hzne : z ≠ z * t := fun h => ht1 (by
    have := congrArg (fun w => z⁻¹ * w) h
    simpa using this.symm)
  have htne : t ≠ z * t := fun h => hz1 (by
    have := congrArg (fun w => w * t⁻¹) h
    simpa using this.symm)
  have h1 : Nat.card (kleinFour hz2 ht2 hzt) = ({1, z, t, z * t} : Set C).ncard :=
    Nat.card_coe_set_eq ({1, z, t, z * t} : Set C)
  rw [h1, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair htne]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, hzne⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz1.symm, ht1.symm, fun h => hztne1 h.symm⟩

private theorem isKleinFour_kleinFour {z t : C} (hz2 : z ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hzt : z * t = t * z) (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hne : z ≠ t) :
    IsKleinFour (kleinFour hz2 ht2 hzt) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨card_kleinFour hz2 ht2 hzt hz1 ht1 hne, ?_⟩
  have hzV : z ∈ kleinFour hz2 ht2 hzt := (mem_kleinFour hz2 ht2 hzt).mpr (Or.inr (Or.inl rfl))
  have : Nontrivial (kleinFour hz2 ht2 hzt) :=
    ⟨⟨⟨z, hzV⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  refine (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_
  intro g hg
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    rcases (mem_kleinFour hz2 ht2 hzt).mp g.2 with h | h | h | h
    · simp [h]
    · simpa [h] using hz2
    · simpa [h] using ht2
    · simp only [Subgroup.coe_pow, Subgroup.coe_one, h]
      rw [Commute.mul_pow hzt, hz2, ht2, one_mul]
  exact orderOf_eq_prime hg2 hg

private theorem odd_card_oddCore_two (D : Type*) [Group D] [Finite D] :
    Odd (Nat.card (CFSG.oddCore D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : CFSG.oddCore D = CFSG.pPrimeCore 2 D := by
    unfold CFSG.oddCore CFSG.pPrimeCore
    congr 1
    ext N
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

private theorem factorization_two_eq_two {n : ℕ} (h4 : 2 ^ 2 ∣ n ∧ ¬ 2 ^ 3 ∣ n) :
    n.factorization 2 = 2 := by
  have hne : n ≠ 0 := by
    rintro rfl
    exact h4.2 (dvd_zero _)
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp h4.1
  have h2 : ¬ 3 ≤ n.factorization 2 := fun h =>
    h4.2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mpr h)
  omega

private theorem exists_conj_aux [Finite C] {z t : C} (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hne : z ≠ t)
    (hzt : z * t = t * z) (V : Subgroup C)
    (hV : ∀ x, x ∈ V ↔ x = 1 ∨ x = z ∨ x = t ∨ x = z * t) (hVcard : Nat.card V = 4)
    (h4 : 2 ^ 2 ∣ Nat.card C ∧ ¬ 2 ^ 3 ∣ Nat.card C) (hNC : ¬ CFSG.HasNormalPComplement 2 C) :
    ∃ x : C, x * z * x⁻¹ = t ∨ x * z * x⁻¹ = z * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcontra
  push Not at hcontra
  have hfact : (Nat.card C).factorization 2 = 2 := factorization_two_eq_two h4
  let S₀ : Sylow 2 C := Sylow.ofCard V (by rw [hVcard, hfact]; norm_num)
  have hS₀ : (S₀ : Subgroup C) = V := rfl
  have hzV : z ∈ V := (hV z).mpr (Or.inr (Or.inl rfl))
  have htV : t ∈ V := (hV t).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hVA : V ≤ normalizer (V : Set C) := Subgroup.le_normalizer
  have hconj : ∀ n ∈ normalizer (V : Set C), ∀ v ∈ V, n * v * n⁻¹ ∈ V :=
    fun n hn v hv => (mem_normalizer_iff.mp hn v).mp hv
  have hAz : ∀ n ∈ normalizer (V : Set C), n * z * n⁻¹ = z := by
    intro n hn
    rcases (hV _).mp (hconj n hn z hzV) with h | h | h | h
    · exact absurd (by simpa using h) hz1
    · exact h
    · exact absurd h (hcontra n).1
    · exact absurd h (hcontra n).2
  have hAt : ∀ n ∈ normalizer (V : Set C), n * t * n⁻¹ = t ∨ n * t * n⁻¹ = z * t := by
    intro n hn
    rcases (hV _).mp (hconj n hn t htV) with h | h | h | h
    · exact absurd (by simpa using h) ht1
    · exfalso
      apply hne
      have h1 := hAz n⁻¹ ((normalizer (V : Set C)).inv_mem hn)
      calc z = n⁻¹ * z * n⁻¹⁻¹ := h1.symm
        _ = n⁻¹ * (n * t * n⁻¹) * n := by rw [h]; simp
        _ = t := by group
    · exact Or.inl h
    · exact Or.inr h
  have hVt : ∀ v ∈ V, v * t = t * v := by
    intro v hv
    rcases (hV v).mp hv with rfl | rfl | rfl | rfl
    · simp
    · exact hzt
    · rfl
    · calc z * t * t = t * z * t := by rw [hzt]
        _ = t * (z * t) := by rw [mul_assoc]
  have hAcomm_t : ∀ n ∈ normalizer (V : Set C), n * t = t * n := by
    let tA : normalizer (V : Set C) := ⟨t, hVA htV⟩
    let zA : normalizer (V : Set C) := ⟨z, hVA hzV⟩
    have hconjA : conjugatesOf tA ⊆ {tA, zA * tA} := by
      intro b hb
      obtain ⟨c, hc⟩ := isConj_iff.mp hb
      rcases hAt c c.2 with h | h
      · left; rw [← hc]; exact Subtype.ext h
      · right; rw [← hc]; exact Subtype.ext h
    have hidx_le : (centralizer ({tA} : Set (normalizer (V : Set C)))).index ≤ 2 := by
      rw [Subgroup.index_centralizer_eq_ncard]
      calc (conjugatesOf tA).ncard ≤ ({tA, zA * tA} : Set (normalizer (V : Set C))).ncard :=
            Set.ncard_le_ncard hconjA (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    have hVA' : V.subgroupOf (normalizer (V : Set C)) ≤
        centralizer ({tA} : Set (normalizer (V : Set C))) := by
      intro g hg
      rw [mem_subgroupOf] at hg
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (hVt g hg)
    have hdvd : (centralizer ({tA} : Set (normalizer (V : Set C)))).index ∣
        (V.subgroupOf (normalizer (V : Set C))).index := Subgroup.index_dvd_of_le hVA'
    have hodd : Odd (V.subgroupOf (normalizer (V : Set C))).index := by
      have h1 := Subgroup.index_mul_card (V.subgroupOf (normalizer (V : Set C)))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hVcard] at h1
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨k, hk⟩ := hev
      apply h4.2
      have hd : Nat.card (normalizer (V : Set C)) ∣ Nat.card C :=
        Subgroup.card_subgroup_dvd_card _
      refine Dvd.dvd.trans ⟨k, ?_⟩ hd
      rw [← h1, hk]
      ring
    have hidx_odd : Odd (centralizer ({tA} : Set (normalizer (V : Set C)))).index :=
      hodd.of_dvd_nat hdvd
    have hpos : 0 < (centralizer ({tA} : Set (normalizer (V : Set C)))).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hidx1 : (centralizer ({tA} : Set (normalizer (V : Set C)))).index = 1 := by
      obtain ⟨k, hk⟩ := hidx_odd
      omega
    have htop : centralizer ({tA} : Set (normalizer (V : Set C))) = ⊤ :=
      Subgroup.index_eq_one.mp hidx1
    intro n hn
    have hmem : (⟨n, hn⟩ : normalizer (V : Set C)) ∈
        centralizer ({tA} : Set (normalizer (V : Set C))) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [mem_centralizer_singleton_iff] at hmem
    exact congrArg Subtype.val hmem
  have hAcomm_z : ∀ n ∈ normalizer (V : Set C), n * z = z * n := by
    intro n hn
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [hAz n hn]
  have hcentral : (S₀ : Subgroup C) ≤
      CFSG.centerIn (normalizer ((S₀ : Subgroup C) : Set C)) := by
    intro v hv
    rw [hS₀] at hv ⊢
    unfold CFSG.centerIn
    rw [Subgroup.mem_inf]
    refine ⟨hVA hv, ?_⟩
    rw [mem_centralizer_iff]
    intro n hn
    rcases (hV v).mp hv with rfl | rfl | rfl | rfl
    · simp
    · exact hAcomm_z n hn
    · exact hAcomm_t n hn
    · calc n * (z * t) = (n * z) * t := (mul_assoc _ _ _).symm
        _ = (z * n) * t := by rw [hAcomm_z n hn]
        _ = z * (n * t) := mul_assoc _ _ _
        _ = z * (t * n) := by rw [hAcomm_t n hn]
        _ = (z * t) * n := (mul_assoc _ _ _).symm
  exact hNC (CFSG.hasNormalPComplement_of_sylow_le_center_normalizer 2 S₀ hcentral)

end KleinFour

theorem exists_conj_of_not_hasNormalPComplement {C : Type*} [Group C] [Finite C] {z t : C}
    (hz2 : z ^ 2 = 1) (ht2 : t ^ 2 = 1) (hzt : z * t = t * z) (hz1 : z ≠ 1) (ht1 : t ≠ 1)
    (hne : z ≠ t) (h4 : 2 ^ 2 ∣ Nat.card C ∧ ¬ 2 ^ 3 ∣ Nat.card C)
    (hNC : ¬ CFSG.HasNormalPComplement 2 C) :
    ∃ x : C, x * z * x⁻¹ = t ∨ x * z * x⁻¹ = z * t :=
  exists_conj_aux hz1 ht1 hne hzt (kleinFour hz2 ht2 hzt) (fun _ => mem_kleinFour hz2 ht2 hzt)
    (card_kleinFour hz2 ht2 hzt hz1 ht1 hne) h4 hNC

theorem not_hasNormalPComplement_quotient_oddCore {C : Type*} [Group C] [Finite C]
    (h : ¬ CFSG.HasNormalPComplement 2 C) :
    ¬ CFSG.HasNormalPComplement 2 (C ⧸ CFSG.oddCore C) := by
  rintro ⟨Xb, hXbn, hcop, hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply h
  let π : C →* C ⧸ CFSG.oddCore C := QuotientGroup.mk' (CFSG.oddCore C)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let X : Subgroup C := Xb.comap π
  have hXn : X.Normal := hXbn.comap π
  have hidx : X.index = Xb.index := Subgroup.index_comap_of_surjective Xb hπ
  have hXcard : Nat.card X = Nat.card Xb * Nat.card (CFSG.oddCore C) := by
    have h1 := Subgroup.card_mul_index X
    have h2 := Subgroup.card_mul_index Xb
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore C)
    have hpos : 0 < Xb.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    have : Nat.card X * Xb.index = (Nat.card Xb * Nat.card (CFSG.oddCore C)) * Xb.index := by
      calc Nat.card X * Xb.index = Nat.card C := h1
        _ = Nat.card (C ⧸ CFSG.oddCore C) * Nat.card (CFSG.oddCore C) := h3
        _ = (Nat.card Xb * Xb.index) * Nat.card (CFSG.oddCore C) := by rw [h2]
        _ = (Nat.card Xb * Nat.card (CFSG.oddCore C)) * Xb.index := by ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hXodd : Odd (Nat.card X) := by
    rw [hXcard]
    exact Odd.mul (Nat.coprime_two_left.mp hcop) (odd_card_oddCore_two C)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hq
  show ∃ (N : Subgroup C) (_ : N.Normal), Nat.Coprime 2 (Nat.card N) ∧ IsPGroup 2 (C ⧸ N)
  exact ⟨X, hXn, Nat.coprime_two_left.mpr hXodd, IsPGroup.of_card (n := j) (by
    rw [← Subgroup.index_eq_card, hidx, Subgroup.index_eq_card]; exact hj)⟩

theorem hasDihedralSylowTwo_quotient_oddCore {C : Type*} [Group C] [Finite C] {z t : C}
    (hz2 : z ^ 2 = 1) (ht2 : t ^ 2 = 1) (hzt : z * t = t * z) (hz1 : z ≠ 1) (ht1 : t ≠ 1)
    (hne : z ≠ t) (h4 : 2 ^ 2 ∣ Nat.card C ∧ ¬ 2 ^ 3 ∣ Nat.card C) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo (C ⧸ CFSG.oddCore C) ∧
      (2 ^ 2 ∣ Nat.card (C ⧸ CFSG.oddCore C) ∧ ¬ 2 ^ 3 ∣ Nat.card (C ⧸ CFSG.oddCore C)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd := odd_card_oddCore_two C
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore C)
  refine ⟨?_, ?_, ?_⟩
  · let π : C →* C ⧸ CFSG.oddCore C := QuotientGroup.mk' (CFSG.oddCore C)
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hVcard : Nat.card (kleinFour hz2 ht2 hzt) = 4 :=
      card_kleinFour hz2 ht2 hzt hz1 ht1 hne
    have hfact : (Nat.card C).factorization 2 = 2 := factorization_two_eq_two h4
    let Q : Sylow 2 C := Sylow.ofCard (kleinFour hz2 ht2 hzt) (by rw [hVcard, hfact]; norm_num)
    have hKlein := isKleinFour_kleinFour hz2 ht2 hzt hz1 ht1 hne
    obtain ⟨eV⟩ : Nonempty (kleinFour hz2 ht2 hzt ≃* DihedralGroup 2) :=
      IsKleinFour.nonempty_mulEquiv
    have hinj : Function.Injective (π.domRestrict (kleinFour hz2 ht2 hzt)) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : (a : C) ∈ CFSG.oddCore C := (QuotientGroup.eq_one_iff _).mp ha
      have h2 : orderOf a ∣ Nat.card (CFSG.oddCore C) := by
        have := Subgroup.orderOf_dvd_natCard (CFSG.oddCore C) h1
        rwa [Subgroup.orderOf_coe] at this
      have h3 : orderOf a ∣ 4 := by
        have := orderOf_dvd_natCard a
        rwa [hVcard] at this
      have hcop : Nat.Coprime 4 (Nat.card (CFSG.oddCore C)) :=
        (Nat.coprime_two_left.mpr hOodd).pow_left 2
      have h5 : orderOf a ∣ Nat.gcd 4 (Nat.card (CFSG.oddCore C)) := Nat.dvd_gcd h3 h2
      rw [hcop] at h5
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
    let T' : Sylow 2 (C ⧸ CFSG.oddCore C) := Sylow.mapSurjective hπ Q
    have hT'' : (T' : Subgroup (C ⧸ CFSG.oddCore C)) = (kleinFour hz2 ht2 hzt).map π := rfl
    let e1 : kleinFour hz2 ht2 hzt ≃* (π.domRestrict (kleinFour hz2 ht2 hzt)).range :=
      MonoidHom.ofInjective hinj
    let e2 : (π.domRestrict (kleinFour hz2 ht2 hzt)).range ≃*
        (kleinFour hz2 ht2 hzt).map π :=
      MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ π)
    let eT' : ↥(T' : Subgroup (C ⧸ CFSG.oddCore C)) ≃* DihedralGroup 2 :=
      (MulEquiv.subgroupCongr hT'').trans (e2.symm.trans (e1.symm.trans eV))
    intro S'
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (C ⧸ CFSG.oddCore C) T' S'
    have hS' : (S' : Subgroup (C ⧸ CFSG.oddCore C)) =
        MulAut.conj g • (T' : Subgroup (C ⧸ CFSG.oddCore C)) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    refine ⟨1, le_rfl, ⟨?_⟩⟩
    exact (MulEquiv.subgroupCongr hS').trans
      ((Subgroup.equivSMul (MulAut.conj g) (T' : Subgroup (C ⧸ CFSG.oddCore C))).symm.trans eT')
  · have hcop : Nat.Coprime (2 ^ 2) (Nat.card (CFSG.oddCore C)) :=
      (Nat.coprime_two_left.mpr hOodd).pow_left 2
    rw [hcard] at h4
    exact hcop.dvd_of_dvd_mul_right h4.1
  · intro h8
    exact h4.2 (hcard ▸ Dvd.dvd.mul_right h8 _)

section ThreeGroup

variable {C : Type*} [Group C]

private theorem centralizes_of_card_eighty_one [Finite C] (O : Subgroup C) [O.Normal]
    (hO : Nat.card O = 81) {y : C} (hy : orderOf y = 5) {s : C} (hsO : s ∈ O) (hs1 : s ≠ 1)
    (hsy : s * y = y * s) : ∀ x ∈ O, x * y = y * x := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype O := Fintype.ofFinite O
  let f : Function.End O := fun x => ⟨y * x * y⁻¹, (inferInstance : O.Normal).conj_mem x x.2 y⟩
  have hpow : ∀ (n : ℕ) (x : O), ((f ^ n) x : C) = y ^ n * x * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp; rfl
    | succ n ih =>
      intro x
      rw [pow_succ']
      show y * ((f ^ n) x : C) * y⁻¹ = _
      rw [ih]
      group
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hpow]
    have : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    rw [this]
    simp
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf5
  rw [← Nat.card_eq_fintype_card, hO, ← Nat.card_eq_fintype_card] at hmod
  let Z : Subgroup O := (centralizer ({y} : Set C)).subgroupOf O
  have hZfix : ∀ x : O, x ∈ Function.fixedPoints f ↔ x ∈ Z := by
    intro x
    rw [Function.mem_fixedPoints_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : y * (x : C) * y⁻¹ = x := congrArg Subtype.val h
      calc (x : C) * y = (y * (x : C) * y⁻¹) * y := by rw [h1]
        _ = y * x := by group
    · intro h
      apply Subtype.ext
      show y * (x : C) * y⁻¹ = x
      calc y * (x : C) * y⁻¹ = ((x : C) * y) * y⁻¹ := by rw [h]
        _ = x := by group
  have hcard : Nat.card (Function.fixedPoints f) = Nat.card Z :=
    Nat.card_congr (Equiv.subtypeEquivRight hZfix)
  rw [hcard] at hmod
  have hdvd : Nat.card Z ∣ 3 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card Z
    rwa [hO] at this
  have hne1 : Nat.card Z ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    have hsZ : (⟨s, hsO⟩ : O) ∈ Z := by
      rw [mem_subgroupOf, mem_centralizer_singleton_iff]
      exact hsy
    rw [h1, Subgroup.mem_bot] at hsZ
    exact hs1 (congrArg Subtype.val hsZ)
  have h81 : Nat.card Z = 81 := by
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hmod' : 81 % 5 = Nat.card Z % 5 := hmod
    interval_cases i
    all_goals rw [hci] at hmod' hne1 ⊢
    all_goals omega
  have hZtop : Z = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, h81, hO]
  intro x hx
  have : (⟨x, hx⟩ : O) ∈ Z := by rw [hZtop]; exact Subgroup.mem_top _
  rw [mem_subgroupOf, mem_centralizer_singleton_iff] at this
  exact this

end ThreeGroup

theorem false_of_simple_sixty_quotient {C : Type*} [Group C] [Finite C] {O : Subgroup C}
    [O.Normal] (hO : Nat.card O = 81) {s : C} (hsO : s ∈ O) (hs1 : s ≠ 1)
    (hsc : ∀ c : C, c * s = s * c) (hK : Nat.card (C ⧸ O) = 60)
    (hKs : IsSimpleGroup (C ⧸ O)) {z : C} (hz2 : z ^ 2 = 1)
    (hzO : ∃ o ∈ O, z * o ≠ o * z) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hC : Nat.card C = 60 * 81 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O, hK, hO]
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [hC]; norm_num)
  have hyO : y ∉ O := fun hyO => by
    have := Subgroup.orderOf_dvd_natCard O hyO
    rw [hy, hO] at this
    norm_num at this
  have hyc : ∀ x ∈ O, x * y = y * x :=
    centralizes_of_card_eighty_one O hO hy hsO hs1 (hsc y).symm
  have hyR : y ∈ centralizer (O : Set C) := mem_centralizer_iff.mpr hyc
  let π : C →* C ⧸ O := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hRn : (centralizer (O : Set C)).Normal := inferInstance
  have hRmap : ((centralizer (O : Set C)).map π).Normal := hRn.map π hπ
  have htop : (centralizer (O : Set C)).map π = ⊤ := by
    rcases hKs.eq_bot_or_eq_top_of_normal ((centralizer (O : Set C)).map π) with h | h
    · exfalso
      have hmem : π y ∈ (centralizer (O : Set C)).map π := ⟨y, hyR, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hyO ((QuotientGroup.eq_one_iff y).mp hmem)
    · exact h
  have hzmem : π z ∈ (centralizer (O : Set C)).map π := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨r, hr, hrz⟩ := hzmem
  obtain ⟨o, hodef⟩ : ∃ o : C, o = r⁻¹ * z := ⟨_, rfl⟩
  have hzro : z = r * o := by rw [hodef]; group
  have hoO : o ∈ O := by
    have : π (r⁻¹ * z) = 1 := by rw [map_mul, map_inv, hrz, inv_mul_cancel]
    rw [hodef]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hrc : ∀ w ∈ O, r * w * r⁻¹ = w := by
    intro w hw
    have := mem_centralizer_iff.mp hr w hw
    calc r * w * r⁻¹ = (r * w) * r⁻¹ := rfl
      _ = (w * r) * r⁻¹ := by rw [this]
      _ = w := by group
  have hstar : ∀ w ∈ O, z * w * z⁻¹ = o * w * o⁻¹ := by
    intro w hw
    have hu : o * w * o⁻¹ ∈ O := O.mul_mem (O.mul_mem hoO hw) (O.inv_mem hoO)
    rw [hzro]
    calc r * o * w * (r * o)⁻¹ = r * (o * w * o⁻¹) * r⁻¹ := by group
      _ = o * w * o⁻¹ := hrc _ hu
  have ho2 : o ^ 2 ∈ centralizer (O : Set C) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hxO : x ∈ O := hx
    have hx1 : o * x * o⁻¹ ∈ O := O.mul_mem (O.mul_mem hoO hxO) (O.inv_mem hoO)
    have hzz : z * z = 1 := by rwa [← pow_two]
    have h1 : z * (o * x * o⁻¹) * z⁻¹ = x := by
      rw [← hstar x hxO]
      calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ := by group
        _ = x := by rw [hzz]; group
    rw [hstar _ hx1] at h1
    calc x * o ^ 2 = (o * (o * x * o⁻¹) * o⁻¹) * o ^ 2 := by rw [h1]
      _ = o ^ 2 * x := by rw [pow_two]; group
  have hodd : Odd (orderOf o) := by
    have hd := Subgroup.orderOf_dvd_natCard O hoO
    rw [hO] at hd
    exact Odd.of_dvd_nat (by decide) hd
  have hoR : o ∈ centralizer (O : Set C) := by
    obtain ⟨k, hk⟩ := hodd
    have hg1 : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    have hg_eq : o = (o ^ 2) ^ (k + 1) := by
      calc o = 1 * o := (one_mul _).symm
        _ = o ^ (2 * k + 1) * o := by rw [hg1]
        _ = o ^ (2 * k + 1 + 1) := (pow_succ _ _).symm
        _ = (o ^ 2) ^ (k + 1) := by rw [← pow_mul]; congr 1
    rw [hg_eq]
    exact pow_mem ho2 (k + 1)
  have hzR : z ∈ centralizer (O : Set C) := by
    rw [hzro]
    exact (centralizer (O : Set C)).mul_mem hr hoR
  obtain ⟨o', ho', hne⟩ := hzO
  exact hne (mem_centralizer_iff.mp hzR o' ho').symm

end CFSG.Sporadic.Recognition.JankoWong
