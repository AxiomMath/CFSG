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
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
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

namespace CFSG.Quasithin

theorem injective_toPermHom_quotient_of_isPGroup {X : Type*} [Group X]
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {S : Subgroup X}
    (hS : IsPGroup 2 S) : Function.Injective (MulAction.toPermHom X (X ⧸ S)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
  exact h2 _ S.normalCore_normal (hS.to_le S.normalCore_le)

theorem card_dvd_factorial_index_of_isPGroup {X : Type*} [Group X] [Finite X]
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {S : Subgroup X}
    (hS : IsPGroup 2 S) : Nat.card X ∣ S.index.factorial := by
  have h := Subgroup.card_dvd_of_injective _ (injective_toPermHom_quotient_of_isPGroup h2 hS)
  rwa [Nat.card_perm, ← Subgroup.index_eq_card] at h

theorem nonempty_mulEquiv_perm_three {X : Type*} [Group X] [Finite X]
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {S : Subgroup X}
    (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hidx : S.index = 3) :
    Nonempty (X ≃* Equiv.Perm (Fin 3)) := by
  have hdvd := card_dvd_factorial_index_of_isPGroup h2 hS
  rw [hidx] at hdvd
  have hcard : Nat.card S * 3 = Nat.card X := by
    rw [← hidx]
    exact Subgroup.card_mul_index S
  obtain ⟨b, hb⟩ := hS.exists_card_eq
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hS1 (Subgroup.card_eq_one.mp (by simpa using hb))
  have h6 : Nat.card X = 6 := by
    have h1 : 2 ^ b * 3 ∣ 6 := by
      rw [← hb, hcard]
      simpa [Nat.factorial] using hdvd
    have h2' : 2 ^ b * 3 ≤ 6 := Nat.le_of_dvd (by norm_num) h1
    have h3 : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hb0)
    rw [← hcard, hb]
    omega
  have hinj := injective_toPermHom_quotient_of_isPGroup h2 hS
  have hbij : Function.Bijective (MulAction.toPermHom X (X ⧸ S)) := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_perm, ← Subgroup.index_eq_card, hidx, h6]
    norm_num [Nat.factorial]
  let e : X ⧸ S ≃ Fin 3 := Finite.equivFinOfCardEq (by rw [← Subgroup.index_eq_card, hidx])
  exact ⟨(MulEquiv.ofBijective _ hbij).trans e.permCongrHom⟩

open scoped Pointwise in
theorem exists_normal_five_complement {X : Type*} [Group X] [Finite X]
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {S : Subgroup X}
    (hS : IsPGroup 2 S) (hidx : S.index = 5) :
    ∃ P : Subgroup X, P.Normal ∧ Nat.card P = 5 ∧ P.IsComplement' S ∧
      ∀ s ∈ S, (∀ p ∈ P, s * p = p * s) → s = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd := card_dvd_factorial_index_of_isPGroup h2 hS
  rw [hidx] at hdvd
  have hcardS : Nat.card S * 5 = Nat.card X := by
    rw [← hidx]
    exact Subgroup.card_mul_index S
  obtain ⟨b, hb⟩ := hS.exists_card_eq
  have hXcard : Nat.card X = 2 ^ b * 5 := by rw [← hcardS, hb]
  have hb3 : b ≤ 3 := by
    have h1 : 2 ^ b * 5 ∣ 120 := by
      rw [← hXcard]
      simpa [Nat.factorial] using hdvd
    have h2' : 2 ^ b * 5 ≤ 120 := Nat.le_of_dvd (by norm_num) h1
    by_contra hlt
    push Not at hlt
    have h4 : 2 ^ 4 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hlt
    have hb4 : b = 4 := by
      by_contra hne
      have h5 : 2 ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hb4
    omega
  obtain ⟨P0⟩ : Nonempty (Sylow 5 X) := inferInstance
  have hP0 : Nat.card (P0 : Subgroup X) = 5 := by
    rw [Sylow.card_eq_multiplicity P0, hXcard]
    have : (2 ^ b * 5).factorization 5 = 1 := by
      rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 5)]
    rw [this, pow_one]
  have hidx0 : (P0 : Subgroup X).index = 2 ^ b := by
    have := Subgroup.card_mul_index (P0 : Subgroup X)
    rw [hP0, hXcard] at this
    omega
  have hmod := card_sylow_modEq_one 5 X
  have hn1 : Nat.card (Sylow 5 X) = 1 := by
    have hdvd' := P0.card_dvd_index
    rw [hidx0] at hdvd'
    obtain ⟨j, hj, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    rw [hn] at hmod ⊢
    have hj3 : j ≤ 3 := hj.trans hb3
    interval_cases j <;> simp [Nat.ModEq] at hmod ⊢
  have : Subsingleton (Sylow 5 X) := (Nat.card_eq_one_iff_unique.mp hn1).1
  have hPn : (P0 : Subgroup X).Normal := P0.normal_of_subsingleton
  have hcompl : (P0 : Subgroup X).IsComplement' S := by
    refine Subgroup.isComplement'_of_coprime (by rw [hP0, hb, hXcard]; ring) ?_
    rw [hP0, hb]
    exact Nat.Coprime.pow_right b (by norm_num)
  refine ⟨P0, hPn, hP0, hcompl, ?_⟩
  intro s hs hcomm
  let T0 : Subgroup X := S ⊓ Subgroup.centralizer (P0 : Set X)
  have hT0 : T0.Normal := by
    refine ⟨fun t ht x => ?_⟩
    have hx : x ∈ ((P0 : Subgroup X) : Set X) * (S : Set X) :=
      (Subgroup.isComplement'_def.mp hcompl).mul_eq ▸ Set.mem_univ x
    obtain ⟨p, hp, s', hs', rfl⟩ := hx
    have hct : ∀ q ∈ (P0 : Subgroup X), q * t = t * q :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht).2
    have ht' : s' * t * s'⁻¹ ∈ T0 := by
      refine Subgroup.mem_inf.mpr
        ⟨S.mul_mem (S.mul_mem hs' (Subgroup.mem_inf.mp ht).1) (S.inv_mem hs'), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : s'⁻¹ * q * s' ∈ (P0 : Subgroup X) := by
        simpa using hPn.conj_mem q hq s'⁻¹
      have h1 := hct _ hq'
      calc q * (s' * t * s'⁻¹) = s' * ((s'⁻¹ * q * s') * t) * s'⁻¹ := by group
        _ = s' * (t * (s'⁻¹ * q * s')) * s'⁻¹ := by rw [h1]
        _ = s' * t * s'⁻¹ * q := by group
    have h2' := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht').2) p hp
    have : p * s' * t * (p * s')⁻¹ = s' * t * s'⁻¹ := by
      calc p * s' * t * (p * s')⁻¹ = (p * (s' * t * s'⁻¹)) * p⁻¹ := by group
        _ = ((s' * t * s'⁻¹) * p) * p⁻¹ := by rw [h2']
        _ = s' * t * s'⁻¹ := by group
    rw [this]
    exact ht'
  have hT0bot : T0 = ⊥ := h2 T0 hT0 (hS.to_le inf_le_left)
  have hsT0 : s ∈ T0 :=
    Subgroup.mem_inf.mpr ⟨hs, Subgroup.mem_centralizer_iff.mpr fun p hp => (hcomm p hp).symm⟩
  rw [hT0bot] at hsT0
  exact hsT0



theorem card_le_four_of_faithful_of_card_five {X : Type*} [Group X] [Finite X] {P S : Subgroup X}
    (hPn : P.Normal) (hP : Nat.card P = 5)
    (hfaith : ∀ s ∈ S, (∀ p ∈ P, s * p = p * s) → s = 1) : Nat.card S ≤ 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPcyc : IsCyclic P := isCyclic_of_prime_card hP
  let φ : S →* MulAut P := MulAut.conjNormal.comp S.subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    apply Subtype.ext
    refine hfaith s s.2 fun p hp => ?_
    have h1 := congrArg (fun f : MulAut P => ((f ⟨p, hp⟩ : P) : X)) hs
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply] at h1
    simp at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have := Nat.card_le_card_of_injective φ hinj
  rwa [IsCyclic.card_mulAut, hP, Nat.totient_prime (by norm_num)] at this

theorem nonempty_mulEquiv_dihedralGroup_of_cyclic_reflection {X : Type*} [Group X] [Finite X]
    (C : Subgroup X) (hC : IsCyclic C) (w : X) (hw_not_mem : w ∉ C) (hw_sq : w * w = 1)
    (hw_inv : ∀ c : X, c ∈ C → w * c * w⁻¹ = c⁻¹) (hindex : C.index = 2) :
    Nonempty (X ≃* DihedralGroup (Nat.card C)) := by
  classical
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C :=
    zmodCyclicMulEquiv hC
  let rot : ZMod (Nat.card C) → X := fun i =>
    (e (Multiplicative.ofAdd i) : C)
  have hrot_mem (i : ZMod (Nat.card C)) : rot i ∈ C :=
    (e (Multiplicative.ofAdd i)).property
  have hrot_add (i j : ZMod (Nat.card C)) :
      rot (i + j) = rot i * rot j := by
    exact congrArg Subtype.val (e.map_mul
      (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_neg (i : ZMod (Nat.card C)) :
      rot (-i) = (rot i)⁻¹ := by
    exact congrArg Subtype.val (e.map_inv (Multiplicative.ofAdd i))
  have hrot_zero : rot 0 = 1 := by
    exact congrArg Subtype.val e.map_one
  have hw_inv_eq : w⁻¹ = w :=
    (eq_inv_of_mul_eq_one_left hw_sq).symm
  have hw_mul_rot (i : ZMod (Nat.card C)) :
      w * rot i = rot (-i) * w := by
    calc
      w * rot i = (w * rot i * w⁻¹) * w := by
        rw [hw_inv_eq, mul_assoc, hw_sq, mul_one]
      _ = (rot i)⁻¹ * w := by rw [hw_inv (rot i) (hrot_mem i)]
      _ = rot (-i) * w := by rw [hrot_neg]
  have hrot_mul_w (i : ZMod (Nat.card C)) :
      rot i * w = w * rot (-i) := by
    calc
      rot i * w = rot (-(-i)) * w := by rw [neg_neg]
      _ = w * rot (-i) := (hw_mul_rot (-i)).symm
  let hom : DihedralGroup (Nat.card C) →* X :=
    { toFun := fun x => match x with
        | DihedralGroup.r i => rot i
        | DihedralGroup.sr i => w * rot i
      map_one' := hrot_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · change rot (i + j) = rot i * rot j
          exact hrot_add i j
        · change w * rot (j - i) = rot i * (w * rot j)
          calc
            w * rot (j - i) = w * rot (-i + j) := by
              rw [sub_eq_add_neg, add_comm]
            _ = w * (rot (-i) * rot j) := by rw [hrot_add]
            _ = (w * rot (-i)) * rot j := by rw [mul_assoc]
            _ = (rot i * w) * rot j := by rw [hrot_mul_w]
            _ = rot i * (w * rot j) := by rw [mul_assoc]
        · change w * rot (i + j) = (w * rot i) * rot j
          rw [hrot_add, mul_assoc]
        · change rot (j - i) = (w * rot i) * (w * rot j)
          calc
            rot (j - i) = rot (-i + j) := by
              rw [sub_eq_add_neg, add_comm]
            _ = rot (-i) * rot j := hrot_add (-i) j
            _ = (w * rot i) * (w * rot j) := by
              calc
                rot (-i) * rot j = (w * w) * (rot (-i) * rot j) := by
                  rw [hw_sq, one_mul]
                _ = (w * (w * rot (-i))) * rot j := by
                  simp only [mul_assoc]
                _ = (w * (rot i * w)) * rot j := by
                  rw [hrot_mul_w]
                _ = (w * rot i) * (w * rot j) := by
                  simp only [mul_assoc] }
  have hhom_injective : Function.Injective hom := by
    rintro (i | i) (j | j) hij
    · apply congrArg DihedralGroup.r
      change rot i = rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
        apply e.injective
        apply Subtype.ext
        exact hij
      exact congrArg Multiplicative.toAdd heq
    · exfalso
      apply hw_not_mem
      change rot i = w * rot j at hij
      have hwrj : w * rot j ∈ C := by
        rw [← hij]
        exact hrot_mem i
      exact (C.mul_mem_cancel_right (hrot_mem j)).mp hwrj
    · exfalso
      apply hw_not_mem
      change w * rot i = rot j at hij
      have hwri : w * rot i ∈ C := by
        rw [hij]
        exact hrot_mem j
      exact (C.mul_mem_cancel_right (hrot_mem i)).mp hwri
    · apply congrArg DihedralGroup.sr
      change w * rot i = w * rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
        apply e.injective
        apply Subtype.ext
        exact mul_left_cancel hij
      exact congrArg Multiplicative.toAdd heq
  have hhom_surjective : Function.Surjective hom := by
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      refine ⟨DihedralGroup.r i.toAdd, ?_⟩
      exact congrArg Subtype.val hi
    · have hxw : w * x ∈ C := by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        simp [hw_not_mem, hx]
      obtain ⟨i, hi⟩ := e.surjective ⟨w * x, hxw⟩
      refine ⟨DihedralGroup.sr i.toAdd, ?_⟩
      change w * rot i.toAdd = x
      have hi' : rot i.toAdd = w * x := congrArg Subtype.val hi
      rw [hi', ← mul_assoc, hw_sq, one_mul]
  exact ⟨(MulEquiv.ofBijective hom
    ⟨hhom_injective, hhom_surjective⟩).symm⟩


theorem nonempty_mulEquiv_dihedralGroup_five {X : Type*} [Group X] [Finite X] {P S : Subgroup X}
    (hPn : P.Normal) (hP : Nat.card P = 5) (hS : Nat.card S = 2) (hcompl : P.IsComplement' S)
    (hfaith : ∀ s ∈ S, (∀ p ∈ P, s * p = p * s) → s = 1) :
    Nonempty (X ≃* DihedralGroup 5) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPcyc : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨w, hwS, hw1⟩ : ∃ w ∈ S, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr hcon
    rw [this] at hS
    simp at hS
  have hw2 : w * w = 1 := by
    have hord : orderOf w ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard S hwS
      rwa [hS] at this
    have hne : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
    have h2' : orderOf w = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact absurd h hne
      · exact h
    rw [← pow_two]
    nth_rewrite 1 [← h2']
    exact pow_orderOf_eq_one w
  have hwP : w ∉ P := fun hwP => hw1 (Subgroup.disjoint_def.mp hcompl.disjoint hwP hwS)
  have hwinv : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  have hinv : ∀ c : X, c ∈ P → w * c * w⁻¹ = c⁻¹ := by
    intro c hc
    let F : Subgroup X := P ⊓ Subgroup.centralizer ({w} : Set X)
    have hFP : F ≤ P := inf_le_left
    have hF1 : F = ⊥ := by
      have hdvd : Nat.card F ∣ 5 := hP ▸ Subgroup.card_dvd_of_le hFP
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
      · exact Subgroup.card_eq_one.mp h
      · exfalso
        have hFeq : F = P := Subgroup.eq_of_le_of_card_ge hFP (by rw [h, hP])
        apply hw1
        refine hfaith w hwS fun p hp => ?_
        have hpF : p ∈ F := hFeq ▸ hp
        have := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hpF).2) w rfl
        exact this
    have hu : w * c * w⁻¹ ∈ P := by simpa using hPn.conj_mem c hc w
    have hcomm : (w * c * w⁻¹) * c = c * (w * c * w⁻¹) := by
      have := IsMulCommutative.is_comm.comm (⟨w * c * w⁻¹, hu⟩ : P) ⟨c, hc⟩
      exact congrArg Subtype.val this
    have hz : c * (w * c * w⁻¹) ∈ F := by
      refine Subgroup.mem_inf.mpr ⟨P.mul_mem hc hu, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hwu : y * (y * c * y⁻¹) * y⁻¹ = c := by
        calc y * (y * c * y⁻¹) * y⁻¹ = (y * y) * c * (y⁻¹ * y⁻¹) := by group
          _ = c := by
            have : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hw2, inv_one]
            rw [hw2, this]; group
      calc y * (c * (y * c * y⁻¹)) = (y * c * y⁻¹) * (y * (y * c * y⁻¹) * y⁻¹) * y := by group
        _ = (y * c * y⁻¹) * c * y := by rw [hwu]
        _ = (c * (y * c * y⁻¹)) * y := by rw [hcomm]
    rw [hF1, Subgroup.mem_bot] at hz
    exact eq_inv_of_mul_eq_one_right hz
  have hP2 : P.index = 2 := by
    rw [hcompl.symm.index_eq_card]
    exact hS
  have := nonempty_mulEquiv_dihedralGroup_of_cyclic_reflection P hPcyc w hwP hw2 hinv hP2
  rwa [hP] at this


private theorem nonempty_semidirect_mulEquiv_hol {P S : Type*} [Group P] [Group S] [Finite P]
    (φ : S →* MulAut P) (hinj : Function.Injective φ) (hP : Nat.card P = 5)
    (hS : Nat.card S = 4) :
    Nonempty (P ⋊[φ] S ≃*
      (Multiplicative (ZMod 5) ⋊[MonoidHom.id (MulAut (Multiplicative (ZMod 5)))]
        MulAut (Multiplicative (ZMod 5)))) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPcyc : IsCyclic P := isCyclic_of_prime_card hP
  have hZcard : Nat.card (Multiplicative (ZMod 5)) = 5 := by simp
  let α : P ≃* Multiplicative (ZMod 5) := mulEquivOfCyclicCardEq (by rw [hP, hZcard])
  let ψ : S →* MulAut (Multiplicative (ZMod 5)) := (MulAut.congr α).toMonoidHom.comp φ
  have hψinj : Function.Injective ψ := (MulAut.congr α).injective.comp hinj
  have hψcard : Nat.card (MulAut (Multiplicative (ZMod 5))) = 4 := by
    rw [IsCyclic.card_mulAut, hZcard, Nat.totient_prime (by norm_num)]
  have hψbij : Function.Bijective ψ :=
    hψinj.bijective_of_nat_card_le (by rw [hψcard, hS])
  let β : S ≃* MulAut (Multiplicative (ZMod 5)) := MulEquiv.ofBijective ψ hψbij
  refine ⟨SemidirectProduct.congr α β fun s => ?_⟩
  ext x
  simp [β, ψ, MulAut.congr_apply]


private theorem nonempty_mulEquiv_hol_of_card_twenty {X : Type*} [Group X] [Finite X]
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) (hX : Nat.card X = 20) :
    Nonempty (X ≃* (Multiplicative (ZMod 5) ⋊[MonoidHom.id (MulAut (Multiplicative (ZMod 5)))]
      MulAut (Multiplicative (ZMod 5)))) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hS4 : Nat.card (S : Subgroup X) = 4 := by
    have h1 := Sylow.card_eq_multiplicity S
    rw [hX] at h1
    have h3 : (20 : ℕ).factorization 2 = 2 := by
      have : (20 : ℕ) = 2 ^ 2 * 5 := by norm_num
      rw [this, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 5)]
    rw [h3] at h1
    simpa using h1
  have hidx : (S : Subgroup X).index = 5 := by
    have := Subgroup.card_mul_index (S : Subgroup X)
    rw [hS4, hX] at this
    omega
  obtain ⟨P, hPn, hP, hcompl, hfaith⟩ := exists_normal_five_complement h2 S.isPGroup' hidx
  have := hPn
  let e0 := SemidirectProduct.mulEquivSubgroup hcompl
  have hinj : Function.Injective (P.normalizerMonoidHom.comp
      (Subgroup.inclusion
        (P.normalizer_eq_top ▸ le_top : (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X)))) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    apply Subtype.ext
    refine hfaith s s.2 fun p hp => ?_
    have h1 := congrArg (fun f : MulAut P => ((f ⟨p, hp⟩ : P) : X)) hs
    simp only [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    simp at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  obtain ⟨f⟩ := nonempty_semidirect_mulEquiv_hol _ hinj hP hS4
  exact ⟨e0.symm.trans f⟩

theorem nonempty_mulEquiv_of_card_twenty {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (hX2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (hY2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hX : Nat.card X = 20) (hY : Nat.card Y = 20) : Nonempty (X ≃* Y) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_hol_of_card_twenty hX2 hX
  obtain ⟨f⟩ := nonempty_mulEquiv_hol_of_card_twenty hY2 hY
  exact ⟨e.trans f.symm⟩

theorem nonempty_mulEquiv_dihedralGroup_five_or_card_twenty {X : Type*} [Group X] [Finite X]
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {S : Subgroup X}
    (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hidx : S.index = 5) :
    Nonempty (X ≃* DihedralGroup 5) ∨ Nat.card X = 20 := by
  obtain ⟨P, hPn, hP, hcompl, hfaith⟩ := exists_normal_five_complement h2 hS hidx
  have hle := card_le_four_of_faithful_of_card_five hPn hP hfaith
  obtain ⟨b, hb⟩ := hS.exists_card_eq
  have hb0 : 1 ≤ b := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    exact hS1 (Subgroup.card_eq_one.mp (by simpa using hb))
  have hcardS : Nat.card S * 5 = Nat.card X := by
    rw [← hidx]
    exact Subgroup.card_mul_index S
  have hb2 : b ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 3 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  interval_cases b
  · left
    exact nonempty_mulEquiv_dihedralGroup_five hPn hP (by simpa using hb) hcompl hfaith
  · right
    rw [← hcardS, hb]
    norm_num

end CFSG.Quasithin
