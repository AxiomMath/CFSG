module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
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
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.Monster.B.Generic

open Subgroup MulAction
open scoped Pointwise commutatorElement

private theorem two_pow_sub_eq_one {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) {r e : ℕ}
    (her : e ≤ r) (h : 2 ^ r ≡ 2 ^ e [MOD ℓ]) : (2 : ZMod ℓ) ^ (r - e) = 1 := by
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h0
    have : ℓ ∣ 2 := (ZMod.natCast_eq_zero_iff 2 ℓ).mp (by exact_mod_cast h0)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp this)
  have h' : (2 : ZMod ℓ) ^ r = 2 ^ e := by
    have := (ZMod.natCast_eq_natCast_iff (2 ^ r) (2 ^ e) ℓ).mpr h
    exact_mod_cast this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le her
  rw [Nat.add_sub_cancel_left]
  rw [pow_add] at h'
  exact mul_left_cancel₀ (pow_ne_zero e h2) (h'.trans (mul_one _).symm)

private theorem exists_two_pow_eq_one_of_mulAut {V : Type*} [Group V] [Finite V] {r : ℕ}
    (hV : Nat.card V = 2 ^ r) {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (τ : MulAut V)
    (hτ : τ ^ ℓ = 1) (hτ1 : τ ≠ 1) : ∃ j, 0 < j ∧ j ≤ r ∧ (2 : ZMod ℓ) ^ j = 1 := by
  have hP : IsPGroup ℓ (zpowers τ) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hτ hτ1, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints V
  have hH : Nat.card (fixedPoints (zpowers τ) V) =
      Nat.card (FixedPoints.subgroup (zpowers τ) V) := rfl
  obtain ⟨e, he, hHe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hV ▸ (FixedPoints.subgroup (zpowers τ) V).card_subgroup_dvd_card)
  have her : e < r := by
    refine lt_of_le_of_ne he ?_
    rintro rfl
    apply hτ1
    have htop : FixedPoints.subgroup (zpowers τ) V = ⊤ :=
      (Subgroup.card_eq_iff_eq_top _).mp (hHe.trans hV.symm)
    ext v
    have hv : v ∈ FixedPoints.subgroup (zpowers τ) V := htop ▸ Subgroup.mem_top v
    have := (FixedPoints.mem_subgroup (zpowers τ) V v).mp hv ⟨τ, mem_zpowers τ⟩
    simpa [Subgroup.mk_smul, MulAut.smul_def] using this
  rw [hV, hH, hHe] at hmod
  exact ⟨r - e, by omega, by omega, two_pow_sub_eq_one hℓ2 he hmod⟩

private theorem conj_eq_of_commute {K : Type*} [Group K] {A₀ : Subgroup K} {C : Set K} {g : K}
    {ℓ : ℕ} (hℓ : Odd ℓ) (hgC : ∀ c ∈ C, g * c * g⁻¹ ∈ C)
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c⁻¹ * c' ∈ A₀) (hcen : ∀ a ∈ A₀, g * a = a * g)
    (hsq : ∀ a ∈ A₀, a ^ 2 = 1) (hℓC : ∀ c ∈ C, g ^ ℓ * c = c * g ^ ℓ) (c : K) (hc : c ∈ C) :
    g * c * g⁻¹ = c := by
  obtain ⟨a, ha⟩ : ∃ a, a = c⁻¹ * (g * c * g⁻¹) := ⟨_, rfl⟩
  have haA : a ∈ A₀ := ha ▸ hC c hc _ (hgC c hc)
  have hca : g * c * g⁻¹ = c * a := by rw [ha]; group
  have key : ∀ n : ℕ, g ^ n * c * (g ^ n)⁻¹ = c * a ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : g * a ^ n = a ^ n * g := (Commute.pow_right (hcen a haA) n).eq
      calc g ^ (n + 1) * c * (g ^ (n + 1))⁻¹ = g * (g ^ n * c * (g ^ n)⁻¹) * g⁻¹ := by group
        _ = (g * c * g⁻¹) * (g * a ^ n * g⁻¹) := by rw [ih]; group
        _ = (c * a) * a ^ n := by rw [h1, hca]; group
        _ = c * a ^ (n + 1) := by rw [pow_succ', mul_assoc]
  have hℓc : g ^ ℓ * c * (g ^ ℓ)⁻¹ = c := by rw [hℓC c hc]; group
  have haℓ : a ^ ℓ = 1 := by
    have := (key ℓ).symm.trans hℓc
    simpa using this
  obtain ⟨k, rfl⟩ := hℓ
  have ha1 : a = 1 := by
    rwa [pow_succ, pow_mul, hsq a haA, one_pow, one_mul] at haℓ
  rw [hca, ha1, mul_one]

private def conjRestrict {K : Type*} [Group K] (H : Subgroup K) (g : K)
    (h₁ : ∀ a ∈ H, g * a * g⁻¹ ∈ H) (h₂ : ∀ a ∈ H, g⁻¹ * a * g ∈ H) : MulAut H where
  toFun a := ⟨g * a * g⁻¹, h₁ a a.2⟩
  invFun a := ⟨g⁻¹ * a * g, h₂ a a.2⟩
  left_inv a := by ext; simp [mul_assoc]
  right_inv a := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

private theorem conjRestrict_pow_apply {K : Type*} [Group K] (H : Subgroup K) (g : K)
    (h₁ : ∀ a ∈ H, g * a * g⁻¹ ∈ H) (h₂ : ∀ a ∈ H, g⁻¹ * a * g ∈ H) (n : ℕ) (a : H) :
    (((conjRestrict H g h₁ h₂) ^ n) a : K) = g ^ n * a * (g ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    change g * (((conjRestrict H g h₁ h₂) ^ n) a : K) * g⁻¹ = _
    rw [ih]
    group

private theorem conj_mem_closure {K : Type*} [Group K] {C : Set K} {g : K}
    (hgC : ∀ c ∈ C, g * c * g⁻¹ ∈ C) {a : K} (ha : a ∈ closure C) :
    g * a * g⁻¹ ∈ closure C := by
  have : closure C ≤ (closure C).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    intro c hc
    simpa using subset_closure (hgC c hc)
  simpa using this ha

theorem conjugate_involution_affine_obstruction {K : Type*} [Group K] [Finite K]
    (D : ConjClasses K) (hD : ∀ x ∈ D.carrier, orderOf x = 2)
    (hgen : closure D.carrier = ⊤) (C : Set K) (hCD : C ⊆ D.carrier) (hCne : C.Nonempty)
    (d : ℕ) (hA : CFSG.IsElementaryAbelian 2 (closure C))
    (hAcard : Nat.card (closure C) = 2 ^ d) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓF : ℓ ∣ Nat.card (MulAction.toPermHom (stabilizer (ConjAct K) C) C).range)
    (hord : d - 1 < orderOf (2 : ZMod ℓ)) :
    Group.IsPerfect K := by
  classical
  have := Fact.mk hℓ
  rw [Group.isPerfect_def]
  by_contra hN
  have hDinv : ∀ x ∈ D.carrier, x⁻¹ = x := fun x hx => by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_two, ← hD x hx]
    exact pow_orderOf_eq_one x
  have hDD : ∀ x ∈ D.carrier, ∀ y ∈ D.carrier, x * y ∈ commutator K := by
    intro x hx y hy
    have hxy : IsConj x y := ConjClasses.mk_eq_mk_iff_isConj.mp
      ((ConjClasses.mem_carrier_iff_mk_eq.mp hx).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp hy).symm)
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
    have : x * (c * x * c⁻¹) = ⁅x⁻¹, c⁆ := by
      rw [commutatorElement_def, inv_inv, hDinv x hx]
      group
    rw [this, _root_.commutator_def]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hDN : ∀ x ∈ D.carrier, x ∉ commutator K := by
    intro x hx hxN
    apply hN
    rw [eq_top_iff, ← hgen, closure_le]
    intro y hy
    simpa using mul_mem (hDD y hy x hx) (inv_mem hxN)
  obtain ⟨c₀, hc₀⟩ := hCne
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Subgroup K, A₀ = closure C ⊓ commutator K := ⟨_, rfl⟩
  have hmemA₀ : ∀ x, x ∈ A₀ ↔ x ∈ closure C ∧ x ∈ commutator K := fun x => by
    rw [hA₀]
    exact mem_inf
  have hA₀sq : ∀ a ∈ A₀, a ^ 2 = 1 := fun a ha =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (A := closure C) a ((hmemA₀ a).mp ha).1
  obtain ⟨r, hrd, hA₀card⟩ : ∃ r, r < d ∧ Nat.card A₀ = 2 ^ r := by
    have hle : A₀ ≤ closure C := fun x hx => ((hmemA₀ x).mp hx).1
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hAcard] at hdvd
    obtain ⟨r, hr, hr'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    refine ⟨r, lt_of_le_of_ne hr ?_, hr'⟩
    rintro rfl
    have hEq : A₀ = closure C := Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard, hr'])
    have hc₀A : c₀ ∈ A₀ := hEq ▸ subset_closure hc₀
    exact hDN c₀ (hCD hc₀) ((hmemA₀ c₀).mp hc₀A).2
  have hC : ∀ c ∈ C, ∀ c' ∈ C, c⁻¹ * c' ∈ A₀ := by
    intro c hc c' hc'
    rw [hmemA₀]
    refine ⟨mul_mem (inv_mem (subset_closure hc)) (subset_closure hc'), ?_⟩
    rw [hDinv c (hCD hc)]
    exact hDD c (hCD hc) c' (hCD hc')
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hℓF
  obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp x.2
  have hfℓ : orderOf (MulAction.toPermHom (stabilizer (ConjAct K) C) C f) = ℓ := by
    rw [hf, Subgroup.orderOf_coe, hx]
  obtain ⟨g, hg⟩ : ∃ g : K, g = ConjAct.ofConjAct (f : ConjAct K) := ⟨_, rfl⟩
  have hsmul : ∀ (n : ℕ) (c : K),
      ((f ^ n : stabilizer (ConjAct K) C) : ConjAct K) • c = g ^ n * c * (g ^ n)⁻¹ := by
    intro n c
    rw [ConjAct.smul_def, hg]
    simp
  have hgC : ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro c hc
    have := (f • (⟨c, hc⟩ : C)).2
    rwa [SMul.smul_stabilizer_def, ConjAct.smul_def, ← hg] at this
  have hgC' : ∀ c ∈ C, g⁻¹ * c * g⁻¹⁻¹ ∈ C := by
    intro c hc
    have := (f⁻¹ • (⟨c, hc⟩ : C)).2
    rw [SMul.smul_stabilizer_def, ConjAct.smul_def] at this
    simpa [← hg] using this
  have hgℓ : ∀ c ∈ C, g ^ ℓ * c = c * g ^ ℓ := by
    intro c hc
    have hσℓ : MulAction.toPermHom (stabilizer (ConjAct K) C) C (f ^ ℓ) = 1 := by
      rw [map_pow, ← hfℓ]
      exact pow_orderOf_eq_one _
    have h1 := congrArg (fun σ : Equiv.Perm C => ((σ ⟨c, hc⟩ : C) : K)) hσℓ
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, SMul.smul_stabilizer_def,
      hsmul, Equiv.Perm.one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hne : ∃ c ∈ C, g * c * g⁻¹ ≠ c := by
    by_contra! hall
    have hσ1 : MulAction.toPermHom (stabilizer (ConjAct K) C) C f = 1 := by
      ext ⟨c, hc⟩
      simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, SMul.smul_stabilizer_def,
        Equiv.Perm.one_apply, ConjAct.smul_def, ← hg]
      exact hall c hc
    rw [hσ1, orderOf_one] at hfℓ
    exact hℓ.one_lt.ne hfℓ
  have hgA : ∀ a ∈ A₀, g * a * g⁻¹ ∈ A₀ := fun a ha => by
    rw [hmemA₀] at ha ⊢
    exact ⟨conj_mem_closure hgC ha.1,
      (inferInstance : (commutator K).Normal).conj_mem a ha.2 g⟩
  have hgA' : ∀ a ∈ A₀, g⁻¹ * a * g ∈ A₀ := fun a ha => by
    rw [hmemA₀] at ha ⊢
    have h1 := conj_mem_closure hgC' ha.1
    rw [inv_inv] at h1
    exact ⟨h1, by simpa using
      (inferInstance : (commutator K).Normal).conj_mem a ha.2 g⁻¹⟩
  have hcA : ∀ a ∈ closure C, g ^ ℓ * a = a * g ^ ℓ := by
    intro a ha
    have : closure C ≤ centralizer {g ^ ℓ} := by
      rw [closure_le]
      intro c hc
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (hgℓ c hc).symm
    exact (mem_centralizer_singleton_iff.mp (this ha)).symm
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut A₀, τ = conjRestrict A₀ g hgA hgA' := ⟨_, rfl⟩
  have hτapp : ∀ (n : ℕ) (a : A₀), ((τ ^ n) a : K) = g ^ n * a * (g ^ n)⁻¹ := by
    intro n a
    rw [hτ]
    exact conjRestrict_pow_apply A₀ g hgA hgA' n a
  have hτℓ : τ ^ ℓ = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [hτapp, MulAut.one_apply, hcA a ((hmemA₀ a).mp a.2).1]
    group
  by_cases hτ1 : τ = 1
  ·
    have hcen : ∀ a ∈ A₀, g * a = a * g := by
      intro a ha
      have := hτapp 1 ⟨a, ha⟩
      rw [pow_one, hτ1, pow_one, MulAut.one_apply] at this
      exact mul_inv_eq_iff_eq_mul.mp this.symm
    obtain ⟨c, hc, hgc⟩ := hne
    exact hgc (conj_eq_of_commute (hℓ.odd_of_ne_two hℓ2) hgC hC hcen hA₀sq hgℓ c hc)
  · obtain ⟨j, hj0, hjr, hj⟩ := exists_two_pow_eq_one_of_mulAut hA₀card hℓ2 τ hτℓ hτ1
    have := orderOf_le_of_pow_eq_one hj0 hj
    omega

end CFSG.Monster.B.Generic
