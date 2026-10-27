module

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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement Matrix

namespace HS6

section Act

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def actM (A : Matrix (Fin 2) (Fin 2) K) (v : (ι → K) × (ι → K)) : (ι → K) × (ι → K) :=
  (A 0 0 • v.1 + A 0 1 • v.2, A 1 0 • v.1 + A 1 1 • v.2)

theorem actM_one (v : (ι → K) × (ι → K)) : actM (1 : Matrix (Fin 2) (Fin 2) K) v = v := by
  simp [actM, Matrix.one_apply]

theorem actM_mul (A B : Matrix (Fin 2) (Fin 2) K) (v : (ι → K) × (ι → K)) :
    actM (A * B) v = actM A (actM B v) := by
  simp only [actM, Matrix.mul_apply, Fin.sum_univ_two]
  refine Prod.ext ?_ ?_
  · show (A 0 0 * B 0 0 + A 0 1 * B 1 0) • v.1 + (A 0 0 * B 0 1 + A 0 1 * B 1 1) • v.2 =
      A 0 0 • (B 0 0 • v.1 + B 0 1 • v.2) + A 0 1 • (B 1 0 • v.1 + B 1 1 • v.2)
    module
  · show (A 1 0 * B 0 0 + A 1 1 * B 1 0) • v.1 + (A 1 0 * B 0 1 + A 1 1 * B 1 1) • v.2 =
      A 1 0 • (B 0 0 • v.1 + B 0 1 • v.2) + A 1 1 • (B 1 0 • v.1 + B 1 1 • v.2)
    module

theorem eq_of_actM_eq [Nonempty ι] {A B : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ v : (ι → K) × (ι → K), actM A v = actM B v) : A = B := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h1 := h (Pi.single i₀ 1, 0)
  have h2 := h (0, Pi.single i₀ 1)
  have e1 := congrFun (congrArg Prod.fst h1) i₀
  have e2 := congrFun (congrArg Prod.snd h1) i₀
  have e3 := congrFun (congrArg Prod.fst h2) i₀
  have e4 := congrFun (congrArg Prod.snd h2) i₀
  simp [actM] at e1 e2 e3 e4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, e2, e3, e4]

@[expose] def diagM (a : Matrix ι ι K) (v : (ι → K) × (ι → K)) : (ι → K) × (ι → K) :=
  (a *ᵥ v.1, a *ᵥ v.2)

theorem exists_mat {G : Type} [Group G] {X : Subgroup G} {a : G → Matrix ι ι K}
    (schur : ∀ f : (ι → K) →+ (ι → K), (∀ x ∈ X, ∀ v, f (a x *ᵥ v) = a x *ᵥ f v) →
      ∃ c : K, ∀ v, f v = c • v)
    (f : (ι → K) × (ι → K) →+ (ι → K) × (ι → K))
    (hf : ∀ x ∈ X, ∀ v, f (diagM (a x) v) = diagM (a x) (f v)) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, ∀ v, f v = actM A v := by
  let e₁ : (ι → K) →+ (ι → K) × (ι → K) := AddMonoidHom.inl _ _
  let e₂ : (ι → K) →+ (ι → K) × (ι → K) := AddMonoidHom.inr _ _
  let p₁ : (ι → K) × (ι → K) →+ (ι → K) := AddMonoidHom.fst _ _
  let p₂ : (ι → K) × (ι → K) →+ (ι → K) := AddMonoidHom.snd _ _
  have key : ∀ (e : (ι → K) →+ (ι → K) × (ι → K)) (p : (ι → K) × (ι → K) →+ (ι → K)),
      (∀ x : G, ∀ v : ι → K, e (a x *ᵥ v) = diagM (a x) (e v)) →
      (∀ x : G, ∀ v : (ι → K) × (ι → K), p (diagM (a x) v) = a x *ᵥ p v) →
      ∃ c : K, ∀ v, p (f (e v)) = c • v := by
    intro e p he hp
    refine schur (p.comp (f.comp e)) (fun x hx v => ?_)
    show p (f (e (a x *ᵥ v))) = a x *ᵥ p (f (e v))
    rw [he, hf x hx, hp]
  have he₁ : ∀ x : G, ∀ v : ι → K, e₁ (a x *ᵥ v) = diagM (a x) (e₁ v) := by
    intro x v
    show ((a x *ᵥ v, 0) : (ι → K) × (ι → K)) = (a x *ᵥ v, a x *ᵥ 0)
    rw [Matrix.mulVec_zero]
  have he₂ : ∀ x : G, ∀ v : ι → K, e₂ (a x *ᵥ v) = diagM (a x) (e₂ v) := by
    intro x v
    show ((0, a x *ᵥ v) : (ι → K) × (ι → K)) = (a x *ᵥ 0, a x *ᵥ v)
    rw [Matrix.mulVec_zero]
  have hp₁ : ∀ x : G, ∀ v : (ι → K) × (ι → K), p₁ (diagM (a x) v) = a x *ᵥ p₁ v :=
    fun x v => rfl
  have hp₂ : ∀ x : G, ∀ v : (ι → K) × (ι → K), p₂ (diagM (a x) v) = a x *ᵥ p₂ v :=
    fun x v => rfl
  obtain ⟨c₁₁, h₁₁⟩ := key e₁ p₁ he₁ hp₁
  obtain ⟨c₂₁, h₂₁⟩ := key e₁ p₂ he₁ hp₂
  obtain ⟨c₁₂, h₁₂⟩ := key e₂ p₁ he₂ hp₁
  obtain ⟨c₂₂, h₂₂⟩ := key e₂ p₂ he₂ hp₂
  refine ⟨!![c₁₁, c₁₂; c₂₁, c₂₂], fun v => ?_⟩
  have hv : v = e₁ v.1 + e₂ v.2 := by
    refine Prod.ext ?_ ?_ <;> simp [e₁, e₂]
  rw [hv, map_add]
  refine Prod.ext ?_ ?_
  · show p₁ (f (e₁ v.1)) + p₁ (f (e₂ v.2)) = _
    rw [h₁₁, h₁₂]
    simp [actM, e₁, e₂]
  · show p₂ (f (e₁ v.1)) + p₂ (f (e₂ v.2)) = _
    rw [h₂₁, h₂₂]
    simp [actM, e₁, e₂]

end Act

section Surj

variable {G : Type} [Group G] [Finite G] {Q Z : Subgroup G} {W : Type*} [AddCommGroup W] [Finite W]

theorem surj_of_card (Φ : G → W) (hZQ : Z ≤ Q) (hadd : ∀ x ∈ Q, ∀ y ∈ Q, Φ (x * y) = Φ x + Φ y)
    (hz : ∀ x ∈ Q, Φ x = 0 ↔ x ∈ Z) (hcard : Nat.card Q = Nat.card Z * Nat.card W) :
    ∀ w : W, ∃ x ∈ Q, Φ x = w := by
  have h1 : Φ 1 = 0 := (hz 1 Q.one_mem).mpr Z.one_mem
  let f : ↥Q →* Multiplicative W :=
    { toFun := fun x => Multiplicative.ofAdd (Φ (x : G))
      map_one' := by simp [h1]
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (Φ ((x : G) * (y : G))) = _
        rw [hadd _ x.2 _ y.2, ofAdd_add] }
  have hker : f.ker = Z.subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (Φ (x : G)) = 1 ↔ _
    rw [ofAdd_eq_one]
    exact hz _ x.2
  have hcr : Nat.card f.range = Nat.card W := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥Q ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.ker = Nat.card Z := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv
    rw [h2, h3, hcard] at h1
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    rw [mul_comm (Nat.card f.range)] at h1
    exact (Nat.eq_of_mul_eq_mul_left hZpos h1).symm
  have htop : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [hcr]
    exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative W ≃ W)).symm)
  intro w
  have hmem : Multiplicative.ofAdd w ∈ f.range := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, x.2, by simpa [f] using congrArg Multiplicative.toAdd hx⟩

end Surj

section Rep

variable {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

structure IsChart (Q Z X : Subgroup G) (Φ : G → (ι → K) × (ι → K)) (a : G → Matrix ι ι K) :
    Prop where
  comm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z
  Zle : Z ≤ Q
  add : ∀ x ∈ Q, ∀ y ∈ Q, Φ (x * y) = Φ x + Φ y
  zero_iff : ∀ x ∈ Q, Φ x = 0 ↔ x ∈ Z
  surj : ∀ w, ∃ x ∈ Q, Φ x = w
  Xnorm : ∀ x ∈ X, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q
  equi : ∀ x ∈ X, ∀ y ∈ Q, Φ (x * y * x⁻¹) = diagM (a x) (Φ y)
  schur : ∀ f : (ι → K) →+ (ι → K), (∀ x ∈ X, ∀ v, f (a x *ᵥ v) = a x *ᵥ f v) →
    ∃ c : K, ∀ v, f v = c • v

variable {Q Z X : Subgroup G} {Φ : G → (ι → K) × (ι → K)} {a : G → Matrix ι ι K}

theorem IsChart.one (hΦ : IsChart Q Z X Φ a) : Φ 1 = 0 :=
  (hΦ.zero_iff 1 Q.one_mem).mpr Z.one_mem

theorem IsChart.inv (hΦ : IsChart Q Z X Φ a) {x : G} (hx : x ∈ Q) : Φ x⁻¹ = -Φ x := by
  have h := hΦ.add x hx x⁻¹ (Q.inv_mem hx)
  rw [mul_inv_cancel, hΦ.one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem IsChart.conj_Q (hΦ : IsChart Q Z X Φ a) {q y : G} (hq : q ∈ Q) (hy : y ∈ Q) :
    Φ (q * y * q⁻¹) = Φ y := by
  have : q * y * q⁻¹ = ⁅q, y⁆ * y := by simp only [commutatorElement_def]; group
  rw [this, hΦ.add _ (hΦ.Zle (hΦ.comm q hq y hy)) y hy,
    (hΦ.zero_iff _ (hΦ.Zle (hΦ.comm q hq y hy))).mpr (hΦ.comm q hq y hy), zero_add]

theorem exists_rep [Nonempty ι] (hΦ : IsChart Q Z X Φ a) (C : Subgroup G)
    (hCQ : ∀ h ∈ C, ∀ y ∈ Q, h * y * h⁻¹ ∈ Q) (hCZ : ∀ h ∈ C, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z)
    (hCX : ∀ h ∈ C, ∀ x ∈ X, ⁅h, x⁆ ∈ Q) :
    ∃ ρ : C →* Matrix (Fin 2) (Fin 2) K,
      ∀ h : C, ∀ y ∈ Q, Φ ((h : G) * y * (h : G)⁻¹) = actM (ρ h) (Φ y) := by
  classical
  choose Λ hΛQ hΛ using hΦ.surj
  let f : G → (ι → K) × (ι → K) → (ι → K) × (ι → K) := fun h v => Φ (h * Λ v * h⁻¹)
  have hA : ∀ h ∈ C, ∀ y ∈ Q, Φ (h * y * h⁻¹) = f h (Φ y) := by
    intro h hh y hy
    have hΛy := hΛQ (Φ y)
    have hz : (Λ (Φ y))⁻¹ * y ∈ Z := by
      refine (hΦ.zero_iff _ (Q.mul_mem (Q.inv_mem hΛy) hy)).mp ?_
      rw [hΦ.add _ (Q.inv_mem hΛy) y hy, hΦ.inv hΛy, hΛ (Φ y)]
      abel
    have e : h * y * h⁻¹ = (h * Λ (Φ y) * h⁻¹) * (h * ((Λ (Φ y))⁻¹ * y) * h⁻¹) := by group
    rw [e, hΦ.add _ (hCQ h hh _ hΛy) _ (hΦ.Zle (hCZ h hh _ hz)),
      (hΦ.zero_iff _ (hΦ.Zle (hCZ h hh _ hz))).mpr (hCZ h hh _ hz), add_zero]
  have hadd : ∀ h ∈ C, ∀ v w, f h (v + w) = f h v + f h w := by
    intro h hh v w
    have h1 : Φ (Λ v * Λ w) = v + w := by rw [hΦ.add _ (hΛQ v) _ (hΛQ w), hΛ, hΛ]
    have h2 := hA h hh (Λ v * Λ w) (Q.mul_mem (hΛQ v) (hΛQ w))
    rw [h1] at h2
    rw [← h2]
    have e : h * (Λ v * Λ w) * h⁻¹ = (h * Λ v * h⁻¹) * (h * Λ w * h⁻¹) := by group
    rw [e, hΦ.add _ (hCQ h hh _ (hΛQ v)) _ (hCQ h hh _ (hΛQ w))]
  have hcomm : ∀ h ∈ C, ∀ x ∈ X, ∀ v, f h (diagM (a x) v) = diagM (a x) (f h v) := by
    intro h hh x hx v
    have hΛv := hΛQ v
    have hxΛ : x * Λ v * x⁻¹ ∈ Q := hΦ.Xnorm x hx _ hΛv
    have hhΛ : h * Λ v * h⁻¹ ∈ Q := hCQ h hh _ hΛv
    have e1 : diagM (a x) v = Φ (x * Λ v * x⁻¹) := by rw [hΦ.equi x hx _ hΛv, hΛ]
    have e2 : diagM (a x) (f h v) = Φ (x * (h * Λ v * h⁻¹) * x⁻¹) := by
      rw [hΦ.equi x hx _ hhΛ]
    rw [e1, ← hA h hh _ hxΛ, e2]
    have hq : ⁅h, x⁆ ∈ Q := hCX h hh x hx
    have hy₁ : x * (h * Λ v * h⁻¹) * x⁻¹ ∈ Q := hΦ.Xnorm x hx _ hhΛ
    have e : h * (x * Λ v * x⁻¹) * h⁻¹ = ⁅h, x⁆ * (x * (h * Λ v * h⁻¹) * x⁻¹) * ⁅h, x⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hΦ.conj_Q hq hy₁
  have hmat : ∀ h : C, ∃ A : Matrix (Fin 2) (Fin 2) K, ∀ v, f h v = actM A v := by
    intro h
    exact exists_mat hΦ.schur (AddMonoidHom.mk' (f h) (hadd h h.2)) (hcomm h h.2)
  choose A hA' using hmat
  have h1 : ∀ v, f 1 v = v := fun v => by
    show Φ (1 * Λ v * 1⁻¹) = v
    rw [one_mul, inv_one, mul_one, hΛ]
  have hmul : ∀ h h' : C, ∀ v, f (h * h' : C) v = f h (f h' v) := by
    intro h h' v
    have hy : (h' : G) * Λ v * (h' : G)⁻¹ ∈ Q := hCQ h' h'.2 _ (hΛQ v)
    have := hA h h.2 _ hy
    have e : (h : G) * ((h' : G) * Λ v * (h' : G)⁻¹) * (h : G)⁻¹ =
        ((h * h' : C) : G) * Λ v * ((h * h' : C) : G)⁻¹ := by
      simp only [Subgroup.coe_mul, mul_inv_rev]; group
    rw [e] at this
    rw [show f (h * h' : C) v = Φ (((h * h' : C) : G) * Λ v * ((h * h' : C) : G)⁻¹) from rfl,
      this]
  refine ⟨{ toFun := A
            map_one' := ?_
            map_mul' := ?_ }, fun h y hy => ?_⟩
  · apply eq_of_actM_eq (ι := ι)
    intro v
    rw [← hA', actM_one]
    exact h1 v
  · intro h h'
    apply eq_of_actM_eq (ι := ι)
    intro v
    rw [← hA', actM_mul, ← hA', ← hA', hmul]
  · show Φ ((h : G) * y * (h : G)⁻¹) = actM (A h) (Φ y)
    rw [hA h h.2 y hy, hA']

theorem scalar_eq_of_smul_eq [Nonempty ι] {c d : K} (h : ∀ u : ι → K, c • u = d • u) : c = d := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have := congrFun (h (fun _ => 1)) i₀
  simpa using this

theorem conj_eq_comm_mul (h y : G) : h * y * h⁻¹ = ⁅h, y⁆ * y := by
  simp only [commutatorElement_def]; group

theorem comm_mem_Z_of_rho_one [Nonempty ι] (hΦ : IsChart Q Z X Φ a) (C : Subgroup G)
    (ρ : C →* Matrix (Fin 2) (Fin 2) K)
    (hρ : ∀ h : C, ∀ y ∈ Q, Φ ((h : G) * y * (h : G)⁻¹) = actM (ρ h) (Φ y))
    (hCQ : ∀ h ∈ C, ∀ y ∈ Q, h * y * h⁻¹ ∈ Q) (h : C) (h1 : ρ h = 1) :
    ∀ y ∈ Q, ⁅(h : G), y⁆ ∈ Z := by
  intro y hy
  have hq : ⁅(h : G), y⁆ ∈ Q := by
    have := Q.mul_mem (hCQ h h.2 y hy) (Q.inv_mem hy)
    simpa [commutatorElement_def, mul_assoc] using this
  have h2 := hρ h y hy
  rw [h1, actM_one, conj_eq_comm_mul, hΦ.add _ hq y hy] at h2
  exact (hΦ.zero_iff _ hq).mp (by simpa using h2)

theorem rho_eq_one_of_mem_Q [Nonempty ι] (hΦ : IsChart Q Z X Φ a) (C : Subgroup G)
    (ρ : C →* Matrix (Fin 2) (Fin 2) K)
    (hρ : ∀ h : C, ∀ y ∈ Q, Φ ((h : G) * y * (h : G)⁻¹) = actM (ρ h) (Φ y))
    (h : C) (hq : (h : G) ∈ Q) : ρ h = 1 := by
  refine eq_of_actM_eq (ι := ι) fun v => ?_
  obtain ⟨y, hy, rfl⟩ := hΦ.surj v
  rw [actM_one, ← hρ h y hy]
  exact hΦ.conj_Q hq hy

theorem rho_upper [Nonempty ι] (hΦ : IsChart Q Z X Φ a) {V : Subgroup G} (hVQ : V ≤ Q)
    (hsnd0 : ∀ x ∈ Q, (Φ x).2 = 0 ↔ x ∈ V) (C : Subgroup G)
    (ρ : C →* Matrix (Fin 2) (Fin 2) K)
    (hρ : ∀ h : C, ∀ y ∈ Q, Φ ((h : G) * y * (h : G)⁻¹) = actM (ρ h) (Φ y))
    (h : C) (hv : ∀ v ∈ V, ⁅(h : G), v⁆ ∈ Z) (hQV : ∀ y ∈ Q, ⁅(h : G), y⁆ ∈ V) :
    ρ h 0 0 = 1 ∧ ρ h 1 0 = 0 ∧ ρ h 1 1 = 1 := by
  have key : ∀ y ∈ Q, Φ ((h : G) * y * (h : G)⁻¹) = Φ ⁅(h : G), y⁆ + Φ y := by
    intro y hy
    rw [conj_eq_comm_mul, hΦ.add _ (hVQ (hQV y hy)) y hy]
  have h2 : ∀ y ∈ Q, (Φ ⁅(h : G), y⁆).2 = 0 := fun y hy => (hsnd0 _ (hVQ (hQV y hy))).mpr (hQV y hy)
  have hrow : ∀ u w : ι → K, ρ h 1 0 • u + ρ h 1 1 • w = w := by
    intro u w
    obtain ⟨y, hy, hyuw⟩ := hΦ.surj (u, w)
    have := congrArg Prod.snd (hρ h y hy)
    rw [key y hy, hyuw] at this
    simpa [actM, h2 y hy] using this.symm
  have h10 : ρ h 1 0 = 0 := by
    refine scalar_eq_of_smul_eq (ι := ι) fun u => ?_
    have := hrow u 0
    simpa using this
  have h11 : ρ h 1 1 = 1 := by
    refine scalar_eq_of_smul_eq (ι := ι) fun u => ?_
    have := hrow 0 u
    simpa using this
  have h00 : ρ h 0 0 = 1 := by
    refine scalar_eq_of_smul_eq (ι := ι) fun u => ?_
    obtain ⟨y, hy, hyu⟩ := hΦ.surj (u, 0)
    have hyV : y ∈ V := (hsnd0 y hy).mp (by rw [hyu])
    have hz : Φ ⁅(h : G), y⁆ = 0 := (hΦ.zero_iff _ (hVQ (hQV y hy))).mpr (hv y hyV)
    have := congrArg Prod.fst (hρ h y hy)
    rw [key y hy, hz, hyu] at this
    simpa [actM] using this.symm
  exact ⟨h00, h10, h11⟩

theorem rho_lower [Nonempty ι] (hΦ : IsChart Q Z X Φ a) {V' : Subgroup G} (hVQ : V' ≤ Q)
    (hfst0 : ∀ x ∈ Q, (Φ x).1 = 0 ↔ x ∈ V') (C : Subgroup G)
    (ρ : C →* Matrix (Fin 2) (Fin 2) K)
    (hρ : ∀ h : C, ∀ y ∈ Q, Φ ((h : G) * y * (h : G)⁻¹) = actM (ρ h) (Φ y))
    (h : C) (hv : ∀ v ∈ V', ⁅(h : G), v⁆ ∈ Z) (hQV : ∀ y ∈ Q, ⁅(h : G), y⁆ ∈ V') :
    ρ h 0 0 = 1 ∧ ρ h 0 1 = 0 ∧ ρ h 1 1 = 1 := by
  have key : ∀ y ∈ Q, Φ ((h : G) * y * (h : G)⁻¹) = Φ ⁅(h : G), y⁆ + Φ y := by
    intro y hy
    rw [conj_eq_comm_mul, hΦ.add _ (hVQ (hQV y hy)) y hy]
  have h2 : ∀ y ∈ Q, (Φ ⁅(h : G), y⁆).1 = 0 := fun y hy => (hfst0 _ (hVQ (hQV y hy))).mpr (hQV y hy)
  have hrow : ∀ u w : ι → K, ρ h 0 0 • u + ρ h 0 1 • w = u := by
    intro u w
    obtain ⟨y, hy, hyuw⟩ := hΦ.surj (u, w)
    have := congrArg Prod.fst (hρ h y hy)
    rw [key y hy, hyuw] at this
    simpa [actM, h2 y hy] using this.symm
  have h00 : ρ h 0 0 = 1 := by
    refine scalar_eq_of_smul_eq (ι := ι) fun u => ?_
    have := hrow u 0
    simpa using this
  have h01 : ρ h 0 1 = 0 := by
    refine scalar_eq_of_smul_eq (ι := ι) fun u => ?_
    have := hrow 0 u
    simpa using this
  have h11 : ρ h 1 1 = 1 := by
    refine scalar_eq_of_smul_eq (ι := ι) fun u => ?_
    obtain ⟨y, hy, hyu⟩ := hΦ.surj (0, u)
    have hyV : y ∈ V' := (hfst0 y hy).mp (by rw [hyu])
    have hz : Φ ⁅(h : G), y⁆ = 0 := (hΦ.zero_iff _ (hVQ (hQV y hy))).mpr (hv y hyV)
    have := congrArg Prod.snd (hρ h y hy)
    rw [key y hy, hz, hyu] at this
    simpa [actM] using this.symm
  exact ⟨h00, h01, h11⟩

end Rep

theorem surj_of_ker {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
    {T Q : Subgroup G} (hQT : Q ≤ T) (f : ↥T →* Multiplicative K)
    (hker : ∀ x : ↥T, f x = 1 ↔ (x : G) ∈ Q) (hcard : Nat.card T = Nat.card Q * Nat.card K) :
    ∀ lam : K, ∃ x : ↥T, f x = Multiplicative.ofAdd lam := by
  have hker' : f.ker = Q.subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker x
  have hcr : Nat.card f.range = Nat.card K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥T ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.ker = Nat.card Q := by
      rw [hker']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv
    rw [h2, h3, hcard] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    rw [mul_comm (Nat.card f.range)] at h1
    exact (Nat.eq_of_mul_eq_mul_left hQpos h1).symm
  have htop : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [hcr]
    exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)).symm)
  intro lam
  have hmem : Multiplicative.ofAdd lam ∈ f.range := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, hx⟩

end HS6

end CFSG.RankThree.GF2n.Stroth80
