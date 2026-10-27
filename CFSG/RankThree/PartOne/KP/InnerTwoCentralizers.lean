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

namespace CFSG.RankThree.PartOne

open Subgroup

@[expose] def restrictAut {P : Type*} [Group P] (α : MulAut P) (H : Subgroup P)
    (h : ∀ x, x ∈ H ↔ α x ∈ H) : MulAut H where
  toFun x := ⟨α x, (h x).1 x.2⟩
  invFun x := ⟨α.symm x, (h (α.symm x)).2 (by simp)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

@[simp] theorem restrictAut_coe {P : Type*} [Group P] (α : MulAut P) (H : Subgroup P)
    (h : ∀ x, x ∈ H ↔ α x ∈ H) (x : H) : (restrictAut α H h x : P) = α x := rfl

theorem exists_induced_aut {M Q : Type*} [Group M] [Group Q] (φ : M →* Q)
    (hφ : Function.Surjective φ) (β : MulAut M) (hK : φ.ker.map β.toMonoidHom = φ.ker) :
    ∃ δ : MulAut Q, ∀ x : M, δ (φ x) = φ (β x) := by
  let e : (M ⧸ φ.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let c : (M ⧸ φ.ker) ≃* (M ⧸ φ.ker) := QuotientGroup.congr φ.ker φ.ker β hK
  refine ⟨e.symm.trans (c.trans e), fun x => ?_⟩
  have h1 : e.symm (φ x) = (QuotientGroup.mk x : M ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show e (c (e.symm (φ x))) = φ (β x)
  rw [h1]
  rfl

theorem eq_one_of_perfect_of_central {M : Type*} [Group M] (u : M →* Subgroup.center M)
    {L : Subgroup M} (hL : Group.IsPerfect L) (x : M) (hx : x ∈ L) : u x = 1 := by
  let φ : L →* Subgroup.center M := u.comp L.subtype
  have h1 : commutator L ≤ φ.ker := Abelianization.commutator_subset_ker φ
  have h2 : commutator L = ⊤ := hL.commutator_eq_top
  rw [h2] at h1
  have := h1 (Subgroup.mem_top ⟨x, hx⟩)
  exact this

theorem mem_smul_sylow_iff {P : Type*} [Group P] {p : ℕ} (S : Sylow p P) (g x : P) :
    x ∈ ((g • S : Sylow p P) : Subgroup P) ↔ g⁻¹ * x * g ∈ (S : Subgroup P) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * (MulAut.conj g • y) * g = y := by
      rw [MulAut.smul_def, MulAut.conj_apply]
      group
    rwa [e]
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply]
    group

theorem mem_centralizer_iff_of_fix {P : Type*} [Group P] (β : MulAut P) {t : P} (h : β t = t)
    (x : P) : x ∈ Subgroup.centralizer ({t} : Set P) ↔
      β x ∈ Subgroup.centralizer ({t} : Set P) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc β x * t = β x * β t := by rw [h]
      _ = β (x * t) := (map_mul _ _ _).symm
      _ = β (t * x) := by rw [hx]
      _ = t * β x := by rw [map_mul, h]
  · intro hx
    apply β.injective
    rw [map_mul, map_mul, h]
    exact hx

theorem allInner_of_two_centralizers {P Q : Type*} [Group P] [Finite P] [Group Q]
    (T : Sylow 2 P) {z t : P} (hz1 : z ≠ 1)
    (hZT : ∀ x : P, (x ∈ (T : Subgroup P) ∧ ∀ y ∈ (T : Subgroup P), x * y = y * x) ↔
      x = 1 ∨ x = z)
    (htz : z * t = t * z)
    (hMall : ∀ α : MulAut (Subgroup.centralizer ({z} : Set P)),
      ∃ m : Subgroup.centralizer ({z} : Set P), α = MulAut.conj m)
    (htM1 : t ∈ Subgroup.centralizer ({t} : Set P))
    {L : Subgroup (Subgroup.centralizer ({t} : Set P))} (hLperf : Group.IsPerfect L)
    (hLsup : L ⊔ Subgroup.zpowers (⟨t, htM1⟩ : Subgroup.centralizer ({t} : Set P)) = ⊤)
    (κ : Subgroup.centralizer ({t} : Set P) →* Q) (hκsurj : Function.Surjective κ)
    (hκker : κ.ker = Subgroup.zpowers (⟨t, htM1⟩ : Subgroup.centralizer ({t} : Set P)))
    {D0 : Subgroup P} (hD0M : D0 ≤ Subgroup.centralizer ({z} : Set P))
    (V : Sylow 2 Q)
    (hV : ∀ v ∈ (V : Subgroup Q), ∃ d : Subgroup.centralizer ({t} : Set P), (d : P) ∈ D0 ∧ κ d = v)
    (hQ : ∀ (W : Sylow 2 Q) (δ : MulAut Q), (∀ w ∈ (W : Subgroup Q), δ w = w) →
      ∃ c : (W : Subgroup Q), c ∈ Subgroup.center (W : Subgroup Q) ∧
        ∀ g : Q, δ g = (c : Q) * g * (c : Q)⁻¹)
    (hC : ∀ q : Q, (∀ d : Subgroup.centralizer ({t} : Set P), (d : P) ∈ D0 →
        q * κ d = κ d * q) →
      q = 1 ∨ q = κ ⟨z, Subgroup.mem_centralizer_singleton_iff.2 htz⟩)
    (hMM1 : Subgroup.centralizer ({z} : Set P) ⊔ Subgroup.centralizer ({t} : Set P) = ⊤)
    (htM : t ∈ Subgroup.centralizer ({z} : Set P)) :
    ∀ α : MulAut P, ∃ g : P, α = MulAut.conj g := by
  intro α
  classical
  have hzS : z ∈ (T : Subgroup P) := ((hZT z).2 (Or.inr rfl)).1
  have hzc : ∀ y ∈ (T : Subgroup P), z * y = y * z := ((hZT z).2 (Or.inr rfl)).2
  have hsurj : Function.Surjective (α.toMonoidHom) := α.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (T.mapSurjective hsurj) T
  set α₁ : MulAut P := MulAut.conj g * α with hα₁def
  have hα₁ : ∀ x, α₁ x = g * α x * g⁻¹ := fun x => by
    rw [hα₁def, MulAut.mul_apply, MulAut.conj_apply]
  have hTα : ∀ x, x ∈ (T : Subgroup P) ↔ α₁ x ∈ (T : Subgroup P) := by
    intro x
    have h1 : α₁ x ∈ (T : Subgroup P) ↔
        g⁻¹ * α₁ x * g ∈ ((T.mapSurjective hsurj : Sylow 2 P) : Subgroup P) := by
      rw [← mem_smul_sylow_iff, hg]
    rw [h1, hα₁]
    have e : g⁻¹ * (g * α x * g⁻¹) * g = α x := by group
    rw [e, Sylow.coe_mapSurjective]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := α.injective hyx
      rwa [this] at hy
  have hα₁z : α₁ z = z := by
    have hmemT : α₁ z ∈ (T : Subgroup P) := (hTα z).1 hzS
    have hcomm : ∀ y ∈ (T : Subgroup P), α₁ z * y = y * α₁ z := by
      intro y hy
      have hy' : α₁.symm y ∈ (T : Subgroup P) := (hTα _).2 (by simpa using hy)
      have h2 := hzc _ hy'
      calc α₁ z * y = α₁ z * α₁ (α₁.symm y) := by simp
        _ = α₁ (z * α₁.symm y) := (map_mul _ _ _).symm
        _ = α₁ (α₁.symm y * z) := by rw [h2]
        _ = α₁ (α₁.symm y) * α₁ z := map_mul _ _ _
        _ = y * α₁ z := by simp
    rcases (hZT (α₁ z)).1 ⟨hmemT, hcomm⟩ with h | h
    · exact absurd (α₁.injective (by rw [h, map_one])) hz1
    · exact h
  have hMα := mem_centralizer_iff_of_fix α₁ hα₁z
  obtain ⟨m, hm⟩ := hMall (restrictAut α₁ _ hMα)
  have hmx : ∀ x : Subgroup.centralizer ({z} : Set P), α₁ x = (m : P) * x * (m : P)⁻¹ := by
    intro x
    have := congrArg (fun f : MulAut (Subgroup.centralizer ({z} : Set P)) => (f x : P)) hm
    simpa using this
  set β : MulAut P := (MulAut.conj (m : P))⁻¹ * α₁ with hβdef
  have hβ : ∀ x, β x = (m : P)⁻¹ * α₁ x * (m : P) := fun x => by
    rw [hβdef, MulAut.mul_apply, MulAut.conj_inv_apply]
  have hβM : ∀ x ∈ Subgroup.centralizer ({z} : Set P), β x = x := by
    intro x hx
    rw [hβ, hmx ⟨x, hx⟩]
    group
  have hβt : β t = t := hβM t htM
  have hM1β := mem_centralizer_iff_of_fix β hβt
  set βM1 : MulAut (Subgroup.centralizer ({t} : Set P)) := restrictAut β _ hM1β with hβM1def
  have hβM1 : ∀ x : Subgroup.centralizer ({t} : Set P), (βM1 x : P) = β x := fun x => rfl
  have ht'fix : βM1 ⟨t, htM1⟩ = ⟨t, htM1⟩ := Subtype.ext hβt
  have hK : κ.ker.map βM1.toMonoidHom = κ.ker := by
    rw [hκker, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers ht'fix
  obtain ⟨δ, hδ⟩ := exists_induced_aut κ hκsurj βM1 hK
  have hfixD : ∀ d : Subgroup.centralizer ({t} : Set P), (d : P) ∈ D0 → βM1 d = d := fun d hd =>
    Subtype.ext (by rw [hβM1]; exact hβM _ (hD0M hd))
  have hδfix : ∀ w ∈ (V : Subgroup Q), δ w = w := by
    intro w hw
    obtain ⟨d, hd, rfl⟩ := hV w hw
    rw [hδ, hfixD d hd]
  obtain ⟨c, -, hc⟩ := hQ V δ hδfix
  have hcD : ∀ d : Subgroup.centralizer ({t} : Set P), (d : P) ∈ D0 →
      (c : Q) * κ d = κ d * (c : Q) := by
    intro d hd
    have h1 := hc (κ d)
    rw [hδ, hfixD d hd] at h1
    calc (c : Q) * κ d = (c : Q) * κ d * (c : Q)⁻¹ * (c : Q) := by group
      _ = κ d * (c : Q) := by rw [← h1]
  have hkey : ∀ (η : MulAut P) (ε : MulAut (Subgroup.centralizer ({t} : Set P))),
      (∀ x : Subgroup.centralizer ({t} : Set P), (ε x : P) = η x) →
      (∀ x ∈ Subgroup.centralizer ({z} : Set P), η x = x) →
      (∀ x : Subgroup.centralizer ({t} : Set P), κ (ε x) = δ (κ x)) →
      ε ⟨t, htM1⟩ = ⟨t, htM1⟩ → β = η := by
    intro η ε hεη hηM hεκ hεt
    have hker : ∀ x : Subgroup.centralizer ({t} : Set P), (ε x)⁻¹ * βM1 x ∈ κ.ker := by
      intro x
      rw [MonoidHom.mem_ker, map_mul, map_inv, hεκ, ← hδ, inv_mul_cancel]
    have hcentral : ∀ x : Subgroup.centralizer ({t} : Set P), (ε x)⁻¹ * βM1 x ∈
        Subgroup.center (Subgroup.centralizer ({t} : Set P)) := by
      intro x
      have h1 := hker x
      rw [hκker] at h1
      refine (Subgroup.zpowers_le.2 ?_) h1
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)
    let u : Subgroup.centralizer ({t} : Set P) →*
        Subgroup.center (Subgroup.centralizer ({t} : Set P)) :=
      { toFun := fun x => ⟨(ε x)⁻¹ * βM1 x, hcentral x⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro x y
          apply Subtype.ext
          have hc1 := Subgroup.mem_center_iff.1 (hcentral x) (ε y)⁻¹
          simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
          calc (ε y)⁻¹ * (ε x)⁻¹ * (βM1 x * βM1 y)
              = (ε y)⁻¹ * ((ε x)⁻¹ * βM1 x) * βM1 y := by group
            _ = ((ε x)⁻¹ * βM1 x) * (ε y)⁻¹ * βM1 y := by rw [← hc1]
            _ = ((ε x)⁻¹ * βM1 x) * ((ε y)⁻¹ * βM1 y) := by group }
    have hu : ∀ x : Subgroup.centralizer ({t} : Set P), u x = 1 := by
      intro x
      have hLle : L ≤ u.ker := fun y hy => eq_one_of_perfect_of_central u hLperf y hy
      have htle : Subgroup.zpowers (⟨t, htM1⟩ : Subgroup.centralizer ({t} : Set P)) ≤ u.ker := by
        rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
        apply Subtype.ext
        show (ε ⟨t, htM1⟩)⁻¹ * βM1 ⟨t, htM1⟩ = 1
        rw [hεt, ht'fix, inv_mul_cancel]
      have : x ∈ u.ker := by
        have h2 : x ∈ L ⊔ Subgroup.zpowers (⟨t, htM1⟩ : Subgroup.centralizer ({t} : Set P)) := by
          rw [hLsup]
          exact Subgroup.mem_top x
        exact (sup_le hLle htle) h2
      exact this
    have hβε : ∀ x : Subgroup.centralizer ({t} : Set P), βM1 x = ε x := by
      intro x
      have h1 := congrArg Subtype.val (hu x)
      have h2 : (ε x)⁻¹ * βM1 x = 1 := h1
      exact (inv_mul_eq_one.1 h2).symm
    have hle1 : Subgroup.centralizer ({z} : Set P) ≤
        MonoidHom.eqLocus β.toMonoidHom η.toMonoidHom := fun x hx => by
      change β x = η x
      rw [hβM x hx, hηM x hx]
    have hle2 : Subgroup.centralizer ({t} : Set P) ≤
        MonoidHom.eqLocus β.toMonoidHom η.toMonoidHom := fun x hx => by
      change β x = η x
      have := hβε ⟨x, hx⟩
      rw [← hεη ⟨x, hx⟩, ← hβM1 ⟨x, hx⟩, this]
    have hle : (⊤ : Subgroup P) ≤ MonoidHom.eqLocus β.toMonoidHom η.toMonoidHom := by
      rw [← hMM1]
      exact sup_le hle1 hle2
    ext x
    exact hle (Subgroup.mem_top x)
  have hα : α = MulAut.conj g⁻¹ * α₁ := by
    ext x
    show α x = g⁻¹ * α₁ x * g⁻¹⁻¹
    rw [hα₁]
    group
  have hα₁β : α₁ = MulAut.conj (m : P) * β := by
    ext x
    show α₁ x = (m : P) * β x * (m : P)⁻¹
    rw [hβ]
    group
  have hzM1 : z ∈ Subgroup.centralizer ({t} : Set P) :=
    Subgroup.mem_centralizer_singleton_iff.2 htz
  rcases hC (c : Q) hcD with h1 | h1
  ·
    have hβ1 : β = 1 := by
      refine hkey 1 1 (fun x => rfl) (fun x _ => rfl) (fun x => ?_) rfl
      rw [hc (κ x), h1]
      simp
    refine ⟨g⁻¹ * m, ?_⟩
    rw [hα, hα₁β, hβ1, mul_one, map_mul]
  ·
    set z' : Subgroup.centralizer ({t} : Set P) := ⟨z, hzM1⟩ with hz'
    have hβz : β = MulAut.conj z := by
      refine hkey (MulAut.conj z) (MulAut.conj z') (fun x => rfl) ?_ (fun x => ?_) ?_
      · intro x hx
        rw [MulAut.conj_apply]
        have := Subgroup.mem_centralizer_singleton_iff.1 hx
        calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [this]
          _ = x := by group
      · rw [hc (κ x), h1]
        simp only [map_mul, map_inv, MulAut.conj_apply]
      · apply Subtype.ext
        rw [MulAut.conj_apply]
        have := Subgroup.mem_centralizer_singleton_iff.1 hzM1
        show z * t * z⁻¹ = t
        calc z * t * z⁻¹ = t * z * z⁻¹ := by rw [htz]
          _ = t := by group
    refine ⟨g⁻¹ * (m * z), ?_⟩
    rw [hα, hα₁β, hβz, map_mul, map_mul]

end CFSG.RankThree.PartOne
