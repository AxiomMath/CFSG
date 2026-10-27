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
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.KFBloom

open Matrix Polynomial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem eq_one_of_commute_irreducible {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 0 < n)
    (H : Subgroup (GL (Fin n) (ZMod p)))
    (hirr : ∀ W : Submodule (ZMod p) (Fin n → ZMod p),
      (∀ g : H, ∀ w ∈ W,
        ((g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤)
    {u : GL (Fin n) (ZMod p)} (hup : u ^ p = 1) (hcomm : ∀ g ∈ H, g * u = u * g) : u = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set U : Matrix (Fin n) (Fin n) (ZMod p) := (u : Matrix (Fin n) (Fin n) (ZMod p)) with hU
  set N : Matrix (Fin n) (Fin n) (ZMod p) := U - 1 with hN
  have hNp : N ^ p = 0 := by
    have h1 : N ^ p = U ^ p - 1 ^ p :=
      sub_pow_char_of_commute (R := Matrix (Fin n) (Fin n) (ZMod p)) p (Commute.one_right U)
    have h2 : U ^ p = 1 := by
      have := congrArg (fun x : GL (Fin n) (ZMod p) => (x : Matrix (Fin n) (Fin n) (ZMod p))) hup
      simpa [hU] using this
    rw [h1, h2]
    simp
  let W : Submodule (ZMod p) (Fin n → ZMod p) := LinearMap.ker (Matrix.toLin' N)
  have hWinv : ∀ g : H, ∀ w ∈ W,
      ((g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w ∈ W := by
    intro g w hw
    have hw' : N *ᵥ w = 0 := hw
    have hcg : ((g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) * N =
        N * ((g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) := by
      have := congrArg (fun x : GL (Fin n) (ZMod p) => (x : Matrix (Fin n) (Fin n) (ZMod p)))
        (hcomm g g.2)
      simp only [Units.val_mul] at this
      simp only [hN, hU, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, this]
    show N *ᵥ (((g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w) = 0
    rw [Matrix.mulVec_mulVec, ← hcg, ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]
  rcases hirr W hWinv with hbot | htop
  · exfalso
    have hinj : ∀ w : Fin n → ZMod p, N *ᵥ w = 0 → w = 0 := by
      intro w hw
      have : w ∈ W := hw
      rw [hbot] at this
      simpa using this
    have key : ∀ k : ℕ, ∀ w : Fin n → ZMod p, (N ^ k) *ᵥ w = 0 → w = 0 := by
      intro k
      induction k with
      | zero => intro w hw; simpa using hw
      | succ k ih =>
        intro w hw
        apply ih
        apply hinj
        rw [Matrix.mulVec_mulVec, ← pow_succ']
        exact hw
    have := key p (Pi.single ⟨0, hn⟩ 1) (by rw [hNp, Matrix.zero_mulVec])
    have h1 := congrFun this ⟨0, hn⟩
    simp at h1
  · have hN0 : N = 0 := by
      ext i j
      have : N *ᵥ (Pi.single j 1) = 0 := by
        have : (Pi.single j (1 : ZMod p)) ∈ W := by rw [htop]; trivial
        exact this
      have h2 := congrFun this i
      simpa [Matrix.mulVec_single_one] using h2
    have : U = 1 := sub_eq_zero.mp hN0
    exact Units.ext this

theorem self_eq_of_iterate_prime {α : Type*} [Finite α] {p : ℕ} [Fact p.Prime]
    (hα : Nat.card α < p) (σ : α → α) (hper : ∀ i, σ^[p] i = i) : ∀ i, σ i = i := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  have hinj : Function.Injective σ := by
    refine Function.LeftInverse.injective (g := σ^[q]) fun i => ?_
    have := hper i
    rw [hq, Function.iterate_succ_apply] at this
    exact this
  have hsurj : Function.Surjective σ := by
    refine Function.RightInverse.surjective (g := σ^[q]) fun i => ?_
    have := hper i
    rw [hq, Function.iterate_succ_apply'] at this
    exact this
  let τ : Equiv.Perm α := Equiv.ofBijective σ ⟨hinj, hsurj⟩
  have hτσ : (⇑τ) = σ := rfl
  have hτ : τ ^ p = 1 := by
    refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.coe_pow, hτσ]
    exact hper i
  have h1 : orderOf τ ∣ p := orderOf_dvd_of_pow_eq_one hτ
  have h2 : orderOf τ ∣ (Fintype.card α).factorial := by
    have := orderOf_dvd_natCard τ
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm] at this
  have h3 : orderOf τ = 1 := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp h2
      rw [Nat.card_eq_fintype_card] at hα
      omega
  have h4 : τ = 1 := orderOf_eq_one_iff.mp h3
  intro i
  have := congrArg (fun f : Equiv.Perm α => f i) h4
  simpa [hτσ] using this

theorem gl_eq_one_of_fixes_iSup_eq_top {K : Type*} [Field K] {n : ℕ}
    (L : Fin n → Submodule K (Fin n → K)) (hsup : ⨆ i, L i = ⊤)
    {g : GL (Fin n) K} (hfix : ∀ i, ∀ v ∈ L i, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v) :
    g = 1 := by
  have h1 : ∀ v : Fin n → K, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
    intro v
    have hv : v ∈ ⨆ i, L i := by rw [hsup]; trivial
    refine Submodule.iSup_induction L
      (motive := fun w => (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w)
      hv (fun i w hw => hfix i w hw) (by simp) (fun a b ha hb => by
        rw [Matrix.mulVec_add, ha, hb])
  apply Units.ext
  ext i j
  have := congrFun (h1 (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem gl_fixes_line {p n : ℕ} [Fact p.Prime] (W : Submodule (ZMod p) (Fin n → ZMod p))
    (hdim : Module.finrank (ZMod p) W = 1) {g : GL (Fin n) (ZMod p)} (hgp : g ^ p = 1)
    (hstab : ∀ v ∈ W, (g : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ v ∈ W) :
    ∀ v ∈ W, (g : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ v = v := by
  obtain ⟨v0, hv0ne, hv0⟩ := (finrank_eq_one_iff' (K := ZMod p) (V := W)).mp hdim
  obtain ⟨c, hc⟩ := hv0 ⟨(g : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ (v0 : Fin n → ZMod p),
    hstab _ v0.2⟩
  have hgv0 : (g : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ (v0 : Fin n → ZMod p) =
      c • (v0 : Fin n → ZMod p) := by
    have := congrArg Subtype.val hc
    simpa using this.symm
  have hpow : ∀ k : ℕ, ((g ^ k : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ
      (v0 : Fin n → ZMod p) = c ^ k • (v0 : Fin n → ZMod p) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hgv0,
        smul_smul, pow_succ]
  have hc1 : c = 1 := by
    have h1 := hpow p
    rw [hgp] at h1
    simp only [Units.val_one, Matrix.one_mulVec] at h1
    have h2 : (c ^ p - 1) • (v0 : Fin n → ZMod p) = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    have hv0' : (v0 : Fin n → ZMod p) ≠ 0 := fun h => hv0ne (Subtype.ext h)
    have h3 := (smul_eq_zero.mp h2).resolve_right hv0'
    have h4 : c ^ p = c := ZMod.pow_card c
    rw [h4] at h3
    exact sub_eq_zero.mp h3
  intro v hv
  obtain ⟨d, hd⟩ := hv0 ⟨v, hv⟩
  have hdv : d • (v0 : Fin n → ZMod p) = v := congrArg Subtype.val hd
  rw [← hdv, Matrix.mulVec_smul, hgv0, hc1, one_smul]

theorem eq_one_of_monomial {p n : ℕ} [Fact p.Prime] (hpn : n < p)
    (L : Fin n → Submodule (ZMod p) (Fin n → ZMod p)) (hint : DirectSum.IsInternal L)
    (hdim : ∀ i, Module.finrank (ZMod p) (L i) = 1)
    {g : GL (Fin n) (ZMod p)} (hgp : g ^ p = 1)
    (hperm : ∀ i, ∃ j,
      (L i).map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) (ZMod p))) = L j) :
    g = 1 := by
  have hne : ∀ i, L i ≠ ⊥ := fun i h => by
    have := hdim i
    rw [h] at this
    simp at this
  have hinj : Function.Injective L := hint.submodule_iSupIndep.injective hne
  choose σ hσ using hperm
  have hiter : ∀ k : ℕ, ∀ i, (L i).map (Matrix.toLin' ((g ^ k : GL (Fin n) (ZMod p)) :
      Matrix (Fin n) (Fin n) (ZMod p))) = L (σ^[k] i) := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      have : ((g ^ (k + 1) : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) =
          (g : Matrix (Fin n) (Fin n) (ZMod p)) * ((g ^ k : GL (Fin n) (ZMod p)) :
            Matrix (Fin n) (Fin n) (ZMod p)) := by
        rw [pow_succ', Units.val_mul]
      rw [this, Matrix.toLin'_mul, Submodule.map_comp, ih, hσ, Function.iterate_succ_apply']
  have hper : ∀ i, σ^[p] i = i := by
    intro i
    apply hinj
    rw [← hiter p i, hgp]
    simp
  have hσid : ∀ i, σ i = i := by
    refine self_eq_of_iterate_prime (α := Fin n) ?_ σ hper
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hpn
  have hstab : ∀ i, ∀ v ∈ L i, (g : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ v ∈ L i := by
    intro i v hv
    have h1 := hσ i
    rw [hσid i] at h1
    have hmem : (Matrix.toLin' (g : Matrix (Fin n) (Fin n) (ZMod p))) v ∈
        (L i).map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) (ZMod p))) :=
      Submodule.mem_map_of_mem hv
    rw [h1] at hmem
    simpa using hmem
  exact gl_eq_one_of_fixes_iSup_eq_top L hint.submodule_iSup_eq_top
    (fun i v hv => gl_fixes_line (L i) (hdim i) hgp (hstab i) v hv)

theorem card_modEq_card_fixed_perm {X : Type*} [Finite X] {p : ℕ} [Fact p.Prime]
    (e : Equiv.Perm X) (he : e ^ p = 1) :
    Nat.card X ≡ Nat.card {x : X // e x = x} [MOD p] := by
  have hP : IsPGroup p (Subgroup.zpowers e) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, he, _root_.one_zpow]
    rfl
  have h1 := hP.card_modEq_card_fixedPoints X
  have h2 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers e) X) =
      Nat.card {x : X // e x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => ?_)
    constructor
    · intro hh
      exact hh ⟨e, Subgroup.mem_zpowers e⟩
    · intro hh β
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp β.2
      have : ∀ n : ℤ, (e ^ n) h = h := by
        intro n
        induction n using Int.induction_on with
        | zero => simp
        | succ i ih => rw [_root_.zpow_add_one, Equiv.Perm.mul_apply, hh, ih]
        | pred i ih =>
          rw [_root_.zpow_sub_one, Equiv.Perm.mul_apply]
          have : (e⁻¹) h = h := by
            rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
            exact hh.symm
          rw [this, ih]
      show (β : Equiv.Perm X) h = h
      rw [← hk, this]
  rwa [h2] at h1

theorem aut_eq_one_of_card_27 {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 27)
    (hZ : Nat.card (Subgroup.center H) = 3) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (α : MulAut H) (hα : α ^ p = 1) : α = 1 := by
  have hpr : p.Prime := Fact.out
  have hαc : ∀ z, z ∈ Subgroup.center H ↔ α z ∈ Subgroup.center H := by
    have key : ∀ (γ : MulAut H) (z : H), z ∈ Subgroup.center H → γ z ∈ Subgroup.center H := by
      intro γ z hz
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨h, rfl⟩ := γ.surjective g
      rw [← map_mul, ← map_mul, hz h]
    intro z
    refine ⟨key α z, fun hz => ?_⟩
    have := key α⁻¹ _ hz
    simpa using this
  have hpow : (MulAut.toPerm H α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  let e : Equiv.Perm (Subgroup.center H) :=
    Equiv.subtypeEquiv (MulAut.toPerm H α) hαc
  have hiter : ∀ k : ℕ, ∀ z : Subgroup.center H,
      ((e^[k] z : Subgroup.center H) : H) = (MulAut.toPerm H α)^[k] (z : H) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [← ih]
      rfl
  have he : e ^ p = 1 := by
    refine Equiv.ext fun z => ?_
    apply Subtype.ext
    rw [Equiv.Perm.coe_pow, hiter]
    have h2 := congrArg (fun f : Equiv.Perm H => f (z : H)) hpow
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq] using h2
  have hcenter : ∀ z : Subgroup.center H, α z = z := by
    by_contra hcon
    obtain ⟨z0, hz0⟩ := not_forall.mp hcon
    have h1 := card_modEq_card_fixed_perm e he
    have h2 : Nat.card {z : Subgroup.center H // e z = z} < Nat.card (Subgroup.center H) :=
      Finite.card_subtype_lt (x := z0) (by
        intro h
        apply hz0
        have := congrArg Subtype.val h
        exact this)
    have h3 : 1 ≤ Nat.card {z : Subgroup.center H // e z = z} := by
      have : Nonempty {z : Subgroup.center H // e z = z} :=
        ⟨⟨1, Subtype.ext (map_one α)⟩⟩
      exact Nat.card_pos
    rw [hZ] at h1 h2
    have h4 := Nat.ModEq.eq_of_lt_of_lt h1 (by omega) (by omega)
    omega
  let F : Subgroup H := MonoidHom.eqLocus (α : H →* H) (MonoidHom.id H)
  have hFmem : ∀ h, h ∈ F ↔ α h = h := fun h => Iff.rfl
  have hZF : Subgroup.center H ≤ F := fun z hz => (hFmem z).mpr (hcenter ⟨z, hz⟩)
  have h3 : 3 ∣ Nat.card F := hZ ▸ Subgroup.card_dvd_of_le hZF
  have h27 : Nat.card F ∣ 27 := hH ▸ Subgroup.card_subgroup_dvd_card F
  have hcount : Nat.card H ≡ Nat.card F [MOD p] := by
    have h1 := card_modEq_card_fixed_perm (MulAut.toPerm H α) hpow
    have h2 : Nat.card {x : H // (MulAut.toPerm H α) x = x} = Nat.card F :=
      Nat.card_congr (Equiv.subtypeEquivRight fun h => Iff.rfl)
    rwa [h2] at h1
  have hF : Nat.card F = 27 := by
    have hdiv : Nat.card F ∈ Nat.divisors 27 := by simp [h27]
    have : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [this] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    rcases hdiv with h | h | h | h
    · omega
    · exfalso
      rw [hH, h] at hcount
      have := (Nat.modEq_iff_dvd' (by norm_num)).mp hcount.symm
      have hle : p ≤ 24 := Nat.le_of_dvd (by norm_num) this
      interval_cases p <;> first | omega | exact absurd hpr (by norm_num)
    · exfalso
      rw [hH, h] at hcount
      have := (Nat.modEq_iff_dvd' (by norm_num)).mp hcount.symm
      have hle : p ≤ 18 := Nat.le_of_dvd (by norm_num) this
      interval_cases p <;> first | omega | exact absurd hpr (by norm_num)
    · exact h
  have hFtop : F = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hF, hH]
  ext h
  have : h ∈ F := hFtop ▸ Subgroup.mem_top h
  exact (hFmem h).mp this

end CFSG.RankThree.PartOne.KFBloom
