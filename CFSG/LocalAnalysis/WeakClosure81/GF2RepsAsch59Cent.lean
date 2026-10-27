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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch59

open Equiv

lemma filter_pair_eq_pair_of_ne {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}
    (hσ : ∀ x, σ (σ x) = x) {x₀ : Ω} (hx₀ : σ x₀ ≠ x₀) :
    (Finset.univ.filter (fun x => σ x ≠ x)).filter
        (fun x => ({x, σ x} : Finset Ω) = {x₀, σ x₀}) = {x₀, σ x₀} := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨-, hx⟩
    have hxmem : x ∈ ({x₀, σ x₀} : Finset Ω) := by
      rw [← hx]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hxmem
  · intro hx
    constructor
    · rcases hx with rfl | rfl
      · exact hx₀
      · simpa [hσ x₀] using hx₀.symm
    · rcases hx with rfl | rfl
      · rfl
      · rw [hσ x₀]
        exact Finset.pair_comm _ _

theorem exists_hom_perm_five_isPGroup_ker {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h11 : Fintype.card Ω ≤ 11) {σ : Perm Ω} (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x y, σ x = x → σ y = y → x = y) {X : Subgroup (Perm Ω)}
    (hX : X ≤ Subgroup.centralizer {σ}) :
    ∃ φ : ↥X →* Perm (Fin 5), IsPGroup 2 φ.ker := by
  classical
  let N : Finset Ω := Finset.univ.filter (fun x => σ x ≠ x)
  let P : Finset (Finset Ω) := N.image (fun x => ({x, σ x} : Finset Ω))
  have hpair_mem : ∀ {x : Ω}, σ x ≠ x → ({x, σ x} : Finset Ω) ∈ P := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, by simpa [N] using hx, rfl⟩
  have hNcard : N.card = 2 * P.card := by
    have hmaps : (N : Set Ω).MapsTo (fun x => ({x, σ x} : Finset Ω)) (P : Set (Finset Ω)) := by
      intro x hx
      exact hpair_mem (by simpa [N] using hx)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ s ∈ P, (N.filter fun x => ({x, σ x} : Finset Ω) = s).card = 2 := by
      intro s hs
      obtain ⟨x₀, hx₀N, hxs⟩ := Finset.mem_image.mp hs
      have hx₀ : σ x₀ ≠ x₀ := by simpa [N] using hx₀N
      rw [← hxs]
      rw [filter_pair_eq_pair_of_ne hσ hx₀, Finset.card_pair (Ne.symm hx₀)]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hPcard : Fintype.card ↥P ≤ 5 := by
    rw [Fintype.card_coe]
    have hNle : N.card ≤ 11 := (Finset.card_le_univ N).trans h11
    omega
  have hcomm : ∀ g : ↥X, (g : Perm Ω) * σ = σ * (g : Perm Ω) := fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hX g.2)
  have hpair_image : ∀ (g : ↥X) (x : Ω),
      ({x, σ x} : Finset Ω).image (g : Ω → Ω) =
        {((g : Perm Ω) x), σ ((g : Perm Ω) x)} := by
    intro g x
    have hgx : (g : Perm Ω) (σ x) = σ ((g : Perm Ω) x) := by
      simpa only [Equiv.Perm.mul_apply] using
        congrArg (fun p : Perm Ω => p x) (hcomm g)
    simp only [Finset.image_insert, Finset.image_singleton, hgx]
  have hsmul_mem : ∀ (g : ↥X) (s : ↥P), s.1.image (g : Ω → Ω) ∈ P := by
    intro g s
    obtain ⟨x, hxN, hxs⟩ := Finset.mem_image.mp s.2
    rw [← hxs]
    have hx : σ x ≠ x := by simpa [N] using hxN
    have hgx : σ ((g : Perm Ω) x) ≠ (g : Perm Ω) x := by
      intro h
      apply hx
      apply (g : Perm Ω).injective
      have hcommx : (g : Perm Ω) (σ x) = σ ((g : Perm Ω) x) := by
        simpa only [Equiv.Perm.mul_apply] using
          congrArg (fun p : Perm Ω => p x) (hcomm g)
      rw [hcommx]
      exact h
    exact Finset.mem_image.mpr ⟨(g : Perm Ω) x, by simpa [N] using hgx,
      (hpair_image g x).symm⟩
  let smulP : ↥X → ↥P → ↥P :=
    fun g s => ⟨s.1.image (g : Ω → Ω), hsmul_mem g s⟩
  have hsmulP_one : ∀ s : ↥P, smulP 1 s = s := by
    intro s
    apply Subtype.ext
    change (s.1.image ((1 : ↥X) : Ω → Ω)) = s.1
    simp
  have hsmulP_mul : ∀ (g h : ↥X) (s : ↥P), smulP (g * h) s = smulP g (smulP h s) := by
    intro g h s
    apply Subtype.ext
    change (s.1.image ((g * h : ↥X) : Ω → Ω)) =
      ((s.1.image (h : Ω → Ω)).image (g : Ω → Ω))
    simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Finset.image_image]
  let φP : ↥X →* Perm ↥P :=
    { toFun := fun g =>
        { toFun := smulP g
          invFun := smulP g⁻¹
          left_inv := fun s => by
            rw [← hsmulP_mul, inv_mul_cancel, hsmulP_one]
          right_inv := fun s => by
            rw [← hsmulP_mul, mul_inv_cancel, hsmulP_one] }
      map_one' := by
        apply Equiv.ext
        intro s
        simpa using hsmulP_one s
      map_mul' := by
        intro g h
        apply Equiv.ext
        intro s
        change smulP (g * h) s = smulP g (smulP h s)
        exact hsmulP_mul g h s }
  obtain ⟨e⟩ : Nonempty (↥P ↪ Fin 5) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hPcard)
  let ψ : Perm ↥P →* Perm (Fin 5) := Equiv.Perm.viaEmbeddingHom e
  have hψ : Function.Injective ψ := Equiv.Perm.viaEmbeddingHom_injective e
  let φ : ↥X →* Perm (Fin 5) := ψ.comp φP
  have hker_toPerm : ∀ g : ↥X, g ∈ φ.ker → φP g = 1 := by
    intro g hg
    have hψg : ψ (φP g) = 1 := by
      simpa [φ, MonoidHom.mem_ker] using hg
    exact hψ (by simpa using hψg)
  have hker_smul : ∀ g : ↥X, g ∈ φ.ker → ∀ s : ↥P, smulP g s = s := by
    intro g hg s
    have hP1 : φP g = 1 := hker_toPerm g hg
    have h := congrFun (congrArg (fun e : Perm ↥P => (e : ↥P → ↥P)) hP1) s
    simpa [φP] using h
  have hpair_fix : ∀ g : ↥X, g ∈ φ.ker → ∀ x : Ω, σ x ≠ x →
      (g : Perm Ω) x = x ∨ (g : Perm Ω) x = σ x := by
    intro g hg x hx
    let s : ↥P := ⟨({x, σ x} : Finset Ω), hpair_mem hx⟩
    have hval : ({x, σ x} : Finset Ω).image (g : Ω → Ω) = {x, σ x} := by
      have h := congrArg Subtype.val (hker_smul g hg s)
      change (s.1.image (g : Ω → Ω)) = s.1 at h
      simpa [s] using h
    have hmem : (g : Perm Ω) x ∈ ({x, σ x} : Finset Ω) := by
      rw [← hval]
      exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hfix_point : ∀ g : ↥X, g ∈ φ.ker → ∀ x : Ω, σ x = x → (g : Perm Ω) x = x := by
    intro g hg x hx
    have hcommg : (g : Perm Ω) (σ x) = σ ((g : Perm Ω) x) := by
      simpa only [Equiv.Perm.mul_apply] using
        congrArg (fun p : Perm Ω => p x) (hcomm g)
    rw [hx] at hcommg
    exact (hfix x ((g : Perm Ω) x) hx hcommg.symm).symm
  have hsq : ∀ g : ↥X, g ∈ φ.ker → (g : Perm Ω) ^ 2 = 1 := by
    intro g hg
    ext x
    change (g : Perm Ω) ((g : Perm Ω) x) = x
    by_cases hx : σ x = x
    · rw [hfix_point g hg x hx, hfix_point g hg x hx]
    · have hne : σ x ≠ x := hx
      rcases hpair_fix g hg x hne with h | h
      · rw [h]
        exact h
      · have hcommg : (g : Perm Ω) (σ x) = σ ((g : Perm Ω) x) := by
          simpa only [Equiv.Perm.mul_apply] using
            congrArg (fun p : Perm Ω => p x) (hcomm g)
        rw [h, hcommg, h, hσ x]
  refine ⟨φ, ?_⟩
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  apply Subtype.ext
  simpa using hsq (g : ↥X) g.2

end CFSG.LocalAnalysis.WeakClosure81.Asch59
