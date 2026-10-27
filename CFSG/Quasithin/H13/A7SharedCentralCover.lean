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
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.Quasithin.H13.A7

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem A7_perfect_central_cover_kernel_has_normal_Sylow_two {A : Type*} [Group A] [Finite X]
    {L : Subgroup X} [hLn : L.Normal] (hLperf : ⁅L, L⁆ = L) {k : ℕ} (hLidx : L.index = 2 ^ k)
    (ρ : X →* A) {R : Subgroup X} (hRLN : R ≤ L ⊓ ρ.ker) (hR : IsPGroup 2 R) [hRn : R.Normal]
    (hcent : ∀ x ∈ L ⊓ ρ.ker, ∀ l ∈ L, ⁅x, l⁆ ∈ R) :
    ⁅L, ρ.ker⁆ ≤ R ∧
      ∃ Q : Subgroup X, Q ≤ ρ.ker ∧ IsPGroup 2 Q ∧ ¬ 2 ∣ Q.relIndex ρ.ker ∧
        (∀ Q' : Subgroup X, Q' ≤ ρ.ker → IsPGroup 2 Q' → Q' ≤ Q) ∧ Q.Normal ∧
        (∀ T : Sylow 2 X, Q = (T : Subgroup X) ⊓ ρ.ker) ∧
        ∀ (T : Sylow 2 X) (V : Subgroup X), V.Normal → IsMulCommutative V →
          V ≤ (T : Subgroup X) → ρ.ker = centralizer (V : Set X) →
          Q = (T : Subgroup X) ⊓ centralizer (V : Set X) ∧ V ≤ Q ∧
            ((T : Subgroup X) ⊓ centralizer (V : Set X)).Normal := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := ρ.ker with hNdef
  have hRL : R ≤ L := fun r hr => (hRLN hr).1
  have hRN : R ≤ N := fun r hr => (hRLN hr).2
  have hLN : ∀ l ∈ L, ∀ n ∈ N, ⁅l, n⁆ ∈ L ⊓ N := by
    intro l hl n hn
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def, show l * n * l⁻¹ * n⁻¹ = l * (n * l⁻¹ * n⁻¹) by group]
      exact L.mul_mem hl (hLn.conj_mem _ (L.inv_mem hl) n)
    · rw [commutatorElement_def]
      exact N.mul_mem ((inferInstance : N.Normal).conj_mem n hn l) (N.inv_mem hn)
  have hcomm : ∀ x ∈ L ⊓ N, ∀ l ∈ L, (QuotientGroup.mk x : X ⧸ R) * QuotientGroup.mk l =
      QuotientGroup.mk l * QuotientGroup.mk x := by
    intro x hx l hl
    have h1 : (QuotientGroup.mk ⁅x, l⁆ : X ⧸ R) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcent x hx l hl)
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
    calc (QuotientGroup.mk x : X ⧸ R) * QuotientGroup.mk l
        = (QuotientGroup.mk x * QuotientGroup.mk l * (QuotientGroup.mk x)⁻¹ *
            (QuotientGroup.mk l)⁻¹) * (QuotientGroup.mk l * QuotientGroup.mk x) := by group
      _ = _ := by rw [h1, one_mul]
  have hLNR : ⁅L, N⁆ ≤ R := by
    rw [commutator_le]
    intro l hl n hn
    let F : L →* X ⧸ R :=
      { toFun := fun m => QuotientGroup.mk ⁅(m : X), n⁆
        map_one' := by simp
        map_mul' := fun a b => by
          have e : ⁅((a * b : L) : X), n⁆ = (a : X) * ⁅(b : X), n⁆ * (a : X)⁻¹ * ⁅(a : X), n⁆ := by
            simp only [Subgroup.coe_mul, commutatorElement_def]
            group
          rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            QuotientGroup.mk_inv]
          have h1 := hcomm _ (hLN b b.2 n hn) a a.2
          have h2 := hcomm _ (hLN b b.2 n hn) _ (hLN a a.2 n hn).1
          calc (QuotientGroup.mk (a : X) : X ⧸ R) * QuotientGroup.mk ⁅(b : X), n⁆ *
                (QuotientGroup.mk (a : X))⁻¹ * QuotientGroup.mk ⁅(a : X), n⁆
              = QuotientGroup.mk ⁅(b : X), n⁆ * QuotientGroup.mk (a : X) *
                (QuotientGroup.mk (a : X))⁻¹ * QuotientGroup.mk ⁅(a : X), n⁆ := by rw [← h1]
            _ = QuotientGroup.mk ⁅(b : X), n⁆ * QuotientGroup.mk ⁅(a : X), n⁆ := by group
            _ = QuotientGroup.mk ⁅(a : X), n⁆ * QuotientGroup.mk ⁅(b : X), n⁆ := h2 }
    have hker : L ≤ F.ker.map L.subtype := by
      conv_lhs => rw [← hLperf]
      rw [commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, ha⟩ : L), ⟨b, hb⟩⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ (hLN a ha n hn) _ (hLN b hb n hn).1
    obtain ⟨m, hm, hml⟩ := hker hl
    have : F m = 1 := hm
    rw [← hml]
    exact (QuotientGroup.eq_one_iff _).1 this
  refine ⟨hLNR, ?_⟩
  have hRNn : (R.subgroupOf N).Normal := Subgroup.normal_subgroupOf
  let ψ : N ⧸ R.subgroupOf N →* X ⧸ L :=
    QuotientGroup.lift (R.subgroupOf N) ((QuotientGroup.mk' L).comp N.subtype) (by
      intro r hr
      rw [mem_subgroupOf] at hr
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hRL hr)
  have hψker : ψ.ker ≤ center (N ⧸ R.subgroupOf N) := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hxL : (x : X) ∈ L := by
      have : ψ (QuotientGroup.mk x) = 1 := hg
      rw [QuotientGroup.lift_mk, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
      exact this
    rw [mem_center_iff]
    intro h
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective h
    have h1 : ⁅(x : X), (y : X)⁆ ∈ R := hLNR (commutator_mem_commutator hxL y.2)
    have h2 : (QuotientGroup.mk ⁅x, y⁆ : N ⧸ R.subgroupOf N) = 1 := by
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact h1
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h2
    calc (QuotientGroup.mk y : N ⧸ R.subgroupOf N) * QuotientGroup.mk x
        = (QuotientGroup.mk x * QuotientGroup.mk y * (QuotientGroup.mk x)⁻¹ *
            (QuotientGroup.mk y)⁻¹)⁻¹ * (QuotientGroup.mk x * QuotientGroup.mk y) := by group
      _ = _ := by rw [h2, inv_one, one_mul]
  have hXL : IsPGroup 2 (X ⧸ L) := IsPGroup.of_card (by rw [← Subgroup.index_eq_card, hLidx])
  have : Group.IsNilpotent (X ⧸ L) := hXL.isNilpotent
  have hnil : Group.IsNilpotent (N ⧸ R.subgroupOf N) :=
    Subgroup.isNilpotent_of_ker_le_center ψ hψker
  obtain ⟨P'⟩ : Nonempty (Sylow 2 (N ⧸ R.subgroupOf N)) := inferInstance
  have hP'n : (P' : Subgroup (N ⧸ R.subgroupOf N)).Normal := inferInstance
  set Q₀ : Subgroup N := (P' : Subgroup (N ⧸ R.subgroupOf N)).comap (QuotientGroup.mk' _)
    with hQ₀def
  set Q : Subgroup X := Q₀.map N.subtype with hQdef
  have hQN : Q ≤ N := Subgroup.map_subtype_le _
  have hQ₀ : Q.subgroupOf N = Q₀ := by
    rw [hQdef, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨_, x, hx, rfl⟩
    obtain ⟨a, ha⟩ := P'.isPGroup' ⟨QuotientGroup.mk' _ x, hx⟩
    have h1 : (QuotientGroup.mk' (R.subgroupOf N) x) ^ 2 ^ a = 1 := congrArg Subtype.val ha
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    obtain ⟨b, hb⟩ := hR ⟨_, h1⟩
    have h2 : ((x : X) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    refine ⟨a + b, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_subtype]
    rw [pow_add, pow_mul, h2]
  have hQidx : ¬ 2 ∣ Q.relIndex N := by
    rw [Subgroup.relIndex, hQ₀, hQ₀def, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective _)]
    exact P'.not_dvd_index
  have hQmax : ∀ Q' : Subgroup X, Q' ≤ N → IsPGroup 2 Q' → Q' ≤ Q := by
    intro Q' hQ'N hQ'2
    have hp : IsPGroup 2 ((Q'.subgroupOf N).map (QuotientGroup.mk' (R.subgroupOf N))) := by
      refine IsPGroup.map ?_ _
      exact IsPGroup.of_equiv hQ'2 (Subgroup.subgroupOfEquivOfLe hQ'N).symm
    obtain ⟨S', hS'⟩ := hp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (N ⧸ R.subgroupOf N) P' S'
    rw [← hg, Sylow.smul_eq_of_normal] at hS'
    intro q hq
    refine ⟨⟨q, hQ'N hq⟩, ?_, rfl⟩
    exact hS' ⟨⟨q, hQ'N hq⟩, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hq, rfl⟩
  have hQn : Q.Normal := by
    refine ⟨fun q hq x => ?_⟩
    have h1 : Q.map (MulAut.conj x).toMonoidHom ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact (inferInstance : N.Normal).conj_mem y (hQN hy) x
    exact hQmax _ h1 (hQ2.map _) ⟨q, hq, rfl⟩
  have hQT : ∀ T : Sylow 2 X, Q = (T : Subgroup X) ⊓ N := by
    intro T
    exact le_antisymm (le_inf (hQ2.le_sylow_of_normal T) hQN)
      (hQmax _ inf_le_right (T.isPGroup'.to_le inf_le_left))
  refine ⟨Q, hQN, hQ2, hQidx, hQmax, hQn, hQT, fun T V _ hVc hVT hNV => ?_⟩
  have hQV : Q = (T : Subgroup X) ⊓ centralizer (V : Set X) := by rw [hQT T, hNV]
  refine ⟨hQV, ?_, hQV ▸ hQn⟩
  intro v hv
  rw [hQV]
  refine ⟨hVT hv, mem_centralizer_iff.2 fun w hw => ?_⟩
  exact congrArg Subtype.val (hVc.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

end CFSG.Quasithin.H13.A7
