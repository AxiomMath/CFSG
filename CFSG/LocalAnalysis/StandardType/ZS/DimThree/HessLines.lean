module

public import CFSG.RankThree.SubgroupLists.CliffordPrime
public import CFSG.Foundations.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import CFSG.RankThree.PartOne.N1322.ExtraspecialAbs
import CFSG.RankThree.PartOne.N1322.CaseBasic
import TauCeti.LinearAlgebra.Dimension.DirectSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Algebra.Subalgebra.Rank
import CFSG.RankThree.PartOne.N1322.CoreHyp
import CFSG.RankThree.PartOne.N1322.Mono
import Mathlib

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne CFSG.RepresentationTheory
open CFSG.RankThree.SubgroupLists (translate)
open scoped commutatorElement

theorem exists_pow_three_eq_one_not_mem_center {E : Type*} [Group E] (h27 : Nat.card E = 27)
    (hE : CFSG.IsExtraspecialPGroup 3 E) : ∃ x : E, x ^ 3 = 1 ∧ x ∉ center E := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h27]; norm_num)
  have hclass : commutator E ≤ Subgroup.center E := hE.2.1.le
  let f : E →* Subgroup.center E :=
    { toFun := fun x => ⟨x ^ 3, N1322.ext27_cube h27 hE x⟩
      map_one' := Subtype.ext (one_pow 3)
      map_mul' := fun x y => Subtype.ext (by
        show (x * y) ^ 3 = x ^ 3 * y ^ 3
        rw [CFSG.RankThree.SubgroupLists.mul_pow_eq_class_two hclass x y 3,
          show (∑ i ∈ Finset.range 3, i) = 3 from by decide,
          N1322.ext27_center_cube hE _
            (CFSG.RankThree.SubgroupLists.commutatorElement_mem_center hclass y x), mul_one]) }
  have hcardker : Nat.card f.ker * Nat.card f.range = 27 := by
    rw [Subgroup.card_ker_mul_card_range f, h27]
  have hdvd : Nat.card f.range ∣ 3 := by
    have h1 := Subgroup.card_subgroup_dvd_card f.range
    rwa [hE.2.2.2] at h1
  have hbig : 3 < Nat.card f.ker := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · rw [h1, mul_one] at hcardker; omega
    · rw [h1] at hcardker; omega
  by_contra hcon
  push Not at hcon
  have hker : f.ker ≤ Subgroup.center E := fun x hx => by
    have h1 : ((f x : Subgroup.center E) : E) = 1 :=
      congrArg (fun z : Subgroup.center E => (z : E)) (MonoidHom.mem_ker.mp hx)
    exact hcon x (by simpa [f] using h1)
  have hsmall : Nat.card f.ker ≤ 3 := by
    have hdvd2 : Nat.card f.ker ∣ 3 := by
      rw [← hE.2.2.2]
      exact Subgroup.card_dvd_of_le hker
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd2 with h | h <;> omega
  omega

variable {p : ℕ} [Fact p.Prime]

private lemma cube_eq_one_of_scalar_zl {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hE : CFSG.IsExtraspecialPGroup 3 H) {z : H} (hz : z ∈ Subgroup.center H) {c : ZMod p}
    (hc : ((z : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.scalar (Fin 3) c) : c ^ 3 = 1 := by
  have h1 : (((z : H) : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) ^ 3 = 1 := by
    simpa using congrArg (fun w : H => ((w : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p))) (N1322.ext27_center_cube hE z hz)
  have h2 : (Matrix.scalar (Fin 3) c) ^ 3 = 1 := by
    rw [← hc]
    exact h1
  rw [← map_pow, ← map_one (Matrix.scalar (Fin 3))] at h2
  exact (Matrix.scalar_inj (n := Fin 3)).mp h2

theorem exists_inv_conj_eq_smul_of_extraspecial {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hE : CFSG.IsExtraspecialPGroup 3 H)
    {x y : GL (Fin 3) (ZMod p)} (hx : x ∈ H) (hy : y ∈ H) (hxy : x * y ≠ y * x) :
    ∃ c : ZMod p, c ≠ 1 ∧ c ^ 3 = 1 ∧
      ((y⁻¹ * x * y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        c • (x : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
  have hclass : commutator H ≤ Subgroup.center H := hE.2.1.le
  have hsch := N1322.scalar_commutant_of_noncomm hirr ⟨x, hx, y, hy, hxy⟩
  let z : H := ⁅(⟨y⁻¹, H.inv_mem hy⟩ : H), (⟨x, hx⟩ : H)⁆
  have hzval : (z : GL (Fin 3) (ZMod p)) = y⁻¹ * x * y * x⁻¹ := by
    rw [show (z : GL (Fin 3) (ZMod p)) =
      ((⁅(⟨y⁻¹, H.inv_mem hy⟩ : H), (⟨x, hx⟩ : H)⁆ : H) : GL (Fin 3) (ZMod p)) from rfl]
    simp [commutatorElement_def]
  have hzmem : z ∈ commutator H :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hzcenterH : z ∈ Subgroup.center H := hclass hzmem
  have hcomm : ∀ a ∈ H, a * (z : GL (Fin 3) (ZMod p)) = (z : GL (Fin 3) (ZMod p)) * a := by
    intro a ha
    exact congrArg (fun w : H => (w : GL (Fin 3) (ZMod p)))
      (Subgroup.mem_center_iff.mp hzcenterH (⟨a, ha⟩ : H))
  obtain ⟨c, hc⟩ := hsch ((z : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) (fun g hg => by
    simpa using congrArg (fun w : GL (Fin 3) (ZMod p) =>
      (w : Matrix (Fin 3) (Fin 3) (ZMod p))) (hcomm g hg))
  have hc1 : c ≠ 1 := by
    intro hc1
    have hzval1 : (z : GL (Fin 3) (ZMod p)) = 1 := by
      apply Units.ext
      rw [hc, hc1]
      exact map_one (Matrix.scalar (Fin 3))
    have hw : y⁻¹ * x * y * x⁻¹ = 1 := by
      rw [← hzval]
      exact hzval1
    apply hxy
    calc x * y = y * (y⁻¹ * x * y) := by group
      _ = y * ((y⁻¹ * x * y * x⁻¹) * x) := by group
      _ = y * x := by rw [hw, one_mul]
  have hc3 : c ^ 3 = 1 := cube_eq_one_of_scalar_zl hE hzcenterH hc
  refine ⟨c, hc1, hc3, ?_⟩
  calc ((y⁻¹ * x * y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))
      = ((y⁻¹ * x * y * x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (x : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
        rw [← Units.val_mul]
        congr 1
        group
    _ = ((z : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (x : Matrix (Fin 3) (Fin 3) (ZMod p)) := by rw [← hzval]
    _ = (Matrix.scalar (Fin 3) c) * (x : Matrix (Fin 3) (Fin 3) (ZMod p)) := by rw [hc]
    _ = c • (x : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem translate_eigenspace_le_of_inv_conj_eq_smul {x g : GL (Fin 3) (ZMod p)} {c : ZMod p}
    (hc : ((g⁻¹ * x * g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      c • (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ : ZMod p) :
    translate g (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) μ) ≤
      Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (c * μ) := by
  intro u hu
  obtain ⟨w, hw, rfl⟩ := CFSG.RankThree.SubgroupLists.mem_translate.mp hu
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  rw [Matrix.toLin'_apply] at hw ⊢
  have hxg : (x : Matrix (Fin 3) (Fin 3) (ZMod p)) * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      c • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        (x : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
    have h1 : ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        (((g⁻¹ * x * g : GL (Fin 3) (ZMod p))) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        ((x : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [hc, Matrix.mul_smul] at h1
    exact h1.symm
  calc (x : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec
        ((g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w)
      = ((x : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (g : Matrix (Fin 3) (Fin 3) (ZMod p))).mulVec w :=
        (Matrix.mulVec_mulVec w _ _)
    _ = (c • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (x : Matrix (Fin 3) (Fin 3) (ZMod p)))).mulVec w := by rw [hxg]
    _ = c • (((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (x : Matrix (Fin 3) (Fin 3) (ZMod p))).mulVec w) := Matrix.smul_mulVec c _ _
    _ = c • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec
          ((x : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w)) := by
        rw [Matrix.mulVec_mulVec w]
    _ = c • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec (μ • w)) := by rw [hw]
    _ = c • (μ • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w)) := by
        rw [Matrix.mulVec_smul]
    _ = (c * μ) • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w) := by rw [smul_smul]

private lemma end_factor_zl {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {c : K} (hT3 : T ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hsum : (1 : K) + c + c ^ 2 = 0) :
    (T - 1) * (T - c • 1) * (T - c ^ 2 • 1) = 0 := by
  have hquad : ∀ a b : K, (T - algebraMap K (Module.End K V) a) *
      (T - algebraMap K (Module.End K V) b) =
      T ^ 2 - algebraMap K (Module.End K V) (a + b) * T +
        algebraMap K (Module.End K V) (a * b) := by
    intro a b
    calc (T - algebraMap K (Module.End K V) a) * (T - algebraMap K (Module.End K V) b)
        = T * T - T * algebraMap K (Module.End K V) b -
            algebraMap K (Module.End K V) a * T +
            algebraMap K (Module.End K V) a * algebraMap K (Module.End K V) b := by
          noncomm_ring
      _ = T * T - algebraMap K (Module.End K V) b * T -
            algebraMap K (Module.End K V) a * T +
            algebraMap K (Module.End K V) a * algebraMap K (Module.End K V) b := by
          rw [(Algebra.commute_algebraMap_right b T).eq]
      _ = T ^ 2 - algebraMap K (Module.End K V) (a + b) * T +
            algebraMap K (Module.End K V) (a * b) := by
          rw [map_add, map_mul, add_mul, pow_two]
          noncomm_ring
  have hc2 : c + c ^ 2 = -1 := by linear_combination hsum
  have hc3' : c * c ^ 2 = 1 := by rw [show c * c ^ 2 = c ^ 3 by ring, hc3]
  calc (T - 1) * (T - c • 1) * (T - c ^ 2 • 1)
      = (T - 1) * ((T - c • 1) * (T - c ^ 2 • 1)) := by rw [mul_assoc]
    _ = (T - 1) * (T ^ 2 + T + 1) := by
        rw [← Algebra.algebraMap_eq_smul_one c, ← Algebra.algebraMap_eq_smul_one (c ^ 2),
          hquad c (c ^ 2), hc2, hc3', map_neg, map_one]
        noncomm_ring
    _ = T ^ 3 - 1 := by noncomm_ring
    _ = 0 := by rw [hT3, sub_self]

private lemma exists_eigenvalue_zl {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] (T : Module.End K V) {c : K} (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hT3 : T ^ 3 = 1) :
    T.eigenspace 1 ≠ ⊥ ∨ T.eigenspace c ≠ ⊥ ∨ T.eigenspace (c ^ 2) ≠ ⊥ := by
  have hsum : (1 : K) + c + c ^ 2 = 0 := by
    have h : (c - 1) * (1 + c + c ^ 2) = c ^ 3 - 1 := by ring
    rw [hc3, sub_self] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') hc1
    · exact h'
  have hfac := end_factor_zl T hT3 hc3 hsum
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  let w2 : V := (T - c ^ 2 • 1) v
  let w1 : V := (T - c • 1) w2
  have hw0 : (T - 1) w1 = 0 := by
    have h := congrArg (fun f : Module.End K V => f v) hfac
    simpa [w1, w2, mul_assoc] using h
  by_cases h2 : w2 = 0
  · right; right
    refine (Submodule.ne_bot_iff _).2 ⟨v, ?_, hv⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [w2] using sub_eq_zero.mp h2
  · by_cases h1 : w1 = 0
    · right; left
      refine (Submodule.ne_bot_iff _).2 ⟨w2, ?_, h2⟩
      rw [Module.End.mem_eigenspace_iff]
      simpa [w1] using sub_eq_zero.mp h1
    · left
      refine (Submodule.ne_bot_iff _).2 ⟨w1, ?_, h1⟩
      rw [Module.End.mem_eigenspace_iff]
      simpa using sub_eq_zero.mp hw0

private lemma exists_eigen_l_zl {T : Module.End (ZMod p) (Fin 3 → ZMod p)} {c : ZMod p}
    (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) (hT3 : T ^ 3 = 1) :
    ∃ l : ZMod p, (l = 1 ∨ l = c ∨ l = c ^ 2) ∧ T.eigenspace l ≠ ⊥ := by
  rcases exists_eigenvalue_zl T hc1 hc3 hT3 with h | h | h
  · exact ⟨1, Or.inl rfl, h⟩
  · exact ⟨c, Or.inr (Or.inl rfl), h⟩
  · exact ⟨c ^ 2, Or.inr (Or.inr rfl), h⟩

private lemma eigenspace_finrank_eq_zl {x y : GL (Fin 3) (ZMod p)} {c l : ZMod p}
    (T : Module.End (ZMod p) (Fin 3 → ZMod p))
    (hT : T = Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p)))
    (hyx : ((y⁻¹ * x * y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      c • (x : Matrix (Fin 3) (Fin 3) (ZMod p)))
    (hc3 : c ^ 3 = 1) (_hlne : T.eigenspace l ≠ ⊥) :
    Module.finrank (ZMod p) (T.eigenspace l) =
        Module.finrank (ZMod p) (T.eigenspace (c * l)) ∧
      Module.finrank (ZMod p) (T.eigenspace (c * l)) =
        Module.finrank (ZMod p) (T.eigenspace (c ^ 2 * l)) := by
  have hstep : ∀ μ, translate y (T.eigenspace μ) ≤ T.eigenspace (c * μ) := by
    intro μ
    simpa [hT] using translate_eigenspace_le_of_inv_conj_eq_smul (x := x) (g := y) hyx μ
  have hle : ∀ μ, Module.finrank (ZMod p) (T.eigenspace μ) ≤
      Module.finrank (ZMod p) (T.eigenspace (c * μ)) := by
    intro μ
    calc Module.finrank (ZMod p) (T.eigenspace μ)
        = Module.finrank (ZMod p) (translate y (T.eigenspace μ)) :=
          (CFSG.RankThree.SubgroupLists.finrank_translate y (T.eigenspace μ)).symm
      _ ≤ Module.finrank (ZMod p) (T.eigenspace (c * μ)) := Submodule.finrank_mono (hstep μ)
  have h0 : Module.finrank (ZMod p) (T.eigenspace l) ≤
      Module.finrank (ZMod p) (T.eigenspace (c * l)) := hle l
  have h1 : Module.finrank (ZMod p) (T.eigenspace (c * l)) ≤
      Module.finrank (ZMod p) (T.eigenspace (c ^ 2 * l)) := by
    have h := hle (c * l)
    rwa [show c * (c * l) = c ^ 2 * l by ring] at h
  have h2 : Module.finrank (ZMod p) (T.eigenspace (c ^ 2 * l)) ≤
      Module.finrank (ZMod p) (T.eigenspace l) := by
    have h := hle (c ^ 2 * l)
    rwa [show c * (c ^ 2 * l) = l by
      rw [show c * (c ^ 2 * l) = c ^ 3 * l by ring, hc3, one_mul]] at h
  exact ⟨le_antisymm h0 (le_trans h1 h2), le_antisymm h1 (le_trans h2 h0)⟩

private lemma eigenvalue_injective_zl {c l : ZMod p} (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hl : l ≠ 0) : Function.Injective (fun i : Fin 3 => c ^ (i : ℕ) * l) := by
  have hord : orderOf c = 3 := by
    have hdvd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have hne1 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  intro i j hij
  exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hord]; exact i.isLt)
    (by rw [hord]; exact j.isLt) (mul_right_cancel₀ hl hij))

private lemma eigenlines_isInternal_zl {T : Module.End (ZMod p) (Fin 3 → ZMod p)} {c l : ZMod p}
    (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) (hl : l ≠ 0)
    (hk0 : Module.finrank (ZMod p) (T.eigenspace l) =
      Module.finrank (ZMod p) (T.eigenspace (c * l)))
    (hk1 : Module.finrank (ZMod p) (T.eigenspace (c * l)) =
      Module.finrank (ZMod p) (T.eigenspace (c ^ 2 * l)))
    (hpos : 0 < Module.finrank (ZMod p) (T.eigenspace l)) :
    (∀ i : Fin 3, Module.finrank (ZMod p) (T.eigenspace (c ^ (i : ℕ) * l)) = 1) ∧
      DirectSum.IsInternal (fun i : Fin 3 => T.eigenspace (c ^ (i : ℕ) * l)) := by
  have hk2 : Module.finrank (ZMod p) (T.eigenspace (c ^ 2 * l)) =
      Module.finrank (ZMod p) (T.eigenspace l) := hk1.symm.trans hk0.symm
  have hinj : Function.Injective (fun i : Fin 3 => c ^ (i : ℕ) * l) :=
    eigenvalue_injective_zl hc1 hc3 hl
  have hind : iSupIndep (fun i : Fin 3 => T.eigenspace (c ^ (i : ℕ) * l)) :=
    (Module.End.eigenspaces_iSupIndep T).comp hinj
  have hsum3 : Module.finrank (ZMod p) ↥(⨆ i : Fin 3, T.eigenspace (c ^ (i : ℕ) * l)) =
      Module.finrank (ZMod p) (T.eigenspace l) + Module.finrank (ZMod p) (T.eigenspace l) +
        Module.finrank (ZMod p) (T.eigenspace l) := by
    rw [TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hind, Fin.sum_univ_three]
    have e0 : c ^ ((0 : Fin 3) : ℕ) * l = l := by norm_num
    have e1 : c ^ ((1 : Fin 3) : ℕ) * l = c * l := by norm_num
    have e2 : c ^ ((2 : Fin 3) : ℕ) * l = c ^ 2 * l := by norm_num
    rw [e0, e1, e2, hk2, ← hk0]
  have htop : Module.finrank (ZMod p) ↥(⨆ i : Fin 3, T.eigenspace (c ^ (i : ℕ) * l)) ≤ 3 := by
    have h := Submodule.finrank_le (⨆ i : Fin 3, T.eigenspace (c ^ (i : ℕ) * l))
    rw [Module.finrank_fin_fun] at h
    exact h
  have hk : Module.finrank (ZMod p) (T.eigenspace l) = 1 := by
    have h := htop
    rw [hsum3] at h
    omega
  have hfin : ∀ i : Fin 3, Module.finrank (ZMod p) (T.eigenspace (c ^ (i : ℕ) * l)) = 1 := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with h | h | h
    · rw [h, show c ^ ((0 : Fin 3) : ℕ) * l = l by norm_num]
      exact hk
    · rw [h, show c ^ ((1 : Fin 3) : ℕ) * l = c * l by norm_num]
      exact hk0.symm.trans hk
    · rw [h, show c ^ ((2 : Fin 3) : ℕ) * l = c ^ 2 * l by norm_num]
      exact hk2.trans hk
  refine ⟨hfin, ?_⟩
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨hind, ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  rw [hsum3, hk, Module.finrank_fin_fun]

theorem exists_eigenlines_of_inv_conj_eq_smul {x y : GL (Fin 3) (ZMod p)} {c : ZMod p}
    (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) (hx3 : x ^ 3 = 1)
    (hyx : ((y⁻¹ * x * y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      c • (x : Matrix (Fin 3) (Fin 3) (ZMod p))) :
    ∃ l : ZMod p,
      (∀ i : Fin 3, Module.finrank (ZMod p) (Module.End.eigenspace
        (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (c ^ (i : ℕ) * l)) = 1) ∧
      DirectSum.IsInternal (fun i : Fin 3 => Module.End.eigenspace
        (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (c ^ (i : ℕ) * l)) := by
  let T : Module.End (ZMod p) (Fin 3 → ZMod p) :=
    Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))
  have hx3' : (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) ^ 3 = 1 := by
    have hmat3 : ((x : Matrix (Fin 3) (Fin 3) (ZMod p))) ^ 3 = 1 := by
      simpa using congrArg (fun w : GL (Fin 3) (ZMod p) =>
        (w : Matrix (Fin 3) (Fin 3) (ZMod p))) hx3
    rw [← Matrix.toLin'_pow, hmat3, Matrix.toLin'_one]
    exact Module.End.one_eq_id.symm
  obtain ⟨l, hlcase, hlne⟩ := exists_eigen_l_zl hc1 hc3 hx3'
  have hl3 : l ^ 3 = 1 := by
    rcases hlcase with rfl | rfl | rfl
    · norm_num
    · exact hc3
    · rw [show (c ^ 2) ^ 3 = (c ^ 3) ^ 2 by ring, hc3]; norm_num
  have hl : l ≠ 0 := by
    intro h; rw [h] at hl3; norm_num at hl3
  obtain ⟨hk0, hk1⟩ := eigenspace_finrank_eq_zl T rfl hyx hc3 hlne
  have hpos : 0 < Module.finrank (ZMod p) (T.eigenspace l) := by
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    exact hlne ((Submodule.finrank_eq_zero (R := ZMod p)).mp hzero)
  have hres := eigenlines_isInternal_zl hc1 hc3 hl hk0 hk1 hpos
  exact ⟨l, hres.1, hres.2⟩

end CFSG.StandardType.ZS.DimThree
