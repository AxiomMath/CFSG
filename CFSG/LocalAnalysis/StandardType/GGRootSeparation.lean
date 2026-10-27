module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
import CFSG.LocalAnalysis.StandardType.GGRootSeparationPendant
import CFSG.LieType.Universal.Spin.Roots.TypeD
import CFSG.LieType.Steinberg.Minuscule.Form
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Field.ZMod
import CFSG.Mathlib.LinearAlgebra.PairFunctional
import CFSG.LinearAlgebra.OuterActorCorrection
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.LieType.RootSystem

section Tags

private theorem cartanA_mk_zero {l : ℕ} {a b : ℕ} (ha : a < l) (hb : b < l)
    (hne : a ≠ b) (h1 : a + 1 ≠ b) (h2 : b + 1 ≠ a) :
    CartanMatrix.A l ⟨a, ha⟩ ⟨b, hb⟩ = 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  simp [hne, h1, h2]

private theorem cartanA_mk_neg_one_of_left {l : ℕ} {a b : ℕ} (ha : a < l) (hb : b < l)
    (h : a + 1 = b) : CartanMatrix.A l ⟨a, ha⟩ ⟨b, hb⟩ = -1 := by
  have hne : a ≠ b := by omega
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  simp [hne, h]

private theorem cartanA_mk_neg_one_of_right {l : ℕ} {a b : ℕ} (ha : a < l) (hb : b < l)
    (h : b + 1 = a) : CartanMatrix.A l ⟨a, ha⟩ ⟨b, hb⟩ = -1 := by
  have hne : a ≠ b := by omega
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  simp [hne, h]

private theorem pendant_A {l : ℕ} (hl : 3 ≤ l) (i j : Fin l) (hij : CartanMatrix.A l i j = -1) :
    ∃ m, (CartanMatrix.A l m i = -1 ∧ CartanMatrix.A l m j = 0) ∨
      (CartanMatrix.A l m i = 0 ∧ CartanMatrix.A l m j = -1) := by
  have hne : i ≠ j := by
    rintro rfl
    simp [CartanMatrix.A] at hij
  have hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
    by_contra h
    have hval : i.val ≠ j.val := fun hv => hne (Fin.ext hv)
    have h0 : CartanMatrix.A l i j = 0 := by
      simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
      simp [hval, h]
    rw [h0] at hij
    norm_num at hij
  have key : ∀ {i j : Fin l}, i.val + 1 = j.val →
      ∃ m, (CartanMatrix.A l m i = -1 ∧ CartanMatrix.A l m j = 0) ∨
        (CartanMatrix.A l m i = 0 ∧ CartanMatrix.A l m j = -1) := by
    intro i j h
    by_cases hlt : i.val + 2 < l
    · refine ⟨⟨i.val + 2, hlt⟩, Or.inr ⟨?_, ?_⟩⟩
      · exact cartanA_mk_zero (l := l) (a := i.val + 2) (b := i.val) hlt i.isLt
          (by omega) (by omega) (by omega)
      · exact cartanA_mk_neg_one_of_right (l := l) (a := i.val + 2) (b := j.val)
          hlt j.isLt (by omega)
    · have hi : 1 ≤ i.val := by omega
      refine ⟨⟨i.val - 1, by omega⟩, Or.inl ⟨?_, ?_⟩⟩
      · exact cartanA_mk_neg_one_of_left (l := l) (a := i.val - 1) (b := i.val)
          (by omega) i.isLt (by omega)
      · exact cartanA_mk_zero (l := l) (a := i.val - 1) (b := j.val)
          (by omega) j.isLt (by omega) (by omega) (by omega)
  rcases hadj with h | h
  · exact key h
  · rcases key (i := j) (j := i) h with ⟨m, hm | hm⟩
    · exact ⟨m, Or.inr ⟨hm.2, hm.1⟩⟩
    · exact ⟨m, Or.inl ⟨hm.2, hm.1⟩⟩

private theorem cartanD_mk_zero {l : ℕ} {a b : ℕ} (ha : a < l) (hb : b < l)
    (hne : a ≠ b) (h1 : ¬ (a + 1 = b ∧ b + 1 < l))
    (h2 : ¬ (b + 1 = a ∧ a + 1 < l)) (h3 : ¬ (a + 3 = l ∧ b + 1 = l))
    (h4 : ¬ (b + 3 = l ∧ a + 1 = l)) :
    Spin.cartanD l ⟨a, ha⟩ ⟨b, hb⟩ = 0 := by
  simp only [Spin.cartanD, Matrix.of_apply, Fin.ext_iff]
  simp [hne, h1, h2, h3, h4]

private theorem cartanD_mk_neg_one_of_chain_left {l : ℕ} {a b : ℕ} (ha : a < l) (hb : b < l)
    (h : a + 1 = b ∧ b + 1 < l) : Spin.cartanD l ⟨a, ha⟩ ⟨b, hb⟩ = -1 := by
  have hne : a ≠ b := by omega
  simp only [Spin.cartanD, Matrix.of_apply, Fin.ext_iff]
  simp [hne, h.1, h.2]

private theorem cartanD_mk_neg_one_of_chain_right {l : ℕ} {a b : ℕ} (ha : a < l) (hb : b < l)
    (h : b + 1 = a ∧ a + 1 < l) : Spin.cartanD l ⟨a, ha⟩ ⟨b, hb⟩ = -1 := by
  have hne : a ≠ b := by omega
  simp only [Spin.cartanD, Matrix.of_apply, Fin.ext_iff]
  simp [hne, h.1, h.2]

private theorem cartanD_mk_neg_one_of_fork_right {l : ℕ} {a b : ℕ} (ha : a < l) (hb : b < l)
    (h : b + 3 = l ∧ a + 1 = l) : Spin.cartanD l ⟨a, ha⟩ ⟨b, hb⟩ = -1 := by
  have hne : a ≠ b := by omega
  simp only [Spin.cartanD, Matrix.of_apply, Fin.ext_iff]
  simp [hne, h.1, h.2]

private theorem pendant_D {l : ℕ} (hl : 3 ≤ l) (i j : Fin l)
    (hij : Spin.cartanD l i j = -1) :
    ∃ m, (Spin.cartanD l m i = -1 ∧ Spin.cartanD l m j = 0) ∨
      (Spin.cartanD l m i = 0 ∧ Spin.cartanD l m j = -1) := by
  have hedge :
      (i.val + 1 = j.val ∧ j.val + 1 < l) ∨
        (j.val + 1 = i.val ∧ i.val + 1 < l) ∨
        (i.val + 3 = l ∧ j.val + 1 = l) ∨
        (j.val + 3 = l ∧ i.val + 1 = l) := by
    by_contra h
    have hne : i ≠ j := by
      rintro rfl
      simp [Spin.cartanD] at hij
    have hval : i.val ≠ j.val := fun hv => hne (Fin.ext hv)
    have h0 : Spin.cartanD l i j = 0 := by
      simp only [Spin.cartanD, Matrix.of_apply, Fin.ext_iff]
      have h' : ¬ ((i.val + 1 = j.val ∧ j.val + 1 < l) ∨
          (j.val + 1 = i.val ∧ i.val + 1 < l) ∨
          (i.val + 3 = l ∧ j.val + 1 = l) ∨
          (j.val + 3 = l ∧ i.val + 1 = l)) := h
      simp [hval, h']
    rw [h0] at hij
    norm_num at hij
  have chain : ∀ {i j : Fin l}, i.val + 1 = j.val → j.val + 1 < l →
      ∃ m, (Spin.cartanD l m i = -1 ∧ Spin.cartanD l m j = 0) ∨
        (Spin.cartanD l m i = 0 ∧ Spin.cartanD l m j = -1) := by
    intro i j h hj
    by_cases hi : 1 ≤ i.val
    · refine ⟨⟨i.val - 1, by omega⟩, Or.inl ⟨?_, ?_⟩⟩
      · exact cartanD_mk_neg_one_of_chain_left (l := l) (a := i.val - 1) (b := i.val)
          (by omega) i.isLt ⟨by omega, by omega⟩
      · exact cartanD_mk_zero (l := l) (a := i.val - 1) (b := j.val)
          (by omega) j.isLt (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hi0 : i.val = 0 := by omega
      by_cases hl3 : l = 3
      · subst l
        refine ⟨⟨2, by omega⟩, Or.inl ⟨?_, ?_⟩⟩
        · exact cartanD_mk_neg_one_of_fork_right (l := 3) (a := 2) (b := i.val)
            (by omega) i.isLt ⟨by omega, by omega⟩
        · exact cartanD_mk_zero (l := 3) (a := 2) (b := j.val)
            (by omega) j.isLt (by omega) (by omega) (by omega) (by omega) (by omega)
      · have hl4 : 4 ≤ l := by omega
        refine ⟨⟨2, by omega⟩, Or.inr ⟨?_, ?_⟩⟩
        · exact cartanD_mk_zero (l := l) (a := 2) (b := i.val)
            (by omega) i.isLt (by omega) (by omega) (by omega) (by omega) (by omega)
        · exact cartanD_mk_neg_one_of_chain_right (l := l) (a := 2) (b := j.val)
            (by omega) j.isLt ⟨by omega, by omega⟩
  have fork : ∀ {i j : Fin l}, i.val + 3 = l → j.val + 1 = l →
      ∃ m, (Spin.cartanD l m i = -1 ∧ Spin.cartanD l m j = 0) ∨
        (Spin.cartanD l m i = 0 ∧ Spin.cartanD l m j = -1) := by
    intro i j h hj
    refine ⟨⟨i.val + 1, by omega⟩, Or.inl ⟨?_, ?_⟩⟩
    · exact cartanD_mk_neg_one_of_chain_right (l := l) (a := i.val + 1) (b := i.val)
        (by omega) i.isLt ⟨by omega, by omega⟩
    · exact cartanD_mk_zero (l := l) (a := i.val + 1) (b := j.val)
        (by omega) j.isLt (by omega) (by omega) (by omega) (by omega) (by omega)
  rcases hedge with h | h | h | h
  · exact chain h.1 h.2
  · rcases chain (i := j) (j := i) h.1 h.2 with ⟨m, hm | hm⟩
    · exact ⟨m, Or.inr ⟨hm.2, hm.1⟩⟩
    · exact ⟨m, Or.inl ⟨hm.2, hm.1⟩⟩
  · exact fork h.1 h.2
  · rcases fork (i := j) (j := i) h.1 h.2 with ⟨m, hm | hm⟩
    · exact ⟨m, Or.inr ⟨hm.2, hm.1⟩⟩
    · exact ⟨m, Or.inl ⟨hm.2, hm.1⟩⟩

private theorem cartanD_isSymm (l : ℕ) : (Spin.cartanD l).IsSymm := by
  rw [Spin.cartanD_eq]
  exact CartanMatrix.D_isSymm l

private theorem pendant_E6 (i j : Fin 6) (hij : CFSG.Blueprint.Chevalley.Tag.cartan .E6 i j = -1) :
    ∃ m, (CFSG.Blueprint.Chevalley.Tag.cartan .E6 m i = -1 ∧
        CFSG.Blueprint.Chevalley.Tag.cartan .E6 m j = 0) ∨
      (CFSG.Blueprint.Chevalley.Tag.cartan .E6 m i = 0 ∧
        CFSG.Blueprint.Chevalley.Tag.cartan .E6 m j = -1) := by
  have h : CFSG.Blueprint.Chevalley.Tag.cartan .E6 =
      CFSG.Blueprint.Chevalley.Tag.cartanE 6 := rfl
  rw [h] at hij ⊢
  revert hij
  fin_cases i <;> fin_cases j <;> decide

private theorem pendant_E7 (i j : Fin 7) (hij : CFSG.Blueprint.Chevalley.Tag.cartan .E7 i j = -1) :
    ∃ m, (CFSG.Blueprint.Chevalley.Tag.cartan .E7 m i = -1 ∧
        CFSG.Blueprint.Chevalley.Tag.cartan .E7 m j = 0) ∨
      (CFSG.Blueprint.Chevalley.Tag.cartan .E7 m i = 0 ∧
        CFSG.Blueprint.Chevalley.Tag.cartan .E7 m j = -1) := by
  have h : CFSG.Blueprint.Chevalley.Tag.cartan .E7 =
      CFSG.Blueprint.Chevalley.Tag.cartanE 7 := rfl
  rw [h] at hij ⊢
  revert hij
  fin_cases i <;> fin_cases j <;> decide

private theorem pendant_E8 (i j : Fin 8) (hij : CFSG.Blueprint.Chevalley.Tag.cartan .E8 i j = -1) :
    ∃ m, (CFSG.Blueprint.Chevalley.Tag.cartan .E8 m i = -1 ∧
        CFSG.Blueprint.Chevalley.Tag.cartan .E8 m j = 0) ∨
      (CFSG.Blueprint.Chevalley.Tag.cartan .E8 m i = 0 ∧
        CFSG.Blueprint.Chevalley.Tag.cartan .E8 m j = -1) := by
  have h : CFSG.Blueprint.Chevalley.Tag.cartan .E8 =
      CFSG.Blueprint.Chevalley.Tag.cartanE 8 := rfl
  rw [h] at hij ⊢
  revert hij
  fin_cases i <;> fin_cases j <;> decide

private theorem cartan_E_isSymm :
    (CFSG.Blueprint.Chevalley.Tag.cartan .E6).IsSymm ∧
      (CFSG.Blueprint.Chevalley.Tag.cartan .E7).IsSymm ∧
      (CFSG.Blueprint.Chevalley.Tag.cartan .E8).IsSymm := by
  refine ⟨?_, ?_, ?_⟩
  · change (CFSG.Blueprint.Chevalley.Tag.cartanE 6).IsSymm
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · change (CFSG.Blueprint.Chevalley.Tag.cartanE 7).IsSymm
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · change (CFSG.Blueprint.Chevalley.Tag.cartanE 8).IsSymm
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

private theorem rank_trivialUniversal : trivialUniversal.D.rank = 0 := by
  simp [trivialUniversal, SpecialLinear.rootDatum]

private theorem ggU_pendant_facts {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h3 : 3 ≤ (ggU t n f).D.rank) :
    (ggU t n f).D.cartan.IsSymm ∧ (ggU t n f).D.divisible = ∅ ∧
      ∀ i j, (ggU t n f).D.cartan i j = -1 → ∃ m,
        ((ggU t n f).D.cartan m i = -1 ∧ (ggU t n f).D.cartan m j = 0) ∨
          ((ggU t n f).D.cartan m i = 0 ∧ (ggU t n f).D.cartan m j = -1) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    cases n with
    | zero =>
      have e : ggU .PSL 0 f = trivialUniversal := by
        simp only [ggU, lieUniversal]
      rw [e, rank_trivialUniversal] at h3
      omega
    | succ m =>
      have e : ggU .PSL (m + 1) f =
          ⟨Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
            SpecialLinear.rootDatum m (GaloisField 2 f)⟩ := by
        simp only [ggU, lieUniversal]
      rw [e] at h3 ⊢
      have hm : 3 ≤ m := by
        simpa only [SpecialLinear.rootDatum] using h3
      refine ⟨?_, ?_, ?_⟩
      · exact CartanMatrix.A_isSymm m
      · rfl
      · intro i j hij
        exact pendant_A hm i j hij
  ·
    by_cases hn : 3 ≤ n
    · have e : ggU .POmegaPlus n f =
          ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
            Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
        simp only [ggU, lieUniversal, hn, ↓reduceDIte]
      rw [e] at h3 ⊢
      refine ⟨?_, ?_, ?_⟩
      · exact cartanD_isSymm n
      · rfl
      · intro i j hij
        exact pendant_D hn i j hij
    · have e : ggU .POmegaPlus n f = trivialUniversal := by
        simp only [ggU, lieUniversal, hn, ↓reduceDIte]
      rw [e, rank_trivialUniversal] at h3
      omega
  ·
    have e : ggU .E6 n f = ⟨CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f,
          CFSG.LieType.Steinberg.Exceptional.e6UniversalDatum 2 f⟩ := by
      simp only [ggU, lieUniversal]
    rw [e] at ⊢
    refine ⟨?_, ?_, ?_⟩
    · change (CFSG.Blueprint.Chevalley.Tag.cartan .E6).IsSymm
      exact cartan_E_isSymm.1
    · rfl
    · intro i j hij
      exact pendant_E6 i j hij
  ·
    have e : ggU .E7 n f = ⟨CFSG.LieType.Steinberg.Exceptional.e7UniversalGroup 2 f,
          CFSG.LieType.Steinberg.Exceptional.e7UniversalDatum 2 f⟩ := by
      simp only [ggU, lieUniversal]
    rw [e] at ⊢
    refine ⟨?_, ?_, ?_⟩
    · change (CFSG.Blueprint.Chevalley.Tag.cartan .E7).IsSymm
      exact cartan_E_isSymm.2.1
    · rfl
    · intro i j hij
      exact pendant_E7 i j hij
  ·
    have e : ggU .E8 n f = ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f)),
        CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 f)⟩ := by
      simp only [ggU, lieUniversal]
    rw [e] at ⊢
    refine ⟨?_, ?_, ?_⟩
    · change (CFSG.Blueprint.Chevalley.Tag.cartan .E8).IsSymm
      exact cartan_E_isSymm.2.2
    · rfl
    · intro i j hij
      exact pendant_E8 i j hij

theorem ggRootSeparation {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h3 : 3 ≤ (ggU t n f).D.rank) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α β : Fin (ggU t n f).D.rank → ℤ} (hα : α ∈ (ggU t n f).D.roots)
    (hβ : β ∈ (ggU t n f).D.roots) (c : ZMod p)
    (hprop : ∀ i, ((∑ j, (ggU t n f).D.cartan i j * β j : ℤ) : ZMod p) =
      c * ((∑ j, (ggU t n f).D.cartan i j * α j : ℤ) : ZMod p)) :
    β = α ∨ β = -α := by
  obtain ⟨hS, hdiv, hpend⟩ := ggU_pendant_facts ht h3
  have hα' : α ∈ roots (ggU t n f).D.isFiniteType ∅ := by
    have := hα
    rwa [UniversalRootDatum.roots, hdiv] at this
  have hβ' : β ∈ roots (ggU t n f).D.isFiniteType ∅ := by
    have := hβ
    rwa [UniversalRootDatum.roots, hdiv] at this
  exact ggRootSeparation_of_pendant (ggU t n f).D.isFiniteType hS hpend hp hp2 hα' hβ' c hprop

noncomputable def ggRootEval {r : ℕ} {p : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (α : Fin r → ℤ) :
    (Fin r → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ i, (((∑ j, A i j * α j : ℤ)) : ZMod p) •
    (LinearMap.proj i : (Fin r → ZMod p) →ₗ[ZMod p] ZMod p)

theorem ggRootEval_apply {r : ℕ} {p : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (α : Fin r → ℤ)
    (x : Fin r → ZMod p) :
    ggRootEval (p := p) A α x =
      ∑ i, x i * ((∑ j, A i j * α j : ℤ) : ZMod p) := by
  simp only [ggRootEval, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem ggRootEval_single {r : ℕ} {p : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (α : Fin r → ℤ)
    (i : Fin r) :
    ggRootEval (p := p) A α (Pi.single i 1) =
      ((∑ j, A i j * α j : ℤ) : ZMod p) := by
  rw [ggRootEval_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem ggRootEval_root_self {r : ℕ} {p : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm) {α : Fin r → ℤ}
    (hα : α ∈ roots hA ∅) :
    ggRootEval (p := p) A α (fun i => (α i : ZMod p)) = ((2 : ℤ) : ZMod p) := by
  rw [ggRootEval_apply]
  have h : (∑ i, (α i : ZMod p) * ((∑ j, A i j * α j : ℤ) : ZMod p)) =
      ((rsForm A α α : ℤ) : ZMod p) := by
    calc
      (∑ i, (α i : ZMod p) * ((∑ j, A i j * α j : ℤ) : ZMod p))
          = ∑ i, (((α i * (∑ j, A i j * α j)) : ℤ) : ZMod p) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Int.cast_mul]
      _ = ((∑ i, α i * (∑ j, A i j * α j) : ℤ) : ZMod p) := by
            rw [Int.cast_sum]
      _ = ((rsForm A α α : ℤ) : ZMod p) := by simp only [rsForm]
  rw [h, rsForm_root hA hS hα]

theorem ggRootEval_root_self_ne_zero {r : ℕ} {p : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm) {α : Fin r → ℤ}
    (hα : α ∈ roots hA ∅) (hp : p.Prime) (hp2 : p ≠ 2) :
    ggRootEval (p := p) A α (fun i => (α i : ZMod p)) ≠ 0 := by
  rw [ggRootEval_root_self A hA hS hα]
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

theorem ggRootPair_surjective {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h3 : 3 ≤ (ggU t n f).D.rank) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α β : Fin (ggU t n f).D.rank → ℤ} (hα : α ∈ (ggU t n f).D.roots)
    (hβ : β ∈ (ggU t n f).D.roots) (hβne : β ≠ α) (hβne' : β ≠ -α) :
    Function.Surjective
      ((ggRootEval (p := p) (ggU t n f).D.cartan α).prod
        (ggRootEval (p := p) (ggU t n f).D.cartan β)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hS, hdiv, -⟩ := ggU_pendant_facts ht h3
  set A := (ggU t n f).D.cartan
  have hα' : α ∈ roots (ggU t n f).D.isFiniteType ∅ := by
    have := hα
    rwa [UniversalRootDatum.roots, hdiv] at this
  have hβ' : β ∈ roots (ggU t n f).D.isFiniteType ∅ := by
    have := hβ
    rwa [UniversalRootDatum.roots, hdiv] at this
  set fα := ggRootEval (p := p) A α with hfα
  set fβ := ggRootEval (p := p) A β with hfβ
  have hfα_eval_ne : fα (fun i => (α i : ZMod p)) ≠ 0 := by
    rw [hfα]
    exact ggRootEval_root_self_ne_zero (p := p) A (ggU t n f).D.isFiniteType hS hα' hp hp2
  have hfβ_eval_ne : fβ (fun i => (β i : ZMod p)) ≠ 0 := by
    rw [hfβ]
    exact ggRootEval_root_self_ne_zero (p := p) A (ggU t n f).D.isFiniteType hS hβ' hp hp2
  have hfα_ne : fα ≠ 0 := by
    intro h0
    exact hfα_eval_ne (by rw [h0]; rfl)
  have hfβ_ne : fβ ≠ 0 := by
    intro h0
    exact hfβ_eval_ne (by rw [h0]; rfl)
  have hnot : ∀ c : ZMod p, fα ≠ c • fβ := by
    intro c hc
    have hcoeff : ∀ i, ((∑ j, A i j * α j : ℤ) : ZMod p) =
        c * ((∑ j, A i j * β j : ℤ) : ZMod p) := by
      intro i
      have hci := congrArg
        (fun φ : (Fin (ggU t n f).D.rank → ZMod p) →ₗ[ZMod p] ZMod p =>
          φ (Pi.single i 1)) hc
      have h1 : fα (Pi.single i 1) = ((∑ j, A i j * α j : ℤ) : ZMod p) := by
        rw [hfα]
        exact ggRootEval_single (p := p) A α i
      have h2 : fβ (Pi.single i 1) = ((∑ j, A i j * β j : ℤ) : ZMod p) := by
        rw [hfβ]
        exact ggRootEval_single (p := p) A β i
      have h3 : (c • fβ) (Pi.single i 1) =
          c * ((∑ j, A i j * β j : ℤ) : ZMod p) := by
        rw [LinearMap.smul_apply, smul_eq_mul, h2]
      rw [h1, h3] at hci
      exact hci
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hfα_ne
      rw [hc, hc0, zero_smul]
    have hprop : ∀ i, ((∑ j, A i j * β j : ℤ) : ZMod p) =
        c⁻¹ * ((∑ j, A i j * α j : ℤ) : ZMod p) := by
      intro i
      rw [hcoeff i, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rcases ggRootSeparation hadm ht h3 hp hp2 hα hβ c⁻¹ hprop with h | h
    · exact hβne h
    · exact hβne' h
  exact CFSG.LinearAlgebra.prod_surjective_of_not_proportional_zmod fα fβ hfα_ne hfβ_ne hnot

end Tags

section Coroots

variable {r p : ℕ} [Fact p.Prime]
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem ggRootEval_on_coroots (A : Matrix (Fin r) (Fin r) ℤ)
    (root : Fin r → V →ₗ[ZMod p] ZMod p) (coroot : Fin r → V)
    (hpair : ∀ i j, root j (coroot i) = (A i j : ZMod p))
    (α : Fin r → ℤ) (x : Fin r → ZMod p) :
    (∑ j, (α j : ZMod p) • root j) (∑ i, x i • coroot i) =
      ggRootEval (p := p) A α x := by
  rw [ggRootEval_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, map_sum, map_smul,
    smul_eq_mul, hpair]
  simp_rw [Finset.mul_sum, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ggRootPair_outer_actor_correction {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h3 : 3 ≤ (ggU t n f).D.rank) (hp : p.Prime) (hp2 : p ≠ 2)
    {A T : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup T] [Module (ZMod p) T]
    (φ : A →ₗ[ZMod p] T) (χ : A →ₗ[ZMod p] ZMod p)
    (root : Fin (ggU t n f).D.rank → T →ₗ[ZMod p] ZMod p)
    (coroot : Fin (ggU t n f).D.rank → A)
    (hpair : ∀ i j, root j (φ (coroot i)) = ((ggU t n f).D.cartan i j : ZMod p))
    (hinner : ∀ i, χ (coroot i) = 0)
    {α β : Fin (ggU t n f).D.rank → ℤ}
    (hα : α ∈ (ggU t n f).D.roots) (hβ : β ∈ (ggU t n f).D.roots)
    (hβne : β ≠ α) (hβne' : β ≠ -α) (a : A) :
    ∃ c ∈ Submodule.span (ZMod p) (Set.range coroot),
      (∑ j, (α j : ZMod p) • root j) (φ (a + c)) = 0 ∧
      (∑ j, (β j : ZMod p) • root j) (φ (a + c)) = 0 ∧
      χ (a + c) = χ a := by
  let I := Submodule.span (ZMod p) (Set.range coroot)
  have hspan : I ≤ χ.ker := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hinner i)
  have hvalue : ∀ (γ : Fin (ggU t n f).D.rank → ℤ) (x : Fin (ggU t n f).D.rank → ZMod p),
      (∑ j, (γ j : ZMod p) • root j) (φ (∑ i, x i • coroot i)) =
        ggRootEval (p := p) (ggU t n f).D.cartan γ x := by
    intro γ x
    rw [map_sum]
    simp only [map_smul]
    exact ggRootEval_on_coroots _ root (fun i => φ (coroot i)) hpair γ x
  have hχκ : χ.comp I.subtype = 0 := by
    ext z
    exact hspan z.property
  have hsurj : Function.Surjective
      (((∑ j, (α j : ZMod p) • root j).comp (φ.comp I.subtype)).prod
        ((∑ j, (β j : ZMod p) • root j).comp (φ.comp I.subtype))) := by
    intro y
    obtain ⟨x, hx⟩ := ggRootPair_surjective hadm ht h3 hp hp2 hα hβ hβne hβne' y
    have hsum : (∑ i, x i • coroot i) ∈ I := by
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨⟨∑ i, x i • coroot i, hsum⟩, ?_⟩
    change ((∑ j, (α j : ZMod p) • root j) (φ (∑ i, x i • coroot i)),
      (∑ j, (β j : ZMod p) • root j) (φ (∑ i, x i • coroot i))) = y
    rw [hvalue α x, hvalue β x]
    exact hx
  obtain ⟨c, hc, hc', hcχ⟩ := CFSG.LinearAlgebra.outer_actor_correction I.subtype φ
    (∑ j, (α j : ZMod p) • root j) (∑ j, (β j : ZMod p) • root j) χ hχκ hsurj a
  exact ⟨c, c.property, hc, hc', hcχ⟩

end Coroots

end CFSG.StandardType

end
