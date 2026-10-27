module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairGeneric
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Reflection
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import CFSG.GroupTheory.SupCommute
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.ValMinAbs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

def word {G : Type*} [Monoid G] {k : ℕ} (g : Fin k → G) (w : List (Fin k)) : G := (w.map g).prod

theorem word_mem {G : Type*} [Group G] {k : ℕ} {g : Fin k → G} {S : Subgroup G}
    (w : List (Fin k)) (hw : ∀ x ∈ w, g x ∈ S) : word g w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons i w ih =>
    simp only [word, List.map_cons, List.prod_cons] at ih ⊢
    exact S.mul_mem (hw i (by simp)) (ih fun x hx => hw x (by simp [hx]))

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem coe_mul' (x y : U ≃ₗ[ZMod p] U) :
    ((x * y : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = (x : U →ₗ[ZMod p] U) * y := rfl

theorem toMatrix_word {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Module.Basis ι (ZMod p) U)
    {k : ℕ} {g : Fin k → U ≃ₗ[ZMod p] U} {M : Fin k → Matrix ι ι (ZMod p)}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = M i) (w : List (Fin k)) :
    LinearMap.toMatrix f f ((word g w : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = (w.map M).prod := by
  induction w with
  | nil =>
    simp only [word, List.map_nil, List.prod_nil]
    rw [show ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id from rfl,
      LinearMap.toMatrix_id]
  | cons i w ih =>
    simp only [word, List.map_cons, List.prod_cons] at ih ⊢
    rw [show ((g i * (w.map g).prod : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (g i : U →ₗ[ZMod p] U) * ((w.map g).prod : U →ₗ[ZMod p] U) from rfl,
      LinearMap.toMatrix_mul, hg i, ih]

theorem toMatrix_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Module.Basis ι (ZMod p) U)
    (x : U ≃ₗ[ZMod p] U) (n : ℕ) :
    LinearMap.toMatrix f f ((x ^ n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, show ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id from rfl,
      LinearMap.toMatrix_id]
  | succ n ih =>
    rw [pow_succ,
      show ((x ^ n * x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        ((x ^ n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) * (x : U →ₗ[ZMod p] U) from rfl,
      LinearMap.toMatrix_mul, ih, pow_succ]

theorem ne_one_of_toMatrix_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Module.Basis ι (ZMod p) U) {x : U ≃ₗ[ZMod p] U} {i j : ι}
    (h : LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) i j ≠ (1 : Matrix ι ι (ZMod p)) i j) :
    x ≠ 1 := by
  rintro rfl
  exact h (by rw [show ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id from rfl,
    LinearMap.toMatrix_id])

theorem toMatrix_reflection_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Module.Basis ι (ZMod p) U) {i : ι} {φ : Module.Dual (ZMod p) U} (hφ : φ (f i) = 2)
    (r c : ι) :
    LinearMap.toMatrix f f (Module.reflection hφ : U →ₗ[ZMod p] U) r c =
      (1 : Matrix ι ι (ZMod p)) r c - if r = i then φ (f c) else 0 := by
  rw [LinearMap.toMatrix_apply]
  change f.repr (Module.reflection hφ (f c)) r = _
  rw [Module.reflection_apply, map_sub, map_smul, Module.Basis.repr_self, Module.Basis.repr_self,
    Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hri : r = i
  · subst hri
    by_cases hrc : r = c
    · subst hrc; simp
    · simp [hrc, Ne.symm hrc]
  · by_cases hrc : r = c
    · subst hrc; simp [hri, Ne.symm hri]
    · simp [hri, hrc, Ne.symm hri, Ne.symm hrc]

theorem exists_basis_roots_fixed [Module.Finite (ZMod p) U] (hU : Module.finrank (ZMod p) U = 4)
    {u : Fin 3 → U} {φ : Fin 3 → Module.Dual (ZMod p) U}
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) :
    ∃ f : Module.Basis (Fin 4) (ZMod p) U, (∀ i : Fin 3, f i.castSucc = u i) ∧
      ∀ i, φ i (f 3) = 0 := by
  let L : U →ₗ[ZMod p] (Fin 3 → ZMod p) := LinearMap.pi φ
  have : FiniteDimensional (ZMod p) U := inferInstance
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := L) (by rw [Module.finrank_fin_fun, hU]; norm_num)
  obtain ⟨w, hwL, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hφw : ∀ i, φ i w = 0 := fun i => congrFun hwL i
  let v : Fin 4 → U := ![u 0, u 1, u 2, w]
  have hli : LinearIndependent (ZMod p) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hrow : ∀ i, φ i (u 0) * g 0 + φ i (u 1) * g 1 + φ i (u 2) * g 2 = 0 := by
      intro i
      have := congrArg (φ i) hg
      simp only [Fin.sum_univ_four, v, Matrix.cons_val, map_add, map_smul, smul_eq_mul, map_zero,
        hφw, mul_zero, add_zero] at this
      linear_combination this
    have h3 : (![g 0, g 1, g 2] : Fin 3 → ZMod p) = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      ext i
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hrow i
    have hg012 : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 :=
      ⟨by simpa using congrFun h3 0, by simpa using congrFun h3 1, by simpa using congrFun h3 2⟩
    have hg3 : g 3 = 0 := by
      simp only [Fin.sum_univ_four, v, Matrix.cons_val, hg012.1, hg012.2.1, hg012.2.2,
        zero_smul, zero_add] at hg
      exact (smul_eq_zero.mp hg).resolve_right hw0
    intro j
    fin_cases j
    · exact hg012.1
    · exact hg012.2.1
    · exact hg012.2.2
    · exact hg3
  let f := basisOfLinearIndependentOfCardEqFinrank hli (by rw [hU]; rfl)
  have hf : ∀ j, f j = v j := fun j => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨f, fun i => ?_, fun i => ?_⟩
  · rw [hf]; fin_cases i <;> rfl
  · rw [hf]; exact hφw i

theorem card_closure_pair_of_mul_self {G : Type*} [Group G] {s t : G} (hs : s * s = 1)
    (ht : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1) {n : ℕ} (hn : orderOf (s * t) = n) :
    Nat.card (Subgroup.closure ({s, t} : Set G)) = 2 * n := by
  rw [← TauCeti.range_dihedralHom hs ht hn]
  exact (Nat.card_congr (MonoidHom.ofInjective
    (TauCeti.dihedralHom_injective hs ht hs1 ht1 hn)).toEquiv.symm).trans DihedralGroup.nat_card

namespace WJ34

abbrev Zθ := QuadraticAlgebra ℤ (-2) 1

instance : DecidableEq Zθ := fun x y =>
  decidable_of_iff (x.re = y.re ∧ x.im = y.im) QuadraticAlgebra.ext_iff.symm

def theta : Zθ := ⟨0, 1⟩

def cartan : Matrix (Fin 3) (Fin 4) Zθ := !![2, theta, -1, 0; 1 - theta, 2, -1, 0; -1, -1, 2, 0]

def gen (i : Fin 3) : Matrix (Fin 4) (Fin 4) Zθ :=
  1 - Matrix.of fun r c => if r = i.castSucc then cartan i c else 0

def wordMat (w : List (Fin 3)) : Matrix (Fin 4) (Fin 4) Zθ := (w.map gen).prod

def hWords : List (List (Fin 3)) :=
  [[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [1, 0, 1], [1, 0, 1, 0]]

def tWords : List (List (Fin 3)) :=
  [[], [2], [0, 2], [1, 2], [1, 0, 2], [0, 1, 2], [0, 1, 0, 2],
  [2, 1, 0, 2], [1, 0, 1, 2], [2, 0, 1, 2], [1, 0, 1, 0, 2], [2, 0, 1, 0, 2],
  [0, 2, 1, 0, 2], [2, 1, 0, 1, 2], [1, 2, 0, 1, 2], [2, 1, 0, 1, 0, 2],
  [0, 2, 0, 1, 0, 2], [1, 2, 0, 1, 0, 2], [1, 0, 2, 1, 0, 2], [0, 2, 1, 0, 1, 2],
  [1, 2, 1, 0, 1, 2], [0, 1, 2, 0, 1, 2], [0, 2, 1, 0, 1, 0, 2],
  [1, 2, 1, 0, 1, 0, 2], [0, 1, 2, 0, 1, 0, 2], [0, 1, 0, 2, 1, 0, 2],
  [1, 0, 2, 1, 0, 1, 2], [1, 0, 1, 2, 0, 1, 2], [1, 0, 2, 1, 0, 1, 0, 2],
  [0, 1, 2, 1, 0, 1, 0, 2], [2, 0, 1, 2, 0, 1, 0, 2], [2, 0, 1, 0, 2, 1, 0, 2],
  [2, 1, 0, 2, 1, 0, 1, 2], [2, 1, 0, 1, 2, 0, 1, 2], [0, 1, 0, 2, 1, 0, 1, 0, 2],
  [2, 1, 0, 2, 1, 0, 1, 0, 2], [1, 0, 1, 2, 1, 0, 1, 0, 2],
  [2, 0, 1, 2, 1, 0, 1, 0, 2], [1, 2, 0, 1, 2, 0, 1, 0, 2],
  [1, 2, 0, 1, 0, 2, 1, 0, 2], [1, 0, 1, 0, 2, 1, 0, 1, 0, 2],
  [2, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2]]

def tabK : List (List ℕ) :=
  [[0, 2, 1, 5, 6, 3, 4, 12, 10, 9, 8, 16, 7, 19, 21, 22, 11, 24, 25, 13, 20,
    14, 15, 29, 17, 18, 26, 27, 34, 23, 37, 31, 39, 38, 28, 35, 40, 30, 33, 32, 36, 41],
   [0, 3, 4, 1, 2, 8, 10, 7, 5, 14, 6, 17, 18, 20, 9, 23, 16, 11, 12, 26, 13,
    27, 28, 15, 24, 25, 19, 21, 22, 36, 38, 39, 35, 33, 40, 32, 29, 37, 30, 31, 34, 41],
   [1, 0, 2, 3, 7, 9, 11, 4, 13, 5, 15, 6, 16, 8, 20, 10, 12, 23, 18, 22, 14,
    21, 19, 17, 30, 31, 32, 33, 35, 37, 24, 25, 26, 27, 34, 28, 36, 29, 38, 39, 41, 40]]

def tabH : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6,
    0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 5, 4, 4, 0, 2, 0, 0, 3, 3, 0, 1],
   [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0,
    0, 0, 0, 5, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 2],
   [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0,
    6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 5, 1, 0, 0]]

theorem table_ok : ∀ s : Fin 3, ∀ k : Fin 42,
    gen s * wordMat (tWords.getD k []) =
      wordMat (tWords.getD ((tabK.getD s []).getD k 0) []) *
        wordMat (hWords.getD ((tabH.getD s []).getD k 0) []) := by
  decide +kernel

def zMat : Matrix (Fin 4) (Fin 4) Zθ := Matrix.diagonal ![-1, -1, -1, 1]

def fixVec : Fin 4 → Zθ := ![4, 3 * theta - 1, 2 * theta + 2, 0]

theorem gen_sq : ∀ i, gen i * gen i = 1 := by
  decide +kernel

theorem zMat_comm : ∀ i, zMat * gen i = gen i * zMat := by
  decide +kernel

theorem fixVec_facts : (gen 0).mulVec fixVec = fixVec ∧ (gen 1).mulVec fixVec = fixVec ∧
    zMat.mulVec fixVec = -fixVec := by
  decide +kernel

theorem tab_lt : ∀ s : Fin 3, ∀ k : Fin 42,
    (tabK.getD s []).getD k 0 < 42 ∧ (tabH.getD s []).getD k 0 < 8 := by
  decide +kernel

theorem hWords_letters : ∀ j : Fin 8, ∀ x ∈ hWords.getD j [], x ≠ 2 := by
  decide +kernel

theorem pow_facts : wordMat [2, 1, 0] ^ 7 = zMat ∧ wordMat [2, 1, 0] ^ 14 = 1 ∧
    wordMat [0, 1] ^ 4 = 1 ∧ (wordMat [0, 1] ^ 2) 0 0 = -1 ∧ wordMat [0, 2] ^ 3 = 1 ∧
    wordMat [0, 2] 0 0 = 0 ∧ (wordMat [2, 1, 0] ^ 2) 0 2 = 1 := by
  decide +kernel

theorem entry_facts : gen 0 0 0 = -1 ∧ gen 1 1 1 = -1 ∧ zMat 0 0 = -1 ∧ fixVec 0 = 4 := by
  decide +kernel

noncomputable def ev {R : Type} [CommRing R] (t : R) (ht : t * t = t - 2) : Zθ →+* R :=
  (QuadraticAlgebra.lift ⟨t, by
    rw [ht]
    simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_ofNat, mul_one, one_smul]
    ring⟩).toRingHom

theorem ev_theta {R : Type} [CommRing R] (t : R) (ht : t * t = t - 2) : ev t ht theta = t := by
  simp [ev, theta, QuadraticAlgebra.lift_apply_apply]

theorem map_table {R : Type} [CommRing R] (t : R) (ht : t * t = t - 2) (s : Fin 3)
    (k : Fin 42) : (gen s).map (ev t ht) * (wordMat (tWords.getD k [])).map (ev t ht) =
      (wordMat (tWords.getD ((tabK.getD s []).getD k 0) [])).map (ev t ht) *
        (wordMat (hWords.getD ((tabH.getD s []).getD k 0) [])).map (ev t ht) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, table_ok]

theorem map_gen {R : Type} [CommRing R] (t : R) (ht : t * t = t - 2) (i : Fin 3) :
    (gen i).map (ev t ht) = 1 - Matrix.of fun r c => if r = i.castSucc then
      (!![2, t, -1, 0; 1 - t, 2, -1, 0; -1, -1, 2, 0] : Matrix (Fin 3) (Fin 4) R) i c else 0 := by
  ext r c
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp [gen, cartan, ev_theta, map_sub, map_neg, map_ofNat]

theorem map_wordMat {R : Type} [CommRing R] (t : R) (ht : t * t = t - 2) (w : List (Fin 3)) :
    (wordMat w).map (ev t ht) = (w.map fun i => (gen i).map (ev t ht)).prod := by
  induction w with
  | nil => simp [wordMat]
  | cons i w ih =>
    simp only [wordMat, List.map_cons, List.prod_cons] at ih ⊢
    rw [Matrix.map_mul, ih]

theorem card_le_336 [Module.Finite (ZMod p) U] (f : Module.Basis (Fin 4) (ZMod p) U)
    {t : ZMod p} (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (hH : Nat.card (Subgroup.closure ({g 0, g 1} : Set (U ≃ₗ[ZMod p] U))) = 8) :
    Nat.card (Subgroup.closure (Set.range g)) ≤ 336 := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective
  have hM : ∀ w : List (Fin 3),
      LinearMap.toMatrix f f ((word g w : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        (wordMat w).map (ev t ht) :=
    fun w => (toMatrix_word f (M := fun i => (gen i).map (ev t ht)) hg w).trans
      (map_wordMat t ht w).symm
  have key := CFSG.EvenSporadicStandard.Co1Pair.card_closure_le (Set.range g)
    (Subgroup.closure ({g 0, g 1} : Set (U ≃ₗ[ZMod p] U))) 42 (fun k => word g (tWords.getD k []))
    ⟨0, by norm_num, rfl⟩ ?_
  · rw [hH] at key
    simpa using key
  rintro _ ⟨s, rfl⟩ k hk
  obtain ⟨hk1, hk2⟩ := tab_lt s ⟨k, hk⟩
  refine ⟨_, hk1, word g (hWords.getD ((tabH.getD s []).getD k 0) []), ?_, ?_⟩
  · refine word_mem _ fun x hx => ?_
    have hx2 := hWords_letters ⟨_, hk2⟩ x hx
    fin_cases x
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact absurd rfl hx2
  · apply LinearEquiv.toLinearMap_injective
    apply (LinearMap.toMatrix f f).injective
    rw [coe_mul', coe_mul', LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hg s, hM, hM, hM]
    exact map_table t ht s ⟨k, hk⟩

private theorem neg_one_ne_one (hp : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by linear_combination -h
  exact ZMod.prime_ne_zero p 2 hp h2

theorem toMatrix_word_pow (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (w : List (Fin 3)) (n : ℕ) :
    LinearMap.toMatrix f f ((word g w ^ n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (wordMat w ^ n).map (ev t ht) := by
  have hM : LinearMap.toMatrix f f ((word g w : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (wordMat w).map (ev t ht) :=
    (toMatrix_word f (M := fun i => (gen i).map (ev t ht)) hg w).trans (map_wordMat t ht w).symm
  rw [toMatrix_pow, hM, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]

theorem word_pow_eq_one (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    {w : List (Fin 3)} {n : ℕ} (h : wordMat w ^ n = 1) : word g w ^ n = 1 := by
  have hone : LinearMap.toMatrix f f ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = 1 := by
    rw [show ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id from rfl,
      LinearMap.toMatrix_id]
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix f f).injective
  rw [toMatrix_word_pow f ht hg, h, hone, ← RingHom.mapMatrix_apply, map_one]

theorem word_pow_ne_one (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    {w : List (Fin 3)} {n : ℕ} {i j : Fin 4}
    (h : ev t ht ((wordMat w ^ n) i j) ≠ (1 : Matrix (Fin 4) (Fin 4) (ZMod p)) i j) :
    word g w ^ n ≠ 1 := by
  refine ne_one_of_toMatrix_ne f (i := i) (j := j) ?_
  rwa [toMatrix_word_pow f ht hg, Matrix.map_apply]

theorem gen_mul_self (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (i : Fin 3) : g i * g i = 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix f f).injective
  rw [coe_mul', LinearMap.toMatrix_mul, hg i, ← Matrix.map_mul, gen_sq]
  rw [show ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id from rfl,
    LinearMap.toMatrix_id, Matrix.map_one _ (map_zero _) (map_one _)]

theorem orderOf_gen (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (hp : p ≠ 2) : orderOf (g 0) = 2 ∧ orderOf (g 1) = 2 := by
  obtain ⟨hG0, hG1, -, -⟩ := entry_facts
  have hne1 := neg_one_ne_one hp
  have hord2 : ∀ i : Fin 3, ∀ j : Fin 4, ev t ht (gen i j j) ≠ 1 → orderOf (g i) = 2 := by
    intro i j hij
    refine orderOf_eq_prime (by rw [pow_two]; exact gen_mul_self f ht hg i) ?_
    refine ne_one_of_toMatrix_ne f (i := j) (j := j) ?_
    rwa [hg i, Matrix.map_apply, Matrix.one_apply_eq]
  exact ⟨hord2 0 0 (by rw [hG0, map_neg, map_one]; exact hne1),
    hord2 1 1 (by rw [hG1, map_neg, map_one]; exact hne1)⟩

theorem orderOf_gen_mul (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (hp : p ≠ 2) : orderOf (g 0 * g 1) = 4 := by
  obtain ⟨-, -, hab4, hab2, -, -, -⟩ := pow_facts
  have hne1 := neg_one_ne_one hp
  have hx : g 0 * g 1 = word g [0, 1] := by simp [word]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g 0 * g 1)
    (by rw [hx]; exact word_pow_ne_one f ht hg (w := [0, 1]) (n := 2 ^ 1) (i := 0) (j := 0) (by
      rw [pow_one, hab2, map_neg, map_one, Matrix.one_apply_eq]; exact hne1))
    (by rw [hx]; exact word_pow_eq_one f ht hg (by norm_num [hab4]))
  simpa using h

theorem card_closure_gen (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (hp : p ≠ 2) :
    Nat.card (Subgroup.closure ({g 0, g 1} : Set (U ≃ₗ[ZMod p] U))) = 8 := by
  obtain ⟨ha2, hb2⟩ := orderOf_gen f ht hg hp
  have hab := orderOf_gen_mul f ht hg hp
  have ha1 : g 0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hb1 : g 1 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  simpa using card_closure_pair_of_mul_self (s := g 0) (t := g 1)
    (gen_mul_self f ht hg 0) (gen_mul_self f ht hg 1) ha1 hb1 hab

theorem zElt_facts (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (hp : p ≠ 2) :
    word g [2, 1, 0] ^ 7 ≠ 1 ∧ orderOf (word g [2, 1, 0] ^ 7) = 2 ∧
      ∀ i, word g [2, 1, 0] ^ 7 * g i = g i * word g [2, 1, 0] ^ 7 := by
  obtain ⟨hz7, hz14, -, -, -, -, -⟩ := pow_facts
  obtain ⟨-, -, hZ0, -⟩ := entry_facts
  have hne1 := neg_one_ne_one hp
  have hz1 : word g [2, 1, 0] ^ 7 ≠ 1 :=
    word_pow_ne_one f ht hg (w := [2, 1, 0]) (n := 7) (i := 0) (j := 0) (by
      rw [hz7, hZ0, map_neg, map_one, Matrix.one_apply_eq]; exact hne1)
  have hzz : (word g [2, 1, 0] ^ 7) ^ 2 = 1 := by
    rw [← pow_mul]; exact word_pow_eq_one f ht hg (n := 14) hz14
  have hzo : orderOf (word g [2, 1, 0] ^ 7) = 2 := orderOf_eq_prime hzz hz1
  refine ⟨hz1, hzo, fun i => ?_⟩
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix f f).injective
  rw [coe_mul', coe_mul', LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, toMatrix_word_pow f ht hg,
    hg i, hz7, ← Matrix.map_mul, ← Matrix.map_mul, zMat_comm]

private theorem repr_fixVec (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {x : U ≃ₗ[ZMod p] U} {M : Matrix (Fin 4) (Fin 4) Zθ}
    (hxM : LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) = M.map (ev t ht))
    {u : U} (hru : ∀ j, f.repr u j = ev t ht (fixVec j)) (j : Fin 4) :
    f.repr (x u) j = ev t ht ((M.mulVec fixVec) j) := by
  have h := congrFun (LinearMap.toMatrix_mulVec_repr f f (x : U →ₗ[ZMod p] U) u) j
  rw [hxM] at h
  rw [show (x u) = (x : U →ₗ[ZMod p] U) u from rfl, ← h, RingHom.map_mulVec]
  congr 1
  ext i
  exact hru i

theorem exists_fixVec (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (hp : p ≠ 2) :
    ∃ u : U, u ≠ 0 ∧ g 0 u = u ∧ g 1 u = u ∧ (word g [2, 1, 0] ^ 7) u = -u := by
  obtain ⟨hu0a, hu0b, hu0z⟩ := fixVec_facts
  obtain ⟨hz7, -, -, -, -, -, -⟩ := pow_facts
  obtain ⟨-, -, -, hu00⟩ := entry_facts
  set u : U := f.equivFun.symm (fun i => ev t ht (fixVec i)) with hu
  have hru : ∀ j, f.repr u j = ev t ht (fixVec j) := fun j => by
    rw [← Module.Basis.equivFun_apply, hu, LinearEquiv.apply_symm_apply]
  have hfix0 : g 0 u = u := by
    apply f.repr.injective
    ext j
    rw [repr_fixVec f ht (hg 0) hru j, hu0a, hru]
  have hfix1 : g 1 u = u := by
    apply f.repr.injective
    ext j
    rw [repr_fixVec f ht (hg 1) hru j, hu0b, hru]
  have hzu : (word g [2, 1, 0] ^ 7) u = -u := by
    apply f.repr.injective
    ext j
    rw [repr_fixVec f ht (toMatrix_word_pow f ht hg [2, 1, 0] 7) hru j, hz7, hu0z, map_neg,
      Finsupp.neg_apply, hru, Pi.neg_apply, map_neg]
  have hu0 : u ≠ 0 := by
    intro h0
    have h4 : (4 : ZMod p) = 0 := by
      have := hru 0
      rw [h0, hu00, map_ofNat] at this
      simpa using this.symm
    have h2 : (2 : ZMod p) * 2 = 0 := by rw [← h4]; norm_num
    exact ZMod.prime_ne_zero p 2 hp (mul_self_eq_zero.mp h2)
  exact ⟨u, hu0, hfix0, hfix1, hzu⟩

theorem zElt_not_mem (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (hp : p ≠ 2) :
    word g [2, 1, 0] ^ 7 ∉ Subgroup.closure ({g 0, g 1} : Set (U ≃ₗ[ZMod p] U)) := by
  obtain ⟨u, hu0, hfix0, hfix1, hzu⟩ := exists_fixVec f ht hg hp
  have hHfix : ∀ x ∈ Subgroup.closure ({g 0, g 1} : Set (U ≃ₗ[ZMod p] U)), x u = u := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hfix0
      · exact hfix1
    | one => rfl
    | mul x y _ _ hx hy => rw [LinearEquiv.mul_apply, hy, hx]
    | inv x _ hx =>
      conv_lhs => rw [← hx]
      exact x.symm_apply_apply u
  intro hzH
  have h1 := hHfix _ hzH
  rw [hzu] at h1
  apply hu0
  have h2 : (2 : ZMod p) • u = 0 := by rw [two_smul]; nth_rewrite 1 [← h1]; simp
  exact (smul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)

theorem sixteen_dvd_card (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (hp : p ≠ 2) : 16 ∣ Nat.card (Subgroup.closure (Set.range g)) := by
  obtain ⟨-, hzo, hzc⟩ := zElt_facts f ht hg hp
  have hzH := zElt_not_mem f ht hg hp
  have hH8 : Nat.card (Subgroup.closure ({g 0, g 1} : Set (U ≃ₗ[ZMod p] U))) = 8 :=
    card_closure_gen f ht hg hp
  set H := Subgroup.closure ({g 0, g 1} : Set (U ≃ₗ[ZMod p] U)) with hHdef
  have hcomm : ∀ x ∈ H, ∀ y ∈ Subgroup.zpowers (word g [2, 1, 0] ^ 7), Commute x y := by
    have hHc : H ≤ Subgroup.centralizer {word g [2, 1, 0] ^ 7} := by
      rw [hHdef, Subgroup.closure_le]
      rintro y (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      · exact (hzc 0).symm
      · exact (hzc 1).symm
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxz : Commute x (word g [2, 1, 0] ^ 7) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hHc hx)
    exact hxz.zpow_right k
  have hdisj : H ⊓ Subgroup.zpowers (word g [2, 1, 0] ^ 7) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyH, hyz⟩ := hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyz
    have hk2 : (word g [2, 1, 0] ^ 7) ^ k = (word g [2, 1, 0] ^ 7) ^ (k % 2) := by
      rw [← zpow_mod_orderOf (word g [2, 1, 0] ^ 7) k, hzo]; norm_num
    rw [Subgroup.mem_bot, hk2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero]
    · rw [hk2, h, zpow_one] at hyH
      exact absurd hyH hzH
  have h16 : Nat.card (H ⊔ Subgroup.zpowers (word g [2, 1, 0] ^ 7) :
      Subgroup (U ≃ₗ[ZMod p] U)) = 16 := by
    simpa [hH8, Nat.card_zpowers, hzo] using
      CFSG.card_sup_eq_mul_of_commute H (Subgroup.zpowers (word g [2, 1, 0] ^ 7)) hcomm hdisj
  have hle : H ⊔ Subgroup.zpowers (word g [2, 1, 0] ^ 7) ≤
      Subgroup.closure (Set.range g) := by
    refine sup_le ?_ ?_
    · rw [hHdef, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.subset_closure ⟨0, rfl⟩
      · exact Subgroup.subset_closure ⟨1, rfl⟩
    · rw [Subgroup.zpowers_le]
      exact (Subgroup.closure (Set.range g)).pow_mem
        (word_mem _ fun x _ => Subgroup.subset_closure ⟨x, rfl⟩) 7
  exact h16 ▸ Subgroup.card_dvd_of_le hle

theorem three_dvd_card (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (_hp : p ≠ 2) : 3 ∣ Nat.card (Subgroup.closure (Set.range g)) := by
  obtain ⟨-, -, -, -, hac3, hac0, -⟩ := pow_facts
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : orderOf (word g [0, 2]) = 3 := by
    refine orderOf_eq_prime (word_pow_eq_one f ht hg hac3) ?_
    simpa using word_pow_ne_one f ht hg (w := [0, 2]) (n := 1) (i := 0) (j := 0) (by
      rw [pow_one, hac0, map_zero, Matrix.one_apply_eq]; exact zero_ne_one)
  have hdvd : orderOf (word g [0, 2]) ∣ Nat.card (Subgroup.closure (Set.range g)) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.closure (Set.range g))
      (word_mem _ fun x _ => Subgroup.subset_closure ⟨x, rfl⟩)
  rwa [h3] at hdvd

theorem seven_dvd_card (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t * t = t - 2) {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht))
    (_hp : p ≠ 2) : 7 ∣ Nat.card (Subgroup.closure (Set.range g)) := by
  obtain ⟨-, hz14, -, -, -, -, hcba2⟩ := pow_facts
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h7 : orderOf (word g [2, 1, 0] ^ 2) = 7 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← pow_mul]; exact word_pow_eq_one f ht hg (n := 14) hz14
    · exact word_pow_ne_one f ht hg (w := [2, 1, 0]) (n := 2) (i := 0) (j := 2) (by
        rw [hcba2, map_one, Matrix.one_apply_ne (by decide)]; exact one_ne_zero)
  have hdvd : orderOf (word g [2, 1, 0] ^ 2) ∣ Nat.card (Subgroup.closure (Set.range g)) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.closure (Set.range g))
      ((Subgroup.closure (Set.range g)).pow_mem
        (word_mem _ fun x _ => Subgroup.subset_closure ⟨x, rfl⟩) 2)
  rwa [h7] at hdvd

theorem card_eq_336 [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p} (ht : t * t = t - 2)
    {g : Fin 3 → U ≃ₗ[ZMod p] U}
    (hg : ∀ i, LinearMap.toMatrix f f (g i : U →ₗ[ZMod p] U) = (gen i).map (ev t ht)) :
    Nat.card (Subgroup.closure (Set.range g)) = 336 := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective
  have hH : Nat.card (Subgroup.closure ({g 0, g 1} : Set (U ≃ₗ[ZMod p] U))) = 8 :=
    card_closure_gen f ht hg hp
  have hle := card_le_336 f ht hg hH
  have h16 := sixteen_dvd_card f ht hg hp
  have h3 := three_dvd_card f ht hg hp
  have h7 := seven_dvd_card f ht hg hp
  have hd : 336 ∣ Nat.card (Subgroup.closure (Set.range g)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 48 7)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 16 3) h16 h3) h7
  have hpos : 0 < Nat.card (Subgroup.closure (Set.range g)) := Nat.card_pos
  exact le_antisymm hle (Nat.le_of_dvd hpos hd)

end WJ34

end CFSG.StandardType.ZS
