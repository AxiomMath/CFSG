module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBaseChange
public import TauCeti.FieldTheory.Finite.FrobeniusFixed
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Descent

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

theorem descent_core_alg {k₀ : Type*} [Field k₀] {n : ℕ} (hn : 1 ≤ n) {F : Type*} [Field F]
    [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ n) {W : Type*} [AddCommGroup W]
    [Module k₀ W] [Finite W] (ρ : Representation k₀ SL(2, F) W)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d)
    (b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W)
    {E : Type*} [Field E] [CharP E 2] [Algebra F E] (ιD : EndRing ρ →+* E) :
    ∃ J : Finset ℕ, J.Nonempty ∧ (∀ i ∈ J, i < n) ∧
      Nonempty ((matRepE b ιD).Equiv (frobTensor F E J)) ∧
      J.image (fun i => (i + d) % n) = J ∧
      Module.finrank (EndRing ρ) W = 2 ^ J.card := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have hιDinj : Function.Injective ιD := ιD.injective
  have hfrobD : ∀ a : EndRing ρ, (ιD a) ^ (2 ^ d) = ιD a := by
    intro a
    have : Fintype (EndRing ρ) := Fintype.ofFinite _
    rw [← map_pow]
    congr 1
    have h1 := FiniteField.pow_card a
    have hfc : Fintype.card (EndRing ρ) = 2 ^ d := by
      rw [Fintype.card_eq_nat_card]; exact hDcard
    rwa [hfc] at h1
  have hirr := matRepE_isIrreducible b ιD
  obtain ⟨J, ⟨hJn, ⟨Φ⟩⟩, -⟩ := frobTensor_classification hF (matRepE b ιD) hirr
  have hJne : J.Nonempty := by
    by_contra hJ0
    rw [Finset.not_nonempty_iff_eq_empty] at hJ0
    subst hJ0
    obtain ⟨g, hg⟩ := hnt
    apply hg
    have hid : ∀ x, matRepE b ιD g x = x := by
      intro x
      have h1 := equiv_apply Φ g x
      rw [frobTensor_empty_apply] at h1
      exact Φ.toLinearEquiv.injective h1
    have hmat : (matRep b g).map ιD = 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro x
      have := hid x
      rw [matRepE_apply] at this
      simpa [Matrix.toLin'_apply] using this
    have hmat' : matRep b g = 1 := by
      have : (matRep b g).map ιD = (1 : Matrix (Fin _) (Fin _) (EndRing ρ)).map ιD := by
        rw [hmat, Matrix.map_one ιD (map_zero ιD) (map_one ιD)]
      exact Matrix.map_injective hιDinj this
    have hrep : repD ρ g = 1 := by
      apply (LinearMap.toMatrix b b).injective
      rw [show LinearMap.toMatrix b b (repD ρ g) = matRep b g from rfl, hmat',
        LinearMap.toMatrix_one]
    apply LinearMap.ext
    intro w
    have h1 := congrArg (fun f : Module.End (EndRing ρ) W => f w) hrep
    have h2 : repD ρ g w = w := by simpa using h1
    exact h2
  have hdim : Module.finrank (EndRing ρ) W = 2 ^ J.card := by
    have h1 := Φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at h1
    exact h1
  have hshift : J.image (fun i => (i + d) % n) = J := by
    have hA : ∀ g, ((matRep b g).map ιD).map (iterateFrobenius E 2 d) = (matRep b g).map ιD := by
      intro g
      ext i j
      simp only [Matrix.map_apply, iterateFrobenius_def]
      exact hfrobD _
    obtain ⟨Φ'⟩ := equiv_frob_twist d (fun i : J => (i : ℕ)) (fun g => (matRep b g).map ιD) hA
      (matRepE b ιD) (fun g x => matRepE_apply b ιD g x) Φ
    exact frobTensor_shift_eq' (by omega) hF hJn (Φ'.symm.trans Φ)
  exact ⟨J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩


theorem descent_core_gen {k₀ : Type*} [Field k₀] {n : ℕ} (hn : 1 ≤ n) {F : Type*} [Field F]
    [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ n) {W : Type*} [AddCommGroup W]
    [Module k₀ W] [Finite W] (ρ : Representation k₀ SL(2, F) W)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d)
    (b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W)
    {E : Type*} [Field E] [CharP E 2] (ιF : F →+* E) (ιD : EndRing ρ →+* E) :
    ∃ J : Finset ℕ, J.Nonempty ∧ (∀ i ∈ J, i < n) ∧
      (letI := ιF.toAlgebra
       Nonempty ((matRepE b ιD).Equiv (frobTensor F E J))) ∧
      J.image (fun i => (i + d) % n) = J ∧
      Module.finrank (EndRing ρ) W = 2 ^ J.card := by
  letI := ιF.toAlgebra
  exact descent_core_alg hn hF ρ hnt hDcard b ιD

section Density

variable {k₀ : Type*} [Field k₀] {G : Type*} [Monoid G] {W : Type*} [AddCommGroup W] [Module k₀ W]
  {ρ : Representation k₀ G W} [Fact ρ.IsIrreducible] [Finite W]

theorem density_closure {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    (P : Matrix (Fin m) (Fin m) (EndRing ρ) → Prop)
    (hadd : ∀ Y Y', P Y → P Y' → P (Y + Y')) (hmul : ∀ Y Y', P Y → P Y' → P (Y * Y'))
    (hsc : ∀ c : k₀, P (Matrix.diagonal fun _ => algebraMap k₀ (EndRing ρ) c))
    (hgen : ∀ g, P (matRep b g)) (Y : Matrix (Fin m) (Fin m) (EndRing ρ)) : P Y := by
  obtain ⟨r, hr⟩ := density_surjective (ρ := ρ) ((LinearMap.toMatrix b b).symm Y)
  have h1 : (LinearMap.toMatrix b b).symm Y = actD r := LinearMap.ext fun w => hr w
  have h2 : Y = LinearMap.toMatrix b b (actD r) := by rw [← h1]; simp
  have hclaim : ∀ r : Module.End k₀ W, ∀ hr : r ∈ spanAlg ρ,
      P (LinearMap.toMatrix b b (actD ⟨r, hr⟩)) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      simpa [matRep, actD_gen] using hgen g
    | algebraMap c =>
      have h1 := actD_algebraMap (ρ := ρ) c
      have h2 : (⟨algebraMap k₀ (Module.End k₀ W) c, Subalgebra.algebraMap_mem _ c⟩ :
          spanAlg ρ) = algebraMap k₀ (spanAlg ρ) c := rfl
      rw [h2, h1, LinearMap.toMatrix_algebraMap]
      simpa only [Matrix.scalar_apply] using hsc c
    | add x y hx hy ihx ihy =>
      have h1 : actD (⟨x + y, add_mem hx hy⟩ : spanAlg ρ) =
          actD (⟨x, hx⟩ : spanAlg ρ) + actD (⟨y, hy⟩ : spanAlg ρ) := rfl
      rw [h1, map_add]
      exact hadd _ _ ihx ihy
    | mul x y hx hy ihx ihy =>
      have h1 : actD (⟨x * y, mul_mem hx hy⟩ : spanAlg ρ) =
          actD (⟨x, hx⟩ : spanAlg ρ) * actD (⟨y, hy⟩ : spanAlg ρ) := rfl
      rw [h1, LinearMap.toMatrix_mul]
      exact hmul _ _ ihx ihy
  rw [h2]
  exact hclaim r r.2

end Density


section Embedding

variable {k₀ : Type*} [Field k₀] [Fintype k₀] {F : Type*} [Field F] [Fintype F] [CharP F 2]
  {W : Type*} [AddCommGroup W] [Module k₀ W] [Finite W] {ρ : Representation k₀ SL(2, F) W}
  [Fact ρ.IsIrreducible]

theorem exists_eq_algebraMap_of_equiv {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    (κ : k₀ →+* F) {E : Type*} [Field E] [CharP E 2] [Algebra F E] (ιD : EndRing ρ →+* E)
    {J : Finset ℕ} (Φ : (matRepE b ιD).Equiv (frobTensor F E J)) (c : EndRing ρ) :
    ∃ f : F, ιD c = algebraMap F E f := by
  classical
  letI : Algebra k₀ E := ((algebraMap F E).comp κ).toAlgebra
  let P : Matrix (Fin m) (Fin m) (EndRing ρ) → Prop := fun Y =>
    ∃ Z : Matrix (J → Fin 2) (J → Fin 2) F, ∀ x : Fin m → E,
      Φ ((Y.map ιD).mulVec x) = (Z.map (algebraMap F E)).mulVec (Φ x)
  have hadd : ∀ Y Y', P Y → P Y' → P (Y + Y') := by
    rintro Y Y' ⟨Z, hZ⟩ ⟨Z', hZ'⟩
    refine ⟨Z + Z', fun x => ?_⟩
    rw [Matrix.map_add _ ιD.map_add, Matrix.add_mulVec, map_add, hZ, hZ',
      Matrix.map_add _ (algebraMap F E).map_add, Matrix.add_mulVec]
  have hmul : ∀ Y Y', P Y → P Y' → P (Y * Y') := by
    rintro Y Y' ⟨Z, hZ⟩ ⟨Z', hZ'⟩
    refine ⟨Z * Z', fun x => ?_⟩
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hZ, hZ', Matrix.map_mul, ← Matrix.mulVec_mulVec]
  have hsc : ∀ c : k₀, P (Matrix.diagonal fun _ => algebraMap k₀ (EndRing ρ) c) := by
    intro c
    have h1 : (ιD (algebraMap k₀ (EndRing ρ) c)) ^ Fintype.card k₀ =
        ιD (algebraMap k₀ (EndRing ρ) c) := by
      rw [← map_pow, ← map_pow, FiniteField.pow_card]
    obtain ⟨c', hc'⟩ := (TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap _).mp h1
    refine ⟨Matrix.diagonal fun _ => κ c', fun x => ?_⟩
    rw [Matrix.diagonal_map ιD.map_zero, Matrix.diagonal_map (algebraMap F E).map_zero]
    have h2 : algebraMap k₀ E c' = algebraMap F E (κ c') := rfl
    rw [h2] at hc'
    rw [← hc']
    have h3 : ∀ (y : Fin m → E), (Matrix.diagonal fun _ => algebraMap F E (κ c')).mulVec y =
        algebraMap F E (κ c') • y := fun y => by
      funext i
      simp [Matrix.mulVec_diagonal]
    have h4 : ∀ (y : (J → Fin 2) → E),
        (Matrix.diagonal fun _ => algebraMap F E (κ c')).mulVec y =
        algebraMap F E (κ c') • y := fun y => by
      funext i
      simp [Matrix.mulVec_diagonal]
    rw [h3, h4, map_smul]
  have hgen : ∀ g, P (matRep b g) := by
    intro g
    refine ⟨Matrix.of fun x' x => ∏ i : J, (g (x' i) (x i)) ^ (2 ^ (i : ℕ)), fun x => ?_⟩
    have h1 := equiv_apply Φ g x
    rw [matRepE_apply] at h1
    rw [h1]
    funext x'
    rw [show frobTensor F E J g (Φ x) x' = ∑ y, tmatE E (fun i : J => (i : ℕ)) g x' y * Φ x y
      from tensorRep_apply _ g _ x']
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, tmatE, twistMat_apply,
      map_prod, map_pow]
  have key : ∀ c : EndRing ρ, P (Matrix.diagonal fun _ => c) := fun c =>
    density_closure b P hadd hmul hsc hgen _
  obtain ⟨Z, hZ⟩ := key c
  let j0 : J → Fin 2 := fun _ => 0
  have h5 := hZ (Φ.symm (Pi.single j0 1))
  rw [Representation.Equiv.apply_symm_apply] at h5
  have h6 : ((Matrix.diagonal fun _ => c).map ιD).mulVec (Φ.symm (Pi.single j0 1)) =
      ιD c • Φ.symm (Pi.single j0 1) := by
    rw [Matrix.diagonal_map ιD.map_zero]
    funext i
    simp [Matrix.mulVec_diagonal]
  rw [h6, map_smul, Representation.Equiv.apply_symm_apply] at h5
  refine ⟨Z j0 j0, ?_⟩
  have h7 := congrFun h5 j0
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.single_apply] using h7


theorem exists_ringHom_endRing {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    (κ : k₀ →+* F) {E : Type*} [Field E] [CharP E 2] [Algebra F E] (ιD : EndRing ρ →+* E)
    {J : Finset ℕ} (Φ : (matRepE b ιD).Equiv (frobTensor F E J)) :
    ∃ ν : EndRing ρ →+* F, ∀ c, ιD c = algebraMap F E (ν c) := by
  choose ν hν using exists_eq_algebraMap_of_equiv b κ ιD Φ
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  refine ⟨{ toFun := ν, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hν⟩
  · apply hinj
    rw [← hν, ιD.map_one, (algebraMap F E).map_one]
  · intro a a'
    apply hinj
    rw [← hν, ιD.map_mul, (algebraMap F E).map_mul, ← hν, ← hν]
  · apply hinj
    rw [← hν, ιD.map_zero, (algebraMap F E).map_zero]
  · intro a a'
    apply hinj
    rw [← hν, ιD.map_add, (algebraMap F E).map_add, ← hν, ← hν]


theorem exists_descent_gen [CharP k₀ 2] {k n : ℕ} (hk : Fintype.card k₀ = 2 ^ k) (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (hnt : ∃ g, ρ g ≠ 1) :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card (EndRing ρ) = 2 ^ (k * f) ∧
      ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W,
        ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (_ : Algebra F E)
          (ιD : EndRing ρ →+* E) (J : Finset ℕ),
          J.Nonempty ∧ (∀ i ∈ J, i < n) ∧
          Nonempty ((matRepE b ιD).Equiv (frobTensor F E J)) ∧
          J.image (fun i => (i + k * f) % n) = J ∧
          Module.finrank (EndRing ρ) W = 2 ^ J.card := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite k₀ (EndRing ρ) := Module.Finite.of_finite
  have : Fintype (EndRing ρ) := Fintype.ofFinite _
  have hDk : Nat.card (EndRing ρ) = 2 ^ (k * Module.finrank k₀ (EndRing ρ)) := by
    rw [Module.natCard_eq_pow_finrank (K := k₀) (V := EndRing ρ), Nat.card_eq_fintype_card, hk,
      ← pow_mul]
  have hf1 : 1 ≤ Module.finrank k₀ (EndRing ρ) := Module.finrank_pos
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · have := Fintype.one_lt_card (α := k₀)
      rw [hk, h0] at this
      simp at this
    · exact h0
  refine ⟨Module.finrank k₀ (EndRing ρ), hf1, hDk, fun b => ?_⟩
  have : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap k₀ (EndRing ρ)).injective 2
  have hFcard : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨e, E, hEF, hEfin, hEchar, ιF, ιD, -, -, -, -, hιFinj, hιDinj, -, hfrobD, -⟩ :=
    finite_fields_common_extension 2 hn (Nat.one_le_iff_ne_zero.mpr (by positivity)) hFcard hDk
  obtain ⟨J, hJne, hJn, hΦ, hshift, hdim⟩ := descent_core_gen hn hF ρ hnt hDk b ιF ιD
  exact ⟨E, hEF, hEfin, hEchar, ιF.toAlgebra, ιD, J, hJne, hJn, hΦ, hshift, hdim⟩


theorem kDescent [CharP k₀ 2] {k n : ℕ} (hk : Fintype.card k₀ = 2 ^ k) (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (κ : k₀ →+* F) (hnt : ∃ g, ρ g ≠ 1) :
    ∃ (f : ℕ) (J : Finset ℕ), 1 ≤ f ∧ Nat.card (EndRing ρ) = 2 ^ (k * f) ∧ k * f ∣ n ∧
      J.Nonempty ∧ (∀ i ∈ J, i < n) ∧ J.image (fun i => (i + k * f) % n) = J ∧
      Module.finrank k₀ W = f * 2 ^ J.card := by
  classical
  obtain ⟨f, hf1, hDk, hb⟩ := exists_descent_gen (ρ := ρ) hk hn hF hnt
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, _, _, _, _, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ :=
    hb (Module.finBasis (EndRing ρ) W)
  obtain ⟨ν, -⟩ := exists_ringHom_endRing (Module.finBasis (EndRing ρ) W) κ ιD Φ
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · have := Fintype.one_lt_card (α := k₀)
      rw [hk, h0] at this
      simp at this
    · exact h0
  refine ⟨f, J, hf1, hDk, ?_, hJne, hJn, hshift, ?_⟩
  · letI := ν.toAlgebra
    haveI : Module.Finite (EndRing ρ) F := Module.Finite.of_finite
    have h1 := Module.natCard_eq_pow_finrank (K := EndRing ρ) (V := F)
    rw [Nat.card_eq_fintype_card, hF, hDk, ← pow_mul] at h1
    exact ⟨Module.finrank (EndRing ρ) F, (Nat.pow_right_injective le_rfl h1)⟩
  · have h1 := Module.natCard_eq_pow_finrank (K := k₀) (V := W)
    have h2 := natCard_eq_pow_finrank (ρ := ρ)
    rw [h2, hDk, hdim, ← pow_mul, Nat.card_eq_fintype_card, hk, ← pow_mul] at h1
    have h3 := Nat.pow_right_injective le_rfl h1
    have h4 : k * (f * 2 ^ J.card) = k * Module.finrank k₀ W := by rw [← h3]; ring
    exact (Nat.eq_of_mul_eq_mul_left hk1 h4).symm


theorem dvd_of_ringHom {D F' : Type*} [Field D] [Field F'] [Finite D] [Fintype F']
    (ν : D →+* F') {m n : ℕ} (hD : Nat.card D = 2 ^ m) (hF : Fintype.card F' = 2 ^ n) : m ∣ n := by
  letI := ν.toAlgebra
  haveI : Module.Finite D F' := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := D) (V := F')
  rw [Nat.card_eq_fintype_card, hF, hD, ← pow_mul] at h1
  exact ⟨Module.finrank D F', Nat.pow_right_injective le_rfl h1⟩

theorem coords_injective {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E]
    (ι : EndRing ρ →+* E) :
    Function.Injective fun (w : W) (i : Fin m) => ι (b.repr w i) := by
  intro w w' h
  apply b.repr.injective
  exact Finsupp.ext fun i => ι.injective (congrFun h i)

theorem coords_rep {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E]
    (ι : EndRing ρ →+* E) (g : SL(2, F)) (w : W) :
    (fun i => ι (b.repr (ρ g w) i)) =
      ((matRep b g).map ι).mulVec (fun i => ι (b.repr w i)) := by
  funext i
  have h1 := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  have h2 := congrFun h1 i
  rw [repD_apply] at h2
  show ι (b.repr (ρ g w) i) = (((matRep b g).map ι).mulVec (fun i => ι (b.repr w i))) i
  rw [← h2]
  exact ι.map_mulVec (matRep b g) (⇑(b.repr w)) i

theorem finrank_eq_mul_finrank {k f : ℕ} (hk : Fintype.card k₀ = 2 ^ k) (hk1 : 1 ≤ k)
    (hDk : Nat.card (EndRing ρ) = 2 ^ (k * f)) :
    Module.finrank k₀ W = f * Module.finrank (EndRing ρ) W := by
  have h1 := Module.natCard_eq_pow_finrank (K := k₀) (V := W)
  have h2 := natCard_eq_pow_finrank (ρ := ρ)
  rw [h2, hDk, ← pow_mul, Nat.card_eq_fintype_card, hk, ← pow_mul] at h1
  have h3 := Nat.pow_right_injective le_rfl h1
  have h4 : k * (f * Module.finrank (EndRing ρ) W) = k * Module.finrank k₀ W := by
    rw [← h3]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hk1 h4).symm

theorem card_fixRoot_coord {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) :
    Nat.card {w : W // ∀ t : F, ρ (uElt t) w = w} =
      Nat.card {x : Fin m → EndRing ρ // ∀ t : F, (matRep b (uElt t) - 1).mulVec x = 0} := by
  refine Nat.card_congr (Equiv.subtypeEquiv b.equivFun.toEquiv fun w => forall_congr' fun t => ?_)
  have h1 := LinearMap.toMatrix_mulVec_repr b b (repD ρ (uElt t)) w
  rw [repD_apply] at h1
  have h2 : (matRep b (uElt t) - 1).mulVec (b.equivFun w) = b.equivFun (ρ (uElt t) w - w) := by
    rw [map_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Module.Basis.equivFun_apply,
      Module.Basis.equivFun_apply, ← h1]
    rfl
  rw [LinearEquiv.coe_toEquiv, h2, LinearEquiv.map_eq_zero_iff, sub_eq_zero]

theorem card_fixRoot_ext {n : ℕ} (hF : Fintype.card F = 2 ^ n) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E] [CharP E 2] [Algebra F E]
    (ιD : EndRing ρ →+* E) {J : Finset ℕ} (hJn : ∀ i ∈ J, i < n)
    (Φ : (matRepE b ιD).Equiv (frobTensor F E J)) :
    Nat.card {x : Fin m → E // ∀ t : F, ((matRep b (uElt t) - 1).map ιD).mulVec x = 0} =
      Nat.card E := by
  have hfix : ∀ x : Fin m → E, (∀ t : F, ((matRep b (uElt t) - 1).map ιD).mulVec x = 0) ↔
      ∃ c : E, Φ x = c • baseVec := by
    intro x
    rw [← tensorRep_fixed_iff hF (fun i : J => (i : ℕ)) Subtype.val_injective
      (fun i => hJn i i.2) (Φ x)]
    refine forall_congr' fun t => ?_
    have h1 : Φ (matRepE b ιD (uElt t) x) =
        tensorRep F E (fun i : J => (i : ℕ)) (uElt t) (Φ x) := equiv_apply Φ (uElt t) x
    rw [Matrix.map_sub _ ιD.map_sub, Matrix.map_one _ ιD.map_zero ιD.map_one, Matrix.sub_mulVec,
      Matrix.one_mulVec, ← matRepE_apply, sub_eq_zero, ← h1]
    exact ⟨fun h => by rw [h], fun h => Φ.toLinearEquiv.injective h⟩
  let f : E → {x : Fin m → E // ∀ t : F, ((matRep b (uElt t) - 1).map ιD).mulVec x = 0} :=
    fun c => ⟨Φ.symm (c • baseVec),
      (hfix _).2 ⟨c, Representation.Equiv.apply_symm_apply Φ _⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      have h1 := congrArg (fun y => Φ y.1) h
      simp only [f, Representation.Equiv.apply_symm_apply] at h1
      have h2 := congrFun h1 (fun _ => 0)
      simpa [baseVec_apply] using h2
    · rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ := (hfix x).1 hx
      refine ⟨c, Subtype.ext ?_⟩
      show Φ.symm (c • baseVec) = x
      rw [← hc, Representation.Equiv.symm_apply_apply]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_fixRoot_gen [CharP k₀ 2] {k n : ℕ} (hk : Fintype.card k₀ = 2 ^ k) (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (hnt : ∃ g, ρ g ≠ 1) :
    Nat.card {w : W // ∀ t : F, ρ (uElt t) w = w} = Nat.card (EndRing ρ) := by
  classical
  obtain ⟨f, hf1, hDk, hb⟩ := exists_descent_gen (ρ := ρ) hk hn hF hnt
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨E, _, _, _, _, ιD, J, -, hJn, ⟨Φ⟩, -, -⟩ := hb b
  have hbc := natCard_common_ker_map ιD fun t : F => matRep b (uElt t) - 1
  rw [card_fixRoot_ext hF b ιD hJn Φ] at hbc
  letI := ιD.toAlgebra
  haveI : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
  have hE : Nat.card E = Nat.card (EndRing ρ) ^ Module.finrank (EndRing ρ) E :=
    Module.natCard_eq_pow_finrank
  have hr : Module.finrank (EndRing ρ) E ≠ 0 := Module.finrank_pos.ne'
  rw [hE] at hbc
  rw [card_fixRoot_coord b]
  exact (Nat.pow_left_injective hr hbc).symm

end Embedding

theorem dvd_card_of_shift {k e : ℕ} (hk : 0 < k) {J : Finset ℕ} (hJ : ∀ i ∈ J, i < k * e)
    (hshift : J.image (fun i => (i + k) % (k * e)) = J) : e ∣ J.card := by
  have hstep : ∀ x ∈ J, (x + k) % (k * e) ∈ J := by
    intro x hx
    rw [← hshift]
    exact Finset.mem_image_of_mem (fun i => (i + k) % (k * e)) hx
  have hiter : ∀ m : ℕ, ∀ x ∈ J, (x + m * k) % (k * e) ∈ J := by
    intro m
    induction m with
    | zero =>
      intro x hx
      rw [zero_mul, add_zero, Nat.mod_eq_of_lt (hJ x hx)]
      exact hx
    | succ m ih =>
      intro x hx
      have h1 : (x + (m + 1) * k) % (k * e) = ((x + m * k) % (k * e) + k) % (k * e) := by
        rw [Nat.mod_add_mod, show x + (m + 1) * k = x + m * k + k by ring]
      rw [h1]
      exact hstep _ (ih x hx)
  have hup : ∀ r ∈ J, r < k → ∀ n : ℕ, n < e → r + k * n ∈ J := by
    intro r hr hrk n
    induction n with
    | zero =>
      intro _
      simpa using hr
    | succ n ih =>
      intro hn
      have hlt : r + k * n + k < k * e := by
        nlinarith [Nat.mul_le_mul_left k (show n + 2 ≤ e by omega)]
      have h1 := hstep _ (ih (by omega))
      rw [Nat.mod_eq_of_lt hlt] at h1
      rw [show r + k * n + k = r + k * (n + 1) by ring] at h1
      exact h1
  have hsurj : J = ((J.filter (fun r => r < k)) ×ˢ Finset.range e).image
      (fun p : ℕ × ℕ => p.1 + k * p.2) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_range,
      Prod.exists]
    constructor
    · intro hj
      have hjk : j < k * e := hJ j hj
      have hdm : j % k + k * (j / k) = j := Nat.mod_add_div j k
      have hn : j / k < e := Nat.div_lt_of_lt_mul hjk
      have hr : j % k < k := Nat.mod_lt j hk
      have hrJ : j % k ∈ J := by
        obtain ⟨m, hm⟩ : ∃ m, j / k + m = e := ⟨e - j / k, Nat.add_sub_of_le hn.le⟩
        have h3 : j + m * k = j % k + k * e := by
          rw [← hm, mul_add]
          linarith [hdm]
        have he : 0 < e := lt_of_le_of_lt (Nat.zero_le _) hn
        have hke : k ≤ k * e := Nat.le_mul_of_pos_right k he
        have hlt : j % k < k * e := lt_of_lt_of_le hr hke
        have h2 : (j + m * k) % (k * e) = j % k := by
          rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
        have h4 := hiter m j hj
        rw [h2] at h4
        exact h4
      exact ⟨j % k, j / k, ⟨⟨hrJ, hr⟩, hn⟩, hdm⟩
    · rintro ⟨r, n, ⟨⟨hrJ, hrk⟩, hne⟩, rfl⟩
      exact hup r hrJ hrk n hne
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + k * p.2)
      (↑((J.filter (fun r => r < k)) ×ˢ Finset.range e) : Set (ℕ × ℕ)) := by
    rintro ⟨r, n⟩ hp ⟨r', n'⟩ hp' hpq
    have hp1 : (r, n) ∈ (J.filter (fun r => r < k)) ×ˢ Finset.range e := Finset.mem_coe.mp hp
    have hp2 : (r', n') ∈ (J.filter (fun r => r < k)) ×ˢ Finset.range e :=
      Finset.mem_coe.mp hp'
    have hrk : r < k := (Finset.mem_filter.mp (Finset.mem_product.mp hp1).1).2
    have hrk' : r' < k := (Finset.mem_filter.mp (Finset.mem_product.mp hp2).1).2
    have hpq' : r + k * n = r' + k * n' := hpq
    have hmod : (r + k * n) % k = (r' + k * n') % k := by rw [hpq']
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrk,
      Nat.mod_eq_of_lt hrk'] at hmod
    subst hmod
    have hnn : n = n' := Nat.eq_of_mul_eq_mul_left hk (Nat.add_left_cancel hpq')
    subst hnn
    rfl
  have hcard : (((J.filter (fun r => r < k)) ×ˢ Finset.range e).image
      (fun p : ℕ × ℕ => p.1 + k * p.2)).card = (J.filter (fun r => r < k)).card * e := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range]
  rw [← hsurj] at hcard
  rw [hcard]
  exact dvd_mul_left e _

end CFSG.RankThree.GF2n.Stroth80.SL2Descent
