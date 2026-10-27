module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
import CFSG.ClassicalInvolution.Balance.Q27FuzzyModel
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyCanon
import CFSG.ClassicalInvolution.Balance.Q27Layers
import CFSG.ClassicalInvolution.Balance.Theorem5Models
import CFSG.ClassicalInvolution.Generic.InductionMain
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
import CFSG.ClassicalInvolution.RouteD.TypeAChain
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

variable {G : Type} [Group G]

section Helpers

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped commutatorElement

section Torus

variable {F : Type} [Field F] {N : ℕ}

private abbrev diagVal (t : Fin N → Fˣ) : Fin N ⊕ Fin N → F :=
  Sum.elim (fun m => (t m : F)) (fun m => (((t m)⁻¹ : Fˣ) : F))

private noncomputable abbrev diagSp (t : Fin N → Fˣ) : StatedSp N F :=
  Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t)

private theorem mat_diagSp (t : Fin N → Fˣ) :
    Symplectic.SpExtras.mat N F (diagSp t) = Matrix.diagonal (diagVal t) :=
  Symplectic.SpExtras.mat_equiv_diagonal t

private theorem diagVal_inl (t : Fin N → Fˣ) (m : Fin N) :
    diagVal t (Sum.inl m) = (t m : F) :=
  Sum.elim_inl _ _ _

private theorem diagVal_inr (t : Fin N → Fˣ) (m : Fin N) :
    diagVal t (Sum.inr m) = (((t m)⁻¹ : Fˣ) : F) :=
  Sum.elim_inr _ _ _

private theorem diagSp_mul (t t' : Fin N → Fˣ) : diagSp t * diagSp t' = diagSp (t * t') := by
  rw [diagSp, diagSp, diagSp, ← map_mul, ← map_mul, map_mul]

private theorem diagSp_one : diagSp (1 : Fin N → Fˣ) = 1 := by
  rw [diagSp, map_one, map_one]

private theorem diagSp_inv (t : Fin N → Fˣ) : (diagSp t)⁻¹ = diagSp t⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [diagSp_mul, mul_inv_cancel, diagSp_one])

private theorem diagVal_inv (t : Fin N → Fˣ) (x : Fin N ⊕ Fin N) :
    diagVal t⁻¹ x = (diagVal t x)⁻¹ := by
  rcases x with m | m
  · rw [diagVal_inl, diagVal_inl, Pi.inv_apply, Units.val_inv_eq_inv_val]
  · rw [diagVal_inr, diagVal_inr, Pi.inv_apply, Units.val_inv_eq_inv_val]

private theorem mat_inv_diagSp (t : Fin N → Fˣ) :
    Symplectic.SpExtras.mat N F ((diagSp t)⁻¹) = Matrix.diagonal fun x => (diagVal t x)⁻¹ := by
  rw [diagSp_inv, mat_diagSp]
  exact congrArg Matrix.diagonal (funext fun x => diagVal_inv t x)

private theorem diagonal_mul_mul_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d d' : ι → F) (M : Matrix ι ι F) (r t : ι) :
    (Matrix.diagonal d * M * Matrix.diagonal d') r t = d r * M r t * d' t := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem mat_conj_diagSp (t : Fin N → Fˣ) (x : StatedSp N F) (r s : Fin N ⊕ Fin N) :
    Symplectic.SpExtras.mat N F (diagSp t * x * (diagSp t)⁻¹) r s =
      diagVal t r * Symplectic.SpExtras.mat N F x r s * (diagVal t s)⁻¹ := by
  rw [map_mul, map_mul, mat_diagSp, mat_inv_diagSp, diagonal_mul_mul_diagonal]

private theorem mat_longBlock_sl2Upper_one (m : Fin N) :
    Symplectic.SpExtras.mat N F
        (longBlock F N m (CFSG.LieType.Steinberg.sl2Upper (1 : F))) (Sum.inl m) (Sum.inr m) = 1 := by
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Upper,
    Symplectic.SpExtras.mat_elt]
  simp [Symplectic.SpExtras.E]

private theorem sq_coord_of_conj_eq {t t' : Fin N → Fˣ}
    (h : ∀ x : StatedSp N F, diagSp t * x * (diagSp t)⁻¹ = diagSp t' * x * (diagSp t')⁻¹)
    (m : Fin N) : t m ^ 2 = t' m ^ 2 := by
  have key : ∀ u : Fin N → Fˣ,
      Symplectic.SpExtras.mat N F (diagSp u *
        longBlock F N m (CFSG.LieType.Steinberg.sl2Upper (1 : F)) * (diagSp u)⁻¹)
        (Sum.inl m) (Sum.inr m) = (u m : F) * (u m : F) := by
    intro u
    rw [mat_conj_diagSp, mat_longBlock_sl2Upper_one, mul_one, diagVal_inl, diagVal_inr,
      Units.val_inv_eq_inv_val, inv_inv]
  have h' := congrFun (congrFun (congrArg (Symplectic.SpExtras.mat N F)
    (h (longBlock F N m (CFSG.LieType.Steinberg.sl2Upper (1 : F))))) (Sum.inl m)) (Sum.inr m)
  rw [key t, key t'] at h'
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_two, pow_two]
  exact h'





variable {F : Type} [Field F] {N : ℕ}

private theorem diagSp_comm_mul (t t' : Fin N → Fˣ) :
    Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t) *
      Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t') =
    Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t') *
      Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t) := by
  rw [diagSp_mul, diagSp_mul, mul_comm]

private abbrev longDiag (k : Fin N) (a : Fˣ) : Fin N ⊕ Fin N → F :=
  fun x => if x = Sum.inl k then (a : F) else if x = Sum.inr k then (((a⁻¹ : Fˣ)) : F) else 1

private theorem mat_longBlock_torus (k : Fin N) (a : Fˣ) :
    Symplectic.SpExtras.mat N F (longBlock F N k (CFSG.ClassicalInvolution.WeakCT.torusHom F a)) =
      Matrix.diagonal (longDiag k a) := by
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_longBlock,
    CFSG.ClassicalInvolution.WeakCT.coe_torusHom,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.blockMat_torusDiag]

private theorem longDiag_inl {k : Fin N} {a : Fˣ} {m : Fin N} (h : m = k) :
    longDiag k a (Sum.inl m) = (a : F) := by
  subst h; simp [longDiag]

private theorem longDiag_inr {k : Fin N} {a : Fˣ} {m : Fin N} (h : m = k) :
    longDiag k a (Sum.inr m) = (((a⁻¹ : Fˣ)) : F) := by
  subst h; simp [longDiag]

private theorem longDiag_of_notMem {k : Fin N} {a : Fˣ} {x : Fin N ⊕ Fin N}
    (h : x ∉ coords k) : longDiag k a x = 1 := by
  rcases x with m | m
  · have h1 : m ≠ k := fun hh => h (by simp [coords, hh])
    simp [longDiag, h1]
  · have h1 : m ≠ k := fun hh => h (by simp [coords, hh])
    simp [longDiag, h1]

private theorem longDiag_ne {k : Fin N} {a : Fˣ} (ha1 : (a : F) ≠ 1)
    (ha2 : (a : F) ≠ (((a⁻¹ : Fˣ)) : F)) {t : Fin N ⊕ Fin N} (ht : t ∈ coords k)
    {r : Fin N ⊕ Fin N} (hrt : r ≠ t) : longDiag k a t ≠ longDiag k a r := by
  rcases mem_coords.1 ht with rfl | rfl
  · by_cases hr : r ∈ coords k
    · rcases mem_coords.1 hr with h | h
      · exact absurd h hrt
      · subst h
        rw [longDiag_inl rfl, longDiag_inr rfl]
        exact ha2
    · rw [longDiag_inl rfl, longDiag_of_notMem hr]
      exact ha1
  · by_cases hr : r ∈ coords k
    · rcases mem_coords.1 hr with h | h
      · subst h
        rw [longDiag_inr rfl, longDiag_inl rfl]
        exact fun hh => ha2 hh.symm
      · exact absurd h hrt
    · rw [longDiag_inr rfl, longDiag_of_notMem hr]
      exact fun hh => ha1 (by rw [Units.val_inv_eq_inv_val] at hh; exact inv_eq_one.1 hh)

private theorem commute_longBlock_iff (k : Fin N) (a : Fˣ) (g : StatedSp N F) :
    Commute g (longBlock F N k (CFSG.ClassicalInvolution.WeakCT.torusHom F a)) ↔
      ∀ r s, Symplectic.SpExtras.mat N F g r s * longDiag k a s =
        longDiag k a r * Symplectic.SpExtras.mat N F g r s := by
  constructor
  · intro h r s
    have hh := congrFun (congrFun (congrArg (Symplectic.SpExtras.mat N F) h.eq) r) s
    rw [map_mul, map_mul, mat_longBlock_torus, Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    exact hh
  · intro h
    refine Symplectic.SpExtras.mat_injective ?_
    rw [map_mul, map_mul, mat_longBlock_torus]
    ext r s
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact h r s

private theorem column_zero_of_commute_longBlock {k : Fin N} {a : Fˣ} (ha1 : (a : F) ≠ 1)
    (ha2 : (a : F) ≠ (((a⁻¹ : Fˣ)) : F)) {s : StatedSp N F}
    (hs : Commute s (longBlock F N k (CFSG.ClassicalInvolution.WeakCT.torusHom F a)))
    {t : Fin N ⊕ Fin N} (ht : t ∈ coords k) {r : Fin N ⊕ Fin N} (hrt : r ≠ t) :
    Symplectic.SpExtras.mat N F s r t = 0 := by
  have h := (commute_longBlock_iff k a s).1 hs r t
  have hne := longDiag_ne ha1 ha2 ht hrt
  have hz : Symplectic.SpExtras.mat N F s r t * (longDiag k a t - longDiag k a r) = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 hz).resolve_right (sub_ne_zero.2 hne)

private theorem column_mul {u v : StatedSp N F} {t : Fin N ⊕ Fin N}
    (hv : ∀ x, x ≠ t → Symplectic.SpExtras.mat N F v x t = 0) (r : Fin N ⊕ Fin N) :
    Symplectic.SpExtras.mat N F (u * v) r t =
      Symplectic.SpExtras.mat N F u r t * Symplectic.SpExtras.mat N F v t t := by
  rw [map_mul, Matrix.mul_apply,
    Finset.sum_eq_single t (fun x _ hx => by rw [hv x hx, mul_zero]) (by simp)]

private theorem commutator_column_one {k : Fin N} {a : Fˣ} (ha1 : (a : F) ≠ 1)
    (ha2 : (a : F) ≠ (((a⁻¹ : Fˣ)) : F)) {s₁ s₂ : StatedSp N F}
    (h1 : Commute s₁ (longBlock F N k (CFSG.ClassicalInvolution.WeakCT.torusHom F a)))
    (h2 : Commute s₂ (longBlock F N k (CFSG.ClassicalInvolution.WeakCT.torusHom F a)))
    {y : Fin N ⊕ Fin N} (hy : y ∈ coords k) (r : Fin N ⊕ Fin N) :
    Symplectic.SpExtras.mat N F ⁅s₁, s₂⁆ r y =
      (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) F) r y := by
  have hz1 : ∀ x, x ≠ y → Symplectic.SpExtras.mat N F s₁ x y = 0 :=
    fun x hx => column_zero_of_commute_longBlock ha1 ha2 h1 hy hx
  have hz1' : ∀ x, x ≠ y → Symplectic.SpExtras.mat N F s₁⁻¹ x y = 0 :=
    fun x hx => column_zero_of_commute_longBlock ha1 ha2 (Commute.inv_left h1) hy hx
  have hz2 : ∀ x, x ≠ y → Symplectic.SpExtras.mat N F s₂ x y = 0 :=
    fun x hx => column_zero_of_commute_longBlock ha1 ha2 h2 hy hx
  have hz2' : ∀ x, x ≠ y → Symplectic.SpExtras.mat N F s₂⁻¹ x y = 0 :=
    fun x hx => column_zero_of_commute_longBlock ha1 ha2 (Commute.inv_left h2) hy hx
  have hd1 : Symplectic.SpExtras.mat N F s₁ y y * Symplectic.SpExtras.mat N F s₁⁻¹ y y = 1 := by
    have := column_mul (u := s₁) (v := s₁⁻¹) hz1' y
    rw [mul_inv_cancel, map_one, Matrix.one_apply_eq] at this
    exact this.symm
  have hd2 : Symplectic.SpExtras.mat N F s₂ y y * Symplectic.SpExtras.mat N F s₂⁻¹ y y = 1 := by
    have := column_mul (u := s₂) (v := s₂⁻¹) hz2' y
    rw [mul_inv_cancel, map_one, Matrix.one_apply_eq] at this
    exact this.symm
  rw [commutatorElement_def,
    column_mul (u := s₁ * s₂ * s₁⁻¹) (v := s₂⁻¹) hz2',
    column_mul (u := s₁ * s₂) (v := s₁⁻¹) hz1',
    column_mul (u := s₁) (v := s₂) hz2]
  by_cases hrt : r = y
  · rw [hrt, Matrix.one_apply_eq]
    calc Symplectic.SpExtras.mat N F s₁ y y * Symplectic.SpExtras.mat N F s₂ y y *
          Symplectic.SpExtras.mat N F s₁⁻¹ y y * Symplectic.SpExtras.mat N F s₂⁻¹ y y
        = (Symplectic.SpExtras.mat N F s₁ y y * Symplectic.SpExtras.mat N F s₁⁻¹ y y) *
          (Symplectic.SpExtras.mat N F s₂ y y * Symplectic.SpExtras.mat N F s₂⁻¹ y y) := by ring
      _ = 1 := by rw [hd1, hd2, mul_one]
  · simp only [hz1 r hrt, Matrix.one_apply_ne hrt, zero_mul]

private theorem exists_coords (x : Fin N ⊕ Fin N) : ∃ m, x ∈ coords m := by
  rcases x with m | m
  · exact ⟨m, inl_mem_coords m⟩
  · exact ⟨m, inr_mem_coords m⟩

private theorem exists_coords_of_notMem {j : Fin N} {t : Fin N ⊕ Fin N} (ht : t ∉ coords j) :
    ∃ m, m ≠ j ∧ t ∈ coords m := by
  obtain ⟨m, hm⟩ := exists_coords t
  refine ⟨m, ?_, hm⟩
  rintro rfl
  exact ht hm

private theorem exists_coords_of_notMem_union {i j : Fin N} {t : Fin N ⊕ Fin N}
    (ht : t ∉ coords i ∪ coords j) : ∃ m, m ≠ i ∧ m ≠ j ∧ t ∈ coords m := by
  obtain ⟨m, hm⟩ := exists_coords t
  refine ⟨m, ?_, ?_, hm⟩
  · rintro rfl; exact ht (Set.mem_union_left _ hm)
  · rintro rfl; exact ht (Set.mem_union_right _ hm)

private theorem commutator_mem_suppGroup_coords_of_commute {j : Fin N} {a : Fˣ}
    (ha1 : (a : F) ≠ 1) (ha2 : (a : F) ≠ (((a⁻¹ : Fˣ)) : F)) {s₁ s₂ : StatedSp N F}
    (h1 : ∀ m, m ≠ j → Commute s₁ (longBlock F N m (CFSG.ClassicalInvolution.WeakCT.torusHom F a)))
    (h2 : ∀ m, m ≠ j → Commute s₂ (longBlock F N m (CFSG.ClassicalInvolution.WeakCT.torusHom F a))) :
    ⁅s₁, s₂⁆ ∈ suppGroup (coords j) := by
  rw [mem_suppGroup_iff (parClosed_coords j)]
  intro t ht r
  obtain ⟨m, hmj, htm⟩ := exists_coords_of_notMem ht
  exact commutator_column_one ha1 ha2 (h1 m hmj) (h2 m hmj) htm r

private theorem commutator_mem_suppGroup_union_of_commute {i j : Fin N} {a : Fˣ}
    (ha1 : (a : F) ≠ 1) (ha2 : (a : F) ≠ (((a⁻¹ : Fˣ)) : F)) {s₁ s₂ : StatedSp N F}
    (h1 : ∀ m, m ≠ i → m ≠ j →
      Commute s₁ (longBlock F N m (CFSG.ClassicalInvolution.WeakCT.torusHom F a)))
    (h2 : ∀ m, m ≠ i → m ≠ j →
      Commute s₂ (longBlock F N m (CFSG.ClassicalInvolution.WeakCT.torusHom F a))) :
    ⁅s₁, s₂⁆ ∈ suppGroup (coords i ∪ coords j) := by
  have hp : ParClosed (coords i ∪ coords j) := by
    intro x hx
    rcases hx with hx | hx
    · rcases mem_coords.1 hx with rfl | rfl
      · exact Set.mem_union_left _ (inr_mem_coords i)
      · exact Set.mem_union_left _ (inl_mem_coords i)
    · rcases mem_coords.1 hx with rfl | rfl
      · exact Set.mem_union_right _ (inr_mem_coords j)
      · exact Set.mem_union_right _ (inl_mem_coords j)
  rw [mem_suppGroup_iff hp]
  intro t ht r
  obtain ⟨m, hmi, hmj, htm⟩ := exists_coords_of_notMem_union ht
  exact commutator_column_one ha1 ha2 (h1 m hmi hmj) (h2 m hmi hmj) htm r




private theorem diagVal_inl_eq_one {t : Fin N → Fˣ} {m : Fin N} (h : t m = 1) :
    diagVal t (Sum.inl m) = 1 := by
  rw [diagVal_inl, h, Units.val_one]

private theorem diagVal_inr_eq_one {t : Fin N → Fˣ} {m : Fin N} (h : t m = 1) :
    diagVal t (Sum.inr m) = 1 := by
  rw [diagVal_inr, h]
  simp

private theorem isSupp_compl_diagSp {t : Fin N → Fˣ} {S : Set (Fin N ⊕ Fin N)}
    (h : ∀ x ∈ S, diagVal t x = 1) : IsSupp Sᶜ (Symplectic.SpExtras.mat N F (diagSp t)) := by
  intro r s hrs
  by_cases hrs' : r = s
  · subst hrs'
    rw [mat_diagSp, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    by_contra hmem
    exact hrs ⟨fun hrS => hmem (h r hrS), fun hrS => hmem (h r hrS)⟩
  · rw [mat_diagSp, Matrix.diagonal_apply_ne _ hrs', Matrix.one_apply_ne hrs']

private theorem commute_diagSp_longBlock {t : Fin N → Fˣ} {j : Fin N} (ht : t j = 1)
    (A : SL(2, F)) :
    Commute (Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t))
      (longBlock F N j A) := by
  have hsupp : Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t) ∈
      suppGroup (coords j)ᶜ :=
    isSupp_compl_diagSp (fun x hx => by
      rcases mem_coords.1 hx with rfl | rfl
      · exact diagVal_inl_eq_one ht
      · exact diagVal_inr_eq_one ht)
  have hlong : longBlock F N j A ∈ suppGroup (coords j) := isSupp_longBlock j A
  exact (commute_suppGroup_compl hlong hsupp).symm

private theorem diagSp_eq_longBlock (k : Fin N) (a : Fˣ) :
    Symplectic.equivStatedSp N F
        (TauCeti.GLSymplecticFin.diagonal (fun m => if m = k then a else 1)) =
      longBlock F N k (CFSG.ClassicalInvolution.WeakCT.torusHom F a) := by
  refine Symplectic.SpExtras.mat_injective ?_
  rw [mat_diagSp, mat_longBlock_torus]
  congr 1
  funext x
  rcases x with m | m
  · rw [diagVal_inl]
    by_cases h : m = k
    · subst h; simp [longDiag]
    · simp [longDiag, h, Sum.inl.injEq]
  · rw [diagVal_inr]
    by_cases h : m = k
    · subst h; simp [longDiag]
    · simp [longDiag, h, Sum.inr.injEq]

private theorem blockMat_diag2 {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ} (hpq : p ≠ q)
    (x y : F) :
    CFSG.LieType.Steinberg.Sp.blockMat p q !![x, 0; 0, y] =
      Matrix.diagonal (fun z => if z = p then x else if z = q then y else 1) := by
  ext r s
  simp only [Matrix.diagonal_apply, CFSG.LieType.Steinberg.Sp.blockMat, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply]
  by_cases hrs : r = s
  · subst hrs
    by_cases hp : r = p <;> by_cases hq : r = q <;> simp_all
  · by_cases hp : r = p <;> by_cases hq : r = q <;> by_cases hp2 : s = p <;>
      by_cases hq2 : s = q <;> simp_all

private theorem diagSp_eq_planeTorusElt {i j : Fin N} (hij : i ≠ j) (a b : Fˣ) :
    Symplectic.equivStatedSp N F
        (TauCeti.GLSymplecticFin.diagonal
          (fun m => if m = i then a else if m = j then b else 1)) =
      planeTorusElt F i j a b := by
  refine Symplectic.SpExtras.mat_injective ?_
  rw [mat_diagSp, mat_planeTorusElt hij]
  congr 1
  funext x
  rcases x with m | m
  · rw [diagVal_inl, planeTorusDiag]
    by_cases h : m = i
    · subst h; simp
    · by_cases h2 : m = j
      · subst h2; simp [h]
      · simp [h, h2, Sum.inl.injEq]
  · rw [diagVal_inr, planeTorusDiag]
    by_cases h : m = i
    · subst h; simp
    · by_cases h2 : m = j
      · subst h2; simp [h]
      · simp [h, h2, Sum.inr.injEq]

private theorem diagSp_eq_shortBlock {i j : Fin N} (hij : i ≠ j) (a : Fˣ) :
    Symplectic.equivStatedSp N F
        (TauCeti.GLSymplecticFin.diagonal
          (fun m => if m = i then a else if m = j then a⁻¹ else 1)) =
      shortBlock F hij (CFSG.ClassicalInvolution.WeakCT.torusHom F a) := by
  refine Symplectic.SpExtras.mat_injective ?_
  rw [mat_diagSp, CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_shortBlock,
    CFSG.ClassicalInvolution.WeakCT.coe_torusHom,
    show ((CFSG.ClassicalInvolution.WeakCT.torusHom F a)⁻¹ : SL(2, F)) =
      CFSG.ClassicalInvolution.WeakCT.torusHom F a⁻¹ from (map_inv _ _).symm,
    CFSG.ClassicalInvolution.WeakCT.coe_torusHom]
  ext r s
  rcases r with x | x <;> rcases s with y | y
  · rw [Matrix.fromBlocks_apply₁₁, blockMat_diag2 hij (a : F) ((a⁻¹ : Fˣ) : F),
      Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy
      rw [diagVal_inl]
      simp only [apply_ite Units.val]
      by_cases h1 : x = i <;> by_cases h2 : x = j <;> simp [h1, h2]
    · simp [hxy]
  · simp [Matrix.fromBlocks_apply₁₂]
  · simp [Matrix.fromBlocks_apply₂₁]
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
      blockMat_diag2 hij ((a⁻¹ : Fˣ) : F) ((((a⁻¹)⁻¹ : Fˣ)) : F),
      Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy
      rw [diagVal_inr]
      simp only [apply_ite Units.val, apply_ite (Inv.inv : Fˣ → Fˣ)]
      by_cases h1 : x = i <;> by_cases h2 : x = j <;> simp [h1, h2]
    · simp [hxy, Ne.symm hxy]

private theorem isSupp_union_coords {i j : Fin N} : ParClosed (coords i ∪ coords j) := by
  intro x hx
  rcases hx with hx | hx
  · rcases mem_coords.1 hx with rfl | rfl
    · exact Set.mem_union_left _ (inr_mem_coords i)
    · exact Set.mem_union_left _ (inl_mem_coords i)
  · rcases mem_coords.1 hx with rfl | rfl
    · exact Set.mem_union_right _ (inr_mem_coords j)
    · exact Set.mem_union_right _ (inl_mem_coords j)

private theorem commute_diagSp_shortBlock {t : Fin N → Fˣ} {i j : Fin N} (hij : i ≠ j)
    (ht : t i = t j) (A : SL(2, F)) :
    Commute (Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t))
      (shortBlock F hij A) := by
  let t' : Fin N → Fˣ := fun m => if m = i ∨ m = j then t i else 1
  let t'' : Fin N → Fˣ := fun m => if m = i ∨ m = j then 1 else t m
  have h1 : t = t' * t'' := by
    funext m
    show t m = (if m = i ∨ m = j then t i else 1) * (if m = i ∨ m = j then 1 else t m)
    by_cases h : m = i ∨ m = j
    · rw [if_pos h, if_pos h, mul_one]
      rcases h with rfl | rfl
      · rfl
      · exact ht.symm
    · rw [if_neg h, if_neg h, one_mul]
  have h2 : t' = fun m => if m = i then t i else if m = j then t i else 1 := by
    funext m
    by_cases h : m = i <;> by_cases h2 : m = j <;> simp [t', h, h2]
  have hsupp : Symplectic.equivStatedSp N F
      (TauCeti.GLSymplecticFin.diagonal t'') ∈ suppGroup (coords i ∪ coords j)ᶜ :=
    isSupp_compl_diagSp (fun x hx => by
      rcases hx with hx | hx
      · rcases mem_coords.1 hx with rfl | rfl
        · exact diagVal_inl_eq_one (by simp [t''])
        · exact diagVal_inr_eq_one (by simp [t''])
      · rcases mem_coords.1 hx with rfl | rfl
        · exact diagVal_inl_eq_one (by simp [t''])
        · exact diagVal_inr_eq_one (by simp [t'']))
  have hshort : shortBlock F hij A ∈ suppGroup (coords i ∪ coords j) :=
    isSupp_shortBlock hij A
  have hcomm2 : Commute (Symplectic.equivStatedSp N F
      (TauCeti.GLSymplecticFin.diagonal t'')) (shortBlock F hij A) :=
    (commute_suppGroup_compl hshort hsupp).symm
  have hcomm1 : Commute (Symplectic.equivStatedSp N F
      (TauCeti.GLSymplecticFin.diagonal t')) (shortBlock F hij A) := by
    rw [h2, diagSp_eq_planeTorusElt hij (t i) (t i)]
    exact (commute_shortBlock_planeTorusElt hij (t i) A).symm
  rw [h1, show Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal (t' * t'')) =
      Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t') *
        Symplectic.equivStatedSp N F (TauCeti.GLSymplecticFin.diagonal t'') from
      (diagSp_mul t' t'').symm]
  exact hcomm1.mul_left hcomm2


section KFrame

variable {p n r f : ℕ} [Fact p.Prime] {Bs K : Subgroup G} {y : G}
variable {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
variable {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
variable {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}

private theorem ggSecFiveBPermSpKTorus_eq_diagSp (b : ↥Bs) :
    CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b =
      diagSp (fun m => χ (eta b (π m.succ))) := rfl

private theorem frame_conj_sq (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) {b : ↥Bs}
    {t' : Fin (r + 1) → (GaloisField 2 f)ˣ}
    (h : ∀ s, (b : G) * κ s * (b : G)⁻¹ = κ (diagSp t' * s * (diagSp t')⁻¹))
    (m : Fin (r + 1)) :
    (χ (eta b (π m.succ))) ^ 2 = t' m ^ 2 := by
  refine sq_coord_of_conj_eq (t := fun m => χ (eta b (π m.succ))) (t' := t') (fun s => ?_) m
  rw [show diagSp (fun m => χ (eta b (π m.succ))) =
      CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b from
    (ggSecFiveBPermSpKTorus_eq_diagSp b).symm]
  refine hF.1 ?_
  rw [← hF.2.2.2 b s]
  exact h s

private theorem eta_eq_of_frame (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) {b : ↥Bs}
    {t' : Fin (r + 1) → (GaloisField 2 f)ˣ} {v : Fin (r + 1) → Multiplicative (ZMod p)}
    (hp2 : p ≠ 2) (hv : ∀ m, t' m = χ (v m))
    (h : ∀ s, (b : G) * κ s * (b : G)⁻¹ = κ (diagSp t' * s * (diagSp t')⁻¹))
    (m : Fin (r + 1)) : eta b (π m.succ) = v m := by
  refine ggSecFiveBChi_sq_inj hp2 hF.2.2.1 ?_
  rw [frame_conj_sq hF h m, hv m]


private theorem diagSp_pow (t : Fin (r + 1) → (GaloisField 2 f)ˣ) (k : ℕ) :
    (diagSp t) ^ k = diagSp (t ^ k) := by
  induction k with
  | zero => simp [diagSp_one]
  | succ k ih => rw [pow_succ, ih, pow_succ, diagSp_mul]

private theorem eta_eq_one_of_centralizes (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) {b : ↥Bs}
    (h : ∀ s : StatedSp (r + 1) (GaloisField 2 f), (b : G) * κ s * (b : G)⁻¹ = κ s)
    (m : Fin (r + 1)) : eta b (π m.succ) = 1 := by
  refine eta_eq_of_frame hF (t' := fun _ => (1 : (GaloisField 2 f)ˣ)) (v := fun _ => 1) hp2
    (fun m => (map_one χ).symm) ?_ m
  intro s
  rw [h s]
  have h1 : (fun _ : Fin (r + 1) => (1 : (GaloisField 2 f)ˣ)) = 1 := rfl
  rw [h1, diagSp_one, one_mul, inv_one, mul_one]

private theorem eta_eq_one_of_centralizes' (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) {b : ↥Bs}
    (h : ∀ s : StatedSp (r + 1) (GaloisField 2 f), Commute (b : G) (κ s))
    (a : Fin (r + 1)) : eta b (π a.succ) = 1 :=
  eta_eq_one_of_centralizes hF hp2 (fun s => by
    have := (h s).eq
    rw [this]
    group) a

private theorem mem_ggBsCoordEq_of_eta_one {b : ↥Bs} (h : ∀ m, eta b m = 1) (i j : Fin n) :
    (b : G) ∈ ggBsCoordEq Bs eta i j :=
  coe_mem_ggBsCoordEq.2 (by rw [h i, h j])

private theorem kappa_diagSp_mem_Bs (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {t_L : Fin (r + 1) → (GaloisField 2 f)ˣ} (hpow : t_L ^ p = 1) :
    κ (diagSp t_L) ∈ Bs := by
  have hcen : κ (diagSp t_L) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hcomm : Commute (diagSp t_L)
        (CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ ⟨b, hb⟩) := by
      rw [ggSecFiveBPermSpKTorus_eq_diagSp]
      exact diagSp_comm_mul t_L _
    have hb' : (b : G) * κ (diagSp t_L) * (b : G)⁻¹ = κ (diagSp t_L) := by
      rw [hF.2.2.2 ⟨b, hb⟩ (diagSp t_L)]
      congr 1
      rw [← hcomm.eq]
      group
    calc (b : G) * κ (diagSp t_L) = ((b : G) * κ (diagSp t_L) * (b : G)⁻¹) * b := by group
      _ = κ (diagSp t_L) * b := by rw [hb']
  refine hBs _ hcen ?_
  rw [← map_pow, diagSp_pow, hpow, diagSp_one, map_one]

private theorem commute_torus_of_mem_centralizer (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    {H : Subgroup G} {g : G} {s : StatedSp (r + 1) (GaloisField 2 f)}
    (hg : g = κ s) (hgc : g ∈ Subgroup.centralizer (H : Set G)) {b : ↥Bs}
    (hb : (b : G) ∈ H) : Commute s (CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b) := by
  have _ : Nat.Prime p := Fact.out
  have h1 : (b : G) * g * (b : G)⁻¹ = g := by
    rw [Subgroup.mem_centralizer_iff.mp hgc (b : G) hb]
    group
  rw [hg] at h1
  have h2 : CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b * s *
      (CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b)⁻¹ = s := by
    apply hF.1
    rw [← hF.2.2.2 b s]
    exact h1
  show s * CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b =
    CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b * s
  have h3 : CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b * s =
      s * CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b := by
    rw [show CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b * s =
      (CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b * s *
        (CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b)⁻¹) *
        CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b from by group, h2]
  exact h3.symm


private theorem longBlock_torus_eq_diagSp (d : Fin (r + 1)) :
    longBlock (GaloisField 2 f) (r + 1) d
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ))) =
      diagSp (fun m => if m = d then ggSecFiveBZeta (χ := χ) else 1) :=
  (diagSp_eq_longBlock d (ggSecFiveBZeta (χ := χ))).symm

private theorem fun_single_pow (d : Fin (r + 1)) :
    (fun m : Fin (r + 1) => if m = d then ggSecFiveBZeta (χ := χ) else 1) ^ p = 1 := by
  funext m
  rw [Pi.pow_apply]
  by_cases h : m = d <;> simp [h, ggSecFiveBZeta_pow_p (χ := χ)]

private theorem eta_of_kappa_diagSp (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) {t_L : Fin (r + 1) → (GaloisField 2 f)ˣ}
    {v : Fin (r + 1) → Multiplicative (ZMod p)} (hv : ∀ m, t_L m = χ (v m))
    (hmem : κ (diagSp t_L) ∈ Bs) (m : Fin (r + 1)) :
    eta ⟨κ (diagSp t_L), hmem⟩ (π m.succ) = v m := by
  refine eta_eq_of_frame hF (b := ⟨κ (diagSp t_L), hmem⟩) (t' := t_L) (v := v) hp2 hv ?_ m
  intro s
  show κ (diagSp t_L) * κ s * (κ (diagSp t_L))⁻¹ = κ (diagSp t_L * s * (diagSp t_L)⁻¹)
  rw [← map_inv, ← map_mul, ← map_mul]


private theorem eta_of_kappa_diagSp' (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) {t_L : Fin (r + 1) → (GaloisField 2 f)ˣ}
    {v : Fin (r + 1) → Multiplicative (ZMod p)} (hv : ∀ m, t_L m = χ (v m))
    {b : ↥Bs} (hb : (b : G) = κ (diagSp t_L)) (m : Fin (r + 1)) :
    eta b (π m.succ) = v m := by
  have hbb : b = ⟨κ (diagSp t_L), hb ▸ b.2⟩ := Subtype.ext hb
  rw [hbb]
  exact eta_of_kappa_diagSp hF hp2 hv (hb ▸ b.2) m

private theorem exists_plane_ne {j : Fin (r + 1)} (hr : 2 ≤ r) :
    ∃ d : Fin (r + 1), d ≠ j := by
  have h2 : 1 < Fintype.card (Fin (r + 1)) := by simp [Fintype.card_fin]; omega
  exact Fintype.exists_ne_of_one_lt_card h2 j

private theorem hgen_short (hp2 : p ≠ 2)
    {t : G} (htB : t ∈ Bs) {i j : Fin (r + 1)} (hij : i ≠ j)
    (hηt : ∀ m, eta ⟨t, htB⟩ (π m.succ) =
      if m = i then Multiplicative.ofAdd 1 else if m = j then Multiplicative.ofAdd (-1) else 1) :
    ∀ e ∈ Bs, ∃ h ∈ ggBsCoordEq Bs eta (π i.succ) (π j.succ), ∃ k : ℤ, e = h * t ^ k := by
  intro e he
  let kk : ZMod p := (Multiplicative.toAdd (eta ⟨e, he⟩ (π i.succ)) -
    Multiplicative.toAdd (eta ⟨e, he⟩ (π j.succ))) / 2
  refine ⟨e * (t ^ kk.val)⁻¹, ?_, ((kk.val : ℕ) : ℤ), ?_⟩
  · rw [mem_ggBsCoordEq]
    have hmem : e * (t ^ kk.val)⁻¹ ∈ Bs :=
      Subgroup.mul_mem Bs he (Subgroup.inv_mem Bs (Subgroup.pow_mem Bs htB kk.val))
    refine ⟨hmem, ?_⟩
    have h1 : eta ⟨e * (t ^ kk.val)⁻¹, hmem⟩ =
        eta ⟨e, he⟩ * ((eta ⟨t, htB⟩) ^ kk.val)⁻¹ :=
      ggSecFiveBEta_subtype_mul_inv_pow he htB _
    have hji : j ≠ i := hij.symm
    have e_i : (eta ⟨t, htB⟩) (π i.succ) = Multiplicative.ofAdd 1 := by
      rw [hηt i, if_pos rfl]
    have e_j : (eta ⟨t, htB⟩) (π j.succ) = Multiplicative.ofAdd (-1) := by
      rw [hηt j, if_neg hji, if_pos rfl]
    have hk : (↑kk.val : ZMod p) = kk := ZMod.natCast_zmod_val kk
    have h4 : (2 : ZMod p) * kk = Multiplicative.toAdd (eta ⟨e, he⟩ (π i.succ)) -
        Multiplicative.toAdd (eta ⟨e, he⟩ (π j.succ)) := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ (ggSecFiveBTwo_ne_zero_zmod hp2)
    have key : (eta ⟨e, he⟩ * ((eta ⟨t, htB⟩) ^ kk.val)⁻¹) (π i.succ) =
        (eta ⟨e, he⟩ * ((eta ⟨t, htB⟩) ^ kk.val)⁻¹) (π j.succ) := by
      rw [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply,
        e_i, e_j]
      refine Multiplicative.toAdd.injective ?_
      rw [ggSecFiveBToAdd_mul, ggSecFiveBToAdd_mul, toAdd_inv, toAdd_inv, ggSecFiveBToAdd_pow,
        ggSecFiveBToAdd_pow]
      have hk1 : (kk.val : ℕ) • (1 : ZMod p) = (kk.val : ZMod p) := by
        rw [nsmul_eq_mul, mul_one]
      have hk2 : (kk.val : ℕ) • (-1 : ZMod p) = -((kk.val : ZMod p)) := by
        rw [nsmul_eq_mul, show ((kk.val : ℕ) : ZMod p) * (-1) =
          -(((kk.val : ℕ) : ZMod p) * 1) from mul_neg _ _, mul_one]
      rw [hk1, hk2, hk]
      have h7 : kk + kk = Multiplicative.toAdd (eta ⟨e, he⟩ (π i.succ)) -
          Multiplicative.toAdd (eta ⟨e, he⟩ (π j.succ)) := by rw [← h4]; ring
      have h8 : Multiplicative.toAdd (eta ⟨e, he⟩ (π i.succ)) =
          Multiplicative.toAdd (eta ⟨e, he⟩ (π j.succ)) + (kk + kk) := by rw [h7]; ring
      rw [h8]
      abel
    calc eta ⟨e * (t ^ kk.val)⁻¹, hmem⟩ (π i.succ)
        = (eta ⟨e, he⟩ * ((eta ⟨t, htB⟩) ^ kk.val)⁻¹) (π i.succ) := by rw [h1]
      _ = (eta ⟨e, he⟩ * ((eta ⟨t, htB⟩) ^ kk.val)⁻¹) (π j.succ) := key
      _ = eta ⟨e * (t ^ kk.val)⁻¹, hmem⟩ (π j.succ) := by rw [h1]
  · rw [zpow_natCast, mul_assoc, inv_mul_cancel, mul_one]

private theorem longBlock_torus_ne_one {d : Fin (r + 1)} {ζ : (GaloisField 2 f)ˣ}
    (h : (ζ : GaloisField 2 f) ≠ 1) :
    longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) ζ) ≠ 1 :=
  fun hh => ggSecFiveBTorusHom_ne_one h (longBlock_injective d (by rw [hh, map_one]))


private theorem kframe_normalizes [Finite G] (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hf : 2 ≤ f) {H : Subgroup G} {y : G} (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K)
    (hyH : y ∈ H) {d : Fin (r + 1)} {j : Fin (r + 1)} (hdj : d ≠ j)
    (hζF1 : ((ggSecFiveBZeta (χ := χ) : (GaloisField 2 f)ˣ) : GaloisField 2 f) ≠ 1)
    (hζFinv : ((ggSecFiveBZeta (χ := χ) : (GaloisField 2 f)ˣ) : GaloisField 2 f) ≠
      (((ggSecFiveBZeta (χ := χ))⁻¹ : (GaloisField 2 f)ˣ) : GaloisField 2 f))
    (hr'H : κ (longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈ H) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  set r' : G := κ (longBlock (GaloisField 2 f) (r + 1) d
    (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
      ggSecFiveBZeta (χ := χ)))) with hr'def
  set J : Subgroup G := (κ.comp (longBlock (GaloisField 2 f) (r + 1) d)).range with hJdef
  have hr'J : r' ∈ J := by rw [hr'def, hJdef]; exact ⟨_, rfl⟩
  have hJK : J ≤ K := by
    rw [hJdef, ← hF.2.1]
    rintro _ ⟨s, rfl⟩
    exact ⟨longBlock (GaloisField 2 f) (r + 1) d s, rfl⟩
  have hr'ne1 : r' ≠ 1 := by
    rw [hr'def]
    exact fun hh => longBlock_torus_ne_one hζF1 (hF.1 (by rw [hh, map_one]))
  have hr'pow : r' ^ p = 1 := by
    rw [hr'def]
    have hpow : (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f)
        (ggSecFiveBZeta (χ := χ))) ^ p = 1 := by
      rw [← map_pow, ggSecFiveBZeta_pow_p (χ := χ), map_one]
    rw [← map_pow, ← map_pow, hpow, map_one, map_one]
  have hne : J ≠ ⊥ := by
    intro hbot
    have hmem : r' ∈ J := hr'J
    rw [hbot] at hmem
    exact hr'ne1 (by simpa using hmem)
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := by
    rw [hJdef]
    exact CFSG.ClassicalInvolution.Balance.Q27.isQuasisimple_range_of_sl2
      (ggSecFiveBFour_le_card_galois hf) (κ.comp (longBlock (GaloisField 2 f) (r + 1) d)) hne
  have hpJ : p ∣ Nat.card ↥J := by
    have h1 : orderOf r' = p := orderOf_eq_prime hr'pow hr'ne1
    have h2 : orderOf r' ∣ Nat.card ↥J := Subgroup.orderOf_dvd_natCard J hr'J
    rwa [h1] at h2
  have hr'C : r' ∉ Subgroup.centralizer (J : Set G) := by
    intro hmem
    have hcomm : κ (longBlock (GaloisField 2 f) (r + 1) d
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.transvOne (GaloisField 2 f))) * r' =
        r' * κ (longBlock (GaloisField 2 f) (r + 1) d
          (CFSG.ClassicalInvolution.Models.SymplecticPairs.transvOne (GaloisField 2 f))) := by
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem _ (by rw [hJdef]; exact ⟨_, rfl⟩)
    rw [hr'def] at hcomm
    have hpe : CFSG.ClassicalInvolution.Models.SymplecticPairs.planeTorusElt (GaloisField 2 f) d j
        (ggSecFiveBZeta (χ := χ)) 1 = longBlock (GaloisField 2 f) (r + 1) d
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
            ggSecFiveBZeta (χ := χ))) := by
      simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.planeTorusElt]
    have hn : ¬ Commute (longBlock (GaloisField 2 f) (r + 1) d
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.transvOne (GaloisField 2 f)))
        (longBlock (GaloisField 2 f) (r + 1) d
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
            ggSecFiveBZeta (χ := χ)))) := by
      have h0 := CFSG.ClassicalInvolution.Models.SymplecticPairs.not_commute_longBlock_planeTorusElt
        (K := GaloisField 2 f) (n := r + 1) (i := d) (j := j) hdj hζFinv (1 : (GaloisField 2 f)ˣ)
      rwa [hpe] at h0
    have hh : (longBlock (GaloisField 2 f) (r + 1) d
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.transvOne (GaloisField 2 f))) *
        (longBlock (GaloisField 2 f) (r + 1) d
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) =
        (longBlock (GaloisField 2 f) (r + 1) d
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) *
        (longBlock (GaloisField 2 f) (r + 1) d
          (CFSG.ClassicalInvolution.Models.SymplecticPairs.transvOne (GaloisField 2 f))) := by
      apply hF.1
      rw [map_mul, map_mul]
      exact hcomm
    exact hn hh
  have hgy : g ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact Subgroup.mem_centralizer_iff.mp hg y hyH
  have hgr' : g * r' = r' * g :=
    (Subgroup.mem_centralizer_iff.mp hg r' hr'H).symm
  exact ggMem_normalizer_of_pComponent hK hJK hJq hpJ hr'J hr'C hgy hgr'


private theorem eta_of_longBlock_torus (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) {d : Fin (r + 1)} {b : ↥Bs}
    (hb : (b : G) = κ (longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))))
    (m : Fin (r + 1)) :
    eta b (π m.succ) = if m = d then Multiplicative.ofAdd 1 else 1 := by
  refine eta_of_kappa_diagSp' hF hp2 (t_L := fun m => if m = d then ggSecFiveBZeta (χ := χ) else 1)
    (v := fun m => if m = d then Multiplicative.ofAdd 1 else 1) (fun m => ?_) ?_ m
  · by_cases h : m = d <;> simp [h]
  · rw [hb, longBlock_torus_eq_diagSp]

private theorem c2_val_ne_one {F : Type} [Field F] {a : Fˣ}
    (ha : (a : F) ≠ ((a⁻¹ : Fˣ) : F)) : (a : F) ≠ 1 := by
  intro h
  apply ha
  have ha1 : a = 1 := Units.ext h
  rw [h, ha1, inv_one, Units.val_one]

private theorem c2_column_zero_of_commute_planeTorusElt {F : Type} [Field F] {N : ℕ}
    {i j u : Fin N} (hij : i ≠ j) (hu : u = i ∨ u = j) {a : Fˣ}
    (ha : (a : F) ≠ ((a⁻¹ : Fˣ) : F)) {g : StatedSp N F}
    (hg : Commute g (planeTorusElt F i j a a)) {x : Fin N ⊕ Fin N}
    (hxi : x ≠ Sum.inl i) (hxj : x ≠ Sum.inl j) :
    Symplectic.SpExtras.mat N F g x (Sum.inl u) = 0 := by
  have hD : planeTorusDiag i j a a (Sum.inl u) = (a : F) := by
    rw [planeTorusDiag_inl_same, if_pos hu]
  have hDx : planeTorusDiag i j a a x ≠ (a : F) := by
    rcases x with y | y
    · rw [planeTorusDiag_inl_same]
      by_cases h : y = i ∨ y = j
      · rcases h with h | h
        · rw [if_pos (Or.inl h)]
          exact (hxi (by rw [h])).elim
        · rw [if_pos (Or.inr h)]
          exact (hxj (by rw [h])).elim
      · rw [if_neg h]
        exact fun e => c2_val_ne_one ha e.symm
    · rw [planeTorusDiag_inr_same]
      by_cases h : y = i ∨ y = j
      · rw [if_pos h]
        exact fun e => ha e.symm
      · rw [if_neg h]
        exact fun e => c2_val_ne_one ha e.symm
  have h := (commute_planeTorusElt_iff hij a a g).1 hg x (Sum.inl u)
  rw [hD] at h
  have hz : Symplectic.SpExtras.mat N F g x (Sum.inl u) *
      ((a : F) - planeTorusDiag i j a a x) = 0 := by
    rw [mul_sub, h,
      mul_comm (Symplectic.SpExtras.mat N F g x (Sum.inl u)) (planeTorusDiag i j a a x),
      sub_self]
  exact (mul_eq_zero.1 hz).resolve_right (sub_ne_zero.2 (Ne.symm hDx))

private theorem c2_leviBlk2_mul_of_commute {F : Type} [Field F] {N : ℕ}
    {i j : Fin N} (hij : i ≠ j) {a : Fˣ}
    (ha : (a : F) ≠ ((a⁻¹ : Fˣ) : F)) {g h : StatedSp N F}
    (hh : Commute h (planeTorusElt F i j a a)) :
    leviBlk2 i j (g * h) = leviBlk2 i j g * leviBlk2 i j h := by
  have hzi : ∀ x, x ≠ Sum.inl i → x ≠ Sum.inl j →
      Symplectic.SpExtras.mat N F h x (Sum.inl i) = 0 :=
    fun x h1 h2 => c2_column_zero_of_commute_planeTorusElt hij (Or.inl rfl) ha hh h1 h2
  have hzj : ∀ x, x ≠ Sum.inl i → x ≠ Sum.inl j →
      Symplectic.SpExtras.mat N F h x (Sum.inl j) = 0 :=
    fun x h1 h2 => c2_column_zero_of_commute_planeTorusElt hij (Or.inr rfl) ha hh h1 h2
  have hcol : ∀ (r : Fin N ⊕ Fin N) (u : Fin N), (u = i ∨ u = j) →
      Symplectic.SpExtras.mat N F (g * h) r (Sum.inl u) =
        Symplectic.SpExtras.mat N F g r (Sum.inl i) *
            Symplectic.SpExtras.mat N F h (Sum.inl i) (Sum.inl u) +
          Symplectic.SpExtras.mat N F g r (Sum.inl j) *
            Symplectic.SpExtras.mat N F h (Sum.inl j) (Sum.inl u) := by
    intro r u hu
    have key : ∀ x, x ≠ Sum.inl i → x ≠ Sum.inl j →
        Symplectic.SpExtras.mat N F h x (Sum.inl u) = 0 := by
      intro x h1 h2
      rcases hu with h | h
      · rw [h]; exact hzi x h1 h2
      · rw [h]; exact hzj x h1 h2
    rw [map_mul, Matrix.mul_apply,
      Fintype.sum_eq_add (Sum.inl i) (Sum.inl j) (by simp [hij])
        (fun x hx => by rw [key x hx.1 hx.2, mul_zero])]
  have hii := hcol (Sum.inl i) i (Or.inl rfl)
  have hij2 := hcol (Sum.inl i) j (Or.inr rfl)
  have hji := hcol (Sum.inl j) i (Or.inl rfl)
  have hjj := hcol (Sum.inl j) j (Or.inr rfl)
  ext r s
  fin_cases r <;> fin_cases s <;> simp [leviBlk2, hii, hij2, hji, hjj]

private theorem c2_det_leviBlk2_commutator_of_commute {F : Type} [Field F] {N : ℕ}
    {i j : Fin N} (hij : i ≠ j) {a : Fˣ}
    (ha : (a : F) ≠ ((a⁻¹ : Fˣ) : F)) {g h : StatedSp N F}
    (hg : Commute g (planeTorusElt F i j a a)) (hh : Commute h (planeTorusElt F i j a a)) :
    (leviBlk2 i j ⁅g, h⁆).det = 1 := by
  have hinv : ∀ x : StatedSp N F, Commute x (planeTorusElt F i j a a) →
      (leviBlk2 i j x).det * (leviBlk2 i j x⁻¹).det = 1 := by
    intro x hx
    rw [← Matrix.det_mul, ← c2_leviBlk2_mul_of_commute hij ha hx.inv_left,
      mul_inv_cancel, leviBlk2_one hij, Matrix.det_one]
  have hgh : Commute (g * h) (planeTorusElt F i j a a) := hg.mul_left hh
  rw [commutatorElement_def,
    c2_leviBlk2_mul_of_commute hij ha hh.inv_left,
    c2_leviBlk2_mul_of_commute hij ha hg.inv_left,
    c2_leviBlk2_mul_of_commute hij ha hh,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  have hg' := hinv g hg
  have hh' := hinv h hh
  calc (leviBlk2 i j g).det * (leviBlk2 i j h).det * (leviBlk2 i j g⁻¹).det *
        (leviBlk2 i j h⁻¹).det
      = ((leviBlk2 i j g).det * (leviBlk2 i j g⁻¹).det) *
        ((leviBlk2 i j h).det * (leviBlk2 i j h⁻¹).det) := by ring
    _ = 1 := by rw [hg', hh', mul_one]

private theorem c2_commutator_commute_of_commute {F : Type} [Field F] {N : ℕ}
    {x g h : StatedSp N F} (hg : Commute g x) (hh : Commute h x) :
    Commute ⁅g, h⁆ x := by
  rw [commutatorElement_def]
  exact ((hg.mul_left hh).mul_left hg.inv_left).mul_left hh.inv_left

private noncomputable abbrev c2_um (π : Fin (r + 2) ≃ Fin n) (m : Fin (r + 1)) :
    Fin n → Multiplicative (ZMod p) :=
  Pi.mulSingle (π m.succ) (Multiplicative.ofAdd 1)

private noncomputable abbrev c2_hm (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (π : Fin (r + 2) ≃ Fin n) (m : Fin (r + 1)) : ↥Bs :=
  eta.symm (c2_um π m)

private noncomputable abbrev c2_uij (π : Fin (r + 2) ≃ Fin n) (i j : Fin (r + 1)) :
    Fin n → Multiplicative (ZMod p) :=
  Pi.mulSingle (π i.succ) (Multiplicative.ofAdd 1) *
    Pi.mulSingle (π j.succ) (Multiplicative.ofAdd 1)

private noncomputable abbrev c2_hij (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (π : Fin (r + 2) ≃ Fin n) (i j : Fin (r + 1)) : ↥Bs :=
  eta.symm (c2_uij π i j)

private noncomputable abbrev c2_tL (i j : Fin (r + 1)) : Fin (r + 1) → (GaloisField 2 f)ˣ :=
  fun m => if m = i then ggSecFiveBZeta (χ := χ) else if m = j then (
    ggSecFiveBZeta (χ := χ))⁻¹ else 1

private noncomputable abbrev c2_v (i j : Fin (r + 1)) : Fin (r + 1) → Multiplicative (ZMod p) :=
  fun m => if m = i then Multiplicative.ofAdd 1 else
    if m = j then Multiplicative.ofAdd (-1) else 1

private theorem c2_hm_mem {i j m : Fin (r + 1)} (hmi : m ≠ i) (hmj : m ≠ j) :
    ((c2_hm eta π m : ↥Bs) : G) ∈ ggBsCoordEq Bs eta (π i.succ) (π j.succ) := by
  refine (coe_mem_ggBsCoordEq (b := c2_hm eta π m)).2 ?_
  show eta (c2_hm eta π m) (π i.succ) = eta (c2_hm eta π m) (π j.succ)
  rw [show eta (c2_hm eta π m) = c2_um π m from MulEquiv.apply_symm_apply eta (c2_um π m)]
  have hπi : π i.succ ≠ π m.succ := fun h => hmi (Fin.succ_inj.mp (π.injective h)).symm
  have hπj : π j.succ ≠ π m.succ := fun h => hmj (Fin.succ_inj.mp (π.injective h)).symm
  simp only [c2_um, Pi.mulSingle_apply, hπi, hπj, if_false]

private theorem c2_hij_mem {i j : Fin (r + 1)} (hij : i ≠ j) :
    ((c2_hij eta π i j : ↥Bs) : G) ∈ ggBsCoordEq Bs eta (π i.succ) (π j.succ) := by
  refine (coe_mem_ggBsCoordEq (b := c2_hij eta π i j)).2 ?_
  show eta (c2_hij eta π i j) (π i.succ) = eta (c2_hij eta π i j) (π j.succ)
  rw [show eta (c2_hij eta π i j) = c2_uij π i j from MulEquiv.apply_symm_apply eta (c2_uij π i j)]
  have hπ : π i.succ ≠ π j.succ := fun h => hij (Fin.succ_inj.mp (π.injective h))
  simp only [c2_uij, Pi.mul_apply, Pi.mulSingle_apply, hπ, hπ.symm, if_true, if_false,
    mul_one, one_mul]

private theorem c2_tau_hm (m : Fin (r + 1)) :
    ggSecFiveBPermSpKTorus eta π χ (c2_hm eta π m) =
      longBlock (GaloisField 2 f) (r + 1) m
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ))) := by
  have hfun : (fun m' => χ (eta (c2_hm eta π m) (π m'.succ))) =
      fun m' => if m' = m then ggSecFiveBZeta (χ := χ) else 1 := by
    funext m'
    rw [show eta (c2_hm eta π m) = c2_um π m from MulEquiv.apply_symm_apply eta (c2_um π m)]
    show χ (c2_um π m (π m'.succ)) = (if m' = m then ggSecFiveBZeta (χ := χ) else 1)
    by_cases h : m' = m
    · rw [if_pos h, h]
      simp only [c2_um, Pi.mulSingle_apply, if_true, ggSecFiveBZeta]
    · have hπ : π m'.succ ≠ π m.succ := fun hh => h (Fin.succ_inj.mp (π.injective hh))
      rw [if_neg h]
      simp only [c2_um, Pi.mulSingle_apply, hπ, if_false, map_one]
  have h1 : ggSecFiveBPermSpKTorus eta π χ (c2_hm eta π m) =
      diagSp (fun m' => if m' = m then ggSecFiveBZeta (χ := χ) else 1) := by
    rw [ggSecFiveBPermSpKTorus_eq_diagSp]
    exact congrArg diagSp hfun
  exact h1.trans (diagSp_eq_longBlock m (ggSecFiveBZeta (χ := χ)))

private theorem c2_tau_hij {i j : Fin (r + 1)} (hij : i ≠ j) :
    ggSecFiveBPermSpKTorus eta π χ (c2_hij eta π i j) =
      planeTorusElt (GaloisField 2 f) i j (ggSecFiveBZeta (χ := χ)) (ggSecFiveBZeta (χ := χ)) := by
  have hfun : (fun m' => χ (eta (c2_hij eta π i j) (π m'.succ))) =
      fun m' => if m' = i then ggSecFiveBZeta (χ := χ) else if m' = j then
        ggSecFiveBZeta (χ := χ) else 1 := by
    funext m'
    rw [show eta (c2_hij eta π i j) = c2_uij π i j from
      MulEquiv.apply_symm_apply eta (c2_uij π i j)]
    show χ (c2_uij π i j (π m'.succ)) =
      (if m' = i then ggSecFiveBZeta (χ := χ) else if m' = j then ggSecFiveBZeta (χ := χ) else 1)
    have hπij : π i.succ ≠ π j.succ := fun h => hij (Fin.succ_inj.mp (π.injective h))
    have hπji : π j.succ ≠ π i.succ := hπij.symm
    by_cases hi : m' = i
    · rw [if_pos hi, hi]
      simp only [c2_uij, Pi.mul_apply, Pi.mulSingle_apply, hπij, if_true, if_false,
        mul_one, ggSecFiveBZeta]
    · by_cases hj : m' = j
      · rw [if_neg hi, if_pos hj, hj]
        simp only [c2_uij, Pi.mul_apply, Pi.mulSingle_apply, hπji, if_false, if_true,
          one_mul, ggSecFiveBZeta]
      · have hπi : π m'.succ ≠ π i.succ := fun h => hi (Fin.succ_inj.mp (π.injective h))
        have hπj : π m'.succ ≠ π j.succ := fun h => hj (Fin.succ_inj.mp (π.injective h))
        rw [if_neg hi, if_neg hj]
        simp only [c2_uij, Pi.mul_apply, Pi.mulSingle_apply, hπi, hπj, if_false,
          map_one, mul_one]
  have h1 : ggSecFiveBPermSpKTorus eta π χ (c2_hij eta π i j) =
      diagSp (fun m' => if m' = i then ggSecFiveBZeta (χ := χ) else
        if m' = j then ggSecFiveBZeta (χ := χ) else 1) := by
    rw [ggSecFiveBPermSpKTorus_eq_diagSp]
    exact congrArg diagSp hfun
  exact h1.trans (diagSp_eq_planeTorusElt hij (ggSecFiveBZeta (χ := χ)) (ggSecFiveBZeta (χ := χ)))

private theorem zeta_val_ne_one (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) :
    ((ggSecFiveBZeta (χ := χ) : (GaloisField 2 f)ˣ) : GaloisField 2 f) ≠ 1 :=
  fun h => ggSecFiveBZeta_ne_one hF.2.2.1 (Units.ext h)

private theorem zeta_val_ne_inv (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) :
    ((ggSecFiveBZeta (χ := χ) : (GaloisField 2 f)ˣ) : GaloisField 2 f) ≠
      (((ggSecFiveBZeta (χ := χ))⁻¹ : (GaloisField 2 f)ˣ) : GaloisField 2 f) :=
  fun h => ggSecFiveBZeta_ne_inv hF.2.2.1 hp2 (Units.ext h)

private theorem longBlock_torus_mem_Bs (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) (d : Fin (r + 1)) :
    κ (longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
        ggSecFiveBZeta (χ := χ)))) ∈ Bs := by
  have h := kappa_diagSp_mem_Bs hF hBs (t_L := fun m => if m = d then ggSecFiveBZeta (χ := χ)
    else 1)
    (fun_single_pow d)
  rw [longBlock_torus_eq_diagSp d]
  exact h

private theorem c2_tL_pow (i j : Fin (r + 1)) : c2_tL (χ := χ) i j ^ p = 1 := by
  funext m
  rw [Pi.pow_apply]
  show (if m = i then ggSecFiveBZeta (χ := χ) else if m = j then (ggSecFiveBZeta (χ := χ))⁻¹
    else 1) ^ p = 1
  by_cases hi : m = i
  · rw [if_pos hi, ggSecFiveBZeta_pow_p (χ := χ)]
  · by_cases hj : m = j
    · rw [if_neg hi, if_pos hj, inv_pow, ggSecFiveBZeta_pow_p, inv_one]
    · rw [if_neg hi, if_neg hj, one_pow]

private theorem c2_t_mem_Bs (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {i j : Fin (r + 1)} (hij : i ≠ j) :
    κ (shortBlock (GaloisField 2 f) hij
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
        ggSecFiveBZeta (χ := χ)))) ∈ Bs := by
  rw [← diagSp_eq_shortBlock hij (ggSecFiveBZeta (χ := χ))]
  exact kappa_diagSp_mem_Bs hF hBs (c2_tL_pow i j)

private theorem c2_eta_t (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (hp2 : p ≠ 2)
    {i j : Fin (r + 1)} (hij : i ≠ j) {b : ↥Bs}
    (hb : (b : G) = κ (shortBlock (GaloisField 2 f) hij
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))))
    (m : Fin (r + 1)) : eta b (π m.succ) = c2_v i j m := by
  have h1 : shortBlock (GaloisField 2 f) hij
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ))) =
      diagSp (c2_tL (χ := χ) i j) := (diagSp_eq_shortBlock hij (ggSecFiveBZeta (χ := χ))).symm
  refine eta_of_kappa_diagSp' hF hp2 (t_L := c2_tL (χ := χ) i j) (v := c2_v i j)
    (fun m => ?_) ?_ m
  · show c2_tL (χ := χ) i j m = χ (c2_v i j m)
    show (if m = i then ggSecFiveBZeta (χ := χ) else if m = j then (ggSecFiveBZeta (χ := χ))⁻¹
      else 1) =
      χ (if m = i then Multiplicative.ofAdd 1 else
        if m = j then Multiplicative.ofAdd (-1) else 1)
    by_cases hi : m = i
    · rw [if_pos hi, if_pos hi]
    · by_cases hj : m = j
      · rw [if_neg hi, if_pos hj, if_neg hi, if_pos hj, ofAdd_neg]
        exact (map_inv χ (Multiplicative.ofAdd 1)).symm
      · rw [if_neg hi, if_neg hj, if_neg hi, if_neg hj, map_one]
  · rw [hb]
    exact congrArg κ h1

private theorem c2_r'mem (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (hp2 : p ≠ 2)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {i j d : Fin (r + 1)} (hdi : d ≠ i) (hdj : d ≠ j) :
    κ (longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈
      ggBsCoordEq Bs eta (π i.succ) (π j.succ) := by
  have hr'B := longBlock_torus_mem_Bs hF hBs d
  have hcoord : ∀ m, eta (⟨κ (longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
        ggSecFiveBZeta (χ := χ)))), hr'B⟩ :
        ↥Bs) (π m.succ) = if m = d then Multiplicative.ofAdd 1 else 1 :=
    eta_of_longBlock_torus hF hp2 rfl
  exact (coe_mem_ggBsCoordEq (b := ⟨_, hr'B⟩)).2 (by
    rw [hcoord i, hcoord j, if_neg (fun h : i = d => hdi h.symm),
      if_neg (fun h : j = d => hdj h.symm)])

private theorem c2_y_mem (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (hp2 : p ≠ 2)
    (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K) (hyB : y ∈ Bs)
    {i j : Fin (r + 1)} :
    y ∈ ggBsCoordEq Bs eta (π i.succ) (π j.succ) := by
  have hcomm : ∀ s : StatedSp (r + 1) (GaloisField 2 f),
      Commute ((⟨y, hyB⟩ : ↥Bs) : G) (κ s) := by
    intro s
    have hsK : κ s ∈ K := by
      rw [← hF.2.1]
      exact ⟨s, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hK.1 hsK) y (by simp)
  exact (coe_mem_ggBsCoordEq (b := ⟨y, hyB⟩)).2 (by
    rw [eta_eq_one_of_centralizes' hF hp2 hcomm i,
      eta_eq_one_of_centralizes' hF hp2 hcomm j])

private theorem c2_hX [Finite G] (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (hp2 : p ≠ 2)
    (hf : 2 ≤ f) (hr : 2 ≤ r)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K)
    {i j : Fin (r + 1)} :
    Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  obtain ⟨d, hdi, hdj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < r + 1)
  have hζinv := zeta_val_ne_inv hF hp2
  have hζ1 := zeta_val_ne_one hF
  have hr'H : κ (longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈
      ggBsCoordEq Bs eta (π i.succ) (π j.succ) :=
    c2_r'mem hF hp2 hBs hdi hdj
  have hyH : y ∈ ggBsCoordEq Bs eta (π i.succ) (π j.succ) :=
    c2_y_mem hF hp2 hK hyB
  exact kframe_normalizes hF hf hK hyH hdj hζ1 hζinv hr'H

private theorem c2_hRC (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    {i j : Fin (r + 1)} (hij : i ≠ j) :
    (κ.comp (shortBlock (GaloisField 2 f) hij)).range ≤
      Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G) := by
  rintro _ ⟨A, rfl⟩
  change κ (shortBlock (GaloisField 2 f) hij A) ∈
    Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhBs : h ∈ Bs := ggBsCoordEq_le (π i.succ) (π j.succ) hh
  have hcoord : eta (⟨h, hhBs⟩ : ↥Bs) (π i.succ) = eta (⟨h, hhBs⟩ : ↥Bs) (π j.succ) :=
    (coe_mem_ggBsCoordEq (b := ⟨h, hhBs⟩)).1 hh
  have ht : (fun m => χ (eta (⟨h, hhBs⟩ : ↥Bs) (π m.succ))) i =
      (fun m => χ (eta (⟨h, hhBs⟩ : ↥Bs) (π m.succ))) j := by
    show χ (eta (⟨h, hhBs⟩ : ↥Bs) (π i.succ)) =
      χ (eta (⟨h, hhBs⟩ : ↥Bs) (π j.succ))
    rw [hcoord]
  set τ := ggSecFiveBPermSpKTorus eta π χ (⟨h, hhBs⟩ : ↥Bs) with hτ
  have hcommτ : Commute τ (shortBlock (GaloisField 2 f) hij A) := by
    rw [hτ, ggSecFiveBPermSpKTorus_eq_diagSp]
    exact commute_diagSp_shortBlock hij ht A
  have hframe : h * κ (shortBlock (GaloisField 2 f) hij A) * h⁻¹ =
      κ (shortBlock (GaloisField 2 f) hij A) := by
    have h1 := hF.2.2.2 (⟨h, hhBs⟩ : ↥Bs) (shortBlock (GaloisField 2 f) hij A)
    have h2 : τ * shortBlock (GaloisField 2 f) hij A * τ⁻¹ =
        shortBlock (GaloisField 2 f) hij A := by
      rw [hcommτ.eq]
      group
    rw [h1, h2]
  calc h * κ (shortBlock (GaloisField 2 f) hij A)
      = (h * κ (shortBlock (GaloisField 2 f) hij A) * h⁻¹) * h := by group
    _ = κ (shortBlock (GaloisField 2 f) hij A) * h := by rw [hframe]

private theorem c2_hRt (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (hp2 : p ≠ 2)
    {i j : Fin (r + 1)} (hij : i ≠ j) :
    (κ.comp (shortBlock (GaloisField 2 f) hij)).range ≤
      ⁅(κ.comp (shortBlock (GaloisField 2 f) hij)).range,
        Subgroup.zpowers (κ (shortBlock (GaloisField 2 f) hij
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
            ggSecFiveBZeta (χ := χ)))))⁆ :=
  ggRange_le_commutator_zpowers_torusHom (κ.comp (shortBlock (GaloisField 2 f) hij))
    (ggSecFiveBZeta_sq_ne_one (χ := χ) hp2 hF.2.2.1)

private theorem c2_commute_longBlock_of_mem_centralizer
    (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) {i j m : Fin (r + 1)}
    {g : G} {s : StatedSp (r + 1) (GaloisField 2 f)} (hg : g = κ s)
    (hgc : g ∈ Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G))
    (hmi : m ≠ i) (hmj : m ≠ j) :
    Commute s (longBlock (GaloisField 2 f) (r + 1) m
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) := by
  have hb : ((c2_hm eta π m : ↥Bs) : G) ∈ ggBsCoordEq Bs eta (π i.succ) (π j.succ) :=
    c2_hm_mem hmi hmj
  have hc := commute_torus_of_mem_centralizer hF hg hgc hb
  rwa [c2_tau_hm m] at hc

private theorem c2_commute_planeTorusElt_of_mem_centralizer
    (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) {i j : Fin (r + 1)} (hij : i ≠ j)
    {g : G} {s : StatedSp (r + 1) (GaloisField 2 f)} (hg : g = κ s)
    (hgc : g ∈ Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G)) :
    Commute s (planeTorusElt (GaloisField 2 f) i j (ggSecFiveBZeta (χ := χ)) (
      ggSecFiveBZeta (χ := χ))) := by
  have hb : ((c2_hij eta π i j : ↥Bs) : G) ∈ ggBsCoordEq Bs eta (π i.succ) (π j.succ) :=
    c2_hij_mem hij
  have hc := commute_torus_of_mem_centralizer hF hg hgc hb
  rwa [c2_tau_hij hij] at hc

private theorem c2_hDR (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (hp2 : p ≠ 2)
    {i j : Fin (r + 1)} (hij : i ≠ j) :
    ⁅K ⊓ Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G),
        K ⊓ Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G)⁆ ≤
      (κ.comp (shortBlock (GaloisField 2 f) hij)).range := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁K : g₁ ∈ κ.range := by rw [hF.2.1]; exact hg₁.1
  have hg₂K : g₂ ∈ κ.range := by rw [hF.2.1]; exact hg₂.1
  obtain ⟨s₁, rfl⟩ := hg₁K
  obtain ⟨s₂, rfl⟩ := hg₂K
  have hl₁ : ∀ m, m ≠ i → m ≠ j → Commute s₁
      (longBlock (GaloisField 2 f) (r + 1) m
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) :=
    fun m hmi hmj => c2_commute_longBlock_of_mem_centralizer hF rfl hg₁.2 hmi hmj
  have hl₂ : ∀ m, m ≠ i → m ≠ j → Commute s₂
      (longBlock (GaloisField 2 f) (r + 1) m
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) :=
    fun m hmi hmj => c2_commute_longBlock_of_mem_centralizer hF rfl hg₂.2 hmi hmj
  have hp₁ : Commute s₁ (planeTorusElt (GaloisField 2 f) i j
      (ggSecFiveBZeta (χ := χ)) (ggSecFiveBZeta (χ := χ))) :=
    c2_commute_planeTorusElt_of_mem_centralizer hF hij rfl hg₁.2
  have hp₂ : Commute s₂ (planeTorusElt (GaloisField 2 f) i j
      (ggSecFiveBZeta (χ := χ)) (ggSecFiveBZeta (χ := χ))) :=
    c2_commute_planeTorusElt_of_mem_centralizer hF hij rfl hg₂.2
  have hsupp : ⁅s₁, s₂⁆ ∈ suppGroup (coords i ∪ coords j) :=
    commutator_mem_suppGroup_union_of_commute (zeta_val_ne_one hF)
      (zeta_val_ne_inv hF hp2) hl₁ hl₂
  have hmem : ⁅s₁, s₂⁆ ∈ leviCent (GaloisField 2 f) i j (ggSecFiveBZeta (χ := χ)) :=
    mem_leviCent.2 ⟨hsupp, c2_commutator_commute_of_commute hp₁ hp₂⟩
  have hdet := c2_det_leviBlk2_commutator_of_commute hij (zeta_val_ne_inv hF hp2) hp₁ hp₂
  obtain ⟨A, hA⟩ := mem_range_shortBlock_of_det hij (zeta_val_ne_inv hF hp2) hmem hdet
  refine ⟨A, ?_⟩
  change κ (shortBlock (GaloisField 2 f) hij A) = ⁅κ s₁, κ s₂⁆
  rw [hA, map_commutatorElement]

private theorem c2_ht (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (hp2 : p ≠ 2)
    {i j : Fin (r + 1)} (hij : i ≠ j) :
    κ (shortBlock (GaloisField 2 f) hij
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈
      ⁅K ⊓ Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G),
        K ⊓ Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G)⁆ := by
  have hRK : (κ.comp (shortBlock (GaloisField 2 f) hij)).range ≤ K := by
    rw [← hF.2.1]
    rintro _ ⟨A, rfl⟩
    exact ⟨shortBlock (GaloisField 2 f) hij A, rfl⟩
  have hRle : (κ.comp (shortBlock (GaloisField 2 f) hij)).range ≤
      K ⊓ Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G) :=
    le_inf hRK (c2_hRC hF hij)
  have htR : κ (shortBlock (GaloisField 2 f) hij
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈
      (κ.comp (shortBlock (GaloisField 2 f) hij)).range := ⟨_, rfl⟩
  have h1 := (c2_hRt hF hp2 hij) htR
  exact (Subgroup.commutator_mono hRle (Subgroup.zpowers_le.mpr (hRle htR))) h1


private theorem c1_y_mem_ggBsCoordZero (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) (hyB : y ∈ Bs)
    (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K) (j : Fin (r + 1)) :
    y ∈ ggBsCoordZero Bs eta (π j.succ) := by
  have hyC : ∀ s : StatedSp (r + 1) (GaloisField 2 f), Commute y (κ s) := by
    intro s
    have hs : κ s ∈ K := by rw [← hF.2.1]; exact ⟨s, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hK.1 hs) y (Set.mem_singleton y)
  exact (coe_mem_ggBsCoordZero (b := ⟨y, hyB⟩)).mpr
    (eta_eq_one_of_centralizes' hF hp2 hyC j)

private theorem c1_longBlock_torus_mem_ggBsCoordZero (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) {d j : Fin (r + 1)}
    (hB : κ (longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈ Bs)
    (hjd : j ≠ d) :
    κ (longBlock (GaloisField 2 f) (r + 1) d
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈
      ggBsCoordZero Bs eta (π j.succ) := by
  rw [mem_ggBsCoordZero]
  refine ⟨hB, ?_⟩
  have h := eta_of_longBlock_torus hF hp2 (b := ⟨_, hB⟩) rfl j
  rw [if_neg hjd] at h
  exact h

private theorem c1_kframe_normalizes_zero [Finite G]
    (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (hp2 : p ≠ 2) (hf : 2 ≤ f) (hr : 2 ≤ r)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K)
    (j : Fin (r + 1)) :
    Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  obtain ⟨d, hdj⟩ := exists_plane_ne (j := j) hr
  have hdB := longBlock_torus_mem_Bs hF hBs d
  exact kframe_normalizes hF hf hK (c1_y_mem_ggBsCoordZero hF hp2 hyB hK j)
    hdj (zeta_val_ne_one hF) (zeta_val_ne_inv hF hp2)
    (c1_longBlock_torus_mem_ggBsCoordZero hF hp2 hdB hdj.symm)

private theorem c1_commute_of_mem_centralizer_zero (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    {j : Fin (r + 1)} {g : G}
    (hg : g ∈ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G))
    {s : StatedSp (r + 1) (GaloisField 2 f)} (hgs : g = κ s)
    {m : Fin (r + 1)} (hm : m ≠ j) :
    Commute s (longBlock (GaloisField 2 f) (r + 1) m
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) := by
  set b : ↥Bs := eta.symm (Pi.mulSingle (π m.succ) (Multiplicative.ofAdd 1)) with hbdef
  have hbH : (b : G) ∈ ggBsCoordZero Bs eta (π j.succ) := by
    rw [mem_ggBsCoordZero]
    refine ⟨b.2, ?_⟩
    rw [hbdef, MulEquiv.apply_symm_apply]
    exact Pi.mulSingle_eq_of_ne (by
      intro h
      exact hm (Fin.succ_inj.mp (π.injective h)).symm) _
  have hfun : (fun m' => χ (eta b (π m'.succ))) =
      (fun m' => if m' = m then ggSecFiveBZeta (χ := χ) else 1) := by
    funext m'
    rw [hbdef, MulEquiv.apply_symm_apply]
    by_cases h : m' = m
    · subst h
      rw [if_pos rfl, Pi.mulSingle_eq_same]
    · rw [if_neg h, Pi.mulSingle_eq_of_ne (by
        intro he
        exact h (Fin.succ_inj.mp (π.injective he))), map_one]
  have hτ : CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ b =
      longBlock (GaloisField 2 f) (r + 1) m
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ))) := by
    rw [ggSecFiveBPermSpKTorus_eq_diagSp, hfun]
    exact diagSp_eq_longBlock m (ggSecFiveBZeta (χ := χ))
  rw [← hτ]
  exact commute_torus_of_mem_centralizer hF hgs hg hbH

private theorem c1_range_le_centralizer_zero (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (j : Fin (r + 1)) :
    (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range ≤
      Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhB : h ∈ Bs := ggBsCoordZero_le (Bs := Bs) (eta := eta) (π j.succ) hh
  have hη : eta ⟨h, hhB⟩ (π j.succ) = 1 :=
    (coe_mem_ggBsCoordZero (b := ⟨h, hhB⟩)).mp hh
  have ht : (fun m => χ (eta ⟨h, hhB⟩ (π m.succ))) j = 1 := by
    show χ (eta ⟨h, hhB⟩ (π j.succ)) = 1
    rw [hη, map_one]
  have hcomm : Commute (CFSG.StandardType.ggSecFiveBPermSpKTorus eta π χ ⟨h, hhB⟩)
      ((longBlock (GaloisField 2 f) (r + 1) j) A) := by
    rw [ggSecFiveBPermSpKTorus_eq_diagSp]
    exact commute_diagSp_longBlock ht A
  have h1 : (h : G) * κ ((longBlock (GaloisField 2 f) (r + 1) j) A) * h⁻¹ =
      κ ((longBlock (GaloisField 2 f) (r + 1) j) A) := by
    rw [hF.2.2.2 ⟨h, hhB⟩ ((longBlock (GaloisField 2 f) (r + 1) j) A)]
    congr 1
    rw [hcomm.eq]
    group
  calc h * κ ((longBlock (GaloisField 2 f) (r + 1) j) A)
      = ((h : G) * κ ((longBlock (GaloisField 2 f) (r + 1) j) A) * h⁻¹) * h := by group
    _ = κ ((longBlock (GaloisField 2 f) (r + 1) j) A) * h := by rw [h1]

private theorem c1_range_le_commutator_zpowers (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) (j : Fin (r + 1)) :
    (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range ≤
      ⁅(κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range,
        Subgroup.zpowers (κ (longBlock (GaloisField 2 f) (r + 1) j
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
            ggSecFiveBZeta (χ := χ)))))⁆ :=
  ggRange_le_commutator_zpowers_torusHom (κ.comp (longBlock (GaloisField 2 f) (r + 1) j))
    (ggSecFiveBZeta_sq_ne_one (χ := χ) hp2 hF.2.2.1)

private theorem c1_t_mem_commutator_zero (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) (j : Fin (r + 1)) :
    κ (longBlock (GaloisField 2 f) (r + 1) j
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈
      ⁅K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G),
        K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G)⁆ := by
  have hRC := c1_range_le_centralizer_zero hF j
  have htR : κ (longBlock (GaloisField 2 f) (r + 1) j
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) ∈
      (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range :=
    ⟨CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)), rfl⟩
  have hRK : (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range ≤ K := by
    intro x hx
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← hF.2.1]
    exact ⟨(longBlock (GaloisField 2 f) (r + 1) j) s, rfl⟩
  have hRD : (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range ≤
      K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G) :=
    fun x hx => ⟨hRK hx, hRC hx⟩
  exact Subgroup.commutator_mono hRD (Subgroup.zpowers_le.mpr (hRD htR))
    (c1_range_le_commutator_zpowers hF hp2 j htR)

private theorem c1_commutator_le_range (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) (j : Fin (r + 1)) :
    ⁅K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G),
        K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G)⁆ ≤
      (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨s₁, rfl⟩ := MonoidHom.mem_range.mp (by rw [hF.2.1]; exact hg₁.1)
  obtain ⟨s₂, rfl⟩ := MonoidHom.mem_range.mp (by rw [hF.2.1]; exact hg₂.1)
  have h1 : ∀ m, m ≠ j → Commute s₁ (longBlock (GaloisField 2 f) (r + 1) m
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) :=
    fun m hm => c1_commute_of_mem_centralizer_zero hF hg₁.2 rfl hm
  have h2 : ∀ m, m ≠ j → Commute s₂ (longBlock (GaloisField 2 f) (r + 1) m
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta (χ := χ)))) :=
    fun m hm => c1_commute_of_mem_centralizer_zero hF hg₂.2 rfl hm
  have hmem : ⁅s₁, s₂⁆ ∈ suppGroup (coords j) :=
    commutator_mem_suppGroup_coords_of_commute (j := j) (a := ggSecFiveBZeta (χ := χ))
      (zeta_val_ne_one hF) (zeta_val_ne_inv hF hp2) h1 h2
  rw [← range_longBlock (K := GaloisField 2 f) (n := r + 1) j] at hmem
  obtain ⟨A, hA⟩ := hmem
  refine ⟨A, ?_⟩
  rw [MonoidHom.comp_apply, hA, map_commutatorElement]

end KFrame

end Torus

end Helpers

theorem ggSecFiveBPermSp_reflComm_K [Finite G] {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hf : 2 ≤ f) (hr : 2 ≤ r) {Bs K : Subgroup G} {y : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) {i j : Fin (r + 1)} (hij : i ≠ j) :
    ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G), Bs⁆ =
      (κ.comp (shortBlock (GaloisField 2 f) hij)).range := by
  set H : Subgroup G := ggBsCoordEq Bs eta (π i.succ) (π j.succ) with hHdef
  set R : Subgroup G := (κ.comp (shortBlock (GaloisField 2 f) hij)).range with hRdef
  set t : G := κ (shortBlock (GaloisField 2 f) hij
    (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
      ggSecFiveBZeta (χ := χ)))) with htdef
  have htB : t ∈ Bs := c2_t_mem_Bs hF hBs hij
  have hηt : ∀ m, eta (⟨t, htB⟩ : ↥Bs) (π m.succ) =
      if m = i then Multiplicative.ofAdd 1 else
        if m = j then Multiplicative.ofAdd (-1) else 1 :=
    fun m => c2_eta_t hF hp2 hij rfl m
  have hgen := hgen_short hp2 htB hij hηt
  have hX : Subgroup.centralizer (ggBsCoordEq Bs eta (π i.succ) (π j.succ) : Set G) ≤
      Subgroup.normalizer (K : Set G) := c2_hX hF hp2 hf hr hBs hyB hK
  have ht := c2_ht hF hp2 hij
  have hDR := c2_hDR hF hp2 hij
  have hRC := c2_hRC hF hij
  have hRt := c2_hRt hF hp2 hij
  exact ggCommutator_centralizer_eq (E := Bs) (H := H) (X := K) (R := R) (t := t)
    hBc (ggBsCoordEq_le (π i.succ) (π j.succ)) htB hgen hX ht hDR hRC hRt

theorem ggSecFiveBPermSp_singletonComm_K [Finite G] {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hf : 2 ≤ f) (hr : 2 ≤ r) {Bs K : Subgroup G} {y : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpKFrame Bs K eta π κ χ) (j : Fin (r + 1)) :
    ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G), Bs⁆ =
      (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range := by
  set t : G := κ (longBlock (GaloisField 2 f) (r + 1) j
    (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (
      ggSecFiveBZeta (χ := χ)))) with htdef
  have htB : t ∈ Bs := by
    rw [htdef]
    exact longBlock_torus_mem_Bs hF hBs j
  have hηt : ∀ m, eta ⟨t, htB⟩ (π m.succ) = if m = j then Multiplicative.ofAdd 1 else 1 :=
    fun m => eta_of_longBlock_torus hF hp2 (b := ⟨t, htB⟩) htdef m
  have hgen : ∀ e ∈ Bs, ∃ h ∈ ggBsCoordZero Bs eta (π j.succ), ∃ k : ℤ, e = h * t ^ k :=
    ggSecFiveBHgen_long htB hηt
  have hX : Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G) ≤
      Subgroup.normalizer (K : Set G) :=
    c1_kframe_normalizes_zero hF hp2 hf hr hBs hyB hK j
  have hRC : (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range ≤
      Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G) :=
    c1_range_le_centralizer_zero hF j
  have hDR : ⁅K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G),
        K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G)⁆ ≤
      (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range :=
    c1_commutator_le_range hF hp2 j
  have hRt : (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range ≤
      ⁅(κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range, Subgroup.zpowers t⁆ := by
    rw [htdef]
    exact c1_range_le_commutator_zpowers hF hp2 j
  have ht : t ∈ ⁅K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G),
      K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π j.succ) : Set G)⁆ := by
    rw [htdef]
    exact c1_t_mem_commutator_zero hF hp2 j
  exact ggCommutator_centralizer_eq (E := Bs) (H := ggBsCoordZero Bs eta (π j.succ))
    (X := K) (R := (κ.comp (longBlock (GaloisField 2 f) (r + 1) j)).range) (t := t)
    hBc (ggBsCoordZero_le (π j.succ)) htB hgen hX ht hDR hRC hRt

end CFSG.StandardType

end
