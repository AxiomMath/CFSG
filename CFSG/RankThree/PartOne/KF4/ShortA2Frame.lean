module

public import CFSG.RankThree.PartOne.KF4.ShortA2Fam
public import CFSG.RankThree.PartOne.KF4.Torus2
public import CFSG.RankThree.PartOne.KF4.A2Frame

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups

section Inj

variable
  {K : Type} [Field K]

theorem mem_subsystemTorus_f4Short {g : ModGL Tag.F4 K} :
    g ∈ subsystemTorus Tag.F4 K f4ShortSupport ↔
      ∃ a b : Kˣ, g = torus2Elt (f4Index 2) (f4Index 3) a b :=
  mem_subsystemTorus_pair (f4Index 2) (f4Index 3)

theorem torusElt_mem_f4Short {i : Fin Tag.F4.rank} (hi : i ∈ f4ShortSupport) (a : Kˣ) :
    torusElt Tag.F4 K i a ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

theorem torus2Elt_mem_f4Short (a b : Kˣ) :
    torus2Elt (f4Index 2) (f4Index 3) a b ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
  mul_mem (torusElt_mem_f4Short ((mem_f4ShortSupport _).2 (Or.inl rfl)) a)
    (torusElt_mem_f4Short ((mem_f4ShortSupport _).2 (Or.inr rfl)) b)

variable (K) in
@[expose] def f4ShortDiag (a b : Kˣ) : SL(3, K) :=
  ⟨Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((a * b⁻¹ : Kˣ) : K), (b : K)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp⟩

theorem Mat_torus2_short (a b : Kˣ) :
    f4Short_data.Mat (torus2Elt (f4Index 2) (f4Index 3) a b) = symRep K (f4ShortDiag K a b) := by
  rw [torus2Elt, f4Short_data.Mat_mul
      (torusElt_mem_f4Short ((mem_f4ShortSupport _).2 (Or.inl rfl)) a)
      (torusElt_mem_f4Short ((mem_f4ShortSupport _).2 (Or.inr rfl)) b),
    f4Short_data.Mat_torusElt, f4Short_data.Mat_torusElt, Matrix.diagonal_mul_diagonal,
    symRep_apply, f4ShortDiag, symCong_diagonal]
  congr 1
  funext k
  obtain ⟨h2, h3⟩ := f4Short_pairing k
  rw [h2, h3]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg, mul_comm, mul_left_comm] <;>
    field_simp

theorem f4ShortPosRoot_mem (m : Fin 3) :
    f4ShortPosRoot m ∈ parabolicRoots Tag.F4 f4ShortSupport := by
  obtain ⟨k, l, hkl, h⟩ := exists_sigma_of_f4ShortPosRoot m
  rw [h]
  exact f4ShortSigma_mem_parabolicRoots (ne_of_gt hkl)

theorem range_f4ShortPosRoot :
    Set.range f4ShortPosRoot = parabolicPosRoots Tag.F4 f4ShortSupport := by
  ext β
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨k, l, hkl, hm⟩ := exists_sigma_of_f4ShortPosRoot m
    rw [hm]
    have hmem := f4ShortSigma_mem_parabolicRoots (ne_of_gt hkl)
    exact ⟨hmem, hmem.1, (f4ShortSigma_height_pos k l (ne_of_gt hkl)).2 hkl⟩
  · rintro ⟨hβ, -, hpos⟩
    obtain ⟨k, l, hkl, rfl⟩ := exists_f4ShortSigma_of_mem hβ
    exact exists_f4ShortPosRoot k l ((f4ShortSigma_height_pos k l hkl).1 hpos)

theorem prod_short_pos (y : Fin 3 → K) :
    ((Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (y 0) *
      (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (y 1) *
        Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (y 2)) :
          SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      1 + (single 1 0 (y 0) + (single 2 1 (y 1) + single 2 0 (y 2))) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection]
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.add_apply,
    Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem f4Short_eq_one_of_Mat_mul_eq_one {t u : ModGL Tag.F4 K}
    (ht : t ∈ subsystemTorus Tag.F4 K f4ShortSupport)
    (hu : u ∈ parabolicLeviUnipotent Tag.F4 K f4ShortSupport)
    (h : f4Short_data.Mat (t * u) = 1) : t = 1 ∧ u = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_f4Short.1 ht
  obtain ⟨x, -, rfl⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) f4ShortPosRoot
    f4ShortPosRoot_injective range_f4ShortPosRoot).surjOn hu
  have f10 := f4ShortRootFamily_all (K := K) 1 0 (by decide)
  have f21 := f4ShortRootFamily_all (K := K) 2 1 (by decide)
  have f20 := f4ShortRootFamily_all (K := K) 2 0 (by decide)
  obtain ⟨ε0, h0⟩ := f10
  obtain ⟨ε1, h1⟩ := f21
  obtain ⟨ε2, h2⟩ := f20
  set y : Fin 3 → K := fun m => (![(ε0 : K), (ε1 : K), (ε2 : K)] m) * x m with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.F4 K (f4ShortPosRoot m) (x m),
      g ∈ subsystemGroup Tag.F4 K f4ShortSupport := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact pinnedX_mem_f4Short (f4ShortPosRoot_mem m) _
  have hMu : f4Short_data.Mat (List.ofFn fun m => pinnedX Tag.F4 K (f4ShortPosRoot m) (x m)).prod =
      symRep K (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (y 0) *
        (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (y 1) *
          Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (y 2))) := by
    rw [f4Short_data.Mat_list_prod _ hlist]
    simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    have e0 : f4ShortPosRoot 0 = f4ShortSigma 1 0 := rfl
    have e1 : f4ShortPosRoot 1 = f4ShortSigma 2 1 := rfl
    have e2 : f4ShortPosRoot 2 = f4ShortSigma 2 0 := rfl
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, e0, e1, e2, h0, h1, h2,
      map_mul, hy]
    rfl
  rw [f4Short_data.Mat_mul (torus2Elt_mem_f4Short a b) (Subgroup.list_prod_mem _ hlist),
    Mat_torus2_short, hMu, ← map_mul] at h
  have hDL : f4ShortDiag K a b *
      (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (y 0) *
        (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (y 1) *
          Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (y 2))) = 1 :=
    symRep_injective (by rw [h, map_one])
  have hmat : Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((a * b⁻¹ : Kˣ) : K), (b : K)] *
      (1 + (single 1 0 (y 0) + (single 2 1 (y 1) + single 2 0 (y 2)))) =
        (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h' := congrArg (fun A : SL(3, K) => (A : Matrix (Fin 3) (Fin 3) K)) hDL
    rw [Matrix.SpecialLinearGroup.coe_mul, prod_short_pos, Matrix.SpecialLinearGroup.coe_one]
      at h'
    exact h'
  have e : ∀ p q, (Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((a * b⁻¹ : Kˣ) : K), (b : K)] *
      (1 + (single 1 0 (y 0) + (single 2 1 (y 1) + single 2 0 (y 2)))) :
        Matrix (Fin 3) (Fin 3) K) p q = (1 : Matrix (Fin 3) (Fin 3) K) p q := fun p q => by
    rw [hmat]
  have d0 := e 0 0
  have d1 := e 1 1
  simp [Matrix.diagonal_mul, Matrix.add_apply] at d0 d1
  have ha : a = 1 := by
    have : (a⁻¹ : Kˣ) = 1 := Units.ext (by simpa using d0)
    simpa using this
  subst ha
  have hb : b = 1 := by
    have : (b⁻¹ : Kˣ) = 1 := Units.ext (by simpa using d1)
    simpa using this
  subst hb
  have o0 := e 1 0
  have o1 := e 2 1
  have o2 := e 2 0
  simp [Matrix.diagonal_mul, Matrix.add_apply] at o0 o1 o2
  have hy0 : ∀ m, y m = 0 := by
    intro m
    fin_cases m
    exacts [o0, o1, o2]
  have hx0 : x = 0 := by
    funext m
    have h0' := hy0 m
    rw [hy] at h0'
    have hne : ((![(ε0 : K), (ε1 : K), (ε2 : K)] : Fin 3 → K) m) ≠ 0 := by
      fin_cases m <;> simp
    exact (mul_eq_zero.1 h0').resolve_left hne
  subst hx0
  refine ⟨torus2Elt_one _ _, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem f4ShortRep_injective : Function.Injective (f4ShortRep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : f4Short_data.Mat (g : ModGL Tag.F4 K) = 1 := by
    rw [Mat_f4ShortRep, hg, map_one]
  exact Subtype.ext (f4Short_bruhat.Mat_eq_one
    (fun t ht u hu => f4Short_eq_one_of_Mat_mul_eq_one ht hu) g.2 hmat)

theorem f4ShortRep_surjective : Function.Surjective (f4ShortRep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, h⟩ := f4ShortRootFamily_all (K := K) i j hij
  have hmem := pinnedX_mem_f4Short (f4ShortSigma_mem_parabolicRoots hij) (((ε⁻¹ : Kˣ) : K) * c)
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply symRep_injective
  rw [← Mat_f4ShortRep]
  change f4Short_data.Mat (pinnedX Tag.F4 K (f4ShortSigma i j) (((ε⁻¹ : Kˣ) : K) * c)) =
    symRep K (Matrix.SpecialLinearGroup.transvection hij c)
  rw [h]
  congr 2
  rw [← mul_assoc, Units.mul_inv, one_mul]

end Inj

section Frame

variable
  (L : Type) [Field L]

theorem f4ShortRep_bijective : Function.Bijective (f4ShortRep L) :=
  ⟨f4ShortRep_injective, f4ShortRep_surjective⟩

@[expose] def f4ShortEquiv : SL(3, L) ≃* subsystemGroup Tag.F4 L f4ShortSupport :=
  (MulEquiv.ofBijective (f4ShortRep L) (f4ShortRep_bijective L)).symm

@[expose] def f4rhoShort : SL(3, L) →* ModGL Tag.F4 L :=
  (subsystemGroup Tag.F4 L f4ShortSupport).subtype.comp (f4ShortEquiv L).toMonoidHom

variable {L}

theorem f4ShortRep_f4ShortEquiv (X : SL(3, L)) : f4ShortRep L (f4ShortEquiv L X) = X :=
  (MulEquiv.ofBijective (f4ShortRep L) (f4ShortRep_bijective L)).apply_symm_apply X

theorem f4rhoShort_f4ShortRep {g : ModGL Tag.F4 L}
    (hg : g ∈ subsystemGroup Tag.F4 L f4ShortSupport) :
    f4rhoShort L (f4ShortRep L ⟨g, hg⟩) = g := by
  have h := (MulEquiv.ofBijective (f4ShortRep L) (f4ShortRep_bijective L)).symm_apply_apply
    (⟨g, hg⟩ : subsystemGroup Tag.F4 L f4ShortSupport)
  exact congrArg Subtype.val h

theorem f4rhoShort_mem (X : SL(3, L)) :
    f4rhoShort L X ∈ subsystemGroup Tag.F4 L f4ShortSupport :=
  (f4ShortEquiv L X).2

theorem Mat_f4rhoShort (X : SL(3, L)) :
    f4Short_data.Mat (f4rhoShort L X) = symRep L X := by
  have h := Mat_f4ShortRep (f4ShortEquiv L X)
  rw [f4ShortRep_f4ShortEquiv] at h
  exact h

theorem f4rhoShort_injective : Function.Injective (f4rhoShort L) := by
  intro X Y h
  apply symRep_injective
  rw [← Mat_f4rhoShort X, ← Mat_f4rhoShort Y, h]

theorem f4rhoShort_range : (f4rhoShort L).range = subsystemGroup Tag.F4 L f4ShortSupport := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ f4rhoShort_mem X) fun g hg => ?_
  exact ⟨f4ShortRep L ⟨g, hg⟩, f4rhoShort_f4ShortRep hg⟩

theorem f4rhoShort_transvection (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, f4rhoShort L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.F4 L (f4ShortSigma i j) ((ε : L) * t) := by
  obtain ⟨ε, h⟩ := f4ShortRootFamily_all (K := L) i j hij
  refine ⟨ε⁻¹, fun s => ?_⟩
  have hmem := pinnedX_mem_f4Short (K := L) (f4ShortSigma_mem_parabolicRoots hij)
    (((ε⁻¹ : Lˣ) : L) * s)
  have hrep : f4ShortRep L ⟨pinnedX Tag.F4 L (f4ShortSigma i j) (((ε⁻¹ : Lˣ) : L) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply symRep_injective
    rw [← Mat_f4ShortRep]
    change f4Short_data.Mat (pinnedX Tag.F4 L (f4ShortSigma i j) (((ε⁻¹ : Lˣ) : L) * s)) = _
    rw [h]
    congr 2
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [← hrep]
  exact f4rhoShort_f4ShortRep hmem

theorem f4rhoShort_diag (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    f4rhoShort L A ∈ torusGroup Tag.F4 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h2 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 ≠ 0 := fun h => by
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  set ua : Lˣ := (Units.mk0 _ h0)⁻¹ with hua
  set ub : Lˣ := Units.mk0 _ h2 with hub
  have hAeq : A = f4ShortDiag L ua ub := by
    apply Subtype.ext
    rw [hdiag]
    change Matrix.diagonal _ = Matrix.diagonal ![((ua⁻¹ : Lˣ) : L), ((ua * ub⁻¹ : Lˣ) : L),
      (ub : L)]
    congr 1
    funext i
    have h11 : (A : Matrix (Fin 3) (Fin 3) L) 1 1 =
        ((A : Matrix (Fin 3) (Fin 3) L) 0 0)⁻¹ * ((A : Matrix (Fin 3) (Fin 3) L) 2 2)⁻¹ := by
      field_simp
      linear_combination hdet
    fin_cases i <;> simp [hua, hub, h11]
  have hrep : f4ShortRep L ⟨torus2Elt (f4Index 2) (f4Index 3) ua ub,
      torus2Elt_mem_f4Short ua ub⟩ = A := by
    apply symRep_injective
    rw [← Mat_f4ShortRep]
    exact (Mat_torus2_short ua ub).trans (by rw [hAeq])
  have hJ : f4rhoShort L A = torus2Elt (f4Index 2) (f4Index 3) ua ub := by
    rw [← hrep]
    exact f4rhoShort_f4ShortRep (torus2Elt_mem_f4Short ua ub)
  rw [hJ]
  have hmem : torus2Elt (f4Index 2) (f4Index 3) ua ub ∈
      subsystemGroup Tag.F4 L f4ShortSupport ⊓ torusGroup Tag.F4 L := by
    rw [subsystemGroup_inf_torusGroup (τ := Tag.F4) (K := L) (A := f4ShortSupport)]
    exact mem_subsystemTorus_f4Short.2 ⟨ua, ub, rfl⟩
  exact hmem.2

theorem f4ShortSigma_neg' (i j : Fin 3) : f4ShortSigma j i = -f4ShortSigma i j :=
  f4ShortSigma_neg i j

theorem f4Short_frame : IsA2Frame (f4rhoShort L) f4ShortSigma where
  injective := f4rhoShort_injective
  isRoot i j hij := (f4ShortSigma_mem_parabolicRoots hij).1
  neg i j := f4ShortSigma_neg i j
  add i j k := f4ShortSigma_add i j k
  transv i j hij := f4rhoShort_transvection i j hij
  range := by
    rw [f4rhoShort_range, subsystemGroup_eq_rootSpan]
    congr 1
    ext r
    constructor
    · intro hr
      obtain ⟨k, l, hkl, rfl⟩ := exists_f4ShortSigma_of_mem hr
      exact ⟨k, l, hkl, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact f4ShortSigma_mem_parabolicRoots hij
  diag A hA := f4rhoShort_diag A hA

end Frame


end CFSG.RankThree.PartOne.KF4
