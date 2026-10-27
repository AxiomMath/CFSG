module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelCenter
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischerConverse
public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import TauCeti.Algebra.Group.Units.Basic

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution

set_option backward.isDefEq.respectTransparency false

instance : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide)

@[expose] def signUnit : Bool → (ZMod 5)ˣ
  | true => 1
  | false => Units.mk0 (2 : ZMod 5) (by decide)

@[expose] def sqClass (b : Bool) : Multiplicative (TauCeti.SquareClassGroup (ZMod 5)) :=
  TauCeti.squareClassHom (signUnit b)

theorem sqClass_true : sqClass true = 1 := by
  show TauCeti.squareClassHom (1 : (ZMod 5)ˣ) = 1
  exact map_one _

theorem sqClass_false :
    sqClass false = TauCeti.squareClassHom (Units.mk0 (2 : ZMod 5) (by decide)) := rfl

private theorem squareClassHom_eq_one_of_isSquare_val {u : (ZMod 5)ˣ}
    (hu : IsSquare (u : ZMod 5)) : TauCeti.squareClassHom u = 1 := by
  rw [← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square,
    ← TauCeti.isSquare_units_val_iff]
  exact hu

theorem squareClassHom_mul_self (u : (ZMod 5)ˣ) :
    TauCeti.squareClassHom u * TauCeti.squareClassHom u = 1 := by
  rw [← map_mul, ← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square]
  exact ⟨u, rfl⟩

private theorem sqClass_false_ne_one : sqClass false ≠ 1 := by
  intro h
  have h1 : Units.mk0 (2 : ZMod 5) (by decide) ∈
      (TauCeti.squareClassHom (K := ZMod 5)).ker := h
  rw [TauCeti.ker_squareClassHom, Subgroup.mem_square, ← TauCeti.isSquare_units_val_iff,
    Units.val_mk0] at h1
  exact absurd h1 (by decide)

theorem sqClass_injective : Function.Injective sqClass := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · rw [sqClass_true] at hab
    exact absurd hab sqClass_false_ne_one
  · rw [sqClass_true] at hab
    exact absurd hab.symm sqClass_false_ne_one
  · rfl

theorem squareClassHom_unitOfInvertible_eq_sqClass {x : ZMod 5} [Invertible x]
    {π : Bool} (hsign : IsSquare x ↔ π = true) :
    TauCeti.squareClassHom (unitOfInvertible x) = sqClass π := by
  by_cases hπ : π = true
  · rw [hπ, sqClass_true]
    apply squareClassHom_eq_one_of_isSquare_val
    rw [val_unitOfInvertible]
    exact hsign.mpr hπ
  · have hπf : π = false := by cases π <;> simp_all
    rw [hπf, sqClass_false]
    have hx0 : x ≠ 0 := by
      intro h0
      exact hπ (hsign.mp (by rw [h0]; exact ⟨0, by simp⟩))
    have hval : ¬ IsSquare x := fun h => hπ (hsign.mp h)
    rw [TauCeti.squareClassHom_apply, TauCeti.squareClassHom_apply,
      Multiplicative.ofAdd.injective.eq_iff, TauCeti.squareClass_eq_iff_isSquare_mul,
      ← TauCeti.isSquare_units_val_iff, Units.val_mul, val_unitOfInvertible, Units.val_mk0]
    fin_cases x
    · exact absurd (⟨0, by decide⟩ : IsSquare (0 : ZMod 5)) hval
    · exact absurd (⟨1, by decide⟩ : IsSquare (1 : ZMod 5)) hval
    · decide
    · decide
    · exact absurd (⟨2, by decide⟩ : IsSquare (4 : ZMod 5)) hval

@[expose] noncomputable def reflO (k : ℕ) (ε : Bool) (v : Fin (k + 1) → ZMod 5) :
    TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε) :=
  ⟨reflect (fiveQ k ε) v, reflect_mem_orthogonalGroup (fiveQ k ε) v⟩

theorem reflO_eq_reflectionOrthogonal {k : ℕ} (ε : Bool)
    (v : Fin (k + 1) → ZMod 5) [Invertible (fiveQ k ε v)] :
    reflO k ε v = TauCeti.QuadraticMap.reflectionOrthogonal (fiveQ k ε) v := by
  apply Subtype.ext
  exact (coe_reflectionOrthogonal_eq_reflect (Q := fiveQ k ε) (v := v)).symm

theorem detSpinorNorm_reflO {k : ℕ} (ε : Bool) (v : Fin (k + 1) → ZMod 5)
    [Invertible (fiveQ k ε v)] :
    detSpinorNorm (fiveQ_nondegenerate k ε) (reflO k ε v) =
      ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (unitOfInvertible (fiveQ k ε v))) := by
  rw [reflO_eq_reflectionOrthogonal, detSpinorNorm_reflectionOrthogonal]

theorem fiveGLIso_mem_orthogonalGroup_of_mem {k : ℕ} {ε π : Bool}
    {g : GL (Fin (k + 1)) (ZMod 5)} (hg : g ∈ Subgroup.closure (fiveReflections k ε π)) :
    fiveGLIso k g ∈ TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [fiveQ_apply, fiveQ_apply, fiveGLIso_apply]
  exact fiveForm_mulVec_of_mem (show g ∈ fiveReflectionGroup k ε π from hg) x x

private theorem weight_ne_zero (k : ℕ) (ε : Bool) (i : Fin (k + 1)) :
    fiveWeight k ε i ≠ 0 := by
  rw [fiveWeight]
  by_cases hi : i = Fin.last k
  · rw [if_pos hi]
    cases ε <;> decide
  · rw [if_neg hi]
    exact (by decide : (1 : ZMod 5) ≠ 0)

private def weightUnit (k : ℕ) (ε : Bool) (i : Fin (k + 1)) : (ZMod 5)ˣ :=
  Units.mk0 (fiveWeight k ε i) (weight_ne_zero k ε i)

private noncomputable def qUnit (k : ℕ) (ε : Bool) (v : Fin (k + 1) → ZMod 5) :
    (ZMod 5)ˣ :=
  if h : fiveQ k ε v = 0 then 1 else Units.mk0 (fiveQ k ε v) h

private theorem qUnit_single (k : ℕ) (ε : Bool) (i : Fin (k + 1)) :
    qUnit k ε (Pi.single i 1) = weightUnit k ε i := by
  apply Units.ext
  rw [qUnit]
  rw [dif_neg (show ¬ (fiveQ k ε (Pi.single i 1) = 0) by
    rw [fiveQ_single]; exact weight_ne_zero k ε i)]
  rw [Units.val_mk0, weightUnit, Units.val_mk0, fiveQ_single]

private theorem squareClassHom_weightUnit_castSucc (k : ℕ) (ε : Bool) (i : Fin k) :
    TauCeti.squareClassHom (weightUnit k ε i.castSucc) = 1 := by
  apply squareClassHom_eq_one_of_isSquare_val
  rw [weightUnit, Units.val_mk0, fiveWeight_castSucc]
  exact ⟨1, by decide⟩

private theorem squareClassHom_weightUnit_last (k : ℕ) (ε : Bool) :
    TauCeti.squareClassHom (weightUnit k ε (Fin.last k)) = sqClass ε := by
  have hwu : weightUnit k ε (Fin.last k) =
      Units.mk0 (-(if ε then (1 : ZMod 5) else 2)) (by cases ε <;> decide) := by
    apply Units.ext
    simp only [weightUnit, Units.val_mk0, fiveWeight_last]
  rw [hwu]
  cases ε
  ·
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sqClass_false]
    rw [TauCeti.squareClassHom_apply, TauCeti.squareClassHom_apply,
      Multiplicative.ofAdd.injective.eq_iff, TauCeti.squareClass_eq_iff_isSquare_mul,
      ← TauCeti.isSquare_units_val_iff, Units.val_mul, Units.val_mk0, Units.val_mk0]
    decide
  ·
    simp only [Bool.true_eq, ↓reduceIte]
    rw [sqClass_true]
    apply squareClassHom_eq_one_of_isSquare_val
    rw [Units.val_mk0]
    exact ⟨2, by decide⟩

private def stdBasis (k : ℕ) : List (Fin (k + 1) → ZMod 5) :=
  List.ofFn (fun i : Fin (k + 1) => Pi.single i 1)

private theorem stdBasis_ne_zero (k : ℕ) (ε : Bool) :
    ∀ a ∈ stdBasis k, fiveQ k ε a ≠ 0 := by
  intro a ha
  rw [stdBasis, List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  rw [fiveQ_single]
  exact weight_ne_zero k ε i

private theorem stdBasis_pairwise (k : ℕ) (ε : Bool) :
    (stdBasis k).Pairwise (fun u v => polar (fiveQ k ε) u v = 0) := by
  rw [stdBasis, List.pairwise_ofFn]
  intro i j hij
  rw [fiveQ_polar, fiveForm_single_single, if_neg (ne_of_lt hij), mul_zero]

private theorem stdBasis_span (k : ℕ) :
    Submodule.span (ZMod 5) {v : Fin (k + 1) → ZMod 5 | v ∈ stdBasis k} = ⊤ := by
  have hset : {v : Fin (k + 1) → ZMod 5 | v ∈ stdBasis k} =
      Set.range (fun i : Fin (k + 1) => Pi.single i (1 : ZMod 5)) := by
    ext v
    rw [Set.mem_setOf_eq, stdBasis, List.mem_ofFn']
  rw [hset, ← (Pi.basisFun (ZMod 5) (Fin (k + 1))).span_eq]
  congr 1
  ext v
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, Pi.basisFun_apply (ZMod 5) (Fin (k + 1)) i⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← Pi.basisFun_apply (ZMod 5) (Fin (k + 1)) i]
    exact hi

private theorem stdBasis_prod_reflect (k : ℕ) (ε : Bool) :
    ((stdBasis k).map (reflect (fiveQ k ε))).prod = LinearEquiv.neg (ZMod 5) :=
  CFSG.ClassicalInvolution.prod_map_reflect_eq_neg (Q := fiveQ k ε)
    (stdBasis_ne_zero k ε) (stdBasis_pairwise k ε) (stdBasis_span k)

private theorem stdBasis_prod_reflO (k : ℕ) (ε : Bool) :
    QuadraticMap.negOrthogonal (fiveQ k ε) = ((stdBasis k).map (reflO k ε)).prod := by
  apply Subtype.ext
  rw [QuadraticMap.coe_negOrthogonal, Subgroup.val_list_prod, List.map_map]
  exact (stdBasis_prod_reflect k ε).symm

private lemma list_prod_pair {α : Type*} (l : List α) (g : α → (ZMod 5)ˣ) :
    (l.map (fun v => ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (g v)))).prod =
      (((-1 : (ZMod 5)ˣ) ^ l.length, TauCeti.squareClassHom ((l.map g).prod))) := by
  induction l with
  | nil => refine Prod.ext rfl ?_
           exact (map_one (TauCeti.squareClassHom (K := ZMod 5))).symm
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih, pow_succ, map_mul]
    exact Prod.ext (mul_comm _ _) rfl

private theorem stdBasis_squareClass_prod (k : ℕ) (ε : Bool) :
    TauCeti.squareClassHom (((stdBasis k).map (fun v => qUnit k ε v)).prod) = sqClass ε := by
  have hmap : (stdBasis k).map (fun v => qUnit k ε v) =
      List.ofFn (fun i : Fin (k + 1) => qUnit k ε (Pi.single i 1)) := by
    rw [stdBasis, List.map_ofFn]; rfl
  rw [hmap, Fin.prod_ofFn, map_prod]
  rw [Finset.prod_eq_single (Fin.last k)]
  · rw [qUnit_single, squareClassHom_weightUnit_last]
  · intro i _ hi
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [qUnit_single, squareClassHom_weightUnit_castSucc]
    · exact absurd rfl hi
  · intro h
    exact absurd (Finset.mem_univ (Fin.last k)) h

private theorem unitOfInvertible_eq_qUnit {k : ℕ} (ε : Bool) {v : Fin (k + 1) → ZMod 5}
    (hv : fiveQ k ε v ≠ 0) [Invertible (fiveQ k ε v)] :
    unitOfInvertible (fiveQ k ε v) = qUnit k ε v := by
  apply Units.ext
  rw [val_unitOfInvertible, qUnit, dif_neg hv, Units.val_mk0]

private theorem fiveGLIso_neg_one_eq_neg {k : ℕ} :
    fiveGLIso k (-1 : GL (Fin (k + 1)) (ZMod 5)) = LinearEquiv.neg (ZMod 5) := by
  apply LinearEquiv.ext
  intro x
  rw [fiveGLIso_apply]
  rw [show ((-1 : GL (Fin (k + 1)) (ZMod 5)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) =
      -(1 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) from rfl,
    Matrix.neg_mulVec, Matrix.one_mulVec]
  rfl

private theorem detSpinorNorm_neg_one_value {k : ℕ} (ε : Bool) :
    detSpinorNorm (fiveQ_nondegenerate k ε) (QuadraticMap.negOrthogonal (fiveQ k ε)) =
      (((-1 : (ZMod 5)ˣ) ^ (k + 1)), sqClass ε) := by
  have hdet : detSpinorNorm (fiveQ_nondegenerate k ε) (QuadraticMap.negOrthogonal (fiveQ k ε)) =
      ((stdBasis k).map (fun v => detSpinorNorm (fiveQ_nondegenerate k ε) (reflO k ε v))).prod := by
    rw [stdBasis_prod_reflO k ε, map_list_prod, List.map_map]
    rfl
  have hper : ∀ v ∈ stdBasis k, detSpinorNorm (fiveQ_nondegenerate k ε) (reflO k ε v) =
      ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (qUnit k ε v)) := by
    intro v hv
    have hvQ : fiveQ k ε v ≠ 0 := stdBasis_ne_zero k ε v hv
    letI : Invertible (fiveQ k ε v) := invertibleOfNonzero hvQ
    rw [detSpinorNorm_reflO, unitOfInvertible_eq_qUnit ε hvQ]
  rw [hdet]
  rw [show ((stdBasis k).map (fun v => detSpinorNorm (fiveQ_nondegenerate k ε) (reflO k ε v))) =
      ((stdBasis k).map (fun v => ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (qUnit k ε v)))) from
    List.map_congr_left hper]
  rw [list_prod_pair (stdBasis k) (fun v => qUnit k ε v), stdBasis_squareClass_prod]
  congr 1
  rw [stdBasis, List.length_ofFn]

private theorem neg_one_mem_imp_cond {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (hneg : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π) :
    ε = true ↔ (π = true ∨ Even (k + 1)) := by
  let a : (ZMod 5)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 5)) :=
    ((-1 : (ZMod 5)ˣ), sqClass π)
  have ha2 : a * a = 1 := by
    refine Prod.ext ?_ ?_
    · apply Units.ext; simp [a]
    · change sqClass π * sqClass π = 1
      exact squareClassHom_mul_self (signUnit π)
  have hmemH : detSpinorNorm (fiveQ_nondegenerate k ε)
      ⟨fiveGLIso k (-1), fiveGLIso_mem_orthogonalGroup_of_mem hneg⟩ ∈
      Subgroup.closure ({a, a} : Set ((ZMod 5)ˣ ×
        Multiplicative (TauCeti.SquareClassGroup (ZMod 5)))) := by
    refine Subgroup.closure_induction (k := fiveReflections k ε π)
      (p := fun g hg => detSpinorNorm (fiveQ_nondegenerate k ε)
        ⟨fiveGLIso k g, fiveGLIso_mem_orthogonalGroup_of_mem hg⟩ ∈
        Subgroup.closure ({a, a} : Set _)) ?_ ?_ ?_ ?_ hneg
    · intro r hr
      obtain ⟨v, hv, hsign, rfl⟩ := exists_eq_fiveReflOf hr
      have hQv : fiveQ k ε v ≠ 0 := by rwa [fiveQ_apply]
      letI : Invertible (fiveQ k ε v) := invertibleOfNonzero hQv
      have hsub : (⟨fiveGLIso k (fiveReflOf k ε v),
          fiveGLIso_mem_orthogonalGroup_of_mem (Subgroup.subset_closure hr)⟩ :
          TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) = reflO k ε v := by
        apply Subtype.ext
        change fiveGLIso k (fiveReflOf k ε v) = reflect (fiveQ k ε) v
        rw [fiveGLIso_fiveReflOf]
        rfl
      have hdet_eq : detSpinorNorm (fiveQ_nondegenerate k ε)
          ⟨fiveGLIso k (fiveReflOf k ε v),
            fiveGLIso_mem_orthogonalGroup_of_mem (Subgroup.subset_closure hr)⟩ =
          detSpinorNorm (fiveQ_nondegenerate k ε) (reflO k ε v) :=
        congrArg (detSpinorNorm (fiveQ_nondegenerate k ε)) hsub
      rw [hdet_eq, detSpinorNorm_reflO]
      have hsign' : IsSquare (fiveQ k ε v) ↔ π = true := by
        rw [fiveQ_apply]
        exact hsign
      rw [squareClassHom_unitOfInvertible_eq_sqClass hsign']
      exact Subgroup.subset_closure (by simp [a])
    · have h1 : (⟨fiveGLIso k 1,
          fiveGLIso_mem_orthogonalGroup_of_mem
            (Subgroup.one_mem (Subgroup.closure (fiveReflections k ε π)))⟩ :
          TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) = 1 := by
        apply Subtype.ext
        change fiveGLIso k 1 = 1
        rw [map_one]
      have hdet1 : detSpinorNorm (fiveQ_nondegenerate k ε)
          ⟨fiveGLIso k 1, fiveGLIso_mem_orthogonalGroup_of_mem
            (Subgroup.one_mem (Subgroup.closure (fiveReflections k ε π)))⟩ = 1 := by
        rw [h1, map_one]
      rw [hdet1]
      exact Subgroup.one_mem _
    · intro x y hx hy ihx ihy
      have hxy : (⟨fiveGLIso k (x * y),
          fiveGLIso_mem_orthogonalGroup_of_mem (Subgroup.mul_mem _ hx hy)⟩ :
          TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) =
          ⟨fiveGLIso k x, fiveGLIso_mem_orthogonalGroup_of_mem hx⟩ *
            ⟨fiveGLIso k y, fiveGLIso_mem_orthogonalGroup_of_mem hy⟩ := by
        apply Subtype.ext
        change fiveGLIso k (x * y) = fiveGLIso k x * fiveGLIso k y
        rw [map_mul]
      have hdet := congrArg (detSpinorNorm (fiveQ_nondegenerate k ε)) hxy
      rw [hdet, map_mul]
      exact Subgroup.mul_mem _ ihx ihy
    · intro x hx ihx
      have hxy : (⟨fiveGLIso k x⁻¹,
          fiveGLIso_mem_orthogonalGroup_of_mem (Subgroup.inv_mem _ hx)⟩ :
          TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) =
          (⟨fiveGLIso k x, fiveGLIso_mem_orthogonalGroup_of_mem hx⟩)⁻¹ := by
        apply Subtype.ext
        change fiveGLIso k x⁻¹ = (fiveGLIso k x)⁻¹
        rw [map_inv]
      have hdet := congrArg (detSpinorNorm (fiveQ_nondegenerate k ε)) hxy
      rw [hdet, map_inv]
      exact Subgroup.inv_mem _ ihx
  have hval := detSpinorNorm_neg_one_value (k := k) ε
  have hnegO : (⟨fiveGLIso k (-1), fiveGLIso_mem_orthogonalGroup_of_mem hneg⟩ :
      TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) =
      QuadraticMap.negOrthogonal (fiveQ k ε) := by
    apply Subtype.ext
    rw [QuadraticMap.coe_negOrthogonal]
    change fiveGLIso k (-1) = LinearEquiv.neg (ZMod 5)
    rw [fiveGLIso_neg_one_eq_neg]
  have hmemH' : detSpinorNorm (fiveQ_nondegenerate k ε)
      (QuadraticMap.negOrthogonal (fiveQ k ε)) ∈
      Subgroup.closure ({a, a} : Set ((ZMod 5)ˣ ×
        Multiplicative (TauCeti.SquareClassGroup (ZMod 5)))) := by
    rw [← hnegO]
    exact hmemH
  rw [hval] at hmemH'
  have hcases := eq_one_or_eq_or_eq_mul_of_mem_closure_pair (a := a) (b := a) ha2 ha2
    (by rw [ha2]) hmemH'
  have key : (((-1 : (ZMod 5)ˣ) ^ (k + 1) = 1) ∧ (sqClass ε = 1)) ∨
      (((-1 : (ZMod 5)ˣ) ^ (k + 1) = -1) ∧ (sqClass ε = sqClass π)) := by
    rcases hcases with h | h | h | h
    · exact Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · exact Or.inr ⟨by simpa [a] using congrArg Prod.fst h,
        by simpa [a] using congrArg Prod.snd h⟩
    · exact Or.inr ⟨by simpa [a] using congrArg Prod.fst h,
        by simpa [a] using congrArg Prod.snd h⟩
    · refine Or.inl ⟨?_, ?_⟩
      · exact congrArg Prod.fst (h.trans ha2)
      · exact congrArg Prod.snd (h.trans ha2)
  have hne : (-1 : (ZMod 5)ˣ) ≠ 1 := by decide
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hε : ε = true := sqClass_injective (by rw [h2, sqClass_true])
    have heven : Even (k + 1) := (neg_one_pow_eq_one_iff_even hne).mp h1
    rw [hε]
    simp [heven]
  · have hε : ε = π := sqClass_injective h2
    have hodd : Odd (k + 1) := (neg_one_pow_eq_neg_one_iff_odd hne).mp h1
    rw [hε]
    simp [Nat.not_even_iff_odd.mpr hodd]

private theorem reflect_comm_of_polar_eq_zero {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {u w : V} (h : polar Q u w = 0) :
    Commute (reflect Q u) (reflect Q w) := by
  show reflect Q u * reflect Q w = reflect Q w * reflect Q u
  have h1 : reflect Q u * reflect Q w * (reflect Q u)⁻¹ = reflect Q w := by
    rw [reflect_conj (reflect_mem_orthogonalGroup Q u) w, reflect_apply_of_polar_eq_zero h]
  rw [reflect_inv] at h1
  calc reflect Q u * reflect Q w
      = (reflect Q u * reflect Q w) * (reflect Q u * reflect Q u) := by
        rw [reflect_mul_self, mul_one]
    _ = reflect Q w * reflect Q u := by rw [← mul_assoc, h1]

private theorem fiveReflOf_comm_of_orthogonal {k : ℕ} (ε : Bool)
    {u w : Fin (k + 1) → ZMod 5} (h : fiveForm k ε u w = 0) :
    Commute (fiveReflOf k ε u) (fiveReflOf k ε w) := by
  apply (fiveGLIso k).injective
  rw [map_mul, map_mul, fiveGLIso_fiveReflOf, fiveGLIso_fiveReflOf]
  exact reflect_comm_of_polar_eq_zero (by rw [fiveQ_polar, h, mul_zero])

private theorem frame_of_cond {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (hcond : ε = true ↔ (π = true ∨ Even (k + 1))) :
    ∃ r : Fin (k + 1) → GL (Fin (k + 1)) (ZMod 5),
      (∀ i, r i ∈ fiveReflections k ε π) ∧ (∀ i j, Commute (r i) (r j)) ∧
        Function.Injective r ∧ (List.ofFn r).prod = -1 := by
  let c : ZMod 5 := if π then 1 else 2
  have hc0 : c ≠ 0 := by
    simp only [c]; split_ifs <;> decide
  let b : LinearMap.BilinForm (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    c • dotProductBilin (ZMod 5) (ZMod 5)
  have hb_apply : ∀ x y, b x y = c * ∑ i, x i * y i := by
    intro x y
    simp only [b, LinearMap.smul_apply, dotProductBilin_apply_apply, dotProduct,
      smul_eq_mul]
  have hsym : ∀ x y, b x y = b y x := by
    intro x y
    rw [hb_apply, hb_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hnd : ∀ x, (∀ y, b x y = 0) → x = 0 := by
    intro x hx
    funext j
    have h := hx (Pi.single j 1)
    rw [hb_apply] at h
    have hsum : ∑ i, x i * (Pi.single j 1 : Fin (k + 1) → ZMod 5) i = x j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi
        simp [Pi.single_apply, hi]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hsum] at h
    exact (mul_eq_zero.mp h).resolve_left hc0
  obtain ⟨ε', A, hA⟩ := exists_linearEquiv_fiveForm_of_bilin hsym hnd
  let v : Fin (k + 1) → (Fin (k + 1) → ZMod 5) := fun i => A (Pi.single i 1)
  have hv_gram : ∀ i j, fiveForm k ε' (v i) (v j) = c * (if i = j then 1 else 0) := by
    intro i j
    rw [hA, hb_apply]
    congr 1
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Finset.sum_eq_single i]
      · simp
      · intro l _ hl
        simp [Pi.single_apply, hl]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [if_neg hij, Finset.sum_eq_zero]
      intro l _
      by_cases hli : l = i
      · subst hli
        simp [Pi.single_apply, hij]
      · simp [Pi.single_apply, hli]
  have hvQ : ∀ i, fiveForm k ε' (v i) (v i) = c := by
    intro i
    rw [hv_gram, if_pos rfl, mul_one]
  have hvQ_ne : ∀ i, fiveForm k ε' (v i) (v i) ≠ 0 := by
    intro i; rw [hvQ]; exact hc0
  have hsign : ∀ i, IsSquare (fiveForm k ε' (v i) (v i)) ↔ π = true := by
    intro i
    rw [hvQ]
    cases π
    · simp [c, not_isSquare_two_zmod5]
    · simp [c, isSquare_one_zmod5]
  let l : List (Fin (k + 1) → ZMod 5) := List.ofFn v
  have hl0 : ∀ a ∈ l, fiveQ k ε' a ≠ 0 := by
    intro a ha
    change a ∈ List.ofFn v at ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    rw [fiveQ_apply]
    exact hvQ_ne i
  have hpair : l.Pairwise (fun a b => polar (fiveQ k ε') a b = 0) := by
    show (List.ofFn v).Pairwise (fun a b => polar (fiveQ k ε') a b = 0)
    rw [List.pairwise_ofFn]
    intro i j hij
    rw [fiveQ_polar, hv_gram, if_neg (ne_of_lt hij)]
    ring
  have hlen : l.length = Module.finrank (ZMod 5) (Fin (k + 1) → ZMod 5) := by
    show (List.ofFn v).length = Module.finrank (ZMod 5) (Fin (k + 1) → ZMod 5)
    rw [List.length_ofFn, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hspan : Submodule.span (ZMod 5) {a | a ∈ l} = ⊤ :=
    span_eq_top_of_pairwise_polar (by decide : (2 : ZMod 5) ≠ 0) hl0 hpair hlen
  have hprodL : (l.map (reflect (fiveQ k ε'))).prod = LinearEquiv.neg (ZMod 5) :=
    prod_map_reflect_eq_neg hl0 hpair hspan
  let r : Fin (k + 1) → GL (Fin (k + 1)) (ZMod 5) := fun i => fiveReflOf k ε' (v i)
  have hfive : (List.ofFn (fun i => fiveReflOf k ε' (v i))).prod = -1 := by
    apply (fiveGLIso k).injective
    rw [map_list_prod, fiveGLIso_neg_one_eq_neg, List.map_ofFn]
    have hfun : (⇑(fiveGLIso k) ∘ fun i => fiveReflOf k ε' (v i)) =
        (fun i => reflect (fiveQ k ε') (v i)) := by
      funext i
      rw [Function.comp_apply, fiveGLIso_fiveReflOf]
      rfl
    rw [hfun, List.ofFn_comp']
    exact hprodL
  have hneg' : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε' π := by
    rw [← hfive]
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.subset_closure (fiveReflOf_mem (hvQ_ne i) (hsign i))
  have hcond' : ε' = true ↔ (π = true ∨ Even (k + 1)) := neg_one_mem_imp_cond hk hneg'
  have hε : ε' = ε := by
    rw [Bool.eq_iff_iff, hcond', hcond]
  subst ε'
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro i
    exact fiveReflOf_mem (hvQ_ne i) (hsign i)
  · intro i j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact fiveReflOf_comm_of_orthogonal ε (by rw [hv_gram, if_neg hij, mul_zero])
  · intro i j hij
    by_contra hne
    have horth : fiveForm k ε (v i) (v j) = 0 := by
      rw [hv_gram, if_neg hne, mul_zero]
    have h1 : (fiveReflOf k ε (v i) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v i =
        -v i := by
      rw [fiveReflOf_mulVec]
      have hcoef : 2 * fiveForm k ε (v i) (v i) * (fiveForm k ε (v i) (v i))⁻¹ =
          (2 : ZMod 5) := by
        rw [mul_assoc, mul_inv_cancel₀ (hvQ_ne i), mul_one]
      rw [hcoef, two_smul]
      abel
    have h2 : (fiveReflOf k ε (v j) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v i =
        v i := by
      rw [fiveReflOf_mulVec, horth]
      simp
    have h3 : (fiveReflOf k ε (v i) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v i =
        (fiveReflOf k ε (v j) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v i := by
      rw [show fiveReflOf k ε (v i) = fiveReflOf k ε (v j) from hij]
    have h3' : -v i = v i := h1.symm.trans (h3.trans h2)
    have hzero : (2 : ZMod 5) • v i = 0 := by
      rw [two_smul]
      exact neg_eq_iff_add_eq_zero.mp h3'
    have hvi0 : v i = 0 := by
      have := congrArg (fun z => (2 : ZMod 5)⁻¹ • z) hzero
      simpa [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0)] using this
    have hbad : fiveForm k ε (v i) (v i) = 0 := by
      rw [hvi0]
      simp [fiveForm]
    exact hvQ_ne i hbad
  · exact hfive

theorem neg_one_mem_fiveReflectionGroup_iff_aux {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π ↔
      (ε = true ↔ (π = true ∨ Even (k + 1))) := by
  constructor
  · exact neg_one_mem_imp_cond hk
  · intro hcond
    obtain ⟨r, hr, _, _, hprod⟩ := frame_of_cond hk hcond
    rw [← hprod]
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.subset_closure (hr i)

theorem exists_frame_of_neg_one_mem_aux {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (hneg : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π) :
    ∃ r : Fin (k + 1) → GL (Fin (k + 1)) (ZMod 5),
      (∀ i, r i ∈ fiveReflections k ε π) ∧ (∀ i j, Commute (r i) (r j)) ∧
        Function.Injective r ∧ (List.ofFn r).prod = -1 :=
  frame_of_cond hk ((neg_one_mem_fiveReflectionGroup_iff_aux hk ε π).mp hneg)

end CFSG.OddTranspositions.PartThree
