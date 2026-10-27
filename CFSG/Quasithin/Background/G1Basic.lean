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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Matrix

namespace CFSG.Quasithin.G1


variable {F : Type*} [Field F] {n : ℕ}

@[expose] def blockMap (i j : Fin n) (B : Matrix (Fin 2) (Fin 2) F) : (Fin n → F) →ₗ[F] (Fin n → F) :=
  LinearMap.pi fun k =>
    if k = i then B 0 0 • LinearMap.proj i + B 0 1 • LinearMap.proj j
    else if k = j then B 1 0 • LinearMap.proj i + B 1 1 • LinearMap.proj j
    else LinearMap.proj k

theorem blockMap_apply (i j : Fin n) (B : Matrix (Fin 2) (Fin 2) F) (v : Fin n → F) (k : Fin n) :
    blockMap i j B v k =
      if k = i then B 0 0 * v i + B 0 1 * v j
      else if k = j then B 1 0 * v i + B 1 1 * v j else v k := by
  unfold blockMap
  by_cases hki : k = i
  · subst hki; simp
  · by_cases hkj : k = j
    · subst hkj; simp [hki]
    · simp [hki, hkj]

theorem blockMap_one (i j : Fin n) : blockMap i j (1 : Matrix (Fin 2) (Fin 2) F) = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun k => ?_
  rw [blockMap_apply]
  by_cases hki : k = i
  · subst hki; simp
  · by_cases hkj : k = j
    · subst hkj; simp [hki]
    · simp [hki, hkj]

theorem blockMap_mul {i j : Fin n} (hij : i ≠ j) (B B' : Matrix (Fin 2) (Fin 2) F) :
    blockMap i j (B * B') = blockMap i j B ∘ₗ blockMap i j B' := by
  refine LinearMap.ext fun v => funext fun k => ?_
  simp only [LinearMap.comp_apply]
  rw [blockMap_apply, blockMap_apply]
  have hji : j ≠ i := hij.symm
  by_cases hki : k = i
  · subst hki
    simp [blockMap_apply, hji, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · by_cases hkj : k = j
    · subst hkj
      simp [blockMap_apply, hji, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [blockMap_apply, hki, hkj]


@[expose] noncomputable def emb (i j : Fin n) (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin n) (Fin n) F :=
  LinearMap.toMatrix' (blockMap i j B)

theorem emb_mulVec (i j : Fin n) (B : Matrix (Fin 2) (Fin 2) F) (v : Fin n → F) :
    emb i j B *ᵥ v = blockMap i j B v := by
  unfold emb
  rw [LinearMap.toMatrix'_mulVec]

theorem emb_one (i j : Fin n) : emb i j (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  unfold emb
  rw [blockMap_one]
  exact LinearMap.toMatrix'_id

theorem emb_mul {i j : Fin n} (hij : i ≠ j) (B B' : Matrix (Fin 2) (Fin 2) F) :
    emb i j (B * B') = emb i j B * emb i j B' := by
  unfold emb
  rw [blockMap_mul hij, LinearMap.toMatrix'_comp]

theorem emb_diagonal {i j : Fin n} (hij : i ≠ j) (D : Fin 2 → F) :
    emb i j (Matrix.diagonal D) =
      Matrix.diagonal (fun k => if k = i then D 0 else if k = j then D 1 else 1) := by
  have hji : j ≠ i := hij.symm
  unfold emb
  rw [← LinearMap.toMatrix'_toLin' (Matrix.diagonal fun k => if k = i then D 0 else if k = j then D 1 else (1 : F))]
  congr 1
  refine LinearMap.ext fun v => funext fun k => ?_
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal, blockMap_apply]
  by_cases hki : k = i
  · subst hki; simp
  · by_cases hkj : k = j
    · subst hkj; simp [hki]
    · simp [hki, hkj]


theorem transvection_mulVec_apply (i j : Fin n) (c : F) (v : Fin n → F) (k : Fin n) :
    (Matrix.transvection i j c *ᵥ v) k = v k + if k = i then c * v j else 0 := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk, Ne.symm hk]

theorem emb_transvection {i j : Fin n} (hij : i ≠ j) (p q : Fin 2) (hpq : p ≠ q) (c : F) :
    emb i j (Matrix.transvection p q c) = Matrix.transvection (![i, j] p) (![i, j] q) c := by
  have hji : j ≠ i := hij.symm
  unfold emb
  rw [← LinearMap.toMatrix'_toLin' (Matrix.transvection (![i, j] p) (![i, j] q) c)]
  congr 1
  refine LinearMap.ext fun v => funext fun k => ?_
  rw [Matrix.toLin'_apply, transvection_mulVec_apply, blockMap_apply]
  by_cases hki : k = i
  · have hkj : k ≠ j := fun h => hij (hki.symm.trans h)
    subst hki
    fin_cases p <;> fin_cases q <;> simp_all [Matrix.transvection]
  · by_cases hkj : k = j
    · subst hkj
      fin_cases p <;> fin_cases q <;> simp_all [Matrix.transvection, add_comm]
    · fin_cases p <;> fin_cases q <;> simp_all


theorem det_emb {i j : Fin n} (hij : i ≠ j) (B : Matrix (Fin 2) (Fin 2) F) :
    (emb i j B).det = B.det := by
  refine Matrix.diagonal_transvection_induction (fun B => (emb i j B).det = B.det) B ?_ ?_ ?_
  · intro D _
    show (emb i j (Matrix.diagonal D)).det = (Matrix.diagonal D).det
    rw [emb_diagonal hij, Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_two]
    rw [Fintype.prod_eq_mul i j hij (fun x hx => by simp [hx.1, hx.2])]
    simp [Ne.symm hij]
  · rintro ⟨p, q, hpq, c⟩
    simp only [Matrix.TransvectionStruct.toMatrix_mk]
    have hne : ![i, j] p ≠ ![i, j] q := by
      fin_cases p <;> fin_cases q <;> simp_all [Ne.symm hij]
    rw [emb_transvection hij p q hpq, Matrix.det_transvection_of_ne _ _ hne c,
      Matrix.det_transvection_of_ne _ _ hpq c]
  · intro A B hA hB
    simp [emb_mul hij, Matrix.det_mul, hA, hB]


@[expose] def Vi (F : Type*) [Field F] (n : ℕ) (i : Fin n) : Submodule F (Fin n → F) :=
  Submodule.span F {Pi.single i 1}

@[expose] def Vhat (F : Type*) [Field F] (n : ℕ) (j : Fin n) : Submodule F (Fin n → F) :=
  ⨆ k : {k : Fin n // k ≠ j}, Vi F n k

theorem mem_Vi {i : Fin n} {v : Fin n → F} : v ∈ Vi F n i ↔ ∀ k, k ≠ i → v k = 0 := by
  unfold Vi
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩ k hk
    simp [hk]
  · intro h
    refine ⟨v i, ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk, h k hk]

theorem mem_Vhat {j : Fin n} {v : Fin n → F} : v ∈ Vhat F n j ↔ v j = 0 := by
  unfold Vhat
  constructor
  · intro hv
    induction hv using Submodule.iSup_induction' with
    | mem k x hx => exact mem_Vi.1 hx j (Ne.symm k.2)
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
  · intro hv
    have hsum : v = ∑ k : Fin n, Pi.single k (v k) := (Finset.univ_sum_single v).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k = j
    · subst hk; simp [hv]
    · exact Submodule.mem_iSup_of_mem (⟨k, hk⟩ : {k : Fin n // k ≠ j})
        (mem_Vi.2 fun m hm => by simp [hm])

theorem mem_Vij {i j : Fin n} (hij : i ≠ j) {v : Fin n → F} :
    v ∈ Vi F n i ⊔ Vi F n j ↔ ∀ k, k ≠ i → k ≠ j → v k = 0 := by
  constructor
  · intro hv k hki hkj
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    simp [mem_Vi.1 ha k hki, mem_Vi.1 hb k hkj]
  · intro h
    have hv : v = Pi.single i (v i) + Pi.single j (v j) := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj, h k hki hkj]
    rw [hv]
    exact Submodule.add_mem_sup (mem_Vi.2 fun m hm => by simp [hm])
      (mem_Vi.2 fun m hm => by simp [hm])

@[expose] def rootGroup (A B : Submodule F (Fin n → F)) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) where
  carrier := {t | (∀ v, t • v - v ∈ A) ∧ ∀ v ∈ B, t • v = v}
  one_mem' := ⟨fun v => by simp, fun v _ => one_smul _ v⟩
  mul_mem' := fun {s t} hs ht => by
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have h1 : (s * t) • v - v = s • (t • v - v) + (s • v - v) := by
        rw [mul_smul, smul_sub]; abel
      rw [h1]
      refine A.add_mem ?_ (hs.1 v)
      have h2 : s • (t • v - v) = (t • v - v) + (s • (t • v - v) - (t • v - v)) := by abel
      rw [h2]
      exact A.add_mem (ht.1 v) (hs.1 _)
    · rw [mul_smul, ht.2 v hv, hs.2 v hv]
  inv_mem' := fun {t} ht => by
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have h1 : t⁻¹ • v - v = -(t • (t⁻¹ • v) - t⁻¹ • v) := by
        rw [smul_inv_smul]; abel
      rw [h1]
      exact A.neg_mem (ht.1 _)
    · have := ht.2 v hv
      rw [inv_smul_eq_iff]
      exact this.symm

theorem mem_rootGroup {A B : Submodule F (Fin n → F)} {t : Matrix.SpecialLinearGroup (Fin n) F} :
    t ∈ rootGroup A B ↔ (∀ v, t • v - v ∈ A) ∧ ∀ v ∈ B, t • v = v := Iff.rfl


theorem smul_eq_mulVec' (A : Matrix.SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    A • v = (A : Matrix (Fin n) (Fin n) F) *ᵥ v := rfl

theorem SL_ext_basis {A B : Matrix.SpecialLinearGroup (Fin n) F}
    (h : ∀ c, A • (Pi.single c 1 : Fin n → F) = B • (Pi.single c 1 : Fin n → F)) : A = B := by
  apply Subtype.ext
  apply Matrix.ext
  intro a c
  have := congrFun (h c) a
  simpa [smul_eq_mulVec', Matrix.mulVec_single_one] using this

theorem T_smul_apply {i j : Fin n} (hij : i ≠ j) (b : F) (v : Fin n → F) (k : Fin n) :
    (Matrix.SpecialLinearGroup.transvection hij b • v) k = v k + if k = i then b * v j else 0 := by
  rw [smul_eq_mulVec', Matrix.SpecialLinearGroup.transvection_coe]
  exact transvection_mulVec_apply i j b v k

theorem T_mem_Rij {i j : Fin n} (hij : i ≠ j) (b : F) :
    Matrix.SpecialLinearGroup.transvection hij b ∈ rootGroup (Vi F n i) (Vhat F n j) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · refine mem_Vi.2 fun k hk => ?_
    simp [T_smul_apply, hk]
  · funext k
    rw [T_smul_apply, mem_Vhat.1 hv]
    simp

theorem mem_Rij_iff {i j : Fin n} (hij : i ≠ j) {t : Matrix.SpecialLinearGroup (Fin n) F} :
    t ∈ rootGroup (Vi F n i) (Vhat F n j) ↔ ∃ b, t = Matrix.SpecialLinearGroup.transvection hij b := by
  constructor
  · intro ht
    refine ⟨(t • (Pi.single j 1 : Fin n → F)) i, SL_ext_basis fun c => ?_⟩
    by_cases hc : c = j
    · subst hc
      funext k
      rw [T_smul_apply]
      have h1 := mem_Vi.1 (ht.1 (Pi.single c 1)) k
      by_cases hk : k = i
      · subst hk
        simp [hij]
      · have := h1 hk
        simp only [Pi.sub_apply] at this
        simp only [hk, ↓reduceIte, add_zero]
        exact sub_eq_zero.1 this
    · have h1 : (Pi.single c 1 : Fin n → F) ∈ Vhat F n j := mem_Vhat.2 (by simp [Ne.symm hc])
      rw [ht.2 _ h1]
      funext k
      rw [T_smul_apply]
      simp [Pi.single_apply, hc]
  · rintro ⟨b, rfl⟩
    exact T_mem_Rij hij b


section G12

variable (F)

@[expose] def Rij (i j : Fin n) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) :=
  rootGroup (Vi F n i) (Vhat F n j)

@[expose] def Lij (i j : Fin n) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) :=
  Rij F i j ⊔ Rij F j i

@[expose] def Vij (i j : Fin n) : Submodule F (Fin n → F) := Vi F n i ⊔ Vi F n j

@[expose] def Vhatij (i j : Fin n) : Submodule F (Fin n → F) := Vhat F n i ⊓ Vhat F n j

@[expose] def commSub (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) : Submodule F (Fin n → F) :=
  Submodule.span F {w | ∃ t ∈ X, ∃ v : Fin n → F, w = t • v - v}

@[expose] def fixSub (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) : Submodule F (Fin n → F) where
  carrier := {v | ∀ t ∈ X, t • v = v}
  zero_mem' := fun t _ => by rw [smul_eq_mulVec', Matrix.mulVec_zero]
  add_mem' := fun {a b} ha hb t ht => by
    have h1 := ha t ht
    have h2 := hb t ht
    rw [smul_eq_mulVec'] at h1 h2 ⊢
    rw [Matrix.mulVec_add, h1, h2]
  smul_mem' := fun c v hv t ht => by
    have h1 := hv t ht
    rw [smul_eq_mulVec'] at h1 ⊢
    rw [Matrix.mulVec_smul, h1]

@[expose] def ptStab (W : Submodule F (Fin n → F)) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) where
  carrier := {A | ∀ v ∈ W, A • v = v}
  one_mem' := fun v _ => one_smul _ v
  mul_mem' := fun {A B} hA hB v hv => by rw [mul_smul, hB v hv, hA v hv]
  inv_mem' := fun {A} hA v hv => by rw [inv_smul_eq_iff]; exact (hA v hv).symm

@[expose] def setStab (W : Submodule F (Fin n → F)) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) where
  carrier := {A | ∀ v, v ∈ W ↔ A • v ∈ W}
  one_mem' := fun v => by simp
  mul_mem' := fun {A B} hA hB v => by rw [hB v, hA (B • v), mul_smul]
  inv_mem' := fun {A} hA v => by
    have := hA (A⁻¹ • v)
    rw [smul_inv_smul] at this
    exact this.symm

variable {F} {i j : Fin n}

theorem Rij_le_rootGroup_bot (W : Submodule F (Fin n → F)) (hW : Vi F n i ≤ W) :
    Rij F i j ≤ rootGroup W ⊥ := by
  intro t ht
  refine ⟨fun v => hW (ht.1 v), fun v hv => ?_⟩
  rw [Submodule.mem_bot] at hv
  subst hv
  simp

theorem commSub_Lij (hij : i ≠ j) : commSub F (Lij F i j) = Vij F i j := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨t, ht, v, rfl⟩
    have hle : Lij F i j ≤ rootGroup (Vij F i j) ⊥ :=
      sup_le (Rij_le_rootGroup_bot _ le_sup_left) (Rij_le_rootGroup_bot _ le_sup_right)
    exact (hle ht).1 v
  · refine sup_le ?_ ?_
    · rw [Vi, Submodule.span_singleton_le_iff_mem]
      refine Submodule.subset_span ⟨Matrix.SpecialLinearGroup.transvection hij 1,
        Subgroup.mem_sup_left (T_mem_Rij hij 1), Pi.single j 1, ?_⟩
      funext k
      simp [T_smul_apply, Pi.single_apply]
    · rw [Vi, Submodule.span_singleton_le_iff_mem]
      refine Submodule.subset_span ⟨Matrix.SpecialLinearGroup.transvection hij.symm 1,
        Subgroup.mem_sup_right (T_mem_Rij hij.symm 1), Pi.single i 1, ?_⟩
      funext k
      simp [T_smul_apply, Pi.single_apply]


theorem fixSub_Lij (hij : i ≠ j) : fixSub F (Lij F i j) = Vhatij F i j := by
  ext v
  constructor
  · intro hv
    have h1 := hv _ (Subgroup.mem_sup_left (T_mem_Rij hij 1))
    have h2 := hv _ (Subgroup.mem_sup_right (T_mem_Rij hij.symm 1))
    have hj : v j = 0 := by
      have := congrFun h1 i
      rw [T_smul_apply] at this
      simpa using this
    have hi : v i = 0 := by
      have := congrFun h2 j
      rw [T_smul_apply] at this
      simpa using this
    exact ⟨mem_Vhat.2 hi, mem_Vhat.2 hj⟩
  · rintro ⟨hvi, hvj⟩ t ht
    have hle : Lij F i j ≤ MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) F) v :=
      sup_le (fun t ht => ht.2 v hvj) (fun t ht => ht.2 v hvi)
    exact hle ht

theorem Rij_le_ptStab_setStab :
    Rij F i j ≤ ptStab F (Vhatij F i j) ⊓ setStab F (Vij F i j) := by
  intro t ht
  refine ⟨fun v hv => ht.2 v hv.2, fun v => ?_⟩
  have h1 : t • v - v ∈ Vij F i j := Submodule.mem_sup_left (ht.1 v)
  constructor
  · intro hv
    have := (Vij F i j).add_mem hv h1
    simpa using this
  · intro hv
    have := (Vij F i j).sub_mem hv h1
    simpa using this

@[expose] noncomputable def embSL (hij : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin n) F where
  toFun B := ⟨emb i j B, by rw [det_emb hij, B.2]⟩
  map_one' := by apply Subtype.ext; simp [emb_one]
  map_mul' := fun B B' => by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact emb_mul hij _ _

theorem embSL_coe (hij : i ≠ j) (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (embSL hij B : Matrix (Fin n) (Fin n) F) = emb i j B := rfl

theorem embSL_mem_Lij (hij : i ≠ j) (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    embSL hij B ∈ Lij F i j := by
  refine Matrix.SL2.transvection_induction (fun B => embSL hij B ∈ Lij F i j)
    ?_ ?_ B
  · intro p q h c
    have hne : ![i, j] p ≠ ![i, j] q := by
      fin_cases p <;> fin_cases q <;> simp_all [Ne.symm hij]
    have key : embSL hij (Matrix.SpecialLinearGroup.transvection h c) =
        Matrix.SpecialLinearGroup.transvection hne c := by
      apply Subtype.ext
      rw [embSL_coe, Matrix.SpecialLinearGroup.transvection_coe]
      exact emb_transvection hij p q h c
    have hp : (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) := by
      fin_cases p <;> fin_cases q <;> first | exact absurd rfl h | simp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [key]
      exact Subgroup.mem_sup_left (T_mem_Rij hij c)
    · rw [key]
      exact Subgroup.mem_sup_right (T_mem_Rij hij.symm c)
  · intro A B hA hB
    rw [map_mul]
    exact Subgroup.mul_mem _ hA hB


theorem emb_apply (i j : Fin n) (B : Matrix (Fin 2) (Fin 2) F) (a c : Fin n) :
    emb i j B a c = blockMap i j B (Pi.single c 1) a := by
  rw [← emb_mulVec]
  simp

theorem SL_apply_eq (A : Matrix.SpecialLinearGroup (Fin n) F) (a c : Fin n) :
    (A • (Pi.single c 1 : Fin n → F)) a = A a c := by
  simp [smul_eq_mulVec']

theorem single_mem_Vhatij {c : Fin n} (hci : c ≠ i) (hcj : c ≠ j) :
    (Pi.single c 1 : Fin n → F) ∈ Vhatij F i j :=
  ⟨mem_Vhat.2 (by simp [Ne.symm hci]), mem_Vhat.2 (by simp [Ne.symm hcj])⟩

theorem single_mem_Vij_left : (Pi.single i 1 : Fin n → F) ∈ Vij F i j :=
  Submodule.mem_sup_left (mem_Vi.2 fun k hk => by simp [hk])

theorem single_mem_Vij_right : (Pi.single j 1 : Fin n → F) ∈ Vij F i j :=
  Submodule.mem_sup_right (mem_Vi.2 fun k hk => by simp [hk])

theorem exists_embSL_eq (hij : i ≠ j) {A : Matrix.SpecialLinearGroup (Fin n) F}
    (hA : A ∈ ptStab F (Vhatij F i j) ⊓ setStab F (Vij F i j)) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) F, A = embSL hij B := by
  have hji : j ≠ i := hij.symm
  set B0 : Matrix (Fin 2) (Fin 2) F := !![A i i, A i j; A j i, A j j] with hB0
  have hmat : (A : Matrix (Fin n) (Fin n) F) = emb i j B0 := by
    refine Matrix.ext fun a c => ?_
    rw [emb_apply, ← SL_apply_eq, blockMap_apply]
    by_cases hci : c = i
    · subst hci
      have hmem := (mem_Vij hij).1 ((hA.2 _).1 (single_mem_Vij_left))
      by_cases hac : a = c
      · subst hac; simp [B0, SL_apply_eq, hji]
      · by_cases haj : a = j
        · subst haj; simp [B0, SL_apply_eq, hac]
        · simp [hac, haj, hmem a hac haj]
    · by_cases hcj : c = j
      · subst hcj
        have hmem := (mem_Vij hij).1 ((hA.2 _).1 (single_mem_Vij_right))
        by_cases hac : a = i
        · subst hac; simp [B0, SL_apply_eq, hij]
        · by_cases haj : a = c
          · subst haj; simp [B0, SL_apply_eq, hac]
          · simp [hac, haj, hmem a hac haj]
      · have h1 := hA.1 (Pi.single c 1) (single_mem_Vhatij hci hcj)
        rw [h1]
        by_cases hai : a = i
        · subst hai; simp [Ne.symm hci, Ne.symm hcj]
        · by_cases haj : a = j
          · subst haj; simp [Ne.symm hci, Ne.symm hcj, hai]
          · simp [hai, haj]
  have hdet : B0.det = 1 := by
    rw [← det_emb hij, ← hmat]
    exact A.2
  exact ⟨⟨B0, hdet⟩, Subtype.ext hmat⟩


theorem Vhatij_comm (i j : Fin n) : Vhatij F j i = Vhatij F i j := inf_comm _ _

theorem Vij_comm (i j : Fin n) : Vij F j i = Vij F i j := sup_comm _ _

theorem Lij_eq (hij : i ≠ j) :
    Lij F i j = ptStab F (Vhatij F i j) ⊓ setStab F (Vij F i j) := by
  apply le_antisymm
  · refine sup_le Rij_le_ptStab_setStab ?_
    have := Rij_le_ptStab_setStab (F := F) (i := j) (j := i)
    rwa [Vhatij_comm, Vij_comm] at this
  · intro A hA
    obtain ⟨B, rfl⟩ := exists_embSL_eq hij hA
    exact embSL_mem_Lij hij B

theorem emb_apply_idx (hij : i ≠ j) (B : Matrix (Fin 2) (Fin 2) F) (p q : Fin 2) :
    emb i j B (![i, j] p) (![i, j] q) = B p q := by
  rw [emb_apply, blockMap_apply]
  fin_cases p <;> fin_cases q <;> simp [hij, hij.symm]

theorem embSL_injective (hij : i ≠ j) : Function.Injective (embSL (F := F) hij) := by
  intro B B' h
  apply Subtype.ext
  apply Matrix.ext
  intro p q
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin n) F =>
    (A : Matrix (Fin n) (Fin n) F) (![i, j] p) (![i, j] q)) h
  simpa only [embSL_coe, emb_apply_idx hij] using this

theorem Lij_mulEquiv (hij : i ≠ j) :
    Nonempty (Lij F i j ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hrange : (embSL (F := F) hij).range = Lij F i j := by
    apply le_antisymm
    · rintro _ ⟨B, rfl⟩
      exact embSL_mem_Lij hij B
    · intro A hA
      have hA' : A ∈ ptStab F (Vhatij F i j) ⊓ setStab F (Vij F i j) := by
        rw [← Lij_eq hij]; exact hA
      obtain ⟨B, rfl⟩ := exists_embSL_eq hij hA'
      exact ⟨B, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective (embSL_injective hij)).symm⟩


theorem SL_ext_vec {A B : Matrix.SpecialLinearGroup (Fin n) F} (h : ∀ v : Fin n → F, A • v = B • v) : A = B :=
  SL_ext_basis fun _ => h _

theorem T_comm {i m j : Fin n} (him : i ≠ m) (hmj : m ≠ j) (hij : i ≠ j) (a b : F) :
    Matrix.SpecialLinearGroup.transvection him a * Matrix.SpecialLinearGroup.transvection hmj b *
        (Matrix.SpecialLinearGroup.transvection him a)⁻¹ *
        (Matrix.SpecialLinearGroup.transvection hmj b)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (a * b) := by
  rw [Matrix.SpecialLinearGroup.transvection_inv him a, Matrix.SpecialLinearGroup.transvection_inv hmj b]
  refine SL_ext_vec fun v => funext fun k => ?_
  simp only [mul_smul, T_smul_apply]
  have hmi : m ≠ i := him.symm
  have hjm : j ≠ m := hmj.symm
  have hji : j ≠ i := hij.symm
  by_cases hki : k = i
  · subst hki; simp [him, hmi, hji, hjm]; ring
  · by_cases hkm : k = m
    · subst hkm; simp [hmi, hji, hjm]
    · by_cases hkj : k = j
      · subst hkj; simp [hki, hkm]
      · simp [hki, hkm]


variable (F) in
@[expose] def Ladj (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) :=
  ⨆ (k : ℕ) (hk : k + 1 < n), Lij F (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩

theorem Lij_le_Ladj (k : ℕ) (hk : k + 1 < n) :
    Lij F (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ ≤ Ladj F n :=
  le_iSup₂ (f := fun (k : ℕ) (hk : k + 1 < n) => Lij F (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩) k hk

theorem Lij_le_Ladj' (i j : Fin n) (hj : j.val = i.val + 1) : Lij F i j ≤ Ladj F n := by
  rcases i with ⟨k, hk⟩
  rcases j with ⟨l, hl⟩
  simp only at hj
  subst hj
  exact Lij_le_Ladj k hl

theorem T_mem_Ladj_aux :
    ∀ (d : ℕ) (i j : Fin n), j.val = i.val + d + 1 → ∀ (hij : i ≠ j) (a : F),
      Matrix.SpecialLinearGroup.transvection hij a ∈ Ladj F n ∧
      Matrix.SpecialLinearGroup.transvection hij.symm a ∈ Ladj F n := by
  intro d
  induction d with
  | zero =>
    intro i j hj hij a
    have hj' : j.val = i.val + 1 := by omega
    exact ⟨Lij_le_Ladj' i j hj' (Subgroup.mem_sup_left (T_mem_Rij hij a)),
      Lij_le_Ladj' i j hj' (Subgroup.mem_sup_right (T_mem_Rij hij.symm a))⟩
  | succ d ih =>
    intro i j hj hij a
    set m : Fin n := ⟨i.val + 1, by omega⟩ with hm
    have hmv : m.val = i.val + 1 := rfl
    have him : i ≠ m := fun h => by have := congrArg Fin.val h; simp [hmv] at this
    have hmj : m ≠ j := fun h => by have := congrArg Fin.val h; simp [hmv] at this; omega
    have hxy := ih m j (by omega) hmj 1
    have hx : Matrix.SpecialLinearGroup.transvection him a ∈ Ladj F n :=
      Lij_le_Ladj' i m hmv (Subgroup.mem_sup_left (T_mem_Rij him a))
    have hx' : Matrix.SpecialLinearGroup.transvection him.symm 1 ∈ Ladj F n :=
      Lij_le_Ladj' i m hmv (Subgroup.mem_sup_right (T_mem_Rij him.symm 1))
    have hy := (ih m j (by omega) hmj a).2
    constructor
    · have := T_comm him hmj hij a 1
      rw [mul_one] at this
      rw [← this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hxy.1)
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hxy.1)
    · have := T_comm hmj.symm him.symm hij.symm a 1
      rw [mul_one] at this
      rw [← this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hx')
        (Subgroup.inv_mem _ hy)) (Subgroup.inv_mem _ hx')

theorem T_mem_Ladj (i j : Fin n) (hij : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup.transvection hij a ∈ Ladj F n := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact (T_mem_Ladj_aux (j.val - i.val - 1) i j (by omega) hij a).1
  · have := (T_mem_Ladj_aux (i.val - j.val - 1) j i (by omega) hij.symm a).2
    exact this


theorem Lij_le_Ladj_of_ne (hij : i ≠ j) : Lij F i j ≤ Ladj F n := by
  refine sup_le (fun t ht => ?_) (fun t ht => ?_)
  · obtain ⟨b, rfl⟩ := (mem_Rij_iff hij).1 ht
    exact T_mem_Ladj i j hij b
  · obtain ⟨b, rfl⟩ := (mem_Rij_iff hij.symm).1 ht
    exact T_mem_Ladj j i hij.symm b

theorem Ladj_eq_top (hn : 2 ≤ n) : Ladj F n = ⊤ := by
  have : Nontrivial (Fin n) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  rw [eq_top_iff]
  intro M _
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun M => M ∈ Ladj F n) M ?_ ?_ ?_
  · intro i j hij c hc
    have : Matrix.SpecialLinearGroup.diag2n hij c hc =
        embSL hij (Matrix.SpecialLinearGroup.diag2 c hc) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.diag2n_coe, embSL_coe, Matrix.SpecialLinearGroup.diag2_coe,
        emb_diagonal hij]
    rw [this]
    exact Lij_le_Ladj_of_ne hij (embSL_mem_Lij hij _)
  · exact fun i j hij a => T_mem_Ladj i j hij a
  · exact fun A B hA hB => Subgroup.mul_mem _ hA hB

end G12

end CFSG.Quasithin.G1
