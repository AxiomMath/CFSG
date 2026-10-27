module

public import CFSG.RankThree.Chevalley.SteinbergCEF4LatticeTools

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace
  CFSG.LieType.Steinberg.Adjoint

namespace F4Weyl

theorem even_card_of_mul_self_eq_neg_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℤ} (h : M * M = -1) : Even (Fintype.card ι) := by
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hdet
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow] at hdet
  nlinarith [sq_nonneg M.det]

theorem submatrix_val_mul_of_vanish {n : Type*} [Fintype n] [DecidableEq n] {J : Set n}
    [DecidablePred (· ∈ J)] {A B : Matrix n n ℤ}
    (hB : ∀ k, k ∉ J → ∀ j ∈ J, B k j = 0) :
    (A * B).submatrix (Subtype.val : J → n) (Subtype.val : J → n) =
      A.submatrix (Subtype.val : J → n) (Subtype.val : J → n) *
        B.submatrix (Subtype.val : J → n) (Subtype.val : J → n) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ J)]
  have h0 : ∑ k : {k // k ∉ J}, A i k * B k j = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hB k.1 k.2 j.1 j.2, mul_zero]
  rw [h0, add_zero]

theorem even_card_of_smul_smul_eq_neg {τ : Tag} {w : WeylGroup τ} {J : Set (Fin τ.rank)}
    (hJ : ∀ j ∈ J, ∀ i ∉ J, (w • (Pi.single j 1 : Fin τ.rank → ℤ)) i = 0)
    (hsq : ∀ x : Fin τ.rank → ℤ, w • (w • x) = -x) : Even (Nat.card J) := by
  classical
  have hM : weylMatrix (w * w) = -1 := by
    ext i j
    rw [weylMatrix_apply, mul_smul, hsq, Pi.neg_apply, Matrix.neg_apply, Matrix.one_apply,
      Pi.single_apply]
  have h := submatrix_val_mul_of_vanish (A := weylMatrix w) (B := weylMatrix w) (J := J)
    fun k hk j hj => by rw [weylMatrix_apply]; exact hJ j hj k hk
  rw [← weylMatrix_mul, hM] at h
  have h1 : (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ).submatrix (Subtype.val : J → Fin τ.rank)
      (Subtype.val : J → Fin τ.rank) = -1 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.neg_apply, Matrix.one_apply, Subtype.ext_iff]
  rw [h1] at h
  rw [Nat.card_eq_fintype_card]
  exact even_card_of_mul_self_eq_neg_one h.symm

@[expose] def f4OrderFourMatrix : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![1, 0, 0, -1; 2, 1, -1, -1; 2, 2, -1, -2; 2, 0, 0, -1]

theorem weylMatrix_f4OrderFour : weylMatrix (f4Coxeter ^ 3) = f4OrderFourMatrix := by
  rw [f4Coxeter_pow, weylMatrix_f4WordProd]
  decide

theorem f4OrderFourMatrix_mul_self : f4OrderFourMatrix * f4OrderFourMatrix = -1 := by
  decide

theorem f4OrderFour_smul_smul (x : Fin Tag.F4.rank → ℤ) :
    (f4Coxeter ^ 3) • ((f4Coxeter ^ 3) • x) = -x := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_f4OrderFour, Matrix.mulVec_mulVec,
    f4OrderFourMatrix_mul_self, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem orderOf_f4OrderFour : orderOf (f4Coxeter ^ 3) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : weylMatrix ((f4Coxeter ^ 3) ^ 2) = -1 := by
    rw [weylMatrix_pow, weylMatrix_f4OrderFour, sq, f4OrderFourMatrix_mul_self]
  have hne : (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) ≠ 1 := by
    decide
  refine (orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_).trans (by norm_num)
  · intro h
    rw [pow_one] at h
    apply hne
    rw [← h2, h, weylMatrix_one]
  · apply weylMatrix_injective
    rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, weylMatrix_pow, h2, weylMatrix_one,
      neg_one_sq]

@[expose] def f4OrderFourCyclic : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  ![Pi.single (f4Index 2) 1, (f4Coxeter ^ 3) • Pi.single (f4Index 2) 1, Pi.single (f4Index 3) 1,
    (f4Coxeter ^ 3) • Pi.single (f4Index 3) 1]

theorem det_f4OrderFourCyclic : (Matrix.of fun i j => f4OrderFourCyclic j i).det = 1 := by
  rw [← detLaplace_eq_det, f4OrderFourCyclic, f4Coxeter_pow, f4WordProd_smul, f4WordProd_smul]
  decide

theorem linearIndependent_f4OrderFourCyclic_and_span_eq_top :
    LinearIndependent ℤ f4OrderFourCyclic ∧
      Submodule.span ℤ (Set.range f4OrderFourCyclic) = ⊤ := by
  rw [(Pi.basisFun ℤ (Fin Tag.F4.rank)).is_basis_iff_det, Module.Basis.det_apply]
  have h : (Pi.basisFun ℤ (Fin Tag.F4.rank)).toMatrix f4OrderFourCyclic =
      Matrix.of fun i j => f4OrderFourCyclic j i := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.of_apply]
  rw [h, det_f4OrderFourCyclic]
  exact isUnit_one

@[expose] def IsOrderFourColumns (J : Finset (Fin Tag.F4.rank))
    (c : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) : Prop :=
  (∀ i ∈ J, colMap c (c i) = -Pi.single i 1 ∧
      iform (c i) (c i) = iform (Pi.single i 1 : Fin Tag.F4.rank → ℤ) (Pi.single i 1)) ∧
    ∀ β ∈ parabolicRootList J, colMap c β ∈ parabolicRootList J

instance decidableIsOrderFourColumns (J : Finset (Fin Tag.F4.rank))
    (c : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) : Decidable (IsOrderFourColumns J c) := by
  delta IsOrderFourColumns
  infer_instance

theorem order_four_restriction_check :
    ∀ J : Finset (Fin Tag.F4.rank), J.card = 2 →
      ∀ c ∈ colCandidates J, IsOrderFourColumns J c →
        J = {f4Index 1, f4Index 2} ∧
          (c = (fun i => if i ∈ J then f4WordAct [1, 2] (Pi.single i 1) else 0) ∨
            c = (fun i => if i ∈ J then f4WordAct [2, 1] (Pi.single i 1) else 0)) := by
  decide +kernel

theorem eq_B2_of_preserves_of_smul_smul_eq_neg {J : Finset (Fin Tag.F4.rank)}
    {w : WeylGroup .F4} (hJ : J.Nonempty) (hJu : J ≠ Finset.univ)
    (hpres : ∀ β ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)),
      w • β ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)))
    (hsq : ∀ x : Fin Tag.F4.rank → ℤ, w • (w • x) = -x) :
    J = {f4Index 1, f4Index 2} ∧
      ((∀ β ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)), w • β = f4WordProd [1, 2] • β) ∨
        ∀ β ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)), w • β = f4WordProd [2, 1] • β) := by
  classical
  have hsingle : ∀ i ∈ J,
      (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)) :=
    fun i hi => ⟨isRoot_single .F4 i, fun k hk => by
      rw [Pi.single_apply, ite_eq_right]
      rintro rfl
      exact hk hi⟩
  have hcol : ∀ i ∈ J, restrCols J w i = w • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) :=
    fun i hi => by rw [restrCols, ite_eq_left hi]
  have heven : Even J.card := by
    have h := even_card_of_smul_smul_eq_neg (J := (J : Set (Fin Tag.F4.rank)))
      (fun j hj i hi => (hpres _ (hsingle j hj)).2 i hi) hsq
    rwa [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h
  have hcard : J.card = 2 := by
    have h1 : 0 < J.card := Finset.card_pos.2 hJ
    have h2 := (Finset.card_lt_iff_ne_univ J).2 hJu
    rw [Fintype.card_fin] at h2
    have h4 : Tag.F4.rank = 4 := rfl
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨hJ12, hc⟩ := order_four_restriction_check J hcard (restrCols J w)
    (restrCols_mem_colCandidates hpres)
    ⟨fun i hi => ⟨by
      rw [hcol i hi, ← smul_eq_colMap_restrCols J w (hpres _ (hsingle i hi)).2, hsq],
      by rw [hcol i hi, iform_smul]⟩,
    fun β hβ => by
      rw [mem_parabolicRootList] at hβ ⊢
      rw [← smul_eq_colMap_restrCols J w hβ.2]
      exact hpres β hβ⟩
  refine ⟨hJ12, ?_⟩
  rw [← restrCols_f4WordProd, ← restrCols_f4WordProd] at hc
  rcases hc with hc | hc
  · refine Or.inl fun β hβ => ?_
    rw [smul_eq_colMap_restrCols J w hβ.2, hc, ← smul_eq_colMap_restrCols J _ hβ.2]
  · refine Or.inr fun β hβ => ?_
    rw [smul_eq_colMap_restrCols J w hβ.2, hc, ← smul_eq_colMap_restrCols J _ hβ.2]

theorem ncard_parabolicRoots_B2 :
    (parabolicRoots .F4 ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank))).ncard = 8 := by
  have h : (parabolicRootList {f4Index 1, f4Index 2}).toFinset.card = 8 := by decide
  rw [← h, ← Set.ncard_coe_finset, ← parabolicRoots_eq_toFinset, coe_pair_finset]

theorem ncard_parabolicRoots_B2_iform {k : ℤ} (hk : k = 4 ∨ k = 2) :
    {α ∈ parabolicRoots .F4 ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)) |
      iform α α = k}.ncard = 4 := by
  have h : ((parabolicRootList {f4Index 1, f4Index 2}).toFinset.filter
      fun α => iform α α = k).card = 4 := by
    rcases hk with rfl | rfl <;> decide
  have e2 : {α ∈ (↑(parabolicRootList {f4Index 1, f4Index 2}).toFinset :
      Set (Fin Tag.F4.rank → ℤ)) | iform α α = k} =
      ↑((parabolicRootList {f4Index 1, f4Index 2}).toFinset.filter fun α => iform α α = k) :=
    (Finset.coe_filter _ _).symm
  rw [← coe_pair_finset, parabolicRoots_eq_toFinset, e2, Set.ncard_coe_finset, h]

theorem exists_smul_charRootKernel_eq_B2_of_f4OrderFour {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    {b : (ZMod p)ˣ} {v : Fin Tag.F4.rank → ZMod p} (hv : v ≠ 0)
    (hwv : (dualMatrix (ZMod p) (f4Coxeter ^ 3)).mulVec v = (b : ZMod p) • v)
    (hne : (charRootKernel v).Nonempty) :
    ∃ u : WeylGroup .F4,
      (fun α => u • α) '' charRootKernel v =
        parabolicRoots .F4 ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)) ∧
      ((∀ β ∈ parabolicRoots .F4 ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)),
          (u * f4Coxeter ^ 3 * u⁻¹) • β = f4WordProd [1, 2] • β) ∨
        ∀ β ∈ parabolicRoots .F4 ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)),
          (u * f4Coxeter ^ 3 * u⁻¹) • β = f4WordProd [2, 1] • β) := by
  obtain ⟨u, J, hJ, hu⟩ := exists_smul_charRootKernel_eq_parabolicRoots hp3 hv
  obtain ⟨J, rfl⟩ := J.toFinite.exists_finset_coe
  have hpres := conj_smul_mem_parabolicRoots
    (fun α hα => (smul_mem_charRootKernel_iff hwv α).2 hα) hu
  have hsq : ∀ x : Fin Tag.F4.rank → ℤ,
      (u * f4Coxeter ^ 3 * u⁻¹) • ((u * f4Coxeter ^ 3 * u⁻¹) • x) = -x := by
    intro x
    have h := conj_quadratic (w := f4Coxeter ^ 3) (a := 1) (b := 0) (c := 1)
      (fun y => by rw [one_smul, zero_smul, add_zero, one_smul, f4OrderFour_smul_smul,
        neg_add_cancel]) u x
    rw [one_smul, zero_smul, add_zero, one_smul] at h
    exact eq_neg_of_add_eq_zero_left h
  have hJne : J.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, parabolicRoots_empty, Set.image_eq_empty] at hu
    exact hne.ne_empty hu
  have hJu : J ≠ Finset.univ := fun h => hJ (by rw [h, Finset.coe_univ])
  obtain ⟨rfl, h⟩ := eq_B2_of_preserves_of_smul_smul_eq_neg hJne hJu hpres hsq
  rw [coe_pair_finset] at hu h
  exact ⟨u, hu, h⟩

theorem ncard_charRootKernel_of_smul_eq_B2 {p : ℕ} {v : Fin Tag.F4.rank → ZMod p}
    {u : WeylGroup .F4}
    (hu : (fun α => u • α) '' charRootKernel v =
      parabolicRoots .F4 ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank))) :
    (charRootKernel v).ncard = 8 ∧
      {α ∈ charRootKernel v | iform α α = 4}.ncard = 4 ∧
      {α ∈ charRootKernel v | iform α α = 2}.ncard = 4 := by
  have hinj : Function.Injective fun α : Fin Tag.F4.rank → ℤ => u • α := MulAction.injective u
  have himage : ∀ k : ℤ, (fun α => u • α) '' {α ∈ charRootKernel v | iform α α = k} =
      {α ∈ parabolicRoots .F4 ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)) |
        iform α α = k} := by
    intro k
    rw [← hu]
    ext γ
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨α, ⟨hα, hk⟩, rfl⟩
      exact ⟨⟨α, hα, rfl⟩, by rw [iform_smul, hk]⟩
    · rintro ⟨⟨α, hα, rfl⟩, hk⟩
      exact ⟨α, ⟨hα, by rwa [iform_smul] at hk⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← Set.ncard_image_of_injective _ hinj, hu, ncard_parabolicRoots_B2]
  · rw [← Set.ncard_image_of_injective _ hinj, himage, ncard_parabolicRoots_B2_iform (Or.inl rfl)]
  · rw [← Set.ncard_image_of_injective _ hinj, himage, ncard_parabolicRoots_B2_iform (Or.inr rfl)]

end F4Weyl

open F4Weyl

theorem F4_order_four_Weyl_lattice_and_surviving_B2_kernels :
    weylMatrix (τ := .F4) (f4Coxeter ^ 3) =
      !![1, 0, 0, -1; 2, 1, -1, -1; 2, 2, -1, -2; 2, 0, 0, -1] ∧
    weylMatrix (f4Coxeter ^ 3) ^ 2 = -1 ∧
    orderOf (f4Coxeter ^ 3) = 4 ∧
    (LinearIndependent ℤ f4OrderFourCyclic ∧
      Submodule.span ℤ (Set.range f4OrderFourCyclic) = ⊤ ∧
      (Matrix.of fun i j => f4OrderFourCyclic j i).det = 1) ∧
    ∀ {p : ℕ}, p.Prime → 3 < p → ∀ b : (ZMod p)ˣ, orderOf b = 4 →
      ∀ v : Fin Tag.F4.rank → ZMod p, v ≠ 0 →
        (dualMatrix (ZMod p) (f4Coxeter ^ 3)).mulVec v = (b : ZMod p) • v →
        (charRootKernel v = ∅ ∨
          ∃ (u : WeylGroup .F4) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
            (fun α => u • α) '' charRootKernel v = parabolicRoots .F4 {f4Index 1, f4Index 2} ∧
            ∀ y ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {f4Index 1, f4Index 2}),
              weylAct .F4 (u * f4Coxeter ^ 3 * u⁻¹) y =
                weylAct .F4 ((simple .F4 (f4Index 1) * simple .F4 (f4Index 2)) ^ ε) y) ∧
        ((charRootKernel v).Nonempty →
          (charRootKernel v).ncard = 8 ∧
            {α ∈ charRootKernel v | iform α α = 4}.ncard = 4 ∧
            {α ∈ charRootKernel v | iform α α = 2}.ncard = 4) := by
  refine ⟨weylMatrix_f4OrderFour, ?_, orderOf_f4OrderFour,
    ⟨linearIndependent_f4OrderFourCyclic_and_span_eq_top.1,
      linearIndependent_f4OrderFourCyclic_and_span_eq_top.2, det_f4OrderFourCyclic⟩, ?_⟩
  · rw [weylMatrix_f4OrderFour, sq, f4OrderFourMatrix_mul_self]
  intro p hp hp3 b _ v hv hwv
  have : Fact p.Prime := ⟨hp⟩
  have hB2 := exists_smul_charRootKernel_eq_B2_of_f4OrderFour hp3 hv hwv
  refine ⟨?_, fun hne => ?_⟩
  · rcases (charRootKernel v).eq_empty_or_nonempty with h | hne
    · exact Or.inl h
    obtain ⟨u, hu, h⟩ := hB2 hne
    refine Or.inr ?_
    rcases h with h | h
    · refine ⟨u, 1, Or.inl rfl, hu, weylAct_eqOn_span fun β hβ => ?_⟩
      rw [h β hβ, zpow_one, f4WordProd_pair]
    · refine ⟨u, -1, Or.inr rfl, hu, weylAct_eqOn_span fun β hβ => ?_⟩
      rw [h β hβ, zpow_neg_one, ← f4WordProd_pair, inv_f4WordProd_pair]
  · obtain ⟨u, hu, -⟩ := hB2 hne
    exact ncard_charRootKernel_of_smul_eq_B2 hu

end CFSG.RankThree.Chevalley
