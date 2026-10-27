module

public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.Quasithin.EmptyFaithful.SzN2Sp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SzN15

section Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6

variable {K : Type} [Field K]

noncomputable def elemSL (i j : Fin 3) (hij : i ≠ j) (c : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

theorem elemSL_mulVec (i j : Fin 3) (hij : i ≠ j) (c : K) (v : Fin 3 → K) :
    ((elemSL i j hij c : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      v + (c * v j) • (Pi.single i (1 : K) : Fin 3 → K) := by
  show Matrix.transvection i j c *ᵥ v = _
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]

theorem elemSL_mem_unitriangular {i j : Fin 3} (hij : i < j) (c : K) :
    elemSL i j hij.ne c ∈ unitriangular 3 K := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · show (Matrix.transvection i j c) a b = 0
    rw [Matrix.transvection]
    have h1 : a ≠ b := ne_of_gt hab
    have h2 : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hij (not_lt.2 hab.le)
    simp [h1, h2]
  · show (Matrix.transvection i j c) a a = 1
    rw [Matrix.transvection]
    have h2 : ¬ (i = a ∧ j = a) := by
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ hij
    simp [h2]

theorem fixed_unitriangular (v : Fin 3 → K) :
    (∀ A ∈ unitriangular 3 K, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) ↔
      v ∈ flagSpace 3 K 1 := by
  rw [mem_flagSpace]
  constructor
  · intro h j hj
    have hj0 : (0 : Fin 3) < j := by
      rw [Fin.lt_def]
      simp
      omega
    have h1 := h _ (elemSL_mem_unitriangular hj0 (1 : K))
    have h2 := congrFun h1 0
    rw [elemSL_mulVec] at h2
    simpa using h2
  · intro h A hA
    have h1 : v 1 = 0 := h 1 (by simp)
    have h2 : v 2 = 0 := h 2 (by simp)
    ext i
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]
    fin_cases i
    · simp [hA.2 0]
    · have : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := hA.1 1 0 (by decide)
      simp [this, h1]
    · have : (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := hA.1 2 0 (by decide)
      simp [this, h2]

variable (K) in
noncomputable abbrev eSL : SpecialLinearGroup (Fin 3) K ≃* ↥(StatedSL 3 K) :=
  specialLinearGroupEquivStatedSL 3 K

theorem natAct_eSL (A : SpecialLinearGroup (Fin 3) K) (m : Multiplicative (Fin 3 → K)) :
    natAct (StatedSL 3 K) (eSL K A) m =
      Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ (Multiplicative.toAdd m)) := by
  simp [natAct, eSL, specialLinearGroupEquivStatedSL_coe]

theorem fixM_unitriangular :
    fixM (StatedSL 3 K) ((unitriangular 3 K).map (eSL K).toMonoidHom) =
      {m | Multiplicative.toAdd m ∈ flagSpace 3 K 1} := by
  ext m
  change (∀ t ∈ (unitriangular 3 K).map (eSL K).toMonoidHom, natAct (StatedSL 3 K) t m = m) ↔ _
  rw [Set.mem_ofPred_eq, ← fixed_unitriangular]
  constructor
  · intro h A hA
    have := h _ ⟨A, hA, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, natAct_eSL] at this
    exact congrArg Multiplicative.toAdd this
  · intro h t ht
    obtain ⟨A, hA, rfl⟩ := ht
    rw [MulEquiv.coe_toMonoidHom, natAct_eSL, h A hA]
    rfl


theorem inv_mulVec_mulVec (A : SpecialLinearGroup (Fin 3) K) (v : Fin 3 → K) :
    ((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (A : SpecialLinearGroup (Fin 3) K) (v : Fin 3 → K) :
    (A : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp (coe_inv_mul_coe A), Matrix.one_mulVec]

theorem mem_stabilizer_iff_sl3 (W : Submodule K (Fin 3 → K)) (A : SpecialLinearGroup (Fin 3) K) :
    A ∈ stabilizer W ↔ ∀ v, v ∈ W ↔ (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
  constructor
  · intro h v
    have h' : W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) = W := h
    constructor
    · intro hv
      rw [← h']
      exact ⟨v, hv, by simp⟩
    · intro hv
      rw [← h'] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have h1 : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ w = (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
        simpa [mulVecLin_apply] using hwv
      have h2 := congrArg (fun x => ((A⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ x) h1
      simp only [inv_mulVec_mulVec] at h2
      rwa [← h2]
  · intro h
    show W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) = W
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [mulVecLin_apply] using (h v).1 hv
    · intro hw
      have hmem : ((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
        rw [h, mulVec_inv_mulVec]
        exact hw
      exact Submodule.mem_map.2 ⟨_, hmem, by rw [mulVecLin_apply]; exact mulVec_inv_mulVec A w⟩

theorem Qt_unitriangular :
    Qt (StatedSL 3 K) ((unitriangular 3 K).map (eSL K).toMonoidHom) =
      (Q3 K 0).map (eSL K).toMonoidHom := by
  ext γ
  obtain ⟨A, rfl⟩ := (eSL K).surjective γ
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [mem_Qt, fixM_unitriangular]
  have hq : A ∈ Q3 K 0 ↔ ∀ v, v ∈ flagSpace 3 K 1 ↔
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ flagSpace 3 K 1 := mem_stabilizer_iff_sl3 _ A
  rw [hq]
  constructor
  · intro h v
    have := h (Multiplicative.ofAdd v)
    simpa [Set.mem_ofPred_eq, natAct_eSL] using this
  · intro h m
    have := h (Multiplicative.toAdd m)
    simpa [Set.mem_ofPred_eq, natAct_eSL] using this

theorem covBy_Q3_zero [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    (Q3 K 0).map (eSL K).toMonoidHom ⋖ ⊤ := by
  have h := CFSG.Quasithin.SzN2.sl3_residualOvergroupsAt hK
  have h0 : Q3 K 0 ⋖ ⊤ := (h.2.2.1 (Q3 K 0) (h.2.1 0)).2 ⟨0, rfl⟩
  have key : ∀ x y : Subgroup (SpecialLinearGroup (Fin 3) K),
      x.map (eSL K).toMonoidHom ⋖ y.map (eSL K).toMonoidHom ↔ x ⋖ y :=
    fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup (eSL K))
  rw [← Subgroup.map_top_of_surjective (eSL K).toMonoidHom (eSL K).surjective, key]
  exact h0

theorem sl3_Qt_covBy [Finite K] [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    {T : Subgroup ↥(StatedSL 3 K)} (hT : IsSylowTwoOf T ⊤) : Qt (StatedSL 3 K) T ⋖ ⊤ := by
  have hU : IsSylowTwoOf ((unitriangular 3 K).map (eSL K).toMonoidHom) ⊤ := by
    have h := isSylowOf_map_injective (p := 2) (eSL K).toMonoidHom (eSL K).injective
      (isSylowTwoOf_iff_isSylowOf.1 (CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := K)
        (n := 3) (by norm_num)))
    rw [Subgroup.map_top_of_surjective _ (eSL K).surjective] at h
    exact isSylowTwoOf_iff_isSylowOf.2 h
  obtain ⟨k, -, hk⟩ := (CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU) (isSylowTwoOf_iff_isSylowOf.1 hT))
  have hTeq : T = ((unitriangular 3 K).map (eSL K).toMonoidHom).map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simpa [MulAut.conj_symm_apply] using hk x
  rw [hTeq]
  exact covBy_top_Qt_conj _ _ (by rw [Qt_unitriangular]; exact covBy_Q3_zero hK)

end Lin

section Sp

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6

variable {K : Type} [Field K]

theorem isUnitriangular_transvection (c : K) :
    IsUnitriangular (Matrix.transvection (0 : Fin 2) 1 c) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h1 : a ≠ b := ne_of_gt hab
    have h2 : ¬ ((0 : Fin 2) = a ∧ (1 : Fin 2) = b) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hab (by decide)
    rw [Matrix.transvection]
    simp [h1, h2]
  · rw [Matrix.transvection]
    have h2 : ¬ ((0 : Fin 2) = a ∧ (1 : Fin 2) = a) := by
      rintro ⟨h, h'⟩
      rw [← h] at h'
      exact absurd h' (by decide)
    simp [h2]

theorem fixed_unipotent (v : Fin 2 ⊕ Fin 2 → K) :
    (∀ g ∈ unipotent 2 K, ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v)
      ↔ v ∈ isoFlag 2 K 1 := by
  rw [mem_isoFlag]
  have hv : v = Sum.elim (fun j => v (Sum.inl j)) (fun j => v (Sum.inr j)) := by
    funext i; rcases i with i | i <;> rfl
  constructor
  · intro h
    have hy : ∀ j : Fin 2, v (Sum.inr j) = 0 := by
      intro j
      obtain ⟨g, hg, hgm⟩ := exists_mem_unipotent (r := 2) (K := K)
        (A := (1 : Matrix (Fin 2) (Fin 2) K)) (C := Matrix.single j j (1 : K)) isUnitriangular_one
        (by simp [Matrix.transpose_single])
      have h1 := congrFun (h g hg) (Sum.inl j)
      rw [hgm, hv, blockMat, fromBlocks_mulVec] at h1
      simpa [Matrix.single_mulVec_eq, Pi.single_apply] using h1
    refine ⟨hy, fun j hj => ?_⟩
    have hj1 : j = 1 := by
      have : (j : ℕ) < 2 := j.2
      ext
      simp
      omega
    subst hj1
    obtain ⟨g, hg, hgm⟩ := exists_mem_unipotent (r := 2) (K := K)
      (A := Matrix.transvection (0 : Fin 2) 1 (1 : K)) (C := (0 : Matrix (Fin 2) (Fin 2) K))
      (isUnitriangular_transvection 1) (by simp)
    have h1 := congrFun (h g hg) (Sum.inl 0)
    have hy' : (fun j => v (Sum.inr j)) = 0 := funext hy
    rw [hgm, hv, blockMat, fromBlocks_mulVec, hy'] at h1
    simpa [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec_eq] using h1
  · rintro ⟨hy, hx⟩ g hg
    obtain ⟨A, C, hA, hC, hgm⟩ := hg
    have hy' : v ∘ Sum.inr = 0 := funext hy
    have hx1 : v (Sum.inl 1) = 0 := hx 1 (by simp)
    rw [hgm, blockMat, fromBlocks_mulVec, hy']
    funext i
    rcases i with i | i
    · simp only [Matrix.mulVec_zero, add_zero, Sum.elim_inl]
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Function.comp]
      fin_cases i
      · simp [hA.2 0, hx1]
      · have : A 1 0 = 0 := hA.1 (by decide)
        simp [this, hx1]
    · simp [hy i]


abbrev matSp (g : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem inv_mulVec_mulVec_sp (g : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) :
    matSp g⁻¹ *ᵥ (matSp g *ᵥ v) = v := by
  rw [mulVec_mulVec]
  show ((((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *ᵥ v = v
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
    one_mulVec]

theorem mulVec_inv_mulVec_sp (g : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) :
    matSp g *ᵥ (matSp g⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec]
  show (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
    (((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *ᵥ v = v
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
    one_mulVec]

theorem mem_stabilizer_iff_sp (W : Submodule K (Fin 2 ⊕ Fin 2 → K)) (g : StatedSp 2 K) :
    g ∈ stabilizer 2 K W ↔ ∀ v, v ∈ W ↔ matSp g *ᵥ v ∈ W := by
  constructor
  · intro h v
    have h' : W.map (mulVecLin (matSp g)) = W := mem_stabilizer.1 h
    have hinv : W.map (mulVecLin (matSp g⁻¹)) = W := mem_stabilizer.1 ((stabilizer 2 K W).inv_mem h)
    constructor
    · intro hv
      rw [← h']
      exact ⟨v, hv, by simp⟩
    · intro hv
      have h3 : matSp g⁻¹ *ᵥ (matSp g *ᵥ v) ∈ W := by
        rw [← hinv]
        exact ⟨matSp g *ᵥ v, hv, by simp⟩
      rwa [inv_mulVec_mulVec_sp] at h3
  · intro h
    refine mem_stabilizer_of_mulVec_mem (fun v hv => (h v).1 hv) (fun v hv => ?_)
    have h4 := (h (matSp g⁻¹ *ᵥ v)).2
    rw [mulVec_inv_mulVec_sp] at h4
    exact h4 hv


theorem natAct_sp (g : ↥(StatedSp 2 K)) (m : Multiplicative (Fin 2 ⊕ Fin 2 → K)) :
    natAct (StatedSp 2 K) g m = Multiplicative.ofAdd (matSp g *ᵥ Multiplicative.toAdd m) := rfl

theorem fixM_unipotent :
    fixM (StatedSp 2 K) (unipotent 2 K) = {m | Multiplicative.toAdd m ∈ isoFlag 2 K 1} := by
  ext m
  change (∀ t ∈ unipotent 2 K, natAct (StatedSp 2 K) t m = m) ↔ _
  rw [Set.mem_ofPred_eq, ← fixed_unipotent]
  constructor
  · intro h g hg
    exact congrArg Multiplicative.toAdd (h g hg)
  · intro h t ht
    exact congrArg Multiplicative.ofAdd (h t ht)

theorem Qt_unipotent : Qt (StatedSp 2 K) (unipotent 2 K) = Q2 K 0 := by
  ext γ
  rw [mem_Qt, fixM_unipotent]
  have hflag : flag 2 K 1 = isoFlag 2 K 1 := by
    simp [flag]
  have hq : γ ∈ Q2 K 0 ↔ ∀ v, v ∈ isoFlag 2 K 1 ↔ matSp γ *ᵥ v ∈ isoFlag 2 K 1 := by
    have := mem_stabilizer_iff_sp (flag 2 K 1) γ
    rw [hflag] at this
    exact this
  rw [hq]
  constructor
  · intro h v
    have := h (Multiplicative.ofAdd v)
    simpa [Set.mem_ofPred_eq, natAct_sp] using this
  · intro h m
    have := h (Multiplicative.toAdd m)
    simpa [Set.mem_ofPred_eq, natAct_sp] using this

theorem covBy_Q2_zero [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) : Q2 K 0 ⋖ ⊤ := by
  have h := CFSG.Quasithin.SzN2.sp4_residualOvergroupsAt hK
  exact (h.2.2.1 (Q2 K 0) (h.2.1 0)).2 ⟨0, rfl⟩

theorem sp4_Qt_covBy [Finite K] [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    {T : Subgroup ↥(StatedSp 2 K)} (hT : IsSylowTwoOf T ⊤) : Qt (StatedSp 2 K) T ⋖ ⊤ := by
  obtain ⟨k, -, hk⟩ := (CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 (CFSG.Quasithin.SzN2.isSylowTwoOf_unipotent (K := K)))
    (isSylowTwoOf_iff_isSylowOf.1 hT))
  have hTeq : T = (unipotent 2 K).map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simpa [MulAut.conj_symm_apply] using hk x
  rw [hTeq]
  exact covBy_top_Qt_conj _ _ (by rw [Qt_unipotent]; exact covBy_Q2_zero hK)

end Sp

end CFSG.Quasithin.SzN15
