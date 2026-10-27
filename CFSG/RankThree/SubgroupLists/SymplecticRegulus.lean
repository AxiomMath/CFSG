module

public import CFSG.RankThree.SubgroupLists.SymplecticSkewPairs

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def lagInl : Submodule K (V₄ → K) where
  carrier := {v | ∀ i, v (Sum.inr i) = 0}
  add_mem' := by intro a b ha hb i; simp [ha i, hb i]
  zero_mem' := by intro i; simp
  smul_mem' := by intro c a ha i; simp [ha i]

@[expose] def graphLag (M : Matrix (Fin 2) (Fin 2) K) : Submodule K (V₄ → K) where
  carrier := {v | ∀ i, v (Sum.inl i) = (M *ᵥ fun j => v (Sum.inr j)) i}
  add_mem' := by
    intro a b ha hb i
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp only [Pi.add_apply, ha i, hb i]
    rw [show (fun j => a (Sum.inr j) + b (Sum.inr j)) =
      (fun j => a (Sum.inr j)) + (fun j => b (Sum.inr j)) from rfl, Matrix.mulVec_add]
    rfl
  zero_mem' := by intro i; simp [Matrix.mulVec, dotProduct]
  smul_mem' := by
    intro c a ha i
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp only [Pi.smul_apply, smul_eq_mul, ha i]
    rw [show (fun j => c * a (Sum.inr j)) = c • (fun j => a (Sum.inr j)) from rfl,
      Matrix.mulVec_smul]
    rfl

theorem mem_lagInl {v : V₄ → K} : v ∈ lagInl ↔ ∀ i, v (Sum.inr i) = 0 := Iff.rfl

theorem mem_graphLag {M : Matrix (Fin 2) (Fin 2) K} {v : V₄ → K} :
    v ∈ graphLag M ↔ ∀ i, v (Sum.inl i) = (M *ᵥ fun j => v (Sum.inr j)) i := Iff.rfl

@[expose] def mkV (a b : Fin 2 → K) : V₄ → K := Sum.elim a b

omit [Field K] in
@[simp] theorem mkV_inl (a b : Fin 2 → K) (i : Fin 2) : mkV a b (Sum.inl i) = a i := rfl

omit [Field K] in
@[simp] theorem mkV_inr (a b : Fin 2 → K) (i : Fin 2) : mkV a b (Sum.inr i) = b i := rfl

omit [Field K] in
theorem eq_mkV (v : V₄ → K) : v = mkV (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) := by
  ext i; rcases i with i | i <;> rfl

theorem fromBlocks_mulVec_mkV (A B C D : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2 → K) :
    fromBlocks A B C D *ᵥ mkV a b = mkV (A *ᵥ a + B *ᵥ b) (C *ᵥ a + D *ᵥ b) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [mkV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Fin.sum_univ_two]

theorem mkV_mem_graphLag {M : Matrix (Fin 2) (Fin 2) K} (b : Fin 2 → K) :
    mkV (M *ᵥ b) b ∈ graphLag M := by
  intro i; rfl

theorem mem_graphLag_iff {M : Matrix (Fin 2) (Fin 2) K} {v : V₄ → K} :
    v ∈ graphLag M ↔ v = mkV (M *ᵥ fun j => v (Sum.inr j)) (fun j => v (Sum.inr j)) := by
  constructor
  · intro h
    ext i; rcases i with i | i
    · exact h i
    · rfl
  · intro h
    rw [h]
    exact mkV_mem_graphLag _

theorem mkV_mem_lagInl (a : Fin 2 → K) : mkV a 0 ∈ lagInl := by
  intro i; rfl

theorem spForm_mkV (a b a' b' : Fin 2 → K) :
    spForm 2 K (mkV a b) (mkV a' b') = a ⬝ᵥ b' - b ⬝ᵥ a' := by
  rw [spForm_apply]
  simp [mkV, dotProduct, Fin.sum_univ_two]

@[expose] def tGL (M : Matrix (Fin 2) (Fin 2) K) : GL V₄ K where
  val := fromBlocks 1 M 0 1
  inv := fromBlocks 1 (-M) 0 1
  val_inv := by rw [fromBlocks_multiply]; simp
  inv_val := by rw [fromBlocks_multiply]; simp

theorem coe_tGL (M : Matrix (Fin 2) (Fin 2) K) :
    ((tGL M : GL V₄ K) : Matrix V₄ V₄ K) = fromBlocks 1 M 0 1 := rfl

theorem tGL_mulVec (M : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2 → K) :
    ((tGL M : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ mkV a b = mkV (a + M *ᵥ b) b := by
  rw [coe_tGL, fromBlocks_mulVec_mkV]
  simp

theorem tGL_mem {M : Matrix (Fin 2) (Fin 2) K} (hM : Mᵀ = M) : tGL M ∈ StatedSp 2 K := by
  rw [mem_statedSp_iff_preserves]
  intro v w
  rw [eq_mkV v, eq_mkV w, tGL_mulVec, tGL_mulVec, spForm_mkV, spForm_mkV, add_dotProduct,
    dotProduct_add, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM]
  ring

theorem tGL_add (M N : Matrix (Fin 2) (Fin 2) K) : tGL M * tGL N = tGL (M + N) := by
  apply Units.ext
  rw [Units.val_mul, coe_tGL, coe_tGL, coe_tGL, fromBlocks_multiply]
  simp [add_comm]

theorem translate_tGL_graphLag (M N : Matrix (Fin 2) (Fin 2) K) :
    translate (tGL M) (graphLag N) = graphLag (M + N) := by
  ext u
  rw [mem_translate]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_graphLag_iff.mp hw, tGL_mulVec]
    rw [show N *ᵥ (fun j => w (Sum.inr j)) + M *ᵥ (fun j => w (Sum.inr j)) =
      (M + N) *ᵥ (fun j => w (Sum.inr j)) by rw [Matrix.add_mulVec, add_comm]]
    exact mkV_mem_graphLag _
  · intro hu
    refine ⟨mkV (N *ᵥ fun j => u (Sum.inr j)) (fun j => u (Sum.inr j)),
      mkV_mem_graphLag _, ?_⟩
    rw [tGL_mulVec]
    conv_rhs => rw [mem_graphLag_iff.mp hu]
    rw [Matrix.add_mulVec, add_comm]

@[expose] def uGL (M : Matrix (Fin 2) (Fin 2) K) : GL V₄ K where
  val := fromBlocks 1 0 M 1
  inv := fromBlocks 1 0 (-M) 1
  val_inv := by rw [fromBlocks_multiply]; simp
  inv_val := by rw [fromBlocks_multiply]; simp

theorem coe_uGL (M : Matrix (Fin 2) (Fin 2) K) :
    ((uGL M : GL V₄ K) : Matrix V₄ V₄ K) = fromBlocks 1 0 M 1 := rfl

theorem uGL_mulVec (M : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2 → K) :
    ((uGL M : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ mkV a b = mkV a (M *ᵥ a + b) := by
  rw [coe_uGL, fromBlocks_mulVec_mkV]
  simp

theorem mulVec_single_one_apply (X : Matrix V₄ V₄ K) (c r : V₄) :
    (X *ᵥ Pi.single c 1) r = X r c := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem single_inl_mem_lagInl (j : Fin 2) : (Pi.single (Sum.inl j) 1 : V₄ → K) ∈ lagInl := by
  intro i
  simp

theorem single_inr_mem_graphLag_zero (j : Fin 2) :
    (Pi.single (Sum.inr j) 1 : V₄ → K) ∈ graphLag 0 := by
  intro i
  simp [Pi.single_apply]

theorem exists_eq_tGL_of_unipAxis_eq_lagInl {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K)
    (hx : IsSqZero x) (hax : unipAxis x = lagInl) :
    ∃ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S ∧ x = tGL S := by
  classical
  set X := (x : Matrix V₄ V₄ K) with hX
  have hcol : ∀ j r, X r (Sum.inl j) = (Pi.single (Sum.inl j) 1 : V₄ → K) r := by
    intro j r
    have h := mem_unipAxis.mp (hax ▸ single_inl_mem_lagInl j)
    rw [← mulVec_single_one_apply X (Sum.inl j) r, hX, h]
  have hcol' : ∀ i j, X (Sum.inr i) (Sum.inr j) = if i = j then 1 else 0 := by
    intro i j
    have h := (hax ▸ sub_one_mulVec_mem_unipAxis hx (Pi.single (Sum.inr j) 1) :
      ((x : Matrix V₄ V₄ K) - 1) *ᵥ Pi.single (Sum.inr j) 1 ∈ lagInl) i
    rw [Matrix.sub_mulVec, Pi.sub_apply, mulVec_single_one_apply, Matrix.one_mulVec,
      sub_eq_zero] at h
    rw [← hX] at h
    rw [h]
    simp [Pi.single_apply]
  set S : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => X (Sum.inl i) (Sum.inr j) with hS
  have hXS : X = fromBlocks 1 S 0 1 := by
    ext r c
    rcases r with i | i <;> rcases c with j | j
    · rw [hcol j]; simp [Pi.single_apply, Matrix.one_apply]
    · simp [hS]
    · rw [hcol j]; simp
    · rw [hcol']; simp [Matrix.one_apply]
  refine ⟨S, ?_, Units.ext hXS⟩
  ext i j
  have h := spForm_mulVec hxS (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) 1)
  rw [← hX, hXS] at h
  rw [eq_mkV (Pi.single (Sum.inr i) 1 : V₄ → K), eq_mkV (Pi.single (Sum.inr j) 1 : V₄ → K),
    fromBlocks_mulVec_mkV, fromBlocks_mulVec_mkV, spForm_mkV, spForm_mkV] at h
  simp [Pi.single_apply, dotProduct] at h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linear_combination h

theorem exists_eq_uGL_of_unipAxis_eq_graphLag_zero {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K)
    (hx : IsSqZero x) (hax : unipAxis x = graphLag 0) :
    ∃ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S ∧ x = uGL S := by
  classical
  set X := (x : Matrix V₄ V₄ K) with hX
  have hcol : ∀ j r, X r (Sum.inr j) = (Pi.single (Sum.inr j) 1 : V₄ → K) r := by
    intro j r
    have h := mem_unipAxis.mp (hax ▸ single_inr_mem_graphLag_zero j)
    rw [← mulVec_single_one_apply X (Sum.inr j) r, hX, h]
  have hcol' : ∀ i j, X (Sum.inl i) (Sum.inl j) = if i = j then 1 else 0 := by
    intro i j
    have h := (hax ▸ sub_one_mulVec_mem_unipAxis hx (Pi.single (Sum.inl j) 1) :
      ((x : Matrix V₄ V₄ K) - 1) *ᵥ Pi.single (Sum.inl j) 1 ∈ graphLag 0) i
    rw [Matrix.zero_mulVec] at h
    rw [Matrix.sub_mulVec, Pi.sub_apply, mulVec_single_one_apply, Matrix.one_mulVec,
      Pi.zero_apply, sub_eq_zero] at h
    rw [← hX] at h
    rw [h]
    simp [Pi.single_apply]
  set S : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => X (Sum.inr i) (Sum.inl j) with hS
  have hXS : X = fromBlocks 1 0 S 1 := by
    ext r c
    rcases r with i | i <;> rcases c with j | j
    · rw [hcol']; simp [Matrix.one_apply]
    · rw [hcol j]; simp
    · simp [hS]
    · rw [hcol j]; simp [Pi.single_apply, Matrix.one_apply]
  refine ⟨S, ?_, Units.ext hXS⟩
  ext i j
  have h := spForm_mulVec hxS (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1)
  rw [← hX, hXS] at h
  rw [eq_mkV (Pi.single (Sum.inl i) 1 : V₄ → K), eq_mkV (Pi.single (Sum.inl j) 1 : V₄ → K),
    fromBlocks_mulVec_mkV, fromBlocks_mulVec_mkV, spForm_mkV, spForm_mkV] at h
  simp [Pi.single_apply, dotProduct] at h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;>
    first | linear_combination h | linear_combination -h

@[expose] noncomputable def graphMap (M : Matrix (Fin 2) (Fin 2) K) :
    (Fin 2 → K) →ₗ[K] (V₄ → K) where
  toFun b := mkV (M *ᵥ b) b
  map_add' a b := by
    rw [Matrix.mulVec_add]
    ext i; rcases i with i | i <;> rfl
  map_smul' c b := by
    rw [Matrix.mulVec_smul]
    ext i; rcases i with i | i <;> rfl

theorem range_graphMap (M : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.range (graphMap M) = graphLag M := by
  ext v
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨b, rfl⟩
    exact mkV_mem_graphLag b
  · intro hv
    exact ⟨_, (mem_graphLag_iff.mp hv).symm⟩

theorem finrank_graphLag (M : Matrix (Fin 2) (Fin 2) K) : finrank K (graphLag M) = 2 := by
  rw [← range_graphMap, LinearMap.finrank_range_of_inj, Module.finrank_fin_fun]
  intro a b hab
  ext i
  have := congrFun hab (Sum.inr i)
  simpa [graphMap, mkV] using this

theorem graphLag_isotropic_iff (M : Matrix (Fin 2) (Fin 2) K) :
    (∀ u ∈ graphLag M, ∀ v ∈ graphLag M, spForm 2 K u v = 0) ↔ Mᵀ = M := by
  constructor
  · intro h
    ext i j
    have := h _ (mkV_mem_graphLag (Pi.single i 1)) _ (mkV_mem_graphLag (Pi.single j 1))
    rw [spForm_mkV] at this
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at this
    simp only [Matrix.transpose_apply]
    linear_combination this
  · intro hM u hu v hv
    rw [mem_graphLag_iff.mp hu, mem_graphLag_iff.mp hv, spForm_mkV, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hM, dotProduct_comm]
    ring

theorem exists_eq_graphLag {C : Submodule K (V₄ → K)} (hC2 : finrank K C = 2)
    (hCiso : ∀ u ∈ C, ∀ v ∈ C, spForm 2 K u v = 0) (hCL : C ⊓ lagInl = ⊥) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, Mᵀ = M ∧ C = graphLag M := by
  classical
  let πr : (V₄ → K) →ₗ[K] (Fin 2 → K) := LinearMap.funLeft K K Sum.inr
  let πl : (V₄ → K) →ₗ[K] (Fin 2 → K) := LinearMap.funLeft K K Sum.inl
  let π : C →ₗ[K] (Fin 2 → K) := πr ∘ₗ C.subtype
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hcL : (c : V₄ → K) ∈ lagInl := fun i => congrFun hc i
    have : (c : V₄ → K) ∈ C ⊓ lagInl := ⟨c.2, hcL⟩
    rw [hCL] at this
    exact Subtype.ext ((Submodule.mem_bot _).mp this)
  have hsurj : Function.Surjective π := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hinj
    · rw [hC2, Module.finrank_fin_fun]
  let e : C ≃ₗ[K] (Fin 2 → K) := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
  set M : Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrix' (πl ∘ₗ C.subtype ∘ₗ e.symm.toLinearMap)
    with hMdef
  have hle : C ≤ graphLag M := by
    intro c hc i
    have h1 : M *ᵥ (fun j => c (Sum.inr j)) = πl (e.symm (π ⟨c, hc⟩)) := by
      rw [hMdef, LinearMap.toMatrix'_mulVec]
      rfl
    have h2 : e.symm (π ⟨c, hc⟩) = ⟨c, hc⟩ := e.symm_apply_apply ⟨c, hc⟩
    rw [h1, h2]
    rfl
  have hCM : C = graphLag M := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [hC2, finrank_graphLag])
  refine ⟨M, (graphLag_isotropic_iff M).mp ?_, hCM⟩
  rw [← hCM]
  exact hCiso

@[expose] noncomputable def lagMap : (Fin 2 → K) →ₗ[K] (V₄ → K) where
  toFun a := mkV a 0
  map_add' a b := by ext i; rcases i with i | i <;> simp [mkV]
  map_smul' c b := by ext i; rcases i with i | i <;> simp [mkV]

theorem finrank_lagInl : finrank K (lagInl : Submodule K (V₄ → K)) = 2 := by
  have hrange : LinearMap.range (lagMap (K := K)) = lagInl := by
    ext v
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact mkV_mem_lagInl a
    · intro hv
      refine ⟨fun i => v (Sum.inl i), ?_⟩
      ext i; rcases i with i | i
      · rfl
      · exact (hv i).symm
  rw [← hrange, LinearMap.finrank_range_of_inj, Module.finrank_fin_fun]
  intro a b hab
  ext i
  have := congrFun hab (Sum.inl i)
  simpa [lagMap, mkV] using this

theorem orth_eq_self_of_isotropic {A : Submodule K (V₄ → K)} (hA2 : finrank K A = 2)
    (hAiso : ∀ u ∈ A, ∀ v ∈ A, spForm 2 K u v = 0) : orth A = A := by
  have hle : A ≤ orth A := fun v hv => mem_orth.mpr fun u hu => hAiso u hu v hv
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_orth, hA2])).symm

theorem gram_entry (M : Matrix V₄ V₄ K) (k l : V₄) :
    (Mᵀ * spGram 2 K * M) k l = spForm 2 K (M *ᵥ Pi.single k 1) (M *ᵥ Pi.single l 1) := by
  rw [spForm_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, mulVec_single_one_apply]
  simp [Fintype.sum_sum_type, Fin.sum_univ_two, spGram, fromBlocks]
  ring

theorem exists_mem_statedSp_translate_eq {A B : Submodule K (V₄ → K)} (hA2 : finrank K A = 2)
    (hB2 : finrank K B = 2) (hAiso : ∀ u ∈ A, ∀ v ∈ A, spForm 2 K u v = 0)
    (hBiso : ∀ u ∈ B, ∀ v ∈ B, spForm 2 K u v = 0) (hAB : A ⊓ B = ⊥) :
    ∃ h ∈ StatedSp 2 K, translate h lagInl = A ∧ translate h (graphLag 0) = B := by
  classical
  let bA : Basis (Fin 2) K A := Module.finBasisOfFinrankEq K A hA2
  let a : Fin 2 → V₄ → K := fun i => (bA i : V₄ → K)
  have ha : ∀ i, a i ∈ A := fun i => (bA i).2
  let ψ : B →ₗ[K] (Fin 2 → K) :=
    { toFun := fun b i => spForm 2 K (a i) b
      map_add' := by intro b b'; ext i; simp
      map_smul' := by intro c b; ext i; simp }
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have hbA : (b : V₄ → K) ∈ orth A := by
      rw [mem_orth]
      intro u hu
      have hu' := bA.sum_repr ⟨u, hu⟩
      have hu'' : u = ∑ i, bA.repr ⟨u, hu⟩ i • a i := by
        have := congrArg Subtype.val hu'
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hu'', map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smul, LinearMap.smul_apply]
      have := congrFun hb i
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rw [this, smul_zero]
    rw [orth_eq_self_of_isotropic hA2 hAiso] at hbA
    have : (b : V₄ → K) ∈ A ⊓ B := ⟨hbA, b.2⟩
    rw [hAB] at this
    exact Subtype.ext ((Submodule.mem_bot _).mp this)
  have hψsurj : Function.Surjective ψ := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hψinj
    · rw [hB2, Module.finrank_fin_fun]
  let eψ : B ≃ₗ[K] (Fin 2 → K) := LinearEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  let b : Fin 2 → V₄ → K := fun j => (eψ.symm (Pi.single j 1) : V₄ → K)
  have hb : ∀ j, b j ∈ B := fun j => (eψ.symm (Pi.single j 1)).2
  have hab : ∀ i j, spForm 2 K (a i) (b j) = if i = j then 1 else 0 := by
    intro i j
    have h1 : ψ (eψ.symm (Pi.single j 1)) = Pi.single j 1 := eψ.apply_symm_apply _
    have h2 := congrFun h1 i
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk] at h2
    rw [h2]
    simp [Pi.single_apply]
  let H : Matrix V₄ V₄ K := Matrix.of fun r c => Sum.elim (fun i => a i r) (fun j => b j r) c
  have hHinl : ∀ i, H *ᵥ Pi.single (Sum.inl i) 1 = a i := by
    intro i; ext r; rw [mulVec_single_one_apply]; rfl
  have hHinr : ∀ j, H *ᵥ Pi.single (Sum.inr j) 1 = b j := by
    intro j; ext r; rw [mulVec_single_one_apply]; rfl
  have hform : ∀ k l, spForm 2 K (H *ᵥ Pi.single k 1) (H *ᵥ Pi.single l 1) = spGram 2 K k l := by
    intro k l
    rcases k with i | i <;> rcases l with j | j
    · rw [hHinl, hHinl, hAiso _ (ha i) _ (ha j)]; simp [spGram]
    · rw [hHinl, hHinr, hab]; simp [spGram, Matrix.one_apply]
    · rw [hHinr, hHinl, ← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, hab]
      simp [spGram, Matrix.one_apply, eq_comm]
    · rw [hHinr, hHinr, hBiso _ (hb i) _ (hb j)]; simp [spGram]
  have hgram : Hᵀ * spGram 2 K * H = spGram 2 K := by
    ext k l
    rw [← hform k l, gram_entry]
  have hJJ : spGram 2 K * spGram 2 K = -1 := by
    rw [spGram, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
    simp
  have hJdet : (spGram 2 K).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hJJ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg, Matrix.det_one] at this
    norm_num [Fintype.card_sum] at this
  have hdet : H.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hgram
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
    exact hJdet this.symm
  let h : GL V₄ K := Matrix.GeneralLinearGroup.mkOfDetNeZero H hdet
  have hcoe : (h : Matrix V₄ V₄ K) = H := rfl
  have hhS : h ∈ StatedSp 2 K := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, hcoe]
    exact hgram
  have hexp : ∀ v : V₄ → K, v = ∑ i, v (Sum.inl i) • (Pi.single (Sum.inl i) 1 : V₄ → K) +
      ∑ j, v (Sum.inr j) • (Pi.single (Sum.inr j) 1 : V₄ → K) := by
    intro v
    ext r
    rcases r with r | r <;> fin_cases r <;> simp
  have hHv : ∀ v : V₄ → K, H *ᵥ v = ∑ i, v (Sum.inl i) • a i + ∑ j, v (Sum.inr j) • b j := by
    intro v
    conv_lhs => rw [hexp v]
    rw [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hHinl, hHinr]
  refine ⟨h, hhS, ?_, ?_⟩
  · have hle : translate h lagInl ≤ A := by
      intro w hw
      rw [mem_translate] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      rw [hcoe, hHv]
      have h0 : ∑ j, v (Sum.inr j) • b j = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [(mem_lagInl.mp hv) j, zero_smul]
      rw [h0, add_zero]
      exact A.sum_mem fun i _ => A.smul_mem _ (ha i)
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_translate, finrank_lagInl, hA2])
  · have hle : translate h (graphLag 0) ≤ B := by
      intro w hw
      rw [mem_translate] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      rw [hcoe, hHv]
      have h0 : ∑ i, v (Sum.inl i) • a i = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [(mem_graphLag.mp hv) i, Matrix.zero_mulVec, Pi.zero_apply, zero_smul]
      rw [h0, zero_add]
      exact B.sum_mem fun j _ => B.smul_mem _ (hb j)
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_translate, finrank_graphLag, hB2])

omit [Field K] in
theorem mkV_sub {R : Type} [AddCommGroup R] (u w u' w' : Fin 2 → R) :
    mkV u w - mkV u' w' = mkV (u - u') (w - w') := by
  ext i; rcases i with i | i <;> rfl

theorem tGL_inv (M : Matrix (Fin 2) (Fin 2) K) : (tGL M)⁻¹ = tGL (-M) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [tGL_add, add_neg_cancel]
  apply Units.ext
  rw [coe_tGL]
  simp

theorem conj_uGL_sub_one_mulVec (M S' : Matrix (Fin 2) (Fin 2) K) (u w : Fin 2 → K) :
    ((tGL M * uGL S' * (tGL M)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ mkV u w - mkV u w =
      mkV (M *ᵥ (S' *ᵥ (u - M *ᵥ w))) (S' *ᵥ (u - M *ᵥ w)) := by
  rw [tGL_inv, gl_mulVec_mul, gl_mulVec_mul, tGL_mulVec, uGL_mulVec, tGL_mulVec, mkV_sub,
    Matrix.neg_mulVec, ← sub_eq_add_neg, Matrix.mulVec_add]
  congr 1 <;> abel

theorem tGL_sub_one_mulVec (S : Matrix (Fin 2) (Fin 2) K) (u w : Fin 2 → K) :
    ((tGL S : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ mkV u w - mkV u w = mkV (S *ᵥ w) 0 := by
  rw [tGL_mulVec, mkV_sub]
  congr 1 <;> abel

theorem sub_one_mulVec_eq (X : Matrix V₄ V₄ K) (v : V₄ → K) : (X - 1) *ᵥ v = X *ᵥ v - v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem pair_lagInl_mulVec (S M S' : Matrix (Fin 2) (Fin 2) K) (a : Fin 2 → K) :
    (((tGL S : GL V₄ K) : Matrix V₄ V₄ K) - 1) *ᵥ
      ((((tGL M * uGL S' * (tGL M)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) *ᵥ mkV a 0) =
      mkV ((S * S') *ᵥ a) 0 := by
  rw [sub_one_mulVec_eq (((tGL M * uGL S' * (tGL M)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)),
    conj_uGL_sub_one_mulVec, sub_one_mulVec_eq, tGL_sub_one_mulVec, Matrix.mulVec_zero,
    sub_zero, Matrix.mulVec_mulVec]

theorem pair_graphLag_mulVec (M₁ S₁ M₂ S₂ : Matrix (Fin 2) (Fin 2) K) (b : Fin 2 → K) :
    ((((tGL M₁ * uGL S₁ * (tGL M₁)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) *ᵥ
      ((((tGL M₂ * uGL S₂ * (tGL M₂)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) *ᵥ
        mkV (M₁ *ᵥ b) b)) =
      mkV (M₁ *ᵥ (-(S₁ * (M₂ - M₁) * S₂ * (M₂ - M₁)) *ᵥ b))
        (-(S₁ * (M₂ - M₁) * S₂ * (M₂ - M₁)) *ᵥ b) := by
  rw [sub_one_mulVec_eq (((tGL M₂ * uGL S₂ * (tGL M₂)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)),
    conj_uGL_sub_one_mulVec, sub_one_mulVec_eq, conj_uGL_sub_one_mulVec]
  have hY : S₁ *ᵥ (M₂ *ᵥ (S₂ *ᵥ (M₁ *ᵥ b - M₂ *ᵥ b)) - M₁ *ᵥ (S₂ *ᵥ (M₁ *ᵥ b - M₂ *ᵥ b))) =
      -(S₁ * (M₂ - M₁) * S₂ * (M₂ - M₁)) *ᵥ b := by
    rw [← Matrix.sub_mulVec, ← Matrix.sub_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_neg,
      show M₁ - M₂ = -(M₂ - M₁) by abel, Matrix.neg_mulVec, Matrix.mulVec_neg,
      Matrix.mulVec_neg, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mulVec_neg]
  rw [hY]

theorem exists_eq_smul_one_of_sq (h2 : (2 : K) ≠ 0) {X : Matrix (Fin 2) (Fin 2) K}
    (h1 : ∃ c : K, X * X = c • 1) (h1' : ∃ d : K, (X - 1) * (X - 1) = d • 1) :
    ∃ e : K, X = e • 1 := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h1'
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  have f01 := congrFun (congrFun hd 0) 1
  have f10 := congrFun (congrFun hd 1) 0
  have f00 := congrFun (congrFun hd 0) 0
  have f11 := congrFun (congrFun hd 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.sub_apply] at f00 f01 f10 f11
  have hb : X 0 1 = 0 := by
    have h3 : X 0 1 * 2 = 0 := by linear_combination e01 - f01
    exact (mul_eq_zero.mp h3).resolve_right h2
  have hc' : X 1 0 = 0 := by
    have h3 : X 1 0 * 2 = 0 := by linear_combination e10 - f10
    exact (mul_eq_zero.mp h3).resolve_right h2
  have had : X 0 0 = X 1 1 := by
    have h3 : (X 0 0 - X 1 1) * 2 = 0 := by
      linear_combination e00 - e11 - f00 + f11
    have := (mul_eq_zero.mp h3).resolve_right h2
    linear_combination this
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb, hc', had]

@[expose] def matE : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem matE_transpose : (matE : Matrix (Fin 2) (Fin 2) K)ᵀ = -matE := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matE]

theorem eq_smul_matE_of_transpose (h2 : (2 : K) ≠ 0) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : Xᵀ = -X) : X = X 0 1 • matE := by
  have e00 := congrFun (congrFun hX 0) 0
  have e11 := congrFun (congrFun hX 1) 1
  have e10 := congrFun (congrFun hX 1) 0
  simp at e00 e11 e10
  have h00 : X 0 0 = 0 := by
    have h3 : X 0 0 * 2 = 0 := by linear_combination e00
    exact (mul_eq_zero.mp h3).resolve_right h2
  have h11 : X 1 1 = 0 := by
    have h3 : X 1 1 * 2 = 0 := by linear_combination e11
    exact (mul_eq_zero.mp h3).resolve_right h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matE, h00, h11]
  linear_combination e10

@[expose] noncomputable def regJ (S : Matrix (Fin 2) (Fin 2) K) : Matrix V₄ V₄ K :=
  fromBlocks (matE * S⁻¹) 0 0 (S⁻¹ * matE)

theorem regJ_mulVec (S : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2 → K) :
    regJ S *ᵥ mkV a b = mkV ((matE * S⁻¹) *ᵥ a) ((S⁻¹ * matE) *ᵥ b) := by
  rw [regJ, fromBlocks_mulVec_mkV]
  simp

theorem regJ_mem_lagInl (S : Matrix (Fin 2) (Fin 2) K) {v : V₄ → K} (hv : v ∈ lagInl) :
    regJ S *ᵥ v ∈ lagInl := by
  rw [eq_mkV v, show (fun i => v (Sum.inr i)) = 0 from funext hv, regJ_mulVec,
    Matrix.mulVec_zero]
  exact mkV_mem_lagInl _

theorem regJ_mem_graphLag {S : Matrix (Fin 2) (Fin 2) K} (hS : S.det ≠ 0) (c : K)
    {v : V₄ → K} (hv : v ∈ graphLag (c • S)) : regJ S *ᵥ v ∈ graphLag (c • S) := by
  rw [mem_graphLag_iff.mp hv, regJ_mulVec]
  have : (matE * S⁻¹) *ᵥ ((c • S) *ᵥ fun j => v (Sum.inr j)) =
      (c • S) *ᵥ ((S⁻¹ * matE) *ᵥ fun j => v (Sum.inr j)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS),
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS),
      Matrix.mul_one, Matrix.one_mul]
  rw [this]
  exact mkV_mem_graphLag _

theorem mulVec_dotProduct_eq (A : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2 → K) :
    (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Aᵀ *ᵥ b) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

theorem regJ_skew {S : Matrix (Fin 2) (Fin 2) K} (hSsym : Sᵀ = S) (v w : V₄ → K) :
    spForm 2 K (regJ S *ᵥ v) w = -spForm 2 K v (regJ S *ᵥ w) := by
  rw [eq_mkV v, eq_mkV w, regJ_mulVec, regJ_mulVec, spForm_mkV, spForm_mkV,
    mulVec_dotProduct_eq, mulVec_dotProduct_eq]
  have hSi : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSsym]
  have hP : (matE * S⁻¹)ᵀ = -(S⁻¹ * matE) := by
    rw [Matrix.transpose_mul, hSi, matE_transpose, Matrix.mul_neg]
  have hU : (S⁻¹ * matE)ᵀ = -(matE * S⁻¹) := by
    rw [Matrix.transpose_mul, hSi, matE_transpose, Matrix.neg_mul]
  rw [hP, hU, Matrix.neg_mulVec, Matrix.neg_mulVec, dotProduct_neg, dotProduct_neg]
  ring

theorem mat_ext_of_mulVec {X Y : Matrix (Fin 2) (Fin 2) K} (h : ∀ b, X *ᵥ b = Y *ᵥ b) :
    X = Y :=
  Matrix.toLin'.injective (LinearMap.ext h)

omit [Field K] in
theorem mkV_smul {R : Type} [Mul R] (c : R) (a b : Fin 2 → R) :
    c • mkV a b = mkV (c • a) (c • b) := by
  ext i; rcases i with i | i <;> rfl

omit [Field K] in
theorem mkV_injective {R : Type} {a b a' b' : Fin 2 → R} (h : mkV a b = mkV a' b') :
    a = a' ∧ b = b' :=
  ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩

theorem mkV_zero_mem_graphLag (M : Matrix (Fin 2) (Fin 2) K) (b : Fin 2 → K)
    (hb : M *ᵥ b = 0) : mkV 0 b ∈ graphLag M := by
  intro i; simp [hb]

theorem exists_eq_smul_regJ (h2 : (2 : K) ≠ 0) {S : Matrix (Fin 2) (Fin 2) K} (hSsym : Sᵀ = S)
    (hS : S.det ≠ 0) {α : Matrix V₄ V₄ K} (h0 : ∀ v ∈ lagInl, α *ᵥ v ∈ lagInl)
    (h1 : ∀ v ∈ graphLag 0, α *ᵥ v ∈ graphLag 0) (h3 : ∀ v ∈ graphLag S, α *ᵥ v ∈ graphLag S)
    (hskew : ∀ v w, spForm 2 K (α *ᵥ v) w = -spForm 2 K v (α *ᵥ w)) :
    ∃ c : K, α = c • regJ S := by
  set P := α.toBlocks₁₁
  set Q := α.toBlocks₁₂
  set R := α.toBlocks₂₁
  set U := α.toBlocks₂₂
  have hα : α = fromBlocks P Q R U := (Matrix.fromBlocks_toBlocks α).symm
  have hαv : ∀ a b, α *ᵥ mkV a b = mkV (P *ᵥ a + Q *ᵥ b) (R *ᵥ a + U *ᵥ b) := by
    intro a b; rw [hα, fromBlocks_mulVec_mkV]
  have hR : R = 0 := by
    apply mat_ext_of_mulVec
    intro a
    have := h0 _ (mkV_mem_lagInl a)
    rw [hαv, Matrix.mulVec_zero, add_zero] at this
    ext i
    have := this i
    simpa using this
  have hQ : Q = 0 := by
    apply mat_ext_of_mulVec
    intro b
    have := h1 _ (mkV_zero_mem_graphLag 0 b (Matrix.zero_mulVec b))
    rw [hαv, Matrix.mulVec_zero, zero_add] at this
    ext i
    have := this i
    simpa using this
  have hPS : P * S = S * U := by
    apply mat_ext_of_mulVec
    intro b
    have := h3 _ (mkV_mem_graphLag (M := S) b)
    rw [hαv, hQ, hR, Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero, zero_add] at this
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    ext i
    exact this i
  have hPU : Pᵀ = -U := by
    apply mat_ext_of_mulVec
    intro b
    have hab : ∀ a, a ⬝ᵥ (Pᵀ *ᵥ b) = a ⬝ᵥ ((-U) *ᵥ b) := by
      intro a
      have := hskew (mkV a 0) (mkV 0 b)
      rw [hαv, hαv, hQ, hR] at this
      simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, zero_add, spForm_mkV,
        dotProduct_zero, sub_zero] at this
      rw [mulVec_dotProduct_eq] at this
      rw [Matrix.neg_mulVec, dotProduct_neg]
      exact this
    ext i
    have := hab (Pi.single i 1)
    simpa [Pi.single_apply, dotProduct] using this
  have hX : (P * S)ᵀ = -(P * S) := by
    rw [Matrix.transpose_mul, hSsym, hPU, hPS, Matrix.mul_neg]
  set c := (P * S) 0 1
  have hPSc := eq_smul_matE_of_transpose h2 hX
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
  have hPc : P = c • (matE * S⁻¹) := by
    calc P = P * S * S⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSu, Matrix.mul_one]
      _ = c • (matE * S⁻¹) := by rw [hPSc, Matrix.smul_mul]
  have hUc : U = c • (S⁻¹ * matE) := by
    have hSi : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSsym]
    rw [← neg_neg U, ← hPU, hPc, Matrix.transpose_smul, Matrix.transpose_mul, hSi,
      matE_transpose, Matrix.mul_neg, smul_neg, neg_neg]
  refine ⟨c, ?_⟩
  rw [hα, hPc, hQ, hR, hUc, regJ, Matrix.fromBlocks_smul, smul_zero]

theorem tGL_zero : tGL (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  apply Units.ext; rw [coe_tGL]; simp

theorem isSqZero_tGL (S : Matrix (Fin 2) (Fin 2) K) : IsSqZero (tGL S) := by
  rw [IsSqZero, coe_tGL, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
    fromBlocks_multiply]
  simp

theorem isSqZero_uGL (S : Matrix (Fin 2) (Fin 2) K) : IsSqZero (uGL S) := by
  rw [IsSqZero, coe_uGL, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
    fromBlocks_multiply]
  simp

theorem mulVec_eq_zero_of_det_ne_zero {S : Matrix (Fin 2) (Fin 2) K} (hS : S.det ≠ 0)
    {b : Fin 2 → K} (hb : S *ᵥ b = 0) : b = 0 := by
  have := congrArg (fun w => S⁻¹ *ᵥ w) hb
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS),
    Matrix.one_mulVec, Matrix.mulVec_zero] at this

theorem unipAxis_tGL {S : Matrix (Fin 2) (Fin 2) K} (hS : S.det ≠ 0) :
    unipAxis (tGL S) = lagInl := by
  ext v
  rw [mem_unipAxis, mem_lagInl]
  conv_lhs => rw [eq_mkV v]
  rw [tGL_mulVec]
  constructor
  · intro h
    have h1 := (mkV_injective h).1
    have hb : S *ᵥ (fun j => v (Sum.inr j)) = 0 := by
      have := congrArg (fun w => w - fun i => v (Sum.inl i)) h1
      simpa using this
    exact fun i => congrFun (mulVec_eq_zero_of_det_ne_zero hS hb) i
  · intro h
    have hb : (fun j => v (Sum.inr j)) = 0 := funext h
    rw [hb, Matrix.mulVec_zero, add_zero]

theorem unipAxis_uGL {S : Matrix (Fin 2) (Fin 2) K} (hS : S.det ≠ 0) :
    unipAxis (uGL S) = graphLag 0 := by
  ext v
  rw [mem_unipAxis, mem_graphLag]
  conv_lhs => rw [eq_mkV v]
  rw [uGL_mulVec]
  simp only [Matrix.zero_mulVec, Pi.zero_apply]
  constructor
  · intro h
    have h1 := (mkV_injective h).2
    have ha : S *ᵥ (fun j => v (Sum.inl j)) = 0 := by
      have := congrArg (fun w => w - fun i => v (Sum.inr i)) h1
      simpa using this
    exact fun i => congrFun (mulVec_eq_zero_of_det_ne_zero hS ha) i
  · intro h
    have ha : (fun j => v (Sum.inl j)) = 0 := funext h
    rw [ha, Matrix.mulVec_zero, zero_add]

theorem lagInl_inf_graphLag (M : Matrix (Fin 2) (Fin 2) K) : lagInl ⊓ graphLag M = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hv
  rw [Submodule.mem_bot]
  have hb : (fun j => v (Sum.inr j)) = 0 := funext h1
  ext i
  rcases i with i | i
  · rw [h2 i, hb, Matrix.mulVec_zero]; rfl
  · exact h1 i

theorem eq_of_graphLag_eq {M N : Matrix (Fin 2) (Fin 2) K} (h : graphLag M = graphLag N) :
    M = N := by
  apply mat_ext_of_mulVec
  intro b
  have := (h ▸ mkV_mem_graphLag (M := M) b : mkV (M *ᵥ b) b ∈ graphLag N)
  ext i
  exact this i

theorem exists_eq_conj_uGL {z : GL V₄ K} (hzS : z ∈ StatedSp 2 K) (hz : IsSqZero z)
    {M : Matrix (Fin 2) (Fin 2) K} (hM : Mᵀ = M) (hax : unipAxis z = graphLag M) :
    ∃ S' : Matrix (Fin 2) (Fin 2) K, S'ᵀ = S' ∧ z = tGL M * uGL S' * (tGL M)⁻¹ := by
  have hMn : (-M)ᵀ = -M := by rw [Matrix.transpose_neg, hM]
  have hinv : (tGL (-M))⁻¹ = tGL M := by rw [tGL_inv, neg_neg]
  have hz'S : tGL (-M) * z * (tGL (-M))⁻¹ ∈ StatedSp 2 K := by
    rw [hinv]
    exact mul_mem (mul_mem (tGL_mem hMn) hzS) (tGL_mem hM)
  have hz'ax : unipAxis (tGL (-M) * z * (tGL (-M))⁻¹) = graphLag 0 := by
    rw [unipAxis_conj, hax, translate_tGL_graphLag, neg_add_cancel]
  obtain ⟨S', hS', hz'eq⟩ :=
    exists_eq_uGL_of_unipAxis_eq_graphLag_zero hz'S (isSqZero_conj hz _) hz'ax
  refine ⟨S', hS', ?_⟩
  rw [← hz'eq, hinv, tGL_inv]
  have h1 : tGL M * tGL (-M) = 1 := by rw [tGL_add, add_neg_cancel, tGL_zero]
  have h2 : tGL (-M) * tGL M = 1 := by rw [tGL_add, neg_add_cancel, tGL_zero]
  calc z = (tGL M * tGL (-M)) * z * (tGL M * tGL (-M)) := by rw [h1, one_mul, mul_one]
    _ = tGL M * (tGL (-M) * z * tGL M) * tGL (-M) := by group

theorem eq_smul_one_of_pair_lagInl {S M S' : Matrix (Fin 2) (Fin 2) K} {τ : K}
    (h : ∀ a ∈ lagInl, (((tGL S : GL V₄ K) : Matrix V₄ V₄ K) - 1) *ᵥ
      ((((tGL M * uGL S' * (tGL M)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) *ᵥ a) = τ • a) :
    S * S' = τ • 1 := by
  apply mat_ext_of_mulVec
  intro b
  have := h _ (mkV_mem_lagInl b)
  rw [pair_lagInl_mulVec, mkV_smul, smul_zero] at this
  rw [(mkV_injective this).1, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem eq_smul_one_of_pair_graphLag {M₁ S₁ M₂ S₂ : Matrix (Fin 2) (Fin 2) K} {τ : K}
    (h : ∀ v ∈ graphLag M₁,
      ((((tGL M₁ * uGL S₁ * (tGL M₁)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) *ᵥ
        ((((tGL M₂ * uGL S₂ * (tGL M₂)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) *ᵥ v)) = τ • v) :
    -(S₁ * (M₂ - M₁) * S₂ * (M₂ - M₁)) = τ • 1 := by
  apply mat_ext_of_mulVec
  intro b
  have := h _ (mkV_mem_graphLag (M := M₁) b)
  rw [pair_graphLag_mulVec, mkV_smul] at this
  rw [(mkV_injective this).2, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem gl_conj_conj (g : GL V₄ K) (X : Matrix V₄ V₄ K) :
    ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * ((g : Matrix V₄ V₄ K) * X *
      ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) * (g : Matrix V₄ V₄ K) = X := by
  calc ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * ((g : Matrix V₄ V₄ K) * X *
        ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) * (g : Matrix V₄ V₄ K)
      = (((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * g) * X *
          (((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * g) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_one]

theorem commute_of_forall_conj_eq_smul {G : Subgroup (GL V₄ K)} [Group.IsPerfect G]
    {J : Matrix V₄ V₄ K} (hJ0 : J ≠ 0)
    (hconj : ∀ g ∈ G, ∃ c : K,
      (g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = c • J) :
    ∀ g ∈ G, (g : Matrix V₄ V₄ K) * J = J * (g : Matrix V₄ V₄ K) := by
  classical
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, J i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hJ0 (Matrix.ext h)
  let cj : GL V₄ K → Matrix V₄ V₄ K := fun g =>
    (g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)
  let c : G → K := fun g => cj (g : GL V₄ K) i₀ j₀ / J i₀ j₀
  have hc : ∀ g : G, cj (g : GL V₄ K) = c g • J := by
    intro g
    obtain ⟨d, hd⟩ := hconj g g.2
    have hd' : cj (g : GL V₄ K) = d • J := hd
    have : c g = d := by
      simp only [c, hd', Matrix.smul_apply, smul_eq_mul]
      field_simp
    rw [this, hd']
  have hc0 : ∀ g : G, c g ≠ 0 := by
    intro g h0
    have := gl_conj_conj (g : GL V₄ K) J
    have h1 : cj (g : GL V₄ K) = 0 := by rw [hc g, h0, zero_smul]
    change ((((g : GL V₄ K))⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * cj (g : GL V₄ K) *
      ((g : GL V₄ K) : Matrix V₄ V₄ K) = J at this
    rw [h1, Matrix.mul_zero, Matrix.zero_mul] at this
    exact hJ0 this.symm
  have hcjmul : ∀ g h : GL V₄ K, cj (g * h) = (g : Matrix V₄ V₄ K) * cj h *
      ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
    intro g h
    simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  have hcmul : ∀ g h : G, c (g * h) = c g * c h := by
    intro g h
    have e : cj ((g * h : G) : GL V₄ K) = (c g * c h) • J := by
      rw [Subgroup.coe_mul, hcjmul, hc h, Matrix.mul_smul, Matrix.smul_mul]
      change c h • cj (g : GL V₄ K) = _
      rw [hc g, smul_smul, mul_comm]
    have e2 := hc (g * h)
    rw [e] at e2
    have := congrFun (congrFun e2 i₀) j₀
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact (mul_right_cancel₀ hij this).symm
  have hc1 : c 1 = 1 := by
    have h1 : cj ((1 : G) : GL V₄ K) = J := by
      simp [cj]
    have := hc 1
    rw [h1] at this
    have h' := congrFun (congrFun this i₀) j₀
    simp only [Matrix.smul_apply, smul_eq_mul] at h'
    have : c 1 * J i₀ j₀ = 1 * J i₀ j₀ := by rw [one_mul]; exact h'.symm
    exact mul_right_cancel₀ hij this
  let χ : G →* Kˣ :=
    { toFun := fun g => Units.mk0 (c g) (hc0 g)
      map_one' := by ext; simp [hc1]
      map_mul' := by intro g h; ext; simp [hcmul] }
  intro g hg
  have hker : (⟨g, hg⟩ : G) ∈ χ.ker :=
    Abelianization.commutator_subset_ker χ Group.IsPerfect.mem_commutator
  have hcg : c ⟨g, hg⟩ = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp hker)
    simpa [χ] using this
  have h3 := hc ⟨g, hg⟩
  rw [hcg, one_smul] at h3
  calc (g : Matrix V₄ V₄ K) * J
      = (g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (g : Matrix V₄ V₄ K) := by
        rw [Matrix.mul_assoc _ ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K), ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Matrix.mul_one]
    _ = J * (g : Matrix V₄ V₄ K) := by
        change cj g * (g : Matrix V₄ V₄ K) = _
        rw [h3]

theorem eq_smul_inv_of_mul_eq_smul {S S' : Matrix (Fin 2) (Fin 2) K} (hS : S.det ≠ 0) {τ : K}
    (h : S * S' = τ • 1) : S' = τ • S⁻¹ := by
  calc S' = S⁻¹ * (S * S') := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS),
          Matrix.one_mul]
    _ = τ • S⁻¹ := by rw [h, Matrix.mul_smul, Matrix.mul_one]

theorem false_of_regulus_core (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)}
    (hGS : G ≤ StatedSp 2 K) [Group.IsPerfect G] (hcomm : commutant G = ⊥)
    (hdich : ∀ y ∈ G, ∀ z ∈ G, IsSqZero y → IsSqZero z → finrank K (unipAxis y) = 2 →
      finrank K (unipAxis z) = 2 → unipAxis y = unipAxis z ∨ unipAxis y ⊓ unipAxis z = ⊥)
    (hΔ : ∀ y ∈ G, ∀ z ∈ G, IsSqZero y → IsSqZero z → finrank K (unipAxis y) = 2 →
      finrank K (unipAxis z) = 2 → unipAxis y ⊓ unipAxis z = ⊥ → ∃ τ : K, ∀ a ∈ unipAxis y,
        ((y : Matrix V₄ V₄ K) - 1) *ᵥ (((z : Matrix V₄ V₄ K) - 1) *ᵥ a) = τ • a)
    {S S' : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) (hSdet : S.det ≠ 0)
    (hS'det : S'.det ≠ 0) (hxG : tGL S ∈ G) (hyG : uGL S' ∈ G) : False := by
  classical
  have hxax := unipAxis_tGL hSdet
  have hyax := unipAxis_uGL hS'det
  have hx2 : finrank K (unipAxis (tGL S)) = 2 := by rw [hxax, finrank_lagInl]
  have hy2 : finrank K (unipAxis (uGL S')) = 2 := by rw [hyax, finrank_graphLag]
  have hy_conj : uGL S' = tGL 0 * uGL S' * (tGL 0)⁻¹ := by rw [tGL_zero]; group
  obtain ⟨τ, hτ⟩ := hΔ _ hxG _ hyG (isSqZero_tGL S) (isSqZero_uGL S') hx2 hy2
    (by rw [hxax, hyax]; exact lagInl_inf_graphLag 0)
  rw [hxax] at hτ
  have hSS' : S * S' = τ • 1 := by
    refine eq_smul_one_of_pair_lagInl (M := 0) fun a ha => ?_
    rw [← hy_conj]
    exact hτ a ha
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hSS'
    have := congrArg Matrix.det hSS'
    rw [Matrix.det_mul, Matrix.det_zero] at this
    exact mul_ne_zero hSdet hS'det this
  have hS'eq := eq_smul_inv_of_mul_eq_smul hSdet hSS'
  set z₁ := tGL S * uGL S' * (tGL S)⁻¹ with hz₁
  have hz₁G : z₁ ∈ G := G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)
  have hz₁ax : unipAxis z₁ = graphLag S := by
    rw [hz₁, unipAxis_conj, hyax, translate_tGL_graphLag, add_zero]
  have hz₁2 : finrank K (unipAxis z₁) = 2 := by rw [hz₁ax, finrank_graphLag]
  have haxes : ∀ z ∈ G, IsSqZero z → finrank K (unipAxis z) = 2 →
      unipAxis z = lagInl ∨ ∃ c : K, unipAxis z = graphLag (c • S) := by
    intro z hzG hz hz2
    rcases hdich _ hxG _ hzG (isSqZero_tGL S) hz hx2 hz2 with h | h
    · left; rw [← h, hxax]
    right
    have hzL : unipAxis z ⊓ lagInl = ⊥ := by rw [inf_comm, ← hxax]; exact h
    obtain ⟨M, hMsym, hM⟩ := exists_eq_graphLag hz2
      (fun u hu v hv => spForm_eq_zero_of_mem_unipAxis (hGS hzG) hz hz2 hu hv) hzL
    obtain ⟨Sz, hSz, hzeq⟩ := exists_eq_conj_uGL (hGS hzG) hz hMsym hM
    obtain ⟨τz, hτz⟩ := hΔ _ hxG _ hzG (isSqZero_tGL S) hz hx2 hz2 h
    rw [hxax] at hτz
    have hSSz : S * Sz = τz • 1 :=
      eq_smul_one_of_pair_lagInl fun a ha => by rw [← hzeq]; exact hτz a ha
    have hτz0 : τz ≠ 0 := by
      rintro rfl
      have hSz0 : Sz = 0 := by
        rw [eq_smul_inv_of_mul_eq_smul hSdet hSSz, zero_smul]
      have hz1 : z = 1 := by
        rw [hzeq, hSz0]
        have : uGL (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by
          apply Units.ext; rw [coe_uGL]; simp
        rw [this, mul_one, mul_inv_cancel]
      rw [hz1] at hz2
      have : unipAxis (1 : GL V₄ K) = ⊤ := by
        ext v; simp [mem_unipAxis]
      rw [this, finrank_top, Module.finrank_fintype_fun_eq_card] at hz2
      simp at hz2
    have hSzeq := eq_smul_inv_of_mul_eq_smul hSdet hSSz
    set X := S⁻¹ * M with hX
    have hXsq : ∀ (M₁ : Matrix (Fin 2) (Fin 2) K) (S₁ : Matrix (Fin 2) (Fin 2) K) (w : GL V₄ K),
        w ∈ G → IsSqZero w → unipAxis w = graphLag M₁ → w = tGL M₁ * uGL S₁ * (tGL M₁)⁻¹ →
        S₁ = τ • S⁻¹ → M ≠ M₁ → ∃ d : K, (S⁻¹ * (M - M₁)) * (S⁻¹ * (M - M₁)) = d • 1 := by
      intro M₁ S₁ w hwG hw hwax hweq hS₁ hne
      have hw2 : finrank K (unipAxis w) = 2 := by rw [hwax, finrank_graphLag]
      have hdisj : unipAxis w ⊓ unipAxis z = ⊥ := by
        rcases hdich _ hwG _ hzG hw hz hw2 hz2 with h' | h'
        · exact absurd (eq_of_graphLag_eq (hwax.symm.trans (h'.trans hM))).symm hne
        · exact h'
      obtain ⟨τ', hτ'⟩ := hΔ _ hwG _ hzG hw hz hw2 hz2 hdisj
      rw [hwax] at hτ'
      have hmat := eq_smul_one_of_pair_graphLag (M₁ := M₁) (S₁ := S₁) (M₂ := M) (S₂ := Sz)
        fun v hv => by rw [← hweq, ← hzeq]; exact hτ' v hv
      rw [hS₁, hSzeq] at hmat
      refine ⟨-τ' / (τ * τz), ?_⟩
      have hττz : τ * τz ≠ 0 := mul_ne_zero hτ0 hτz0
      have key : (τ • S⁻¹) * (M - M₁) * (τz • S⁻¹) * (M - M₁) =
          (τ * τz) • ((S⁻¹ * (M - M₁)) * (S⁻¹ * (M - M₁))) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm τz τ]
      have : (τ * τz) • ((S⁻¹ * (M - M₁)) * (S⁻¹ * (M - M₁))) = (-τ') • 1 := by
        rw [← key, neg_smul, ← hmat, neg_neg]
      calc (S⁻¹ * (M - M₁)) * (S⁻¹ * (M - M₁))
          = (τ * τz)⁻¹ • ((τ * τz) • ((S⁻¹ * (M - M₁)) * (S⁻¹ * (M - M₁)))) := by
            rw [smul_smul, inv_mul_cancel₀ hττz, one_smul]
        _ = (-τ' / (τ * τz)) • 1 := by
            rw [this, smul_smul, div_eq_inv_mul]
    have hX1 : ∃ d : K, X * X = d • 1 := by
      by_cases hM0 : M = 0
      · exact ⟨0, by rw [hX, hM0, Matrix.mul_zero, Matrix.zero_mul, zero_smul]⟩
      obtain ⟨d, hd⟩ := hXsq 0 S' _ hyG (isSqZero_uGL S') hyax hy_conj hS'eq hM0
      exact ⟨d, by rw [hX]; simpa using hd⟩
    have hX2 : ∃ d : K, (X - 1) * (X - 1) = d • 1 := by
      have hXS : X - 1 = S⁻¹ * (M - S) := by
        rw [hX, Matrix.mul_sub, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hSdet)]
      by_cases hMS : M = S
      · exact ⟨0, by rw [hXS, hMS, sub_self, Matrix.mul_zero, Matrix.zero_mul, zero_smul]⟩
      obtain ⟨d, hd⟩ := hXsq S S' z₁ hz₁G (isSqZero_conj (isSqZero_uGL S') _) hz₁ax hz₁ hS'eq hMS
      exact ⟨d, by rw [hXS]; exact hd⟩
    obtain ⟨e, he⟩ := exists_eq_smul_one_of_sq h2 hX1 hX2
    refine ⟨e, ?_⟩
    rw [hM]
    congr 1
    calc M = S * (S⁻¹ * M) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hSdet),
            Matrix.one_mul]
      _ = e • S := by rw [← hX, he, Matrix.mul_smul, Matrix.mul_one]
  set J := regJ S with hJ
  have hJpres : ∀ z ∈ G, IsSqZero z → finrank K (unipAxis z) = 2 →
      ∀ v ∈ unipAxis z, J *ᵥ v ∈ unipAxis z := by
    intro z hzG hz hz2 v hv
    rcases haxes z hzG hz hz2 with h | ⟨c, h⟩
    · rw [h] at hv ⊢; exact regJ_mem_lagInl S hv
    · rw [h] at hv ⊢; exact regJ_mem_graphLag hSdet c hv
  have hpres : ∀ g ∈ G, ∀ w ∈ G, IsSqZero w → finrank K (unipAxis w) = 2 →
      ∀ v ∈ unipAxis w, ((g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) *ᵥ v ∈
        unipAxis w := by
    intro g hg w hwG hw hw2 v hv
    have hw'G : g⁻¹ * w * g⁻¹⁻¹ ∈ G :=
      G.mul_mem (G.mul_mem (G.inv_mem hg) hwG) (G.inv_mem (G.inv_mem hg))
    have hw'2 : finrank K (unipAxis (g⁻¹ * w * g⁻¹⁻¹)) = 2 := by
      rw [finrank_unipAxis_conj]; exact hw2
    have h1 : ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v ∈ unipAxis (g⁻¹ * w * g⁻¹⁻¹) := by
      rw [unipAxis_conj]; exact mulVec_mem_translate hv
    have h2' := hJpres _ hw'G (isSqZero_conj hw _) hw'2 _ h1
    have h3 : unipAxis w = translate g (unipAxis (g⁻¹ * w * g⁻¹⁻¹)) := by
      rw [unipAxis_conj, ← translate_mul, mul_inv_cancel, translate_one]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3]
    exact mulVec_mem_translate h2'
  have hskewg : ∀ g ∈ G, ∀ v w : V₄ → K,
      spForm 2 K (((g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) *ᵥ v) w =
        -spForm 2 K v (((g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) *ᵥ w) := by
    intro g hg v w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    conv_lhs => rw [← gl_mulVec_inv_mulVec g w]
    rw [spForm_mulVec (hGS hg), regJ_skew hS]
    conv_rhs => rw [← gl_mulVec_inv_mulVec g v, spForm_mulVec (hGS hg)]
  have hconj : ∀ g ∈ G, ∃ c : K,
      (g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = c • J := by
    intro g hg
    refine exists_eq_smul_regJ h2 hS hSdet ?_ ?_ ?_ (hskewg g hg)
    · intro v hv
      rw [← hxax] at hv ⊢
      exact hpres g hg _ hxG (isSqZero_tGL S) hx2 v hv
    · intro v hv
      rw [← hyax] at hv ⊢
      exact hpres g hg _ hyG (isSqZero_uGL S') hy2 v hv
    · intro v hv
      rw [← hz₁ax] at hv ⊢
      exact hpres g hg _ hz₁G (isSqZero_conj (isSqZero_uGL S') _) hz₁2 v hv
  have hmatE0 : (matE : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 0) 1
    simp [matE] at this
  have hJ0 : J ≠ 0 := by
    intro h0
    apply hmatE0
    have h1 : matE * S⁻¹ = 0 := by
      ext i j
      have := congrFun (congrFun h0 (Sum.inl i)) (Sum.inl j)
      simpa [hJ, regJ] using this
    calc (matE : Matrix (Fin 2) (Fin 2) K) = matE * S⁻¹ * S := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hSdet),
            Matrix.mul_one]
      _ = 0 := by rw [h1, Matrix.zero_mul]
  have hJmem : J ∈ commutant G :=
    mem_commutant.mpr (commute_of_forall_conj_eq_smul hJ0 hconj)
  rw [hcomm, Algebra.mem_bot] at hJmem
  obtain ⟨c, hc⟩ := hJmem
  have hJc : J = c • 1 := by rw [← hc, Algebra.algebraMap_eq_smul_one]
  have hblk : matE * S⁻¹ = c • 1 := by
    ext i j
    have := congrFun (congrFun hJc (Sum.inl i)) (Sum.inl j)
    simpa [hJ, regJ, Matrix.one_apply] using this
  have hES : (matE : Matrix (Fin 2) (Fin 2) K) = c • S := by
    calc (matE : Matrix (Fin 2) (Fin 2) K) = matE * S⁻¹ * S := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hSdet),
            Matrix.mul_one]
      _ = c • S := by rw [hblk, Matrix.smul_mul, Matrix.one_mul]
  have hT := congrArg Matrix.transpose hES
  rw [matE_transpose, Matrix.transpose_smul, hS, ← hES] at hT
  apply hmatE0
  have h2E : (2 : K) • (matE : Matrix (Fin 2) (Fin 2) K) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hT]
    abel
  exact (smul_eq_zero.mp h2E).resolve_left h2

end CFSG.RankThree.SubgroupLists
