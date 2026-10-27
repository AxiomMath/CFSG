module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open scoped commutatorElement

namespace TableBSymp

variable {K : Type} [Field K]

section MatrixTorus

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ggTorusLift_of_matrixTorus {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup (GL ι K)} (τ : (Fin k → Multiplicative (ZMod p)) →* GL ι K)
    (hτH : ∀ f, τ f ∈ H) (hτs : ∀ f, τ f ∈ LargeEvenScalars ι K → f = 1)
    (hinv : ∀ i j : Fin k, ∃ w ∈ H, w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
      (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j))
    (X : Multiplicative K →* GL ι K) (hXH : ∀ c, X c ∈ H)
    (hX1 : X (Multiplicative.ofAdd 1) ∉ LargeEvenScalars ι K) (hX2 : ∀ c, X c ^ 2 = 1)
    (hτX : ∀ f c, ∃ c', τ f * X c * (τ f)⁻¹ = X c') :
    GGTorusLift p k (LargeEvenProj H) := by
  set τH : (Fin k → Multiplicative (ZMod p)) →* H := τ.codRestrict H hτH with hτHdef
  set τR := (LargeEvenProjMk H).comp τH with hτR
  set XH : Multiplicative K →* H := X.codRestrict H hXH with hXHdef
  set U := ((LargeEvenProjMk H).comp XH).range with hU
  have hτRinj : Function.Injective τR := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have hf' : ((τH f : H) : LargeEvenProj H) = 1 := hf
    exact hτs f ((QuotientGroup.eq_one_iff (τH f)).mp hf')
  refine ggTorusLift_of_torus hp hp2 τR hτRinj ?_ (U := U) ?_ ?_ ?_
  · intro i j
    obtain ⟨w, hwH, hw1, hw2⟩ := hinv i j
    refine ⟨LargeEvenProjMk H ⟨w, hwH⟩, ?_, fun hji => ?_⟩
    · rw [torusBasis, hτR, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτHdef, MonoidHom.codRestrict_apply]
      exact hw1
    · rw [torusBasis, hτR, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτHdef, MonoidHom.codRestrict_apply]
      exact hw2 hji
  · intro hbot
    have hmem : (LargeEvenProjMk H).comp XH (Multiplicative.ofAdd 1) ∈ U := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hmem' : ((XH (Multiplicative.ofAdd 1) : H) : LargeEvenProj H) = 1 := hmem
    exact hX1 ((QuotientGroup.eq_one_iff (XH (Multiplicative.ofAdd 1))).mp hmem')
  · rintro ⟨_, c, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
    have : XH c ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hXHdef,
      MonoidHom.codRestrict_apply, hX2 c, Subgroup.coe_one])
    rw [MonoidHom.comp_apply, map_pow, this, map_one]
  · rintro f _ ⟨c, rfl⟩
    obtain ⟨c', hc'⟩ := hτX f c
    refine ⟨c', ?_⟩
    rw [hτR, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv,
      ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτHdef, hXHdef, MonoidHom.codRestrict_apply]
    exact hc'.symm

end MatrixTorus

section SplitForm

variable {m : ℕ}

theorem mem_orthGroup_of_isometry {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → K) → K}
    {g : GL ι K} (h : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v) : g ∈ LargeEvenOrthGroup Q :=
  Subgroup.subset_closure h

theorem largeEvenQPlus_eq (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m v = (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) :=
  rfl

theorem largeEvenQPlus_diagGL (u : Fin m → Kˣ) (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m ((TauCeti.diagGL (pairedUnits u) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      *ᵥ v) = LargeEvenQPlus K m v := by
  rw [TauCeti.diagGL_coe]
  simp only [largeEvenQPlus_def, Matrix.mulVec_diagonal, pairedUnits, Sum.elim_inl, Sum.elim_inr]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((u i : Kˣ) : K) * (((u i)⁻¹ : Kˣ) : K) = 1 := Units.mul_inv (u i)
  linear_combination (v (Sum.inl i) * v (Sum.inr i)) * h

theorem permutationGL_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι)
    (v : ι → K) :
    ((TauCeti.permutationGL (k := K) π : GL ι K) : Matrix ι ι K) *ᵥ v = v ∘ ⇑(π⁻¹) := by
  rw [TauCeti.permutationGL_coe, Matrix.permMatrix_mulVec]

theorem largeEvenQPlus_comp_pairSwap (k : Fin m) (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m (v ∘ pairSwap k) = LargeEvenQPlus K m v := by
  simp only [largeEvenQPlus_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = k
  · subst hi
    simp [pairSwap, mul_comm]
  · simp [pairSwap, Equiv.swap_apply_def, hi]

theorem largeEvenQPlus_comp_sumCongr (τ : Equiv.Perm (Fin m)) (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m (v ∘ Equiv.Perm.sumCongr τ τ) = LargeEvenQPlus K m v := by
  simp only [largeEvenQPlus_def, Function.comp_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl,
    Sum.map_inr]
  exact Equiv.sum_comp τ (fun i => v (Sum.inl i) * v (Sum.inr i))

theorem largeEvenQPlus_comp_sumComm (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m (v ∘ Equiv.sumComm (Fin m) (Fin m)) = LargeEvenQPlus K m v := by
  simp only [largeEvenQPlus_def, Function.comp_apply, Equiv.sumComm_apply, Sum.swap_inl,
    Sum.swap_inr]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem permutationGL_mem_orthPlus {π : Equiv.Perm (Fin m ⊕ Fin m)}
    (hπ : ∀ v, LargeEvenQPlus K m (v ∘ ⇑(π⁻¹)) = LargeEvenQPlus K m v) :
    TauCeti.permutationGL (k := K) π ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) :=
  mem_orthGroup_of_isometry fun v => by rw [permutationGL_mulVec, hπ]

theorem pairSwap_inv (k : Fin m) : (pairSwap k)⁻¹ = pairSwap k :=
  Equiv.swap_inv _ _

theorem pairSwap_mem_orthPlus (k : Fin m) :
    TauCeti.permutationGL (k := K) (pairSwap k) ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) :=
  permutationGL_mem_orthPlus fun v => by
    rw [pairSwap_inv, largeEvenQPlus_comp_pairSwap]

theorem sumCongr_mem_orthPlus (τ : Equiv.Perm (Fin m)) :
    TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr τ τ) ∈
      LargeEvenOrthGroup (LargeEvenQPlus K m) :=
  permutationGL_mem_orthPlus fun v => by
    have : (Equiv.Perm.sumCongr τ τ)⁻¹ = Equiv.Perm.sumCongr τ⁻¹ τ⁻¹ := by
      ext x
      rcases x with x | x <;> rfl
    rw [this, largeEvenQPlus_comp_sumCongr]

theorem sumComm_mem_orthPlus :
    TauCeti.permutationGL (k := K) (Equiv.sumComm (Fin m) (Fin m)) ∈
      LargeEvenOrthGroup (LargeEvenQPlus K m) :=
  permutationGL_mem_orthPlus fun v => by
    have : (Equiv.sumComm (Fin m) (Fin m) : Equiv.Perm (Fin m ⊕ Fin m))⁻¹ =
        Equiv.sumComm (Fin m) (Fin m) := by
      ext x
      rcases x with x | x <;> rfl
    rw [this, largeEvenQPlus_comp_sumComm]

theorem diagGL_pairedUnits_mem_orthPlus (u : Fin m → Kˣ) :
    TauCeti.diagGL (pairedUnits u) ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) :=
  mem_orthGroup_of_isometry (largeEvenQPlus_diagGL u)

end SplitForm

section Siegel

variable {m : ℕ}

@[expose] def siegelS (i₀ i₁ : Fin m) : Matrix (Fin m) (Fin m) K :=
  Matrix.single i₀ i₁ 1 + Matrix.single i₁ i₀ 1

@[expose] def siegelMat (i₀ i₁ : Fin m) (c : K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  Matrix.fromBlocks 1 (c • siegelS i₀ i₁) 0 1

theorem siegelMat_mul (i₀ i₁ : Fin m) (c d : K) :
    siegelMat i₀ i₁ c * siegelMat i₀ i₁ d = siegelMat (K := K) i₀ i₁ (c + d) := by
  simp only [siegelMat, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, add_smul]
  rw [add_comm (d • siegelS i₀ i₁)]

theorem siegelMat_zero (i₀ i₁ : Fin m) : siegelMat (K := K) i₀ i₁ 0 = 1 := by
  rw [siegelMat, zero_smul, Matrix.fromBlocks_one]

@[expose] noncomputable def siegelGL (i₀ i₁ : Fin m) (c : K) : GL (Fin m ⊕ Fin m) K where
  val := siegelMat i₀ i₁ c
  inv := siegelMat i₀ i₁ (-c)
  val_inv := by rw [siegelMat_mul, add_neg_cancel, siegelMat_zero]
  inv_val := by rw [siegelMat_mul, neg_add_cancel, siegelMat_zero]

theorem coe_siegelGL (i₀ i₁ : Fin m) (c : K) :
    ((siegelGL i₀ i₁ c : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      siegelMat i₀ i₁ c :=
  rfl

@[expose] noncomputable def siegelHom (i₀ i₁ : Fin m) :
    Multiplicative K →* GL (Fin m ⊕ Fin m) K where
  toFun c := siegelGL i₀ i₁ (Multiplicative.toAdd c)
  map_one' := Units.ext (siegelMat_zero i₀ i₁)
  map_mul' _ _ := Units.ext (siegelMat_mul i₀ i₁ _ _).symm

theorem siegelHom_apply (i₀ i₁ : Fin m) (c : Multiplicative K) :
    siegelHom i₀ i₁ c = siegelGL i₀ i₁ (Multiplicative.toAdd c) :=
  rfl

theorem largeEvenQPlus_siegelMat [CharP K 2] (i₀ i₁ : Fin m) (c : K) (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m (siegelMat i₀ i₁ c *ᵥ v) = LargeEvenQPlus K m v := by
  rw [largeEvenQPlus_eq, largeEvenQPlus_eq, siegelMat, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add,
    add_dotProduct, Matrix.smul_mulVec, smul_dotProduct, siegelS, Matrix.add_mulVec,
    Matrix.single_mulVec, Matrix.single_mulVec, add_dotProduct]
  have h1 : ∀ (i : Fin m) (a : K), Function.update (0 : Fin m → K) i a ⬝ᵥ (v ∘ Sum.inr) =
      a * v (Sum.inr i) := fun i a => by
    simp [dotProduct, Function.update_apply, Finset.sum_ite_eq']
  rw [h1, h1]
  have h2 : 1 * (v ∘ Sum.inr) i₁ * v (Sum.inr i₀) + 1 * (v ∘ Sum.inr) i₀ * v (Sum.inr i₁) = 0 := by
    simp only [Function.comp_apply, one_mul]
    rw [mul_comm, CharTwo.add_self_eq_zero]
  rw [h2, smul_zero, add_zero]

theorem diagGL_pairedUnits_conj_siegelGL (u : Fin m → Kˣ) (i₀ i₁ : Fin m) (c : K) :
    TauCeti.diagGL (pairedUnits u) * siegelGL i₀ i₁ c * (TauCeti.diagGL (pairedUnits u))⁻¹ =
      siegelGL i₀ i₁ ((u i₀ : K) * (u i₁ : K) * c) := by
  apply Units.ext
  have hd : ∀ w : Fin m → Kˣ, ((TauCeti.diagGL (pairedUnits w) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.fromBlocks
        (Matrix.diagonal fun i => ((w i : Kˣ) : K)) 0 0
        (Matrix.diagonal fun i => (((w i)⁻¹ : Kˣ) : K)) := by
    intro w
    rw [TauCeti.diagGL_coe, Matrix.fromBlocks_diagonal]
    congr 1
    funext x
    rcases x with x | x <;> rfl
  have hinv : (TauCeti.diagGL (pairedUnits u))⁻¹ = TauCeti.diagGL (pairedUnits u⁻¹) := by
    rw [← pairedHom_apply, ← pairedHom_apply, ← map_inv, ← map_inv]
  rw [Units.val_mul, Units.val_mul, hinv, hd, hd, coe_siegelGL, coe_siegelGL, siegelMat, siegelMat,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.diagonal_mul_diagonal, Pi.inv_apply, inv_inv, Matrix.mul_smul, Matrix.smul_mul,
    smul_zero]
  congr 1
  · rw [show (fun i => ((u i : Kˣ) : K) * (((u i)⁻¹ : Kˣ) : K)) = fun _ => (1 : K) from
      funext fun i => Units.mul_inv (u i), Matrix.diagonal_one]
  · rw [siegelS, Matrix.mul_add, Matrix.add_mul, TauCeti.diagonal_mul_single_mul_diagonal,
      TauCeti.diagonal_mul_single_mul_diagonal, smul_add, smul_add, Matrix.smul_single,
      Matrix.smul_single, Matrix.smul_single, Matrix.smul_single]
    congr 2 <;> ring
  · rw [show (fun i => (((u i)⁻¹ : Kˣ) : K) * ((u i : Kˣ) : K)) = fun _ => (1 : K) from
      funext fun i => Units.inv_mul (u i), Matrix.diagonal_one]

end Siegel

section OmegaPlus

variable {m p : ℕ} {ζ : Kˣ}

theorem permutationGL_sumComm_conj (u : Fin m → Kˣ) :
    TauCeti.permutationGL (k := K) (Equiv.sumComm (Fin m) (Fin m)) *
      TauCeti.diagGL (pairedUnits u) *
      (TauCeti.permutationGL (k := K) (Equiv.sumComm (Fin m) (Fin m)))⁻¹ =
        (TauCeti.diagGL (pairedUnits u))⁻¹ := by
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix _ (Equiv.sumComm (Fin m) (Fin m))⁻¹
    (TauCeti.permutationGL_coe _), mul_inv_cancel_right, ← map_inv, ← pairedHom_apply, ← map_inv]
  congr 1
  funext x
  rcases x with x | x <;> rfl

theorem pow_card_eq_one_zmod (f : Fin m → Multiplicative (ZMod p)) : f ^ p = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i), ← ofAdd_nsmul, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem spTorusGL_mem_omegaPlus (hζ : ζ ^ p = 1) (hp : Odd p)
    (f : Fin m → Multiplicative (ZMod p)) :
    spTorusGL hζ f ∈ LargeEvenOmega (LargeEvenQPlus K m) := by
  obtain ⟨k, hk⟩ := hp
  set x := spTorusGL (K := K) hζ (f ^ (k + 1)) with hx
  set w := TauCeti.permutationGL (k := K) (Equiv.sumComm (Fin m) (Fin m)) with hw
  have hmem : ⁅x, w⁆ ∈ LargeEvenOmega (LargeEvenQPlus K m) :=
    Subgroup.commutator_mem_commutator (diagGL_pairedUnits_mem_orthPlus _) sumComm_mem_orthPlus
  have hconj : w * x * w⁻¹ = x⁻¹ := permutationGL_sumComm_conj _
  have hpow : f ^ (k + 1) * f ^ (k + 1) = f := by
    rw [← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ, pow_card_eq_one_zmod, one_mul]
  have : ⁅x, w⁆ = spTorusGL hζ f := by
    rw [commutatorElement_def]
    calc x * w * x⁻¹ * w⁻¹ = x * (w * x * w⁻¹)⁻¹ := by group
      _ = x * x := by rw [hconj, inv_inv]
      _ = spTorusGL hζ f := by rw [hx, ← map_mul, hpow]
  rw [← this]
  exact hmem

theorem permutationGL_pairSwap_mul_mem_omegaPlus {i k : Fin m} :
    TauCeti.permutationGL (k := K) (pairSwap i * pairSwap k) ∈
      LargeEvenOmega (LargeEvenQPlus K m) := by
  set π : Equiv.Perm (Fin m ⊕ Fin m) := Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k)
  have hperm : π * pairSwap k * π⁻¹ * (pairSwap k)⁻¹ = pairSwap i * pairSwap k := by
    rw [pairSwap_inv]
    congr 1
    unfold pairSwap
    rw [← Equiv.swap_apply_apply]
    simp [π]
  have hmem := Subgroup.commutator_mem_commutator (sumCongr_mem_orthPlus (K := K) (Equiv.swap i k))
    (pairSwap_mem_orthPlus (K := K) k)
  rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hperm] at hmem
  exact hmem

theorem pairSwap_mul_conj (i k : Fin m) (u : Fin m → Kˣ) :
    TauCeti.permutationGL (k := K) (pairSwap i * pairSwap k) * TauCeti.diagGL (pairedUnits u) *
        (TauCeti.permutationGL (k := K) (pairSwap i * pairSwap k))⁻¹ =
      TauCeti.diagGL (pairedUnits (Function.update (Function.update u k (u k)⁻¹) i
        ((Function.update u k (u k)⁻¹) i)⁻¹)) := by
  rw [map_mul, _root_.mul_inv_rev]
  calc TauCeti.permutationGL (pairSwap i) * TauCeti.permutationGL (pairSwap k) *
        TauCeti.diagGL (pairedUnits u) *
        ((TauCeti.permutationGL (pairSwap k))⁻¹ * (TauCeti.permutationGL (pairSwap i))⁻¹)
      = TauCeti.permutationGL (pairSwap i) * (TauCeti.permutationGL (pairSwap k) *
          TauCeti.diagGL (pairedUnits u) * (TauCeti.permutationGL (pairSwap k))⁻¹) *
          (TauCeti.permutationGL (pairSwap i))⁻¹ := by group
    _ = _ := by
      rw [permutationGL_pairSwap_conj, pairedUnits_comp_pairSwap, permutationGL_pairSwap_conj,
        pairedUnits_comp_pairSwap]

theorem exists_ne_ne_of_three_le (hm : 3 ≤ m) (i j : Fin m) : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := by
    intro k _
    by_cases hki : k = i
    · simp [hki]
    · simp [h k hki]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := this.trans (Finset.card_le_two (a := i) (b := j))
  omega

end OmegaPlus

section OmegaPlusLift

variable {m p : ℕ} {ζ : Kˣ}

theorem update_update_of_eq_one {u : Fin m → Kˣ} {i k : Fin m} (hk : u k = 1) :
    Function.update (Function.update u k (u k)⁻¹) i ((Function.update u k (u k)⁻¹) i)⁻¹ =
      Function.update u i (u i)⁻¹ := by
  have h : Function.update u k (u k)⁻¹ = u :=
    Function.update_eq_self_iff.mpr (by rw [hk, inv_one])
  rw [h]

theorem siegelGL_mul (i₀ i₁ : Fin m) (a b : K) :
    siegelGL i₀ i₁ a * siegelGL i₀ i₁ b = siegelGL i₀ i₁ (a + b) :=
  Units.ext (siegelMat_mul i₀ i₁ a b)

theorem siegelGL_inv (i₀ i₁ : Fin m) (a : K) :
    (siegelGL i₀ i₁ a)⁻¹ = siegelGL (K := K) i₀ i₁ (-a) :=
  inv_eq_of_mul_eq_one_right (by
    rw [siegelGL_mul, add_neg_cancel]
    exact Units.ext (siegelMat_zero i₀ i₁))

theorem siegelGL_mem_orthPlus [CharP K 2] (i₀ i₁ : Fin m) (c : K) :
    siegelGL i₀ i₁ c ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) :=
  mem_orthGroup_of_isometry (largeEvenQPlus_siegelMat i₀ i₁ c)

theorem zmodPowHom_mulSingle_of_ne (hζ : ζ ^ p = 1) {i l : Fin m} (hl : l ≠ i) :
    zmodPowHom hζ ((Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p)) :
      Fin m → Multiplicative (ZMod p)) l) = 1 := by
  rw [Pi.mulSingle_eq_of_ne hl, map_one]

theorem zmodPowHom_mulSingle_self (hζ : ζ ^ p = 1) (i : Fin m) :
    zmodPowHom hζ ((Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p)) :
      Fin m → Multiplicative (ZMod p)) i) = ζ := by
  rw [Pi.mulSingle_eq_same]
  have := zmodPowHom_natCast hζ 1
  rwa [Nat.cast_one, pow_one] at this

theorem siegelGL_mem_omegaPlus [CharP K 2] (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) {i₀ i₁ : Fin m}
    (h01 : i₁ ≠ i₀) (c : K) : siegelGL i₀ i₁ c ∈ LargeEvenOmega (LargeEvenQPlus K m) := by
  set u : Fin m → Kˣ := fun l => zmodPowHom hζ ((Pi.mulSingle i₀ (Multiplicative.ofAdd 1) :
    Fin m → Multiplicative (ZMod p)) l) with hu
  have hu0 : u i₀ = ζ := zmodPowHom_mulSingle_self hζ i₀
  have hu1 : u i₁ = 1 := zmodPowHom_mulSingle_of_ne hζ h01
  have hζK : (ζ : K) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hζ1 (Units.ext h)
  set c' := c / ((ζ : K) - 1) with hc'
  have hmem : ⁅TauCeti.diagGL (pairedUnits u), siegelGL i₀ i₁ c'⁆ ∈
      LargeEvenOmega (LargeEvenQPlus K m) :=
    Subgroup.commutator_mem_commutator (diagGL_pairedUnits_mem_orthPlus u)
      (siegelGL_mem_orthPlus i₀ i₁ c')
  rw [commutatorElement_def, diagGL_pairedUnits_conj_siegelGL, siegelGL_inv, siegelGL_mul, hu0,
    hu1] at hmem
  convert hmem using 2
  rw [hc', Units.val_one, mul_one]
  field_simp
  ring

theorem eq_one_of_spTorusGL_mem_scalars (hζ : ζ ^ p = 1) [NeZero p] (hζo : orderOf ζ = p)
    (hp : Odd p) {f : Fin m → Multiplicative (ZMod p)}
    (h : spTorusGL (K := K) hζ f ∈ LargeEvenScalars (Fin m ⊕ Fin m) K) : f = 1 := by
  apply spTorus_injective hζ hζo hp
  rw [map_one]
  exact (QuotientGroup.eq_one_iff (spTorusSp hζ f)).mpr h

theorem pairSwap_mul_conj_torusBasis_self (hζ : ζ ^ p = 1) {i k : Fin m} (hki : k ≠ i) :
    TauCeti.permutationGL (k := K) (pairSwap i * pairSwap k) * torusBasis (spTorusGL hζ) i *
        (TauCeti.permutationGL (k := K) (pairSwap i * pairSwap k))⁻¹ =
      (torusBasis (spTorusGL (K := K) hζ) i)⁻¹ := by
  set u : Fin m → Kˣ := fun l => zmodPowHom hζ ((Pi.mulSingle i (Multiplicative.ofAdd 1) :
    Fin m → Multiplicative (ZMod p)) l) with hu
  have hfun : Function.update u i (u i)⁻¹ = u⁻¹ := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · have h1 : u l = 1 := zmodPowHom_mulSingle_of_ne hζ hl
      rw [Function.update_of_ne hl, Pi.inv_apply, h1, inv_one]
  rw [torusBasis, spTorusGL_apply, pairSwap_mul_conj,
    update_update_of_eq_one (zmodPowHom_mulSingle_of_ne hζ hki)]
  rw [← hu, hfun, ← pairedHom_apply, ← pairedHom_apply, map_inv, map_inv]

theorem pairSwap_mul_conj_torusBasis_of_ne (hζ : ζ ^ p = 1) {i j k : Fin m} (hkj : k ≠ j)
    (hji : j ≠ i) :
    TauCeti.permutationGL (k := K) (pairSwap i * pairSwap k) * torusBasis (spTorusGL hζ) j *
        (TauCeti.permutationGL (k := K) (pairSwap i * pairSwap k))⁻¹ =
      torusBasis (spTorusGL (K := K) hζ) j := by
  rw [torusBasis, spTorusGL_apply, pairSwap_mul_conj,
    update_update_of_eq_one (zmodPowHom_mulSingle_of_ne hζ hkj)]
  congr 2
  exact Function.update_eq_self_iff.mpr (by rw [zmodPowHom_mulSingle_of_ne hζ (Ne.symm hji),
    inv_one])

theorem ggTorusLift_omegaPlus [Finite K] [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) :
    GGTorusLift p m (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units]; exact hpq)
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  refine ggTorusLift_of_matrixTorus hp hp2 (spTorusGL hζ) (spTorusGL_mem_omegaPlus hζ hodd)
    (fun f hf => eq_one_of_spTorusGL_mem_scalars hζ hζo hodd hf) ?_ (siegelHom i₀ i₁)
    (fun c => siegelGL_mem_omegaPlus hζ hζ1 h01 _) ?_ ?_ ?_
  · intro i j
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne_of_three_le hm i j
    refine ⟨TauCeti.permutationGL (pairSwap i * pairSwap k),
      permutationGL_pairSwap_mul_mem_omegaPlus, ?_, fun hji => ?_⟩
    · exact pairSwap_mul_conj_torusBasis_self hζ hki
    · exact pairSwap_mul_conj_torusBasis_of_ne hζ hkj hji
  · rintro ⟨u, hu⟩
    have e := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i₀) (Sum.inr i₁)) hu
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, siegelHom_apply,
      coe_siegelGL, siegelMat, siegelS, h01, Ne.symm h01] at e
  · intro c
    rw [sq, siegelHom_apply, siegelGL_mul, CharTwo.add_self_eq_zero]
    exact Units.ext (siegelMat_zero i₀ i₁)
  · intro f c
    refine ⟨Multiplicative.ofAdd ((zmodPowHom hζ (f i₀) : K) * (zmodPowHom hζ (f i₁) : K) *
      Multiplicative.toAdd c), ?_⟩
    rw [spTorusGL_apply, siegelHom_apply, siegelHom_apply, diagGL_pairedUnits_conj_siegelGL,
      toAdd_ofAdd]

theorem recipeOmegaPlus_torusLift {l n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 3 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F => Q R I F ∧ GGTorusLift p l R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    ggTorusLift_omegaPlus hp hp2 (by rw [hK]; exact hpn) hl⟩

end OmegaPlusLift

section OmegaMinus

variable {m p : ℕ} {ζ : Kˣ}

@[expose] def blockInlMat :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K →*
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by
    rw [Matrix.fromBlocks_multiply]
    simp

@[expose] noncomputable def blockInl : GL (Fin m ⊕ Fin m) K →* GL (LargeEvenMinusIdx m) K :=
  Units.map blockInlMat

theorem coe_blockInl (g : GL (Fin m ⊕ Fin m) K) :
    ((blockInl g : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
      Matrix.fromBlocks (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) 0 0 1 :=
  rfl

theorem largeEvenQMinus_eq (b c : K) (w : LargeEvenMinusIdx m → K) :
    LargeEvenQMinus m b c w = LargeEvenQPlus K m (w ∘ Sum.inl) +
      (w (Sum.inr 0) ^ 2 + b * w (Sum.inr 0) * w (Sum.inr 1) + c * w (Sum.inr 1) ^ 2) := by
  simp only [LargeEvenQMinus, largeEvenQPlus_def, Function.comp_apply]
  ring

theorem largeEvenQMinus_blockInl {b c : K} {g : GL (Fin m ⊕ Fin m) K}
    (hg : ∀ v, LargeEvenQPlus K m ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) =
      LargeEvenQPlus K m v) (w : LargeEvenMinusIdx m → K) :
    LargeEvenQMinus m b c
        ((blockInl g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ w) =
      LargeEvenQMinus m b c w := by
  rw [largeEvenQMinus_eq, largeEvenQMinus_eq, coe_blockInl, Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl, Matrix.zero_mulVec, add_zero, hg]
  simp

theorem map_blockInl_orth_le (b c : K) :
    (LargeEvenOrthGroup (LargeEvenQPlus K m)).map blockInl ≤
      LargeEvenOrthGroup (LargeEvenQMinus m b c) := by
  rw [largeEvenOrthGroup_def, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact Subgroup.subset_closure (largeEvenQMinus_blockInl hg)

theorem map_blockInl_omega_le (b c : K) :
    (LargeEvenOmega (LargeEvenQPlus K m)).map blockInl ≤
      LargeEvenOmega (LargeEvenQMinus m b c) := by
  rw [largeEvenOmega_def, largeEvenOmega_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono (map_blockInl_orth_le b c) (map_blockInl_orth_le b c)

theorem blockInl_mem_omegaMinus (b c : K) {g : GL (Fin m ⊕ Fin m) K}
    (hg : g ∈ LargeEvenOmega (LargeEvenQPlus K m)) :
    blockInl g ∈ LargeEvenOmega (LargeEvenQMinus m b c) :=
  map_blockInl_omega_le b c ⟨g, hg, rfl⟩

theorem mem_scalars_of_blockInl {g : GL (Fin m ⊕ Fin m) K}
    (h : blockInl g ∈ LargeEvenScalars (LargeEvenMinusIdx m) K) :
    g ∈ LargeEvenScalars (Fin m ⊕ Fin m) K := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, Units.ext ?_⟩
  ext x y
  have e := congrArg (fun h : GL (LargeEvenMinusIdx m) K =>
    (h : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inl x) (Sum.inl y)) hu
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_blockInl,
    Matrix.fromBlocks_apply₁₁] at e
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  rw [← e]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [Matrix.diagonal_apply_ne _ hxy,
      Matrix.diagonal_apply_ne _ (fun h => hxy (Sum.inl_injective h))]

theorem ggTorusLift_omegaMinus [Finite K] [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) (b c : K) :
    GGTorusLift p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units]; exact hpq)
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  refine ggTorusLift_of_matrixTorus hp hp2 (blockInl.comp (spTorusGL hζ))
    (fun f => blockInl_mem_omegaMinus b c (spTorusGL_mem_omegaPlus hζ hodd f))
    (fun f hf => eq_one_of_spTorusGL_mem_scalars hζ hζo hodd (mem_scalars_of_blockInl hf)) ?_
    (blockInl.comp (siegelHom i₀ i₁))
    (fun _ => blockInl_mem_omegaMinus b c (siegelGL_mem_omegaPlus hζ hζ1 h01 _)) ?_ ?_ ?_
  · intro i j
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne_of_three_le hm i j
    refine ⟨blockInl (TauCeti.permutationGL (pairSwap i * pairSwap k)),
      blockInl_mem_omegaMinus b c permutationGL_pairSwap_mul_mem_omegaPlus, ?_, fun hji => ?_⟩
    · have h1 : torusBasis (blockInl.comp (spTorusGL (K := K) hζ)) i =
          blockInl (torusBasis (spTorusGL hζ) i) := rfl
      rw [h1, ← map_inv blockInl (TauCeti.permutationGL (pairSwap i * pairSwap k)), ← map_mul,
        ← map_mul, pairSwap_mul_conj_torusBasis_self hζ hki, map_inv]
    · have h1 : torusBasis (blockInl.comp (spTorusGL (K := K) hζ)) j =
          blockInl (torusBasis (spTorusGL hζ) j) := rfl
      rw [h1, ← map_inv blockInl (TauCeti.permutationGL (pairSwap i * pairSwap k)), ← map_mul,
        ← map_mul, pairSwap_mul_conj_torusBasis_of_ne hζ hkj hji]
  · rintro ⟨u, hu⟩
    have e := congrArg (fun g : GL (LargeEvenMinusIdx m) K =>
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inl (Sum.inl i₀))
        (Sum.inl (Sum.inr i₁))) hu
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, siegelHom_apply,
      coe_siegelGL, siegelMat, siegelS, coe_blockInl, h01, Ne.symm h01] at e
  · intro x
    rw [MonoidHom.comp_apply, ← map_pow, sq, siegelHom_apply, siegelGL_mul,
      CharTwo.add_self_eq_zero, show siegelGL (K := K) i₀ i₁ 0 = 1 from
        Units.ext (siegelMat_zero i₀ i₁), map_one]
  · intro f x
    refine ⟨Multiplicative.ofAdd ((zmodPowHom hζ (f i₀) : K) * (zmodPowHom hζ (f i₁) : K) *
      Multiplicative.toAdd x), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul,
      ← map_mul, spTorusGL_apply, siegelHom_apply, siegelHom_apply,
      diagGL_pairedUnits_conj_siegelGL, toAdd_ofAdd]

theorem recipeOmegaMinus_torusLift {l n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 3 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus l (2 ^ n) fun R _ I F => Q R I F ∧ GGTorusLift p l R := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ,
    ggTorusLift_omegaMinus hp hp2 (by rw [hK]; exact hpn) hl b c⟩

end OmegaMinus

end TableBSymp

theorem ne_two_of_dvd_two_pow_sub_one' {p n : ℕ} (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 hpn
  rw [Nat.sub_sub_self h1] at this
  omega

open TableBSymp in
theorem largeEvenLabelAll_torusLift_D {lab : LargeEvenLabel} (htag : lab.tag = .D)
    (hlab : LargeEvenInLambda2 lab) (hl : 4 ≤ lab.rank) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p lab.rank R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  have hp2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · exact recipeOmegaPlus_torusLift hp hp2 hpn (by omega) hQ

open TableBSymp in
theorem largeEvenLabelAll_torusLift_twD {lab : LargeEvenLabel} (htag : lab.tag = .twD)
    (hlab : LargeEvenInLambda2 lab) (hl : 4 ≤ lab.rank) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - 1) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  have hp2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · exact recipeOmegaMinus_torusLift hp hp2 hpn (by omega) hQ

namespace TableBSymp

end TableBSymp

end CFSG.StandardType
