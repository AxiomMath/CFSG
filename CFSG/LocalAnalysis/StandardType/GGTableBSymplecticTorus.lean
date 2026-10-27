module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
public import CFSG.LocalAnalysis.StandardType.Marking
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import TauCeti.LinearAlgebra.SymplecticGroup
import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

variable {K : Type} [Field K] {m : ℕ}

@[expose] def pairedUnits (u : Fin m → Kˣ) : Fin m ⊕ Fin m → Kˣ :=
  Sum.elim u fun i => (u i)⁻¹

@[expose] def pairedHom : (Fin m → Kˣ) →* (Fin m ⊕ Fin m → Kˣ) where
  toFun := pairedUnits
  map_one' := by
    funext x
    cases x <;> simp [pairedUnits]
  map_mul' u v := by
    funext x
    cases x <;> simp [pairedUnits, mul_comm]

theorem pairedHom_apply (u : Fin m → Kˣ) : pairedHom u = pairedUnits u :=
  rfl

theorem largeEvenSpForm_apply (x y : Fin m ⊕ Fin m) :
    LargeEvenSpForm K m x y = match x, y with
      | .inl a, .inr b => if a = b then 1 else 0
      | .inr a, .inl b => if a = b then -1 else 0
      | _, _ => 0 := by
  rcases x with a | a <;> rcases y with b | b <;>
    simp [largeEvenSpForm_def, Matrix.fromBlocks, Matrix.one_apply]
  split_ifs <;> simp

theorem diagGL_pairedUnits_mem (u : Fin m → Kˣ) :
    TauCeti.diagGL (pairedUnits u) ∈ LargeEvenSpGroup K m := by
  rw [largeEvenSpGroup_def]
  refine Subgroup.subset_closure ?_
  simp only [Set.mem_ofPred_eq]
  rw [TauCeti.diagGL_coe, Matrix.diagonal_transpose]
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases x with a | a <;> rcases y with b | b <;>
    simp only [largeEvenSpForm_apply, pairedUnits, Sum.elim_inl, Sum.elim_inr] <;>
    (try split_ifs) <;> simp_all

theorem permutationGL_mem_sp (π : Equiv.Perm (Fin m ⊕ Fin m))
    (hπ : ∀ x y, LargeEvenSpForm K m (π x) (π y) = LargeEvenSpForm K m x y) :
    TauCeti.permutationGL (k := K) π ∈ LargeEvenSpGroup K m := by
  refine Subgroup.subset_closure ?_
  simp only [Set.mem_ofPred_eq]
  rw [TauCeti.permutationGL_coe, Matrix.transpose_permMatrix, inv_inv, Equiv.Perm.permMatrix,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  simp only [Matrix.submatrix_apply, id]
  rw [Equiv.Perm.inv_def, Equiv.symm_symm]
  exact hπ x y

@[expose] def pairSwap (i : Fin m) : Equiv.Perm (Fin m ⊕ Fin m) :=
  Equiv.swap (Sum.inl i) (Sum.inr i)

set_option linter.unusedSimpArgs false in
theorem largeEvenSpForm_pairSwap [CharP K 2] (i : Fin m) (x y : Fin m ⊕ Fin m) :
    LargeEvenSpForm K m (pairSwap i x) (pairSwap i y) = LargeEvenSpForm K m x y := by
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  rw [largeEvenSpForm_apply, largeEvenSpForm_apply]
  rcases x with a | a <;> rcases y with b | b <;>
    by_cases ha : a = i <;> by_cases hb : b = i <;>
    first
      | (subst ha; subst hb; simp [pairSwap, hneg])
      | (subst ha; simp [pairSwap, Equiv.swap_apply_def, hb, Ne.symm hb, hneg])
      | (subst hb; simp [pairSwap, Equiv.swap_apply_def, ha, Ne.symm ha, hneg])
      | simp [pairSwap, Equiv.swap_apply_def, ha, hb, Ne.symm ha, Ne.symm hb, hneg]

theorem pairedUnits_comp_pairSwap (u : Fin m → Kˣ) (i : Fin m) :
    pairedUnits u ∘ pairSwap i = pairedUnits (Function.update u i (u i)⁻¹) := by
  funext x
  rcases x with a | a <;> by_cases ha : a = i
  · subst ha
    simp [pairedUnits, pairSwap]
  · simp [pairedUnits, pairSwap, Equiv.swap_apply_def, ha]
  · subst ha
    simp [pairedUnits, pairSwap]
  · simp [pairedUnits, pairSwap, Equiv.swap_apply_def, ha]

theorem permutationGL_pairSwap_conj (i : Fin m) (d : Fin m ⊕ Fin m → Kˣ) :
    TauCeti.permutationGL (k := K) (pairSwap i) * TauCeti.diagGL d *
        (TauCeti.permutationGL (k := K) (pairSwap i))⁻¹ =
      TauCeti.diagGL (d ∘ pairSwap i) := by
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix (TauCeti.permutationGL (k := K) (pairSwap i))
    (pairSwap i)⁻¹ (TauCeti.permutationGL_coe _), mul_inv_cancel_right]
  congr 2

theorem mem_sp_of_mem_symplecticGroup {g : GL (Fin m ⊕ Fin m) K}
    (h : (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) ∈ Matrix.symplecticGroup (Fin m) K) :
    g ∈ LargeEvenSpGroup K m :=
  Subgroup.subset_closure
    ((CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mpr h)

theorem transvection_inl_inr_eq (i₀ : Fin m) (c : K) :
    Matrix.transvection (Sum.inl i₀ : Fin m ⊕ Fin m) (Sum.inr i₀) c =
      Matrix.fromBlocks 1 (Matrix.single i₀ i₀ c) 0 1 := by
  ext x y
  rcases x with a | a <;> rcases y with b | b <;>
    simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Matrix.fromBlocks]

@[expose] noncomputable def spRootGL (i₀ : Fin m) : Multiplicative K →* GL (Fin m ⊕ Fin m) K :=
  TauCeti.transvectionHom (Sum.inl_ne_inr : (Sum.inl i₀ : Fin m ⊕ Fin m) ≠ Sum.inr i₀)

theorem spRootGL_coe (i₀ : Fin m) (c : Multiplicative K) :
    ((spRootGL i₀ c : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      Matrix.transvection (Sum.inl i₀) (Sum.inr i₀) (Multiplicative.toAdd c) := by
  rw [spRootGL, TauCeti.transvectionHom_apply, TauCeti.coe_transvectionUnit]

theorem spRootGL_mem (i₀ : Fin m) (c : Multiplicative K) :
    spRootGL i₀ c ∈ LargeEvenSpGroup K m := by
  apply mem_sp_of_mem_symplecticGroup
  rw [spRootGL_coe, transvection_inl_inr_eq]
  exact SymplecticGroup.fromBlocks_upper_mem (by rw [Matrix.transpose_single])

theorem diagGL_pairedUnits_conj_spRootGL (u : Fin m → Kˣ) (i₀ : Fin m) (c : Multiplicative K) :
    TauCeti.diagGL (pairedUnits u) * spRootGL i₀ c * (TauCeti.diagGL (pairedUnits u))⁻¹ =
      spRootGL i₀ (Multiplicative.ofAdd ((u i₀ : K) * Multiplicative.toAdd c * (u i₀ : K))) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, TauCeti.diagGL_coe, TauCeti.diagGL_coe, spRootGL_coe,
    spRootGL_coe, TauCeti.diagonal_mul_transvection_mul_diagonal]
  · simp [pairedUnits]
  · intro a
    simp

section Torus

variable {p : ℕ} {ζ : Kˣ}

omit [Field K] in
theorem zmodPowHom_eq_one_iff {L' : Type*} [Group L'] [NeZero p] {t : L'} (ht : t ^ p = 1)
    (hto : orderOf t = p) {a : Multiplicative (ZMod p)} : zmodPowHom ht a = 1 ↔ a = 1 := by
  rw [zmodPowHom_apply, ← orderOf_dvd_iff_pow_eq_one, hto]
  constructor
  · intro h
    have h0 : (Multiplicative.toAdd a).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt (Multiplicative.toAdd a))
    rw [ZMod.val_eq_zero] at h0
    rw [← ofAdd_toAdd a, h0, ofAdd_zero]
  · rintro rfl
    simp

@[expose] noncomputable def spTorusGL (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* GL (Fin m ⊕ Fin m) K :=
  TauCeti.diagGL.comp (pairedHom.comp ((zmodPowHom hζ).compLeft (Fin m)))

theorem spTorusGL_apply (hζ : ζ ^ p = 1) (f : Fin m → Multiplicative (ZMod p)) :
    spTorusGL hζ f = TauCeti.diagGL (pairedUnits fun i => zmodPowHom hζ (f i)) :=
  rfl

theorem spTorusGL_mem (hζ : ζ ^ p = 1) (f : Fin m → Multiplicative (ZMod p)) :
    spTorusGL hζ f ∈ LargeEvenSpGroup K m :=
  diagGL_pairedUnits_mem _

@[expose] noncomputable def spTorusSp (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* LargeEvenSpGroup K m :=
  (spTorusGL hζ).codRestrict _ (spTorusGL_mem hζ)

theorem spTorusSp_coe (hζ : ζ ^ p = 1) (f : Fin m → Multiplicative (ZMod p)) :
    ((spTorusSp hζ f : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) = spTorusGL hζ f :=
  rfl

@[expose] noncomputable def spTorus (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* LargeEvenProj (LargeEvenSpGroup K m) :=
  (LargeEvenProjMk _).comp (spTorusSp hζ)

theorem spTorus_injective (hζ : ζ ^ p = 1) [NeZero p] (hζo : orderOf ζ = p) (hp : Odd p) :
    Function.Injective (spTorus (m := m) hζ) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  have hf' : ((spTorusSp hζ f : LargeEvenSpGroup K m) : LargeEvenProj (LargeEvenSpGroup K m)) = 1 :=
    hf
  have h1 : (spTorusSp hζ f : GL (Fin m ⊕ Fin m) K) ∈ LargeEvenScalars (Fin m ⊕ Fin m) K :=
    (QuotientGroup.eq_one_iff (spTorusSp hζ f)).mp hf'
  obtain ⟨c, hc⟩ := h1
  rw [spTorusSp_coe, spTorusGL_apply] at hc
  funext i
  have e1 := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i) (Sum.inl i)) hc
  have e2 := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inr i) (Sum.inr i)) hc
  simp only [TauCeti.diagGL_coe, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, pairedUnits, Sum.elim_inl, Sum.elim_inr] at e1 e2
  set χ := zmodPowHom hζ with hχ
  have h3 : χ (f i) = (χ (f i))⁻¹ := Units.ext (e1.symm.trans e2)
  have h4 : χ (f i) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h3]
    exact mul_inv_cancel _
  have h5 : χ (f i) ^ p = 1 := by
    rw [← map_pow]
    have : f i ^ p = 1 := by
      rw [← ofAdd_toAdd (f i), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        ofAdd_zero]
    rw [this, map_one]
  obtain ⟨k, hk⟩ := hp
  have h6 : χ (f i) = 1 := by
    have : χ (f i) ^ (2 * k + 1) = (χ (f i) ^ 2) ^ k * χ (f i) := by rw [pow_succ, pow_mul]
    rw [← hk, h4, one_pow, one_mul, h5] at this
    exact this.symm
  exact (zmodPowHom_eq_one_iff hζ hζo).mp h6

@[expose] noncomputable def spSwapSp [CharP K 2] (i : Fin m) : LargeEvenSpGroup K m :=
  ⟨TauCeti.permutationGL (pairSwap i), permutationGL_mem_sp _ (largeEvenSpForm_pairSwap i)⟩

theorem spSwapSp_coe [CharP K 2] (i : Fin m) :
    ((spSwapSp i : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) =
      TauCeti.permutationGL (pairSwap i) :=
  rfl

theorem spSwap_conj_spTorus [CharP K 2] (hζ : ζ ^ p = 1) (i : Fin m)
    (f : Fin m → Multiplicative (ZMod p)) :
    LargeEvenProjMk _ (spSwapSp i) * spTorus hζ f * (LargeEvenProjMk _ (spSwapSp i))⁻¹ =
      spTorus hζ (Function.update f i (f i)⁻¹) := by
  rw [spTorus, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spSwapSp_coe, spTorusSp_coe,
    spTorusSp_coe, spTorusGL_apply, spTorusGL_apply, permutationGL_pairSwap_conj,
    pairedUnits_comp_pairSwap]
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

@[expose] noncomputable def spRootSp (i₀ : Fin m) : Multiplicative K →* LargeEvenSpGroup K m :=
  (spRootGL i₀).codRestrict _ (spRootGL_mem i₀)

theorem spRootSp_coe (i₀ : Fin m) (a : Multiplicative K) :
    ((spRootSp i₀ a : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) = spRootGL i₀ a :=
  rfl

@[expose] noncomputable def spRootGroup (i₀ : Fin m) :
    Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) :=
  ((LargeEvenProjMk _).comp (spRootSp i₀)).range

theorem spRootGroup_ne_bot (i₀ : Fin m) : spRootGroup (K := K) i₀ ≠ ⊥ := by
  intro h
  have hmem : (LargeEvenProjMk _).comp (spRootSp i₀) (Multiplicative.ofAdd (1 : K)) ∈
      spRootGroup (K := K) i₀ := ⟨_, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have hmem' : ((spRootSp i₀ (Multiplicative.ofAdd (1 : K)) : LargeEvenSpGroup K m) :
      LargeEvenProj (LargeEvenSpGroup K m)) = 1 := hmem
  have h1 : ((spRootSp i₀ (Multiplicative.ofAdd (1 : K)) : LargeEvenSpGroup K m) :
      GL (Fin m ⊕ Fin m) K) ∈ LargeEvenScalars (Fin m ⊕ Fin m) K :=
    (QuotientGroup.eq_one_iff (spRootSp i₀ (Multiplicative.ofAdd (1 : K)))).mp hmem'
  obtain ⟨c, hc⟩ := h1
  rw [spRootSp_coe] at hc
  have e := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i₀) (Sum.inr i₀)) hc
  simp only [spRootGL_coe, toAdd_ofAdd, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply] at e
  rw [Matrix.diagonal_apply_ne _ Sum.inl_ne_inr, Matrix.transvection, Matrix.add_apply,
    Matrix.one_apply_ne Sum.inl_ne_inr, Matrix.single_apply_same, zero_add] at e
  exact zero_ne_one e

theorem spRootGroup_isPGroup [CharP K 2] (i₀ : Fin m) : IsPGroup 2 (spRootGroup (K := K) i₀) := by
  rintro ⟨_, a, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← map_pow]
  have : a ^ 2 = 1 := by
    rw [← ofAdd_toAdd a, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
  rw [this, map_one, Subgroup.coe_one]

theorem spTorus_conj_spRootGroup (hζ : ζ ^ p = 1) (i₀ : Fin m) (f : Fin m → Multiplicative (ZMod p))
    {u : LargeEvenProj (LargeEvenSpGroup K m)} (hu : u ∈ spRootGroup i₀) :
    spTorus hζ f * u * (spTorus hζ f)⁻¹ ∈ spRootGroup i₀ := by
  obtain ⟨a, rfl⟩ := hu
  refine ⟨Multiplicative.ofAdd (((zmodPowHom hζ (f i₀) : Kˣ) : K) * Multiplicative.toAdd a *
    ((zmodPowHom hζ (f i₀) : Kˣ) : K)), ?_⟩
  rw [spTorus, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv,
    ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spRootSp_coe, spRootSp_coe,
    spTorusSp_coe, spTorusGL_apply, diagGL_pairedUnits_conj_spRootGL]

end Torus

theorem ggTorusLift_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGTorusLift p m (LargeEvenProj (LargeEvenSpGroup K m)) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  refine ggTorusLift_of_torus hp hp2 (spTorus hζ) (spTorus_injective hζ hζo (hp.odd_of_ne_two hp2))
    ?_ (spRootGroup_ne_bot (K := K) ⟨0, hm⟩) (spRootGroup_isPGroup _)
    fun d u hu => spTorus_conj_spRootGroup hζ _ d hu
  intro i j
  refine ⟨LargeEvenProjMk _ (spSwapSp i), ?_, fun hji => ?_⟩
  · rw [torusBasis, spSwap_conj_spTorus, ← map_inv, ← Pi.mulSingle_inv]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx
      simp
    · simp [Function.update_of_ne hx, Pi.mulSingle_eq_of_ne hx]
  · rw [torusBasis, spSwap_conj_spTorus]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx
      simp only [Function.update_self, Pi.mulSingle_eq_of_ne (Ne.symm hji)]
      exact (inv_one : (1 : Multiplicative (ZMod p))⁻¹ = 1)
    · simp [Function.update_of_ne hx]

theorem recipeSymplectic_torusLift {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 1 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧ GGTorusLift p l R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    ggTorusLift_symplectic hp hp2 (by rw [hK]; exact hpn) hl⟩

end TableBSymp

end CFSG.StandardType
