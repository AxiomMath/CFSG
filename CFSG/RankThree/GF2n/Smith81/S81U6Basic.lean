module

public import CFSG.RankThree.GF2n.Smith81.S81A5Pure
public import CFSG.RankThree.GF2n.Smith81.S81A5Beta
public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

@[expose] noncomputable def theta (σ : K ≃+* K) : Cube K →+ Cube K where
  toFun ξ := ∑ I : Set.powersetCard (Fin 6) 3, σ (coord K ξ I) • cubeBasis K (cmpl I)
  map_zero' := by simp [coord_zero]
  map_add' := by
    intro a b
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [coord_add, map_add, add_smul]

theorem theta_apply (ξ : Cube K) :
    theta σ ξ = ∑ I : Set.powersetCard (Fin 6) 3, σ (coord K ξ I) • cubeBasis K (cmpl I) := rfl

theorem cmpl_cmpl (I : Set.powersetCard (Fin 6) 3) : cmpl (cmpl I) = I := by
  apply Subtype.ext
  show Finset.univ \ (Finset.univ \ I.val) = I.val
  simp

theorem cmpl_injective : Function.Injective (cmpl : Set.powersetCard (Fin 6) 3 → _) :=
  Function.LeftInverse.injective cmpl_cmpl

theorem coord_theta (ξ : Cube K) (I : Set.powersetCard (Fin 6) 3) :
    coord K (theta σ ξ) (cmpl I) = σ (coord K ξ I) := by
  rw [theta_apply]
  unfold coord
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single I]
  · simp [Finsupp.single_apply]
  · intro J _ hJ
    have : cmpl J ≠ cmpl I := fun h => hJ (cmpl_injective h)
    simp [Finsupp.single_apply, this]
  · intro h; exact absurd (Finset.mem_univ I) h

theorem theta_smul (c : K) (ξ : Cube K) : theta σ (c • ξ) = σ c • theta σ ξ := by
  rw [theta_apply, theta_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [coord_smul, map_mul, smul_smul]

theorem theta_theta (hσ : ∀ c, σ (σ c) = c) (ξ : Cube K) : theta σ (theta σ ξ) = ξ := by
  apply (cubeBasis K).ext_elem
  intro I
  show coord K (theta σ (theta σ ξ)) I = coord K ξ I
  have h1 := coord_theta (σ := σ) (theta σ ξ) (cmpl I)
  have h2 := coord_theta (σ := σ) ξ I
  rw [cmpl_cmpl] at h1
  rw [h1, h2, hσ]

private theorem rho_one' : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem rho_mul_apply' (g h : GL (Fin 6) K) (ξ : Cube K) :
    rho K (g * h) ξ = rho K g (rho K h ξ) := by
  rw [rho, map_mul, Module.End.mul_apply]

abbrev Idx : Type := Set.powersetCard (Fin 6) 3

@[expose] noncomputable def cmat (g : GL (Fin 6) K) : Matrix Idx Idx K :=
  fun I J => coord K (rho K g (cubeBasis K J)) I

theorem coord_rho (g : GL (Fin 6) K) (ξ : Cube K) (I : Idx) :
    coord K (rho K g ξ) I = ∑ J, cmat g I J * coord K ξ J := by
  conv_lhs => rw [← (cubeBasis K).sum_repr ξ]
  simp only [map_sum, map_smul, coord, cmat, smul_eq_mul, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [mul_comm]

theorem cmat_mul (g h : GL (Fin 6) K) : cmat (g * h) = cmat g * cmat h := by
  ext I J
  rw [Matrix.mul_apply]
  unfold cmat
  rw [rho_mul_apply']
  exact coord_rho g (rho K h (cubeBasis K J)) I

theorem cmat_one : cmat (1 : GL (Fin 6) K) = 1 := by
  ext I J
  unfold cmat
  rw [rho_one', Module.End.one_apply, Matrix.one_apply]
  unfold coord
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

theorem cmat_apply_det (g : GL (Fin 6) K) (I J : Idx) :
    cmat g I J = (Matrix.of fun (i j : Fin 3) =>
      (g : Matrix (Fin 6) (Fin 6) K) (enum I j) (enum J i)).det := by
  unfold cmat
  rw [cubeBasis_apply, rho_ιMulti, coord_ιMulti]
  congr 1
  ext i j
  simp [Matrix.mulVec, dotProduct, e, Pi.single_apply]

theorem coe_inv_of_mem_SUid {g : GL (Fin 6) K} (hg : g ∈ SUid σ 6) :
    ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = conjTr σ (g : Matrix (Fin 6) (Fin 6) K) := by
  rw [Matrix.coe_units_inv]
  exact Matrix.inv_eq_left_inv hg.2

theorem cmat_inv_of_mem_SUid {g : GL (Fin 6) K} (hg : g ∈ SUid σ 6) (I J : Idx) :
    cmat g⁻¹ I J = σ (cmat g J I) := by
  rw [cmat_apply_det, cmat_apply_det, coe_inv_of_mem_SUid hg]
  set M : Matrix (Fin 3) (Fin 3) K :=
    Matrix.of fun (i j : Fin 3) => (g : Matrix (Fin 6) (Fin 6) K) (enum J i) (enum I j) with hM
  have h1 : (Matrix.of fun (i j : Fin 3) =>
      conjTr σ (g : Matrix (Fin 6) (Fin 6) K) (enum I j) (enum J i)) = M.map σ := by
    ext i j
    simp [conjTr, hM]
  have h2 : (Matrix.of fun (i j : Fin 3) =>
      (g : Matrix (Fin 6) (Fin 6) K) (enum J j) (enum I i)) = Mᵀ := by
    ext i j
    simp [hM]
  rw [h1, h2, Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom M).symm

@[expose] noncomputable def bmat : Matrix Idx Idx K := fun I J => beta K (cubeBasis K I) (cubeBasis K J)

theorem bmat_eq_zero {I J : Idx} (h : J ≠ cmpl I) : bmat (K := K) I J = 0 := by
  apply beta_cubeBasis_of_not_disjoint
  intro hd
  apply h
  have := eq_of_disjoint_cmpl (I := cmpl I) (I' := J) (by rw [cmpl_cmpl]; exact hd.symm)
  rw [this]

theorem bmat_cmpl_ne_zero (I : Idx) : bmat (K := K) I (cmpl I) ≠ 0 :=
  beta_cubeBasis_ne_zero_of_disjoint (disjoint_cmpl I)

theorem beta_expand (ξ η : Cube K) :
    beta K ξ η = ∑ a, ∑ b, coord K ξ a * coord K η b * bmat a b := by
  rw [beta1_expand_left ξ η]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [beta1_expand_right (cubeBasis K a) η, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : coord K (cubeBasis K a) a = 1 := by simp [coord]
  unfold bmat
  ring

private def tp₀ : Set.powersetCard (Fin 6) 6 := ⟨Finset.univ, by simp⟩

private theorem bmat_cmpl_formula (I : Idx) :
    ∃ u : ℤˣ, bmat (K := K) I (cmpl I) = u • exteriorPower.topEquiv (Pi.basisFun K (Fin 6))
      ((Pi.basisFun K (Fin 6)).exteriorPower 6 tp₀) := by
  have hk : (3 : ℕ) + 3 = Fintype.card (Fin 6) := by simp
  have h := disjoint_cmpl I
  have hcard : (I.val ∪ (cmpl I).val).card = Fintype.card (Fin 6) := by
    simp [Finset.card_union_of_disjoint h, beta1_card I, beta1_card (cmpl I)]
  have hIJ : I.val ∪ (cmpl I).val = tp₀.val := Finset.eq_univ_of_card _ hcard
  have h1 := exteriorPower.wedge_apply_of_disjoint (Pi.basisFun K (Fin 6)) hk h
  have hw : exteriorPower.wedge K (Fin 6 → K) 3 3 (cubeBasis K I) (cubeBasis K (cmpl I)) =
      Set.powersetCard.sign I • (Pi.basisFun K (Fin 6)).exteriorPower 6 tp₀ := by
    unfold cubeBasis
    apply Subtype.ext
    rw [SetLike.val_smul_of_tower, h1, hIJ, ExteriorAlgebra.basis_eq_coe_basis]
  refine ⟨Set.powersetCard.sign I, ?_⟩
  show exteriorPower.topEquiv (Pi.basisFun K (Fin 6))
    (exteriorPower.wedge K (Fin 6 → K) 3 3 (cubeBasis K I) (cubeBasis K (cmpl I))) = _
  rw [hw, map_zsmul_unit]

theorem bmat_cmpl_eq [CharP K 2] (I I' : Idx) :
    bmat (K := K) I (cmpl I) = bmat I' (cmpl I') := by
  obtain ⟨u, hu⟩ := bmat_cmpl_formula (K := K) I
  obtain ⟨u', hu'⟩ := bmat_cmpl_formula (K := K) I'
  have key : ∀ (v : ℤˣ) (x : K), v • x = x := by
    intro v x
    rcases Int.units_eq_one_or v with rfl | rfl
    · simp
    · simp [CharTwo.neg_eq]
  rw [hu, hu', key, key]

@[expose] def Pm : Matrix Idx Idx K := fun I J => if J = cmpl I then 1 else 0

theorem Pm_apply_cmpl (I : Idx) : (Pm : Matrix Idx Idx K) I (cmpl I) = 1 := by simp [Pm]

theorem Pm_mul_apply (M : Matrix Idx Idx K) (I J : Idx) :
    (Pm * M * Pm : Matrix Idx Idx K) I J = M (cmpl I) (cmpl J) := by
  simp only [Matrix.mul_apply, Pm]
  simp [cmpl_cmpl]
  rw [Finset.sum_eq_single (cmpl J)]
  · simp [cmpl_cmpl]
  · intro x _ hx
    have : J ≠ cmpl x := fun h => hx (by rw [h, cmpl_cmpl])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Pm_mul_self : (Pm : Matrix Idx Idx K) * Pm = 1 := by
  ext I J
  have h := Pm_mul_apply (1 : Matrix Idx Idx K) I J
  rw [Matrix.mul_one] at h
  rw [h, Matrix.one_apply, Matrix.one_apply]
  by_cases hIJ : I = J
  · simp [hIJ]
  · have : cmpl I ≠ cmpl J := fun e => hIJ (cmpl_injective e)
    simp [hIJ, this]

theorem bmat_eq_smul_Pm [CharP K 2] : ∃ t : K, t ≠ 0 ∧ (bmat : Matrix Idx Idx K) = t • Pm := by
  let I₀ : Idx := ⟨{0, 1, 2}, by show ({0, 1, 2} : Finset (Fin 6)).card = 3; decide⟩
  refine ⟨bmat I₀ (cmpl I₀), bmat_cmpl_ne_zero I₀, ?_⟩
  ext I J
  simp only [Matrix.smul_apply, Pm, smul_eq_mul]
  by_cases h : J = cmpl I
  · subst h
    simp [bmat_cmpl_eq I I₀]
  · simp [h, bmat_eq_zero h]

theorem cmat_beta (g : GL (Fin 6) K) :
    (cmat g)ᵀ * bmat * cmat g = (g : Matrix (Fin 6) (Fin 6) K).det • (bmat : Matrix Idx Idx K) := by
  ext I J
  have h := beta_rho g (cubeBasis K I) (cubeBasis K J)
  rw [beta_expand, beta_expand] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  have e1 : ∀ a, coord K (rho K g (cubeBasis K I)) a = cmat g a I := fun a => rfl
  have e2 : ∀ b, coord K (rho K g (cubeBasis K J)) b = cmat g b J := fun b => rfl
  simp only [e1, e2] at h
  have hr : ∑ a, ∑ b, coord K (cubeBasis K I) a * coord K (cubeBasis K J) b * bmat a b =
      bmat I J := by
    have c1 : ∀ a, coord K (cubeBasis K I) a = if I = a then 1 else 0 := by
      intro a; simp [coord, Module.Basis.repr_self, Finsupp.single_apply]
    have c2 : ∀ b, coord K (cubeBasis K J) b = if J = b then 1 else 0 := by
      intro b; simp [coord, Module.Basis.repr_self, Finsupp.single_apply]
    simp [c1, c2]
  rw [hr] at h
  rw [← h]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem cmat_inv_eq {g : GL (Fin 6) K} (hgU : g ∈ SUid σ 6) :
    cmat g⁻¹ = ((cmat g).map σ)ᵀ := by
  ext I J
  rw [cmat_inv_of_mem_SUid hgU]
  rfl

theorem cmat_sigma [CharP K 2] {g : GL (Fin 6) K} (hg : g ∈ SUid σ 6) (I J : Idx) :
    σ (cmat g I J) = cmat g (cmpl I) (cmpl J) := by
  obtain ⟨t, ht, hbt⟩ := bmat_eq_smul_Pm (K := K)
  have hdet : (g : Matrix (Fin 6) (Fin 6) K).det = 1 := hg.1
  have hB := cmat_beta g
  rw [hdet, one_smul, hbt, Matrix.mul_smul, Matrix.smul_mul] at hB
  have hB' : (cmat g)ᵀ * Pm * cmat g = Pm := smul_right_injective _ ht hB
  have h1 : cmat g * cmat g⁻¹ = 1 := by rw [← cmat_mul, mul_inv_cancel, cmat_one]
  have h2 : (Pm * (cmat g)ᵀ * Pm) * cmat g = 1 := by
    calc (Pm * (cmat g)ᵀ * Pm) * cmat g = Pm * ((cmat g)ᵀ * Pm * cmat g) := by
          simp only [Matrix.mul_assoc]
      _ = Pm * Pm := by rw [hB']
      _ = 1 := Pm_mul_self
  have h3 : cmat g⁻¹ = Pm * (cmat g)ᵀ * Pm := by
    calc cmat g⁻¹ = (Pm * (cmat g)ᵀ * Pm * cmat g) * cmat g⁻¹ := by rw [h2, Matrix.one_mul]
      _ = Pm * (cmat g)ᵀ * Pm := by rw [Matrix.mul_assoc _ (cmat g), h1, Matrix.mul_one]
  have h4 := congrFun (congrFun h3 J) I
  rw [cmat_inv_eq hg] at h4
  rw [Matrix.transpose_apply, Matrix.map_apply, Pm_mul_apply, Matrix.transpose_apply] at h4
  exact h4

@[expose] def cmplEquiv : Idx ≃ Idx := ⟨cmpl, cmpl, cmpl_cmpl, cmpl_cmpl⟩

theorem theta_rho [CharP K 2] {g : GL (Fin 6) K} (hg : g ∈ SUid σ 6) (ξ : Cube K) :
    theta σ (rho K g ξ) = rho K g (theta σ ξ) := by
  apply (cubeBasis K).ext_elem
  intro I
  show coord K (theta σ (rho K g ξ)) I = coord K (rho K g (theta σ ξ)) I
  have e1 : coord K (theta σ (rho K g ξ)) I = σ (coord K (rho K g ξ) (cmpl I)) := by
    have := coord_theta (σ := σ) (rho K g ξ) (cmpl I)
    rwa [cmpl_cmpl] at this
  rw [e1, coord_rho, coord_rho, map_sum]
  refine Fintype.sum_equiv cmplEquiv _ _ fun J => ?_
  show σ (cmat g (cmpl I) J * coord K ξ J) = cmat g I (cmpl J) * coord K (theta σ ξ) (cmpl J)
  rw [map_mul, cmat_sigma hg (cmpl I) J, cmpl_cmpl, coord_theta]

@[expose] def I012 : Idx := tripleSet 0 1 2 (by decide) (by decide) (by decide)

private theorem cmpl_I012 : cmpl I012 = tripleSet 3 4 5 (by decide) (by decide) (by decide) := by
  apply Subtype.ext
  show Finset.univ \ ({0, 1, 2} : Finset (Fin 6)) = ({3, 4, 5} : Finset (Fin 6))
  decide

theorem bmat_I012 : bmat (K := K) I012 (cmpl I012) = 1 := by
  unfold bmat
  rw [cmpl_I012, cubeBasis_apply, cubeBasis_apply, beta_ιMulti]
  have h1 : (fun s => e K (enum I012 s)) = fun s => e K (![0, 1, 2] s) :=
    funext fun s => by rw [show enum I012 s = ![0, 1, 2] s from
      enum_tripleSet (by decide : (0 : Fin 6) < 1) (by decide : (1 : Fin 6) < 2) s]
  have h2 : (fun s => e K (enum (tripleSet 3 4 5 (by decide) (by decide) (by decide)) s)) =
      fun s => e K (![3, 4, 5] s) :=
    funext fun s => by rw [show enum (tripleSet 3 4 5 (by decide) (by decide) (by decide)) s =
      ![3, 4, 5] s from enum_tripleSet (by decide : (3 : Fin 6) < 4) (by decide : (4 : Fin 6) < 5) s]
  rw [h1, h2]
  have h3 : (Matrix.of (Fin.append (fun s : Fin 3 => e K (![0, 1, 2] s))
      (fun s : Fin 3 => e K (![3, 4, 5] s))) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fin.append, Fin.addCases, e, Pi.single_apply]
  rw [h3, Matrix.det_one]

theorem bmat_eq_Pm [CharP K 2] : (bmat : Matrix Idx Idx K) = Pm := by
  ext I J
  simp only [Pm]
  by_cases h : J = cmpl I
  · subst h
    simp [bmat_cmpl_eq I I012, bmat_I012]
  · simp [h, bmat_eq_zero h]

theorem coord_theta' (ξ : Cube K) (a : Idx) : coord K (theta σ ξ) a = σ (coord K ξ (cmpl a)) := by
  have := coord_theta (σ := σ) ξ (cmpl a)
  rwa [cmpl_cmpl] at this

theorem beta_eq_sum [CharP K 2] (ξ η : Cube K) :
    beta K ξ η = ∑ a, coord K ξ a * coord K η (cmpl a) := by
  rw [beta_expand]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (cmpl a)]
  · rw [show bmat (K := K) a (cmpl a) = 1 by rw [bmat_eq_Pm]; exact Pm_apply_cmpl a, mul_one]
  · intro b _ hb
    rw [bmat_eq_zero hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem beta_theta [CharP K 2] (hσ : ∀ c, σ (σ c) = c) (ξ η : Cube K) :
    beta K (theta σ ξ) (theta σ η) = σ (beta K ξ η) := by
  rw [beta_eq_sum, beta_eq_sum, map_sum]
  refine Fintype.sum_equiv cmplEquiv _ _ fun a => ?_
  show coord K (theta σ ξ) a * coord K (theta σ η) (cmpl a) =
    σ (coord K ξ (cmpl a) * coord K η (cmpl (cmpl a)))
  rw [coord_theta', coord_theta', map_mul, cmpl_cmpl]

@[expose] def Wsub (σ : K ≃+* K) : AddSubgroup (Cube K) where
  carrier := {ξ | theta σ ξ = ξ}
  add_mem' := by intro a b ha hb; simp_all [map_add]
  zero_mem' := by simp
  neg_mem' := by intro a ha; simp_all [map_neg]

theorem mem_Wsub_iff {ξ : Cube K} : ξ ∈ Wsub σ ↔ theta σ ξ = ξ := Iff.rfl

theorem rho_mem_Wsub [CharP K 2] {g : GL (Fin 6) K} (hg : g ∈ SUid σ 6) {ξ : Cube K}
    (hξ : ξ ∈ Wsub σ) : rho K g ξ ∈ Wsub σ := by
  rw [mem_Wsub_iff, theta_rho hg, hξ]

theorem smul_mem_Wsub {c : K} (hc : σ c = c) {ξ : Cube K} (hξ : ξ ∈ Wsub σ) : c • ξ ∈ Wsub σ := by
  rw [mem_Wsub_iff, theta_smul, hc, hξ]

theorem add_theta_mem_Wsub (hσ : ∀ c, σ (σ c) = c) (ξ : Cube K) : ξ + theta σ ξ ∈ Wsub σ := by
  rw [mem_Wsub_iff, map_add, theta_theta hσ, add_comm]

theorem exists_decomp [CharP K 2] (hσ : IsUnitaryInvolution σ) (ξ : Cube K) :
    ∃ τ : K, ∃ a ∈ Wsub σ, ∃ b ∈ Wsub σ, ξ = σ τ • a + b ∧
      (∀ S : Submodule K (Cube K), (∀ x ∈ S, theta σ x ∈ S) → ξ ∈ S → a ∈ S ∧ b ∈ S) := by
  obtain ⟨τ, hτ⟩ := hσ.trace_surj 1 (map_one σ)
  refine ⟨τ, ξ + theta σ ξ, add_theta_mem_Wsub hσ.invol ξ,
    τ • ξ + theta σ (τ • ξ), add_theta_mem_Wsub hσ.invol _, ?_, ?_⟩
  · have h2 : ∀ x : Cube K, x + x = 0 := fun x => by
      rw [← two_smul K, CharTwo.two_eq_zero, zero_smul]
    rw [theta_smul, smul_add]
    have hξ : σ τ • ξ + τ • ξ = ξ := by rw [← add_smul, add_comm, hτ, one_smul]
    have hY : σ τ • theta σ ξ + σ τ • theta σ ξ = 0 := h2 _
    calc ξ = (σ τ • ξ + τ • ξ) + (σ τ • theta σ ξ + σ τ • theta σ ξ) := by rw [hξ, hY, add_zero]
      _ = _ := by abel
  · intro S hS hξ
    refine ⟨S.add_mem hξ (hS _ hξ), S.add_mem (S.smul_mem τ hξ) (hS _ (S.smul_mem τ hξ))⟩

theorem span_Wsub [CharP K 2] (hσ : IsUnitaryInvolution σ) :
    Submodule.span K (Wsub σ : Set (Cube K)) = ⊤ := by
  rw [eq_top_iff]
  intro ξ _
  obtain ⟨τ, a, ha, b, hb, rfl, -⟩ := exists_decomp hσ ξ
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ha))
    (Submodule.subset_span hb)

theorem linearMap_eq_of_eq_on_Wsub [CharP K 2] (hσ : IsUnitaryInvolution σ)
    {f g : Cube K →ₗ[K] Cube K} (h : ∀ w ∈ Wsub σ, f w = g w) : f = g :=
  LinearMap.ext_on (span_Wsub hσ) h

theorem beta_mem_fixed [CharP K 2] (hσ : ∀ c, σ (σ c) = c) {ξ η : Cube K} (hξ : ξ ∈ Wsub σ)
    (hη : η ∈ Wsub σ) : σ (beta K ξ η) = beta K ξ η := by
  have h := beta_theta hσ ξ η
  rw [hξ, hη] at h
  exact h.symm

theorem beta_nondeg_Wsub [CharP K 2] (hσ : IsUnitaryInvolution σ) {w : Cube K} (hw : w ∈ Wsub σ)
    (h : ∀ w' ∈ Wsub σ, beta K w w' = 0) : w = 0 := by
  have hall : ∀ η : Cube K, beta K w η = 0 := by
    intro η
    have hη : η ∈ Submodule.span K (Wsub σ : Set (Cube K)) := by
      rw [span_Wsub hσ]; trivial
    induction hη using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  apply eq_zero_of_coord_eq_zero
  intro I
  have h1 := beta_apply_cubeBasis_cmpl w I
  rw [hall, show beta K (cubeBasis K I) (cubeBasis K (cmpl I)) = 1 from by
    have := bmat_eq_Pm (K := K)
    exact (congrFun (congrFun this I) (cmpl I)).trans (Pm_apply_cmpl I), mul_one] at h1
  exact h1.symm

theorem rho_Wsub_eq_id_iff [CharP K 2] (hσ : IsUnitaryInvolution σ) {g : GL (Fin 6) K} :
    (∀ w ∈ Wsub σ, rho K g w = w) ↔ ∃ l : K, l ^ 3 = 1 ∧ (g : Matrix (Fin 6) (Fin 6) K) = l • 1 := by
  rw [← rho_eq_one_iff]
  constructor
  · intro h
    exact linearMap_eq_of_eq_on_Wsub hσ (f := rho K g) (g := 1) fun w hw => h w hw
  · intro h w _
    rw [h]
    rfl

@[expose] def Fσ (σ : K ≃+* K) : Subfield K where
  carrier := {c | σ c = c}
  mul_mem' := by intro a b ha hb; simp_all
  one_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  zero_mem' := by simp
  neg_mem' := by intro a ha; simp_all
  inv_mem' := by intro a ha; simp_all

theorem mem_Fσ_iff {c : K} : c ∈ Fσ σ ↔ σ c = c := Iff.rfl

@[expose] def Wform (σ : K ≃+* K) : Submodule (Fσ σ) (Cube K) where
  carrier := {ξ | theta σ ξ = ξ}
  add_mem' := (Wsub σ).add_mem
  zero_mem' := (Wsub σ).zero_mem
  smul_mem' := by
    intro c ξ hξ
    show theta σ ((c : K) • ξ) = (c : K) • ξ
    rw [theta_smul, c.2, hξ]

theorem mem_Wform_iff {ξ : Cube K} : ξ ∈ Wform σ ↔ ξ ∈ Wsub σ := Iff.rfl

private theorem rho_one_wact : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem rho_one_apply_wact (ξ : Cube K) : rho K (1 : GL (Fin 6) K) ξ = ξ :=
  congrArg (fun f : Cube K →ₗ[K] Cube K => f ξ) rho_one_wact

private theorem rho_mul_apply_wact (g h : GL (Fin 6) K) (ξ : Cube K) :
    rho K (g * h) ξ = rho K g (rho K h ξ) := by
  rw [rho, map_mul, Module.End.mul_apply]

@[expose] noncomputable def wactLin [CharP K 2] (g : SUid σ 6) : Wform σ →ₗ[Fσ σ] Wform σ where
  toFun w := ⟨rho K (g : GL (Fin 6) K) (w : Cube K),
    mem_Wform_iff.mpr (rho_mem_Wsub g.2 (mem_Wform_iff.mp w.2))⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (rho K (g : GL (Fin 6) K)) (x : Cube K) (y : Cube K)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (rho K (g : GL (Fin 6) K)) (c : K) (x : Cube K)

@[expose] noncomputable def wactEquiv [CharP K 2] (g : SUid σ 6) :
    Wform σ ≃ₗ[Fσ σ] Wform σ where
  toLinearMap := wactLin g
  invFun w := wactLin g⁻¹ w
  left_inv w := by
    apply Subtype.ext
    show rho K ((g⁻¹ : SUid σ 6) : GL (Fin 6) K) (rho K (g : GL (Fin 6) K) (w : Cube K)) =
      (w : Cube K)
    rw [← rho_mul_apply_wact, Subgroup.coe_inv, inv_mul_cancel, rho_one_apply_wact]
  right_inv w := by
    apply Subtype.ext
    show rho K (g : GL (Fin 6) K) (rho K ((g⁻¹ : SUid σ 6) : GL (Fin 6) K) (w : Cube K)) =
      (w : Cube K)
    rw [← rho_mul_apply_wact, Subgroup.coe_inv, mul_inv_cancel, rho_one_apply_wact]

@[expose] noncomputable def Wact [CharP K 2] (σ : K ≃+* K) : SUid σ 6 →* (Wform σ ≃ₗ[Fσ σ] Wform σ) where
  toFun g := wactEquiv g
  map_one' := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    show rho K ((1 : SUid σ 6) : GL (Fin 6) K) (w : Cube K) = (w : Cube K)
    rw [Subgroup.coe_one, rho_one_apply_wact]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    show rho K ((g * h : SUid σ 6) : GL (Fin 6) K) (w : Cube K) =
      rho K (g : GL (Fin 6) K) (rho K (h : GL (Fin 6) K) (w : Cube K))
    rw [Subgroup.coe_mul, rho_mul_apply_wact]

theorem Wact_apply [CharP K 2] (g : SUid σ 6) (w : Wform σ) :
    ((Wact σ g w : Wform σ) : Cube K) = rho K (g : GL (Fin 6) K) (w : Cube K) := rfl

theorem Wact_eq_one_iff [CharP K 2] (hσ : IsUnitaryInvolution σ) (g : SUid σ 6) :
    Wact σ g = 1 ↔ ∃ l : K, l ^ 3 = 1 ∧ ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = l • 1 := by
  refine Iff.trans ?_ (rho_Wsub_eq_id_iff (g := (g : GL (Fin 6) K)) hσ)
  constructor
  · intro h w hw
    have h1 : ((Wact σ g ⟨w, mem_Wform_iff.mpr hw⟩ : Wform σ) : Cube K) = w :=
      congrArg (fun e : Wform σ ≃ₗ[Fσ σ] Wform σ =>
        ((e ⟨w, mem_Wform_iff.mpr hw⟩ : Wform σ) : Cube K)) h
    rw [Wact_apply] at h1
    exact h1
  · intro h
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [Wact_apply]
    exact h w (mem_Wform_iff.mp w.2)

end CFSG.RankThree.GF2n.Smith81.U6Cube
