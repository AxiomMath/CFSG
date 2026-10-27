module

public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestCore
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldSymplectic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace InndiagCommRest

section LinearTwo

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo NbrGraphLinear

theorem ggOutComm_linearTwo {K : Type} [Field K] [Finite K] (hK : (Nat.card Kˣ).Coprime 2) :
    GGOutComm (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) := by
  set c := MulAut.congr (recipeEquivTwo K) with hc
  set g : (K ≃+* K) →* MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) :=
    c.symm.toMonoidHom.comp (psl2FieldAut K) with hg
  refine ggOutComm_of_forall_inner_mul (Set.range g) ?_ fun φ => ?_
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, ringEquiv_mul_comm_of_finite σ τ]
  obtain ⟨x, hx⟩ := semilinearAction_surjective K (c φ)
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  set u := pglAction K (Matrix.ProjGenLinGroup.mk A) with hu
  have hφ : c φ = u * psl2FieldAut K x.right := by
    rw [← hx, hu, hA]
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  obtain ⟨r, hr⟩ := matConjImage_gl_subset_inn hK (symm_congr_pglAction_mem A)
  refine ⟨c.symm u, ⟨r, hr⟩, g x.right, ⟨x.right, rfl⟩, ?_⟩
  change φ = c.symm u * c.symm (psl2FieldAut K x.right)
  rw [← map_mul, ← hφ, MulEquiv.symm_apply_apply]

theorem recipeLinearTwo_inndiagComm {N : ℕ} (hN : Odd (N - 1)) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear 2 N Q) :
    LargeEvenRecipeLinear 2 N fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard GGInndiagCommEq R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have hcop : (Nat.card Kˣ).Coprime 2 := by
    rw [Nat.card_units, hK]
    exact Nat.coprime_two_right.mpr hN
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ =>
    ggInndiagCommEq_of_subset_inn (matConjImage_gl_subset_inn hcop) (ggOutComm_linearTwo hcop)⟩

end LinearTwo

section SymplecticTwo

open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem ggOutComm_symplecticTwo {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : GGOutComm (LargeEvenProj (LargeEvenSpGroup K 2)) := by
  have : CharP K 2 := charP_two_of_card hK
  have hA : GGOutComm (antiSp K) := by
    refine ggOutComm_of_forall_inner_mul (Set.range fun j : ℕ => minorAut K ^ j) ?_ fun α => ?_
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [← pow_add, ← pow_add, add_comm]
    · obtain ⟨g, j, -, rfl⟩ := CFSG.QuasithinUnique.Setup.X7b.aut_eq_conj_mul_pow hf hK α
      exact ⟨MulAut.conj g, ⟨g, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  exact hA.of_mulEquiv (CFSG.QuasithinUnique.Setup.X7b.antiProjEquiv K).symm

theorem ggInndiagCommEq_symplecticTwo {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    GGInndiagCommEq (LargeEvenProj (LargeEvenSpGroup K 2))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 2)) (LargeEvenGSpSet K 2))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K 2))) := by
  have : CharP K 2 := charP_two_of_card hK
  exact ggInndiagCommEq_of_subset_inn (fun φ hφ => matConjImage_gsp_subset_inn 2 hφ)
    (ggOutComm_symplecticTwo hf hK)

end SymplecticTwo

section Omega

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  RecipeFieldOmega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggOutComm_omegaMinus {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    GGOutComm (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))) := by
  have hM : GGOutComm (matrixDerived (Qm n hn4 b c)) := by
    refine ggOutComm_of_forall_inner_mul (Set.range fun k : ℕ => AutOm.frobAut hn4 hirr ^ k) ?_
      fun α => ?_
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [← pow_add, ← pow_add, add_comm]
    · obtain ⟨ι, hι, k, rfl⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf α
      exact ⟨ι, hι, _, ⟨k, rfl⟩, rfl⟩
  exact hM.of_mulEquiv (minusEquiv hn4 b c)

theorem ggOutComm_omegaPlus {m : ℕ} (hm5 : 5 ≤ m) :
    GGOutComm (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := by
  have hm : 1 ≤ m := by omega
  have hφ : ∀ σ τ : K ≃+* K, AutOm.fieldAutP m σ * AutOm.fieldAutP m τ =
      AutOm.fieldAutP m τ * AutOm.fieldAutP m σ := fun σ τ => by
    rw [← map_mul, ← map_mul, ringEquiv_mul_comm_of_finite σ τ]
  have hyφ : ∀ y ∈ ({1, AutOm.plusRefl hm} :
      Set (MulAut (matrixDerived (coordinateQuadPlus m K)))), ∀ σ : K ≃+* K,
      y * AutOm.fieldAutP m σ = AutOm.fieldAutP m σ * y := by
    rintro y (rfl | rfl) σ
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP hm σ
  have hyy : ∀ y ∈ ({1, AutOm.plusRefl hm} :
      Set (MulAut (matrixDerived (coordinateQuadPlus m K)))),
      ∀ y' ∈ ({1, AutOm.plusRefl hm} : Set (MulAut (matrixDerived (coordinateQuadPlus m K)))),
        y * y' = y' * y := by
    rintro y (rfl | rfl) y' (rfl | rfl) <;> simp
  have hM : GGOutComm (matrixDerived (coordinateQuadPlus m K)) := by
    refine ggOutComm_of_forall_inner_mul (AutOm.plusCompl (K := K) hm :
      Set (MulAut (matrixDerived (coordinateQuadPlus m K)))) ?_ fun α => ?_
    · intro c hc d hd
      obtain ⟨y, hy, σ, rfl⟩ := exists_eq_mul_fieldAutP_of_mem_plusCompl hm hc
      obtain ⟨y', hy', τ, rfl⟩ := exists_eq_mul_fieldAutP_of_mem_plusCompl hm hd
      calc y * AutOm.fieldAutP m σ * (y' * AutOm.fieldAutP m τ)
          = y * (AutOm.fieldAutP m σ * y') * AutOm.fieldAutP m τ := by simp only [mul_assoc]
        _ = y * (y' * AutOm.fieldAutP m σ) * AutOm.fieldAutP m τ := by rw [hyφ y' hy' σ]
        _ = (y * y') * (AutOm.fieldAutP m σ * AutOm.fieldAutP m τ) := by simp only [mul_assoc]
        _ = (y' * y) * (AutOm.fieldAutP m τ * AutOm.fieldAutP m σ) := by
          rw [hyy y hy y' hy', hφ σ τ]
        _ = y' * (y * AutOm.fieldAutP m τ) * AutOm.fieldAutP m σ := by simp only [mul_assoc]
        _ = y' * (AutOm.fieldAutP m τ * y) * AutOm.fieldAutP m σ := by rw [hyφ y hy τ]
        _ = y' * AutOm.fieldAutP m τ * (y * AutOm.fieldAutP m σ) := by simp only [mul_assoc]
    · obtain ⟨ι, hι, c, hc, rfl⟩ := AutOm.exists_inner_mul_plusCompl hm5 α
      exact ⟨ι, hι, c, hc, rfl⟩
  exact hM.of_mulEquiv (plusEquiv hm)

end Omega

end InndiagCommRest

open InndiagCommRest

theorem largeEvenLabelAll_inndiagComm_linearTwo {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2)) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  intro Q hQ
  rcases h with ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht hl hn <;> subst ht hl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeLinearTwo_inndiagComm (ggOdd_two_pow_sub_one hn) hQ
  · simp only [LargeEvenRawDatum, ↓reduceIte] at hQ ⊢
    exact recipeLinearTwo_inndiagComm (by rw [← pow_mul]; exact ggOdd_two_pow_sub_one (by omega))
      hQ

theorem largeEvenLabelAll_inndiagComm_symplecticTwo {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hS, hl⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at hl hn
  subst hl
  intro Q₀ hQ
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK _ _ =>
      ggInndiagCommEq_symplecticTwo hn hK) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK _ _ =>
      ggInndiagCommEq_symplecticTwo hn hK) hQ

theorem largeEvenLabelAll_inndiagComm_omegaPlus
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .D) (h5 : 5 ≤ lab.rank) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  refine largeEvenLabelAll_inndiagComm_of_inn (largeEvenLabelAll_subset_inn hlab
    (Or.inl (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩))))) ?_
  exact largeEvenLabelAll_omegaPlus ht (by omega) fun K _ _ _ _ _ _ => ggOutComm_omegaPlus h5

theorem largeEvenLabelAll_inndiagComm_omegaMinus
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twD) (h4 : 4 ≤ lab.rank) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  refine largeEvenLabelAll_inndiagComm_of_inn (largeEvenLabelAll_subset_inn hlab
    (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega, by omega⟩)))))) ?_
  exact largeEvenLabelAll_omegaMinus ht h4 fun _ _ _ _ hK _ _ hirr _ _ =>
    ggOutComm_omegaMinus h4 hirr hK

end CFSG.StandardType

end
