module

public import CFSG.Timmesfeld.Transvection.QTwoSetup
public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.HardMathSupport.RichardWeiss.Proving.WCLocalBridge
public import CFSG.LieType.Universal.SymplecticExtras

public section

namespace CFSG.Timmesfeld.Transvection.QTwo

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Assembly.LowTwoRank Matrix

noncomputable def glSympRingEquiv {K F : Type*} [Field K] [Field F] (n : ℕ) (e : K ≃+* F) :
    TauCeti.GLSymplectic (Fin n) K ≃* TauCeti.GLSymplectic (Fin n) F where
  toFun := TauCeti.GLSymplectic.map (Fin n) e.toRingHom
  invFun := TauCeti.GLSymplectic.map (Fin n) e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
  right_inv A := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
  map_mul' := (TauCeti.GLSymplectic.map (Fin n) e.toRingHom).map_mul

theorem glSympRingEquiv_apply {K F : Type*} [Field K] [Field F] (n : ℕ) (e : K ≃+* F)
    (A : TauCeti.GLSymplectic (Fin n) K) (i j : Fin n ⊕ Fin n) :
    (((glSympRingEquiv n e A : TauCeti.GLSymplectic (Fin n) F) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) i j =
      e ((((A : GL (Fin n ⊕ Fin n) K)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) i j) := by
  change ((TauCeti.GLSymplectic.map (Fin n) e.toRingHom A : TauCeti.GLSymplectic (Fin n) F) :
    GL (Fin n ⊕ Fin n) F).val i j = _
  rw [TauCeti.GLSymplectic.coe_map]
  rfl

theorem galoisField_two_one_cases (c : GaloisField 2 1) : c = 0 ∨ c = 1 :=
  CFSG.HardMathSupport.RichardWeiss.Proving.galoisField_two_one_eq_zero_or_one c

abbrev tvMat {K : Type*} [Field K] {n : ℕ} (i : Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  1 + Matrix.single (Sum.inl i) (Sum.inr i) 1

theorem spConclusion {H : Type} [Group H] {Δ : Set (Subgroup H)} {D : Set H}
    (hΔ : ∀ X : Subgroup H, X ∈ Δ ↔ ∃ x ∈ D, X = Subgroup.zpowers x)
    (hD : ∀ x ∈ D, ∀ y, IsConj x y ↔ y ∈ D) {n : ℕ} (hn : 2 ≤ n)
    (ψ : H ≃* TauCeti.GLSymplectic (Fin n) (ZMod 2))
    (hψ : ∀ t : TauCeti.GLSymplectic (Fin n) (ZMod 2),
      ((t : GL (Fin n ⊕ Fin n) (ZMod 2)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) =
        tvMat ⟨n - 1, by omega⟩ → ψ.symm t ∈ D) :
    ∃ n : ℕ, ∃ hn : 2 ≤ n, ∃ Φ : ↥(StatedSp n (GaloisField 2 1)) →* H,
      Function.Bijective Φ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
        ∃ g, X = (conjSub ((Symplectic.rootDatum n (GaloisField 2 1)).rootGroup
          (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g).map Φ := by
  set F := GaloisField 2 1
  let eF : F ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  let Φ₀ : StatedSp n F ≃* TauCeti.GLSymplectic (Fin n) F :=
    MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
  let Ψ : StatedSp n F ≃* H := (Φ₀.trans (glSympRingEquiv n eF)).trans ψ.symm
  refine ⟨n, hn, Ψ.toMonoidHom, Ψ.bijective, fun X => ?_⟩
  set i₀ : Fin n := ⟨n - 1, by omega⟩
  set r := TauCeti.GLSymplecticFin.RootSubgroupIndex.positiveLong i₀
  set t₀ := Symplectic.SpExtras.elt (F := F) r 1
  have hr : Symplectic.stdVec r = Symplectic.toStd n (Pi.single i₀ 1) := by
    rw [Symplectic.SpExtras.toStd_single_of_not_lt' (by simp [i₀]; omega)]
    rfl
  have hT : (Symplectic.rootDatum n F).rootGroup (Pi.single i₀ 1) = Subgroup.zpowers t₀ := by
    change Symplectic.rootGroup n F (Pi.single i₀ 1) = _
    apply le_antisymm
    · intro x hx
      obtain ⟨c, rfl⟩ := (Symplectic.SpExtras.mem_rootGroup_iff hr).1 hx
      rcases galoisField_two_one_cases c with rfl | rfl
      · rw [Symplectic.SpExtras.elt_zero]
        exact one_mem _
      · exact Subgroup.mem_zpowers _
    · exact (Subgroup.zpowers_le).2 ((Symplectic.SpExtras.mem_rootGroup_iff hr).2 ⟨1, rfl⟩)
  have ht₀ : Ψ t₀ ∈ D := by
    have key : Ψ t₀ = ψ.symm (glSympRingEquiv n eF (Φ₀ t₀)) := rfl
    rw [key]
    apply hψ
    ext a c
    rw [glSympRingEquiv_apply]
    change eF ((Symplectic.SpExtras.mat n F t₀) a c) = _
    rw [Symplectic.SpExtras.mat_elt, one_smul]
    change eF ((1 + Matrix.single (Sum.inl i₀) (Sum.inr i₀) 1 : Matrix _ _ F) a c) = _
    simp only [Matrix.add_apply, map_add, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  exact mem_iff_conjSub_map hΔ hD Ψ.toMonoidHom Ψ.surjective hT ht₀ X

section Isometry

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ComponentClassification.CatalogueBAlternatingIsometry CFSG.Open
  CFSG.ClassicalGroups.Orthogonal CFSG.Fischer.Classification

variable {m : ℕ}

theorem bilin_basis_inl {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} (bas : Module.Basis (Fin n ⊕ Fin n) (ZMod 2) V)
    (hbas : LinearMap.BilinForm.toMatrix bas B = Matrix.J (Fin n) (ZMod 2)) (x : V) (i : Fin n) :
    B x (bas (Sum.inl i)) = bas.equivFun x (Sum.inr i) := by
  conv_lhs => rw [← bas.sum_equivFun x]
  simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left]
  have hB : ∀ j, B (bas j) (bas (Sum.inl i)) = Matrix.J (Fin n) (ZMod 2) j (Sum.inl i) :=
    fun j => by rw [← hbas, LinearMap.BilinForm.toMatrix_apply]
  simp only [hB, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem exists_sympEquiv_of_isometry {H : Type} [Group H] {D : Set H}
    (b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)) (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (φ : H ≃* (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y))
    (hφ : ∀ g : H, g ∈ D ↔ ((φ g : GL (Fin (2 * m)) (ZMod 2)) ∈
      fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    ∃ ψ : H ≃* TauCeti.GLSymplectic (Fin m) (ZMod 2), ∀ (i : Fin m)
      (t : TauCeti.GLSymplectic (Fin m) (ZMod 2)),
      ((t : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) =
        tvMat i → ψ.symm t ∈ D := by
  have hB : b.IsAlt := halt
  have hBnd : b.Nondegenerate := by
    refine ⟨fun x hx => hnd x hx, fun y hy => hnd y fun x => ?_⟩
    have h := hB.self_eq_zero (x + y)
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, halt, halt, hy x, zero_add, add_zero, zero_add] at h
    exact h
  obtain ⟨n, bas, hdim, hbas⟩ := exists_symplectic_basis b hB hBnd
  have hnm : n = m := by
    rw [Module.finrank_fin_fun] at hdim
    omega
  subst hnm
  have hmap : (fischerMatrixGroup fun A : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) =>
      ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y).map (toLinEquiv (Fin (2 * n)) (ZMod 2)).toMonoidHom =
        isometryGroup b := by
    ext L
    rw [Subgroup.mem_map_equiv, mem_fischerMatrixGroup_bilin_iff, mem_isometryGroup_iff]
    refine forall₂_congr fun x y => ?_
    rw [← toLinEquiv_apply, ← toLinEquiv_apply, MulEquiv.apply_symm_apply]
  let Θ := ((toLinEquiv (Fin (2 * n)) (ZMod 2)).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  have hΘ : ∀ A x, ((Θ A : isometryGroup b) :
      (Fin (2 * n) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * n) → ZMod 2)) x =
      ((A : GL (Fin (2 * n)) (ZMod 2)) : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) *ᵥ x :=
    fun _ _ => rfl
  refine ⟨φ.trans (Θ.trans (isometryMatrixEquiv bas b hbas)), fun i t ht => ?_⟩
  set L := (isometryMatrixEquiv bas b hbas).symm t
  set v₀ := bas (Sum.inl i)
  have hL : ∀ x, (L : (Fin (2 * n) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * n) → ZMod 2)) x =
      x + b x v₀ • v₀ := by
    intro x
    apply bas.equivFun.injective
    rw [← isometryMatrixEquiv_symm_mulVec bas b hbas t x, ht, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec, map_add, map_smul, bilin_basis_inl bas hbas]
    congr 1
    ext j
    rw [Pi.smul_apply, show v₀ = bas (Sum.inl i) from rfl, Module.Basis.equivFun_self,
      Function.update_apply, smul_eq_mul]
    split_ifs with h1 h2 h2
    · rw [one_mul, mul_one]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [Pi.zero_apply, mul_zero]
  have hv₀ : v₀ ≠ 0 := bas.ne_zero _
  rw [MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply]
  set A := Θ.symm L
  have hA : ∀ x, ((A : GL (Fin (2 * n)) (ZMod 2)) : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) *ᵥ
      x = x + b x v₀ • v₀ := by
    intro x
    rw [← hΘ, MulEquiv.apply_symm_apply, hL]
  refine (hφ _).2 ?_
  rw [MulEquiv.apply_symm_apply]
  exact ⟨v₀, hv₀, hA⟩

end Isometry

section PermSix

open CFSG.ComponentClassification.PresentationLocal

@[expose] def fourIdx : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun i := if i = 0 then Sum.inl 0 else if i = 1 then Sum.inl 1 else if i = 2 then Sum.inr 1
    else Sum.inr 0
  invFun
    | Sum.inl 0 => 0
    | Sum.inl 1 => 1
    | Sum.inr 1 => 2
    | Sum.inr 0 => 3
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def glFourEquiv : GL (Fin 4) (ZMod 2) ≃* GL (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx).toMulEquiv

theorem glFourEquiv_apply (g : GL (Fin 4) (ZMod 2)) :
    ((glFourEquiv g : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix _ _ (ZMod 2)) =
      Matrix.reindex fourIdx fourIdx (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  rfl

theorem reindex_antidiagGram :
    Matrix.reindex fourIdx fourIdx antidiagGram = Matrix.J (Fin 2) (ZMod 2) := by
  ext a c
  rcases a with a | a <;> rcases c with c | c <;> fin_cases a <;> fin_cases c <;> decide

theorem map_sympFour :
    sympFour.map glFourEquiv.toMonoidHom = TauCeti.GLSymplectic (Fin 2) (ZMod 2) := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_sympFour_iff, TauCeti.GLSymplectic.mem_iff']
  set M := ((glFourEquiv.symm g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hg : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      Matrix.reindex fourIdx fourIdx M := by
    rw [← glFourEquiv_apply, MulEquiv.apply_symm_apply]
  have e : ∀ X : Matrix (Fin 4) (Fin 4) (ZMod 2), Matrix.reindex fourIdx fourIdx X =
      Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx X := fun X =>
    (congrFun (Matrix.coe_reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx) X).symm
  rw [hg, ← reindex_antidiagGram, Matrix.transpose_reindex, e, e, e, ← map_mul, ← map_mul]
  exact (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx).injective.eq_iff.symm

theorem exists_sympEquiv_of_perm_six {H : Type} [Group H] {D : Set H}
    (φ : H ≃* Equiv.Perm (Fin 6)) (hφ : ∀ g, g ∈ D ↔ (φ g).IsSwap) :
    ∃ ψ : H ≃* TauCeti.GLSymplectic (Fin 2) (ZMod 2), ∀ t : TauCeti.GLSymplectic (Fin 2) (ZMod 2),
      ((t : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
        tvMat 1 → ψ.symm t ∈ D := by
  let ω : sympFour ≃* Equiv.Perm (Fin 6) :=
    MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩
  let ρ : sympFour ≃* TauCeti.GLSymplectic (Fin 2) (ZMod 2) :=
    (glFourEquiv.subgroupMap sympFour).trans (MulEquiv.subgroupCongr map_sympFour)
  refine ⟨φ.trans (ω.symm.trans ρ), fun t ht => ?_⟩
  have hρ : ρ rootInvolutionA = t := by
    apply Subtype.ext
    apply Units.ext
    have h1 : ((ρ rootInvolutionA : TauCeti.GLSymplectic (Fin 2) (ZMod 2)) :
        GL (Fin 2 ⊕ Fin 2) (ZMod 2)) = glFourEquiv (rootInvolutionA : GL (Fin 4) (ZMod 2)) :=
      rfl
    rw [h1, glFourEquiv_apply, ht]
    change Matrix.reindex fourIdx fourIdx (1 + Matrix.single 1 2 1) = _
    ext a c
    rcases a with a | a <;> rcases c with c | c <;> fin_cases a <;> fin_cases c <;> decide
  rw [MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, ← hρ,
    MulEquiv.symm_apply_apply]
  refine (hφ _).2 ?_
  rw [MulEquiv.apply_symm_apply]
  change (omegaPerm rootInvolutionA).IsSwap
  rw [omegaPerm_rootInvolutionA]
  exact ⟨2, 3, by decide, rfl⟩

end PermSix

end CFSG.Timmesfeld.Transvection.QTwo
