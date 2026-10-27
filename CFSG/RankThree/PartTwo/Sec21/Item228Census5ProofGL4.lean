module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofCubeField
public import CFSG.RankThree.PartOne.KF.SpSylow
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census5Proof

open Matrix CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def idxV₄ : V₄ ≃ Fin 4 := finSumFinEquiv

variable (K) in
@[expose] noncomputable def reindexV₄ : GL V₄ K ≃* GL (Fin 4) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K idxV₄).toRingEquiv.toMulEquiv

theorem coe_reindexV₄ (g : GL V₄ K) :
    ((reindexV₄ K g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.reindex idxV₄ idxV₄ (g : Matrix V₄ V₄ K) :=
  rfl

theorem coe_mul_coe_inv (s : (cubeAlg K)ˣ) :
    ((s : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) *
      (((s⁻¹ : (cubeAlg K)ˣ) : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]

theorem coe_inv_mul_coe (s : (cubeAlg K)ˣ) :
    (((s⁻¹ : (cubeAlg K)ˣ) : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) *
      ((s : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one]

@[expose] noncomputable def cubeTorus : (cubeAlg K)ˣ × (cubeAlg K)ˣ →* GL V₄ K where
  toFun x :=
    { val := fromBlocks ((x.1 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) 0 0
        ((x.2 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)
      inv := fromBlocks (((x.1⁻¹ : (cubeAlg K)ˣ) : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) 0 0
        (((x.2⁻¹ : (cubeAlg K)ˣ) : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [fromBlocks_multiply]
        simp [coe_mul_coe_inv]
      inv_val := by
        rw [fromBlocks_multiply]
        simp [coe_inv_mul_coe] }
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by simp [fromBlocks_multiply])

theorem coe_cubeTorus (x : (cubeAlg K)ˣ × (cubeAlg K)ˣ) :
    ((cubeTorus x : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks ((x.1 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) 0 0
        ((x.2 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem cubeTorus_injective : Function.Injective (cubeTorus (K := K)) := by
  intro x y h
  have e := congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K)) h
  simp only [coe_cubeTorus] at e
  obtain ⟨e1, -, -, e4⟩ := Matrix.fromBlocks_inj.mp e
  exact Prod.ext (Units.ext (Subtype.ext e1)) (Units.ext (Subtype.ext e4))

theorem orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem factorization_card_GL_three [Finite K] (hK : ∀ s : K, s * s + s + 1 ≠ 0)
    (hq : Nat.card K % 3 = 2) :
    (Nat.card (GL V₄ K)).factorization 3 = 2 * (Nat.card (cubeAlg K)ˣ).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have hpK : ¬ 3 ∣ Fintype.card K := by
    rw [Fintype.card_eq_nat_card]
    omega
  have hord : orderOf (Fintype.card K : ZMod 3) = 2 := by
    have e : ((Fintype.card K : ℕ) : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod, Fintype.card_eq_nat_card, hq]
      rfl
    rw [e, orderOf_two_zmod_three]
  have h2 : padicValNat 3 (Nat.factorial (4 / 2)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by decide)
  rw [card_units_cubeAlg hK, Nat.factorization_def (Nat.card K ^ 2 - 1) Nat.prime_three,
    Nat.card_congr (reindexV₄ K).toEquiv,
    CFSG.GroupTheory.WeirSylow.factorization_card_GL (p := 3) (by decide) K hpK 4, hord, h2,
    Fintype.card_eq_nat_card]
  ring

theorem exists_conj_cubeTorus [Finite K] (hK : ∀ s : K, s * s + s + 1 ≠ 0)
    (hq : Nat.card K % 3 = 2) {A : GL V₄ K} (hA3 : A ^ 3 = 1) :
    ∃ (g : GL V₄ K) (s t : (cubeAlg K)ˣ), s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      g * A * g⁻¹ = cubeTorus (s, t) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 (cubeAlg K)ˣ := default
  let Sg : Subgroup (cubeAlg K)ˣ := (S : Subgroup (cubeAlg K)ˣ)
  have hSg : Nat.card Sg = 3 ^ (Nat.card (cubeAlg K)ˣ).factorization 3 :=
    Sylow.card_eq_multiplicity S
  let emb : ↥Sg × ↥Sg →* GL V₄ K := cubeTorus.comp (Sg.subtype.prodMap Sg.subtype)
  have hemb : Function.Injective emb := by
    refine cubeTorus_injective.comp ?_
    intro a b h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hPcard : Nat.card emb.range = 3 ^ (Nat.card (GL V₄ K)).factorization 3 := by
    rw [factorization_card_GL_three hK hq,
      Nat.card_congr (MonoidHom.ofInjective hemb).toEquiv.symm, Nat.card_prod, hSg, ← sq,
      ← pow_mul, mul_comm]
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KFU.exists_conj_le_sylow emb.range hPcard
    (Subgroup.zpowers A) (by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hA3,
        _root_.one_zpow])
  obtain ⟨⟨s, t⟩, hst⟩ := hg A (Subgroup.mem_zpowers A)
  have hxp : (g * A * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hA3, mul_one, mul_inv_cancel]
  have h2 : (s, t) ^ 3 = 1 := by
    apply hemb
    rw [map_pow, hst, hxp, map_one]
  refine ⟨g, s, t, ?_, ?_, ?_⟩
  · simpa using congrArg (fun z : ↥Sg => (z : (cubeAlg K)ˣ)) (congrArg Prod.fst h2)
  · simpa using congrArg (fun z : ↥Sg => (z : (cubeAlg K)ˣ)) (congrArg Prod.snd h2)
  · rw [← hst]
    rfl

variable (K) in
@[expose] def swapTwoMat : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem swapTwoMat_mul_self : swapTwoMat K * swapTwoMat K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapTwoMat, Matrix.mul_apply, Fin.sum_univ_two]

variable (K) in
@[expose] def swapTwo : GL (Fin 2) K where
  val := swapTwoMat K
  inv := swapTwoMat K
  val_inv := swapTwoMat_mul_self
  inv_val := swapTwoMat_mul_self

theorem swapTwo_conj_sq : swapTwoMat K * (cubeMat K * cubeMat K) * swapTwoMat K = cubeMat K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapTwoMat, cubeMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_conj_cubeMat {a : Matrix (Fin 2) (Fin 2) K}
    (ha : a = cubeMat K ∨ a = cubeMat K * cubeMat K) :
    ∃ X : GL (Fin 2) K,
      (X : Matrix (Fin 2) (Fin 2) K) * a * ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        cubeMat K := by
  rcases ha with rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨swapTwo K, swapTwo_conj_sq⟩

@[expose] def blockGL (X Y : GL (Fin 2) K) : GL V₄ K where
  val := fromBlocks X 0 0 Y
  inv := fromBlocks ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
    ((Y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  val_inv := by
    rw [fromBlocks_multiply]
    simp
  inv_val := by
    rw [fromBlocks_multiply]
    simp

variable (K) in
@[expose] def swapBlocks : GL V₄ K where
  val := fromBlocks 0 1 1 0
  inv := fromBlocks 0 1 1 0
  val_inv := by
    rw [fromBlocks_multiply]
    simp
  inv_val := by
    rw [fromBlocks_multiply]
    simp

theorem coe_blockGL_conj (X Y : GL (Fin 2) K) (a b : Matrix (Fin 2) (Fin 2) K) :
    ((blockGL X Y : GL V₄ K) : Matrix V₄ V₄ K) * fromBlocks a 0 0 b *
        (((blockGL X Y)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks ((X : Matrix (Fin 2) (Fin 2) K) * a * ((X⁻¹ : GL (Fin 2) K) : Matrix _ _ K)) 0 0
        ((Y : Matrix (Fin 2) (Fin 2) K) * b * ((Y⁻¹ : GL (Fin 2) K) : Matrix _ _ K)) := by
  change fromBlocks (X : Matrix (Fin 2) (Fin 2) K) 0 0 Y * fromBlocks a 0 0 b *
    fromBlocks ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
      ((Y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem coe_swapBlocks_conj (a b : Matrix (Fin 2) (Fin 2) K) :
    ((swapBlocks K : GL V₄ K) : Matrix V₄ V₄ K) * fromBlocks a 0 0 b *
        (((swapBlocks K)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = fromBlocks b 0 0 a := by
  change fromBlocks 0 1 1 0 * fromBlocks a 0 0 b * fromBlocks 0 1 1 0 = _
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem exists_normal_form_GL4 [Finite K] (hK : ∀ s : K, s * s + s + 1 ≠ 0)
    (hq : Nat.card K % 3 = 2) {A : GL V₄ K} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    ∃ P : GL V₄ K, ((P * A * P⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = fromBlocks (cubeMat K) 0 0 1 ∨
      ((P * A * P⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = fromBlocks (cubeMat K) 0 0 (cubeMat K) := by
  obtain ⟨g, s, t, hs3, ht3, hg⟩ := exists_conj_cubeTorus hK hq hA3
  have hcube : ∀ u : (cubeAlg K)ˣ, u ^ 3 = 1 →
      ((u : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((u : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = cubeMat K ∨
          ((u : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = cubeMat K * cubeMat K := by
    intro u hu
    have hu' : (u : cubeAlg K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
    rcases eq_of_pow_three_eq_one hK hu' with h | h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (Or.inl (by rw [h]; rfl))
    · exact Or.inr (Or.inr (by rw [h]; rfl))
  have hgA : ((g * A * g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks ((s : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) 0 0
        ((t : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [hg]
    rfl
  have hconj : ∀ X Y : GL (Fin 2) K,
      ((blockGL X Y * g * A * (blockGL X Y * g)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
        fromBlocks ((X : Matrix (Fin 2) (Fin 2) K) * ((s : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) *
            ((X⁻¹ : GL (Fin 2) K) : Matrix _ _ K)) 0 0
          ((Y : Matrix (Fin 2) (Fin 2) K) * ((t : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) *
            ((Y⁻¹ : GL (Fin 2) K) : Matrix _ _ K)) := by
    intro X Y
    have e : blockGL X Y * g * A * (blockGL X Y * g)⁻¹ =
        blockGL X Y * (g * A * g⁻¹) * (blockGL X Y)⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul, hgA, coe_blockGL_conj]
  have hne : ¬ (((s : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = 1 ∧
      ((t : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = 1) := by
    rintro ⟨ha1, hb1⟩
    apply hA1
    have h1 : g * A * g⁻¹ = 1 := Units.ext (by rw [hgA, ha1, hb1, fromBlocks_one]; rfl)
    calc A = g⁻¹ * (g * A * g⁻¹) * g := by group
      _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
  rcases hcube s hs3 with ha1 | ha1
  ·
    have hb1 : ((t : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = cubeMat K ∨
        ((t : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) = cubeMat K * cubeMat K := by
      rcases hcube t ht3 with h | h
      · exact absurd ⟨ha1, h⟩ hne
      · exact h
    obtain ⟨Y, hY⟩ := exists_conj_cubeMat hb1
    refine ⟨swapBlocks K * (blockGL 1 Y * g), Or.inl ?_⟩
    have e : swapBlocks K * (blockGL 1 Y * g) * A * (swapBlocks K * (blockGL 1 Y * g))⁻¹ =
        swapBlocks K * (blockGL 1 Y * g * A * (blockGL 1 Y * g)⁻¹) * (swapBlocks K)⁻¹ := by
      group
    rw [e, Units.val_mul, Units.val_mul, hconj, hY, ha1, coe_swapBlocks_conj]
    simp
  · obtain ⟨X, hX⟩ := exists_conj_cubeMat ha1
    rcases hcube t ht3 with hb1 | hb1
    · refine ⟨blockGL X 1 * g, Or.inl ?_⟩
      rw [hconj, hX, hb1]
      simp
    · obtain ⟨Y, hY⟩ := exists_conj_cubeMat hb1
      exact ⟨blockGL X Y * g, Or.inr (by rw [hconj, hX, hY])⟩

end CFSG.RankThree.PartTwo.Sec21.Item228Census5Proof
