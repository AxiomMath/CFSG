module

public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Monster.CodeAut.Bridge
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix

section Notation

variable {G : Type} [Group G]

abbrev fsuL0 (T L : Subgroup G) : Subgroup G :=
  conjClosure L T

abbrev fsuM (T L : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (fsuL0 T L : Set G)

abbrev fsuV (T I : Subgroup G) : Subgroup G :=
  conjClosure I T

abbrev fsuVM (T L I : Subgroup G) : Subgroup G :=
  conjClosure (fsuV T I) (fsuM T L)

abbrev fsuUL (T L I : Subgroup G) : Subgroup G :=
  ⁅fsuVM T L I, L⁆

abbrev fsuCVM (T L I : Subgroup G) : Subgroup G :=
  fsuVM T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)

end Notation

section TensorPair

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def tensorPairAct (Γ₁ Γ₂ : Subgroup (Matrix.GeneralLinearGroup ι F)) (g : ↥Γ₁ × ↥Γ₂)
    (X : Multiplicative (Matrix ι ι F)) : Multiplicative (Matrix ι ι F) :=
  Multiplicative.ofAdd
    (((g.1 : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) * Multiplicative.toAdd X *
      (((g.2 : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F))ᵀ)

@[expose] def tensorPairModel (Γ₁ Γ₂ : Subgroup (Matrix.GeneralLinearGroup ι F)) : FFModel where
  Gam := ↥Γ₁ × ↥Γ₂
  Amb := Multiplicative (Matrix ι ι F)
  act := tensorPairAct Γ₁ Γ₂
  sec := ⊤
  ker := ⊥

end TensorPair

@[expose] def nativeGolayC : Subgroup (G6.PermMod 24) :=
  golayC.map (G6.permAct 24 CFSG.Monster.Code.bridgeQ).toMonoidHom

theorem nativeGolayC_invariant {g : Equiv.Perm (Fin 24)} (hg : g ∈ NativeSporadic.M24)
    {y : G6.PermMod 24} (hy : y ∈ nativeGolayC) : G6.permAct 24 g y ∈ nativeGolayC := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hp : CFSG.Monster.Code.bridgeQ⁻¹ * g * CFSG.Monster.Code.bridgeQ ∈
      CFSG.Monster.Code.AutPerm := by
    have hle : Subgroup.closure {CFSG.Monster.Code.bridgePA, CFSG.Monster.Code.bridgePB} ≤
        CFSG.Monster.Code.AutPerm := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact CFSG.Monster.Code.bridgePA_mem
      · exact CFSG.Monster.Code.bridgePB_mem
    apply hle
    rw [CFSG.Monster.Code.bridge_closure_eq_map]
    refine ⟨g, hg, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  refine ⟨G6.permAct 24 (CFSG.Monster.Code.bridgeQ⁻¹ * g * CFSG.Monster.Code.bridgeQ) x,
    ((CFSG.Monster.Code.AutPerm.inv_mem hp) (Multiplicative.toAdd x)).1 hx, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
  congr 2
  group

@[expose] def NativeCocode24 {V : Type*} [CommGroup V] (H : Subgroup (MulAut V))
    (U Z : Subgroup V) : Prop :=
  (FFModel.golaySec NativeSporadic.M24 (G6.coreMod 24) nativeGolayC).Realizes H U Z

section Conclusions

variable {G : Type} [Group G]

@[expose] def Concl701FF (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)] : Prop :=
  ∃ A : Subgroup (MulAut ↥(fsuV T I)),
    IsFFStarOffender (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn (fsuL0 T L) (fsuV T I) : Set (MulAut ↥(fsuV T I)))) A

@[expose] def Concl701J4 (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)] : Prop :=
  fsuV T I ≤ fsuM T L ∧ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
    Nat.card ↥(fsuV T I) = 2 ^ 11 ∧
    fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) = fsuV T I ∧
    NativeCocode24 (V := ↥(fsuV T I)) (autOn (fsuM T L) (fsuV T I)) ⊤ ⊥ ∧
    Nonempty (G ≃* NativeSporadic.J4)

@[expose] def Concl701Orth (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)] : Prop :=
  ∃ n : ℕ, 1 < n ∧ BinaryOrthogonalFour (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n

@[expose] def Shape701 (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∨
    (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥L ⧸ CFSG.pCore 2 ↥L) 2 n) ∨
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))

variable [Finite G]

@[expose] def Concl326Three (T L I : Subgroup G) : Prop :=
  ∃ _ : IsMulCommutative ↥(fsuVM T L I), IsElemAbelian 2 (fsuVM T L I) ∧
    fsuVM T L I ≤ Subgroup.normalizer (fsuCVM T L I : Set G) ∧
    (∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
      fsuUL T L I ⊔ CFSG.conjugate (fsuUL T L I) t ⊔ fsuCVM T L I = fsuVM T L I ∧
      (fsuUL T L I ⊔ fsuCVM T L I) ⊓ (CFSG.conjugate (fsuUL T L I) t ⊔ fsuCVM T L I) =
        fsuCVM T L I ∧
      fsuUL T L I ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G)) ∧
    (∀ A ∈ QhatStar (V := ↥(fsuVM T L I)) (autOn (fsuM T L) (fsuVM T L I)), ∀ a ∈ A,
      ∀ u : ↥(fsuVM T L I), (u : G) ∈ fsuUL T L I → ((a u : ↥(fsuVM T L I)) : G) ∈ fsuUL T L I) ∧
    (∃ _ : IsMulCommutative ↥(fsuUL T L I),
      qhatOf (V := ↥(fsuUL T L I)) (autOn (fsuL0 T L ⊔ T) (fsuUL T L I)) ≤ 2) ∧
    ((fsuUL T L I = I ∧ fsuV T I = fsuVM T L I) ∨
      (Nonempty (↥(autOn (autOn (fsuM T L) (fsuVM T L I)) (autOn L (fsuVM T L I))) ≃*
          MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) ∧
        fsuV T I = fsuVM T L I ∧ Nat.card ↥I = 2 ^ 3 ∧
        ∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set G) ∧
          s ∉ L ⊔ pCoreOf 2 (L ⊔ T ⊓ Subgroup.normalizer (L : Set G)) ∧
          fsuUL T L I = I ⊔ CFSG.conjugate I s ∧ I ⊓ CFSG.conjugate I s = ⊥) ∨
      (Nonempty (↥(autOn L (fsuVM T L I)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        DirectSumOfCopies (V := ↥(fsuVM T L I)) (autOn L (fsuVM T L I))
          ((fsuUL T L I).subgroupOf (fsuVM T L I)) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 ∧
        (Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
              Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
                Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5)) ∨
          Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
              Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
                Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5 × ZMod 5)))))

@[expose] def Concl326ThreeIv (T L I : Subgroup G) [IsMulCommutative ↥(fsuVM T L I)] : Prop :=
  ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    LieModel ↥(autOn L (fsuVM T L I)) .PSL 2 2 n ∧
    DirectSumOfCopies (V := ↥(fsuVM T L I)) (autOn L (fsuVM T L I))
      ((fsuUL T L I).subgroupOf (fsuVM T L I))
      ((fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (fsuVM T L I))
      (FFModel.nat (StatedSL 2 K)) 2

@[expose] def Concl326ThreeC (T L I : Subgroup G) : Prop :=
  (∃ x ∈ T, Concl326Three T L (CFSG.conjugate I x)) ∨
    ∃ _ : IsMulCommutative ↥(fsuVM T L I), Concl326ThreeIv T L I

theorem concl326ThreeC_of_concl326Three {T L I : Subgroup G} (h : Concl326Three T L I) :
    Concl326ThreeC T L I := by
  refine Or.inl ⟨1, T.one_mem, ?_⟩
  have h1 : CFSG.conjugate I 1 = I := by
    ext x
    simp [CFSG.conjugate]
  rw [h1]
  exact h

@[expose] def Concl701Four (T L I : Subgroup G) : Prop :=
  L < fsuL0 T L ∧ Shape701 L ∧ Concl326ThreeC T L I

end Conclusions

@[expose] def Stmt7_0_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I →
    ∃ _ : IsMulCommutative ↥(fsuV T I), IsElemAbelian 2 (fsuV T I) ∧
      fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      (Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I ∨ Concl701Four T L I)

@[expose] def StmtFSUModule : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I →
    IsElemAbelian 2 (fsuV T I) ∧ fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)

@[expose] def Stmt7_0_1_shape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    Concl326Three T L I → Shape701 L

@[expose] def Stmt7_0_1_shapeC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    Concl326ThreeC T L I → Shape701 L

structure Hyp7_0_2 (G : Type) [Group G] [Finite G] (T L I : Subgroup G) : Prop where
  fsu : FSU G T L I
  notFF : ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Concl701FF T L I
  notThree : ¬ (L < fsuL0 T L ∧ Concl326ThreeC T L I)
  notOrth : ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Concl701Orth T L I

section Rows

variable {G : Type} [Group G]

@[expose] def IsTwistedPair (T L I : Subgroup G) : Prop :=
  ∃ t ∈ T, I ⊔ CFSG.conjugate I t = fsuV T I ∧ I ⊓ CFSG.conjugate I t = ⊥ ∧
    ¬ IsXSectionIso L ⊥ I (CFSG.conjugate I t)

variable (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)]

@[expose] def Row711SU3 : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ BinaryNaturalSU3 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n

@[expose] def Row711Sz : Prop :=
  ∃ n : ℕ, BinaryNaturalSz (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n

@[expose] def Row711L3Nine (n : ℕ) : Prop :=
  1 ≤ n ∧ BinaryNineTensor (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n

@[expose] def Row711M12 : Prop :=
  M12Ten (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ ∧
    Nonempty (↥(autOn (fsuL0 T L ⊔ T) (fsuV T I)) ≃* MulAut ↥NativeSporadic.M12)

@[expose] def Row711M22Hat : Prop :=
  Mhat22Twelve (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥

@[expose] def Row711M22Code : Prop :=
  MathieuCode22 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥

@[expose] def Row711M22Cocode : Prop :=
  MathieuCocode22 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥

@[expose] def Row711M23Code : Prop :=
  MathieuCode23 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥

@[expose] def Row711M23Cocode : Prop :=
  MathieuCocode23 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥

@[expose] def Row711M24Code : Prop :=
  MathieuCode24 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥

@[expose] def Row711M24Cocode : Prop :=
  MathieuCocode24 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥

@[expose] def Row711SL3Pair (n : ℕ) : Prop :=
  IsTwistedPair T L I ∧ BinaryNaturalSL (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
    (I.subgroupOf (fsuV T I)) ⊥ 3 n

@[expose] def Row711Sp4Pair : Prop :=
  IsTwistedPair T L I ∧
    ((∃ n : ℕ, 2 ≤ n ∧ BinaryNaturalSp4 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
        (I.subgroupOf (fsuV T I)) ⊥ n) ∨
      AlternatingNatural (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
        (I.subgroupOf (fsuV T I)) ⊥ 6)

@[expose] def Row711S7Pair : Prop :=
  IsTwistedPair T L I ∧
    A7Four (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) (I.subgroupOf (fsuV T I)) ⊥

@[expose] def Row711L3Wreath : Prop :=
  L < fsuL0 T L ∧ FFModel.RealizesMod (V := ↥(fsuV T I))
    (tensorPairModel (StatedSL 3 (ZMod 2)) (StatedSL 3 (ZMod 2))) (autOn (fsuL0 T L) (fsuV T I))

@[expose] def Row711OmegaPlus (n : ℕ) : Prop :=
  L < fsuL0 T L ∧ 2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    FFModel.RealizesMod (V := ↥(fsuV T I)) (tensorPairModel (StatedSL 2 K) (StatedSL 2 K))
      (autOn (fsuL0 T L) (fsuV T I))

@[expose] def Rows7_1_1 : Prop :=
  Row711SU3 T L I ∨ Row711Sz T L I ∨ (∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M12 T L I ∨
    Row711M22Hat T L I ∨ Row711M22Code T L I ∨ Row711M22Cocode T L I ∨ Row711M23Code T L I ∨
    Row711M23Cocode T L I ∨ Row711M24Code T L I ∨ Row711M24Cocode T L I ∨
    (∃ n : ℕ, Row711SL3Pair T L I n) ∨ Row711Sp4Pair T L I ∨ Row711S7Pair T L I ∨
    Row711L3Wreath T L I ∨ (∃ n : ℕ, Row711OmegaPlus T L I n)

end Rows

@[expose] def Stmt7_1_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∃ _ : IsMulCommutative ↥(fsuV T I), Rows7_1_1 T L I

section Hyps

variable {G : Type} [Group G]

@[expose] def Hyp7_3_1 (T L I : Subgroup G) : Prop :=
  ∀ _ : IsMulCommutative ↥(fsuV T I), ∀ n : ℕ, ¬ Row711OmegaPlus T L I n

@[expose] def Hyp8_2_1 (T L I : Subgroup G) : Prop :=
  ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Row711L3Wreath T L I

end Hyps

@[expose] def Stmt7_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Row711Sp4Pair T L I

@[expose] def Stmt7_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      (¬ Row711SU3 T L I ∧ ¬ Row711Sz T L I ∧ ¬ Row711M22Hat T L I) ∧
        ∀ n : ℕ, Row711SL3Pair T L I n → n = 1

@[expose] def Stmt7_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Row711M12 T L I ∧ ¬ Row711M23Code T L I

@[expose] def Stmt7_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Row711S7Pair T L I

@[expose] def Stmt7_6_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Row711SL3Pair T L I 1

@[expose] def Stmt8_1_3_M24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711M22Cocode T L I ∨ Row711M23Cocode T L I ∨ Row711M24Cocode T L I →
        Row711M24Cocode T L I

@[expose] def Stmt8_2_13_cocode : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I ∨ Row711M24Code T L I ∨
          Row711M24Cocode T L I) →
        (fsuV T I ≤ L ∧ L ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
            L ⊓ Subgroup.centralizer (fsuV T I : Set G) = fsuV T I ∧
            Nat.card ↥(fsuV T I) = 2 ^ 11 ∧
            NativeCocode24 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥) ∧
          L = fsuM T L

@[expose] def Stmt8_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I ∨ Row711M24Code T L I ∨
          Row711M24Cocode T L I) →
        Nonempty (G ≃* NativeSporadic.J4)

@[expose] def Stmt8_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Row711L3Wreath T L I

@[expose] def Stmt9_omegaPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), ∀ n : ℕ, ¬ Row711OmegaPlus T L I n

theorem stmt7_0_1_of_chain (hmod : StmtFSUModule) (hshape : Stmt7_0_1_shapeC)
    (h711 : Stmt7_1_1) (h735 : Stmt7_3_5) (h752 : Stmt7_5_2) (h754 : Stmt7_5_4)
    (h755 : Stmt7_5_5) (h761 : Stmt7_6_1) (h813 : Stmt8_1_3_M24)
    (h8213 : Stmt8_2_13_cocode) (h8214 : Stmt8_2_14) (h831 : Stmt8_3_1)
    (h9 : Stmt9_omegaPlus) : Stmt7_0_1 := by
  intro G _ _ T L I hfsu
  obtain ⟨hab, hnorm⟩ := hmod G T L I hfsu
  have hc : IsMulCommutative ↥(fsuV T I) := hab.1
  refine ⟨hc, hab, hnorm, ?_⟩
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hyp : Hyp7_0_2 G T L I :=
    { fsu := hfsu
      notFF := fun _ => h1
      notThree := fun h => h4 ⟨h.1, hshape G T L I hfsu h.1 h.2, h.2⟩
      notOrth := fun _ => h3 }
  have h731 : Hyp7_3_1 T L I := by
    intro _ n hn
    exact h9 G T L I hyp _ n hn
  have h821 : Hyp8_2_1 T L I := by
    intro _ hw
    exact h831 G T L I hyp h731 _ hw
  have hJ4 : ((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I ∨ Row711M24Code T L I ∨
      Row711M24Cocode T L I) → False := by
    intro hrow
    obtain ⟨⟨hVL, hLN, hLC, hcard, hcoc⟩, hLM⟩ := h8213 G T L I hyp h731 h821 _ hrow
    refine h2 ⟨hVL.trans hLM.le, hLM.symm.le.trans hLN, hcard, ?_, ?_,
      h8214 G T L I hyp h731 h821 _ hrow⟩
    · rw [← hLM]
      exact hLC
    · rw [← hLM]
      exact hcoc
  obtain ⟨_, hrow⟩ := h711 G T L I hyp
  rcases hrow with h | h | h | h | h | h | h | h | h | h | h | ⟨n, h⟩ | h | h | h | ⟨n, h⟩
  · exact (h752 G T L I hyp h731 _).1.1 h
  · exact (h752 G T L I hyp h731 _).1.2.1 h
  · exact hJ4 (Or.inl h)
  · exact (h754 G T L I hyp h731 _).1 h
  · exact (h752 G T L I hyp h731 _).1.2.2 h
  · exact hJ4 (Or.inr (Or.inl h))
  · exact hJ4 (Or.inr (Or.inr (Or.inr (h813 G T L I hyp h731 _ (Or.inl h)))))
  · exact (h754 G T L I hyp h731 _).2 h
  · exact hJ4 (Or.inr (Or.inr (Or.inr (h813 G T L I hyp h731 _ (Or.inr (Or.inl h))))))
  · exact hJ4 (Or.inr (Or.inr (Or.inl h)))
  · exact hJ4 (Or.inr (Or.inr (Or.inr h)))
  · have hn := (h752 G T L I hyp h731 _).2 n h
    subst hn
    exact h761 G T L I hyp h731 _ h
  · exact h735 G T L I hyp h731 _ h
  · exact h755 G T L I hyp h731 _ h
  · exact h821 _ h
  · exact h731 _ n h

end CFSG.Quasithin.H13
