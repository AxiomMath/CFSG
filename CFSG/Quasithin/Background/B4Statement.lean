
module

public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.D2Params
public import CFSG.Quasithin.Background.A1cModuleDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def kleinPairs6 : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure {Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 2 3 * Equiv.swap 4 5}

@[expose] def kleinRegular7 : Subgroup (Equiv.Perm (Fin 7)) :=
  Subgroup.closure {Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3}

@[expose] def AltConjTo (n : ℕ) (P : Subgroup ↥(alternatingGroup (Fin n))) (K : Subgroup (Equiv.Perm (Fin n))) :
    Prop :=
  ∃ c ∈ alternatingGroup (Fin n),
    P.map (alternatingGroup (Fin n)).subtype = K.map (MulAut.conj c).toMonoidHom

@[expose] def IsEndNodeRadical5 (B : Subgroup ↥(StatedSL 5 (ZMod 2))) : Prop :=
  (∃ v : Fin 5 → ZMod 2, v ≠ 0 ∧ ∀ g : ↥(StatedSL 5 (ZMod 2)), g ∈ B ↔
    ∃ φ : Fin 5 → ZMod 2, φ ⬝ᵥ v = 0 ∧
      ((g : Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
        1 + Matrix.vecMulVec v φ) ∨
  (∃ φ : Fin 5 → ZMod 2, φ ≠ 0 ∧ ∀ g : ↥(StatedSL 5 (ZMod 2)), g ∈ B ↔
    ∃ w : Fin 5 → ZMod 2, φ ⬝ᵥ w = 0 ∧
      ((g : Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
        1 + Matrix.vecMulVec w φ)

@[expose] def IsTransvectionFourGroup {K : Type} [Field K]
    (B : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) : Prop :=
  Nat.card B = 4 ∧ ∃ W : Submodule K (Fin 3 → K), Module.finrank K W = 2 ∧
    ∀ g ∈ B, g ≠ 1 → (∀ w ∈ W, ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w) ∧
      ∀ v, ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v - v ∈ W

section Cases

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def B4Hyp (G L : Subgroup (MulAut V)) : Prop :=
  SQTKGroup ↥G ∧ L = quasithinGenFitting G ∧ CFSG.IsQuasisimple ↥L ∧
    XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤

variable (G L A : Subgroup (MulAut V))

@[expose] def B42Case1 : Prop :=
  ffJ G = L ∧ (∃ n, BinaryNaturalSL L ⊤ ⊥ 2 n) ∧ IsSylowTwoOf A L ∧
    qOf G = ((1 : ℚ) : WithTop ℚ)

@[expose] def B42Case2 : Prop :=
  ffJ G = L ∧ (∃ n, BinaryNaturalSL L ⊤ ⊥ 3 n) ∧ qOf G = ((1 / 2 : ℚ) : WithTop ℚ)

@[expose] def B42Case3 : Prop :=
  (∃ n, BinaryNaturalSp4 (ffJ G) ⊤ ⊥ n ∧ (1 < n → ffJ G = L)) ∧ qOf G = ((2 / 3 : ℚ) : WithTop ℚ)

@[expose] def B42Case4 : Prop :=
  (∃ n, G2Natural (ffJ G) ⊤ ⊥ n ∧ rk ↥A = 3 * n ∧ (1 < n → ffJ G = L)) ∧
    qOf G = ((1 : ℚ) : WithTop ℚ)

@[expose] def B42Case5 : Prop :=
  (∃ n, (n = 5 ∨ n = 7) ∧ ∃ π : Equiv.Perm (Fin n) →* ↥(ffJ G),
    (FFModel.symDn n).RealizesVia (ffJ G) ⊤ ⊥ π ∧
    ∃ T : Set (Equiv.Perm (Fin n)), (∀ t ∈ T, t.IsSwap) ∧ T.Pairwise Commute ∧
      A.subgroupOf (ffJ G) = (Subgroup.closure T).map π) ∧
    qOf G = ((1 : ℚ) : WithTop ℚ)

@[expose] def B42Case6 : Prop :=
  ffJ G = L ∧ AlternatingNatural L ⊤ ⊥ 6 ∧ rk ↥A = 2 ∧ qOf G = ((1 : ℚ) : WithTop ℚ) ∧
    ∀ π : ↥(alternatingGroup (Fin 6)) →* ↥L, (FFModel.altDn 6).RealizesVia L ⊤ ⊥ π →
      AltConjTo 6 ((A.subgroupOf L).comap π) kleinPairs6

@[expose] def B42Case7 : Prop :=
  G = ffJ G ∧ ffJ G = L ∧ A7Four L ⊤ ⊥ ∧ Nat.card V = 2 ^ 4 ∧ qOf G = ((1 : ℚ) : WithTop ℚ) ∧
    ∀ π : ↥(alternatingGroup (Fin 7)) ≃* ↥L,
      AltConjTo 7 ((A.subgroupOf L).comap π.toMonoidHom) kleinRegular7

@[expose] def B42Case8 : Prop :=
  ffJ G = L ∧ Nat.card V = 2 ^ 6 ∧ qOf G = ((1 : ℚ) : WithTop ℚ) ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (Γ₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)),
      Nat.card K = 4 ∧
      (∀ g ∈ Γ₀, ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) ∧
      IsHat ↥Γ₀ ↥(alternatingGroup (Fin 6)) ∧
      (∀ g ∈ Subgroup.center ↥Γ₀, ∃ c : K,
        (((g : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) ∧
      ∃ π : ↥Γ₀ →* ↥L, (FFModel.nat Γ₀).RealizesVia L ⊤ ⊥ π ∧
        IsTransvectionFourGroup ((A.subgroupOf L).comap π |>.map Γ₀.subtype)

@[expose] def B42Case9 : Prop :=
  ffJ G = L ∧ ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ BinaryNaturalSL L ⊤ ⊥ n 1 ∧
    qOf G = ((1 / ((n : ℚ) - 1) : ℚ) : WithTop ℚ)

@[expose] def B42Case10 : Prop :=
  SLExteriorTwo L ⊤ ⊥ 4 ∧
    ((G = ffJ G ∧ ffJ G = L ∧ rk ↥A = 3 ∧ qOf G = ((1 : ℚ) : WithTop ℚ)) ∨
      (G = ffJ G ∧ Nonempty (↥G ≃* Equiv.Perm (Fin 8)) ∧ qOf G = ((3 / 4 : ℚ) : WithTop ℚ)))

@[expose] def B42Case11 : Prop :=
  G = ffJ G ∧ ffJ G = L ∧ Nat.card V = 2 ^ 10 ∧ qOf G = ((1 : ℚ) : WithTop ℚ) ∧
    ∃ π : ↥(StatedSL 5 (ZMod 2)) →* ↥L, (FFModel.extSq (ZMod 2) 5).RealizesVia L ⊤ ⊥ π ∧
      IsEndNodeRadical5 ((A.subgroupOf L).comap π)

@[expose] def B42Conclusion : Prop :=
  B42Case1 G L A ∨ B42Case2 G L ∨ B42Case3 G L ∨ B42Case4 G L A ∨ B42Case5 G A ∨
  B42Case6 G L A ∨ B42Case7 G L A ∨ B42Case8 G L A ∨ B42Case9 G L ∨ B42Case10 G L A ∨
  B42Case11 G L A

end Cases

@[expose] def AsB42 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender G A → B42Conclusion G L A

@[expose] def AsB43 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → (∃ A, IsFFStarOffender G A ∧ ¬ A ≤ L) →
      ((∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural (ffJ G) ⊤ ⊥ n) ∨ G2Natural (ffJ G) ⊤ ⊥ 1) ∧
        ((2 / 3 : ℚ) : WithTop ℚ) ≤ qOf G

section Table

variable {V : Type} [CommGroup V] [Finite V] (G L : Subgroup (MulAut V))

@[expose] def AsB45Table : Prop :=
  (AlternatingNatural L ⊤ ⊥ 7 ∧ qOf G = ((3 / 2 : ℚ) : WithTop ℚ) ∧
      qhatOf G = ((3 / 2 : ℚ) : WithTop ℚ)) ∨
  (∃ m, 1 ≤ m ∧ BinaryOrthogonalFour L ⊤ ⊥ m ∧ qOf G ≤ ((2 : ℚ) : WithTop ℚ) ∧
      qhatOf G ≤ ((3 / 2 : ℚ) : WithTop ℚ)) ∨
  (∃ m, BinaryNaturalSU3 L ⊤ ⊥ m ∧ qOf G = ((2 : ℚ) : WithTop ℚ) ∧
      qhatOf G = ((2 : ℚ) : WithTop ℚ)) ∨
  (∃ f, BinaryNaturalSz L ⊤ ⊥ f ∧ qOf G = ((2 : ℚ) : WithTop ℚ) ∧
      qhatOf G = ((2 : ℚ) : WithTop ℚ)) ∨
  (∃ m, 1 ≤ m ∧ BinaryNineTensor L ⊤ ⊥ m ∧ ((2 : ℚ) : WithTop ℚ) < qOf G ∧
      qhatOf G = ((5 / 4 : ℚ) : WithTop ℚ)) ∨
  (G2NaturalDerived L ⊤ ⊥ 1 ∧ qOf G = ((3 / 2 : ℚ) : WithTop ℚ) ∧
      qhatOf G = ((3 / 2 : ℚ) : WithTop ℚ)) ∨
  (M12Ten L ⊤ ⊥ ∧ ((2 : ℚ) : WithTop ℚ) < qOf G) ∨
  (Mhat22Twelve L ⊤ ⊥ ∧ ((1 : ℚ) : WithTop ℚ) < qOf G) ∨
  (MathieuCocode22 L ⊤ ⊥ ∧ ((2 : ℚ) : WithTop ℚ) < qOf G) ∨
  (MathieuCode22 L ⊤ ⊥ ∧ ((2 : ℚ) : WithTop ℚ) ≤ qOf G) ∨
  ((MathieuCocode23 L ⊤ ⊥ ∨ MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥ ∨ MathieuCode24 L ⊤ ⊥) ∧
      ((2 : ℚ) : WithTop ℚ) < qOf G)

@[expose] def AsB45Part3 : Prop :=
  qhatOf G = ((2 : ℚ) : WithTop ℚ) ∧ ((2 : ℚ) : WithTop ℚ) < qOf G ∧
    ((∃ a, 1 ≤ a ∧ TwistedTensorSp4 L ⊤ ⊥ a) ∨
      (IsSporadic .J2 ↥L ∧ Nat.card V = 2 ^ 12 ∧ J2Twelve L ⊤ ⊥))

end Table

@[expose] def AsB45 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → qhatOf G ≤ ((2 : ℚ) : WithTop ℚ) →
      (qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) ∧ (∃ A, IsFFStarOffender G A) ∧
        ∀ A, IsFFStarOffender G A → B42Conclusion G L A) ∨
      (((1 : ℚ) : WithTop ℚ) < qhatOf G ∧ AsB45Table G L) ∨
      AsB45Part3 G L

end CFSG.Quasithin
