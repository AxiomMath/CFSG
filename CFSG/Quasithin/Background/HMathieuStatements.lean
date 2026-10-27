module

public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin

namespace H

namespace Mathieu

open CFSG.Open CFSG.Monster.Code

variable {V : Type*} [CommGroup V]

@[expose] def xiV (A : Subgroup (MulAut V)) : Subgroup V :=
  ⨆ (a : MulAut V) (_ : a ∈ A) (_ : a ≠ 1), fixV (Subgroup.zpowers a)

@[expose] def RealizesBy (D : FFModel) (H : Subgroup (MulAut V)) (U Z : Subgroup V)
    (π : D.Gam →* ↥H) (β : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec) : Prop :=
  Function.Surjective π ∧ Z ≤ U ∧ D.ker ≤ D.sec ∧
  (∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U) ∧ (∀ h : ↥H, ∀ z ∈ Z, (h : MulAut V) z ∈ Z) ∧
  (∀ γ : D.Gam, ∀ m ∈ D.sec, D.act γ m ∈ D.sec) ∧ (∀ γ : D.Gam, ∀ m ∈ D.ker, D.act γ m ∈ D.ker) ∧
  Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
  ∀ (γ : D.Gam) (u : ↥U) (m : ↥D.sec) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U)
    (hm : D.act γ (m : D.Amb) ∈ D.sec),
    β u = QuotientGroup.mk m →
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩

theorem realizesVia_iff (D : FFModel) (H : Subgroup (MulAut V)) (U Z : Subgroup V)
    (π : D.Gam →* ↥H) : D.RealizesVia H U Z π ↔ ∃ β, RealizesBy D H U Z π β := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, β, h8, h9, h10⟩
    exact ⟨β, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro ⟨β, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, β, h8, h9, h10⟩

theorem realizes_iff (D : FFModel) (H : Subgroup (MulAut V)) (U Z : Subgroup V) :
    D.Realizes H U Z ↔ ∃ π β, RealizesBy D H U Z π β := by
  unfold FFModel.Realizes
  simp only [realizesVia_iff]

abbrev stab (x : Fin 24) : Subgroup (Equiv.Perm (Fin 24)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 24)) x

abbrev cocode24 : FFModel :=
  FFModel.golaySec CFSG.Monster.Code.AutPerm (G6.coreMod 24) golayC

abbrev cocode23 (x : Fin 24) : FFModel :=
  FFModel.golaySec (CFSG.Monster.Code.AutPerm ⊓ stab x) (G6.coreMod 24) golayC

abbrev cocode22 (x y : Fin 24) : FFModel :=
  FFModel.golaySec (CFSG.Monster.Code.AutPerm ⊓ stab x ⊓ stab y) (G6.coreMod 24)
    (golayC ⊔ Subgroup.zpowers (pairVec x y))

abbrev code24 : FFModel :=
  FFModel.golaySec CFSG.Monster.Code.AutPerm golayC (Subgroup.zpowers (G6.allOnes 24))

abbrev code23 (x : Fin 24) : FFModel :=
  FFModel.golaySec (CFSG.Monster.Code.AutPerm ⊓ stab x) golayC
    (Subgroup.zpowers (G6.allOnes 24))

abbrev code22 (x y : Fin 24) : FFModel :=
  FFModel.golaySec (CFSG.Monster.Code.AutPerm ⊓ stab x ⊓ stab y) (golayC ⊓ pairKer x y)
    (Subgroup.zpowers (G6.allOnes 24))

theorem mathieuCocode24_iff (H : Subgroup (MulAut V)) (U Z : Subgroup V) :
    MathieuCocode24 H U Z ↔ cocode24.Realizes H U Z := Iff.rfl

theorem mathieuCocode23_iff (H : Subgroup (MulAut V)) (U Z : Subgroup V) :
    MathieuCocode23 H U Z ↔ ∃ x, (cocode23 x).Realizes H U Z := Iff.rfl

theorem mathieuCocode22_iff (H : Subgroup (MulAut V)) (U Z : Subgroup V) :
    MathieuCocode22 H U Z ↔ ∃ x y, x ≠ y ∧ (cocode22 x y).Realizes H U Z := Iff.rfl

theorem pairVec_mem_coreMod (i j : Fin 24) : pairVec i j ∈ G6.coreMod 24 := by
  change ∑ k, Multiplicative.toAdd (pairVec i j) k = 0
  simp only [pairVec, unitVec, toAdd_mul, toAdd_ofAdd, Pi.add_apply, Finset.sum_add_distrib,
    Finset.sum_pi_single']
  simp only [Finset.mem_univ, ite_true]
  decide

@[expose] def IsCocodeO2 (L : Subgroup (MulAut V)) (v : V) : Prop :=
  (∃ (π : cocode24.Gam →* ↥L) (β : ↥(⊤ : Subgroup V) →* ↥cocode24.sec ⧸
      cocode24.ker.subgroupOf cocode24.sec), RealizesBy cocode24 L ⊤ ⊥ π β ∧
    ∃ (i j : Fin 24), i ≠ j ∧
      β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk ⟨pairVec i j, pairVec_mem_coreMod _ _⟩) ∨
  (∃ (x : Fin 24) (π : (cocode23 x).Gam →* ↥L) (β : ↥(⊤ : Subgroup V) →* ↥(cocode23 x).sec ⧸
      (cocode23 x).ker.subgroupOf (cocode23 x).sec), RealizesBy (cocode23 x) L ⊤ ⊥ π β ∧
    ∃ j : Fin 24, x ≠ j ∧
      β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk ⟨pairVec x j, pairVec_mem_coreMod _ _⟩) ∨
  (∃ (x y : Fin 24) (_ : x ≠ y) (π : (cocode22 x y).Gam →* ↥L)
      (β : ↥(⊤ : Subgroup V) →* ↥(cocode22 x y).sec ⧸
        (cocode22 x y).ker.subgroupOf (cocode22 x y).sec),
    RealizesBy (cocode22 x y) L ⊤ ⊥ π β ∧ ∃ j : Fin 24, x ≠ j ∧ y ≠ j ∧
      β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk ⟨pairVec x j, pairVec_mem_coreMod _ _⟩)

@[expose] def IsOver (L M : Subgroup (MulAut V)) : Prop :=
  L ≤ M ∧ M ≤ Subgroup.normalizer (L : Set (MulAut V))

@[expose] def StmtH13Card : Prop :=
  ∀ (V : Type) [CommGroup V] (L : Subgroup (MulAut V)),
    ((MathieuCocode24 L ⊤ ⊥ ∨ MathieuCode24 L ⊤ ⊥) → Nat.card V = 2 ^ 11) ∧
    ((MathieuCocode23 L ⊤ ⊥ ∨ MathieuCode23 L ⊤ ⊥) → Nat.card V = 2 ^ 11) ∧
    ((MathieuCocode22 L ⊤ ⊥ ∨ MathieuCode22 L ⊤ ⊥) → Nat.card V = 2 ^ 10)

@[expose] def StmtH14PRank : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), IsOver L M →
    ((MathieuCocode24 L ⊤ ⊥ ∨ MathieuCode24 L ⊤ ⊥) → CFSG.Open.pRank 2 M ≤ 6) ∧
    ((MathieuCocode23 L ⊤ ⊥ ∨ MathieuCode23 L ⊤ ⊥) → CFSG.Open.pRank 2 M ≤ 4) ∧
    ((MathieuCocode22 L ⊤ ⊥ ∨ MathieuCode22 L ⊤ ⊥) → CFSG.Open.pRank 2 M ≤ 5)

@[expose] def StmtH14_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), IsOver L M →
    ((MathieuCocode24 L ⊤ ⊥ ∨ MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥ ∨
        MathieuCode23 L ⊤ ⊥) → E3.mParam M = 4) ∧
    ((MathieuCocode22 L ⊤ ⊥ ∨ MathieuCode22 L ⊤ ⊥) → 3 ≤ E3.mParam M)

@[expose] def StmtH15O2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), IsOver L M →
    ∀ U : Subgroup V, (∀ v ∈ U, ¬ IsCocodeO2 L v) →
      ((∃ A : Subgroup (MulAut V), IsFOneOffender M A ∧ U ≤ fixV A) ∨
        (∃ y ∈ M, y ≠ 1 ∧ Odd (orderOf y) ∧ U ≤ fixV (Subgroup.zpowers y))) →
      (MathieuCocode22 L ⊤ ⊥ → rk ↥U ≤ 4) ∧ (MathieuCocode23 L ⊤ ⊥ → rk ↥U ≤ 4) ∧
        (MathieuCocode24 L ⊤ ⊥ → rk ↥U ≤ 3)

@[expose] def StmtH15M22 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), IsOver L M →
    MathieuCocode22 L ⊤ ⊥ →
      (∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A → Nat.card A = 32 →
        xiV A = ⊤ ∧ (⨆ (B : Subgroup (MulAut V)) (_ : B ≤ A) (_ : Nat.card B = 4), fixV B) = ⊤) ∧
      (∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A → Nat.card A = 16 →
        rkIdx (xiV A) ≤ 1)

@[expose] def StmtH15M24 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), IsOver L M →
    MathieuCocode24 L ⊤ ⊥ →
      ∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A → Nat.card A = 64 →
        xiV A = ⊤ ∨ rk ↥(fixV A) = 3

end Mathieu

end H

end CFSG.Quasithin
