
module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped Matrix

structure FFModel where
  Gam : Type
  [gamGroup : Group Gam]
  Amb : Type
  [ambGroup : CommGroup Amb]
  act : Gam → Amb → Amb
  sec : Subgroup Amb
  ker : Subgroup Amb

attribute [instance] FFModel.gamGroup FFModel.ambGroup

namespace FFModel

variable {V : Type*} [CommGroup V]

@[expose] def RealizesVia (D : FFModel) (H : Subgroup (MulAut V)) (U Z : Subgroup V)
    (π : D.Gam →* ↥H) : Prop :=
  Function.Surjective π ∧ Z ≤ U ∧ D.ker ≤ D.sec ∧
  (∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U) ∧ (∀ h : ↥H, ∀ z ∈ Z, (h : MulAut V) z ∈ Z) ∧
  (∀ γ : D.Gam, ∀ m ∈ D.sec, D.act γ m ∈ D.sec) ∧ (∀ γ : D.Gam, ∀ m ∈ D.ker, D.act γ m ∈ D.ker) ∧
  ∃ β : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec,
    Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
    ∀ (γ : D.Gam) (u : ↥U) (m : ↥D.sec) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U)
      (hm : D.act γ (m : D.Amb) ∈ D.sec),
      β u = QuotientGroup.mk m →
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩

@[expose] def Realizes (D : FFModel) (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ π : D.Gam →* ↥H, D.RealizesVia H U Z π

@[expose] def RealizesMod (D : FFModel) (H : Subgroup (MulAut V)) : Prop :=
  D.Realizes H ⊤ ⊥

end FFModel

section Natural

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def natAct (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (g : ↥Γ)
    (x : Multiplicative (ι → K)) : Multiplicative (ι → K) :=
  Multiplicative.ofAdd
    ((((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)).mulVec (Multiplicative.toAdd x))

@[expose] def FFModel.nat (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) : FFModel where
  Gam := ↥Γ
  Amb := Multiplicative (ι → K)
  act := natAct Γ
  sec := ⊤
  ker := ⊥

@[expose] def dualNatAct (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (g : ↥Γ)
    (x : Multiplicative (ι → K)) : Multiplicative (ι → K) :=
  Multiplicative.ofAdd
    ((((g⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)ᵀ.mulVec (Multiplicative.toAdd x))

@[expose] def FFModel.dualNat (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) : FFModel where
  Gam := ↥Γ
  Amb := Multiplicative (ι → K)
  act := dualNatAct Γ
  sec := ⊤
  ker := ⊥

end Natural

section BinaryNatural

variable {V : Type*} [CommGroup V]

@[expose] def BinaryNaturalSL (H : Subgroup (MulAut V)) (U Z : Subgroup V) (d a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.nat (StatedSL d K)).Realizes H U Z

@[expose] def BinaryNaturalSp4 (H : Subgroup (MulAut V)) (U Z : Subgroup V) (a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.nat (StatedSp 2 K)).Realizes H U Z

@[expose] def BinaryNaturalSU3 (H : Subgroup (MulAut V)) (U Z : Subgroup V) (a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ a) ^ 2 ∧
    (FFModel.nat (StatedSU 3 (2 ^ a) K)).Realizes H U Z

@[expose] def BinaryNaturalSz (H : Subgroup (MulAut V)) (U Z : Subgroup V) (f : ℕ) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
    (FFModel.nat (CFSG.Blueprint.suzukiGroup a K)).Realizes H U Z

end BinaryNatural

@[expose] def FFModel.altDn (n : ℕ) : FFModel where
  Gam := ↥(alternatingGroup (Fin n))
  Amb := G6.PermMod n
  act σ x := G6.permAct n (σ : Equiv.Perm (Fin n)) x
  sec := G6.coreMod n
  ker := Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n

@[expose] def FFModel.symDn (n : ℕ) : FFModel where
  Gam := Equiv.Perm (Fin n)
  Amb := G6.PermMod n
  act σ x := G6.permAct n σ x
  sec := G6.coreMod n
  ker := Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n

section Alternating

variable {V : Type*} [CommGroup V]

@[expose] def AlternatingNatural (H : Subgroup (MulAut V)) (U Z : Subgroup V) (n : ℕ) : Prop :=
  (FFModel.altDn n).Realizes H U Z

@[expose] def SymmetricNatural (H : Subgroup (MulAut V)) (U Z : Subgroup V) (n : ℕ) : Prop :=
  (FFModel.symDn n).Realizes H U Z

end Alternating

@[expose] noncomputable def altLift7 :
    ↥(alternatingGroup (Fin 7)) →* ↥(alternatingGroup (Fin 8)) :=
  ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 7 ↪ Fin 8)).comp
      (alternatingGroup (Fin 7)).subtype).codRestrict (alternatingGroup (Fin 8)) fun σ => by
    have h := σ.2
    rw [Equiv.Perm.mem_alternatingGroup] at h ⊢
    have key : Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 7 ↪ Fin 8)
        (σ : Equiv.Perm (Fin 7))) = Equiv.Perm.sign (σ : Equiv.Perm (Fin 7)) := by
      classical
      rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
      convert Equiv.Perm.sign_extendDomain (σ : Equiv.Perm (Fin 7))
        (Equiv.ofInjective (Fin.castSuccEmb : Fin 7 ↪ Fin 8).1 (Fin.castSuccEmb : Fin 7 ↪ Fin 8).2)
    exact key.trans h

@[expose] noncomputable def a7Act
    (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (σ : ↥(alternatingGroup (Fin 7))) (x : Multiplicative (Fin 4 → ZMod 2)) :
    Multiplicative (Fin 4 → ZMod 2) :=
  Multiplicative.ofAdd
    ((((α (altLift7 σ) : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec
      (Multiplicative.toAdd x))

@[expose] noncomputable def FFModel.a7Four
    (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : FFModel where
  Gam := ↥(alternatingGroup (Fin 7))
  Amb := Multiplicative (Fin 4 → ZMod 2)
  act := a7Act α
  sec := ⊤
  ker := ⊥

section A7

variable {V : Type*} [CommGroup V]

@[expose] def A7Four (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
    (FFModel.a7Four α).Realizes H U Z

end A7

section TripleA6

variable {V : Type*} [CommGroup V]

@[expose] def TripleA6Six (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (Γ₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)),
    Nat.card K = 4 ∧ (∀ g ∈ Γ₀, ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) ∧
    IsHat ↥Γ₀ ↥(alternatingGroup (Fin 6)) ∧
    (∀ g ∈ Subgroup.center ↥Γ₀, ∃ c : K,
      (((g : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) ∧
    (FFModel.nat Γ₀).Realizes H U Z

end TripleA6

end CFSG.Quasithin
