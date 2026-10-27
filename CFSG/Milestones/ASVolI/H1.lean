module

public import Mathlib
public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.Background.E3Defs
import CFSG.Quasithin.Background.H11Main
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

open scoped commutatorElement

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] def linToMulAut (F W : Type*) [Field F] [AddCommGroup W] [Module F W] :
    (W ≃ₗ[F] W) →* MulAut (Multiplicative W) where
  toFun g := AddEquiv.toMultiplicative g.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def IsFTransvection (F : Type*) [Field F] (ι : Type*) [Fintype ι]
    (t : MulAut (Multiplicative (ι → F))) : Prop :=
  ∃ g : (ι → F) ≃ₗ[F] (ι → F), linToMulAut F (ι → F) g = t ∧
    Module.finrank F (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1 ∧
    (g.toLinearMap - LinearMap.id) ∘ₗ (g.toLinearMap - LinearMap.id) = 0

section Orth

variable (F : Type*) [Field F]

@[expose] def orthPlus (x : Fin 4 → F) : F := x 0 * x 1 + x 2 * x 3

@[expose] def orthMinus (a : F) (x : Fin 4 → F) : F :=
  x 0 * x 1 + x 2 ^ 2 + x 2 * x 3 + a * x 3 ^ 2

@[expose] def isometryGroup (Q : (Fin 4 → F) → F) : Subgroup ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) where
  carrier := {g | ∀ x, Q (g x) = Q x}
  mul_mem' {g h} hg hh x := by
    show Q (g (h x)) = Q x
    rw [hg, hh]
  one_mem' _ := rfl
  inv_mem' {g} hg x := by
    show Q (g.symm x) = Q x
    have := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

@[expose] def omegaFour (Q : (Fin 4 → F) → F) : Subgroup (MulAut (Multiplicative (Fin 4 → F))) :=
  (⁅isometryGroup F Q, isometryGroup F Q⁆).map (linToMulAut F (Fin 4 → F))

end Orth

@[expose] def IsOrthOmega (F : Type*) [Field F] (ε : ℤ) {V : Type*} [CommGroup V]
    (e : V ≃* Multiplicative (Fin 4 → F)) (L : Subgroup (MulAut V)) : Prop :=
  (ε = 1 ∧ L.map (MulAut.congr e).toMonoidHom = omegaFour F (orthPlus F)) ∨
  (ε = -1 ∧ ∃ a : F, (∀ t : F, t ^ 2 + t + a ≠ 0) ∧
    L.map (MulAut.congr e).toMonoidHom = omegaFour F (orthMinus F a))

section General

variable {V : Type*} [CommGroup V]

@[expose] def xiSub (A : Subgroup (MulAut V)) : Subgroup V :=
  ⨆ (a : MulAut V) (_ : a ∈ A) (_ : a ≠ 1), fixV (Subgroup.zpowers a)

@[expose] def commOn (W : Subgroup V) (A : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {u | ∃ a ∈ A, ∃ w ∈ W, u = a w * w⁻¹}

@[expose] def conjAut (g : MulAut V) (A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  A.map (MulAut.conj g).toMonoidHom

@[expose] def IsTwoCentralVec (M : Subgroup (MulAut V)) (v : V) : Prop :=
  ∃ S : Subgroup (MulAut V), IsSylowIn 2 S M ∧ ∀ s ∈ S, s v = v

@[expose] def InducesOn (G : Subgroup (MulAut V)) (U Z : Subgroup V) (A : Type*) [CommGroup A]
    (Γ : Subgroup (MulAut A)) : Prop :=
  Z ≤ U ∧ (∀ g ∈ G, ∀ u ∈ U, g u ∈ U) ∧ (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) ∧
  ∃ β : ↥U →* A, Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
    (∀ g ∈ G, ∃ γ ∈ Γ, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u)) ∧
    (∀ γ ∈ Γ, ∃ g ∈ G, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u))

@[expose] def natHom (d : ℕ) (K : Type*) [Field K] :
    GL (Fin d) K →* MulAut (Multiplicative (Fin d → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      left_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]

end General

section Chief

variable {A : Type*} [Group A]

@[expose] def IsActsInv (acts : Set (A → A)) (U : Subgroup A) : Prop :=
  ∀ f ∈ acts, ∀ u ∈ U, f u ∈ U

@[expose] def IsChiefFactorUnder (acts : Set (A → A)) (X Y : Subgroup A) : Prop :=
  X < Y ∧ IsActsInv acts X ∧ IsActsInv acts Y ∧
    ∀ W : Subgroup A, X ≤ W → W ≤ Y → IsActsInv acts W → W = X ∨ W = Y

@[expose] def NoncentralChiefCount (acts : Set (A → A)) (U : Subgroup A) (c : ℕ) : Prop :=
  ∃ (k : ℕ) (S : ℕ → Subgroup A), S 0 = ⊥ ∧ S k = U ∧
    (∀ i < k, IsChiefFactorUnder acts (S i) (S (i + 1))) ∧
    Set.ncard {i : ℕ | i < k ∧ ∃ f ∈ acts, ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i} = c

end Chief

@[expose] def actsOnModule {V : Type*} [CommGroup V] (Y : Subgroup (MulAut V)) : Set (V → V) :=
  {f | ∃ y ∈ Y, f = fun v => y v}

@[expose] def actsByConj {X : Type*} [Group X] (P : Subgroup X) : Set (X → X) :=
  {f | ∃ p ∈ P, f = fun u => p * u * p⁻¹}

@[expose] def natSub (d : ℕ) (K : Type*) [Field K] (S : Subgroup (GL (Fin d) K)) :
    Subgroup (MulAut (Multiplicative (Fin d → K))) :=
  S.map (natHom d K)

@[expose] def glStab {K : Type*} [Field K] (S : Set (Fin 3 → K)) : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∀ v ∈ S, (g : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ S ∧
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ S}
  mul_mem' {g h} hg hh v hv := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hg _ (hh v hv).1).1
    · rw [mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hh _ (hg v hv).2).2
  one_mem' v hv := by
    simpa using hv
  inv_mem' {g} hg v hv := by
    refine ⟨(hg v hv).2, ?_⟩
    simpa using (hg v hv).1

@[expose] def glFix {K : Type*} [Field K] (S : Set (Fin 3 → K)) : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∀ v ∈ S, (g : Matrix (Fin 3) (Fin 3) K).mulVec v = v}
  mul_mem' {g h} hg hh v hv := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh v hv, hg v hv]
  one_mem' v hv := by simp
  inv_mem' {g} hg v hv := by
    have h := hg v hv
    calc ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v
        = ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
            ((g : Matrix (Fin 3) (Fin 3) K).mulVec v) := by rw [h]
      _ = v := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

@[expose] def IsIrredOn {V : Type*} [CommGroup V] (L : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  W ≠ ⊥ ∧ ∀ U : Subgroup V, U ≤ W → (∀ l ∈ L, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = W

@[expose] def IsConjIn {X : Type*} [Group X] (G : Subgroup X) (u v : X) : Prop :=
  ∃ g ∈ G, g * u * g⁻¹ = v

@[expose] def IsExtOf {X : Type*} [Group X] (C E : Subgroup X) (Q : Type*) [Group Q] : Prop :=
  E ≤ C ∧ ∃ f : ↥C →* Q, Function.Surjective f ∧ f.ker = E.subgroupOf C


@[expose] def IsTwoCentralElt {X : Type*} [Group X] (M : Subgroup X) (a : X) : Prop :=
  ∃ S : Subgroup X, IsSylowIn 2 S M ∧ ∀ s ∈ S, s * a = a * s

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.ASVolI.ChH

@[expose] def H_0_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (M : Subgroup (MulAut V)) (n : ℕ), 1 ≤ n →
  ∀ (F : Type) [Field F], Nat.card F = 2 ^ n →
  ∀ [Module F (Additive V)] (d : ℕ), Module.finrank F (Additive V) = d →
  (∀ l ∈ perfectCore M, ∀ (c : F) (v : Additive V),
    MulEquiv.toAdditive l (c • v) = c • MulEquiv.toAdditive l v) →
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ x ∈ M, orderOf x = p →
  (∃ σ : F ≃+* F, σ ≠ 1 ∧ ∀ (c : F) (v : Additive V),
    MulEquiv.toAdditive x (c • v) = σ c • MulEquiv.toAdditive x v) →
    ((rkIdx (fixV (Subgroup.zpowers x)) : ℚ) = (p - 1) * n * d / p ∧
      (p - 1) * n * d / p ≥ 2 * n * d / (3 : ℚ))

theorem as_H_0_1 : H_0_1 := by
  intro V _ _ hV M n hn F _ hF _ d hd hL p hp hp2 x hx hord hσ
  obtain ⟨σ, hσ1, hxσ⟩ := hσ
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H.lemma_H_0_1 hn hF hd hp hp2 hord hσ1 hxσ
  have hp1 : 1 ≤ p := Nat.one_le_of_lt hp.one_lt
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e1 : (rkIdx (fixV (Subgroup.zpowers x)) : ℚ) * p = (p - 1) * n * d := by
    have := congrArg (Nat.cast : ℕ → ℚ) h1
    push_cast [Nat.cast_sub hp1] at this
    exact this
  have e2 : (rkIdx (fixV (Subgroup.zpowers x)) : ℚ) = (p - 1) * n * d / p := by
    rw [eq_div_iff hp0]
    exact e1
  refine ⟨e2, ?_⟩
  rw [← e2, ge_iff_le, div_le_iff₀ (by norm_num : (0 : ℚ) < 3)]
  have := congrArg (Nat.cast : ℕ → ℚ) (Nat.mul_comm 3 (rkIdx (fixV (Subgroup.zpowers x))))
  have h2' : (2 * n * d : ℚ) ≤ 3 * rkIdx (fixV (Subgroup.zpowers x)) := by exact_mod_cast h2
  linarith

@[expose] def H_1_1 : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) →
  ∀ (F : Type) [Field F], Nat.card F = 2 ^ n →
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (M : Subgroup (MulAut V)) (e : V ≃* Multiplicative (Fin 4 → F)),
    IsOrthOmega F ε e (perfectCore M) →
  ∀ A : Subgroup (MulAut V), IsA2 M A →
    (rk ↥A + n ≤ rkIdx (fixV A) + 1) ∧
    (rk ↥A + 2 ≤ rkIdx (fixV A) ∨
      (n = 2 ∧ ∃ t ∈ A, IsFTransvection F (Fin 4) (MulAut.congr e t))) ∧
    (A ≤ perfectCore M → rk ↥A + n ≤ rkIdx (fixV A))

theorem as_H_1_1 : H_1_1 := CFSG.Quasithin.H11Proof.h11_main

end CFSG.ASVolI
