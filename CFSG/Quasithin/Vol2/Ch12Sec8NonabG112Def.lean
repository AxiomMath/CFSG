module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.Open.SQTKSimpleListTauCeti
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def permAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => x (σ⁻¹ i)

@[expose] def permCore (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {x | ∑ i, x i = 0}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hx ⊢
    rw [hx, mul_zero]

@[expose] def IsQuotientOfSQTKTauCeti (X : Type*) [Group X] : Prop :=
  ∃ (S : Type) (_ : Group S) (_ : Finite S), CFSG.Open.SQTKTauCeti.StronglyQuasithin S ∧
    CFSG.SectionRank.IsKGroupCat S ∧ ∃ φ : S →* X, Function.Surjective φ

section Conclusions

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def commSpanOf (L : Subgroup (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ γ ∈ L, ∃ v, w = γ v - v}

@[expose] def orthogonalSubgroupOf (q : V → ZMod 2) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {γ | ∀ v, q (γ v) = q v}
  mul_mem' := fun {a b} ha hb v => by
    show q (a (b v)) = q v
    rw [ha, hb]
  one_mem' := fun v => rfl
  inv_mem' := fun {a} ha v => by
    have := ha (a.symm v)
    simpa using this.symm

@[expose] def G112Concl1 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 2 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin 3))

@[expose] def G112Concl2 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 4 ∧ (10 ∣ Nat.card Γ ∨ 18 ∣ Nat.card Γ)

@[expose] def G112Concl3Partial (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 6 ∧ ∃ P : Subgroup ↥Γ, P.Normal ∧ CFSG.IsExtraspecial 3 ↥P ∧
    Nat.card P = 27 ∧ (∀ x : ↥P, x ^ 3 = 1) ∧ P.index ∣ 16 ∧ 4 ∣ P.index

@[expose] def IsSubSD16Heis (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∃ P : Subgroup ↥Γ, P.Normal ∧ CFSG.IsExtraspecial 3 ↥P ∧
    Nat.card P = 27 ∧ (∀ x : ↥P, x ^ 3 = 1) ∧ P.index ∣ 16 ∧ 4 ∣ P.index ∧
    ∃ S : Subgroup (V ≃ₗ[ZMod 2] V),
      CFSG.QuasithinUnique.IsSylowTwoOf S
        (Subgroup.normalizer (P.map Γ.subtype : Set (V ≃ₗ[ZMod 2] V))) ∧
      Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup 4) ∧
      Γ ≤ P.map Γ.subtype ⊔ S ∧
      ∃ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ S ∧ CFSG.Open.IsElemAbelian 2 E ∧
        Nat.card E = 4 ∧ E ≤ Γ

@[expose] def G112Concl3 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 6 ∧ IsSubSD16Heis Γ

theorem G112Concl3.toPartial {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (full : G112Concl3 Γ) : G112Concl3Partial Γ := by
  obtain ⟨dimension, P, normal, extraspecial, cardinality, exponent, indexBound,
    indexLower, realization⟩ := full
  exact ⟨dimension, P, normal, extraspecial, cardinality, exponent, indexBound, indexLower⟩

@[expose] def G112Concl4 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 6 ∧
    ∃ (φ : ↥(genFittingFStar ↥Γ) ≃* ↥(alternatingGroup (Fin 7)))
      (ψ : V ≃ₗ[ZMod 2] ↥(permCore 7)),
      ∀ (γ : ↥(genFittingFStar ↥Γ)) (v : V),
        (ψ (((γ : ↥Γ) : V ≃ₗ[ZMod 2] V) v) : Fin 7 → ZMod 2) =
          permAct ((φ γ : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) (ψ v)

@[expose] def G112Concl5 (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Prop :=
  Module.finrank (ZMod 2) V = 6 ∧ ∃ q : V → ZMod 2,
    (∀ v w, q (v + w) = q v + q w + B v w) ∧ (∀ (c : ZMod 2) v, q (c • v) = c * c * q v) ∧
      (∃ S : Submodule (ZMod 2) V, Module.finrank (ZMod 2) S = 3 ∧ ∀ s ∈ S, q s = 0) ∧
      Γ ≤ orthogonalSubgroupOf q ∧ Γ.relIndex (orthogonalSubgroupOf q) ≤ 2

@[expose] def G112Concl6 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 6 ∧ Nat.card Γ = 12096

@[expose] def G112Concl7 (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    Nonempty (↥(genFittingFStar ↥Γ) ≃* (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))) ∧
    ¬ X ≤ (genFittingFStar ↥Γ).map Γ.subtype

@[expose] def G112Concl8 (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Prop :=
  Module.finrank (ZMod 2) V = 8 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin 7)) ∧
    ∃ I : Submodule (ZMod 2) V, Module.finrank (ZMod 2) I = 4 ∧
      (∀ w ∈ I, ∀ w' ∈ I, B w w' = 0) ∧
      (∀ γ ∈ (genFittingLayer ↥Γ).map Γ.subtype, ∀ v ∈ I, γ v ∈ I) ∧
      ∃ x ∈ X, (∃ v ∈ I, x v ∉ I) ∧ IsCompl I (I.map (x : V →ₗ[ZMod 2] V))

@[expose] def G112Concl9 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    (Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) ∨
      Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 5)))))

@[expose] def G112Concl10 (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧ Nat.card Γ = 2160 ∧
    Nonempty (↥(genFittingLayer ↥Γ) ≃* ↥(alternatingGroup (Fin 6))) ∧
    Nat.card (pCore 3 ↥Γ) = 3 ∧
    ∃ x ∈ X, ∃ hx : x ∈ Γ, ∀ y : ↥(pCore 3 ↥Γ),
      (⟨x, hx⟩ : ↥Γ) * (y : ↥Γ) * (⟨x, hx⟩ : ↥Γ)⁻¹ = (y : ↥Γ)⁻¹

@[expose] def G112Concl11 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    Nonempty (↥(genFittingFStar ↥Γ) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))

@[expose] def G112Concl12 (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    ∃ (x : V ≃ₗ[ZMod 2] V) (L : Subgroup (V ≃ₗ[ZMod 2] V)), x ∈ X ∧ L ≤ Γ ∧
      (genFittingFStar ↥Γ).map Γ.subtype = L ⊔ L.map (MulAut.conj x).toMonoidHom ∧
      L ⊓ L.map (MulAut.conj x).toMonoidHom = ⊥ ∧
      (∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj x).toMonoidHom, a * b = b * a) ∧
      IsCompl (commSpanOf L) (commSpanOf (L.map (MulAut.conj x).toMonoidHom)) ∧
      (∃ (φ : ↥L ≃* ↥(alternatingGroup (Fin 5))) (ψ : ↥(commSpanOf L) ≃ₗ[ZMod 2] ↥(permCore 5)),
        ∀ (γ : ↥L) (v w : ↥(commSpanOf L)), (w : V) = (γ : V ≃ₗ[ZMod 2] V) (v : V) →
          (ψ w : Fin 5 → ZMod 2) = permAct ((φ γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
            (ψ v)) ∧
      Nat.card X = 8 ∧ X = Subgroup.zpowers x ⊔ (X ⊓ (L ⊔ L.map (MulAut.conj x).toMonoidHom))

@[expose] def G112Concl13 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 12 ∧ Nat.card Γ = 2661120

@[expose] def G112Conclusion (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  G112Concl1 Γ ∨ G112Concl2 Γ ∨ G112Concl3 Γ ∨ G112Concl4 Γ ∨ G112Concl5 B Γ ∨ G112Concl6 Γ ∨
    G112Concl7 Γ X ∨ G112Concl8 B Γ X ∨ G112Concl9 Γ ∨ G112Concl10 Γ X ∨ G112Concl11 Γ ∨
    G112Concl12 Γ X ∨ G112Concl13 Γ

end Conclusions

@[expose] def TheoremG112 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → IsQuotientOfSQTKTauCeti ↥Γ → G112Conclusion B Γ X

end CFSG.Quasithin
