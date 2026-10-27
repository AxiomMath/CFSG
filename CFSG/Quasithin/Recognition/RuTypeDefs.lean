module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Recognition.RuTypeF4

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

@[expose] def natAct3 (g : SL(3, ZMod 2)) (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v

@[expose] def IsTraceZero (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop := A.trace = 0

instance : DecidablePred IsTraceZero := fun A => inferInstanceAs (Decidable (A.trace = 0))

@[expose] def stAct (g : SL(3, ZMod 2)) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
    ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))

@[expose] def frobF4 : F4 →+* F4 where
  toFun x := x * x
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem frobF4_apply (x : F4) : frobF4 x = x * x := rfl

theorem frobF4_frobF4 (x : F4) : frobF4 (frobF4 x) = x := by
  revert x
  decide

@[expose] def frobSL : MulAut SL(2, F4) where
  toFun := Matrix.SpecialLinearGroup.map frobF4
  invFun := Matrix.SpecialLinearGroup.map frobF4
  left_inv := fun A => by ext i j; simp [frobF4_frobF4]
  right_inv := fun A => by ext i j; simp [frobF4_frobF4]
  map_mul' := fun A B => map_mul _ A B

theorem frobSL_mul_self : frobSL * frobSL = 1 := by
  ext A i j
  simp [frobSL, frobF4_frobF4]

@[expose] def slFrobAct : Multiplicative (ZMod 2) →* MulAut SL(2, F4) where
  toFun k := if Multiplicative.toAdd k = 0 then 1 else frobSL
  map_one' := by simp
  map_mul' := fun a b => by
    have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    rcases key (Multiplicative.toAdd a) with ha | ha <;>
      rcases key (Multiplicative.toAdd b) with hb | hb <;>
      simp [ha, hb, toAdd_mul, frobSL_mul_self, h11]

abbrev SigmaL2F4 : Type := SL(2, F4) ⋊[slFrobAct] Multiplicative (ZMod 2)

@[expose] def frobVec (k : Multiplicative (ZMod 2)) (v : Fin 2 → F4) : Fin 2 → F4 :=
  if Multiplicative.toAdd k = 0 then v else fun i => frobF4 (v i)

@[expose] def sigmaAct (x : SigmaL2F4) (v : Fin 2 → F4) : Fin 2 → F4 :=
  (x.left : Matrix (Fin 2) (Fin 2) F4).mulVec (frobVec x.right v)

variable {G : Type*} [Group G]

structure RuOne (L : Subgroup G) : Prop where
  center_eq_commutator : centerOf (pCoreOf 2 L) = ⁅pCoreOf 2 L, pCoreOf 2 L⁆
  center_eq_frattini : centerOf (pCoreOf 2 L) = frattiniOf (pCoreOf 2 L)
  center_elem : IsElemAbelian 2 (centerOf (pCoreOf 2 L))
  modules : ∃ θ : L →* SL(3, ZMod 2), Function.Surjective θ ∧
    θ.ker = (pCoreOf 2 L).subgroupOf L ∧
    (∃ ψ : centerOf (pCoreOf 2 L) ≃* Multiplicative (Fin 3 → ZMod 2),
      ∀ (l : L) (v w : centerOf (pCoreOf 2 L)), (w : G) = l * v * (l : G)⁻¹ →
        ψ w = Multiplicative.ofAdd (natAct3 (θ l) (Multiplicative.toAdd (ψ v)))) ∧
    (∃ χ : pCoreOf 2 L →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)),
      χ.ker = (centerOf (pCoreOf 2 L)).subgroupOf (pCoreOf 2 L) ∧
      (∀ s, IsTraceZero (Multiplicative.toAdd (χ s))) ∧
      (∀ A, IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A) ∧
      ∀ (l : L) (s t : pCoreOf 2 L), (t : G) = l * s * (l : G)⁻¹ →
        χ t = Multiplicative.ofAdd (stAct (θ l) (Multiplicative.toAdd (χ s))))
  eq_normalizer : L = Subgroup.normalizer (centerOf (pCoreOf 2 L) : Set G)

structure RuTwo (L : Subgroup G) (T : Sylow 2 G) : Prop where
  sylow_inf : ¬ 2 ∣ ((T : Subgroup G) ⊓ L).relIndex L
  V_le_H : centerOf (pCoreOf 2 L) ≤ Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)
  Z_le_U : centerOf (T : Subgroup G) ≤ conjClosure (centerOf (pCoreOf 2 L))
    (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))
  U_le_Q : conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) ≤
    pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))
  symmetric : ∃ φ : Subgroup.centralizer (centerOf (T : Subgroup G) : Set G) →*
      Equiv.Perm (Fin 5), Function.Surjective φ ∧
    φ.ker = (pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))).subgroupOf
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))
  UZ_elem : ∀ u ∈ conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)),
    ∀ u' ∈ conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)),
    u * u' * u⁻¹ * u'⁻¹ ∈ centerOf (T : Subgroup G) ∧ u ^ 2 ∈ centerOf (T : Subgroup G)
  UZ_central : ∀ q ∈ pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)),
    ∀ u ∈ conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)),
    q * u * q⁻¹ * u⁻¹ ∈ centerOf (T : Subgroup G)
  natural : ∃ (φ : Subgroup.centralizer (centerOf (T : Subgroup G) : Set G) →* SigmaL2F4)
      (ψ : conjClosure (centerOf (pCoreOf 2 L))
        (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) →*
        Multiplicative (Fin 2 → F4)),
    Function.Surjective φ ∧
    φ.ker = (pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))).subgroupOf
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) ∧
    Function.Surjective ψ ∧
    ψ.ker = (centerOf (T : Subgroup G)).subgroupOf (conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))) ∧
    ∀ (h : Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))
      (u u' : conjClosure (centerOf (pCoreOf 2 L))
        (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))),
      (u' : G) = h * u * (h : G)⁻¹ →
        ψ u' = Multiplicative.ofAdd (sigmaAct (φ h) (Multiplicative.toAdd (ψ u)))
  QU_elem : ∀ q ∈ pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)),
    ∀ q' ∈ pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)),
    q * q' * q⁻¹ * q'⁻¹ ∈ conjClosure (centerOf (pCoreOf 2 L))
        (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) ∧
      q ^ 2 ∈ conjClosure (centerOf (pCoreOf 2 L))
        (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))
  QU_card : (conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))).relIndex
    (pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))) = 2 ^ 6
  QU_indecomposable : ∀ A B : Subgroup G,
    conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) ≤ A →
    conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) ≤ B →
    A ≤ pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) →
    B ≤ pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) →
    Subgroup.centralizer (centerOf (T : Subgroup G) : Set G) ≤
      Subgroup.normalizer (A : Set G) →
    Subgroup.centralizer (centerOf (T : Subgroup G) : Set G) ≤
      Subgroup.normalizer (B : Set G) →
    A ⊓ B = conjClosure (centerOf (pCoreOf 2 L))
      (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) →
    A ⊔ B = pCoreOf 2 (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) →
    A = conjClosure (centerOf (pCoreOf 2 L))
        (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G)) ∨
      B = conjClosure (centerOf (pCoreOf 2 L))
        (Subgroup.centralizer (centerOf (T : Subgroup G) : Set G))

@[expose] def IsTypeRu (G : Type*) [Group G] : Prop :=
  ∃ L : Subgroup G, RuOne L ∧ ∃ T : Sylow 2 G, RuTwo L T

@[expose] def StatementJ11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTypeRu G →
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Ru)

end CFSG.Quasithin.RuType
