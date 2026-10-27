module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

variable {G : Type*} [Group G] [Finite G]

@[expose] def InducesTypeOn (L : Subgroup G) (x : G) (k : ℕ) : Prop :=
  ∃ (hx : x ∈ Subgroup.normalizer (L : Set G)) (π : Bool) (p f : ℕ) (K : Type) (_ : Field K)
    (_ : PiField π p f K) (_ : ModThree π (p ^ f))
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K))
    (y : GL (Fin 3) K), y ∈ glPi π 3 (p ^ f) K ∧ Type123 π (p ^ f) K y k ∧
      ∀ z : L ⧸ aschbacherSolvableCore 3 L,
        ((e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) z) :
            ProjGenLinGroup (Fin 3) K)) =
          ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹

@[expose] def IsTypeCOn (E L : Subgroup G) : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : PiField π p f K)
    (_ : ModThree π (p ^ f))
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K))
    (D : Subgroup (GL (Fin 3) K)), IsTypeC π (p ^ f) K D ∧
      (∀ τ ∈ autThetaQuot E L, ∃ y ∈ D, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
        ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
          ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) ∧
      ∀ y ∈ D, ∃ τ ∈ autThetaQuot E L, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
        ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
          ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹

@[expose] def IsHeisCentral (X : Type) [Group X] (Y : Type) [Group Y] : Prop :=
  ∃ U V : Subgroup X, U ⊔ V = ⊤ ∧ (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧ IsHeisThree U ∧
    Nonempty (V ≃* Y) ∧ Nat.card (U ⊓ V : Subgroup X) = 3

@[expose] def IsSLThreePiTwo (X : Type) [Group X] : Prop :=
  ∃ (L₀ : Subgroup X) (hL : L₀.Normal) (u a : X), IsSLThreePi L₀ ∧
    u ∈ Subgroup.centralizer (L₀ : Set X) ∧ u ∉ L₀ ∧ orderOf u = 3 ∧ a ^ 3 = 1 ∧
    L₀ ⊔ Subgroup.closure {u, a} = ⊤ ∧ u * a * u⁻¹ * a⁻¹ ≠ 1 ∧
    u * a * u⁻¹ * a⁻¹ ∈ L₀ ⊓ Subgroup.centralizer (L₀ : Set X) ∧
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : PiField π p f K)
      (_ : ModThree π (p ^ f)) (e : L₀ ≃* slPi π 3 (p ^ f) K) (y : GL (Fin 3) K),
      y ∈ glPi π 3 (p ^ f) K ∧ Type123 π (p ^ f) K y 3 ∧
        ∀ z : L₀, ((e ⟨a * z * a⁻¹, hL.conj_mem z z.2 a⟩ : GL (Fin 3) K)) =
          y * (e z : GL (Fin 3) K) * y⁻¹

end CFSG.RankThree.PartTwo.Sec4
