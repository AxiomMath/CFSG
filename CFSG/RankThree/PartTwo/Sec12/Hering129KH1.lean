module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KE1
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)

@[expose] def PglHess (π : Bool) (p f : ℕ) (K : Type) [Field K] (y : GL (Fin 3) K)
    (m₀ : ProjGenLinGroup (Fin 3) K) (F : Subgroup (ProjGenLinGroup (Fin 3) K)) : Prop :=
  F ≤ projImage (Sec4.slPi π 3 (p ^ f) K) ∧
    CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ m₀ ∈ F ∧
    (∀ g ∈ F, ProjGenLinGroup.mk y * g * (ProjGenLinGroup.mk y)⁻¹ ∈ F) ∧
    F ⊓ (Subgroup.zpowers (ProjGenLinGroup.mk y) ⊔ Subgroup.zpowers m₀) =
      Subgroup.zpowers m₀ ∧
    (∀ g ∈ F, ProjGenLinGroup.mk y * g * (ProjGenLinGroup.mk y)⁻¹ * g⁻¹ ∈
      Subgroup.zpowers m₀) ∧
    (∃ g ∈ F, ProjGenLinGroup.mk y * g * (ProjGenLinGroup.mk y)⁻¹ * g⁻¹ ≠ 1) ∧
    (∀ g ∈ F, g ≠ 1 → ∃ n ∈ projImage (Sec4.slPi π 3 (p ^ f) K) ⊓
      Subgroup.normalizer (F : Set (ProjGenLinGroup (Fin 3) K)), n * m₀ * n⁻¹ = g) ∧
    Nonempty (Sec4.autIn (projImage (Sec4.slPi π 3 (p ^ f) K) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk y)) F ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

@[expose] def KF_L3_PGL : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K], Sec4.PiField π p f K → Sec4.ModThree π (p ^ f) →
    ∀ y : GL (Fin 3) K, y ∈ Sec4.glPi π 3 (p ^ f) K → y ∉ StatedScalars (Fin 3) K →
      y ^ 3 ∈ StatedScalars (Fin 3) K →
    ∀ m₀ : ProjGenLinGroup (Fin 3) K, m₀ ∈ projImage (Sec4.slPi π 3 (p ^ f) K) → m₀ ≠ 1 →
      m₀ ^ 3 = 1 → ProjGenLinGroup.mk y * m₀ = m₀ * ProjGenLinGroup.mk y →
    ∀ Xm : Subgroup (ProjGenLinGroup (Fin 3) K), Xm ≤ projImage (Sec4.slPi π 3 (p ^ f) K) →
      Xm ≤ Subgroup.centralizer ({ProjGenLinGroup.mk y} : Set (ProjGenLinGroup (Fin 3) K)) →
      Group.IsPerfect Xm → ¬ Group.IsSolvable Xm → m₀ ∈ Xm →
      ∃ F : Subgroup (ProjGenLinGroup (Fin 3) K), PglHess π p f K y m₀ F


@[expose] def Gap129HessL3Deg : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (Yh Bh : Subgroup P) (xh bh ch : P),
    HessData Yh Bh xh bh ch → ∀ (p : ℕ) [Fact p.Prime], p % 3 ≠ 1 →
      ¬ Nonempty (↥Yh ≃* projSL 3 (GaloisField p 0))

end CFSG.RankThree.PartTwo.Sec12
