module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

variable {Q : Type} [Group Q]

structure LeviData (L : Subgroup Q) (p : ℕ) (y : Q) (Y : Subgroup Q) : Prop where
  eq_commutator :
    Y = ⁅L ⊓ centralizer ({y} : Set Q), L ⊓ centralizer ({y} : Set Q)⁆
  mem : y ∈ Y
  centralizer_le_normalizer : centralizer ({y} : Set Q) ≤ normalizer (Y : Set Q)
  sl2 : Nonempty (↥Y ≃* SL(2, ZMod p))
  involution_eq : ∀ c ∈ L ⊓ centralizer (Y : Set Q), orderOf c = 2 → c = y
  exists_not_mem :
    ∃ g ∈ L ⊓ centralizer ({y} : Set Q), ∀ s ∈ Y, s⁻¹ * g ∉ centralizer (Y : Set Q)

structure OuterData (L : Subgroup Q) (p : ℕ) (b : Q) : Prop where
  pgl2 : Nonempty (↥(L ⊓ centralizer ({b} : Set Q)) ≃* CFSG.GorensteinWalter.PGL2 (ZMod p))
  psl2 : Nonempty (↥⁅L ⊓ centralizer ({b} : Set Q), L ⊓ centralizer ({b} : Set Q)⁆ ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
  centralizer_le_normalizer : centralizer ({b} : Set Q) ≤
    normalizer ((⁅L ⊓ centralizer ({b} : Set Q), L ⊓ centralizer ({b} : Set Q)⁆ :
      Subgroup Q) : Set Q)
  inf_centralizer_eq_bot : L ⊓ centralizer
    ((⁅L ⊓ centralizer ({b} : Set Q), L ⊓ centralizer ({b} : Set Q)⁆ : Subgroup Q) : Set Q) = ⊥
  card_eq : Nat.card ↥(L ⊓ centralizer ({b} : Set Q)) = p * (p ^ 2 - 1)

structure PermThreeMember (L T A : Subgroup Q) (z : Q) (X : Subgroup Q) : Prop where
  le : X ≤ L
  bar2 : Nonempty (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 X ≃* Equiv.Perm (Fin 3))
  sylow : IsSylowIn 2 (T ⊓ X) X
  tA_le_normalizer : UniquenessCase.PartTwo.tA T A ≤ normalizer (X : Set Q)
  tA_inf_le : UniquenessCase.PartTwo.tA T A ⊓ L ≤ X
  not_inf_le_pCore : ¬ A ⊓ L ≤ pCoreOf 2 X
  exists_conj : ∃ c ∈ X, c * z * c⁻¹ ≠ z ∧ c * z * c⁻¹ * z = z * (c * z * c⁻¹)

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
