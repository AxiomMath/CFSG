module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431LieW

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint

universe u

section Lie

variable {Mb : Type u} [Group Mb]

@[expose] def spN (N1 N2 : Subgroup Mb) : Fin 2 → Subgroup Mb := ![N1, N2]

@[expose] def spQ (N1 N2 : Subgroup Mb) (j : Fin 2) : Subgroup Mb := pCoreOf 2 (spN N1 N2 j)

@[expose] def spZ (N1 N2 : Subgroup Mb) (j : Fin 2) : Subgroup Mb :=
  centerOf (perfectCore (spN N1 N2 j))

structure F431SpLie (T N1 N2 : Subgroup Mb) (I : Finset Mb) : Prop where
  W : F431LieW T N1 N2 I
  Q_abel : ∀ j, ∀ x ∈ spQ N1 N2 j, ∀ y ∈ spQ N1 N2 j, x * y = y * x
  Z_le_Q : ∀ j, centerOf T ≤ spQ N1 N2 j
  Z_sq : ∀ z ∈ centerOf T, z ^ 2 = 1
  inv_mem : ∀ x ∈ T, x ^ 2 = 1 → ∃ j, x ∈ spQ N1 N2 j
  cen : ∀ j, ∀ x ∈ spQ N1 N2 j, x ∉ centerOf T → ∀ y ∈ T, y * x = x * y → y ∈ spQ N1 N2 j
  ex : ∀ j, ∃ x ∈ spQ N1 N2 j, x ∉ centerOf T ∧ x ^ 2 = 1
  O2N12 : pCoreOf 2 (N1 ⊓ N2) = T
  I_center : ∀ i ∈ I, i ∈ centerOf T
  I_type : ∀ i ∈ I,
    (i ∈ spZ N1 N2 0 ∧ Subgroup.centralizer ({i} : Set Mb) ≤ N1) ∨
    (i ∈ spZ N1 N2 1 ∧ Subgroup.centralizer ({i} : Set Mb) ≤ N2) ∨
    Subgroup.centralizer ({i} : Set Mb) ≤ N1 ⊓ N2
  Z_le : ∀ j, spZ N1 N2 j ≤ centerOf T
  Z_cls : ∀ j, ∀ x ∈ spZ N1 N2 j, ∀ y ∈ centerOf T, IsConj x y → y ∈ spZ N1 N2 j
  Z_trans : ∀ j, ∀ x ∈ spZ N1 N2 j, ∀ y ∈ spZ N1 N2 j, x ≠ 1 → y ≠ 1 →
    ∃ m ∈ spN N1 N2 j, m * x * m⁻¹ = y
  Z_ne : ∀ j, ∃ x ∈ spZ N1 N2 j, x ≠ 1

end Lie

@[expose] def F431SpLieProp (f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D .PSp 2 2 f → ∀ A : LieAmalgamExt D,
    Odd (Nat.card ↥A.K / Nat.card D) →
    ∃ (T : Subgroup ↥A.K) (I : Finset ↥A.K), F431SpLie T A.Mb1 A.Mb2 I

end CFSG.Quasithin.H13.F431
