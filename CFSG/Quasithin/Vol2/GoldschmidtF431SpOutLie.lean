module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLie

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint

universe u

section Lie

variable {Mb : Type u} [Group Mb]

@[expose] def spTf (T : Subgroup Mb) (f : Mb) : Subgroup Mb :=
  T ⊓ Subgroup.centralizer ({f} : Set Mb)

@[expose] def spWf (T : Subgroup Mb) (f : Mb) : Subgroup Mb :=
  centerOf (spTf T f) ⊓ ⁅spTf T f, spTf T f⁆

structure F431SpOut (T S : Subgroup Mb) (f : Mb) (N1 N2 : Subgroup Mb) (I : Finset Mb) :
    Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le₁ : T ≤ N1
  T_le₂ : T ≤ N2
  Q_abel : ∀ j, ∀ x ∈ spQ N1 N2 j, ∀ y ∈ spQ N1 N2 j, x * y = y * x
  Q_card : Nat.card (spQ N1 N2 1) = Nat.card (spQ N1 N2 0)
  A_eq : ∀ A : Subgroup Mb, A ≤ T → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    Nat.card A = Nat.card (spQ N1 N2 0) → A = spQ N1 N2 0 ∨ A = spQ N1 N2 1
  S_le : S ≤ T
  S_norm : T ≤ Subgroup.normalizer (S : Set Mb)
  cyc : ∃ t₀ : Mb, T = S ⊔ Subgroup.zpowers t₀
  I_center : ∀ i ∈ I, i ∈ centerOf T
  I_le_S : ∀ i ∈ I, i ∈ S
  order_two : ∀ i ∈ I, orderOf i = 2
  rep : ∀ x ∈ S, orderOf x = 2 → ∃! i, i ∈ I ∧ IsConj i x
  fusion : ∀ x ∈ S, orderOf x = 2 → ∃ i ∈ I,
    (∃ m ∈ N1, m * x * m⁻¹ = i) ∨ (∃ m ∈ N2, m * x * m⁻¹ = i)
  f_mem : f ∈ T
  f_not : f ∉ S
  f_sq : f ^ 2 = 1
  f_not_central : f ∉ centerOf T
  Z_sq : ∀ j, ∀ x ∈ spZ N1 N2 j, x ^ 2 = 1
  Z_cls : ∀ j, ∀ x ∈ spZ N1 N2 j, ∀ y ∈ centerOf S, IsConj x y → y ∈ spZ N1 N2 j
  W_le : spWf T f ≤ centerOf S
  W_ne : ∃ j, ∃ x ∈ spWf T f, x ∈ spZ N1 N2 j ∧ x ≠ 1
  Sylow_Tf : ∀ j, IsSylowTwoOf (spTf T f) (Subgroup.centralizer ({f} : Set Mb) ⊓ spN N1 N2 j)

end Lie

@[expose] def F431SpOutLieProp (f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D .PSp 2 2 f → ∀ A : LieAmalgamExt D,
    ¬ Odd (Nat.card ↥A.K / Nat.card D) →
    ∃ (T S : Subgroup ↥A.K) (g : ↥A.K) (I : Finset ↥A.K), F431SpOut T S g A.Mb1 A.Mb2 I

end CFSG.Quasithin.H13.F431
