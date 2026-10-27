module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutLie

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint

universe u

section Lie

variable {Mb : Type u} [Group Mb]

structure F431TwoOut (T S : Subgroup Mb) (f : Mb) (N N' : Subgroup Mb) (z : Mb) (I : Finset Mb) :
    Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le : T ≤ N
  T_le' : T ≤ N'
  S_le : S ≤ T
  S_norm : T ≤ Subgroup.normalizer (S : Set Mb)
  cyc : ∃ t₀ : Mb, T = S ⊔ Subgroup.zpowers t₀
  z_mem : z ∈ T
  z_two : orderOf z = 2
  z_ZN : z ∈ centerOf (perfectCore N)
  center_T : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w
  I_le : ∀ i ∈ I, i ∈ S ∧ orderOf i = 2
  fusion : ∀ x ∈ S, orderOf x = 2 → ∃ i ∈ I,
    (∃ m ∈ N, m * x * m⁻¹ = i) ∨ (∃ m ∈ N', m * x * m⁻¹ = i)
  f_mem : f ∈ T
  f_not : f ∉ S
  f_sq : f ^ 2 = 1
  Tf_lt : ∀ i ∈ I, Nat.card (spTf T f) < Nat.card ↥(T ⊓ Subgroup.centralizer ({i} : Set Mb))
  Sylow_Tf : IsSylowTwoOf (spTf T f) (Subgroup.centralizer ({f} : Set Mb) ⊓ N)
  Z_sq : ∀ x ∈ centerOf (perfectCore N), x ^ 2 = 1
  Z_S : centerOf S ≤ centerOf (perfectCore N)
  W_le : spWf T f ≤ centerOf S
  W_ne : ∃ x ∈ spWf T f, x ∈ centerOf (perfectCore N) ∧ x ≠ 1

end Lie

@[expose] def F431TwoOutLieProp (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D t m 2 f → ∀ A : LieAmalgamExt D,
    ¬ Odd (Nat.card ↥A.K / Nat.card D) →
    ∃ (T S : Subgroup ↥A.K) (g z : ↥A.K) (I : Finset ↥A.K),
      F431TwoOut T S g A.Mb1 A.Mb2 z I ∨ F431TwoOut T S g A.Mb2 A.Mb1 z I

end CFSG.Quasithin.H13.F431
