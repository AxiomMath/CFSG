module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace S126C

structure Conf12626 {Q : Type} [Group Q] (K L P T : Subgroup Q) (v : Q) : Prop where
  comp : CFSG.IsComponent K
  sylow : IsSylowTwoOf T ⊤
  v_mem : v ∈ T
  v_central : ∀ t ∈ T, v * t = t * v
  v_sq : v ^ 2 = 1
  v_norm : v ∈ Subgroup.normalizer (K : Set Q)
  v_nc : ∃ k ∈ K, v * k ≠ k * v
  inv : ∀ x : Q, Odd (orderOf x) → v * x * v⁻¹ = x⁻¹ → x ^ 3 = 1 ∨ x ^ 5 = 1
  L_cent : ∀ l ∈ L, v * l = l * v
  L_star : Subgroup.centralizer ({v} : Set Q) ≤ Subgroup.normalizer (L : Set Q)
  L_norm : L ≤ Subgroup.normalizer (K : Set Q)
  L_gen : oTwoUpper L = L
  L_three : ∀ x ∈ L, Odd (orderOf x) → x ^ 3 = 1
  L_nc : ∃ l ∈ L, ∃ k ∈ K, l * k ≠ k * l
  P_le : P ≤ L
  P_elem : IsElemAbelian 3 P
  P_card : Nat.card P = 9

end S126C

@[expose] def FactComp12626 : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    S126C.Conf12626 K L P T v →
      IsHat ↥K (alternatingGroup (Fin 7)) ∨ IsHat ↥K (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
        IsPSL 2 11 1 ↥K

@[expose] def FactM22Twelve12626 : Prop :=
  ∀ (Y W : Type) [Group Y] [Finite Y] [Group W] [Finite W],
    (∀ a b : W, a * b = b * a) → (∀ w : W, w ^ 2 = 1) → ∀ (ρ : Y →* MulAut W) (K : Subgroup Y),
      IsHat ↥K (CFSG.Blueprint.NativeSporadic.Carrier .M22) → K ⊓ ρ.ker = ⊥ →
      ∀ t : Y, t ^ 2 = 1 → t ∈ Subgroup.normalizer (K : Set Y) → (∃ k ∈ K, t * k ≠ k * t) →
        Nat.card ↥{x : W | ∃ w, x = w⁻¹ * ρ t w} ≤ 2 ^ 4 →
          Group.IsSolvable ↥(K ⊓ Subgroup.centralizer ({t} : Set Y)) ∧
            ∀ w : W, (∃ u, w = u⁻¹ * ρ t u) → w ≠ 1 →
              ¬ Group.IsSolvable ↥(K ⊓ (MulAction.stabilizer (MulAut W) w).comap ρ)

end CFSG.Quasithin.H13
