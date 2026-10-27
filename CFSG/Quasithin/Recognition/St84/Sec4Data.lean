module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.St84.Sec6ZTools
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

section TypeZero

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable (X : Setup Γ G)

theorem S_le_L (i : ℤ) (hi : i = 0 ∨ i = 1) : X.S ≤ X.L i := by
  rcases hi with rfl | rfl
  · rw [← X.edgeSylow_zero]
    exact X.edgeSylow_le_L 0
  · rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow_L_succ 0).1

private theorem K_le_normalizer_S : X.K ≤ Subgroup.normalizer (X.S : Set G) :=
  X.K_le_inf.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1))

theorem card_inf_of_card (hc : CharTwoStab (V := V) (G := G)) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 1) * Nat.card X.S = Nat.card (X.Q 0) * Nat.card (X.Q 1) := by
  have hsup : X.Q 0 ⊔ X.Q 1 = X.S := by
    have h := X.sup_Q_eq_edgeSylow hc 0
    rw [show (0 : ℤ) + 1 = 1 by norm_num] at h
    rw [h, X.edgeSylow_zero]
  have hSG : X.S ≤ X.Gi 0 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left
  have hQ1S : X.Q 1 ≤ X.S := by
    rw [← hsup]
    exact le_sup_right
  have hnorm : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hQ1S.trans (hSG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hsup] at h
  rw [mul_comm (Nat.card X.S) (Nat.card ↥(X.Q 0 ⊓ X.Q 1))] at h
  exact h

theorem Ki_inf_eq_bot_of (i : ℤ) (hi : i = 0 ∨ i = 1)
    {U : Subgroup G} (hU : U ≠ ⊥) (h₀ : U ≤ Subgroup.centralizer (X.Ki i : Set G))
    (h₁ : ∀ k ∈ X.Ki (1 - i), k ≠ 1 → ∀ u ∈ U, k * u = u * k → u = 1) :
    X.Ki 0 ⊓ X.Ki 1 = ⊥ := by
  obtain ⟨u, hu, hu1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hU
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  by_contra hk1
  have hker : k ∈ X.Ki i ∧ k ∈ X.Ki (1 - i) := by
    rcases hi with rfl | rfl
    · exact ⟨hk.1, hk.2⟩
    · exact ⟨hk.2, hk.1⟩
  have hcomm : k * u = u * k :=
    (Subgroup.mem_centralizer_iff.mp (h₀ hu)) k hker.1
  exact hu1 (h₁ k hker.2 hk1 u hu hcomm)

private theorem card_K_eq_of_Ki_inf_eq_bot (h : X.Ki 0 ⊓ X.Ki 1 = ⊥) :
    Nat.card X.K = (2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1) := by
  have hKi1N : X.Ki 1 ≤ Subgroup.normalizer (X.Ki 0 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    have hyK : y ∈ X.K := (inf_le_left : X.Ki 1 ≤ X.K) hy
    have hxK : x ∈ X.K := (inf_le_left : X.Ki 0 ≤ X.K) hx
    have hxL : x ∈ X.L 0 := (inf_le_right : X.Ki 0 ≤ X.L 0) hx
    refine ⟨?_, ?_⟩
    · exact X.K.mul_mem (X.K.mul_mem hyK hxK) (X.K.inv_mem hyK)
    · have hyG : y ∈ X.Gi 0 := X.K_le_Gi 0 hyK
      exact (Subgroup.le_normalizer_iff.mp (le_normalizer_oTwoPrime (X.Gi 0)) y hyG x hxL)
  have hKcard : Nat.card X.K = Nat.card (X.Ki 0) * Nat.card (X.Ki 1) := by
    rw [X.K_eq_sup]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (X.Ki 0) (X.Ki 1) hKi1N (by rw [disjoint_iff]; exact h)
  have hKi0 : Nat.card (X.Ki 0) = 2 ^ X.n 0 - 1 := X.card_Ki 0
  have hKi1 : Nat.card (X.Ki 1) = 2 ^ X.n 1 - 1 := X.card_Ki 1
  rw [hKcard, hKi0, hKi1]

theorem card_edge_of_Ki_inf (h : X.Ki 0 ⊓ X.Ki 1 = ⊥) :
    Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) =
      Nat.card X.S * ((2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1)) := by
  have hE : X.Gi 0 ⊓ X.Gi 1 = X.K ⊔ X.S := X.K_sup.symm
  have hKSdisj : Disjoint X.K X.S := disjoint_iff.mpr X.K_inf
  have hKS : Nat.card ↥(X.K ⊔ X.S) = Nat.card X.K * Nat.card X.S := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      X.S X.K X.K_le_normalizer_S hKSdisj.symm
    rw [sup_comm] at h
    rw [h, mul_comm]
  rw [hE, hKS, X.card_K_eq_of_Ki_inf_eq_bot h]
  ring

end Setup

end TypeZero

end CFSG.Quasithin.St84
