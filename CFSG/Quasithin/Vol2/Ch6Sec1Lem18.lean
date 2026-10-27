module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem17

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem V_le_pCoreOf_H (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    V ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (h.V_le_pCoreOf hH).trans ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left) (h.le_normalizer_pCoreOf hH)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem amalgamHypV (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    AmalgamHypV (L ⊔ T ⊔ H) (L ⊔ T) H T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := h.toHyp611.isUniqueM h432
  have hQ : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) :=
    h.toHyp611.centralizer_eq
  refine
    { gen := rfl
      charTwo := ?_
      sylow₁ := h.toHyp611.isSylowIn_T
      sylow₂ := h.isSylowTwoOf hH
      o2_trivial := ?_
      reduced := h.module.isTwoReducedIn
      cT := ?_ }
  · obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
    have hLT : InH (P : Subgroup G) (L ⊔ T) := by
      rw [hP]
      exact ⟨le_sup_right, h.maximal.1.2.2.2⟩
    exact CFSG.Quasithin.charTwo_of_inH h.qtke.2.1 P hLT
  · by_contra hne
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T ⊔ H)
    have hle := le_of_isUniqueM_of_le_twoLocal hU (le_sup_left.trans hN)
      ⟨_, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    exact hH.2.1 ((le_sup_right.trans hN).trans hle)
  ·
    apply le_antisymm
    · have hle : ch6Q T V ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
        inf_le_inf_right _ le_sup_right
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle ?_
        (h.sylow.1.to_le inf_le_left)
      rw [hQ]
      exact inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
    · rw [hQ]
      have hnorm : L ⊔ T ≤ Subgroup.normalizer
          (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
        intro x hx
        have h1 : x ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
          F7.normalizer_le_normalizer_centralizer V (h.toHyp611.sup_le_normalizer hx)
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp
          (Subgroup.le_normalizer hx) y, Subgroup.mem_normalizer_iff.mp h1 y]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
        (hnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

end Hyp6116

theorem stmt6_1_18 (h432 : Stmt4_3_2) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
      ∀ H : Subgroup G, IsInHS T M L V H → 1 < CosetGeom.critDist (L ⊔ T ⊔ H) (L ⊔ T) H V := by
  intro G _ _ T M L V n h H hH
  have := two_le_critDist_of_le_pCoreOf (h.amalgamHypV h432 hH) h.toHyp611.ne_bot
    (h.V_le_pCoreOf_H hH)
  omega

end CFSG.Quasithin.H13
