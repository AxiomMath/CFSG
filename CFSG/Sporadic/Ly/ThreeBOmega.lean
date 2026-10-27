module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAbstract
public import CFSG.RankThree.PartOne.KS.LyFiveGeneric

public section

namespace CFSG.Sporadic.Ly.Omega

variable {G X : Type*} [Group G] [Finite G] [MulAction G X]

theorem card_centralizer_le_fix_mul (p : X) (H : Subgroup G)
    (hH : MulAction.stabilizer G p = H) {y : G} (hyH : y ∈ H) (F : Finset X)
    (hF : ∀ x : X, y • x = x → x ∈ F) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) ≤
      F.card * Nat.card (Subgroup.centralizer ({(⟨y, hyH⟩ : H)} : Set H)) := by
  have hp : y • p = p := by
    rw [← MulAction.mem_stabilizer_iff, hH]
    exact hyH
  have h := CFSG.ClassicalInvolution.card_centralizer_le_of_fixed y p hp F hF
  rwa [hH, CFSG.RankThree.PartOne.card_centralizer_inf_eq H y hyH] at h

theorem exists_threeB_element_of (p : X) (H : Subgroup G) (hH : MulAction.stabilizer G p = H)
    {y : G} (hyH : y ∈ H) (hy : orderOf y = 3) (F : Finset X)
    (hF : ∀ x : X, y • x = x → x ∈ F) (hFc : F.card ≤ 243)
    (hC : Nat.card (Subgroup.centralizer ({(⟨y, hyH⟩ : H)} : Set H)) ≤ 720) :
    ∃ y : G, orderOf y = 3 ∧ Nat.card ↥(Subgroup.centralizer ({y} : Set G)) ≤ 174960 :=
  ⟨y, hy, (card_centralizer_le_fix_mul p H hH hyH F hF).trans
    ((Nat.mul_le_mul hFc hC).trans (by norm_num))⟩

end CFSG.Sporadic.Ly.Omega
