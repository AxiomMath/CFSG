module

public import CFSG.Quasithin.Vol2.Ch11SecCB51Main
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
open CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem ffModule_structure_of_two (h51 : AsB51) (h1102 : Stmt11_0_2) (hKF : KindModuleFacts)
    {T L I : Subgroup G} {n : ℕ} (hyp : Hyp11 G T L I n) (hJ : L = ⁅L, thompsonJ T⁆)
    {Y W : Subgroup G} (hLY : L ⊔ T ≤ Y) (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hW : IsTwoReducedIn Y W) (hVW : fsuV T I ≤ W) (hWL : ⁅W, L⁆ ≠ ⊥)
    (hY2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (W : Set G)) :
    ∃ _ : IsMulCommutative ↥⁅W, L⁆,
      (KindSL3 L (fsuV T I) n ∧ BinaryNaturalSL (V := ↥⁅W, L⁆) (autOn L ⁅W, L⁆) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅W, L⁆) 3 n) ∨
      (KindSp4 L (fsuV T I) n ∧ BinaryNaturalSp4 (V := ↥⁅W, L⁆) (autOn L ⁅W, L⁆) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅W, L⁆) n) ∨
      (KindG2 L (fsuV T I) n ∧ G2Natural (V := ↥⁅W, L⁆) (autOn L ⁅W, L⁆) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅W, L⁆) n) ∨
      (KindSL3 L (fsuV T I) n ∧ ⁅W, L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        SumTwoNatural L ⁅W, L⁆ n) := by
  have h : B51.BridgeHyp T L I n Y W := ⟨hyp, hLY, hYL, hW, hVW, hWL⟩
  have hc : IsMulCommutative ↥W := h.isElemAbelian.1
  exact B51.ffModule_structure_of_b51Hyp h51 h1102 hKF h (h.b51Hyp_of_two h1102 hJ hY2) rfl

theorem fsuV_eq_VM_or (h51 : AsB51) (h56 : AsB56) (h1102 : Stmt11_0_2)
    (hKF : KindModuleFacts) (h322 : Ch10.TmpL6_3_2_2_two) {T L I : Subgroup G} {n : ℕ}
    (hyp : Hyp11 G T L I n) (hJ : L = ⁅L, thompsonJ T⁆) :
    fsuV T I = VM T L I ∨
      (KindSL3 L (fsuV T I) n ∧ cVM T L I = ⊥ ∧ SumTwoNatural L (VM T L I) n) := by
  have hVM := h322 G T L I hyp.fsu
  rw [SecA.fsuVM_eq hyp, SecA.fsuM_eq hyp] at hVM
  have hW : IsTwoReducedIn (Subgroup.normalizer (L : Set G)) (VM T L I) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 hVM
  have hLY : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hyp.normal
  have hVW : fsuV T I ≤ VM T L I := le_conjClosure _ _
  have hWL := B51.commutator_VM_eq hyp
  have hV1 := B51.fsuV_ne_bot h1102 hKF.2.2.2 hyp
  have hW1 : VM T L I ≠ ⊥ := fun h0 => hV1 (le_bot_iff.mp (h0 ▸ hVW))
  have h : B51.BridgeHyp T L I n (Subgroup.normalizer (L : Set G)) (VM T L I) :=
    ⟨hyp, hLY, le_rfl, hW, hVW, by rw [hWL]; exact hW1⟩
  have hc : IsMulCommutative ↥(VM T L I) := h.isElemAbelian.1
  have hB := h.b51Hyp_of_b56 h56 h1102 hJ hWL
  have hW2 : ∀ w : ↥(VM T L I), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simpa using h.isElemAbelian.2 w w.2)
  obtain ⟨-, hcases⟩ := (h51 ↥(VM T L I) hW2 _ _ hB).1
  rcases hcases with hi | hii | ⟨m, hiii⟩ | hiv
  · exact Or.inl (h.eq_of_case1i h1102 hKF.2.2.2 hi hWL)
  · exact Or.inr (B51.sumTwoNatural_of_case1ii h1102 hKF h hii hWL)
  · exact (B51.not_case1iii h1102 hKF.2.2.2 h hiii).elim
  · exact (B51.not_case1iv h1102 hKF.2.2.2 h hiv).elim

end CFSG.Quasithin.Vol2.Ch11.SecC
