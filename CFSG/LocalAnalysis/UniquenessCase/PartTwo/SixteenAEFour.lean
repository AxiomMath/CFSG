module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEStabThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEStabSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16ae_aSet_eq_empty_of_symSum {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) {X L : Subgroup (MulAut T)} {p r k : ℕ} (hp : p = 3 ∨ p = 7)
    (hr : 1 < r) (hL : IsElemAbelianOfRank p r ↥L) (hLP : L ≤ pCoreOf p X)
    (hS : SymSumOfConj X (⊤ : Subgroup T) r (dParam p))
    (hge : 3 ≤ CFSG.Open.pRank p X) (hk : 2 ≤ k) : E3.aSet k X = ∅ := by
  classical
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  letI := hι
  have hY : ∀ i, Y i ≠ ⊥ := by
    intro i h
    have h0 := hrk i
    rw [h, rk_bot] at h0
    rcases hp with rfl | rfl
    · rw [s16c1610_dParam_three] at h0
      omega
    · rw [s16c1610_dParam_seven] at h0
      omega
  obtain ⟨-, -, -, -, -, hQ⟩ :=
    s16n9b_case4_kernel hT hp hr hL hLP hge hind hinj hsup hcard hrk hperm hsurj
  apply s16ae_aSet_eq_empty
  intro A hAX hA1 hAel
  by_cases hmove : ∃ a ∈ A, ∃ i, (Y i).map a.toMonoidHom ≠ Y i
  · obtain ⟨B, hBA, hq, hne⟩ := s16ae_exists_index_two_fix_ne_of_moved hT hind hY hAel
      (fun a ha i => hperm a (hAX ha) i) hmove
    exact ⟨B, hBA, by omega, hne⟩
  · have hstab : ∀ a ∈ A, ∀ i, (Y i).map a.toMonoidHom = Y i :=
      fun a ha i => by_contra fun h => hmove ⟨a, ha, i, h⟩
    rcases hp with rfl | rfl
    · have hrk2 : ∀ i, rk ↥(Y i) = 2 := fun i => (hrk i).trans s16c1610_dParam_three
      obtain ⟨B, hBA, hq, hne⟩ :=
        s16ae_exists_index_two_fix_ne_of_stab_three hT hsup hrk2 hAel hA1 hstab
      exact ⟨B, hBA, by omega, hne⟩
    · obtain ⟨Q, hQX, hQp, hQ1, hQn, hQY⟩ := hQ rfl
      have hrk3 : ∀ i, rk ↥(Y i) = 3 := fun i => (hrk i).trans s16c1610_dParam_seven
      have htrans : ∀ i j, ∃ g ∈ X, (Y i).map g.toMonoidHom = Y j := by
        intro i j
        obtain ⟨g, hg, hgY⟩ := hsurj (Equiv.swap i j)
        exact ⟨g, hg, by simpa using hgY i⟩
      exact absurd (s16ae_eq_bot_of_stab_seven hT hsup hrk3 htrans hQX hQp hQ1 hQn hQY hAX hAel
        hstab) hA1

theorem s16ae_calABar_eq_empty_of_case168_4With (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h4 : 3 < CFSG.Open.evenRank G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hm : 1 < mBar D.M ⊥ V hV) {r : ℕ}
    (hr : 1 < r) (h : Case168_4With D ⊥ V hV L r) :
    calABar (mBar D.M ⊥ V hV) D.M ⊥ V hV = ∅ := by
  obtain ⟨p, hp, h4At⟩ := h
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  exact s16ae_aSet_eq_empty_of_symSum (s15_Infra_vtil_sq_eq_one ⊥ V hV) hp hr h4At.1
    (s16n9b_case4_pcore D hV hc hpp hr h4At.1) h4At.2.1
    (s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 h4At.2.2) hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
