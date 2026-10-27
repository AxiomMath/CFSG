module

public import CFSG.Quasithin.Background.RonanH155Alt3
public import CFSG.Quasithin.Background.RonanH143NF
public import CFSG.Quasithin.Background.RonanH143QH

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk CFSG.QuasithinUnique.Setup.X1
  CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH154

@[expose] def g5A : Array ℕ :=
  #[0, 1, 7, 4, 6, 3, 5, 2, 8, 22, 20, 10, 12, 18, 16, 14, 21, 11, 9, 23, 17, 15, 13, 19]

@[expose] def g5I : Array ℕ :=
  #[0, 1, 7, 5, 3, 6, 4, 2, 8, 18, 11, 17, 12, 22, 15, 21, 14, 20, 13, 23, 10, 16, 9, 19]

@[expose] def g6A : Array ℕ :=
  #[0, 1, 5, 7, 2, 6, 4, 3, 8, 17, 11, 18, 20, 13, 23, 14, 21, 12, 22, 15, 9, 16, 10, 19]

@[expose] def g6I : Array ℕ :=
  #[0, 1, 4, 7, 6, 2, 5, 3, 8, 20, 22, 10, 17, 13, 15, 19, 21, 9, 11, 23, 12, 16, 18, 14]

theorem g5_ok : InvPairOK 24 g5A g5I = true ∧ autArrOK g5A g5I = true ∧ g5A[0]! = 0 ∧
    g5A[1]! = 1 ∧ ∀ s ∈ subprods (specials155.getD 5 []),
      ∃ u < 32, compA24 (compA24 g5A (arrP2 s)) g5I = nq2Arr u := by
  decide +kernel

theorem g6_ok : InvPairOK 24 g6A g6I = true ∧ autArrOK g6A g6I = true ∧ g6A[0]! = 0 ∧
    g6A[1]! = 1 ∧ ∀ s ∈ subprods (specials155.getD 6 []),
      ∃ u < 32, compA24 (compA24 g6A (arrP2 s)) g6I = nq2Arr u := by
  decide +kernel

theorem std155 (T₀ : Subgroup P24)
    (hT : T₀ ⊓ mog22plus = P2) : Concl155 Rc 0 1 Ostd Sstd Bstd T₀ := by
  intro A hA hE
  have hAP2 : A ≤ P2 := by
    rw [← hT]
    exact hA
  have hKH : KY mog22plus ((Ostd.erase 0).erase 1) = fixO := by
    rw [← Hstd_eq]
    exact KY_H_L2
  have hKQ : KY mog22plus (Sstd.erase Bstd) = NQ2 := by
    rw [Sstd_erase]
    exact KY_Q_L2
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := hE.1.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hcard : Nat.card A = 16 := by
    rw [hE.2]
    norm_num
  rcases E16_P2_cases A hAP2 hE with hKO | hNQ | ⟨l, hl, hAeq⟩
  ·
    left
    have hle : A ≤ fixO := fun x hx => hKO x hx
    have hAeq : A = fixO :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_fixO', hcard])
    rw [hKH, hAeq]
    exact ⟨rfl, alt1_KO⟩
  ·
    right
    left
    have hle : A ≤ KY mog22plus Qstd := by
      rw [KY_Q_L2]
      exact fun x hx => hNQ x hx
    have hc : Nat.card A * 2 = Nat.card (KY mog22plus Qstd) := by
      rw [KY_Q_L2, card_NQ2, hcard]
    obtain ⟨hxi, hrk⟩ := hyp3_std A hle hc
    rw [hKQ]
    exact ⟨⟨1, one_mem _, by
      rw [conjSubg_eq_self (one_mem A)]
      exact fun x hx => hNQ x hx⟩, hrk, hxi⟩
  ·
    obtain ⟨k, hk, hkl⟩ := List.mem_iff_getElem.1 hl
    have hlk : l = specials155.getD k [] := by
      rw [List.getD_eq_getElem _ _ hk]
      exact hkl.symm
    subst hlk
    have hk7 : k < 7 := hk
    interval_cases k
    ·
      right
      right
      left
      exact alt3_of_data alt3D15 alt3_ok_15 hAeq hcomm hcard
    · right
      right
      left
      exact alt3_of_data alt3D24 alt3_ok_24 hAeq hcomm hcard
    ·
      right
      right
      right
      rw [hKH]
      exact alt4_chain hAeq alt4_check2
    · right
      right
      right
      rw [hKH]
      exact alt4_chain hAeq alt4_check3
    · right
      right
      right
      rw [hKH]
      exact alt4_chain hAeq alt4_check4
    ·
      right
      left
      obtain ⟨hg, hrk, hxi⟩ := alt2b_chain hAeq alt2b_check5 g5A g5I (g5_ok.1) (g5_ok.2.1)
        (g5_ok.2.2.1) (g5_ok.2.2.2.1) g5_ok.2.2.2.2
      rw [hKQ]
      exact ⟨hg, hrk, hxi⟩
    · right
      left
      obtain ⟨hg, hrk, hxi⟩ := alt2b_chain hAeq alt2b_check6 g6A g6I (g6_ok.1) (g6_ok.2.1)
        (g6_ok.2.2.1) (g6_ok.2.2.2.1) g6_ok.2.2.2.2
      rw [hKQ]
      exact ⟨hg, hrk, hxi⟩

end CFSG.Quasithin.RonanH155
