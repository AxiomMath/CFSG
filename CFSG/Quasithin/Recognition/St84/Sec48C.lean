module

public import CFSG.Quasithin.Recognition.St84.Sec48B

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement Matrix

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

variable {r d : ℕ}

variable {X}

namespace Comm48

private theorem Qg_le_S_and_sup (C : X.Comm48 s r d) :
    X.Qg r ≤ X.S ∧ X.Qg r ⊔ X.Q 0 = X.S := by
  obtain ⟨-, -, hZbQg, -⟩ := X.s48_2 C
  have h := (X.Z_succ_sup_Q_zero_and_inf C).1
  rw [hZbQg, X.edgeSylow_zero] at h
  exact ⟨le_sup_left.trans h.le, h⟩

private theorem d_eq_five (C : X.Comm48 s r d) (h12 : r = 12) : d = 5 := by
  have := (X.s48_2 C).2.1
  omega

private theorem hasB_zero_six (C : X.Comm48 s r d) (h12 : r = 12) : X.HasB 0 6 := by
  simpa [d_eq_five C h12] using (X.s48_2 C).1

private theorem hasB_one_five (C : X.Comm48 s r d) (h12 : r = 12) : X.HasB 1 5 := by
  simpa [d_eq_five C h12] using C.hasB

private theorem Z_zero_le_centralizer_Z_six (C : X.Comm48 s r d) (h12 : r = 12) :
    X.Z 0 ≤ Subgroup.centralizer (X.Z 6 : Set G) := by
  have hB6 : X.HasB 6 6 :=
    (X.hasB_iff_of_even (i := 6) (j := 0) (by norm_num) 6).mpr
      (hasB_zero_six C h12)
  have hZ6G0 : X.Z 6 ≤ X.Gi 0 := hB6.Z_le_Gi (by omega)
  have hZ6L0 : X.Z 6 ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (X.Gi 6)).to_le (X.Z_le_Q 6)) hZ6G0
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hz0 : z ∈ centerOf (X.L 0) := by
    rw [← (X.s48_0 C).2]
    exact hz
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz0).2 w (hZ6L0 hw)

private theorem Z_two_le_centralizer_Z_seven (C : X.Comm48 s r d) (h12 : r = 12) :
    X.Z 2 ≤ Subgroup.centralizer (X.Z 7 : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hB2 : X.HasB 2 6 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) 6).mpr
      (hasB_zero_six C h12)
  have hzQ7 : z ∈ X.Q 7 := X.Z_le_Q_of_lt hB2 (by norm_num) hz
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 7 hw)).2
    z hzQ7).symm

private theorem Z_six_le_centralizer_Z_four (C : X.Comm48 s r d) (h12 : r = 12) :
    X.Z 6 ≤ Subgroup.centralizer (X.Z 4 : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hB6 : X.HasB 6 6 :=
    (X.hasB_iff_of_even (i := 6) (j := 0) (by norm_num) 6).mpr
      (hasB_zero_six C h12)
  have hzQ4 : z ∈ X.Q 4 := X.Z_le_Q_of_lt hB6 (by norm_num) hz
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 4 hw)).2
    z hzQ4).symm

private theorem Vk_four_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 4 = X.Z 3 ⊔ X.Z 5 := by
  obtain ⟨hVk, -, -, -, -, -, -⟩ := X.s48_8 C hH
  have h := X.Vk_add 2 0
  rw [show (0 : ℤ) + 2 * 2 = 4 by norm_num] at h
  rw [h, hVk, conjSub_sup, ← X.Z_add 2 1, ← X.Z_add 2 (-1)]
  rw [sup_comm]
  norm_num

private theorem Vk_zero_le_Gi (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) :
    ∀ j : ℤ, -4 ≤ j → j ≤ 4 → X.Vk 0 ≤ X.Gi j := by
  obtain ⟨hVk, -, -, -, -, -, -⟩ := X.s48_8 C hH
  have hB1 := hasB_one_five C h12
  have hBm1 : X.HasB (-1) 5 :=
    (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) 5).mpr hB1
  intro j hj1 hj2
  rw [hVk]
  refine sup_le ?_ ?_
  · exact hB1.Z_le_Gi (by omega)
  · exact hBm1.Z_le_Gi (by omega)

private theorem Vk_four_le_Gi (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) :
    ∀ j : ℤ, 0 ≤ j → j ≤ 8 → X.Vk 4 ≤ X.Gi j := by
  have hB1 := hasB_one_five C h12
  have hB3 : X.HasB 3 5 :=
    (X.hasB_iff_of_even (i := 3) (j := 1) (by norm_num) 5).mpr hB1
  have hB5 : X.HasB 5 5 :=
    (X.hasB_iff_of_even (i := 5) (j := 1) (by norm_num) 5).mpr hB1
  intro j hj1 hj2
  rw [Vk_four_eq C hH]
  refine sup_le ?_ ?_
  · exact hB3.Z_le_Gi (by omega)
  · exact hB5.Z_le_Gi (by omega)

private theorem R48_eq_commutator (C : X.Comm48 s r d) (h12 : r = 12) :
    X.R48 d = ⁅X.Z (-1), X.Z 6⁆ := by
  rw [Setup.R48, d_eq_five C h12]
  norm_num

private theorem R48_le_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) : X.R48 d ≤ X.Vk 0 := by
  obtain ⟨-, -, -, -, -, -, hRZ1⟩ := X.s48_8 C hH
  have hZVk0 : X.Z 1 ≤ X.Vk 0 := by
    have h := le_iSup₂_of_le (f := fun g (_ : g ∈ X.L 0) => conjSub g (X.Z (0 + 1)))
      (1 : G) (X.L 0).one_mem (le_refl (conjSub (1 : G) (X.Z (0 + 1))))
    simpa [Setup.Vk, conjSub_one, show (0:ℤ) + 1 = 1 by norm_num] using h
  rw [R48_eq_commutator C h12] at hRZ1 ⊢
  exact hRZ1.trans hZVk0

private theorem R48_le_Vk_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) : X.R48 d ≤ X.Vk 4 := by
  have hB1 := hasB_one_five C h12
  have hBm1 : X.HasB (-1) 5 :=
    (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) 5).mpr hB1
  have hZ5 : X.Z 5 = X.Z 4 ⊔ X.Z 6 := by
    simpa using X.Z_eq_sup_of_odd C hH (j := 5) (by norm_num)
  have hZ6V4 : X.Z 6 ≤ X.Vk 4 := by
    rw [Vk_four_eq C hH, hZ5]
    exact le_sup_right.trans le_sup_right
  have hZmG4 : X.Z (-1) ≤ X.Gi 4 := hBm1.Z_le_Gi (by omega)
  have hZmP : IsPGroup 2 (X.Z (-1)) :=
    (pCoreOf_isPGroup' (X.Gi (-1))).to_le (X.Z_le_Q (-1))
  have hZmL4 : X.Z (-1) ≤ X.L 4 :=
    le_oTwoPrime_of_isPGroup hZmP hZmG4
  rw [R48_eq_commutator C h12]
  exact (Subgroup.commutator_mono hZmL4 hZ6V4).trans
    (Subgroup.le_normalizer_iff_commutator_le_right.mp (X.L_le_normalizer_Vk 4))

private theorem R48_le_arcStab (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) :
    X.R48 d ≤ X.arcStab (-4) 8 := by
  rw [X.arcStab_eq_inf (by norm_num)]
  exact le_inf
    ((R48_le_Vk_zero C hH h12).trans (Vk_zero_le_Gi C hH h12 (-4) (by norm_num) (by norm_num)))
    ((R48_le_Vk_four C hH h12).trans (Vk_four_le_Gi C hH h12 8 (by norm_num) le_rfl))

private theorem R48_eq_Z_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) : X.R48 d = X.Z 2 := by
  have hZ0pc : X.Z 0 = pCoreOf 2 (X.arcStab (-6) 6) :=
    by simpa [d_eq_five C h12] using (X.s48_2 C).2.2.2.1
  have hKR : X.K ≤ Subgroup.normalizer (X.R48 d : Set G) := by
    intro k hk
    rw [mem_normalizer_iff_conjSub]
    rw [R48_eq_commutator C h12, ← conjSub_commutator,
      X.Z_normal (-1) k (X.K_le_Gi (-1) hk), X.Z_normal 6 k (X.K_le_Gi 6 hk)]
  have hRne : X.R48 d ≠ ⊥ := (X.s48_9 C hH).1
  obtain ⟨-, -, -, -, -, -, hRZ1⟩ := X.s48_8 C hH
  have hR2 : IsPGroup 2 (X.R48 d) :=
    ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)).to_le hRZ1
  have hpR : X.R48 d = pCoreOf 2 (X.arcStab (-4) 8) := by
    have harc' : X.R48 d ≤ X.arcStab (-4) ((-4 : ℤ) + (r : ℤ)) := by
      simpa [show (-4 : ℤ) + (r : ℤ) = 8 by omega] using R48_le_arcStab C hH h12
    have hp' : X.R48 d ≤ pCoreOf 2 (X.arcStab (-4) ((-4 : ℤ) + (r : ℤ))) :=
      X.le_pCoreOf_arcStab_r C.hyp hR2 harc'
    have h := X.eq_of_le_pCoreOf_arcStab_r C.hyp (U := X.R48 d) (a := -4) hKR hRne hp'
    rwa [show (-4 : ℤ) + (r : ℤ) = 8 by omega] at h
  have hpZ : pCoreOf 2 (X.arcStab (-4) 8) = X.Z 2 := by
    have h := X.arcStab_add 1 (-6) 6
    rw [show (-6 : ℤ) + 2 * 1 = -4 by norm_num,
      show (6 : ℤ) + 2 * 1 = 8 by norm_num] at h
    rw [h, pCoreOf_conjSub, ← hZ0pc, ← X.Z_add 1 0]
    norm_num
  exact hpR.trans hpZ

private theorem commutator_Z_neg_one_Z_five
    (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) :
    ⁅X.Z (-1), X.Z 5⁆ = X.Z 2 := by
  have hZ5 : X.Z 5 = X.Z 4 ⊔ X.Z 6 := by
    simpa using X.Z_eq_sup_of_odd C hH (j := 5) (by norm_num)
  have hR48 : X.R48 d = ⁅X.Z (-1), X.Z 6⁆ := by
    rw [Setup.R48, d_eq_five C h12]
    norm_num
  have hB4 : X.HasB 4 6 :=
    (X.hasB_iff_of_even (i := 4) (j := 0) (by norm_num) 6).mpr
      (hasB_zero_six C h12)
  have hZ6Z4 : X.Z 6 ≤ Subgroup.normalizer (X.Z 4 : Set G) :=
    (Z_six_le_centralizer_Z_four C h12).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZ4Zm : ⁅X.Z 4, X.Z (-1)⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr ?_
    intro z hz w hw
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hzQ : z ∈ X.Q (-1) := X.Z_le_Q_of_lt hB4 (by norm_num) hz
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center (-1) hw)).2 z hzQ

  rw [hZ5, sup_comm (X.Z 4) (X.Z 6),
    CFSG.LocalAnalysis.SteinbergBV.ConstantRank.commutator_sup_eq_of_centralizer
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZ4Zm) hZ6Z4, ← hR48]
  exact R48_eq_Z_two C hH h12

private theorem commutator_Z_add_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {j : ℤ} (hj : Odd j) :
    ⁅X.Z j, X.Z (j + 6)⁆ = X.Z (j + 3) := by
  have hbase := commutator_Z_neg_one_Z_five C hH h12
  obtain ⟨m, hm⟩ := Int.even_or_odd' j
  rcases hm with hjeven | hjodd
  · exact absurd hj (by rw [hjeven]; exact Int.not_odd_iff_even.mpr ⟨m, by ring⟩)
  · set k : ℤ := m + 1 with hk
    have hZj : X.Z j = conjSub (X.τ ^ k) (X.Z (-1)) := by
      rw [show j = -1 + 2 * k by omega, X.Z_add]
    have hZj6 : X.Z (j + 6) = conjSub (X.τ ^ k) (X.Z 5) := by
      rw [show j + 6 = 5 + 2 * k by omega, X.Z_add]
    have hZj3 : X.Z (j + 3) = conjSub (X.τ ^ k) (X.Z 2) := by
      rw [show j + 3 = 2 + 2 * k by omega, X.Z_add]
    rw [hZj, hZj6, hZj3, conjSub_commutator (X.τ ^ k) (X.Z (-1)) (X.Z 5), hbase]

private theorem Vk_six_eq : X.Vk 6 = conjSub (X.τ ^ (3 : ℤ)) (X.Vk 0) := by
  have h := X.Vk_add 3 0
  rw [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at h
  exact h

private theorem Vk_six_eq_sup (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 6 = X.Z 5 ⊔ X.Z 7 := by
  rw [Vk_six_eq]
  obtain ⟨hVk0, -, -, -, -, -, -⟩ := X.s48_8 C hH
  rw [hVk0, conjSub_sup, ← X.Z_add 3 1, ← X.Z_add 3 (-1)]
  rw [show (1 : ℤ) + 2 * 3 = 7 by norm_num,
    show (-1 : ℤ) + 2 * 3 = 5 by norm_num, sup_comm]

private theorem Vk_six_le_Q_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) : X.Vk 6 ≤ X.Q 6 := by
  have hB1 := hasB_one_five C h12
  have hB5 : X.HasB 5 5 :=
    (X.hasB_iff_of_even (i := 5) (j := 1) (by norm_num) 5).mpr hB1
  have hB7 : X.HasB 7 5 :=
    (X.hasB_iff_of_even (i := 7) (j := 1) (by norm_num) 5).mpr hB1
  rw [Vk_six_eq_sup C hH]
  exact sup_le (X.Z_le_Q_of_lt hB5 (by norm_num))
    (X.Z_le_Q_of_lt hB7 (by norm_num))

private theorem NatQuot_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    NatQuot (X.L 6) (X.Vk 6) (X.Z 6) (X.n 6) := by
  obtain ⟨-, -, -, -, -, hNat, -⟩ := X.s48_8 C hH
  have h := NatQuot.conj hNat (X.τ ^ (3 : ℤ))
  have hL : X.L 6 = conjSub (X.τ ^ (3 : ℤ)) (X.L 0) := by
    have := X.L_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this
  have hZ : X.Z 6 = conjSub (X.τ ^ (3 : ℤ)) (X.Z 0) := by
    have := X.Z_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this
  have hn : X.n 6 = X.n 0 := by
    have := X.n_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this
  rw [hn, hL, Vk_six_eq, hZ]
  exact h

private theorem isElemAbelian_Vk_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : IsElemAbelian 2 (X.Vk 6) := by
  obtain ⟨-, -, hEl, -, -, -, -⟩ := X.s48_8 C hH
  have h := F7.isElemAbelian_conjSub (p := 2) (g := X.τ ^ (3 : ℤ)) (X := X.Vk 0) hEl
  rwa [← Vk_six_eq] at h

private theorem commutator_Vk_Q_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ⁅X.Vk 6, X.Q 6⁆ = X.Z 6 := by
  obtain ⟨-, -, -, -, hComm, -, -⟩ := X.s48_8 C hH
  have h := congrArg (conjSub (X.τ ^ (3 : ℤ))) hComm
  rw [← conjSub_commutator, ← Vk_six_eq] at h
  have hQ : X.Q 6 = conjSub (X.τ ^ (3 : ℤ)) (X.Q 0) := by
    have := X.Q_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this
  have hZ : X.Z 6 = conjSub (X.τ ^ (3 : ℤ)) (X.Z 0) := by
    have := X.Z_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this
  rw [← hQ, ← hZ] at h
  exact h

private theorem pCoreOf_L_six : pCoreOf 2 (X.L 6) = X.Q 6 :=
  (X.hyp.isLocL2_oTwoPrime (X.vert 6)).pCoreOf_eq
private theorem Z_one_eq_sup_Z_zero_Z_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 1 = X.Z 0 ⊔ X.Z 2 ∧ IsElemAbelian 2 (X.Z 1) := by
  obtain ⟨-, hZ1sup, -, -, hZ1el, -⟩ := X.s48_4' C hH
  exact ⟨hZ1sup, hZ1el⟩

private theorem Z_two_le_centralizer_Z_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 2 ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
  obtain ⟨hZ1sup, hZ1el⟩ := Z_one_eq_sup_Z_zero_Z_two C hH
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hz1 : z ∈ X.Z 1 := by
    rw [hZ1sup]
    exact (le_sup_right : X.Z 2 ≤ X.Z 0 ⊔ X.Z 2) hz
  have hw1 : w ∈ X.Z 1 := by
    rw [hZ1sup]
    exact (le_sup_left : X.Z 0 ≤ X.Z 0 ⊔ X.Z 2) hw
  exact (CFSG.Open.IsElemAbelian.comm hZ1el hz1 hw1).symm

private theorem Z_seven_eq_sup_Z_six_Z_eight (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 7 = X.Z 6 ⊔ X.Z 8 := by
  simpa using X.Z_eq_sup_of_odd C hH (j := 7) (by norm_num)

private theorem isElemAbelian_Z_seven (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : IsElemAbelian 2 (X.Z 7) := by
  obtain ⟨-, -, -, -, hZ1el, -⟩ := X.s48_4' C hH
  have h := F7.isElemAbelian_conjSub (p := 2) (g := X.τ ^ (3 : ℤ)) (X := X.Z 1) hZ1el
  have hZ71 : X.Z 7 = conjSub (X.τ ^ (3 : ℤ)) (X.Z 1) := by
    have := X.Z_add 3 1
    rwa [show (1 : ℤ) + 2 * 3 = 7 by norm_num] at this
  rwa [← hZ71] at h

private theorem Z_eight_le_centralizer_Z_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 8 ≤ Subgroup.centralizer (X.Z 6 : Set G) := by
  have hZ7sup := Z_seven_eq_sup_Z_six_Z_eight C hH
  have hZ7el := isElemAbelian_Z_seven C hH
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hz7 : z ∈ X.Z 7 := by
    rw [hZ7sup]
    exact (le_sup_right : X.Z 8 ≤ X.Z 6 ⊔ X.Z 8) hz
  have hw7 : w ∈ X.Z 7 := by
    rw [hZ7sup]
    exact (le_sup_left : X.Z 6 ≤ X.Z 6 ⊔ X.Z 8) hw
  exact (CFSG.Open.IsElemAbelian.comm hZ7el hz7 hw7).symm

private theorem exists_decomp_Z_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {x : G} (hx : x ∈ X.Z 1) (hx2 : x ∉ X.Z 2) :
    ∃ x0 ∈ X.Z 0, ∃ x2 ∈ X.Z 2, x = x0 * x2 ∧ x0 ≠ 1 := by
  obtain ⟨hZ1sup, -⟩ := Z_one_eq_sup_Z_zero_Z_two C hH
  have hZ2cent := Z_two_le_centralizer_Z_zero C hH
  obtain ⟨x0, hx0, x2, hx2', hxeq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (hZ2cent.trans (Subgroup.centralizer_le_normalizer _))).mp
      (by rw [← hZ1sup]; exact hx)
  refine ⟨x0, hx0, x2, hx2', hxeq, ?_⟩
  intro h1
  apply hx2
  rw [hxeq, h1, one_mul]
  exact hx2'

private theorem exists_decomp_Z_seven (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {y : G} (hy : y ∈ X.Z 7) (hy6 : y ∉ X.Z 6) :
    ∃ y6 ∈ X.Z 6, ∃ y8 ∈ X.Z 8, y = y6 * y8 ∧ y8 ≠ 1 := by
  have hZ7sup := Z_seven_eq_sup_Z_six_Z_eight C hH
  have hZ8cent := Z_eight_le_centralizer_Z_six C hH
  obtain ⟨y6, hy6', y8, hy8, hyeq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (hZ8cent.trans (Subgroup.centralizer_le_normalizer _))).mp
      (by rw [← hZ7sup]; exact hy)
  refine ⟨y6, hy6', y8, hy8, hyeq, ?_⟩
  intro h1
  apply hy6
  rw [hyeq, h1, mul_one]
  exact hy6'

private theorem commutator_eq_Z_zero_Z_eight_of_decomp (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {x x0 x2 y y6 y8 : G}
    (hxeq : x = x0 * x2) (hyeq : y = y6 * y8) (hx0 : x0 ∈ X.Z 0)
    (hx2 : x2 ∈ X.Z 2) (hy : y ∈ X.Z 7) (hy6 : y6 ∈ X.Z 6) (hy8 : y8 ∈ X.Z 8) :
    ⁅x, y⁆ = ⁅x0, y8⁆ := by
  have hZ1sup := (Z_one_eq_sup_Z_zero_Z_two C hH).1
  have hZ7sup := Z_seven_eq_sup_Z_six_Z_eight C hH
  have hZ0Z6 := Z_zero_le_centralizer_Z_six C h12
  have hZ2Z7 := Z_two_le_centralizer_Z_seven C h12
  have hx2y : ⁅x2, y⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hZ2Z7 hx2) y hy).symm
  have hx0y6 : ⁅x0, y6⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hZ0Z6 hx0) y6 hy6).symm
  have hx0y8in4 : ⁅x0, y8⁆ ∈ X.Z 4 := by
    have h : ⁅X.Z 1, X.Z 7⁆ = X.Z 4 := by
      simpa using commutator_Z_add_six C hH h12 (j := 1) (by norm_num)
    rw [← h]
    exact Subgroup.commutator_mem_commutator
      (by rw [hZ1sup]; exact (le_sup_left : X.Z 0 ≤ X.Z 0 ⊔ X.Z 2) hx0)
      (by rw [hZ7sup]; exact (le_sup_right : X.Z 8 ≤ X.Z 6 ⊔ X.Z 8) hy8)
  have hZ6Z4 := Z_six_le_centralizer_Z_four C h12
  calc ⁅x, y⁆ = ⁅x0 * x2, y⁆ := by rw [hxeq]
    _ = ⁅x0, y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hx2y]
      simp
    _ = ⁅x0, y6 * y8⁆ := by rw [hyeq]
    _ = ⁅x0, y8⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hx0y6, one_mul]
      have hcent := Subgroup.mem_centralizer_iff.mp (hZ6Z4 hy6) ⁅x0, y8⁆ hx0y8in4
      rw [← hcent]
      group

private theorem exists_commutator_eq_Z_zero_Z_eight
    (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {x y : G}
    (hx : x ∈ X.Z 1) (hx2 : x ∉ X.Z 2) (hy : y ∈ X.Z 7) (hy6 : y ∉ X.Z 6) :
    ∃ x0 ∈ X.Z 0, x0 ≠ 1 ∧ ∃ y8 ∈ X.Z 8, y8 ≠ 1 ∧ ⁅x, y⁆ = ⁅x0, y8⁆ := by
  obtain ⟨x0, hx0, x2, hx2', hxeq, hx0ne⟩ := exists_decomp_Z_one C hH hx hx2
  obtain ⟨y6, hy6', y8, hy8, hyeq, hy8ne⟩ := exists_decomp_Z_seven C hH hy hy6
  exact ⟨x0, hx0, hx0ne, y8, hy8, hy8ne,
    commutator_eq_Z_zero_Z_eight_of_decomp C hH h12 hxeq hyeq hx0 hx2' hy hy6' hy8⟩

private theorem mem_L_six_and_notMem_Q_six (C : X.Comm48 s r d) (h12 : r = 12) {x0 : G}
    (hx0 : x0 ∈ X.Z 0) (hx0ne : x0 ≠ 1) : x0 ∈ X.L 6 ∧ x0 ∉ X.Q 6 := by
  have hd := d_eq_five C h12
  have hB0 := hasB_zero_six C h12
  have hx0G6 : x0 ∈ X.Gi 6 := hB0.1 6 (by norm_num) hx0
  have hx0L6 : x0 ∈ X.L 6 := by
    have hx0P : IsPGroup 2 (Subgroup.zpowers x0) :=
      ((pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)).to_le
        (Subgroup.zpowers_le.mpr hx0)
    exact le_oTwoPrime_of_isPGroup hx0P (Subgroup.zpowers_le.mpr hx0G6)
      (Subgroup.mem_zpowers x0)
  have hx0notQ6 : x0 ∉ X.Q 6 := by
    intro hmem
    have hbot : x0 ∈ X.Z 0 ⊓ X.Q 6 := Subgroup.mem_inf.mpr ⟨hx0, hmem⟩
    have hbot' := (X.s48_2 C).2.2.2.2.2.2.1
    rw [show (d : ℤ) + 1 = 6 by omega] at hbot'
    rw [hbot'] at hbot
    exact hx0ne (Subgroup.mem_bot.mp hbot)

  exact ⟨hx0L6, hx0notQ6⟩

private theorem eq_bot_of_fixes_arc (C : X.Comm48 s r d)
    {U : Subgroup G} (hU : IsPGroup 2 U) {a : ℤ} {k : ℕ}
    (hfix : U ≤ X.arcStab a (a + k)) (hk : r < k) : U = ⊥ := by
  by_contra hne
  have := X.le_r_of_fixes C.hyp (a := a) (k := k) hU hne hfix
  omega

private theorem Z_four_inf_Z_six (C : X.Comm48 s r d) (h12 : r = 12) :
    X.Z 4 ⊓ X.Z 6 = ⊥ := by
  have hB4 := (X.hasB_iff_of_even (i := 4) (j := 0) (by norm_num) 6).mpr
    (hasB_zero_six C h12)
  have hB6 := (X.hasB_iff_of_even (i := 6) (j := 0) (by norm_num) 6).mpr
    (hasB_zero_six C h12)
  have hZ46bot : X.Z 4 ⊓ X.Z 6 = ⊥ := by
    have hU2 : IsPGroup 2 ↥(X.Z 4 ⊓ X.Z 6) :=
      ((pCoreOf_isPGroup' (X.Gi 4)).to_le (X.Z_le_Q 4)).to_le inf_le_left
    have hfix : X.Z 4 ⊓ X.Z 6 ≤ X.arcStab (-2 : ℤ) ((-2 : ℤ) + 14) := by
      rw [show (-2 : ℤ) + 14 = 12 by norm_num, X.arcStab_eq_inf (by norm_num)]
      refine le_inf ?_ ?_
      · refine inf_le_left.trans ?_
        exact hB4.Z_le_Gi (by omega)
      · refine inf_le_right.trans ?_
        exact hB6.Z_le_Gi (by omega)
    exact eq_bot_of_fixes_arc C hU2 hfix (by rw [h12]; norm_num)
  exact hZ46bot

private theorem not_fixes_seven_of_mem_Z_zero (C : X.Comm48 s r d) (h12 : r = 12) {z : G}
    (hz0 : z ∈ X.Z 0) (hz1 : z ≠ 1) : z • X.vert 7 ≠ X.vert 7 := by
  have hB0 := hasB_zero_six C h12
  have hZ0P : IsPGroup 2 (X.Z 0) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
  have hz_not7 : z • X.vert 7 ≠ X.vert 7 := by
    intro hz7
    have hU2 : IsPGroup 2 (Subgroup.zpowers z) :=
      hZ0P.to_le (Subgroup.zpowers_le.mpr hz0)
    have hfix : Subgroup.zpowers z ≤ X.arcStab (-6) ((-6 : ℤ) + 13) := by
      rw [Subgroup.zpowers_le]
      rw [Setup.arcStab, Fan86.mem_fixSet]
      rintro v ⟨k, hk, rfl⟩
      rw [Set.mem_Icc] at hk
      by_cases hk6 : k ≤ 6
      · exact MulAction.mem_stabilizer_iff.mp (by simpa using hB0.1 k (by omega) hz0)
      · have hk7 : k = 7 := by omega
        subst k
        exact hz7
    have hbot := eq_bot_of_fixes_arc C hU2 hfix (by omega : r < 13)
    have hzmem : z ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers z
    exact hz1 (Subgroup.mem_bot.mp hzmem)
  exact hz_not7

private theorem L_six_not_isPGroup (C : X.Comm48 s r d) :
    ¬ IsPGroup 2 ↥(X.L 6) := by
  intro hL
  haveI : Finite ↥(X.L 6) := finite_of_le_stabilizer X.hyp (H := X.L 6) (X.L_le_Gi 6)
  have htop : CFSG.pCore 2 ↥(X.L 6) = ⊤ := by
    refine le_antisymm le_top ?_
    exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup Subgroup.normal_top (hL.to_subgroup (⊤ : Subgroup ↥(X.L 6)))
  have h1 : Nat.card (oTwoQuot ↥(X.L 6)) = 1 := by
    haveI : Subsingleton (↥(X.L 6) ⧸ ⊤) := QuotientGroup.subsingleton_quotient_top
    show Nat.card (↥(X.L 6) ⧸ CFSG.pCore 2 ↥(X.L 6)) = 1
    rw [htop]
    exact Nat.card_of_subsingleton (1 : ↥(X.L 6) ⧸ ⊤)
  have hquot := (X.hyp.isLocL2_oTwoPrime (X.vert 6)).quot
  have hcard := IsL2Quot.card (f := X.n 6) (by have := C.hyp.two_le_n 6; omega) hquot
  rw [h1] at hcard
  have h2 : 2 ≤ 2 ^ X.n 6 := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ X.n 6 := Nat.pow_le_pow_right (by norm_num) (by have := C.hyp.two_le_n 6; omega)
  have h4 : 16 ≤ 4 ^ X.n 6 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ X.n 6 := Nat.pow_le_pow_right (by norm_num) (C.hyp.two_le_n 6)
  have h3 : 2 ≤ 2 ^ X.n 6 * (4 ^ X.n 6 - 1) := by
    have h4' : 1 ≤ 4 ^ X.n 6 - 1 := by omega
    calc 2 = 2 * 1 := by norm_num
      _ ≤ 2 ^ X.n 6 * (4 ^ X.n 6 - 1) := Nat.mul_le_mul h2 h4'
  omega

private theorem commutator_conj_mem_Z_six_gen (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {b x t : G}
    (hbx : ⁅b, x⁆ ∈ X.Z 6) (hbt : ⁅b, t⁆ ∈ X.Z 6)
    (hxL : x ∈ X.L 6) (htL : t ∈ X.L 6) :
    ⁅b, x * t * x⁻¹⁆ ∈ X.Z 6 := by
  have hNat := NatQuot_six C hH
  have hZnorm : X.L 6 ≤ Subgroup.normalizer (X.Z 6 : Set G) := fun y hy =>
    (Subgroup.mem_inf.mp (hNat.normal hy)).2
  have hV6L : X.Vk 6 ≤ X.L 6 := hNat.E_le
  set z : G := x⁻¹ * ⁅b, x⁆ * x with hzdef
  have hz : z ∈ X.Z 6 := by
    rw [hzdef]
    simpa using (Subgroup.mem_normalizer_iff.mp (hZnorm ((X.L 6).inv_mem hxL)) ⁅b, x⁆).mp hbx
  have hzL : z ∈ X.L 6 := hV6L (hNat.Z_le hz)
  have h1 : x⁻¹ * b * x = z * b := by
    rw [hzdef, commutatorElement_def]
    group
  have h2 : ⁅x⁻¹ * b * x, t⁆ ∈ X.Z 6 := by
    rw [h1, commutatorElement_mul_left_eq_conj_mul]
    have hconj : z * ⁅b, t⁆ * z⁻¹ ∈ X.Z 6 :=
      (Subgroup.mem_normalizer_iff.mp (hZnorm hzL) ⁅b, t⁆).mp hbt
    have hzt : ⁅z, t⁆ ∈ X.Z 6 := by
      have htzt : t * z * t⁻¹ ∈ X.Z 6 :=
        (Subgroup.mem_normalizer_iff.mp (hZnorm htL) z).mp hz
      have hEq : ⁅z, t⁆ = z * (t * z * t⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [hEq]
      exact (X.Z 6).mul_mem hz ((X.Z 6).inv_mem htzt)
    exact (X.Z 6).mul_mem hconj hzt
  have h3 : x * ⁅x⁻¹ * b * x, t⁆ * x⁻¹ ∈ X.Z 6 :=
    (Subgroup.mem_normalizer_iff.mp (hZnorm hxL) ⁅x⁻¹ * b * x, t⁆).mp h2
  have hEq : x * ⁅x⁻¹ * b * x, t⁆ * x⁻¹ = ⁅b, x * t * x⁻¹⁆ := by
    have hcc := conjugate_commutatorElement (g₁ := x⁻¹ * b * x) (g₂ := t) (g₃ := x)
    have hb : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
    rwa [hb] at hcc
  rw [← hEq]
  exact h3

private theorem mem_edgeSylow_five_of_mem_Z_zero (C : X.Comm48 s r d) (h12 : r = 12)
    {x0 : G} (hx0 : x0 ∈ X.Z 0) : x0 ∈ X.edgeSylow 5 := by
  have hZ0Q5 : X.Z 0 ≤ X.Q 5 :=
    X.Z_le_Q_of_lt (hasB_zero_six C h12) (i := 0) (j := 5) (by norm_num)
  exact X.Q_le_edgeSylow_left 5 (hZ0Q5 hx0)

private theorem not_edgeSylow_five_le_edgeSylow_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) :
    ¬ X.edgeSylow 5 ≤ X.edgeSylow 6 ⊔ X.Vk 6 := by
  have hT5 : IsSylowTwoOf (X.edgeSylow 5) (X.L 6) := by
    simpa using X.isSylowTwoOf_edgeSylow_L_succ 5
  have hT6 : IsSylowTwoOf (X.edgeSylow 6) (X.L 6) := by
    simpa using X.isSylowTwoOf_edgeSylow_L 6
  haveI : Finite ↥(X.edgeSylow 6) :=
    finite_of_le_stabilizer X.hyp (H := X.edgeSylow 6) (hT6.1.trans (X.L_le_Gi 6))
  have hV6Q6 : X.Vk 6 ≤ X.Q 6 := Vk_six_le_Q_six C hH h12
  have hQ6T6 : X.Q 6 ≤ X.edgeSylow 6 := X.Q_le_edgeSylow_left 6
  rw [sup_eq_left.mpr (hV6Q6.trans hQ6T6)]
  intro hle
  have hEq : X.edgeSylow 6 = X.edgeSylow 5 :=
    CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le hT5 hT6.2.1 hT6.1 hle
  have hL : X.L 6 = X.edgeSylow 5 ⊔ X.edgeSylow 6 := (X.edgeSylow_sup_edgeSylow 6).symm
  have hEql : X.L 6 = X.edgeSylow 6 := by rw [hL, ← hEq, sup_idem]
  exact L_six_not_isPGroup C (hEql ▸ hT6.2.1)

private theorem not_mem_normalizer_edgeSylow_six_of_mem_Z_zero (C : X.Comm48 s r d)
    (h12 : r = 12) {x0 : G} (hx0 : x0 ∈ X.Z 0) (hx0ne : x0 ≠ 1) :
    x0 ∉ Subgroup.normalizer (X.edgeSylow 6 : Set G) := by
  obtain ⟨hx0L6, -⟩ := mem_L_six_and_notMem_Q_six C h12 hx0 hx0ne
  intro hx0N
  have hstab := (X.hyp.isLocL2_oTwoPrime (X.vert 6)).inf_stabilizer_eq_inf_normalizer_pointSylowN
    X.hyp.adj_smul (X.hyp.finite_stab (X.vert 6)) (X.hyp.valency (X.vert 6)).2
    (X.hyp.valency (X.vert 6)).1 (X.adj 6)
  have hmap : (Subgroup.map (oTwoPrime (MulAction.stabilizer G (X.vert 6))).subtype
      ((X.hyp.isLocL2_oTwoPrime (X.vert 6)).pointSylowN
        X.hyp.adj_smul (X.hyp.finite_stab (X.vert 6)) (X.hyp.valency (X.vert 6)).2
        (X.hyp.valency (X.vert 6)).1 (X.vert (6 + 1)) :
          Subgroup (oTwoPrime (MulAction.stabilizer G (X.vert 6))))) = X.edgeSylow 6 := by
    change vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert 6)) (X.vert (6 + 1)) =
      X.edgeSylow 6
    rw [← X.edgeSylow_eq_vertexSylow 6]
  rw [hmap] at hstab
  have hmem : x0 ∈ oTwoPrime (MulAction.stabilizer G (X.vert 6)) ⊓
      Subgroup.normalizer (X.edgeSylow 6 : Set G) := ⟨hx0L6, hx0N⟩
  rw [← hstab] at hmem
  have hfix : x0 • X.vert (6 + 1) = X.vert (6 + 1) :=
    MulAction.mem_stabilizer_iff.mp hmem.2
  have hfix7 : x0 • X.vert 7 = X.vert 7 := by
    rwa [show (6 : ℤ) + 1 = 7 by norm_num] at hfix
  exact not_fixes_seven_of_mem_Z_zero C h12 hx0 hx0ne hfix7

private theorem not_conjSub_edgeSylow_six_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {x0 : G}
    (hx0 : x0 ∈ X.Z 0) (hx0ne : x0 ≠ 1) :
    ¬ X.edgeSylow 6 ≤ conjSub x0 (X.edgeSylow 6) ⊔ X.Vk 6 := by
  obtain ⟨hx0L6, -⟩ := mem_L_six_and_notMem_Q_six C h12 hx0 hx0ne
  have hV6Q6 : X.Vk 6 ≤ X.Q 6 := Vk_six_le_Q_six C hH h12
  have hQ6T6 : X.Q 6 ≤ X.edgeSylow 6 := X.Q_le_edgeSylow_left 6
  have hQ6norm : X.L 6 ≤ Subgroup.normalizer (X.Q 6 : Set G) :=
    (X.L_le_Gi 6).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 6))
  have hQ6T'' : X.Q 6 ≤ conjSub x0 (X.edgeSylow 6) := by
    intro q hq
    rw [mem_conjSub]
    exact hQ6T6 (by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (hQ6norm ((X.L 6).inv_mem hx0L6)) q).mp hq)
  rw [sup_eq_left.mpr (hV6Q6.trans hQ6T'')]
  intro hle
  have hT6 : IsSylowTwoOf (X.edgeSylow 6) (X.L 6) := by
    simpa using X.isSylowTwoOf_edgeSylow_L 6
  have hT'' : IsSylowTwoOf (conjSub x0 (X.edgeSylow 6)) (X.L 6) := by
    have h := B6.isSylowTwoOf_conjSub hT6 x0
    change IsSylowTwoOf (conjSub x0 (X.edgeSylow 6)) (conjSub x0 (X.L 6)) at h
    rwa [conjSub_eq_of_mem hx0L6] at h
  haveI : Finite ↥(X.edgeSylow 6) :=
    finite_of_le_stabilizer X.hyp (H := X.edgeSylow 6) (hT6.1.trans (X.L_le_Gi 6))
  haveI : Finite ↥(conjSub x0 (X.edgeSylow 6)) :=
    finite_of_le_stabilizer X.hyp (H := conjSub x0 (X.edgeSylow 6))
      (hT''.1.trans (X.L_le_Gi 6))
  have hEq : conjSub x0 (X.edgeSylow 6) = X.edgeSylow 6 :=
    CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le hT6 hT''.2.1 hT''.1 hle
  exact not_mem_normalizer_edgeSylow_six_of_mem_Z_zero C h12 hx0 hx0ne (by
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq])

private theorem exists_decomp_relCent_zpowers (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {x0 : G}
    (hx0 : x0 ∈ X.Z 0) (hx0ne : x0 ≠ 1) {e : G}
    (he : e ∈ relCent (X.Vk 6) (X.Z 6) (Subgroup.zpowers x0)) :
    ∃ a ∈ relCent (X.Vk 6) (X.Z 6) (X.edgeSylow 5), ∃ b ∈ X.Z 6, e = a * b := by
  obtain ⟨hx0L6, -⟩ := mem_L_six_and_notMem_Q_six C h12 hx0 hx0ne
  have hNat := NatQuot_six C hH
  have hV6L : X.Vk 6 ≤ X.L 6 := hNat.E_le
  have hEZ : X.Vk 6 ≤ Subgroup.normalizer (X.Z 6 : Set G) := fun e he =>
    (Subgroup.mem_inf.mp (hNat.normal (hV6L he))).2
  have hT5 : IsSylowTwoOf (X.edgeSylow 5) (X.L 6) := by
    simpa using X.isSylowTwoOf_edgeSylow_L_succ 5
  have hT6 : IsSylowTwoOf (X.edgeSylow 6) (X.L 6) := by
    simpa using X.isSylowTwoOf_edgeSylow_L 6
  have hT'' : IsSylowTwoOf (conjSub x0 (X.edgeSylow 6)) (X.L 6) := by
    have h := B6.isSylowTwoOf_conjSub hT6 x0
    change IsSylowTwoOf (conjSub x0 (X.edgeSylow 6)) (conjSub x0 (X.L 6)) at h
    rwa [conjSub_eq_of_mem hx0L6] at h
  have hlines56 := hNat.lines_inf (X.edgeSylow 5) (X.edgeSylow 6) hT5 hT6
    (not_edgeSylow_five_le_edgeSylow_six C hH h12)
  have hlines6 := hNat.lines_inf (X.edgeSylow 6) (conjSub x0 (X.edgeSylow 6)) hT6 hT''
    (not_conjSub_edgeSylow_six_le C hH h12 hx0 hx0ne)
  have hcent : relCent (X.Vk 6) (X.Z 6) (X.edgeSylow 5) ≤
      Subgroup.centralizer (relCent (X.Vk 6) (X.Z 6) (X.edgeSylow 6) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (isElemAbelian_Vk_six C hH).comm hy.1 hx.1
  have hN := hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨a, ha, b, hb, heq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer
      (H := relCent (X.Vk 6) (X.Z 6) (X.edgeSylow 5))
      (K := relCent (X.Vk 6) (X.Z 6) (X.edgeSylow 6)) hN).mp
      (by rw [hlines56.2]; exact he.1)
  have he_mem : e ∈ relCent (X.Vk 6) (X.Z 6) (Subgroup.zpowers x0) := he
  have hx0T5 := mem_edgeSylow_five_of_mem_Z_zero C h12 hx0
  have haC : a ∈ relCent (X.Vk 6) (X.Z 6) (Subgroup.zpowers x0) := by
    rw [mem_relCent hEZ]
    refine ⟨ha.1, fun y hy => ?_⟩
    exact ha.2.2 y (Subgroup.zpowers_le.mpr hx0T5 hy)
  have hbC : b ∈ relCent (X.Vk 6) (X.Z 6) (Subgroup.zpowers x0) := by
    have h : a⁻¹ * e = b := by rw [heq]; group
    rw [← h]
    exact (relCent (X.Vk 6) (X.Z 6) (Subgroup.zpowers x0)).mul_mem
      ((relCent (X.Vk 6) (X.Z 6) (Subgroup.zpowers x0)).inv_mem haC) he_mem
  have hbT'' : b ∈ relCent (X.Vk 6) (X.Z 6) (conjSub x0 (X.edgeSylow 6)) := by
    rw [mem_relCent hEZ]
    refine ⟨hb.1, fun y hy => ?_⟩
    rw [mem_conjSub] at hy
    have hy' : y = x0 * (x0⁻¹ * y * x0) * x0⁻¹ := by group
    rw [hy']
    exact commutator_conj_mem_Z_six_gen C hH
      (hbC.2.2 x0 (Subgroup.mem_zpowers x0))
      (hb.2.2 (x0⁻¹ * y * x0) hy) hx0L6 (hT6.1 hy)
  have hbZ6 : b ∈ X.Z 6 := by
    have hbin : b ∈ relCent (X.Vk 6) (X.Z 6) (X.edgeSylow 6) ⊓
        relCent (X.Vk 6) (X.Z 6) (conjSub x0 (X.edgeSylow 6)) := ⟨hb, hbT''⟩
    rw [hlines6.1] at hbin
    exact hbin
  exact ⟨a, ha, b, hbZ6, heq⟩

private theorem relCent_zpowers_le_edgeSylow_five (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {x0 : G}
    (hx0 : x0 ∈ X.Z 0) (hx0ne : x0 ≠ 1) :
    relCent (X.Vk 6) (X.Z 6) (Subgroup.zpowers x0) ≤
      relCent (X.Vk 6) (X.Z 6) (X.edgeSylow 5) := by
  intro e he
  obtain ⟨a, ha, b, hb, heq⟩ := exists_decomp_relCent_zpowers C hH h12 hx0 hx0ne he
  have hNat := NatQuot_six C hH
  have hV6L : X.Vk 6 ≤ X.L 6 := hNat.E_le
  have hEZ : X.Vk 6 ≤ Subgroup.normalizer (X.Z 6 : Set G) := fun e he =>
    (Subgroup.mem_inf.mp (hNat.normal (hV6L he))).2
  have hZnorm : X.L 6 ≤ Subgroup.normalizer (X.Z 6 : Set G) := fun y hy =>
    (Subgroup.mem_inf.mp (hNat.normal hy)).2
  have hT5 : IsSylowTwoOf (X.edgeSylow 5) (X.L 6) := by
    simpa using X.isSylowTwoOf_edgeSylow_L_succ 5
  rw [mem_relCent hEZ] at he ⊢
  refine ⟨he.1, fun t ht => ?_⟩
  have hbt : ⁅b, t⁆ ∈ X.Z 6 := by
    have htZ : t * b * t⁻¹ ∈ X.Z 6 :=
      (Subgroup.mem_normalizer_iff.mp (hZnorm (hT5.1 ht)) b).mp hb
    have hEq : ⁅b, t⁆ = b * (t * b * t⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hEq]
    exact (X.Z 6).mul_mem hb ((X.Z 6).inv_mem htZ)
  have hat : ⁅a, t⁆ ∈ X.Z 6 := ha.2.2 t ht
  rw [heq, commutatorElement_mul_left_eq_conj_mul]
  have hconj : a * ⁅b, t⁆ * a⁻¹ ∈ X.Z 6 :=
    (Subgroup.mem_normalizer_iff.mp (hZnorm (hV6L ha.1)) ⁅b, t⁆).mp hbt
  exact (X.Z 6).mul_mem hconj hat

private theorem exists_sylow_relCent_zpowers_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {x0 : G}
    (hx0 : x0 ∈ X.Z 0) (hx0ne : x0 ≠ 1) :
    ∃ T : Subgroup G, IsSylowTwoOf T (X.L 6) ∧
      relCent (X.Vk 6) (X.Z 6) (Subgroup.zpowers x0) = relCent (X.Vk 6) (X.Z 6) T := by
  have hNat := NatQuot_six C hH
  have hV6L : X.Vk 6 ≤ X.L 6 := hNat.E_le
  have hEZ : X.Vk 6 ≤ Subgroup.normalizer (X.Z 6 : Set G) := fun e he =>
    (Subgroup.mem_inf.mp (hNat.normal (hV6L he))).2
  have hT5 : IsSylowTwoOf (X.edgeSylow 5) (X.L 6) := by
    simpa using X.isSylowTwoOf_edgeSylow_L_succ 5
  have hx0T5 := mem_edgeSylow_five_of_mem_Z_zero C h12 hx0
  refine ⟨X.edgeSylow 5, hT5, le_antisymm ?_ ?_⟩
  · exact relCent_zpowers_le_edgeSylow_five C hH h12 hx0 hx0ne
  · intro e he
    rw [mem_relCent hEZ] at he ⊢
    exact ⟨he.1, fun y hy => he.2 y (Subgroup.zpowers_le.mpr hx0T5 hy)⟩

private theorem Z_five_inf_Z_eight (C : X.Comm48 s r d) (h12 : r = 12) :
    X.Z 5 ⊓ X.Z 8 = ⊥ := by
  have hB5 : X.HasB 5 5 :=
    (X.hasB_iff_of_even (i := 5) (j := 1) (by norm_num) 5).mpr
      (hasB_one_five C h12)
  have hB8 : X.HasB 8 6 :=
    (X.hasB_iff_of_even (i := 8) (j := 0) (by norm_num) 6).mpr
      (hasB_zero_six C h12)
  have hZ5P : IsPGroup 2 (X.Z 5) :=
    (pCoreOf_isPGroup' (X.Gi 5)).to_le (X.Z_le_Q 5)
  have hZ5Z8bot : X.Z 5 ⊓ X.Z 8 = ⊥ := by
    by_contra hne
    let U : Subgroup G := X.Z 5 ⊓ X.Z 8
    have hne' : U ≠ ⊥ := by simpa [U] using hne
    have hU2 : IsPGroup 2 U := hZ5P.to_le (fun x hx => hx.1)
    have hfix : U ≤ X.arcStab 0 14 := by
      intro z hz
      rw [Setup.arcStab, Fan86.mem_fixSet]
      rintro v ⟨k, hk, rfl⟩
      rw [Set.mem_Icc] at hk
      by_cases hk10 : k ≤ 10
      · have hz5 : z ∈ X.Gi k := by
          by_cases hk5 : k ≤ 5
          · exact X.le_Gi_of_sub_le (i := 5) (m := 5) (hB5.Z_le_Gi (by omega))
              k (by omega) (by omega) hz.1
          · exact X.le_Gi_of_le_add (i := 5) (m := 5)
              (hB5.1 5 (by norm_num)) k (by omega) (by omega) hz.1
        exact MulAction.mem_stabilizer_iff.mp hz5
      · have hz8 : z ∈ X.Gi k :=
          X.le_Gi_of_le_add (i := 8) (m := 6)
            (hB8.1 6 (by norm_num)) k (by omega) (by omega) hz.2
        exact MulAction.mem_stabilizer_iff.mp hz8
    have h := X.le_r_of_fixes C.hyp (a := (0 : ℤ)) (k := 14) hU2 hne' hfix
    omega
  exact hZ5Z8bot

private theorem Z_zero_le_centralizer_Z_five
    (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) :
    X.Z 0 ≤ Subgroup.centralizer (X.Z 5 : Set G) := by
  have hB0 := hasB_zero_six C h12
  have hZ4center : X.Z 4 = centerOf (X.L 4) := by
    have h := (X.s48_0 C).2
    have hZ4 : X.Z 4 = conjSub (X.τ ^ (2 : ℤ)) (X.Z 0) := by
      have := X.Z_add 2 0
      rwa [show (0 : ℤ) + 2 * 2 = 4 by norm_num] at this
    have hL4 : X.L 4 = conjSub (X.τ ^ (2 : ℤ)) (X.L 0) := by
      have := X.L_add 2 0
      rwa [show (0 : ℤ) + 2 * 2 = 4 by norm_num] at this
    rw [hZ4, hL4, h, centerOf_conjSub]
  have hZ0L4 : X.Z 0 ≤ X.L 4 :=
    le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0))
      (hB0.1 4 (by norm_num))
  have hZ0Z4 : X.Z 0 ≤ Subgroup.centralizer (X.Z 4 : Set G) := by
    intro z0 hz0
    rw [Subgroup.mem_centralizer_iff]
    intro z4 hz4
    have hz4c : z4 ∈ centerOf (X.L 4) := by rw [← hZ4center]; exact hz4
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp hz4c).2 z0 (hZ0L4 hz0)).symm

  rw [show X.Z 5 = X.Z 4 ⊔ X.Z 6 by
      simpa using X.Z_eq_sup_of_odd C hH (j := 5) (by norm_num),
    Subgroup.le_centralizer_iff]
  exact sup_le (Subgroup.le_centralizer_iff.mp hZ0Z4)
    (Subgroup.le_centralizer_iff.mp (Z_zero_le_centralizer_Z_six C h12))

private theorem mem_relCent_zpowers_of_commute {E Z : Subgroup G} {x y : G}
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) (hy : y ∈ E) (hxy : Commute x y) :
    y ∈ relCent E Z (Subgroup.zpowers x) := by
  refine (mem_relCent hEZ).mpr ⟨hy, fun a ha => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hxy.zpow_left n).symm.eq]
  exact Z.one_mem

private theorem Z_six_le_Vk_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 6 ≤ X.Vk 6 := by
  have hZ7sup := Z_seven_eq_sup_Z_six_Z_eight C hH
  have hVk_eq := Vk_six_eq_sup C hH
  rw [hVk_eq]
  exact ((by rw [hZ7sup]; exact le_sup_left) : X.Z 6 ≤ X.Z 7).trans
    (le_sup_right : X.Z 7 ≤ X.Z 5 ⊔ X.Z 7)

private theorem Z_six_eq_centerOf_L_six (C : X.Comm48 s r d) :
    X.Z 6 = centerOf (X.L 6) := by
  have hZ6 : X.Z 6 = conjSub (X.τ ^ (3 : ℤ)) (X.Z 0) := by
    have := X.Z_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this
  have hL6 : X.L 6 = conjSub (X.τ ^ (3 : ℤ)) (X.L 0) := by
    have := X.L_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this
  rw [hZ6, hL6, (X.s48_0 C).2, centerOf_conjSub]

private theorem Z_six_le_relCent_sylow (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {T : Subgroup G}
    (hT : IsSylowTwoOf T (X.L 6)) : X.Z 6 ≤ relCent (X.Vk 6) (X.Z 6) T := by
  have hNat := NatQuot_six C hH
  have hEZ : X.Vk 6 ≤ Subgroup.normalizer (X.Z 6 : Set G) := fun e he =>
    (Subgroup.mem_inf.mp (hNat.normal (hNat.E_le he))).2
  have hZ6E := Z_six_le_Vk_six C hH
  have hZ6center := Z_six_eq_centerOf_L_six C
  intro z hz
  rw [mem_relCent hEZ]
  refine ⟨hZ6E hz, fun a ha => ?_⟩
  have hzcent : z ∈ centerOf (X.L 6) := by rw [← hZ6center]; exact hz
  have hcomm : ⁅z, a⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzcent).2 a (hT.1 ha)).symm
  rw [hcomm]
  exact (X.Z 6).one_mem

private theorem card_Z_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : Nat.card (X.Z 6) = 2 ^ X.n 0 := by
  have hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0 := (X.s48_2 C).2.2.2.2.1
  have hZ6conj : X.Z 6 = conjSub (X.τ ^ (3 : ℤ)) (X.Z 0) := by
    have := X.Z_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this
  rw [hZ6conj, card_conjSub]
  exact hcardZ0

private theorem card_Z_five (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : Nat.card (X.Z 5) = 2 ^ (2 * X.n 0) := by
  have hcardZ1 : Nat.card (X.Z 1) = 2 ^ (2 * X.n 0) := (X.s48_4' C hH).2.2.2.1
  have hZ5conj : X.Z 5 = conjSub (X.τ ^ (2 : ℤ)) (X.Z 1) := by
    have := X.Z_add 2 1
    rwa [show (1 : ℤ) + 2 * 2 = 5 by norm_num] at this
  rw [hZ5conj, card_conjSub]
  exact hcardZ1

private theorem relIndex_relCent_sylow (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {T : Subgroup G}
    (hT : IsSylowTwoOf T (X.L 6)) :
    (X.Z 6).relIndex (relCent (X.Vk 6) (X.Z 6) T) = 2 ^ X.n 0 := by
  have h := (NatQuot_six C hH).line T hT
  rwa [show X.n 6 = X.n 0 from by
    have := X.n_add 3 0
    rwa [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at this] at h

private theorem card_relCent_sylow (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {T : Subgroup G}
    (hT : IsSylowTwoOf T (X.L 6)) (hZ6rel : X.Z 6 ≤ relCent (X.Vk 6) (X.Z 6) T) :
    Nat.card (relCent (X.Vk 6) (X.Z 6) T) = 2 ^ (2 * X.n 0) := by
  have hNat := NatQuot_six C hH
  have hcardZ6 := card_Z_six C hH
  have hrelT := relIndex_relCent_sylow C hH hT
  have hrelR_le : relCent (X.Vk 6) (X.Z 6) T ≤ X.Vk 6 := fun x hx => hx.1
  haveI : Finite ↥(X.Z 6) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 6) (X.Z_le_Gi 6)
  haveI : Finite ↥(relCent (X.Vk 6) (X.Z 6) T) :=
    finite_of_le_stabilizer X.hyp (H := relCent (X.Vk 6) (X.Z 6) T)
      ((hrelR_le.trans hNat.E_le).trans (X.L_le_Gi 6))
  have h := Subgroup.relIndex_mul_card (H := X.Z 6) (K := relCent (X.Vk 6) (X.Z 6) T)
  have hinf : X.Z 6 ⊓ relCent (X.Vk 6) (X.Z 6) T = X.Z 6 :=
    le_antisymm inf_le_left (le_inf le_rfl hZ6rel)
  rw [hinf, hrelT, hcardZ6] at h
  rw [← h, ← pow_add]
  congr 1
  ring

private theorem Z_five_eq_relCent (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {T : Subgroup G}
    (hT : IsSylowTwoOf T (X.L 6)) (hZ5le : X.Z 5 ≤ relCent (X.Vk 6) (X.Z 6) T) :
    X.Z 5 = relCent (X.Vk 6) (X.Z 6) T := by
  have hNat := NatQuot_six C hH
  have hZ6rel := Z_six_le_relCent_sylow C hH hT
  have hrelR_le : relCent (X.Vk 6) (X.Z 6) T ≤ X.Vk 6 := fun x hx => hx.1
  haveI : Finite ↥(relCent (X.Vk 6) (X.Z 6) T) :=
    finite_of_le_stabilizer X.hyp (H := relCent (X.Vk 6) (X.Z 6) T)
      ((hrelR_le.trans hNat.E_le).trans (X.L_le_Gi 6))
  refine Subgroup.eq_of_le_of_card_ge hZ5le ?_
  rw [card_relCent_sylow C hH hT hZ6rel, card_Z_five C hH]

private theorem aniso_seven (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {x y : G}
    (hx : x ∈ X.Z 1) (hx2 : x ∉ X.Z 2) (hy : y ∈ X.Z 7) (hy6 : y ∉ X.Z 6) : ⁅x, y⁆ ≠ 1 := by
  obtain ⟨x0, hx0, hx0ne, y8, hy8, hy8ne, hcommxy⟩ :=
    exists_commutator_eq_Z_zero_Z_eight C hH h12 hx hx2 hy hy6
  intro hxy
  have hzero : ⁅x0, y8⁆ = 1 := by rw [← hcommxy]; exact hxy
  obtain ⟨T, hT, hrelG⟩ := exists_sylow_relCent_zpowers_eq C hH h12 hx0 hx0ne
  have hVk_le_L : X.Vk 6 ≤ X.L 6 := (Vk_six_le_Q_six C hH h12).trans (X.Q_le_L 6)
  have hEZ : X.Vk 6 ≤ Subgroup.normalizer (X.Z 6 : Set G) := fun e he =>
    (Subgroup.mem_inf.mp ((NatQuot_six C hH).normal (hVk_le_L he))).2
  have hZ7sup : X.Z 7 = X.Z 6 ⊔ X.Z 8 := by
    simpa using X.Z_eq_sup_of_odd C hH (j := 7) (by norm_num)
  have hZ5E : X.Z 5 ≤ X.Vk 6 := by rw [Vk_six_eq_sup C hH]; exact le_sup_left
  have hZ8E : X.Z 8 ≤ X.Vk 6 := by
    rw [Vk_six_eq_sup C hH, hZ7sup]; exact le_sup_right.trans le_sup_right
  have hZ5le : X.Z 5 ≤ relCent (X.Vk 6) (X.Z 6) T := by
    rw [← hrelG]
    intro z hz
    exact mem_relCent_zpowers_of_commute hEZ (hZ5E hz)
      (Subgroup.mem_centralizer_iff.mp (Z_zero_le_centralizer_Z_five C hH h12 hx0) z hz).symm
  have hy8R : y8 ∈ relCent (X.Vk 6) (X.Z 6) T := by
    rw [← hrelG]
    exact mem_relCent_zpowers_of_commute hEZ (hZ8E hy8)
      (commutatorElement_eq_one_iff_mul_comm.mp hzero)
  rw [← Z_five_eq_relCent C hH h12 hT hZ5le] at hy8R
  have hbot : y8 ∈ X.Z 5 ⊓ X.Z 8 := Subgroup.mem_inf.mpr ⟨hy8R, hy8⟩
  rw [Z_five_inf_Z_eight C h12] at hbot
  exact hy8ne (Subgroup.mem_bot.mp hbot)

private theorem exists_smul_arc_six_eq_line (C : X.Comm48 s r d) (lam : Arc Γ 6)
    (hlam : lam.vert 0 ∈ MulAction.orbit G (X.vert 1)) :
    ∃ h : G, ∀ i : ℕ, i ≤ 5 → h • lam.vert (i + 1) = X.vert i := by
  have hneigh := exists_adj_of_isSingularity X.hyp.isTree C.hyp.sing
  have horb := orbit_eq_even_of_adj X.hyp.isTree X.hyp.adj_smul X.hyp.edgeTrans
    X.hyp.preservesParts (X.adj 0) hneigh
  have hodd0 : Odd (Γ.dist (X.vert 0) (lam.vert 0)) :=
    (horb.2 (lam.vert 0)).mp hlam
  have heven1 : Even (Γ.dist (X.vert 0) (lam.vert 1)) := by
    rcases IsTree.dist_adj_cases X.hyp.isTree (r := X.vert 0)
      (lam.adj 0 (by norm_num)) with h | h
    · rw [h]
      exact (even_succ_iff_odd _).mpr hodd0
    · exact (odd_succ_iff_even _).mp (h ▸ hodd0)
  have hlam1 : lam.vert 1 ∈ MulAction.orbit G (X.vert 0) :=
    (horb.1 (lam.vert 1)).mpr heven1
  obtain ⟨g, hg⟩ := hlam1
  have hg' : g⁻¹ • lam.vert 1 = X.vert 0 := by
    rw [← hg, inv_smul_smul]
  let P : Arc Γ 5 :=
    { vert := fun i => lam.vert (i + 1)
      adj := fun i _ => lam.adj (i + 1) (by omega)
      nb := fun i _ => lam.nb (i + 1) (by omega) }
  let Q : Arc Γ 5 := X.line.arc 0 5
  have hgP : g⁻¹ • P.vert 0 = Q.vert 0 := by
    simpa [P, Q, Line.arc_vert_zero] using hg'
  obtain ⟨h, hh⟩ := arc_conj_of_le X.hyp.adj_smul
    (fun v a b ha hb => X.hyp.locTrans ha hb) C.hyp.sing (le_trans (by norm_num) C.hyp.five_le)
    P Q g⁻¹ hgP
  have hh' : ∀ i, i ≤ 5 → h • lam.vert (i + 1) = X.vert i := by
    intro i hi
    simpa [P, Q, Line.arc] using hh i hi
  exact ⟨h, hh'⟩

private theorem exists_mem_arcStab_smul_eq
    (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {a : V}
    (hadja : Γ.Adj (X.vert 0) a) (hane : a ≠ X.vert 1) :
    ∃ q ∈ X.arcStab 0 12, q • a = X.vert (-1) := by
  subst r
  have hadjm : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h := (X.adj (-1)).symm
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hnem : X.vert (-1) ≠ X.vert 1 := by
    intro hh
    have := X.vert_injective hh
    omega
  have hSleS : X.S ≤ X.edgeSylow 0 := by rw [X.edgeSylow_zero]
  obtain ⟨s, hsS, hsa⟩ := X.edgeSylow_transitive_left 0 a (X.vert (-1)) hadja hane
    hadjm hnem
  have hsS' : s ∈ X.S := by rwa [X.edgeSylow_zero] at hsS
  obtain ⟨-, hSsup⟩ := Qg_le_S_and_sup C
  have hsSup : s ∈ X.Qg 12 ⊔ X.Q 0 := by
    rw [hSsup]
    exact hsS'
  have hQgNorm : X.Qg 12 ≤ Subgroup.normalizer (X.Q 0 : Set G) := by
    have hQleS : X.Qg 12 ≤ X.S := (Qg_le_S_and_sup C).1
    exact hQleS.trans (hSleS.trans
      ((X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left |>.trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))))
  obtain ⟨q, hq, q0, hq0, hsq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQgNorm).mp hsSup
  rw [hsq] at hsa
  have hq0fix : q0 • a = a :=
    X.Q_fixes_neighbors_vert 0 a hadja q0 hq0
  have hqA : q ∈ X.arcStab 0 12 := by
    have hcle : X.Qg 12 ≤ X.arcStab 0 12 :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab 0 12))
    exact hcle hq

  have hqa : q • a = X.vert (-1) := by
    have h1 : (q * q0) • a = q • a := by
      rw [mul_smul, hq0fix]
    rw [← h1]
    exact hsa
  exact ⟨q, hqA, hqa⟩

private theorem exists_conj_arc_std (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) (lam : Arc Γ 6)
    (hlam : lam.vert 0 ∈ MulAction.orbit G (X.vert 1)) :
    ∃ g : G, g • lam.vert 0 = X.vert 1 ∧ g • lam.vert 1 = X.vert 2 ∧
      g • lam.vert 3 = X.vert 4 ∧ g • lam.vert 5 = X.vert 6 ∧ g • lam.vert 6 = X.vert 7 := by
  obtain ⟨h, hh'⟩ := exists_smul_arc_six_eq_line C lam hlam
  have hh0 := hh' 0 (by norm_num)
  have hh5 := hh' 5 (by norm_num)
  set a : V := h • lam.vert 0 with ha
  have hadja : Γ.Adj (X.vert 0) a := by
    have h := (X.hyp.adj_smul h (lam.vert 0) (lam.vert 1)).2 (lam.adj 0 (by norm_num))
    rw [hh0, ← ha] at h
    simpa using h.symm
  have hane : a ≠ X.vert 1 := by
    intro hat
    have hEq : h • lam.vert 0 = h • lam.vert 2 := by
      rw [← ha, hat, hh' 1 (by norm_num)]
      norm_num
    exact lam.nb 0 (by norm_num) (MulAction.injective h hEq)

  obtain ⟨q, hqA, hqa⟩ := exists_mem_arcStab_smul_eq C hH h12 hadja hane
  have hqfix : ∀ i : ℤ, 0 ≤ i → i ≤ 5 → q • X.vert i = X.vert i := by
    intro i hi0 hi5
    have hGi : q ∈ X.Gi i := X.arcStab_le_Gi_of_between (by omega) (by omega) hqA
    exact MulAction.mem_stabilizer_iff.mp hGi

  set k : G := q * h with hk
  have hk0 : k • lam.vert 0 = X.vert (-1) := by
    rw [hk, mul_smul]
    change q • a = X.vert (-1)
    exact hqa
  have hk3 : k • lam.vert 3 = X.vert 2 := by
    rw [hk, mul_smul, hh' 2 (by norm_num)]
    simpa using hqfix 2 (by norm_num) (by norm_num)
  have hk6 : k • lam.vert 6 = X.vert 5 := by
    rw [hk, mul_smul, hh5]
    simpa using hqfix 5 (by norm_num) (by norm_num)
  let g : G := X.τ * k
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show g = X.τ * k from rfl, mul_smul, hk0]
    simpa using X.zpow_smul_vert 1 (-1)
  · rw [show g = X.τ * k from rfl, mul_smul]
    have hk1 : k • lam.vert 1 = X.vert 0 := by
      rw [hk, mul_smul, hh' 0 (by norm_num)]
      simpa using hqfix 0 (by norm_num) (by norm_num)
    rw [hk1]
    simpa using X.zpow_smul_vert 1 0
  · rw [show g = X.τ * k from rfl, mul_smul, hk3]
    simpa using X.zpow_smul_vert 1 2
  · rw [show g = X.τ * k from rfl, mul_smul]
    have hk5 : k • lam.vert 5 = X.vert 4 := by
      rw [hk, mul_smul, hh' 4 (by norm_num)]
      simpa using hqfix 4 (by norm_num) (by norm_num)
    rw [hk5]
    simpa using X.zpow_smul_vert 1 4
  · rw [show g = X.τ * k from rfl, mul_smul, hk6]
    simpa using X.zpow_smul_vert 1 5

private theorem commutator_vertZ_arc_six_eq
    (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) (lam : Arc Γ 6)
    (hlam : lam.vert 0 ∈ MulAction.orbit G (X.vert 1)) :
    ⁅vertZ (V := V) (G := G) (lam.vert 0), vertZ (V := V) (G := G) (lam.vert 6)⁆ =
      vertZ (V := V) (G := G) (lam.vert 3) := by
  obtain ⟨g, hg0, -, hg3, -, hg6⟩ := exists_conj_arc_std C hH h12 lam hlam
  have e : ∀ (i : ℕ) (j : ℤ), g • lam.vert i = X.vert j →
      vertZ (V := V) (G := G) (lam.vert i) = conjSub g⁻¹ (X.Z j) := by
    intro i j hij
    have h := vertZ_smul (V := V) (G := G) g (lam.vert i)
    rw [hij, ← X.Z_eq_vertZ j] at h
    simpa [conjSub_conjSub_inv] using (congrArg (conjSub g⁻¹) h).symm
  have hb : ⁅X.Z 1, X.Z 7⁆ = X.Z 4 := by
    simpa using commutator_Z_add_six C hH h12 (j := 1) (by norm_num)
  rw [e 0 1 hg0, e 6 7 hg6, e 3 4 hg3, conjSub_commutator g⁻¹ (X.Z 1) (X.Z 7), hb]

private theorem commutator_ne_one_of_arc_six (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) (lam : Arc Γ 6)
    (hlam : lam.vert 0 ∈ MulAction.orbit G (X.vert 1)) {x y : G}
    (hx : x ∈ vertZ (V := V) (G := G) (lam.vert 0))
    (hx' : x ∉ vertZ (V := V) (G := G) (lam.vert 1))
    (hy : y ∈ vertZ (V := V) (G := G) (lam.vert 6))
    (hy' : y ∉ vertZ (V := V) (G := G) (lam.vert 5)) : ⁅x, y⁆ ≠ 1 := by
  obtain ⟨g, hg0, hg1, -, hg5, hg6⟩ := exists_conj_arc_std C hH h12 lam hlam
  let x' : G := g * x * g⁻¹
  let y' : G := g * y * g⁻¹
  have hxZ1 : x' ∈ X.Z 1 := by
    have h : x' ∈ conjSub g (vertZ (V := V) (G := G) (lam.vert 0)) := by
      exact mul_mem_conjSub hx
    rw [← vertZ_smul (V := V) (G := G) g (lam.vert 0), hg0,
      ← X.Z_eq_vertZ 1] at h
    exact h
  have hx2 : x' ∉ X.Z 2 := by
    intro h
    apply hx'
    have hmem : x' ∈ conjSub g (vertZ (V := V) (G := G) (lam.vert 1)) := by
      rw [← vertZ_smul (V := V) (G := G) g (lam.vert 1), hg1, ← X.Z_eq_vertZ 2]
      exact h
    have hxeq : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have := mem_conjSub.mp hmem
    simpa [x', hxeq] using this
  have hyZ7 : y' ∈ X.Z 7 := by
    have h : y' ∈ conjSub g (vertZ (V := V) (G := G) (lam.vert 6)) := by
      exact mul_mem_conjSub hy
    rw [← vertZ_smul (V := V) (G := G) g (lam.vert 6), hg6,
      ← X.Z_eq_vertZ 7] at h
    exact h
  have hy6 : y' ∉ X.Z 6 := by
    intro h
    apply hy'
    have hmem : y' ∈ conjSub g (vertZ (V := V) (G := G) (lam.vert 5)) := by
      rw [← vertZ_smul (V := V) (G := G) g (lam.vert 5), hg5, ← X.Z_eq_vertZ 6]
      exact h
    have hyeq : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have := mem_conjSub.mp hmem
    simpa [y', hyeq] using this
  have hne' : ⁅x', y'⁆ ≠ 1 := aniso_seven C hH h12 hxZ1 hx2 hyZ7 hy6
  intro hxy
  apply hne'
  have hconj : g * ⁅x, y⁆ * g⁻¹ = ⁅x', y'⁆ := by
    rw [commutatorElement_def]
    simp only [x', y', commutatorElement_def]
    group
  rw [← hconj, hxy]
  simp

private theorem not_fixes_three_of_mem_Z_ten (C : X.Comm48 s r d) (h12 : r = 12)
    {z' : G} (hz10 : z' ∈ X.Z 10) (hz1 : z' ≠ 1) : z' • X.vert 3 ≠ X.vert 3 := by
  have hB10 : X.HasB 10 6 :=
    (X.hasB_iff_of_even (i := 10) (j := 0) (by norm_num) 6).mpr
      (hasB_zero_six C h12)
  have hZ10P : IsPGroup 2 (X.Z 10) :=
    (pCoreOf_isPGroup' (X.Gi 10)).to_le (X.Z_le_Q 10)
  have hz'_not3 : z' • X.vert 3 ≠ X.vert 3 := by
    intro hz3
    have hU2 : IsPGroup 2 (Subgroup.zpowers z') :=
      hZ10P.to_le (Subgroup.zpowers_le.mpr hz10)
    have hfix : Subgroup.zpowers z' ≤ X.arcStab 3 ((3 : ℤ) + 13) := by
      rw [Subgroup.zpowers_le]
      rw [Setup.arcStab, Fan86.mem_fixSet]
      rintro v ⟨k, hk, rfl⟩
      rw [Set.mem_Icc] at hk
      by_cases hk4 : 4 ≤ k
      · have hzGk : z' ∈ X.Gi k := by
          by_cases hk10 : 10 ≤ k
          · exact X.le_Gi_of_le_add (i := 10) (m := 6)
              (hB10.1 6 (by norm_num)) k (by omega) (by omega) hz10
          · exact X.le_Gi_of_sub_le (i := 10) (m := 6) (hB10.Z_le_Gi (by omega))
              k (by omega) (by omega) hz10
        exact MulAction.mem_stabilizer_iff.mp hzGk
      · have hk3 : k = 3 := by omega
        subst k
        exact hz3
    have hbot := eq_bot_of_fixes_arc C hU2 hfix (by omega : r < 13)
    have hzmem : z' ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers z'
    exact hz1 (Subgroup.mem_bot.mp hzmem)
  exact hz'_not3

private theorem exists_arc_six_through_six {z : G} (hz6 : z • X.vert 6 = X.vert 6)
    (hz7 : z • X.vert 7 ≠ X.vert 7) :
    ∃ lam : Arc Γ 6, lam.vert 0 = z • X.vert 9 ∧ lam.vert 3 = X.vert 6 ∧
      lam.vert 6 = X.vert 9 ∧ lam.vert 0 ∈ MulAction.orbit G (X.vert 1) := by
  let P : Arc Γ 3 := (X.line.arc 6 3).rev
  let Q : Arc Γ 3 := X.line.arc 6 3
  have hPend : (smulArc X.hyp.adj_smul z P).vert 3 = Q.vert 0 := by
    have hL : (smulArc X.hyp.adj_smul z P).vert 3 = z • X.vert 6 := by
      simp [P, Arc.rev_vert, Line.arc]
    have hR : Q.vert 0 = X.vert 6 := by simp [Q, Line.arc]
    rw [hL, hR]
    exact hz6
  have hPnb : 1 ≤ 3 → 1 ≤ 3 →
      (smulArc X.hyp.adj_smul z P).vert (3 - 1) ≠ Q.vert 1 := by
    intro _ _
    have hL : (smulArc X.hyp.adj_smul z P).vert (3 - 1) = z • X.vert 7 := by
      simp [P, Arc.rev_vert, Line.arc]
    have hR : Q.vert 1 = X.vert 7 := by simp [Q, Line.arc]
    rw [hL, hR]
    exact hz7
  let lam : Arc Γ 6 := Arc.append (smulArc X.hyp.adj_smul z P) Q hPend hPnb
  have lam0 : lam.vert 0 = z • X.vert 9 := by
    have h := Arc.append_vert_le (smulArc X.hyp.adj_smul z P) Q hPend hPnb
      (i := 0) (by omega)
    have h' : lam.vert 0 = (smulArc X.hyp.adj_smul z P).vert 0 := h
    rw [h']
    simp [P, Arc.rev_vert, Line.arc]
  have lam3 : lam.vert 3 = X.vert 6 := by
    have h := Arc.append_vert_le (smulArc X.hyp.adj_smul z P) Q hPend hPnb
      (i := 3) le_rfl
    have h' : lam.vert 3 = (smulArc X.hyp.adj_smul z P).vert 3 := h
    rw [h']
    have hL : (smulArc X.hyp.adj_smul z P).vert 3 = z • X.vert 6 := by
      simp [P, Arc.rev_vert, Line.arc]
    rw [hL, hz6]
  have lam6 : lam.vert 6 = X.vert 9 := by
    have h := Arc.append_vert_ge (smulArc X.hyp.adj_smul z P) Q hPend hPnb
      (i := 6) (by omega)
    have h' : lam.vert 6 = Q.vert (6 - 3) := h
    rw [h']
    norm_num
    simp [Q, Line.arc]

  have hlam : lam.vert 0 ∈ MulAction.orbit G (X.vert 1) := by
    rw [lam0]
    have h := MulAction.mem_orbit (X.vert 1) (z * X.τ ^ (4 : ℤ))
    rwa [mul_smul, X.zpow_smul_vert 4 1,
      show (1 : ℤ) + 2 * (4 : ℤ) = 9 by norm_num] at h
  exact ⟨lam, lam0, lam3, lam6, hlam⟩

private theorem exists_arc_six_through_four {z' : G} (hz4 : z' • X.vert 4 = X.vert 4)
    (hz3 : z' • X.vert 3 ≠ X.vert 3) :
    ∃ lam : Arc Γ 6, lam.vert 0 = X.vert 1 ∧ lam.vert 1 = X.vert 2 ∧
      lam.vert 3 = X.vert 4 ∧ lam.vert 5 = z' • X.vert 2 ∧ lam.vert 6 = z' • X.vert 1 := by
  let P' : Arc Γ 3 := X.line.arc 1 3
  let Q' : Arc Γ 3 := (X.line.arc 1 3).rev
  have hP'end : P'.vert 3 = (smulArc X.hyp.adj_smul z' Q').vert 0 := by
    have hL : P'.vert 3 = X.vert 4 := by simp [P', Line.arc]
    have hR : (smulArc X.hyp.adj_smul z' Q').vert 0 = z' • X.vert 4 := by
      simp [Q', Arc.rev_vert, Line.arc]
    rw [hL, hR]
    exact hz4.symm
  have hP'nb : 1 ≤ 3 → 1 ≤ 3 →
      P'.vert (3 - 1) ≠ (smulArc X.hyp.adj_smul z' Q').vert 1 := by
    intro _ _
    have hL : P'.vert (3 - 1) = X.vert 3 := by simp [P', Line.arc]
    have hR : (smulArc X.hyp.adj_smul z' Q').vert 1 = z' • X.vert 3 := by
      simp [Q', Arc.rev_vert, Line.arc]
    rw [hL, hR]
    exact hz3.symm
  let lam' : Arc Γ 6 := Arc.append P' (smulArc X.hyp.adj_smul z' Q') hP'end hP'nb
  have lam'0 : lam'.vert 0 = X.vert 1 := by
    have h := Arc.append_vert_le P' (smulArc X.hyp.adj_smul z' Q') hP'end hP'nb
      (i := 0) (by omega)
    have h' : lam'.vert 0 = P'.vert 0 := h
    rw [h']
    simp [P', Line.arc]
  have lam'1 : lam'.vert 1 = X.vert 2 := by
    have h := Arc.append_vert_le P' (smulArc X.hyp.adj_smul z' Q') hP'end hP'nb
      (i := 1) (by omega)
    have h' : lam'.vert 1 = P'.vert 1 := h
    rw [h']
    simp [P', Line.arc]
  have lam'3 : lam'.vert 3 = X.vert 4 := by
    have h := Arc.append_vert_le P' (smulArc X.hyp.adj_smul z' Q') hP'end hP'nb
      (i := 3) le_rfl
    have h' : lam'.vert 3 = P'.vert 3 := h
    rw [h']
    simp [P', Line.arc]
  have lam'5 : lam'.vert 5 = z' • X.vert 2 := by
    have h := Arc.append_vert_ge P' (smulArc X.hyp.adj_smul z' Q') hP'end hP'nb
      (i := 5) (by omega)
    have h' : lam'.vert 5 = (smulArc X.hyp.adj_smul z' Q').vert (5 - 3) := h
    rw [h']
    norm_num
    simp [Q', Arc.rev_vert, Line.arc]
  have lam'6 : lam'.vert 6 = z' • X.vert 1 := by
    have h := Arc.append_vert_ge P' (smulArc X.hyp.adj_smul z' Q') hP'end hP'nb
      (i := 6) (by omega)
    have h' : lam'.vert 6 = (smulArc X.hyp.adj_smul z' Q').vert (6 - 3) := h
    rw [h']
    norm_num
    simp [Q', Arc.rev_vert, Line.arc]
  exact ⟨lam', lam'0, lam'1, lam'3, lam'5, lam'6⟩

private theorem commutator_conj_mem_Z_six
    (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {z z' : G}
    (hz0 : z ∈ X.Z 0) (hz1 : z ≠ 1) (hz10 : z' ∈ X.Z 10) :
    ⁅z * z' * z⁻¹, z'⁆ ∈ X.Z 6 := by
  have hzfix6 : z • X.vert 6 = X.vert 6 :=
    MulAction.mem_stabilizer_iff.mp ((hasB_zero_six C h12).1 6 (by norm_num) hz0)
  obtain ⟨lam, lam0, lam3, lam6, hlam⟩ :=
    exists_arc_six_through_six hzfix6 (not_fixes_seven_of_mem_Z_zero C h12 hz0 hz1)
  have hZ9sup : X.Z 9 = X.Z 8 ⊔ X.Z 10 := by
    have h := X.Z_eq_sup_of_odd C hH (j := 9) (by norm_num)
    simpa using h
  have hz9 : z' ∈ X.Z 9 := by
    rw [hZ9sup]
    exact (le_sup_right : X.Z 10 ≤ X.Z 8 ⊔ X.Z 10) hz10

  have hw_mem : z * z' * z⁻¹ ∈ vertZ (V := V) (G := G) (z • X.vert 9) := by
    have hZ : vertZ (V := V) (G := G) (z • X.vert 9) = conjSub z (X.Z 9) := by
      rw [vertZ_smul, ← X.Z_eq_vertZ 9]
    rw [hZ]
    simpa using mul_mem_conjSub (g := z) hz9
  have hc6 : ⁅z * z' * z⁻¹, z'⁆ ∈ X.Z 6 := by
    have h := commutator_vertZ_arc_six_eq C hH h12 lam hlam
    have hmem : ⁅z * z' * z⁻¹, z'⁆ ∈ ⁅vertZ (V := V) (G := G) (lam.vert 0),
        vertZ (V := V) (G := G) (lam.vert 6)⁆ :=
      Subgroup.commutator_mem_commutator (by rw [lam0]; exact hw_mem)
        (by rw [lam6]; exact hz9)
    rw [h, lam3] at hmem
    exact hmem
  exact hc6

private theorem commutator_conj_mem_Z_four
    (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h12 : r = 12) {z z' : G}
    (hz0 : z ∈ X.Z 0) (hz1 : z ≠ 1) (hz10 : z' ∈ X.Z 10) (hz'1 : z' ≠ 1) :
    ⁅z, z' * z * z'⁻¹⁆ ∈ X.Z 4 ∧ ⁅z, z' * z * z'⁻¹⁆ ≠ 1 := by
  have hB10 : X.HasB 10 6 :=
    (X.hasB_iff_of_even (i := 10) (j := 0) (by norm_num) 6).mpr
      (hasB_zero_six C h12)
  have hz'fix4 : z' • X.vert 4 = X.vert 4 :=
    MulAction.mem_stabilizer_iff.mp (hB10.Z_le_Gi (by omega) hz10)
  obtain ⟨lam', lam'0, lam'1, lam'3, lam'5, lam'6⟩ :=
    exists_arc_six_through_four hz'fix4
      (not_fixes_three_of_mem_Z_ten C h12 hz10 hz'1)
  have hlam' : lam'.vert 0 ∈ MulAction.orbit G (X.vert 1) := by
    rw [lam'0]
    exact MulAction.mem_orbit_self (X.vert 1)

  have hZ01 : X.Z 0 ≤ X.Z 1 := (X.s48_1 C).1
  have hzZ1 : z ∈ X.Z 1 := hZ01 hz0

  have hz_notZ2 : z ∉ X.Z 2 := by
    intro hz2mem
    have hmem : z ∈ X.Z 0 ⊓ X.Z 2 := Subgroup.mem_inf.mpr ⟨hz0, hz2mem⟩
    have hbot := (X.s48_4' C hH).2.2.1
    rw [hbot] at hmem
    exact hz1 (Subgroup.mem_bot.mp hmem)

  have hy_mem : z' * z * z'⁻¹ ∈ vertZ (V := V) (G := G) (z' • X.vert 1) := by
    have hZ : vertZ (V := V) (G := G) (z' • X.vert 1) = conjSub z' (X.Z 1) := by
      rw [vertZ_smul, ← X.Z_eq_vertZ 1]
    rw [hZ]
    simpa using mul_mem_conjSub (g := z') hzZ1
  have hy_not : z' * z * z'⁻¹ ∉ vertZ (V := V) (G := G) (z' • X.vert 2) := by
    have hZ : vertZ (V := V) (G := G) (z' • X.vert 2) = conjSub z' (X.Z 2) := by
      rw [vertZ_smul, ← X.Z_eq_vertZ 2]
    rw [hZ]
    intro hy
    have hz2 : z ∈ X.Z 2 := by
      have h := mem_conjSub.mp hy
      have hzy : z'⁻¹ * (z' * z * z'⁻¹) * z' = z := by group
      rwa [hzy] at h
    exact hz_notZ2 hz2
  have hne1 : ⁅z, z' * z * z'⁻¹⁆ ≠ 1 := by
    refine commutator_ne_one_of_arc_six C hH h12 lam' hlam' ?_ ?_ ?_ ?_
    · rw [lam'0]
      exact hzZ1
    · rw [lam'1]
      exact hz_notZ2
    · rw [lam'6]
      exact hy_mem
    · rw [lam'5]
      exact hy_not
  have hc4 : ⁅z, z' * z * z'⁻¹⁆ ∈ X.Z 4 := by
    have h := commutator_vertZ_arc_six_eq C hH h12 lam' hlam'
    have hmem : ⁅z, z' * z * z'⁻¹⁆ ∈ ⁅vertZ (V := V) (G := G) (lam'.vert 0),
        vertZ (V := V) (G := G) (lam'.vert 6)⁆ :=
      Subgroup.commutator_mem_commutator (by rw [lam'0]; exact hzZ1)
        (by rw [lam'6]; exact hy_mem)
    rw [h, lam'3] at hmem
    exact hmem
  exact ⟨hc4, hne1⟩

private theorem commutator_conj_eq_pow_four {z z' : G} (hz : z ^ 2 = 1) (hz' : z' ^ 2 = 1) :
    ⁅z, z' * z * z'⁻¹⁆ = (z * z') ^ 4 ∧ ⁅z * z' * z⁻¹, z'⁆ = (z * z') ^ 4 := by
  have hzz : z * z = 1 := by simpa [pow_two] using hz
  have hz'z' : z' * z' = 1 := by simpa [pow_two] using hz'
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'z'
  have hy2 : (z' * z * z'⁻¹) * (z' * z * z'⁻¹) = 1 := by
    have h := congrArg (fun t => z' * t * z'⁻¹) hzz
    simpa [mul_assoc] using h
  have hyinv : (z' * z * z'⁻¹)⁻¹ = z' * z * z'⁻¹ :=
    inv_eq_of_mul_eq_one_right hy2
  have hw2 : (z * z' * z⁻¹) * (z * z' * z⁻¹) = 1 := by
    have h := congrArg (fun t => z * t * z⁻¹) hz'z'
    simpa [mul_assoc] using h
  have hwinv : (z * z' * z⁻¹)⁻¹ = z * z' * z⁻¹ :=
    inv_eq_of_mul_eq_one_right hw2
  have hzy : ⁅z, z' * z * z'⁻¹⁆ = (z * z') ^ 4 := by
    rw [commutatorElement_def, hyinv, hzi, hz'i,
      pow_succ, pow_succ, pow_succ, pow_one]
    group
  have hwz : ⁅z * z' * z⁻¹, z'⁆ = (z * z') ^ 4 := by
    rw [commutatorElement_def, hwinv, hzi, hz'i,
      pow_succ, pow_succ, pow_succ, pow_one]
    group
  exact ⟨hzy, hwz⟩

end Comm48

variable (X) in
open Comm48 in
theorem s48_r_ne_12 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : r ≠ 12 := by
  intro h12
  have hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0 := (X.s48_2 C).2.2.2.2.1
  have hZ0el : IsElemAbelian 2 (X.Z 0) := (X.s48_2 C).2.2.2.2.2.1
  have hpow : 4 ≤ 2 ^ X.n 0 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (C.hyp.two_le_n 0)
  have hZ0ne : X.Z 0 ≠ ⊥ := by
    intro h
    have := hcardZ0
    rw [h] at this
    simp at this
    omega
  obtain ⟨zH, hzH1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ0ne
  let z : G := zH
  have hz0 : z ∈ X.Z 0 := zH.2
  have hz1 : z ≠ 1 := fun h => hzH1 (Subtype.ext h)
  have hz2 : z ^ 2 = 1 := hZ0el.2 z hz0

  have hZ10conj : X.Z 10 = conjSub (X.τ ^ (5 : ℤ)) (X.Z 0) := by
    have := X.Z_add 5 0
    rwa [show (0 : ℤ) + 2 * 5 = 10 by norm_num] at this
  have hcardZ10 : Nat.card (X.Z 10) = 2 ^ X.n 0 := by
    rw [hZ10conj, card_conjSub]; exact hcardZ0
  have hZ10ne : X.Z 10 ≠ ⊥ := by
    intro h
    have := hcardZ10
    rw [h] at this
    simp at this
    omega
  obtain ⟨zH', hzH'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ10ne
  let z' : G := zH'
  have hz10 : z' ∈ X.Z 10 := zH'.2
  have hz10_1 : z' ≠ 1 := fun h => hzH'1 (Subtype.ext h)
  have hZ10el : IsElemAbelian 2 (X.Z 10) := by
    have h := F7.isElemAbelian_conjSub (p := 2) (g := X.τ ^ (5 : ℤ)) (X := X.Z 0) hZ0el
    rwa [← hZ10conj] at h
  have hz'2 : z' ^ 2 = 1 := hZ10el.2 z' hz10

  obtain ⟨hc4, hne1⟩ := commutator_conj_mem_Z_four C hH h12 hz0 hz1 hz10 hz10_1
  have hc6 := commutator_conj_mem_Z_six C hH h12 hz0 hz1 hz10
  obtain ⟨hzy, hwz⟩ := commutator_conj_eq_pow_four hz2 hz'2
  have hmem_bot : ⁅z, z' * z * z'⁻¹⁆ ∈ (⊥ : Subgroup G) := by
    rw [← Z_four_inf_Z_six C h12]
    exact Subgroup.mem_inf.mpr ⟨hc4, by rw [hzy, ← hwz]; exact hc6⟩
  exact hne1 (Subgroup.mem_bot.mp hmem_bot)

end Setup

end CFSG.Quasithin.St84

end
