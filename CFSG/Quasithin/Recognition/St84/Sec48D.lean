module

public import CFSG.Quasithin.Recognition.St84.Sec48C
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
public import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD
public import CFSG.Quasithin.Recognition.St84.Sec4QuotA
public import CFSG.Quasithin.Recognition.St84.Sec6S5

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

abbrev QA : Subgroup G := X.Q 1 ⊓ X.Q (-1)

abbrev QD : Subgroup G := X.Q 0 ⊓ Subgroup.centralizer (X.Ki 0 : Set G)

theorem inf_Gi_le_normalizer_inf_Q :
    X.Gi 0 ⊓ X.Gi 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G) :=
  CFSG.Quasithin.F7.le_normalizer_inf
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
    (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)))

variable {r d : ℕ}

variable {X}

variable (X) in
theorem s48_12 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : r = 8 ∧ d = 3 := by
  have h2 := (X.s48_2 C).2.1
  have h9 := X.s48_9 C hH
  have hne := X.s48_r_ne_12 C hH
  have hr : r = 8 := h9.2.resolve_right hne
  have hd : d = 3 := by omega
  exact ⟨hr, hd⟩

namespace Comm48

private theorem mem_fixSet_iff_gi (U : Subgroup G) (j : ℤ) :
    j ∈ X.fixSet U ↔ U ≤ X.Gi j := by
  constructor
  · intro h g hg
    exact MulAction.mem_stabilizer_iff.mpr (h g hg)
  · intro h g hg
    exact MulAction.mem_stabilizer_iff.mp (h hg)

private theorem isPGroup_Z_four : IsPGroup 2 (X.Z 4) :=
  (pCoreOf_isPGroup' (X.Gi 4)).to_le (X.Z_le_Q 4)

private theorem isPGroup_Z_neg_four : IsPGroup 2 (X.Z (-4)) :=
  (pCoreOf_isPGroup' (X.Gi (-4))).to_le (X.Z_le_Q (-4))

private theorem card_Z_zero (C : X.Comm48 s r d) :
    Nat.card ↥(X.Z 0) = 2 ^ X.n 0 :=
  (X.s48_2 C).2.2.2.2.1

end Comm48

variable (X) in
open Comm48 in
theorem card_Z_four (C : X.Comm48 s r d) : Nat.card ↥(X.Z 4) = 2 ^ X.n 0 := by
  have hZ : X.Z 4 = conjSub (X.τ ^ (2 : ℤ)) (X.Z 0) := by
    have h := X.Z_add 2 0
    rw [show (0 : ℤ) + 2 * 2 = 4 by norm_num] at h
    exact h
  rw [hZ, card_conjSub]
  exact card_Z_zero C

namespace Comm48

private theorem card_Z_neg_four (C : X.Comm48 s r d) :
    Nat.card ↥(X.Z (-4)) = 2 ^ X.n 0 := by
  have hZ : X.Z (-4) = conjSub (X.τ ^ (-2 : ℤ)) (X.Z 0) := by
    have h := X.Z_add (-2) 0
    rw [show (0 : ℤ) + 2 * (-2) = -4 by norm_num] at h
    exact h
  rw [hZ, card_conjSub]
  exact card_Z_zero C

private theorem Z_zero_eq_pCoreOf (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 0 = pCoreOf 2 (X.arcStab (-4) 4) := by
  have h := (X.s48_2 C).2.2.2.1
  have hd : d = 3 := (X.s48_12 C hH).2
  rw [hd] at h
  simpa using h

private theorem hasB_zero_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.HasB 0 4 := by
  have h := (X.s48_2 C).1
  have hd : d + 1 = 4 := by
    have := (X.s48_12 C hH).2
    omega
  simpa [hd] using h

end Comm48

variable (X) in
open Comm48 in
theorem hasB_four_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.HasB 4 4 :=
  (X.hasB_iff_of_even (i := 4) (j := 0) (by norm_num) 4).mpr
    (hasB_zero_four C hH)

namespace Comm48

private theorem hasB_neg_four_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.HasB (-4) 4 :=
  (X.hasB_iff_of_even (i := -4) (j := 0) (by norm_num) 4).mpr
    (hasB_zero_four C hH)

private theorem hasB_one_three (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.HasB 1 3 := by
  have h := C.hasB
  rwa [(X.s48_12 C hH).2] at h

private theorem Z_four_inf_Q_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 4 ⊓ X.Q 0 = ⊥ := by
  have hB4 := X.hasB_four_four C hH
  have hr : r = 8 := (X.s48_12 C hH).1
  have hP : IsPGroup 2 ↥(X.Z 4 ⊓ X.Q 0) :=
    isPGroup_Z_four.to_le inf_le_left
  by_contra hne
  have hfix : X.Z 4 ⊓ X.Q 0 ≤ X.arcStab (-1) (-1 + 9) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    rw [mem_fixSet_iff_gi]
    rcases lt_or_ge j 0 with hlt | hge
    · have hj1 : j = -1 := by omega
      subst hj1
      exact inf_le_right.trans ((X.Q_le_Gi_adj 0).trans inf_le_left)
    · exact inf_le_left.trans (hB4.Z_le_Gi (j := j) (by omega))
  have h9 : 9 ≤ r := X.le_r_of_fixes C.hyp hP hne hfix
  omega

private theorem Z_neg_four_inf_Q_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z (-4) ⊓ X.Q 0 = ⊥ := by
  have hB4 := hasB_neg_four_four C hH
  have hr : r = 8 := (X.s48_12 C hH).1
  have hP : IsPGroup 2 ↥(X.Z (-4) ⊓ X.Q 0) :=
    isPGroup_Z_neg_four.to_le inf_le_left
  by_contra hne
  have hfix : X.Z (-4) ⊓ X.Q 0 ≤ X.arcStab (-8) (-8 + 9) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    rw [mem_fixSet_iff_gi]
    by_cases hge : 0 ≤ j
    · have hj01 : j = 0 ∨ j = 1 := by omega
      rcases hj01 with hj0 | hj0
      · subst hj0
        exact inf_le_right.trans (X.Q_le_Gi 0)
      · subst hj0
        exact inf_le_right.trans ((X.Q_le_Gi_adj 0).trans inf_le_right)
    · exact inf_le_left.trans (hB4.Z_le_Gi (j := j) (by omega))
  have h9 : 9 ≤ r := X.le_r_of_fixes C.hyp hP hne hfix
  omega

private theorem Z_one_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 1 = X.Z 0 ⊔ X.Z 2 :=
  (X.s48_4' C hH).2.1

private theorem Z_zero_inf_Z_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 0 ⊓ X.Z 2 = ⊥ :=
  (X.s48_4' C hH).2.2.1

private theorem Z_two_le_Z_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 2 ≤ X.Z 1 := by
  rw [Z_one_eq C hH]
  exact le_sup_right

private theorem Z_three_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 3 = X.Z 2 ⊔ X.Z 4 := by
  have h := congrArg (conjSub X.τ) (Z_one_eq C hH)
  rw [conjSub_sup] at h
  have h1 : conjSub X.τ (X.Z 1) = X.Z 3 := by
    have h' := (X.Z_add 1 1).symm
    simpa using h'
  have h0 : conjSub X.τ (X.Z 0) = X.Z 2 := by
    have h' := (X.Z_add 1 0).symm
    simpa using h'
  have h2 : conjSub X.τ (X.Z 2) = X.Z 4 := by
    have h' := (X.Z_add 1 2).symm
    simpa using h'
  rwa [h1, h0, h2] at h

private theorem conjSub_tau_Vk_zero : conjSub (X.τ ^ (1 : ℤ)) (X.Vk 0) = X.Vk 2 := by
  rw [← X.Vk_add 1 0]; norm_num

private theorem Vk_two_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 2 = X.Z 1 ⊔ X.Z 4 := by
  have h8 := (X.s48_8 C hH).1
  rw [← conjSub_tau_Vk_zero, h8, conjSub_sup]
  have h1 : conjSub (X.τ ^ (1 : ℤ)) (X.Z 1) = X.Z 3 := by
    simpa using (X.Z_add 1 1).symm
  have hm : conjSub (X.τ ^ (1 : ℤ)) (X.Z (-1)) = X.Z 1 := by
    simpa using (X.Z_add 1 (-1)).symm
  rw [h1, hm, Z_three_eq C hH]
  have hZ2Z1 : X.Z 2 ≤ X.Z 1 := Z_two_le_Z_one C hH
  rw [sup_assoc, sup_comm (X.Z 4) (X.Z 1), ← sup_assoc, sup_comm (X.Z 2) (X.Z 1),
    sup_eq_left.mpr hZ2Z1]

private theorem Z_one_inf_Z_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 1 ⊓ X.Z 4 = ⊥ := by
  have hV : X.Vk 0 ≤ X.Q 0 ⊓ X.Q 1 := (X.s48_8 C hH).2.2.2.1
  have hZ1V : X.Z 1 ≤ X.Vk 0 := by
    rw [(X.s48_8 C hH).1]
    exact le_sup_left
  have hZ1Q0 : X.Z 1 ≤ X.Q 0 := hZ1V.trans (hV.trans inf_le_left)
  exact le_bot_iff.mp (calc X.Z 1 ⊓ X.Z 4 ≤ X.Q 0 ⊓ X.Z 4 := inf_le_inf hZ1Q0 le_rfl
    _ = X.Z 4 ⊓ X.Q 0 := inf_comm _ _
    _ = ⊥ := Z_four_inf_Q_zero C hH)

private theorem Vk_two_inf_Q_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 2 ⊓ X.Q 0 = X.Z 1 := by
  have hV : X.Vk 0 ≤ X.Q 0 ⊓ X.Q 1 := (X.s48_8 C hH).2.2.2.1
  have hZ1Q0 : X.Z 1 ≤ X.Q 0 := by
    rw [(X.s48_8 C hH).1] at hV
    exact (le_sup_left : X.Z 1 ≤ X.Z 1 ⊔ X.Z (-1)).trans (hV.trans inf_le_left)
  have hZ4N : X.Z 4 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hxG : x ∈ X.Gi 1 := (X.hasB_four_four C hH).Z_le_Gi (j := 1) (by omega) hx
    exact X.Z_normal 1 x hxG
  have hded := Subgroup.inf_sup_assoc_of_le (H := X.Z 4) (K := X.Q 0) (N := X.Z 1)
    hZ4N hZ1Q0
  rw [Vk_two_eq C hH, inf_comm]
  rw [show X.Z 1 ⊔ X.Z 4 = X.Z 4 ⊔ X.Z 1 from sup_comm _ _]
  rw [← hded, inf_comm (X.Q 0) (X.Z 4), Z_four_inf_Q_zero C hH, bot_sup_eq]

private theorem Vk_two_le_Gi (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 2 ≤ X.Gi 0 ⊓ X.Gi 1 := by
  rw [Vk_two_eq C hH]
  have hB4 := X.hasB_four_four C hH
  have h1 : X.Z 1 ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf ((X.Z_le_Q 1).trans ((X.Q_le_Gi_adj 1).trans inf_le_left)) (X.Z_le_Gi 1)
  have h40 : X.Z 4 ≤ X.Gi 0 := hB4.Z_le_Gi (j := 0) (by omega)
  have h41 : X.Z 4 ≤ X.Gi 1 := hB4.Z_le_Gi (j := 1) (by omega)
  have h4 : X.Z 4 ≤ X.Gi 0 ⊓ X.Gi 1 := le_inf h40 h41
  exact sup_le h1 h4

private theorem QA_le_E1 : X.QA ≤ X.Q 0 ⊓ X.Q 1 :=
  le_inf ((inf_comm (X.Q 1) (X.Q (-1))).le.trans X.Q_neg_one_inf_Q_one_le_Q_zero) inf_le_left

private theorem Z_neg_one_le_Q_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z (-1) ≤ X.Q 1 := by
  have hB : X.HasB (-1) 3 :=
    (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) 3).mpr
      (hasB_one_three C hH)
  exact X.Z_le_Q_of_lt hB (j := 1) (by norm_num)

private theorem Z_one_le_Q_neg_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 1 ≤ X.Q (-1) :=
  X.Z_le_Q_of_lt (hasB_one_three C hH) (j := -1) (by norm_num)

private theorem Vk_zero_le_QA (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 0 ≤ X.QA := by
  rw [(X.s48_8 C hH).1]
  exact sup_le (le_inf (X.Z_le_Q 1) (Z_one_le_Q_neg_one C hH))
    (le_inf (Z_neg_one_le_Q_one C hH) (X.Z_le_Q (-1)))

private theorem commutator_Vk_two_E1_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅X.Vk 2, X.Q 0 ⊓ X.Q 1⁆ ≤ X.Z 1 := by
  have hE1G2 : X.Q 0 ⊓ X.Q 1 ≤ X.Gi 2 :=
    inf_le_right.trans (fun x hx => (X.Q_le_Gi_adj 1 hx).2)
  have hE1N : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.normalizer (X.Vk 2 : Set G) :=
    hE1G2.trans (X.Gi_le_normalizer_Vk 2)
  have hV2N : X.Vk 2 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G) :=
    (Vk_two_le_Gi C hH).trans X.inf_Gi_le_normalizer_inf_Q
  have hEq : X.Vk 2 ⊓ (X.Q 0 ⊓ X.Q 1) = X.Z 1 := by
    rw [← inf_assoc, Vk_two_inf_Q_zero C hH, inf_eq_left.mpr (X.Z_le_Q 1)]
  exact (CFSG.Quasithin.F7.commutator_le_inf_of_normalizes hV2N hE1N).trans hEq.le

private theorem commutator_QA_Vk_two_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ⁅X.QA, X.Vk 2⁆ ≤ X.Vk 0 := by
  calc ⁅X.QA, X.Vk 2⁆ ≤ ⁅X.Q 0 ⊓ X.Q 1, X.Vk 2⁆ :=
        Subgroup.commutator_mono QA_le_E1 le_rfl
    _ = ⁅X.Vk 2, X.Q 0 ⊓ X.Q 1⁆ := Subgroup.commutator_comm _ _
    _ ≤ X.Z 1 := commutator_Vk_two_E1_le C hH
    _ ≤ X.Vk 0 := by
        rw [(X.s48_8 C hH).1]
        exact le_sup_left

private theorem commutator_QA_Z_four_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ⁅X.QA, X.Z 4⁆ ≤ X.Vk 0 :=
  (Subgroup.commutator_mono le_rfl (by rw [Vk_two_eq C hH]; exact le_sup_right)).trans
    (commutator_QA_Vk_two_le C hH)

private theorem exists_reflection_data (C : X.Comm48 s r d) :
    ∃ t ∈ oTwoRes (X.L 0) ⊓ Subgroup.normalizer (X.K : Set G),
      ∀ m : ℤ, t • X.vert m = X.vert (-m) := by
  obtain ⟨t, ht, hrefl, -⟩ := X.exists_reflection_oTwoRes C.hyp 0
  exact ⟨t, ht, by simpa using hrefl⟩

private theorem commutator_QA_Z_neg_four_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅X.QA, X.Z (-4)⁆ ≤ X.Vk 0 := by
  obtain ⟨t, -, hrefl⟩ := exists_reflection_data C
  have hZ4 : conjSub t (X.Z 4) = X.Z (-4) := (X.Z_smul X (hrefl 4)).symm
  have hZ1 : conjSub t (X.Z 1) = X.Z (-1) := (X.Z_smul X (hrefl 1)).symm
  have hZm1 : conjSub t (X.Z (-1)) = X.Z 1 := by
    have h := X.Z_smul X (hrefl (-1))
    simpa using h.symm
  have hQA : conjSub t X.QA = X.QA := by
    have h1 : X.Q (-1) = conjSub t (X.Q 1) := X.Q_smul X (hrefl 1)
    have hm : X.Q 1 = conjSub t (X.Q (-1)) := X.Q_smul X (hrefl (-1))
    rw [Setup.QA, conjSub_inf, ← h1, ← hm, inf_comm]
  have hV0 : conjSub t (X.Vk 0) = X.Vk 0 := by
    rw [(X.s48_8 C hH).1, conjSub_sup, hZ1, hZm1, sup_comm]
  have h := conjSub_mono t (commutator_QA_Z_four_le C hH)
  rw [← conjSub_commutator, hQA, hZ4, hV0] at h
  exact h

private theorem Q_zero_le_normalizer_QA : X.Q 0 ≤ Subgroup.normalizer (X.QA : Set G) := by
  have h1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) := by
    refine (show X.Q 0 ≤ X.Gi 1 from ?_).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
    simpa using ((X.Q_le_Gi_adj 0).trans inf_le_right)
  have h2 : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) := by
    refine (show X.Q 0 ≤ X.Gi (-1) from ?_).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
    simpa using ((X.Q_le_Gi_adj 0).trans inf_le_left)
  exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem K_le_normalizer_QA : X.K ≤ Subgroup.normalizer (X.QA : Set G) := by
  have h1 : X.K ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have h2 : X.K ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    (X.K_le_Gi (-1)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
  exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem L_zero_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.L 0 = X.Z 4 ⊔ X.Z (-4) ⊔ X.Q 0 := by
  have hB4 := X.hasB_four_four C hH
  have hBm4 := hasB_neg_four_four C hH
  have hZ4G0 : X.Z 4 ≤ X.Gi 0 := hB4.Z_le_Gi (j := 0) (by omega)
  have hZ4G1 : X.Z 4 ≤ X.Gi 1 := hB4.Z_le_Gi (j := 1) (by omega)
  have hZmG0 : X.Z (-4) ≤ X.Gi 0 := hBm4.Z_le_Gi (j := 0) (by omega)
  have hZmGm1 : X.Z (-4) ≤ X.Gi (-1) := hBm4.Z_le_Gi (j := -1) (by omega)
  have hA : X.Z 4 ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup isPGroup_Z_four hZ4G0
  have hB : X.Z (-4) ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup isPGroup_Z_neg_four hZmG0
  have hAidx : (X.Z 4 ⊓ X.Q 0).relIndex (X.Z 4) = 2 ^ X.n 0 := by
    rw [Z_four_inf_Q_zero C hH, Subgroup.relIndex_bot_left, X.card_Z_four C]
  have hBidx : (X.Z (-4) ⊓ X.Q 0).relIndex (X.Z (-4)) = 2 ^ X.n 0 := by
    rw [Z_neg_four_inf_Q_zero C hH, Subgroup.relIndex_bot_left, card_Z_neg_four C]
  have hb : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h := (X.adj (-1)).symm
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hab : X.vert 1 ≠ X.vert (-1) := by
    intro h
    have := X.vert_injective h
    omega
  exact X.L_eq_sup_of_fixes 0 (X.adj 0) hb hab hA hB hZ4G1 hZmGm1 hAidx hBidx

private theorem Gi_zero_eq_L_sup_K : X.Gi 0 = X.L 0 ⊔ X.K := by
  have hf : X.Gi 0 ⊓ X.Gi 1 ⊔ X.L 0 = X.Gi 0 :=
    frattini_oTwoPrime X.hyp (X.adj 0)
  have hKS : X.K ⊔ X.edgeSylow 0 = X.Gi 0 ⊓ X.Gi 1 := X.K_sup_edgeSylow 0
  have hSL : X.edgeSylow 0 ≤ X.L 0 := X.edgeSylow_le_L 0
  rw [← hf, ← hKS, sup_assoc, sup_eq_right.mpr hSL, sup_comm]

private theorem QA_normal (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Gi 0 ≤ Subgroup.normalizer (X.QA : Set G) := by
  have hZ4N : X.Z 4 ≤ Subgroup.normalizer (X.QA : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((commutator_QA_Z_four_le C hH).trans (Vk_zero_le_QA C hH))
  have hZm4N : X.Z (-4) ≤ Subgroup.normalizer (X.QA : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((commutator_QA_Z_neg_four_le C hH).trans (Vk_zero_le_QA C hH))
  have hL0N : X.L 0 ≤ Subgroup.normalizer (X.QA : Set G) := by
    rw [L_zero_eq C hH]
    exact sup_le (sup_le hZ4N hZm4N) Q_zero_le_normalizer_QA
  rw [Gi_zero_eq_L_sup_K]
  exact sup_le hL0N K_le_normalizer_QA

private theorem Z_one_le_QA (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 1 ≤ X.QA :=
  le_inf (X.Z_le_Q 1) (Z_one_le_Q_neg_one C hH)

private theorem edgeSylow_zero_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.edgeSylow 0 = X.Z 4 ⊔ X.Q 0 := by
  have hB4 := X.hasB_four_four C hH
  have hK : X.K ≤ Subgroup.normalizer (X.Z 4 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 4 k (X.K_le_Gi 4 hk)
  have h41 : X.Z 4 ≤ X.Q 1 := X.Z_le_Q_of_lt hB4 (j := 1) (by norm_num)
  have hZ4S : X.Z 4 ≤ X.edgeSylow 0 :=
    h41.trans (by simpa using X.Q_le_edgeSylow (i := 0))
  have hnot : ¬ X.Z 4 ≤ X.Q 0 := by
    intro hle
    have hbot : X.Z 4 = ⊥ := by
      have h := Z_four_inf_Q_zero C hH
      rwa [inf_eq_left.mpr hle] at h
    have hc := X.card_Z_four C
    rw [hbot, Subgroup.card_bot] at hc
    have hlt : 1 < 2 ^ X.n 0 := Nat.one_lt_two_pow (by have := C.hyp.two_le_n 0; omega)
    omega
  exact (X.sup_Q_eq_edgeSylow_of_left_gen (i := 0) (A := X.Z 4)
    (inf_le_left.trans hK) hZ4S hnot).symm

private theorem commutator_Q_zero_edgeSylow_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅⁅X.Q 0, X.edgeSylow 0⁆, X.edgeSylow 0⁆ ≤ X.QA := by
  have hS := edgeSylow_zero_eq C hH
  have hB4 := X.hasB_four_four C hH
  have hZ4G0 : X.Z 4 ≤ X.Gi 0 := hB4.Z_le_Gi (j := 0) (by omega)
  have hZ4G1 : X.Z 4 ≤ X.Gi 1 := hB4.Z_le_Gi (j := 1) (by omega)
  have hZ4Q1 : X.Z 4 ≤ X.Q 1 := X.Z_le_Q_of_lt hB4 (j := 1) (by norm_num)
  have hQ0Z4 : ⁅X.Q 0, X.Z 4⁆ ≤ X.Q 0 ⊓ X.Q 1 := by
    refine le_inf ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hZ4G0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
    · refine (Subgroup.commutator_mono le_rfl hZ4Q1).trans ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((show X.Q 0 ≤ X.Gi 1 from by
            simpa using ((X.Q_le_Gi_adj 0).trans inf_le_right)).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)))
  have hQ0' : ⁅X.Q 0, X.Q 0⁆ ≤ X.QA := by
    have h := (X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0).2.2.1
    simpa [Setup.QA, inf_comm] using h
  have hZ4E1 : X.Z 4 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G) :=
    (le_inf hZ4G0 hZ4G1).trans X.inf_Gi_le_normalizer_inf_Q
  have hQ0E1 : X.Q 0 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G) :=
    (le_inf (X.Q_le_Gi 0) (show X.Q 0 ≤ X.Gi 1 from by
      simpa using ((X.Q_le_Gi_adj 0).trans inf_le_right))).trans X.inf_Gi_le_normalizer_inf_Q
  have hQ0S : ⁅X.Q 0, X.edgeSylow 0⁆ ≤ X.Q 0 ⊓ X.Q 1 := by
    rw [hS]
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (Y := X.Q 0) (A := X.Z 4)
      (B := X.Q 0) (N := X.Q 0 ⊓ X.Q 1) hZ4E1 hQ0E1 hQ0Z4 (hQ0'.trans QA_le_E1)
  have hZ4NA : X.Z 4 ≤ Subgroup.normalizer (X.QA : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((commutator_QA_Z_four_le C hH).trans (Vk_zero_le_QA C hH))
  have hE1V2 : ⁅X.Q 0 ⊓ X.Q 1, X.Vk 2⁆ ≤ X.Z 1 := by
    rw [Subgroup.commutator_comm]
    exact commutator_Vk_two_E1_le C hH
  have hE1Z4 : ⁅X.Q 0 ⊓ X.Q 1, X.Z 4⁆ ≤ X.QA := by
    have h := (Subgroup.commutator_mono le_rfl
      (show X.Z 4 ≤ X.Vk 2 from by rw [Vk_two_eq C hH]; exact le_sup_right)).trans hE1V2
    exact h.trans (Z_one_le_QA C hH)
  have hE1Q0 : ⁅X.Q 0 ⊓ X.Q 1, X.Q 0⁆ ≤ X.QA :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans hQ0'
  have hKN : ⁅⁅X.Q 0, X.edgeSylow 0⁆, X.Z 4⁆ ≤ X.QA :=
    (Subgroup.commutator_mono hQ0S le_rfl).trans hE1Z4
  have hLN : ⁅⁅X.Q 0, X.edgeSylow 0⁆, X.Q 0⁆ ≤ X.QA :=
    (Subgroup.commutator_mono hQ0S le_rfl).trans hE1Q0
  rw [hS] at hKN hLN ⊢
  exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
    (Y := ⁅X.Q 0, X.Z 4 ⊔ X.Q 0⁆) (A := X.Z 4) (B := X.Q 0) (N := X.QA) hZ4NA
    Q_zero_le_normalizer_QA hKN hLN

private theorem exists_nontrivial_action_QA (C : X.Comm48 s r d) :
    ∃ l ∈ X.L 0, ∃ e ∈ X.Q 0, ⁅l, e⁆ ∉ X.QA := by
  have h4 : 4 ≤ s := by have := C.hyp.five_le; omega
  have hnot := (X.Q_quot_of_normal_general C.hyp.char C.hyp.sing h4).2.2.2.1
  have hA_le_E : X.QA ≤ X.Q 0 ⊓ X.Q (-1) :=
    le_inf (QA_le_E1.trans inf_le_left) inf_le_right
  have hne : ¬ ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ X.QA := by
    intro hle
    apply hnot
    constructor
    · have hQ0N : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) := by
        intro x hx
        exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi (-1))
          (((X.Q_le_Gi_adj 0) hx).1)
      have hQ0NE : X.Q 0 ≤
          Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
        (le_inf Subgroup.le_normalizer hQ0N).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      exact (inf_le_left : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0).trans hQ0NE
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr (hle.trans hA_le_E)
  have hne' : ¬ ∀ x ∈ X.Q 0 ⊓ X.Q (-1), ∀ y ∈ X.Q 1, ⁅x, y⁆ ∈ X.QA := by
    intro h
    exact hne (Subgroup.commutator_le.mpr h)
  push Not at hne'
  obtain ⟨x, hx, y, hy, hxy⟩ := hne'
  refine ⟨y, ?_, x, hx.1, ?_⟩
  · have hy' := le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi (0 + 1)))
      ((X.Q_le_Gi_adj (0 + 1)).trans inf_le_left) hy
    simpa using hy'
  · intro hmem
    apply hxy
    simpa [commutatorElement_inv] using (X.QA).inv_mem hmem

private theorem natPre_QA (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    NatPre (X.Gi 0) (X.L 0) (X.Q 0) X.QA (X.n 0) := by
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  have hQ := X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0
  have hA := QA_normal C hH
  have hcard : X.QA.relIndex (X.Q 0) = 2 ^ (2 * X.n 0) := by
    have h := hQ.2.2.2.1
    rw [show (0 : ℤ) + 1 = 1 by norm_num, C.n_one_eq hH] at h
    simpa [Setup.QA, inf_comm] using h
  have hsec : IsElemSec X.QA (X.Q 0) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [Setup.QA, inf_comm] using hQ.1
    · simpa [Setup.QA, inf_comm] using hQ.2.2.1
    · intro e he
      simpa [Setup.QA, inf_comm] using hQ.2.1 e he
  have hcore : ∀ q ∈ pCoreOf 2 (X.Gi 0), ∀ e ∈ X.Q 0, ⁅q, e⁆ ∈ X.QA := by
    intro q hq e he
    simpa [Setup.QA, inf_comm] using
      (Subgroup.commutator_le.mp hQ.2.2.1) q hq e he
  have hnontriv := exists_nontrivial_action_QA C
  exact
    { le := X.L_le_Gi 0
      norm_L := (Subgroup.normal_subgroupOf_iff_le_normalizer (X.L_le_Gi 0)).mp
        (X.hyp.isLocL2_oTwoPrime (X.vert 0)).normal
      norm_E := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi 0)
      norm_K := hA
      sec := hsec
      card := hcard
      core := hcore
      quot := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
      nontriv := hnontriv }

private theorem commutator_Q_one_Q_zero_le : ⁅X.Q 0, X.Q 1⁆ ≤ X.Q 0 := by
  have hQ1N : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.Q_le_Gi_adj 1).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQ1N

private theorem commutator_C_edgeSylow_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆, X.edgeSylow 0⁆ ≤ X.QA := by
  have hquad := commutator_Q_zero_edgeSylow_le C hH
  have hC_le : ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ ⁅X.Q 0, X.edgeSylow 0⁆ :=
    Subgroup.commutator_mono inf_le_left (X.Q_le_edgeSylow 0)
  exact (Subgroup.commutator_mono hC_le le_rfl).trans hquad

private theorem C_le_normalizer_QA (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ Subgroup.normalizer (X.QA : Set G) := by
  have hA := QA_normal C hH
  have hC_le_Qi : ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ X.Q 0 :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans commutator_Q_one_Q_zero_le
  exact (hC_le_Qi.trans (X.Q_le_Gi 0)).trans hA

private theorem comm_sup_QA_edgeSylow_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ X.QA, X.edgeSylow 0⁆ ≤ X.QA := by
  set C' : Subgroup G := ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ with hC'
  change ⁅C' ⊔ X.QA, X.edgeSylow 0⁆ ≤ X.QA
  have hA := QA_normal C hH
  have h2 : ⁅X.QA, X.edgeSylow 0⁆ ≤ X.QA := by
    refine Subgroup.le_normalizer_iff_commutator_le_left.mp ?_
    exact ((X.edgeSylow_le_L 0).trans (X.L_le_Gi 0)).trans hA
  have h1 : ⁅C', X.edgeSylow 0⁆ ≤ X.QA := by
    rw [hC']
    exact commutator_C_edgeSylow_le C hH
  have h1' : ⁅X.edgeSylow 0, C'⁆ ≤ X.QA := by
    rw [Subgroup.commutator_comm]
    exact h1
  have hCnorm : C' ≤ Subgroup.normalizer (X.QA : Set G) := by
    rw [hC']
    exact C_le_normalizer_QA C hH
  have h2' : ⁅X.edgeSylow 0, X.QA⁆ ≤ X.QA := by
    rw [Subgroup.commutator_comm]
    exact h2
  have hsup' : ⁅X.edgeSylow 0, C' ⊔ X.QA⁆ ≤ X.QA :=
    CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      hCnorm Subgroup.le_normalizer h1' h2'
  rw [Subgroup.commutator_comm]
  exact hsup'

private theorem Q_one_inf_Q_two_le_relCent (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Q 0 ⊓ X.Q 1 ≤ relCent (X.Q 0) X.QA (X.edgeSylow 0) := by
  have h4 : 4 ≤ s := by have := C.hyp.five_le; omega
  have hA := QA_normal C hH
  have hQnormA : X.Q 0 ≤ Subgroup.normalizer (X.QA : Set G) :=
    (X.Q_le_Gi 0).trans hA
  have hsup := comm_sup_QA_edgeSylow_le C hH
  have hDsub : X.Q 0 ⊓ X.Q 1 ≤ ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ X.QA := by
    have h := (X.Q_quot_of_normal_general C.hyp.char C.hyp.sing h4).2.2.2.2
    rw [show X.QA = X.Q (-1) ⊓ X.Q 1 by rw [Setup.QA, inf_comm]]
    exact h
  intro e he
  refine (mem_relCent hQnormA).mpr ⟨he.1, fun s hs => ?_⟩
  exact (Subgroup.commutator_le.mp hsup) e (hDsub he) s hs

private theorem two_pow_le_relIndex_QA_relCent (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    2 ^ X.n 0 ≤ X.QA.relIndex (relCent (X.Q 0) X.QA (X.edgeSylow 0)) := by
  have hA := QA_normal C hH
  have hQnormA : X.Q 0 ≤ Subgroup.normalizer (X.QA : Set G) :=
    (X.Q_le_Gi 0).trans hA
  have hDrel : X.QA.relIndex (X.Q 0 ⊓ X.Q 1) = 2 ^ X.n 0 := by
    have h := (X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0).2.2.2.2.1
    rw [show (0 : ℤ) + 1 = 1 by norm_num, C.n_one_eq hH] at h
    simpa [Setup.QA, inf_comm] using h
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥(X.Q 0) :=
    Finite.of_injective (Subgroup.inclusion (X.Q_le_Gi 0)) (Subgroup.inclusion_injective _)
  haveI : Finite ↥(relCent (X.Q 0) X.QA (X.edgeSylow 0)) :=
    Finite.of_injective
      (Subgroup.inclusion (fun x hx => ((mem_relCent hQnormA).mp hx).1))
      (Subgroup.inclusion_injective _)
  have hle := Subgroup.relIndex_le_of_le_right (H := X.QA)
    (Q_one_inf_Q_two_le_relCent C hH)
    Subgroup.index_ne_zero_of_finite
  rwa [hDrel] at hle

private theorem natQuot_QA (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : NatQuot (X.L 0) (X.Q 0) X.QA (X.n 0) := by
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  exact natQuot_of_two_pow_le (C.hyp.two_le_n 0) (natPre_QA C hH) (X.Q_le_L 0)
    (X.isSylowTwoOf_edgeSylow_L 0) (two_pow_le_relIndex_QA_relCent C hH)

private theorem L_zero_le_normalizer_conj_sup :
    X.L 0 ≤ Subgroup.normalizer
      ((⨆ (g : G) (_ : g ∈ X.L 0), conjSub g (X.Z 4 ⊔ X.Z (-4)) : Subgroup G) : Set G) := by
  let N : Subgroup G := ⨆ (g : G) (_ : g ∈ X.L 0), conjSub g (X.Z 4 ⊔ X.Z (-4))
  change X.L 0 ≤ Subgroup.normalizer (N : Set G)
  intro g hg
  rw [mem_normalizer_iff_conjSub]
  have hstep : ∀ g' ∈ X.L 0, conjSub g' N ≤ N := by
    intro g' hg'
    change conjSub g' (⨆ (h : G), ⨆ (_ : h ∈ X.L 0), conjSub h (X.Z 4 ⊔ X.Z (-4))) ≤ N
    rw [conjSub_iSup]
    refine iSup_le fun h => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hh => ?_
    rw [← conjSub_mul]
    exact le_iSup_of_le (g' * h) (le_iSup_of_le ((X.L 0).mul_mem hg' hh) le_rfl)
  refine le_antisymm (hstep g hg) ?_
  have h := conjSub_mono g (hstep g⁻¹ ((X.L 0).inv_mem hg))
  rwa [conjSub_inv_conjSub] at h

private theorem comm_QA_oTwoRes (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ⁅X.QA, oTwoRes (X.L 0)⁆ ≤ X.Vk 0 := by
  have hB4 := X.hasB_four_four C hH
  have hZ4G0 : X.Z 4 ≤ X.Gi 0 := hB4.Z_le_Gi (j := 0) (by omega)
  have hZm4G0 : X.Z (-4) ≤ X.Gi 0 :=
    (hasB_neg_four_four C hH).Z_le_Gi (j := 0) (by omega)
  let N : Subgroup G := ⨆ (g : G) (_ : g ∈ X.L 0), conjSub g (X.Z 4 ⊔ X.Z (-4))
  have hTleL : X.Z 4 ⊔ X.Z (-4) ≤ X.L 0 :=
    sup_le (le_oTwoPrime_of_isPGroup isPGroup_Z_four hZ4G0)
      (le_oTwoPrime_of_isPGroup isPGroup_Z_neg_four hZm4G0)
  have hNnorm : X.L 0 ≤ Subgroup.normalizer (N : Set G) :=
    L_zero_le_normalizer_conj_sup (X := X)
  have hTN : X.Z 4 ⊔ X.Z (-4) ≤ N := by
    have h : conjSub (1 : G) (X.Z 4 ⊔ X.Z (-4)) ≤ N := by
      apply le_iSup_of_le (1 : G)
      apply le_iSup_of_le (show (1 : G) ∈ X.L 0 from (X.L 0).one_mem)
      exact le_rfl
    simpa only [conjSub_one] using h
  have hsup : X.L 0 ≤ N ⊔ X.Q 0 := by
    rw [L_zero_eq C hH]
    exact sup_le (hTN.trans le_sup_left) le_sup_right
  have hQL : X.Q 0 ≤ X.L 0 := X.Q_le_L 0
  have hO2 : oTwoRes (X.L 0) ≤ N :=
    CFSG.Quasithin.F53.Stellmacher.S43.oTwoRes_le_of_cover hNnorm
      (pCoreOf_isPGroup' (X.Gi 0)) hQL
      fun x hx => (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
        (hQL.trans hNnorm)).mp (hsup hx)
  have hV0norm : X.Gi 0 ≤ Subgroup.normalizer (X.Vk 0 : Set G) := X.Gi_le_normalizer_Vk 0
  have hV0fix : ∀ g ∈ X.L 0, conjSub g (X.Vk 0) = X.Vk 0 := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hV0norm (X.L_le_Gi 0 hg))
  have hbase : ⁅X.QA, X.Z 4 ⊔ X.Z (-4)⁆ ≤ X.Vk 0 :=
    CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (Y := X.QA) (A := X.Z 4)
      (B := X.Z (-4)) (N := X.Vk 0) (hZ4G0.trans hV0norm) (hZm4G0.trans hV0norm)
      (commutator_QA_Z_four_le C hH) (commutator_QA_Z_neg_four_le C hH)
  have hnorm : ∀ g ∈ X.L 0,
      conjSub g (X.Z 4 ⊔ X.Z (-4)) ≤ Subgroup.normalizer (X.Vk 0 : Set G) := by
    intro g hg x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have hxL : g * t * g⁻¹ ∈ X.L 0 :=
      (X.L 0).mul_mem ((X.L 0).mul_mem hg (hTleL ht)) ((X.L 0).inv_mem hg)
    exact hV0norm (X.L_le_Gi 0 hxL)
  have hcomm : ∀ g ∈ X.L 0, ⁅X.QA, conjSub g (X.Z 4 ⊔ X.Z (-4))⁆ ≤ X.Vk 0 := by
    intro g hg
    have hQA : conjSub g X.QA = X.QA :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (QA_normal C hH (X.L_le_Gi 0 hg))
    rw [← hQA, conjSub_commutator, ← hV0fix g hg]
    exact conjSub_mono g hbase
  have hNcom : ⁅X.QA, N⁆ ≤ X.Vk 0 :=
    CFSG.GroupTheory.commutator_iSup_right_le_of_le_normalizer
      (fun g => iSup_le fun hg => hnorm g hg)
      (fun g => CFSG.GroupTheory.commutator_iSup_right_le_of_le_normalizer
        (fun hg => hnorm g hg) (fun hg => hcomm g hg))
  exact (Subgroup.commutator_mono le_rfl hO2).trans hNcom

private theorem four_le_two_pow_n (C : X.Comm48 s r d) : 4 ≤ 2 ^ X.n 0 := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (C.hyp.two_le_n 0)

private theorem odd_card_Ki_zero (C : X.Comm48 s r d) :
    Odd (Nat.card ↥(X.Ki 0)) := by
  rw [X.card_Ki 0]
  exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)

private theorem card_Ki_zero_ne_one (C : X.Comm48 s r d) :
    Nat.card ↥(X.Ki 0) ≠ 1 := by
  rw [X.card_Ki 0]
  have h4 := four_le_two_pow_n C
  omega

private theorem Ki_zero_ne_bot (C : X.Comm48 s r d) : X.Ki 0 ≠ ⊥ := by
  intro hbot
  have hc := card_Ki_zero_ne_one C
  rw [hbot, Subgroup.card_bot] at hc
  exact hc rfl

private theorem QD_le_QA (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.QD ≤ X.QA := by
  obtain ⟨k, hkK, hk1, hk3, -⟩ := X.exists_generator_Ki 0 (C.hyp.two_le_n 0)
  have hkL : k ∈ X.L 0 := hkK.2
  have hodd : Odd (orderOf k) := by
    rw [hk3]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)
  have hkQ : k ∉ X.Q 0 := by
    intro hkQ0
    have hmem : k ∈ X.K ⊓ X.edgeSylow 0 :=
      ⟨hkK.1, (X.Q_le_edgeSylow_left 0) hkQ0⟩
    rw [X.K_inf_edgeSylow 0, Subgroup.mem_bot] at hmem
    exact hk1 hmem
  have hNA := natQuot_QA C hH
  intro d hd
  obtain ⟨hdQ, hdC⟩ := Subgroup.mem_inf.mp hd
  refine hNA.fpf k hkL hodd hkQ d hdQ ?_
  have hcomm : ⁅d, k⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hdC k hkK).symm
  rw [hcomm]
  exact X.QA.one_mem

private theorem QA_coprime_decomp (C : X.Comm48 s r d) :
    X.QA ≤ ⁅X.QA, X.Ki 0⁆ ⊔
      (X.QA ⊓ Subgroup.centralizer ((X.Ki 0 : Subgroup G) : Set G)) := by
  let P : Subgroup G := X.QA
  let L : Subgroup G := X.Ki 0
  have hPL : L ≤ Subgroup.normalizer (P : Set G) :=
    (inf_le_left : X.Ki 0 ≤ X.K).trans K_le_normalizer_QA
  have hP2 : IsPGroup 2 ↥P := (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  have hPle : P ≤ X.Gi 1 := inf_le_left.trans (X.Q_le_Gi 1)
  haveI hPfin : Finite ↥P := finite_of_le_stabilizer X.hyp (H := P) hPle
  haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hsolv : Group.IsSolvable ↥P := inferInstance
  have hLle : L ≤ X.Gi 0 := inf_le_right.trans (X.L_le_Gi 0)
  haveI hLfin : Finite ↥L := finite_of_le_stabilizer X.hyp (H := L) hLle
  have hLcard : Nat.card ↥L = 2 ^ X.n 0 - 1 := X.card_Ki 0
  have hcop : Nat.Coprime (Nat.card ↥L) (Nat.card ↥P) := by
    obtain ⟨m, hm⟩ := hP2.exists_card_eq
    rw [hm, hLcard]
    exact (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)).coprime_two_right.pow_right m
  exact CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hPL hcop hsolv

private theorem QA_le_QD_sup_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.QA ≤ X.QD ⊔ X.Vk 0 := by
  have h1 := QA_coprime_decomp C
  have hoddKi : Odd (Nat.card ↥(X.Ki 0)) := odd_card_Ki_zero C
  have hKO : X.Ki 0 ≤ oTwoRes (X.L 0) :=
    le_oTwoRes_of_odd_card (P := X.Ki 0) (X := X.L 0) inf_le_right hoddKi
  have h2 : ⁅X.QA, X.Ki 0⁆ ≤ X.Vk 0 :=
    (Subgroup.commutator_mono le_rfl hKO).trans (comm_QA_oTwoRes C hH)
  have h3 : X.QA ⊓ Subgroup.centralizer ((X.Ki 0 : Subgroup G) : Set G) ≤ X.QD := by
    rw [Setup.QD]
    exact inf_le_inf_right _ (QA_le_E1.trans inf_le_left)
  exact h1.trans (sup_le (h2.trans le_sup_right) (h3.trans le_sup_left))

private theorem K_le_normalizer_Z_zero : X.K ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
  fun k hk => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 k (X.K_le_Gi 0 hk))

private theorem Z_zero_le_centralizer_Ki_zero (C : X.Comm48 s r d) :
    X.Z 0 ≤ Subgroup.centralizer (X.Ki 0 : Set G) := by
  intro z hz
  have hzL : z ∈ centerOf (X.L 0) := (X.s48_0 C).2 ▸ hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzL).2 y hy.2

private theorem Z_two_inf_Z_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 2 ⊓ X.Z 4 = ⊥ := by
  refine le_bot_iff.mp ?_
  calc X.Z 2 ⊓ X.Z 4 ≤ X.Z 1 ⊓ X.Z 4 := inf_le_inf (Z_two_le_Z_one C hH) le_rfl
    _ = ⊥ := Z_one_inf_Z_four C hH

private theorem Vk_two_le_Q_two_three (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 2 ≤ X.Q 2 ⊓ X.Q 3 := by
  have h := conjSub_mono (X.τ ^ (1 : ℤ)) ((X.s48_8 C hH).2.2.2.1)
  have e2 : conjSub (X.τ ^ (1 : ℤ)) (X.Q 0) = X.Q 2 := by
    rw [← X.Q_add 1 0]; norm_num
  have e3 : conjSub (X.τ ^ (1 : ℤ)) (X.Q 1) = X.Q 3 := by
    rw [← X.Q_add 1 1]; norm_num
  rwa [conjSub_tau_Vk_zero, conjSub_inf, e2, e3] at h

private theorem Vk_two_le_normalizer_Z_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Vk 2 ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hvQ : v ∈ X.Q 2 := (Subgroup.mem_inf.mp (Vk_two_le_Q_two_three C hH hv)).1
  exact X.Z_normal 2 v (X.Q_le_Gi 2 hvQ)

private theorem natQuot_L2_Vk2_Z2 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : NatQuot (X.L 2) (X.Vk 2) (X.Z 2) (X.n 0) := by
  have h := NatQuot.conj ((X.s48_8 C hH).2.2.2.2.2.1) (X.τ ^ (1 : ℤ))
  have e1 : conjSub (X.τ ^ (1 : ℤ)) (X.L 0) = X.L 2 := by
    rw [← X.L_add 1 0]; norm_num
  have e2 : conjSub (X.τ ^ (1 : ℤ)) (X.Vk 0) = X.Vk 2 := by
    rw [← X.Vk_add 1 0]; norm_num
  have e3 : conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) = X.Z 2 := by
    rw [← X.Z_add 1 0]; norm_num
  rwa [e1, e2, e3] at h

private theorem commutator_Vk_two_Q_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ⁅X.Vk 2, X.Q 2⁆ = X.Z 2 := by
  have h := (X.s48_8 C hH).2.2.2.2.1
  have h' : conjSub (X.τ ^ (1 : ℤ)) ⁅X.Vk 0, X.Q 0⁆ =
      conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) := by rw [h]
  rw [← conjSub_commutator] at h'
  have e2 : conjSub (X.τ ^ (1 : ℤ)) (X.Q 0) = X.Q 2 := by
    rw [← X.Q_add 1 0]; norm_num
  have e3 : conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) = X.Z 2 := by
    rw [← X.Z_add 1 0]; norm_num
  rwa [conjSub_tau_Vk_zero, e2, e3] at h'

private theorem false_of_QD_le_two_not_three (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (h2 : X.QD ≤ X.Q 2) (h3 : ¬ X.QD ≤ X.Q 3) : False := by
  have hPD : IsPGroup 2 ↥X.QD := (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  have hE2 : X.QD ≤ X.edgeSylow 2 := h2.trans (X.Q_le_edgeSylow_left 2)
  have hPS3 : X.QD ⊔ X.Q 3 = X.edgeSylow 2 :=
    X.sup_Q_eq_edgeSylow_of_gen (i := 2) (A := X.QD)
      (inf_le_left.trans (X.K_le_normalizer_Q_inf_centralizer_Ki 0)) hE2 h3
  have hPU : X.QD ≤ Subgroup.centralizer (X.Ki 0 : Set G) := inf_le_right
  obtain ⟨hfix3, htrans3⟩ :=
    X.fix_nbrs_of_centralizes C.hyp.char 3 (U := X.Ki 0) (P := X.QD)
      (inf_le_left : X.Ki 0 ≤ X.K) hPD (Or.inr hPS3) hPU
  have hd : d = 3 := (X.s48_12 C hH).2
  have hPZ : IsPGroup 2 ↥(X.Z 0) := (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
  have hZ0E3 : X.Z 0 ≤ X.edgeSylow 3 := by
    have h := X.Z_le_Q_of_lt (i := 0) (d := 4) (hasB_zero_four C hH)
      (j := 3) (by norm_num)
    exact h.trans (X.Q_le_edgeSylow_left 3)
  have hnot4 : ¬ X.Z 0 ≤ X.Q 4 := by
    intro h
    have hbot : X.Z 0 ⊓ X.Q 4 = ⊥ := by
      have := (X.s48_2 C).2.2.2.2.2.2.1
      rwa [hd] at this
    have hZ0bot : X.Z 0 = ⊥ := by
      calc X.Z 0 = X.Z 0 ⊓ X.Q 4 := (inf_eq_left.mpr h).symm
        _ = ⊥ := hbot
    have hc := card_Z_zero C
    rw [hZ0bot, Subgroup.card_bot] at hc
    have h4 := four_le_two_pow_n C
    omega
  have hPS4 : X.Z 0 ⊔ X.Q 4 = X.edgeSylow 3 :=
    X.sup_Q_eq_edgeSylow_of_gen (i := 3) (A := X.Z 0)
      (inf_le_left.trans K_le_normalizer_Z_zero) hZ0E3 hnot4
  have hPUZ : X.Z 0 ≤ Subgroup.centralizer (X.Ki 0 : Set G) :=
    Z_zero_le_centralizer_Ki_zero C
  obtain ⟨hfix4, htrans4⟩ :=
    X.fix_nbrs_of_centralizes C.hyp.char 4 (U := X.Ki 0) (P := X.Z 0)
      (inf_le_left : X.Ki 0 ≤ X.K) hPZ (Or.inr hPS4) hPUZ
  have hKi0Gi : X.Ki 0 ≤ X.Gi 3 ⊓ X.Gi 4 :=
    le_inf ((inf_le_left : X.Ki 0 ≤ X.K).trans (X.K_le_Gi 3))
      ((inf_le_left : X.Ki 0 ≤ X.K).trans (X.K_le_Gi 4))
  have hbot : X.Ki 0 = ⊥ :=
    eq_bot_of_normalizer_trans X.hyp (X.adj 3) hKi0Gi htrans3 htrans4
  exact Ki_zero_ne_bot C hbot

private theorem QA_eq_QD_sup_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.QA = X.QD ⊔ X.Vk 0 :=
  le_antisymm (QA_le_QD_sup_Vk_zero C hH)
    (sup_le (QD_le_QA C hH) (Vk_zero_le_QA C hH))

private theorem QD_inf_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.QD ⊓ X.Vk 0 = X.Z 0 := by
  obtain ⟨k, hkK, hk1, hk3, -⟩ := X.exists_generator_Ki 0 (C.hyp.two_le_n 0)
  have hkL : k ∈ X.L 0 := hkK.2
  have hodd : Odd (orderOf k) := by
    rw [hk3]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)
  have hV0card : Nat.card ↥(X.Vk 0) = 2 ^ (3 * X.n 0) := (X.s48_8 C hH).2.1
  have hkV : k ∉ X.Vk 0 := by
    intro hkV0
    have hdvd := Subgroup.orderOf_dvd_natCard (X.Vk 0) hkV0
    rw [hV0card, hk3] at hdvd
    have hcop : Nat.Coprime (2 ^ X.n 0 - 1) (2 ^ (3 * X.n 0)) :=
      (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)).coprime_two_right.pow_right
        (3 * X.n 0)
    have hone := hcop.eq_one_of_dvd hdvd
    have h4 := four_le_two_pow_n C
    omega
  have hnatV := (X.s48_8 C hH).2.2.2.2.2.1
  have hV0Q : X.Vk 0 ≤ X.Q 0 := ((X.s48_8 C hH).2.2.2.1).trans inf_le_left
  refine le_antisymm ?_ ?_
  · intro e he
    obtain ⟨heQD, heV⟩ := Subgroup.mem_inf.mp he
    obtain ⟨heQ, heC⟩ := Subgroup.mem_inf.mp heQD
    refine hnatV.fpf k hkL hodd hkV e heV ?_
    have hcomm : ⁅e, k⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp heC k hkK).symm
    rw [hcomm]
    exact (X.Z 0).one_mem
  · intro z hz
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_inf.mpr ⟨X.Z_le_Q 0 hz, Z_zero_le_centralizer_Ki_zero C hz⟩
    · rw [(X.s48_8 C hH).1]
      exact ((X.s48_1 C).1.trans le_sup_left) hz

end Comm48

variable (X) in
open Comm48 in
theorem s48_13 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Vk 2 = X.Z 1 ⊔ X.Z 4 ∧ X.Vk 2 ⊓ X.Q 0 = X.Z 1 ∧
      X.Gi 0 ≤ Subgroup.normalizer (X.QA : Set G) ∧
      NatQuot (X.L 0) (X.Q 0) X.QA (X.n 0) ∧ ⁅X.QA, oTwoRes (X.L 0)⁆ ≤ X.Vk 0 ∧
      X.QA = X.QD ⊔ X.Vk 0 ∧ X.QD ⊓ X.Vk 0 = X.Z 0 :=
  ⟨Vk_two_eq C hH, Vk_two_inf_Q_zero C hH, QA_normal C hH,
    natQuot_QA C hH, comm_QA_oTwoRes C hH,
    QA_eq_QD_sup_Vk_zero C hH, QD_inf_Vk_zero C hH⟩

namespace Comm48

private theorem mem_normalizer_QD {t : G} (hQ : t ∈ Subgroup.normalizer (X.Q 0 : Set G))
    (hK : t ∈ Subgroup.normalizer (X.Ki 0 : Set G)) :
    t ∈ Subgroup.normalizer (X.QD : Set G) :=
  CFSG.Quasithin.F7.mem_normalizer_inf hQ
    (CFSG.Quasithin.B6.le_normalizer_centralizer le_rfl hK)

private theorem commutator_mem_Z_zero_of_mem_QD (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {t : G}
    (htO2 : t ∈ oTwoRes (X.L 0)) (hQDn : t ∈ Subgroup.normalizer (X.QD : Set G))
    {x : G} (hx : x ∈ X.QD) : ⁅x, t⁆ ∈ X.Z 0 := by
  have hxV : ⁅x, t⁆ ∈ X.Vk 0 :=
    Subgroup.commutator_le.mp (comm_QA_oTwoRes C hH) x (QD_le_QA C hH hx) t htO2
  have hxQD : ⁅x, t⁆ ∈ X.QD := by
    have h1 : t * x * t⁻¹ ∈ X.QD := (Subgroup.mem_normalizer_iff.mp hQDn x).mp hx
    have h1' : t * x⁻¹ * t⁻¹ ∈ X.QD := by
      have hinv := X.QD.inv_mem h1
      rwa [show (t * x * t⁻¹)⁻¹ = t * x⁻¹ * t⁻¹ by group] at hinv
    rw [commutatorElement_def, show x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) by group]
    exact X.QD.mul_mem hx h1'
  rw [← QD_inf_Vk_zero C hH]
  exact Subgroup.mem_inf.mpr ⟨hxQD, hxV⟩

private theorem Z_zero_le_QD_inf_L_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 0 ≤ X.QD ⊓ X.L 4 := by
  refine le_inf (le_inf (X.Z_le_Q 0) (Z_zero_le_centralizer_Ki_zero C)) ?_
  have hZ0G4 : X.Z 0 ≤ X.Gi 4 :=
    (hasB_zero_four C hH).Z_le_Gi (j := 4) (by omega)
  exact le_oTwoPrime_of_isPGroup
    ((pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)) hZ0G4

private theorem le_arcStab_neg_four_four_of_reflection {U : Subgroup G} {t : G}
    (hrefl : ∀ m : ℤ, t • X.vert m = X.vert (-m)) (hUt : conjSub t U = U)
    (hUGm1 : U ≤ X.Gi (-1)) (hU4 : U ≤ X.Gi 4) (hUarc1 : U ≤ X.arcStab (-1) 4) :
    U ≤ X.arcStab (-4) 4 := by
  refine X.le_arcStab_of_fixSet ?_
  intro j hj
  rw [Set.mem_Icc] at hj
  rw [mem_fixSet_iff_gi]
  intro u hu
  have hu1 : u ∈ X.Gi (-1) := hUGm1 hu
  have hu4 : u ∈ X.Gi 4 := hU4 hu
  by_cases hjm : j ≤ 1
  ·
    have htut : t * u * t⁻¹ ∈ U := by
      have hmem : t * u * t⁻¹ ∈ conjSub t U := mul_mem_conjSub hu
      rwa [hUt] at hmem
    have hk : (-j) ∈ Set.Icc (-1 : ℤ) 4 := by rw [Set.mem_Icc]; omega
    have hkfix : (t * u * t⁻¹) • X.vert (-j) = X.vert (-j) := by
      have h4 : (t * u * t⁻¹) ∈ X.arcStab (-1) 4 := hUarc1 htut
      unfold Setup.arcStab at h4
      rw [Fan86.mem_fixSet] at h4
      exact h4 (X.vert (-j)) ⟨-j, hk, rfl⟩
    have h1 : t⁻¹ • X.vert (-j) = X.vert j := by
      have h := congrArg (fun v => t⁻¹ • v) (hrefl j)
      simpa using h.symm
    have hkfix2 : t • (u • X.vert j) = t • X.vert j := by
      have e : t * u * t⁻¹ = (t * u) * t⁻¹ := by group
      have htj : X.vert (-j) = t • X.vert j := (hrefl j).symm
      rw [e, mul_smul, mul_smul, h1, htj] at hkfix
      exact hkfix
    have hcancel : u • X.vert j = X.vert j := by
      have := congrArg (fun v => t⁻¹ • v) hkfix2
      simpa using this
    exact MulAction.mem_stabilizer_iff.mpr hcancel
  · exact X.mem_Gi_of_between (g := u) hu1 hu4 (by omega) (by omega)

private theorem reflection_mem_normalizer_QD_inf_L_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {t : G}
    (htO2 : t ∈ oTwoRes (X.L 0)) (htK : t ∈ Subgroup.normalizer (X.K : Set G)) :
    t ∈ Subgroup.normalizer (X.QD ⊓ X.L 4 : Set G) := by
  have htG0 : t ∈ X.Gi 0 := X.L_le_Gi 0 (oTwoRes_le (X.L 0) htO2)
  have hQ0n : t ∈ Subgroup.normalizer (X.Q 0 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) htG0
  have hK0n : t ∈ Subgroup.normalizer (X.Ki 0 : Set G) :=
    CFSG.Quasithin.F7.mem_normalizer_inf htK (le_normalizer_oTwoPrime (X.Gi 0) htG0)
  have hQDn : t ∈ Subgroup.normalizer (X.QD : Set G) := mem_normalizer_QD hQ0n hK0n
  have hZ0U : X.Z 0 ≤ X.QD ⊓ X.L 4 := Z_zero_le_QD_inf_L_four C hH
  refine (Subgroup.mem_normalizer_iff (G := G) (H := X.QD ⊓ X.L 4)).mpr fun x => ⟨?_, ?_⟩
  · intro hx
    have hxQD : x ∈ X.QD := (inf_le_left : X.QD ⊓ X.L 4 ≤ X.QD) hx
    have hc : ⁅t, x⁆ ∈ X.Z 0 := by
      have h := commutator_mem_Z_zero_of_mem_QD C hH htO2 hQDn hxQD
      have he : ⁅t, x⁆ = ⁅x, t⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [he]
      exact (X.Z 0).inv_mem h
    have he : t * x * t⁻¹ = ⁅t, x⁆ * x := by
      rw [commutatorElement_def]; group
    rw [he]
    exact (X.QD ⊓ X.L 4).mul_mem (hZ0U hc) hx
  · intro hx
    have hyQD : t * x * t⁻¹ ∈ X.QD := (inf_le_left : X.QD ⊓ X.L 4 ≤ X.QD) hx
    have hc : ⁅t⁻¹, t * x * t⁻¹⁆ ∈ X.Z 0 := by
      have hcommZ' : ⁅t * x * t⁻¹, t⁻¹⁆ ∈ X.Z 0 :=
        commutator_mem_Z_zero_of_mem_QD C hH ((oTwoRes (X.L 0)).inv_mem htO2)
          ((Subgroup.normalizer (X.QD : Set G)).inv_mem hQDn) hyQD
      have he : ⁅t⁻¹, t * x * t⁻¹⁆ = ⁅t * x * t⁻¹, t⁻¹⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [he]
      exact (X.Z 0).inv_mem hcommZ'
    have he : x = ⁅t⁻¹, t * x * t⁻¹⁆ * (t * x * t⁻¹) := by
      rw [commutatorElement_def]; group
    rw [he]
    exact (X.QD ⊓ X.L 4).mul_mem (hZ0U hc) hx

private theorem QD_inf_L_four_eq_Z_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.QD ⊓ X.L 4 = X.Z 0 := by
  have hKD : X.K ≤ Subgroup.normalizer (X.QD : Set G) :=
    X.K_le_normalizer_Q_inf_centralizer_Ki 0
  have hKL4 : X.K ≤ Subgroup.normalizer (X.L 4 : Set G) :=
    (X.K_le_Gi 4).trans (le_normalizer_oTwoPrime (X.Gi 4))
  have hKN : X.K ≤ Subgroup.normalizer (X.QD ⊓ X.L 4 : Set G) :=
    (le_inf hKD hKL4).trans Subgroup.inf_normalizer_le_normalizer_inf
  refine le_antisymm ?_ (Z_zero_le_QD_inf_L_four C hH)
  · set U : Subgroup G := X.QD ⊓ X.L 4 with hU
    have hUQ0 : U ≤ X.Q 0 := (inf_le_left : U ≤ X.QD).trans inf_le_left
    have hU4 : U ≤ X.Gi 4 := (inf_le_right : U ≤ X.L 4).trans (X.L_le_Gi 4)
    have hP : IsPGroup 2 ↥U := (pCoreOf_isPGroup' (X.Gi 0)).to_le hUQ0
    have hUGm1 : U ≤ X.Gi (-1) :=
      hUQ0.trans ((X.Q_le_Gi_adj 0).trans inf_le_left)
    have hUarc1 : U ≤ X.arcStab (-1) 4 := by
      rw [X.arcStab_eq_inf (by norm_num)]
      exact le_inf hUGm1 hU4
    obtain ⟨t, ht, hrefl⟩ := exists_reflection_data C
    have htUn : t ∈ Subgroup.normalizer (U : Set G) :=
      reflection_mem_normalizer_QD_inf_L_four C hH ht.1 ht.2
    have hUtnorm : conjSub t U = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htUn
    have hfix : U ≤ X.arcStab (-4) 4 :=
      le_arcStab_neg_four_four_of_reflection hrefl hUtnorm hUGm1 hU4 hUarc1
    have hr : r = 8 := (X.s48_12 C hH).1
    have hidx : ((-4 : ℤ) + (r : ℤ)) = 4 := by rw [hr]; norm_num
    have hfix' : U ≤ X.arcStab (-4) ((-4 : ℤ) + (r : ℤ)) := by
      rwa [hidx]
    have hle := X.le_pCoreOf_arcStab_r C.hyp hP hfix'
    have hPC : pCoreOf 2 (X.arcStab (-4) ((-4 : ℤ) + (r : ℤ))) = X.Z 0 := by
      rw [hidx]
      exact (Z_zero_eq_pCoreOf C hH).symm
    rwa [hPC] at hle

end Comm48

variable (X) in
open Comm48 in
theorem Z_four_eq_pCoreOf (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 4 = pCoreOf 2 (X.arcStab 0 8) := by
  have hZ : X.Z 4 = conjSub (X.τ ^ (2 : ℤ)) (X.Z 0) := by
    rw [← X.Z_add 2 0]; norm_num
  have hA : X.arcStab 0 8 = conjSub (X.τ ^ (2 : ℤ)) (X.arcStab (-4) 4) := by
    have h := X.arcStab_add (2 : ℤ) (-4) 4
    rwa [show (-4 : ℤ) + 2 * 2 = 0 by norm_num,
      show (4 : ℤ) + 2 * 2 = 8 by norm_num] at h
  rw [hZ, Z_zero_eq_pCoreOf C hH, hA, ← pCoreOf_conjSub]

namespace Comm48

private theorem Ki_inf_centralizer_Z_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Ki 0 ⊓ Subgroup.centralizer (X.Z 4 : Set G) = ⊥ := by
  refine le_bot_iff.mp ?_
  intro k hk
  obtain ⟨hkKi, hkC⟩ := Subgroup.mem_inf.mp hk
  by_contra hk1
  have hr : r = 8 := (X.s48_12 C hH).1
  subst hr
  have hZ4 : X.Z 4 = pCoreOf 2 (X.arcStab 0 8) := X.Z_four_eq_pCoreOf C hH
  have hbot : X.Z 4 = ⊥ := by
    rw [hZ4]
    rw [eq_bot_iff]
    intro u hu
    exact X.Ki_fpf_pCoreOf_arcStab_r C.hyp 0 hkKi hk1 u hu
      (Subgroup.mem_centralizer_iff.mp hkC u (hZ4 ▸ hu)).symm
  have hc := X.card_Z_four C
  rw [hbot, Subgroup.card_bot] at hc
  have h4 := four_le_two_pow_n C
  omega

private theorem conj_mem_Vk_two {g v : G} (hgL : g ∈ X.L 2) (hvE : v ∈ X.Vk 2) :
    g * v * g⁻¹ ∈ X.Vk 2 := by
  have hmem : g * v * g⁻¹ ∈ conjSub g (X.Vk 2) := mul_mem_conjSub hvE
  have hV2norm : g ∈ Subgroup.normalizer (X.Vk 2 : Set G) :=
    X.Gi_le_normalizer_Vk 2 (X.L_le_Gi 2 hgL)
  have e : conjSub g (X.Vk 2) = X.Vk 2 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hV2norm
  rwa [e] at hmem

private theorem conjugate_correction_mem_Z_two {g v k : G} (hgL : g ∈ X.L 2)
    (hvGi : v ∈ X.Gi 2) (hvZ : ⁅v, k⁆ ∈ X.Z 2) :
    g * (v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v) * g⁻¹ ∈ X.Z 2 := by
  have hζ : k * v * k⁻¹ * v⁻¹ ∈ X.Z 2 := by
    have hinv := (X.Z 2).inv_mem hvZ
    rw [commutatorElement_def] at hinv
    rwa [show (v * k * v⁻¹ * k⁻¹)⁻¹ = k * v * k⁻¹ * v⁻¹ by group] at hinv
  have hzZ : v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v ∈ X.Z 2 := by
    have hmem : v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v ∈ conjSub (v⁻¹) (X.Z 2) := by
      simpa using mul_mem_conjSub (g := v⁻¹) hζ
    have hv' : v⁻¹ ∈ X.Gi 2 := (X.Gi 2).inv_mem hvGi
    have e : conjSub (v⁻¹) (X.Z 2) = X.Z 2 := X.Z_normal 2 v⁻¹ hv'
    rwa [e] at hmem
  have hmem : g * (v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v) * g⁻¹ ∈ conjSub g (X.Z 2) :=
    mul_mem_conjSub hzZ
  have e : conjSub g (X.Z 2) = X.Z 2 := X.Z_normal 2 g (X.L_le_Gi 2 hgL)
  rwa [e] at hmem

private theorem conj_commutator_mem_Z_two_aux (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hKL : ⁅X.Ki 0, X.L 2⁆ ≤ X.Q 2) {g : G} (hgL : g ∈ X.L 2) {v : G}
    (hv : v ∈ relCent (X.Vk 2) (X.Z 2) (X.Ki 0)) {k : G} (hk : k ∈ X.Ki 0) :
    ⁅k, g * v * g⁻¹⁆ ∈ X.Z 2 := by
  have hV2N := Vk_two_le_normalizer_Z_two C hH
  obtain ⟨hvE, hvcomm⟩ := (mem_relCent hV2N).mp hv
  have hwV : g * v * g⁻¹ ∈ X.Vk 2 := conj_mem_Vk_two hgL hvE
  have hkGi : k ∈ X.Gi 2 := X.K_le_Gi 2 hk.1
  have hq : ⁅k, g⁆ ∈ X.Q 2 := Subgroup.commutator_le.mp hKL k hk g hgL
  have hqGi : ⁅k, g⁆ ∈ X.Gi 2 := X.Q_le_Gi 2 hq
  have hkg : k * g * k⁻¹ = ⁅k, g⁆ * g := by
    rw [commutatorElement_def]; group
  have hkg' : k * g⁻¹ * k⁻¹ = (⁅k, g⁆ * g)⁻¹ := by rw [← hkg]; group
  have hvQ : v ∈ X.Q 2 := (Subgroup.mem_inf.mp (Vk_two_le_Q_two_three C hH hvE)).1
  have hvGi : v ∈ X.Gi 2 := X.Q_le_Gi 2 hvQ
  have hvZ : ⁅v, k⁆ ∈ X.Z 2 := hvcomm k hk
  have hzv : k * v * k⁻¹ = v * (v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v) := by group
  have hz' : g * (v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v) * g⁻¹ ∈ X.Z 2 :=
    conjugate_correction_mem_Z_two hgL hvGi hvZ
  have hwGi : g * v * g⁻¹ ∈ X.Gi 2 :=
    (X.Gi 2).mul_mem ((X.Gi 2).mul_mem (X.L_le_Gi 2 hgL) hvGi)
      ((X.Gi 2).inv_mem (X.L_le_Gi 2 hgL))
  have hkw : k * (g * v * g⁻¹) * k⁻¹ =
      ⁅k, g⁆ * (g * v * g⁻¹) *
        (g * (v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v) * g⁻¹) * ⁅k, g⁆⁻¹ := by
    rw [show k * (g * v * g⁻¹) * k⁻¹ =
      (k * g * k⁻¹) * (k * v * k⁻¹) * (k * g⁻¹ * k⁻¹) by group]
    rw [hkg, hzv, hkg']
    group
  have h1 : ⁅k, g * v * g⁻¹⁆ ∈ X.Z 2 := by
    have he1 : ⁅k, g * v * g⁻¹⁆ =
        ((⁅k, g⁆ * (g * v * g⁻¹)) *
          (g * (v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v) * g⁻¹) *
          (⁅k, g⁆ * (g * v * g⁻¹))⁻¹) *
        (⁅k, g⁆ * (g * v * g⁻¹) * ⁅k, g⁆⁻¹ * (g * v * g⁻¹)⁻¹) := by
      rw [commutatorElement_def, hkw]
      group
    rw [he1]
    have hqW : ⁅k, g⁆ * (g * v * g⁻¹) ∈ X.Gi 2 := (X.Gi 2).mul_mem hqGi hwGi
    have hfac1 : (⁅k, g⁆ * (g * v * g⁻¹)) *
        (g * (v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v) * g⁻¹) *
        (⁅k, g⁆ * (g * v * g⁻¹))⁻¹ ∈ X.Z 2 := by
      have hmem : (⁅k, g⁆ * (g * v * g⁻¹)) *
          (g * (v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v) * g⁻¹) *
          (⁅k, g⁆ * (g * v * g⁻¹))⁻¹ ∈
          conjSub (⁅k, g⁆ * (g * v * g⁻¹)) (X.Z 2) := mul_mem_conjSub hz'
      have e : conjSub (⁅k, g⁆ * (g * v * g⁻¹)) (X.Z 2) = X.Z 2 :=
        X.Z_normal 2 _ hqW
      rwa [e] at hmem
    have hfac2 : ⁅k, g⁆ * (g * v * g⁻¹) * ⁅k, g⁆⁻¹ * (g * v * g⁻¹)⁻¹ ∈ X.Z 2 := by
      have h2 : ⁅g * v * g⁻¹, ⁅k, g⁆⁆ ∈ X.Z 2 :=
        Subgroup.commutator_le.mp (le_of_eq (commutator_Vk_two_Q_two C hH))
          _ hwV _ hq
      have hinv := (X.Z 2).inv_mem h2
      rwa [show (⁅g * v * g⁻¹, ⁅k, g⁆⁆)⁻¹ =
        ⁅k, g⁆ * (g * v * g⁻¹) * ⁅k, g⁆⁻¹ * (g * v * g⁻¹)⁻¹ by
        rw [commutatorElement_def]; group] at hinv
    exact (X.Z 2).mul_mem hfac1 hfac2
  exact h1

private theorem conj_commutator_mem_Z_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hKL : ⁅X.Ki 0, X.L 2⁆ ≤ X.Q 2) {g : G} (hgL : g ∈ X.L 2) {v : G}
    (hv : v ∈ relCent (X.Vk 2) (X.Z 2) (X.Ki 0)) {k : G} (hk : k ∈ X.Ki 0) :
    ⁅g * v * g⁻¹, k⁆ ∈ X.Z 2 := by
  have h1 := conj_commutator_mem_Z_two_aux C hH hKL hgL hv hk
  have hinv := (X.Z 2).inv_mem h1
  rw [commutatorElement_def] at hinv
  rwa [show (k * (g * v * g⁻¹) * k⁻¹ * (g * v * g⁻¹)⁻¹)⁻¹ =
    (g * v * g⁻¹) * k * (g * v * g⁻¹)⁻¹ * k⁻¹ by group] at hinv

private theorem conj_mem_relCent_Vk_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hKL : ⁅X.Ki 0, X.L 2⁆ ≤ X.Q 2) {g : G} (hgL : g ∈ X.L 2) {v : G}
    (hv : v ∈ relCent (X.Vk 2) (X.Z 2) (X.Ki 0)) :
    g * v * g⁻¹ ∈ relCent (X.Vk 2) (X.Z 2) (X.Ki 0) := by
  have hV2N := Vk_two_le_normalizer_Z_two C hH
  obtain ⟨hvE, -⟩ := (mem_relCent hV2N).mp hv
  rw [mem_relCent hV2N]
  exact ⟨conj_mem_Vk_two hgL hvE,
    fun k hk => conj_commutator_mem_Z_two C hH hKL hgL hv hk⟩

private theorem L_two_le_normalizer_relCent (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (hKL : ⁅X.Ki 0, X.L 2⁆ ≤ X.Q 2) :
    X.L 2 ≤ Subgroup.normalizer (relCent (X.Vk 2) (X.Z 2) (X.Ki 0) : Set G) := by
  intro g hg
  refine CFSG.Quasithin.B6.mem_normalizer_of_forall_mem ?_ ?_
  · intro v hv
    exact conj_mem_relCent_Vk_two C hH hKL hg hv
  · intro v hv
    have h := conj_mem_relCent_Vk_two C hH hKL ((X.L 2).inv_mem hg) hv
    simpa using h

private theorem exists_mem_Z_zero_ne_one (C : X.Comm48 s r d) :
    ∃ z ∈ X.Z 0, z ≠ 1 := by
  refine (Subgroup.bot_or_exists_ne_one (X.Z 0)).resolve_left fun h => ?_
  have hc := card_Z_zero C
  rw [h, Subgroup.card_bot] at hc
  have h4 := four_le_two_pow_n C
  omega

private theorem Ki_zero_le_centralizer_Z_four_of_commutator_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hcommVK : ⁅X.Vk 2, X.Ki 0⁆ ≤ X.Z 2) : X.Ki 0 ≤ Subgroup.centralizer (X.Z 4 : Set G) := by
  have hZ4V : X.Z 4 ≤ X.Vk 2 := by rw [Vk_two_eq C hH]; exact le_sup_right
  have hcommZ4Z2 : ⁅X.Z 4, X.Ki 0⁆ ≤ X.Z 2 :=
    (Subgroup.commutator_mono hZ4V le_rfl).trans hcommVK
  have hZ4norm : X.Ki 0 ≤ Subgroup.normalizer (X.Z 4 : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 4 k (X.K_le_Gi 4 hk.1))
  have hcommZ4Z4 : ⁅X.Z 4, X.Ki 0⁆ ≤ X.Z 4 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hZ4norm
  have hcommZ4bot : ⁅X.Z 4, X.Ki 0⁆ = ⊥ := by
    refine le_bot_iff.mp ((le_inf hcommZ4Z4 hcommZ4Z2).trans ?_)
    rw [inf_comm, Z_two_inf_Z_four C hH]
  exact Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommZ4bot)

private theorem Z_two_le_relCent_Vk_two_Ki (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 2 ≤ relCent (X.Vk 2) (X.Z 2) (X.Ki 0) := by
  have hV2N := Vk_two_le_normalizer_Z_two C hH
  intro z hz
  rw [mem_relCent hV2N]
  constructor
  · rw [Vk_two_eq C hH]
    exact Subgroup.mem_sup_left ((Z_two_le_Z_one C hH) hz)
  · intro k hk
    have hkGi : k ∈ X.Gi 2 := X.K_le_Gi 2 hk.1
    have h1 : k * z * k⁻¹ ∈ X.Z 2 := by
      have hmem : k * z * k⁻¹ ∈ conjSub k (X.Z 2) := mul_mem_conjSub hz
      have e : conjSub k (X.Z 2) = X.Z 2 := X.Z_normal 2 k hkGi
      rwa [e] at hmem
    have h2 : k * z⁻¹ * k⁻¹ ∈ X.Z 2 := by
      have hinv := (X.Z 2).inv_mem h1
      rwa [show (k * z * k⁻¹)⁻¹ = k * z⁻¹ * k⁻¹ by group] at hinv
    rw [commutatorElement_def,
      show z * k * z⁻¹ * k⁻¹ = z * (k * z⁻¹ * k⁻¹) by group]
    exact (X.Z 2).mul_mem hz h2

private theorem false_of_not_QD_le_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (h2 : ¬ X.QD ≤ X.Q 2) : False := by
  have hDleQ1 : X.QD ≤ X.Q 1 := (QD_le_QA C hH).trans inf_le_left
  have hE1 : X.QD ≤ X.edgeSylow 1 := hDleQ1.trans (X.Q_le_edgeSylow_left 1)
  have hPS : X.QD ⊔ X.Q 2 = X.edgeSylow 1 :=
    X.sup_Q_eq_edgeSylow_of_gen (i := 1) (A := X.QD)
      (inf_le_left.trans (X.K_le_normalizer_Q_inf_centralizer_Ki 0)) hE1 h2
  have hPD : IsPGroup 2 ↥X.QD := (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  obtain ⟨hfix2, -⟩ :=
    X.fix_nbrs_of_centralizes C.hyp.char 2 (U := X.Ki 0) (P := X.QD)
      (inf_le_left : X.Ki 0 ≤ X.K) hPD (Or.inr hPS) inf_le_right
  have hKL : ⁅X.Ki 0, X.L 2⁆ ≤ X.Q 2 := by
    refine Subgroup.commutator_le.mpr ?_
    intro k hk l hl
    exact X.commutator_mem_Q_of_fixes_neighbors 2 (X.K_le_Gi 2 hk.1)
      (fun w hw => hfix2 w hw k hk) l hl
  have hV2N := Vk_two_le_normalizer_Z_two C hH
  set Cr : Subgroup G := relCent (X.Vk 2) (X.Z 2) (X.Ki 0) with hCr
  have hLC : X.L 2 ≤ Subgroup.normalizer (Cr : Set G) :=
    L_two_le_normalizer_relCent C hH hKL
  have hCV : Cr ≤ X.Vk 2 := fun v hv => ((mem_relCent hV2N).mp hv).1
  have hZC : X.Z 2 ≤ Cr := Z_two_le_relCent_Vk_two_Ki C hH
  have hirred := (natQuot_L2_Vk2_Z2 C hH).irred Cr hZC hCV hLC
  obtain ⟨z0, hz0Z0, hz0ne⟩ := exists_mem_Z_zero_ne_one C
  have hz0V : z0 ∈ X.Vk 2 := by
    have hz1 : z0 ∈ X.Z 1 := (X.s48_1 C).1 hz0Z0
    rw [Vk_two_eq C hH]
    exact Subgroup.mem_sup_left hz1
  have hz0C : z0 ∈ Cr := by
    rw [hCr, mem_relCent hV2N]
    refine ⟨hz0V, ?_⟩
    intro k hk
    have hc1 : ⁅z0, k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Z_zero_le_centralizer_Ki_zero C hz0Z0) k hk).symm
    rw [hc1]
    exact (X.Z 2).one_mem
  have hCne : Cr ≠ X.Z 2 := by
    intro heq
    have hz0Z2 : z0 ∈ X.Z 2 := heq ▸ hz0C
    have hmem : z0 ∈ X.Z 0 ⊓ X.Z 2 := Subgroup.mem_inf.mpr ⟨hz0Z0, hz0Z2⟩
    rw [Z_zero_inf_Z_two C hH, Subgroup.mem_bot] at hmem
    exact hz0ne hmem
  have hCeq : Cr = X.Vk 2 := hirred.resolve_left hCne
  have hcommVK : ⁅X.Vk 2, X.Ki 0⁆ ≤ X.Z 2 := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    have hvC : v ∈ Cr := hCeq ▸ hv
    exact ((mem_relCent hV2N).mp hvC).2 k hk
  have hbot : X.Ki 0 = ⊥ := by
    have h := Ki_inf_centralizer_Z_four C hH
    rwa [inf_eq_left.mpr (Ki_zero_le_centralizer_Z_four_of_commutator_le C hH hcommVK)] at h
  exact Ki_zero_ne_bot C hbot

end Comm48

variable (X) in
open Comm48 in
theorem s48_14 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.QD = X.Z 0 := by
  by_contra hne
  by_cases h2 : X.QD ≤ X.Q 2
  · by_cases h3 : X.QD ≤ X.Q 3
    ·
      have hPD : IsPGroup 2 ↥X.QD := (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
      have hDL4 : X.QD ≤ X.L 4 := by
        have hG4 : X.QD ≤ X.Gi 4 := h3.trans ((X.Q_le_Gi_adj 3).trans inf_le_right)
        exact le_oTwoPrime_of_isPGroup hPD hG4
      have hDZ : X.QD = X.Z 0 := by
        rw [← QD_inf_L_four_eq_Z_zero C hH]
        exact (inf_eq_left.mpr hDL4).symm
      exact hne hDZ
    · exact false_of_QD_le_two_not_three C hH h2 h3
  · exact false_of_not_QD_le_two C hH h2

end Setup

end CFSG.Quasithin.St84

end
