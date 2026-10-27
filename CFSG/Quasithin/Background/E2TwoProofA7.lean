module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique Equiv

namespace E2P

namespace A7

open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

abbrev Q10 : Subgroup ↥A7s := (Z 10).subgroupOf A7s

abbrev Q7 : Subgroup ↥A7s := (Z 7).subgroupOf A7s

theorem Z10_le : Z 10 ≤ A7s := by
  rw [Z, Subgroup.closure_le]
  intro g hg
  have h : latGens.getD 10 [] = dGens ++ [perm7 [[3, 4, 5]]] := rfl
  rw [h] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Equiv.Perm.mem_alternatingGroup.mpr (D7_le_A7s_this g hg)
  · rw [List.mem_singleton.mp hg]
    exact Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)

@[expose] def x36 : P7 := perm7 [[3, 6], [4, 5]]

theorem x36_mem : x36 ∈ Z 7 := by
  rw [Z]
  apply Subgroup.subset_closure
  show x36 ∈ latGens.getD 7 []
  have h : latGens.getD 7 [] = dGens ++ [x36] := rfl
  rw [h]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem x36_sign : Perm.sign x36 = 1 := by decide +kernel

theorem x36_six : x36 6 ≠ 6 := by decide +kernel

theorem Z7_le : Z 7 ≤ A7s := by
  rw [Z, Subgroup.closure_le]
  intro g hg
  have h : latGens.getD 7 [] = dGens ++ [x36] := rfl
  rw [h] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Equiv.Perm.mem_alternatingGroup.mpr (D7_le_A7s_this g hg)
  · rw [List.mem_singleton.mp hg]
    exact Equiv.Perm.mem_alternatingGroup.mpr x36_sign

theorem T7_le_Q10 : T7 ≤ Q10 :=
  Subgroup.subgroupOf_mono _ (D7_le_closure [perm7 [[3, 4, 5]]])

theorem T7_le_Q7 : T7 ≤ Q7 :=
  Subgroup.subgroupOf_mono _ (D7_le_closure [x36])

theorem card_Q10 :
    Nat.card Q10 = 360 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Z10_le).toEquiv, card_Z (by norm_num)]
  rfl

theorem card_Q7 :
    Nat.card Q7 = 120 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Z7_le).toEquiv, card_Z (by norm_num)]
  rfl

theorem map_Q10 : Q10.map A7s.subtype = Z 10 :=
  Subgroup.map_subgroupOf_eq_of_le Z10_le

theorem map_Q7 : Q7.map A7s.subtype = Z 7 :=
  Subgroup.map_subgroupOf_eq_of_le Z7_le

theorem eq_Q10
    {W : Subgroup ↥A7s} (hT : T7 ≤ W) (hc : Nat.card W = 360) : W = Q10 := by
  obtain ⟨i, hi, hW⟩ := overgroup_Z hT
  have hci : Nat.card (Z i) = 360 := by rw [← hW, card_map_subtype, hc]
  rw [card_Z hi] at hci
  have hi10 : i = 10 := by interval_cases i <;> simp_all
  subst hi10
  exact Subgroup.map_injective A7s.subtype_injective (hW.trans map_Q10.symm)

theorem eq_Q7
    {W : Subgroup ↥A7s} (hT : T7 ≤ W) (hc : Nat.card W = 120) : W = Q7 := by
  obtain ⟨i, hi, hW⟩ := overgroup_Z hT
  have hci : Nat.card (Z i) = 120 := by rw [← hW, card_map_subtype, hc]
  rw [card_Z hi] at hci
  have hi7 : i = 7 := by interval_cases i <;> simp_all
  subst hi7
  exact Subgroup.map_injective A7s.subtype_injective (hW.trans map_Q7.symm)

theorem sup_eq_top :
    Q10 ⊔ Q7 = ⊤ := by
  obtain ⟨i, hi, hW⟩ := overgroup_Z (T7_le_Q10.trans (le_sup_left : Q10 ≤ Q10 ⊔ Q7))
  have hdvd : 360 ∣ Nat.card (Z i) := by
    rw [← hW, card_map_subtype, ← card_Q10]
    exact Subgroup.card_dvd_of_le le_sup_left
  rw [card_Z hi] at hdvd
  interval_cases i
  all_goals first | (exfalso; revert hdvd; decide) | skip
  ·
    exfalso
    have hx : (⟨x36, Equiv.Perm.mem_alternatingGroup.mpr x36_sign⟩ : ↥A7s) ∈ Q10 ⊔ Q7 :=
      Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr x36_mem)
    have hx10 : x36 ∈ Z 10 := by
      rw [← hW]
      exact ⟨_, hx, rfl⟩
    exact x36_six ((mem_Z10 x36_sign).mp hx10)
  ·
    apply Subgroup.eq_top_of_card_eq
    rw [← card_map_subtype, hW, card_Z (by norm_num), card_A7s]
    rfl

theorem Q10_ne_top : Q10 ≠ ⊤ := by
  intro h
  have h1 := card_Q10
  rw [h, Subgroup.card_top, card_A7s] at h1
  exact absurd h1 (by decide)

theorem Q7_ne_top : Q7 ≠ ⊤ := by
  intro h
  have h1 := card_Q7
  rw [h, Subgroup.card_top, card_A7s] at h1
  exact absurd h1 (by decide)

theorem inv (α : MulAut ↥A7s)
    (hα : T7.map α.toMonoidHom = T7) :
    Q10.map α.toMonoidHom = Q10 ∧ Q7.map α.toMonoidHom = Q7 := by
  refine ⟨eq_Q10 ?_ ?_, eq_Q7 ?_ ?_⟩
  · rw [← hα]
    exact Subgroup.map_mono T7_le_Q10
  · rw [Subgroup.card_map_of_injective α.injective, card_Q10]
  · rw [← hα]
    exact Subgroup.map_mono T7_le_Q7
  · rw [Subgroup.card_map_of_injective α.injective, card_Q7]

end A7

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem ASHyp.not_a7
    (hX : ASHyp K T M) (e : ↥K ≃* alternatingGroup (Fin 7)) : False :=
  hX.false_of_invPair e Vol2Native.A312L.Seven.isSylowTwoOf_T7 A7.T7_le_Q10 A7.T7_le_Q7
    A7.Q10_ne_top A7.Q7_ne_top A7.sup_eq_top A7.inv

end E2P

end CFSG.Quasithin
