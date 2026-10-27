module

public import CFSG.Quasithin.Background.E2TwoProofSporPerm
public import CFSG.Quasithin.Background.RonanE114Pair
public import CFSG.Quasithin.Background.RonanE114A7

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L PermLat Equiv
open CFSG.QuasithinUnique.Unc25K1.Six (IsEnc)
open CFSG.Open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB CFSG.Quasithin.RonanE114

namespace RonanE114

section M11

open CFSG.QuasithinUnique.Vol2Native.A312L.M11Lat

theorem m11_x2_mem : permOf 11 [[0, 1], [5, 7], [6, 8], [9, 10]] ∈ Mgrp := by
  rw [show permOf 11 [[0, 1], [5, 7], [6, 8], [9, 10]] =
    evalW cert.mGens [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1] by decide +kernel]
  exact evalW_mem_closure _ _

@[expose] def m11Pair (x : Fin 11) : Bool := decide (x.val = 1 ∨ x.val = 2)

theorem hasSolvInvPair_M11 : HasSolvInvPair ↥Mgrp := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 11) hck (k := 4) (m := 495) (by decide) (by decide)
      (by omega)
  have htm := t_le_m_of_check (rawIsEnc 11) hck
  have hL1 : (cert.tGens :: cert.lat)[1]'(by decide) =
      cert.tGens ++ [permOf 11 [[2, 3], [5, 7], [6, 10], [8, 9]]] := rfl
  have hL2 : (cert.tGens :: cert.lat)[2]'(by decide) =
      cert.tGens ++ [permOf 11 [[0, 1], [5, 7], [6, 8], [9, 10]]] := rfl
  have hL4 : (cert.tGens :: cert.lat)[4]'(by decide) =
      cert.tGens ++ [permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]] := rfl
  have hle2 : Subgroup.closure {g | g ∈ cert.tGens ++ [permOf 11 [[0, 1], [5, 7], [6, 8], [9, 10]]]}
      ≤ Mgrp := closure_append_le htm m11_x2_mem
  have hle4 : Subgroup.closure {g | g ∈ cert.tGens ++ [permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]]}
      ≤ Mgrp := closure_append_le htm m11_x4_mem
  have hM : Nat.card Mgrp = 7920 := cert.card_m (rawIsEnc 11) hcl hsz
  have hc2 : Nat.card (Subgroup.closure {g | g ∈ cert.tGens ++
      [permOf 11 [[0, 1], [5, 7], [6, 8], [9, 10]]]}) = 48 := by
    rw [← hL2]
    exact cert.card_member_idx (rawIsEnc 11) hcl hsz 2 (by decide)
  have hc4 : Nat.card (Subgroup.closure {g | g ∈ cert.tGens ++
      [permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]]}) = 144 := by
    rw [← hL4]
    exact cert.card_member_idx (rawIsEnc 11) hcl hsz 4 (by decide)
  set P := (Subgroup.closure {g | g ∈ cert.tGens ++
      [permOf 11 [[0, 1], [5, 7], [6, 8], [9, 10]]]}).subgroupOf Mgrp with hP
  set P' := (Subgroup.closure {g | g ∈ cert.tGens ++
      [permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]]}).subgroupOf Mgrp with hP'
  have hcP : Nat.card P = 48 := by rw [hP, card_subgroupOf_of_le hle2, hc2]
  have hcP' : Nat.card P' = 144 := by rw [hP', card_subgroupOf_of_le hle4, hc4]
  have hUle : ∀ {L : Subgroup (Perm (Fin 11))}, Subgroup.closure {g | g ∈ cert.tGens} ≤ L →
      Ugrp ≤ L.subgroupOf Mgrp := fun hL x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hL hx
  have hUP : Ugrp ≤ P := hUle (closure_le_append _ _)
  have hUP' : Ugrp ≤ P' := hUle (closure_le_append _ _)
  have hcases := fun (Y : Subgroup ↥Mgrp) (hY : Ugrp ≤ Y) =>
    cert.overgroup_cases_idx (rawIsEnc 11) hck Y hY
  have hu2 : ∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y → Nat.card Y = Nat.card P → Y = P := by
    intro Y hY hYc
    obtain ⟨j, hj, hjM, hYj, hcj⟩ := hcases Y hY
    have hj5 : j < 5 := by simpa [cert, lat] using hj
    have hsj : cert.sizes.getD j 0 = 48 := by
      rw [← hcj, ← card_subgroupOf_of_le hjM, ← hYj, hYc, hcP]
    interval_cases j
    all_goals first | exact absurd hsj (by decide) | exact hYj
  have hu4 : ∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y → Nat.card Y = Nat.card P' → Y = P' := by
    intro Y hY hYc
    obtain ⟨j, hj, hjM, hYj, hcj⟩ := hcases Y hY
    have hj5 : j < 5 := by simpa [cert, lat] using hj
    have hsj : cert.sizes.getD j 0 = 144 := by
      rw [← hcj, ← card_subgroupOf_of_le hjM, ← hYj, hYc, hcP']
    interval_cases j
    all_goals first | exact absurd hsj (by decide) | exact hYj
  have hsP : Group.IsSolvable ↥P :=
    solvable_subgroupOf_two_three hle2 (a := 4) (b := 1) (by rw [hc2]; norm_num)
  have hsP' : Group.IsSolvable ↥P' :=
    solvable_subgroupOf_two_three hle4 (a := 4) (b := 2) (by rw [hc4]; norm_num)
  refine hasSolvInvPair_of_unique_orders hU hUP hUP' hsP hsP' ?_ hu2 hu4
  obtain ⟨j, hj, hjM, hYj, hcj⟩ := hcases (P ⊔ P') (hUP.trans le_sup_left)
  have hj5 : j < 5 := by simpa [cert, lat] using hj
  have hPPc : Nat.card ↥(P ⊔ P') = cert.sizes.getD j 0 := by
    rw [hYj, card_subgroupOf_of_le hjM, hcj]
  by_cases hs : cert.sizes.getD j 0 = 7920
  · have hjtop := Subgroup.eq_of_le_of_card_ge hjM (by rw [hM, hcj, hs])
    rw [hYj, hjtop, Subgroup.subgroupOf_self]
  · exfalso
    have hd144 : 144 ∣ cert.sizes.getD j 0 := by
      rw [← hPPc, ← hcP']
      exact Subgroup.card_dvd_of_le le_sup_right
    have hj14 : j = 1 ∨ j = 4 := by
      revert hs hd144
      interval_cases j <;> decide
    rcases hj14 with rfl | rfl
    ·
      rw [hL1] at hYj
      have hx : permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]] ∈
          Subgroup.closure {g | g ∈ cert.tGens ++
            [permOf 11 [[2, 3], [5, 7], [6, 10], [8, 9]]]} := by
        have h2 : (⟨permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]], m11_x4_mem⟩ : ↥Mgrp) ∈ P' :=
          Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))
        exact (le_sup_right.trans (le_of_eq hYj)) h2
      have hst : Subgroup.closure {g | g ∈ cert.tGens ++
          [permOf 11 [[2, 3], [5, 7], [6, 10], [8, 9]]]} ≤
          MulAction.stabilizer (Equiv.Perm (Fin 11)) (0 : Fin 11) := by
        have key : (cert.tGens ++ [permOf 11 [[2, 3], [5, 7], [6, 10], [8, 9]]]).all
            (fun g => decide (g 0 = 0)) = true := by decide +kernel
        rw [Subgroup.closure_le]
        exact fun g hg => MulAction.mem_stabilizer_iff.mpr
          (of_decide_eq_true (List.all_eq_true.mp key g hg))
      have h0 : (permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]) 0 = 0 :=
        MulAction.mem_stabilizer_iff.mp (hst hx)
      exact absurd h0 (by decide +kernel)
    ·
      rw [hL4] at hYj
      have hx : permOf 11 [[0, 1], [5, 7], [6, 8], [9, 10]] ∈
          Subgroup.closure {g | g ∈ cert.tGens ++
            [permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]]} := by
        have h2 : (⟨permOf 11 [[0, 1], [5, 7], [6, 8], [9, 10]], m11_x2_mem⟩ : ↥Mgrp) ∈ P :=
          Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))
        exact (le_sup_left.trans (le_of_eq hYj)) h2
      have hst : Subgroup.closure {g | g ∈ cert.tGens ++
          [permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]]} ≤ fibreStab m11Pair := by
        have key : (cert.tGens ++ [permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]]).all
            (fun g => (List.finRange 11).all fun x => m11Pair (g x) == m11Pair x) = true := by
          decide +kernel
        rw [Subgroup.closure_le]
        exact fun g hg => mem_fibreStab.mpr fun x => beq_iff_eq.mp
          (List.all_eq_true.mp (List.all_eq_true.mp key g hg) x (List.mem_finRange x))
      exact absurd ((mem_fibreStab.mp (hst hx)) 1) (by decide +kernel)

theorem nParam_eq_one_of_isM11
    {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hM : IsSporadic .M11 (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) = 1 := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hM
  refine le_antisymm (nParam_le_one_of_hasSolvInvPair hasSolvInvPair_M11 hLn
    (e₀.trans (MulEquiv.subgroupCongr mGens_closure).symm) hTs hFT) ?_
  refine Vol2.Ch11.SecE3.one_le_nParam_of_not_odd
    (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G) ?_)
  have h1 : Nat.card ↥(CFSG.generalizedFitting G) = 7920 := by
    rw [Nat.card_congr (e₀.trans (MulEquiv.subgroupCongr mGens_closure).symm).toEquiv]
    exact cert.card_m (rawIsEnc 11) (LatCert.closedOK_of_check cert_check)
      (LatCert.sizesOK_of_check cert_check)
  rw [h1]
  norm_num

end M11

end RonanE114

end CFSG.Quasithin
