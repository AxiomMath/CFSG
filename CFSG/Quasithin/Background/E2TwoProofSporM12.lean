module

public import CFSG.Quasithin.Background.E2TwoProofSporPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM12
public import Certificates.Certificate7122

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L PermLat Equiv
open CFSG.QuasithinUnique.Unc25K1.Six (IsEnc)

namespace E2P

namespace SporB

section M12

open CFSG.QuasithinUnique.Vol2Native.A312L.M12Lat

abbrev m12Grp : Subgroup (Perm (Fin 12)) := Subgroup.closure {g | g ∈ cert.mGens}

abbrev m12Syl : Subgroup ↥m12Grp := (Subgroup.closure {g | g ∈ cert.tGens}).subgroupOf m12Grp

theorem m12_x2_mem : permOf 12 [[1, 2], [5, 9], [6, 10], [7, 11]] ∈ m12Grp := by
  rw [show permOf 12 [[1, 2], [5, 9], [6, 10], [7, 11]] =
    evalW cert.mGens [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0,
      1, 1, 0, 1, 1, 0] by decide +kernel]
  exact evalW_mem_closure _ _

theorem m12_x3_mem : permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]] ∈ m12Grp := by
  rw [show permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]] =
    evalW cert.mGens [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] by decide +kernel]
  exact evalW_mem_closure _ _

theorem m12_z_eq : permOf 12 [[4, 8], [5, 10], [6, 9], [7, 11]] = evalW cert.tGens [0, 0] := by
  decide +kernel

theorem m12_center_three
    {w : Perm (Fin 12)}
    (hw : w ∈ Subgroup.closure {g | g ∈ cert.tGens ++
      [permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]]]})
    (hc : ∀ g ∈ cert.tGens ++ [permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]]],
      w * g = g * w) : w = 1 :=
  Certificates.certificate7122 w hw hc

theorem hasInvPair_M12 :
    HasInvPair ↥m12Grp := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : IsSylowTwoOf m12Syl ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 12) hck (k := 6) (m := 1485) (by decide) (by decide)
      (by omega)
  have htm := t_le_m_of_check (rawIsEnc 12) hck
  set x2 := permOf 12 [[1, 2], [5, 9], [6, 10], [7, 11]] with hx2
  set x3 := permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]] with hx3
  set L2 := cert.tGens ++ [x2] with hL2def
  set L3 := cert.tGens ++ [x3] with hL3def
  have hL2 : (cert.tGens :: cert.lat)[2]'(by decide) = L2 := rfl
  have hL3 : (cert.tGens :: cert.lat)[3]'(by decide) = L3 := rfl
  have hle2 : Subgroup.closure {g | g ∈ L2} ≤ m12Grp := closure_append_le htm m12_x2_mem
  have hle3 : Subgroup.closure {g | g ∈ L3} ≤ m12Grp := closure_append_le htm m12_x3_mem
  have hM : Nat.card m12Grp = 95040 := cert.card_m (rawIsEnc 12) hcl hsz
  have hc2 : Nat.card (Subgroup.closure {g | g ∈ L2}) = 192 := by
    rw [← hL2]
    exact cert.card_member_idx (rawIsEnc 12) hcl hsz 2 (by decide)
  have hc3 : Nat.card (Subgroup.closure {g | g ∈ L3}) = 192 := by
    rw [← hL3]
    exact cert.card_member_idx (rawIsEnc 12) hcl hsz 3 (by decide)
  set P := (Subgroup.closure {g | g ∈ L2}).subgroupOf m12Grp with hP
  set P' := (Subgroup.closure {g | g ∈ L3}).subgroupOf m12Grp with hP'
  have hcP : Nat.card P = 192 := by rw [hP, card_subgroupOf_of_le hle2, hc2]
  have hcP' : Nat.card P' = 192 := by rw [hP', card_subgroupOf_of_le hle3, hc3]
  have hUle : ∀ {L : Subgroup (Perm (Fin 12))}, Subgroup.closure {g | g ∈ cert.tGens} ≤ L →
      m12Syl ≤ L.subgroupOf m12Grp := fun hL x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hL hx
  have hUP : m12Syl ≤ P := hUle (closure_le_append _ _)
  have hUP' : m12Syl ≤ P' := hUle (closure_le_append _ _)
  have hpair : ∀ Y : Subgroup ↥m12Grp, m12Syl ≤ Y → Nat.card Y = Nat.card P → Y = P ∨ Y = P' := by
    intro Y hY hYc
    obtain ⟨j, hj, hjM, hYj, hcj⟩ := cert.overgroup_cases_idx (rawIsEnc 12) hck Y hY
    have hj4 : j < 4 := by simpa [cert, lat] using hj
    have hsj : cert.sizes.getD j 0 = 192 := by
      rw [← hcj, ← card_subgroupOf_of_le hjM, ← hYj, hYc, hcP]
    interval_cases j
    · exact absurd hsj (by decide)
    · exact absurd hsj (by decide)
    · exact Or.inl hYj
    · exact Or.inr hYj
  have hz : permOf 12 [[4, 8], [5, 10], [6, 9], [7, 11]] ∈
      Subgroup.closure {g | g ∈ cert.tGens} := by
    rw [m12_z_eq]
    exact evalW_mem_closure _ _
  have hzM : permOf 12 [[4, 8], [5, 10], [6, 9], [7, 11]] ∈ m12Grp := htm hz
  set z : ↥m12Grp := ⟨_, hzM⟩ with hzdef
  have hzP : z ∈ P := closure_le_append _ _ hz
  have hz1' : permOf 12 [[4, 8], [5, 10], [6, 9], [7, 11]] ≠ 1 := by decide +kernel
  have hz1 : z ≠ 1 := fun h => hz1' (congrArg Subtype.val h)
  have hzc : (L2.all fun g => decide (permOf 12 [[4, 8], [5, 10], [6, 9], [7, 11]] * g =
      g * permOf 12 [[4, 8], [5, 10], [6, 9], [7, 11]])) = true := by decide +kernel
  have hzC : Subgroup.closure {g | g ∈ L2} ≤
      Subgroup.centralizer {permOf 12 [[4, 8], [5, 10], [6, 9], [7, 11]]} := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (of_decide_eq_true (List.all_eq_true.mp hzc g hg)).symm
  have hzcen : ∀ x ∈ P, z * x = x * z := by
    intro x hx
    have := Subgroup.mem_centralizer_singleton_iff.mp (hzC hx)
    exact Subtype.ext this.symm
  have hZ' : ∀ w ∈ P', (∀ x ∈ P', w * x = x * w) → w = 1 := by
    intro w hw hcw
    apply Subtype.ext
    refine m12_center_three hw fun g hg => ?_
    have hgM : g ∈ m12Grp := hle3 (Subgroup.subset_closure hg)
    have hgP : (⟨g, hgM⟩ : ↥m12Grp) ∈ P' := Subgroup.subset_closure hg
    exact congrArg Subtype.val (hcw _ hgP)
  have hinv := fun α hα => map_eq_of_center_pair hUP hUP' (hcP'.trans hcP.symm) hpair hzP hz1
    hzcen hZ' α hα
  have hne : ∀ {Q : Subgroup ↥m12Grp}, Nat.card Q = 192 → Q ≠ ⊤ := fun hQ h => by
    rw [h, Subgroup.card_top, hM] at hQ
    exact absurd hQ (by decide)
  refine ⟨m12Syl, P, P', hU, hUP, hUP', hne hcP, hne hcP', ?_, hinv⟩
  obtain ⟨j, hj, hjM, hYj, hcj⟩ := cert.overgroup_cases_idx (rawIsEnc 12) hck (P ⊔ P')
    (hUP.trans le_sup_left)
  have hj4 : j < 4 := by simpa [cert, lat] using hj
  have hPPc : Nat.card ↥(P ⊔ P') = cert.sizes.getD j 0 := by
    rw [hYj, card_subgroupOf_of_le hjM, hcj]
  by_cases hs : cert.sizes.getD j 0 = 95040
  · have h1 := Subgroup.eq_of_le_of_card_ge hjM (hM.trans (hcj.trans hs).symm).le
    rw [hYj, h1, Subgroup.subgroupOf_self]
  · exfalso
    have hdiv : 192 ∣ cert.sizes.getD j 0 := by
      rw [← hPPc, ← hcP]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h192 : cert.sizes.getD j 0 = 192 := by
      revert hs hdiv
      interval_cases j <;> decide
    have hPs : P = P ⊔ P' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcP, hPPc, h192])
    have hP's : P' = P ⊔ P' := Subgroup.eq_of_le_of_card_ge le_sup_right
      (by rw [hcP', hPPc, h192])
    have hPP : P = P' := hPs.trans hP's.symm
    exact hz1 (hZ' z (by rw [← hPP]; exact hzP) fun x hx => hzcen x (by rw [hPP]; exact hx))

theorem asc86bClauseB_M12 :
    Asc86bClauseB .M12 :=
  @asc86bClauseB_of_hasInvPair .M12 ↥m12Grp inferInstance inferInstance
    (MulEquiv.subgroupCongr mGens_closure).symm hasInvPair_M12

end M12

end SporB

end E2P

end CFSG.Quasithin
