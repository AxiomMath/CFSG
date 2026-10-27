module

public import CFSG.Quasithin.Background.RonanE114C5Gen
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.Quasithin.RonanE114.C5.M22

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E2P.SporB

section JoinEntry

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open CFSG.QuasithinUnique.Unc25K1.Six (IsEnc)

variable {G : Type} [Group G] [Finite G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  {enc : G → R}

theorem join_entry (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.joinsOK enc = true) {a b d : ℕ} {w : List (List ℕ)} (hw : (a, b, d, w) ∈ c.joins)
    (ha : a < (c.tGens :: c.lat).length) (hb : b < (c.tGens :: c.lat).length)
    (hd : d < (c.tGens :: c.lat).length) :
    Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[a]} ⊔
        Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[b]} =
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[d]} := by
  simp only [LatCert.joinsOK, Bool.and_eq_true, List.all_eq_true] at hc
  have h1 := hc.2 _ hw
  have hma : (c.members enc)[a]? = some ((c.tGens :: c.lat)[a], elts enc c.depth ((c.tGens :: c.lat)[a])) := by
    show ((c.tGens :: c.lat).map (fun L => (L, elts enc c.depth L)))[a]? = _
    rw [List.getElem?_map, List.getElem?_eq_getElem ha]
    rfl
  have hmb : (c.members enc)[b]? = some ((c.tGens :: c.lat)[b], elts enc c.depth ((c.tGens :: c.lat)[b])) := by
    show ((c.tGens :: c.lat).map (fun L => (L, elts enc c.depth L)))[b]? = _
    rw [List.getElem?_map, List.getElem?_eq_getElem hb]
    rfl
  have hmd : (c.members enc)[d]? = some ((c.tGens :: c.lat)[d], elts enc c.depth ((c.tGens :: c.lat)[d])) := by
    show ((c.tGens :: c.lat).map (fun L => (L, elts enc c.depth L)))[d]? = _
    rw [List.getElem?_map, List.getElem?_eq_getElem hd]
    rfl
  simp only [hma, hmb, hmd] at h1
  have hmem : (c.tGens :: c.lat)[d] ∈ c.tGens :: c.lat := List.getElem_mem hd
  have := closure_eq_of_eqCert h (c.members_closed hcl _ hmem) h1
  rw [← this]
  have hset : {g : G | g ∈ (c.tGens :: c.lat)[a] ++ (c.tGens :: c.lat)[b]} =
      {g | g ∈ (c.tGens :: c.lat)[a]} ∪ {g | g ∈ (c.tGens :: c.lat)[b]} := by
    ext g
    simp
  rw [hset, Subgroup.closure_union]

end JoinEntry

section Abstract

def sz (j : ℕ) : ℕ := #[128, 384, 1920, 5760, 443520, 384][j]!

structure Data {Γ : Type} [Group Γ] (U : Subgroup Γ) (Y : ℕ → Subgroup Γ) : Prop where
  S_le : ∀ j < 6, U ≤ Y j
  complete : ∀ Z : Subgroup Γ, U ≤ Z → ∃ j < 6, Z = Y j
  card : ∀ j < 6, Nat.card (Y j) = sz j
  card_top : Nat.card (⊤ : Subgroup Γ) = 443520
  j12 : Y 1 ⊔ Y 2 = Y 2
  j13 : Y 1 ⊔ Y 3 = Y 3
  j15 : Y 1 ⊔ Y 5 = Y 3
  j35 : Y 3 ⊔ Y 5 = Y 3
  j23 : Y 2 ⊔ Y 3 = Y 4
  j25 : Y 2 ⊔ Y 5 = Y 4

variable {Γ : Type} [Group Γ] {U : Subgroup Γ} {Y : ℕ → Subgroup Γ}

theorem Data.Y4_top [Finite Γ] (h : Data U Y) : Y 4 = ⊤ := by
  have hΓ : Nat.card Γ = 443520 := by rw [← Subgroup.card_top]; exact h.card_top
  exact Subgroup.eq_top_of_card_eq _ (by rw [h.card 4 (by norm_num), hΓ]; rfl)

theorem Data.Y1_le_Y2 (h : Data U Y) : Y 1 ≤ Y 2 := le_sup_left.trans h.j12.le

theorem Data.Y5_le_Y3 (h : Data U Y) : Y 5 ≤ Y 3 := le_sup_right.trans h.j35.le

theorem Data.not_Y5_le_Y2 [Finite Γ] (h : Data U Y) : ¬ Y 5 ≤ Y 2 := fun hle => by
  have h1 : Y 2 ⊔ Y 5 = Y 2 := sup_eq_left.mpr hle
  have h2 := h.j25
  rw [h1, h.Y4_top] at h2
  have := congrArg (fun K : Subgroup Γ => Nat.card K) h2
  have hΓ : Nat.card Γ = 443520 := by rw [← Subgroup.card_top]; exact h.card_top
  rw [h.card 2 (by norm_num)] at this
  rw [Subgroup.card_top, hΓ] at this
  exact absurd this (by decide)

theorem Data.card_eq (h : Data U Y) {j k : ℕ} (hj : j < 6) (hk : k < 6)
    (hc : Nat.card (Y j) = Nat.card (Y k)) : sz j = sz k := by
  rw [h.card j hj, h.card k hk] at hc
  exact hc

theorem Data.unique_of_sz (h : Data U Y) {a : ℕ} (ha : a < 6) (hu : ∀ j < 6, sz j = sz a → j = a) :
    ∀ Z : Subgroup Γ, U ≤ Z → Nat.card Z = Nat.card (Y a) → Z = Y a := by
  intro Z hZ hc
  obtain ⟨j, hj, rfl⟩ := h.complete Z hZ
  rw [hu j hj (h.card_eq hj ha hc)]

theorem Data.inv2 (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 2).map α.toMonoidHom = Y 2 :=
  map_eq_of_unique_card (h.S_le 2 (by norm_num))
    (h.unique_of_sz (a := 2) (by norm_num) (by decide)) α hα

theorem Data.inv3 (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 3).map α.toMonoidHom = Y 3 :=
  map_eq_of_unique_card (h.S_le 3 (by norm_num))
    (h.unique_of_sz (a := 3) (by norm_num) (by decide)) α hα

theorem Data.inv1 [Finite Γ] (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 1).map α.toMonoidHom = Y 1 := by
  have h2 := h.inv2 α hα
  refine map_eq_of_unique_pred α hα (fun Z => Z ≤ Y 2) h.Y1_le_Y2 (h.S_le 1 (by norm_num))
    (fun Z hZ => map_le_of_inv α h2 hZ) ?_
  intro Z hZ hZ2 hc
  obtain ⟨j, hj, rfl⟩ := h.complete Z hZ
  have hs := h.card_eq hj (by norm_num) hc
  have key : ∀ j < 6, sz j = sz 1 → j = 1 ∨ j = 5 := by decide
  rcases key j hj hs with rfl | rfl
  · rfl
  · exact absurd hZ2 h.not_Y5_le_Y2

theorem Data.inv5 [Finite Γ] (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 5).map α.toMonoidHom = Y 5 := by
  have h2 := h.inv2 α hα
  have h3 := h.inv3 α hα
  refine map_eq_of_unique_pred α hα (fun Z => Z ≤ Y 3 ∧ ¬ Z ≤ Y 2)
    ⟨h.Y5_le_Y3, h.not_Y5_le_Y2⟩ (h.S_le 5 (by norm_num))
    (fun Z hZ => ⟨map_le_of_inv α h3 hZ.1, fun hle => hZ.2 ((map_le_iff_of_eq α h2).mp hle)⟩) ?_
  intro Z hZ hZp hc
  obtain ⟨j, hj, rfl⟩ := h.complete Z hZ
  have hs := h.card_eq hj (by norm_num) hc
  have key : ∀ j < 6, sz j = sz 5 → j = 1 ∨ j = 5 := by decide
  rcases key j hj hs with rfl | rfl
  · exact absurd h.Y1_le_Y2 hZp.2
  · rfl

theorem Data.card_Y1 (h : Data U Y) : Nat.card (Y 1) = 2 ^ 7 * 3 := by
  rw [h.card 1 (by norm_num)]
  rfl

theorem Data.card_Y5 (h : Data U Y) : Nat.card (Y 5) = 2 ^ 7 * 3 := by
  rw [h.card 5 (by norm_num)]
  rfl

theorem Data.card_Y2 (h : Data U Y) : Nat.card (Y 2) = 2 ^ 7 * 3 * 5 := by
  rw [h.card 2 (by norm_num)]
  rfl

theorem Data.Y1_solvable [Finite Γ] (h : Data U Y) : Group.IsSolvable ↥(Y 1) :=
  A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 7) (b := 1)
    h.card_Y1

theorem Data.Y5_solvable [Finite Γ] (h : Data U Y) : Group.IsSolvable ↥(Y 5) :=
  A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 7) (b := 1)
    h.card_Y5

theorem Data.Y2_not_solvable [Finite Γ] (h : Data U Y) (hU : IsPGroup 2 ↥U) :
    ¬ Group.IsSolvable ↥(Y 2) :=
  not_isSolvable_of_no_overgroup (h.S_le 2 (by norm_num)) hU (e := 7) (m := 3) (p := 5)
    (by norm_num) h.card_Y2 (by norm_num) (by norm_num) fun H hUH _ hc => by
      obtain ⟨j, hj, rfl⟩ := h.complete H hUH
      rw [h.card j hj] at hc
      have key : ∀ j < 6, sz j ≠ 2 ^ 7 * 5 := by decide
      exact key j hj hc

theorem Data.Y2_levi5 [Finite Γ] (h : Data U Y) (hU : IsPGroup 2 ↥U) :
    ∃ ρ : ↥(Y 2) →* Equiv.Perm (Fin 5), IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range := by
  have hcard' : Nat.card ((Y 1).subgroupOf (Y 2)) = 2 ^ 7 * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Y1_le_Y2).toEquiv]
    exact h.card_Y1
  exact levi5_of_index_five (h.Y2_not_solvable hU) (e := 7) h.card_Y2 hcard'

theorem Data.good_pair [Finite Γ] (h : Data U Y) (hU : IsPGroup 2 ↥U) (𝒜 : Set (MulAut Γ))
    (h𝒜 : ∀ α ∈ 𝒜, U.map α.toMonoidHom = U) : GoodGam 𝒜 (Y 2) ∧ GoodGam 𝒜 (Y 3) := by
  have g1 : GoodGam 𝒜 (Y 1) := GoodGam.solvable (fun α hα => h.inv1 α (h𝒜 α hα)) h.Y1_solvable
  have g5 : GoodGam 𝒜 (Y 5) := GoodGam.solvable (fun α hα => h.inv5 α (h𝒜 α hα)) h.Y5_solvable
  refine ⟨GoodGam.levi5 (fun α hα => h.inv2 α (h𝒜 α hα)) (h.Y2_levi5 hU), ?_⟩
  rw [← h.j15]
  exact GoodGam.join g1 g5

theorem Data.sup_2_3 [Finite Γ] (h : Data U Y) : Y 2 ⊔ Y 3 = ⊤ := by
  rw [h.j23]
  exact h.Y4_top

end Abstract

section Instance

open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat Equiv CFSG.Quasithin.E2P

abbrev Lj (j : ℕ) : Subgroup (Perm (Fin 22)) :=
  Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat).getD j []}

abbrev Yj (j : ℕ) : Subgroup ↥Mgrp := (Lj j).subgroupOf Mgrp

theorem Lj_eq {j : ℕ} (hj : j < 6) :
    Lj j = Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[j]'(by simpa [cert, lat] using hj)} := by
  have h6 : j < (cert.tGens :: cert.lat).length := by simpa [cert, lat] using hj
  show Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat).getD j []} = _
  rw [List.getD_eq_getElem _ _ h6]

theorem join_ent {a b d : ℕ}
    (hw : (cert.joins.any fun j => j.1 == a && j.2.1 == b && j.2.2.1 == d) = true)
    (ha : a < 6) (hb : b < 6) (hd : d < 6) : Lj a ⊔ Lj b = Lj d := by
  obtain ⟨⟨j1, j2, j3, w⟩, hj, hjeq⟩ := List.any_eq_true.mp hw
  simp only [Bool.and_eq_true, beq_iff_eq] at hjeq
  obtain ⟨⟨h1, h2⟩, h3⟩ := hjeq
  subst h1 h2 h3
  have h6 : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  rw [Lj_eq ha, Lj_eq hb, Lj_eq hd]
  exact join_entry (rawIsEnc 22) cert (LatCert.closedOK_of_check cert_check)
    (by
      have := cert_check
      simp only [LatCert.check, Bool.and_eq_true] at this
      exact this.1.1.2) hj (by omega) (by omega) (by omega)

theorem Lj0_le : Lj 0 ≤ Mgrp := t_le_m_of_check (rawIsEnc 22) cert_check

private theorem hL2def : (cert.tGens :: cert.lat).getD 2 [] = cert.tGens ++
    [permOf 22 [[2, 3], [6, 9], [7, 12], [8, 11], [10, 21], [14, 19], [15, 16], [17, 20]]] := rfl

private theorem hL3def : (cert.tGens :: cert.lat).getD 3 [] = cert.tGens ++
    [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20], [15, 16]]] := rfl

theorem Lj2_le : Lj 2 ≤ Mgrp := by
  show Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat).getD 2 []} ≤ _
  rw [hL2def]
  exact closure_append_le (t_le_m_of_check (rawIsEnc 22) cert_check) SporB.m22_y2_mem

theorem Lj3_le : Lj 3 ≤ Mgrp := by
  show Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat).getD 3 []} ≤ _
  rw [hL3def]
  exact closure_append_le (t_le_m_of_check (rawIsEnc 22) cert_check) SporB.m22_y3_mem

theorem Lj1_le : Lj 1 ≤ Mgrp :=
  (le_sup_left.trans (join_ent (a := 1) (b := 3) (d := 3) (by decide +kernel) (by norm_num)
    (by norm_num) (by norm_num)).le).trans Lj3_le

theorem Lj5_le : Lj 5 ≤ Mgrp :=
  (le_sup_right.trans (join_ent (a := 3) (b := 5) (d := 3) (by decide +kernel) (by norm_num)
    (by norm_num) (by norm_num)).le).trans Lj3_le

theorem Lj4_le : Lj 4 ≤ Mgrp := by
  rw [← join_ent (a := 2) (b := 3) (d := 4) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)]
  exact sup_le Lj2_le Lj3_le

theorem Lj_le {j : ℕ} (hj : j < 6) : Lj j ≤ Mgrp := by
  interval_cases j
  · exact Lj0_le
  · exact Lj1_le
  · exact Lj2_le
  · exact Lj3_le
  · exact Lj4_le
  · exact Lj5_le

theorem Yj_sup {a b d : ℕ}
    (hw : (cert.joins.any fun j => j.1 == a && j.2.1 == b && j.2.2.1 == d) = true)
    (ha : a < 6) (hb : b < 6) (hd : d < 6) : Yj a ⊔ Yj b = Yj d := by
  rw [← Subgroup.subgroupOf_sup (Lj_le ha) (Lj_le hb), join_ent hw ha hb hd]

theorem Ugrp_le {j : ℕ} (hj : j < 6) : Ugrp ≤ Yj j := by
  have h0 : Lj 0 ≤ Lj j := by
    interval_cases j
    · exact le_rfl
    · exact le_sup_left.trans (join_ent (a := 0) (b := 1) (d := 1) (by decide +kernel)
        (by norm_num) (by norm_num) (by norm_num)).le
    · exact le_sup_left.trans (join_ent (a := 0) (b := 2) (d := 2) (by decide +kernel)
        (by norm_num) (by norm_num) (by norm_num)).le
    · exact le_sup_left.trans (join_ent (a := 0) (b := 3) (d := 3) (by decide +kernel)
        (by norm_num) (by norm_num) (by norm_num)).le
    · exact le_sup_left.trans (join_ent (a := 0) (b := 4) (d := 4) (by decide +kernel)
        (by norm_num) (by norm_num) (by norm_num)).le
    · exact le_sup_left.trans (join_ent (a := 0) (b := 5) (d := 5) (by decide +kernel)
        (by norm_num) (by norm_num) (by norm_num)).le
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact h0 hx

theorem data : Data Ugrp Yj where
  S_le := fun j hj => Ugrp_le hj
  complete := fun Z hZ => by
    obtain ⟨j, hj, -, hZeq, -⟩ := cert.overgroup_cases_idx (rawIsEnc 22) cert_check Z hZ
    have hj6 : j < 6 := by simpa [cert, lat] using hj
    refine ⟨j, hj6, ?_⟩
    rw [hZeq]
    show _ = (Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat).getD j []}).subgroupOf Mgrp
    rw [List.getD_eq_getElem _ _ hj]
  card := fun j hj => by
    have h6 : j < (cert.tGens :: cert.lat).length := by simpa [cert, lat] using hj
    show Nat.card ((Lj j).subgroupOf Mgrp) = _
    rw [SporB.card_subgroupOf_of_le (Lj_le hj), Lj_eq hj,
      cert.card_member_idx (rawIsEnc 22) (LatCert.closedOK_of_check cert_check)
        (LatCert.sizesOK_of_check cert_check) j h6]
    interval_cases j <;> rfl
  card_top := by
    rw [Subgroup.card_top]
    exact cert.card_m (rawIsEnc 22) (LatCert.closedOK_of_check cert_check)
      (LatCert.sizesOK_of_check cert_check)
  j12 := Yj_sup (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  j13 := Yj_sup (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  j15 := Yj_sup (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  j35 := Yj_sup (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  j23 := Yj_sup (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  j25 := Yj_sup (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

theorem U_sylow : IsSylowTwoOf Ugrp ⊤ :=
  cert.isSylowTwoOf_top (rawIsEnc 22) cert_check (k := 7) (m := 3465) (by decide) (by decide)
    (by omega)

theorem nParam_le_two_of_isM22
    {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hM22 : IsSporadic .M22 (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ ((2 : ℕ) : ℕ∞) := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hM22
  exact nParam_le_two_of_goodPair (U := Ugrp) U_sylow data.sup_2_3
    (fun 𝒜 h => data.good_pair U_sylow.2.1 𝒜 h) hLn
    (e₀.trans (MulEquiv.subgroupCongr mGens_closure).symm) hTs hFT

end Instance

end CFSG.Quasithin.RonanE114.C5.M22
