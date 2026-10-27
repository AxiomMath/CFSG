module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLat
public import CFSG.Quasithin.Background.E2TwoProofSporM12

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.Quasithin.Background.RonanE43Out

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L PermLat Equiv
open CFSG.QuasithinUnique.Unc25K1.Six (IsEnc)
open CFSG.Quasithin.E2P.SporB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

section PermLat

variable {s : TauCeti.SporadicName} {G : Type} [Group G] [Finite G] {R : Type} [Mul R] [One R]
  [DecidableEq R] [Hashable R] {enc : G → R}

theorem asch54SporGenAt_of_permLat (h : IsEnc enc) (c : LatCert G) (hc : c.check enc = true)
    (hsC : Nonempty (s.Group ≃* ↥(Subgroup.closure {g | g ∈ c.mGens})))
    (hP0 : ∀ (X : Type) [Group X] [Finite X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    (hO : LieOrderFormulasInput)
    (hOut : Nat.card (Outer ↥(Subgroup.closure {g | g ∈ c.mGens})) ≤ 2)
    (hU : IsSylowTwoOf ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})) ⊤)
    {a b : ℕ} (ha : a < (c.tGens :: c.lat).length) (hb : b < (c.tGens :: c.lat).length)
    (hTa : Subgroup.closure {g | g ∈ c.tGens} ≤
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[a]})
    (hTb : Subgroup.closure {g | g ∈ c.tGens} ≤
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[b]})
    (hla : Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[a]} ≤ Subgroup.closure {g | g ∈ c.mGens})
    (hlb : Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[b]} ≤ Subgroup.closure {g | g ∈ c.mGens})
    (hua : ∀ j < (c.tGens :: c.lat).length, c.sizes.getD j 0 = c.sizes.getD a 0 → j = a)
    (hub : ∀ j < (c.tGens :: c.lat).length, c.sizes.getD j 0 = c.sizes.getD b 0 → j = b)
    (hsa : c.sizes.getD a 0 ≠ c.msize) (hsb : c.sizes.getD b 0 ≠ c.msize)
    (hmax : ∀ j < (c.tGens :: c.lat).length, c.sizes.getD a 0 ∣ c.sizes.getD j 0 →
      c.sizes.getD j 0 ≠ c.msize → j = a)
    (hnot : ¬ Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[b]} ≤
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[a]})
    {k : ℕ} (hka : calL0FreeCheck k (c.sizes.getD a 0) = true)
    (hkb : calL0FreeCheck k (c.sizes.getD b 0) = true) : Asch54SporGenAt s := by
  set M := Subgroup.closure {g | g ∈ c.mGens} with hMdef
  set U := (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf M with hUdef
  have hcl := LatCert.closedOK_of_check hc
  have hsz := LatCert.sizesOK_of_check hc
  have hM : Nat.card M = c.msize := c.card_m h hcl hsz
  have hcard : ∀ j (hj : j < (c.tGens :: c.lat).length),
      Nat.card (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]}) = c.sizes.getD j 0 :=
    fun j hj => c.card_member_idx h hcl hsz j hj
  have hcases := fun (Y : Subgroup M) (hY : U ≤ Y) => c.overgroup_cases_idx h hc Y hY
  have hUle : ∀ {L : Subgroup G}, Subgroup.closure {g | g ∈ c.tGens} ≤ L →
      U ≤ L.subgroupOf M := fun hL x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hL hx
  have huniq : ∀ i (hi : i < (c.tGens :: c.lat).length),
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]} ≤ M →
      (∀ j < (c.tGens :: c.lat).length, c.sizes.getD j 0 = c.sizes.getD i 0 → j = i) →
      ∀ Y : Subgroup M, U ≤ Y →
        Nat.card Y = Nat.card ((Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]}).subgroupOf M) →
        Y = (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]}).subgroupOf M := by
    intro i hi hli hu Y hY hYc
    obtain ⟨j, hj, hjM, hYj, hcj⟩ := hcases Y hY
    have hji : j = i := hu j hj (by
      rw [← hcj, ← card_subgroupOf_of_le hjM, ← hYj, hYc, card_subgroupOf_of_le hli,
        hcard i hi])
    subst hji
    exact hYj
  have hne : ∀ i (hi : i < (c.tGens :: c.lat).length),
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]} ≤ M → c.sizes.getD i 0 ≠ c.msize →
        (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]}).subgroupOf M ≠ ⊤ := by
    intro i hi hli hs htop
    apply hs
    rw [← hcard i hi, ← card_subgroupOf_of_le hli, htop, Subgroup.card_top, hM]
  have hgen : (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[a]}).subgroupOf M ⊔
      (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[b]}).subgroupOf M = ⊤ := by
    obtain ⟨j, hj, hjM, hYj, hcj⟩ := hcases _ ((hUle hTa).trans le_sup_left)
    by_cases hs : c.sizes.getD j 0 = c.msize
    · have hjtop : Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]} = M :=
        Subgroup.eq_of_le_of_card_ge hjM (by rw [hM, hcj, hs])
      rw [hYj, hjtop, Subgroup.subgroupOf_self]
    · exfalso
      have hdvd : c.sizes.getD a 0 ∣ c.sizes.getD j 0 := by
        rw [← hcard a ha, ← card_subgroupOf_of_le hla, ← hcj, ← card_subgroupOf_of_le hjM, ← hYj]
        exact Subgroup.card_dvd_of_le le_sup_left
      have hja := hmax j hj hdvd hs
      subst hja
      apply hnot
      intro x hx
      have hxM : (⟨x, hlb hx⟩ : M) ∈
          (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[b]}).subgroupOf M := hx
      exact (le_sup_right.trans (le_of_eq hYj)) hxM
  refine asch54SporGenAt_of_isLPair_of_aut hsC hP0 hOut (T₀ := U) hU
    ⟨hUle hTa, hUle hTb, hne a ha hla hsa, hne b hb hlb hsb,
      not_hasCompFactor_isCalL0_of_dvd hO hka
        (dvd_of_eq (by rw [card_subgroupOf_of_le hla, hcard a ha])),
      not_hasCompFactor_isCalL0_of_dvd hO hkb
        (dvd_of_eq (by rw [card_subgroupOf_of_le hlb, hcard b hb])), hgen⟩
    fun ψ hψ => ⟨map_eq_of_unique_card (hUle hTa) (huniq a ha hla hua) ψ hψ,
      map_eq_of_unique_card (hUle hTb) (huniq b hb hlb hub) ψ hψ⟩

end PermLat


theorem asch54SporGenAt_m11 :
    Asch54SporGenAt .M11 := by
  have hOut : Nat.card (Outer ↥M11Lat.Mgrp) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.Schreier.at_m11_schreier.1
      (MulEquiv.subgroupCongr M11Lat.mGens_closure)
  have hΓ : Nat.card ↥M11Lat.Mgrp = 7920 :=
    (Nat.card_congr (MulEquiv.subgroupCongr M11Lat.mGens_closure).toEquiv).trans
      CFSG.Sporadic.Mathieu.card_M11
  exact asch54SporGenAt_of_hasInvPair_of_dvd
    (CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv.map fun f =>
      f.symm.trans (MulEquiv.subgroupCongr M11Lat.mGens_closure).symm)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut hasInvPair_M11
    (k := 4) (by decide +kernel) (dvd_of_eq hΓ)

theorem asch54SporGenAt_m12 :
    Asch54SporGenAt .M12 := by
  have hOut : Nat.card (Outer ↥m12Grp) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv
      CFSG.ComponentClassification.M12Cover.card_outer.le
      (MulEquiv.subgroupCongr M12Lat.mGens_closure)
  have hΓ : Nat.card ↥m12Grp = 95040 :=
    (Nat.card_congr (MulEquiv.subgroupCongr M12Lat.mGens_closure).toEquiv).trans
      CFSG.Sporadic.Mathieu.card_M12
  exact asch54SporGenAt_of_hasInvPair_of_dvd
    (CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv.map fun f =>
      f.symm.trans (MulEquiv.subgroupCongr M12Lat.mGens_closure).symm)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut hasInvPair_M12
    (k := 6) (by decide +kernel) (dvd_of_eq hΓ)

theorem asch54SporGenAt_m22 :
    Asch54SporGenAt .M22 := by
  have hck := M22Lat.cert_check
  have hU : IsSylowTwoOf M22Lat.Ugrp ⊤ :=
    M22Lat.cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  have htm := t_le_m_of_check (rawIsEnc 22) hck
  have hL3 : (M22Lat.cert.tGens :: M22Lat.cert.lat)[3]'(by decide) = M22Lat.cert.tGens ++
      [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20], [15, 16]]] :=
    rfl
  have hL2 : (M22Lat.cert.tGens :: M22Lat.cert.lat)[2]'(by decide) = M22Lat.cert.tGens ++
      [permOf 22 [[2, 3], [6, 9], [7, 12], [8, 11], [10, 21], [14, 19], [15, 16], [17, 20]]] :=
    rfl
  have hOut : Nat.card (Outer ↥M22Lat.Mgrp) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv
      (CFSG.Quasithin.RonanE43.card_outer_le_of_card_mulAut_le
        CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card)
      (MulEquiv.subgroupCongr M22Lat.mGens_closure)
  refine asch54SporGenAt_of_permLat (rawIsEnc 22) M22Lat.cert hck
    (CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv.map fun f =>
      f.symm.trans (MulEquiv.subgroupCongr M22Lat.mGens_closure).symm)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut hU (a := 3) (b := 2)
    (by decide) (by decide) ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_ (k := 7) (by decide +kernel) (by decide +kernel)
  · rw [hL3]
    exact closure_le_append _ _
  · rw [hL2]
    exact closure_le_append _ _
  · rw [hL3]
    exact closure_append_le htm m22_y3_mem
  · rw [hL2]
    exact closure_append_le htm m22_y2_mem
  · rw [hL3, hL2]
    intro hle
    have hx : permOf 22 [[2, 3], [6, 9], [7, 12], [8, 11], [10, 21], [14, 19], [15, 16],
        [17, 20]] ∈ Subgroup.closure {g | g ∈ M22Lat.cert.tGens ++
          [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20],
            [15, 16]]]} :=
      hle (Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _)))
    have hst : Subgroup.closure {g | g ∈ M22Lat.cert.tGens ++
        [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20],
          [15, 16]]]} ≤ fibreStab m22Hexad := by
      have key : (M22Lat.cert.tGens ++ [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18],
          [12, 14], [13, 20], [15, 16]]]).all (fun g => (List.finRange 22).all
            fun x => m22Hexad (g x) == m22Hexad x) = true := by decide +kernel
      rw [Subgroup.closure_le]
      exact fun g hg => mem_fibreStab.mpr fun x => beq_iff_eq.mp
        (List.all_eq_true.mp (List.all_eq_true.mp key g hg) x (List.mem_finRange x))
    exact absurd ((mem_fibreStab.mp (hst hx)) 2) (by decide +kernel)

end CFSG.LocalAnalysis.WeakClosure81

end
