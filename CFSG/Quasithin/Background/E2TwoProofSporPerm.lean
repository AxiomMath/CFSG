module

public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM11
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L PermLat Equiv
open CFSG.QuasithinUnique.Unc25K1.Six (IsEnc)

namespace E2P

namespace SporB

section PermLat

variable {G : Type} [Group G] [Finite G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  {enc : G → R}

omit [Finite G] in
theorem card_subgroupOf_of_le {L M : Subgroup G} (h : L ≤ M) :
    Nat.card (L.subgroupOf M) = Nat.card L :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem hasInvPair_of_permLat (h : IsEnc enc) (c : LatCert G) (hc : c.check enc = true)
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
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[a]}) :
    HasInvPair ↥(Subgroup.closure {g | g ∈ c.mGens}) := by
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
  refine hasInvPair_of_unique hU (hUle hTa) (hUle hTb) (hne a ha hla hsa) (hne b hb hlb hsb)
    (huniq a ha hla hua) (huniq b hb hlb hub) ?_
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
    have h2 := (le_sup_right.trans (le_of_eq hYj)) hxM
    exact h2

end PermLat

@[expose] def fibreStab {α β : Type} (f : α → β) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, f (g x) = f x}
  one_mem' := fun _ => rfl
  mul_mem' := fun {g h} hg hh x => (hg (h x)).trans (hh x)
  inv_mem' := fun {g} hg x => by
    have := hg (g⁻¹ x)
    rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at this
    exact this.symm

theorem mem_fibreStab {α β : Type} {f : α → β} {g : Equiv.Perm α} :
    g ∈ fibreStab f ↔ ∀ x, f (g x) = f x := Iff.rfl

theorem closure_le_append {G : Type} [Group G] (A : List G) (x : G) :
    Subgroup.closure {g | g ∈ A} ≤ Subgroup.closure {g | g ∈ A ++ [x]} :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem closure_append_le {G : Type} [Group G] {A : List G} {x : G} {M : Subgroup G}
    (hA : Subgroup.closure {g | g ∈ A} ≤ M) (hx : x ∈ M) :
    Subgroup.closure {g | g ∈ A ++ [x]} ≤ M := by
  rw [Subgroup.closure_le]
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hA (Subgroup.subset_closure hg)
  · rw [List.mem_singleton.mp hg]
    exact hx

theorem t_le_m_of_check {G : Type} [Group G] [Finite G] {R : Type} [Mul R] [One R]
    [DecidableEq R] [Hashable R] {enc : G → R} (h : IsEnc enc) {c : LatCert G}
    (hc : c.check enc = true) :
    Subgroup.closure {g | g ∈ c.tGens} ≤ Subgroup.closure {g | g ∈ c.mGens} := by
  have htle : c.tleOK enc = true := by
    simp only [LatCert.check, Bool.and_eq_true] at hc
    exact hc.2
  exact c.t_le_m h (LatCert.closedOK_of_check hc) htle

section M11

open CFSG.QuasithinUnique.Vol2Native.A312L.M11Lat

theorem m11_x1_mem : permOf 11 [[2, 3], [5, 7], [6, 10], [8, 9]] ∈ Mgrp := by
  rw [show permOf 11 [[2, 3], [5, 7], [6, 10], [8, 9]] =
    evalW cert.mGens [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1] by decide +kernel]
  exact evalW_mem_closure _ _

theorem m11_x4_mem : permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]] ∈ Mgrp := by
  rw [show permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]] =
    evalW cert.mGens [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] by decide +kernel]
  exact evalW_mem_closure _ _

theorem hasInvPair_M11 : HasInvPair ↥Mgrp := by
  have hck := cert_check
  have hU : IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 11) hck (k := 4) (m := 495) (by decide) (by decide)
      (by omega)
  have htm := t_le_m_of_check (rawIsEnc 11) hck
  have hL1 : (cert.tGens :: cert.lat)[1]'(by decide) =
      cert.tGens ++ [permOf 11 [[2, 3], [5, 7], [6, 10], [8, 9]]] := rfl
  have hL4 : (cert.tGens :: cert.lat)[4]'(by decide) =
      cert.tGens ++ [permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]]] := rfl
  refine hasInvPair_of_permLat (rawIsEnc 11) cert hck hU (a := 1) (b := 4) (by decide)
    (by decide) ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  · rw [hL1]
    exact closure_le_append _ _
  · rw [hL4]
    exact closure_le_append _ _
  · rw [hL1]
    exact closure_append_le htm m11_x1_mem
  · rw [hL4]
    exact closure_append_le htm m11_x4_mem
  · rw [hL1, hL4]
    intro hle
    have hx : permOf 11 [[0, 3], [5, 10], [6, 9], [7, 8]] ∈
        Subgroup.closure {g | g ∈ cert.tGens ++ [permOf 11 [[2, 3], [5, 7], [6, 10], [8, 9]]]} :=
      hle (Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _)))
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

theorem asc86bClauseB_M11 : Asc86bClauseB .M11 :=
  @asc86bClauseB_of_hasInvPair .M11 ↥Mgrp inferInstance inferInstance
    (MulEquiv.subgroupCongr mGens_closure).symm hasInvPair_M11

end M11

section M22

open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

theorem m22_y3_mem :
    permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20], [15, 16]] ∈
      Mgrp := by
  rw [show permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20], [15, 16]] =
    evalW cert.mGens [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0] by decide +kernel]
  exact evalW_mem_closure _ _

theorem m22_y2_mem :
    permOf 22 [[2, 3], [6, 9], [7, 12], [8, 11], [10, 21], [14, 19], [15, 16], [17, 20]] ∈
      Mgrp := by
  rw [show permOf 22 [[2, 3], [6, 9], [7, 12], [8, 11], [10, 21], [14, 19], [15, 16], [17, 20]] =
    evalW cert.mGens [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0,
      1, 0, 1, 0, 1, 0] by decide +kernel]
  exact evalW_mem_closure _ _

@[expose] def m22Hexad (x : Fin 22) : Bool := decide (x.val ∈ [0, 1, 2, 9, 17, 19])

theorem hasInvPair_M22 : HasInvPair ↥Mgrp := by
  have hck := cert_check
  have hU : IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  have htm := t_le_m_of_check (rawIsEnc 22) hck
  have hL3 : (cert.tGens :: cert.lat)[3]'(by decide) = cert.tGens ++
      [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20], [15, 16]]] :=
    rfl
  have hL2 : (cert.tGens :: cert.lat)[2]'(by decide) = cert.tGens ++
      [permOf 22 [[2, 3], [6, 9], [7, 12], [8, 11], [10, 21], [14, 19], [15, 16], [17, 20]]] :=
    rfl
  refine hasInvPair_of_permLat (rawIsEnc 22) cert hck hU (a := 3) (b := 2) (by decide)
    (by decide) ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) (by decide) (by decide) ?_
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
        [17, 20]] ∈ Subgroup.closure {g | g ∈ cert.tGens ++
          [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20],
            [15, 16]]]} :=
      hle (Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _)))
    have hst : Subgroup.closure {g | g ∈ cert.tGens ++
        [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18], [12, 14], [13, 20],
          [15, 16]]]} ≤ fibreStab m22Hexad := by
      have key : (cert.tGens ++ [permOf 22 [[1, 2], [5, 21], [6, 7], [9, 19], [11, 18],
          [12, 14], [13, 20], [15, 16]]]).all (fun g => (List.finRange 22).all
            fun x => m22Hexad (g x) == m22Hexad x) = true := by decide +kernel
      rw [Subgroup.closure_le]
      exact fun g hg => mem_fibreStab.mpr fun x => beq_iff_eq.mp
        (List.all_eq_true.mp (List.all_eq_true.mp key g hg) x (List.mem_finRange x))
    exact absurd ((mem_fibreStab.mp (hst hx)) 2) (by decide +kernel)

theorem asc86bClauseB_M22 : Asc86bClauseB .M22 :=
  @asc86bClauseB_of_hasInvPair .M22 ↥Mgrp inferInstance inferInstance
    (MulEquiv.subgroupCongr mGens_closure).symm hasInvPair_M22

end M22

end SporB

end E2P

end CFSG.Quasithin
