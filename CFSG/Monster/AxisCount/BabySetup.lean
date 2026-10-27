module

public import CFSG.Monster.AxisCount.BabyCount
public import CFSG.Monster.AxisCount.BabyCover
public import CFSG.Monster.AxisCount.BabyCoverCheck
public import CFSG.Monster.AxisCount.BabyIdentCheck
public import CFSG.Monster.AxisCount.BabyInvCheck
public import Certificates.Certificate16026

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.Baby

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short

open CFSG.Monster.B.TwoA (hE0)

theorem orbitOK_all
    {j : ℕ} (hj : j < 10) : BabyOrbits (bo j) := by
  interval_cases j
  · exact orbitOK_0
  · exact orbitOK_1
  · exact orbitOK_2
  · exact orbitOK_3
  · exact orbitOK_4
  · exact orbitOK_5
  · exact orbitOK_6
  · exact orbitOK_7
  · exact orbitOK_8
  · exact orbitOK_9

theorem orbitFacts
    {j : ℕ} (hj : j < 10) :
    OrbitFacts (bo j).U (bo j).h.toList (bo j).lam.toList (bo j).size.toList :=
  orbitFacts_of (orbitOK_all hj)

theorem wordLin_mem_Jstar_of_jWords
    {j : ℕ} (hj : j < 10) {w : List Native.Gen}
    (hw : w ∈ jWords j) : wordLin w ∈ Jstar := by
  obtain ⟨hτ, hfix⟩ := (orbitIdent_all j hj).2.2.1 w hw
  exact mem_Jstar_of_fix (wordLin_mem_Gvis w hτ) hfix

theorem mem_jWords_U {j : ℕ} {w : List Native.Gen} (hw : w ∈ (bo j).U) : w ∈ jWords j := by
  simp [jWords, hw]

theorem mem_jWords_h {j : ℕ} {w : List Native.Gen} (hw : w ∈ (bo j).h.toList) : w ∈ jWords j := by
  simp only [jWords, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hw))

theorem mem_jWords_kappaPlus {j : ℕ} {w : List Native.Gen} (hw : w ∈ (bo j).kappaPlus.toList) :
    w ∈ jWords j := by
  simp only [jWords, List.mem_append]
  exact Or.inl (Or.inr hw)

theorem mem_jWords_kappaMinus {j : ℕ} {w : List Native.Gen} (hw : w ∈ (bo j).kappaMinus.toList) :
    w ∈ jWords j := by
  simp only [jWords, List.mem_append]
  exact Or.inr hw

theorem shapeOK_eq_true : shapeOK = true :=
  Certificates.certificate16026.1

theorem shape_of {j : ℕ} (hj : j < 10) :
    (bo j).kappaPlus.size = (bo j).h.size ∧ (bo j).kappaMinus.size = (bo j).h.size ∧
      (bo j).tPlus.size = (bo j).h.size ∧ (bo j).tMinus.size = (bo j).h.size ∧
      (bo j).size.size = (bo j).h.size ∧ (bo j).lam.size = (bo j).h.size := by
  have h := List.all_eq_true.1 shapeOK_eq_true j (List.mem_range.2 hj)
  simpa [Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem getElem!_mem_toList {α : Type*} [Inhabited α] (a : Array α) {r : ℕ} (hr : r < a.size) :
    a[r]! ∈ a.toList := by
  rw [getElem!_pos a r hr]
  exact List.getElem_mem (by simpa using hr)

theorem U_mem_Jstar
    {j : ℕ} (hj : j < 10) : ∀ w ∈ (bo j).U, wordLin w ∈ Jstar := fun _ hw =>
  wordLin_mem_Jstar_of_jWords hj (mem_jWords_U hw)

theorem hs_mem_all
    {j : ℕ} (hj : j < 10) : ∀ w ∈ (bo j).h.toList, wordLin w ∈ Jstar := fun _ hw =>
  wordLin_mem_Jstar_of_jWords hj (mem_jWords_h hw)

theorem U_fix
    {j : ℕ} (hj : j < 10) : ∀ w ∈ (bo j).U, wordLin w (vv j) = vv j :=
  (orbitIdent_all j hj).1

theorem hW_mem_Jstar
    {j : ℕ} (hj : j < 10) {r : ℕ} (hr : r < nrec j) :
    wordLin (hW j r) ∈ Jstar :=
  wordLin_mem_Jstar_of_jWords hj (mem_jWords_h (getElem!_mem_toList _ hr))

theorem kW_mem_Jstar
    {j : ℕ} (hj : j < 10) {r : ℕ} (hr : r < nrec j) (ε : Bool) :
    wordLin (kW j r ε) ∈ Jstar := by
  obtain ⟨h1, h2, -⟩ := shape_of hj
  cases ε
  · exact wordLin_mem_Jstar_of_jWords hj (mem_jWords_kappaMinus
      (getElem!_mem_toList _ (by rw [h2]; exact hr)))
  · exact wordLin_mem_Jstar_of_jWords hj (mem_jWords_kappaPlus
      (getElem!_mem_toList _ (by rw [h1]; exact hr)))

theorem tgt_lt
    {j : ℕ} (hj : j < 10) {r : ℕ} (hr : r < nrec j) (ε : Bool) : tgt j r ε < 10 :=
  ((orbitIdent_all j hj).2.1 r hr ε).1

theorem wordLin_tpw (ε : Bool) : wordLin (tpw ε) = tpow tauB ε := by
  cases ε
  · exact wordLin_tauPow_two
  · show wordLin [Native.Gen.tau] = tauB
    rw [wordLin_cons, wordLin_nil, one_mul]
    rfl

theorem spec_j
    {j : ℕ} (hj : j < 10) {r : ℕ} (hr : r < nrec j) (ε : Bool) :
    (wordLin (kW j r ε) * tpow tauB ε * wordLin (hW j r)) • vv j = vv (tgt j r ε) := by
  have h := ((orbitIdent_all j hj).2.1 r hr ε).2
  rw [xW, wordLin_append, wordLin_append, wordLin_tpw, ← mul_assoc] at h
  exact h

theorem cover_j
    {j : ℕ} (hj : j < 10) :
    (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ⊆ ⋃ r : Fin (nrec j),
      DoubleCoset.doubleCoset (wordLin (hW j r)) ((Jstar ⊓ Nfr : Subgroup _) : Set _)
        (wordGroup (bo j).U : Set _) := by
  refine ((orbitFacts hj).cover_doubleCoset (U_mem_Jstar hj) (hs_mem_all hj)
    babyDelta_ncard_le).trans ?_
  refine Set.iUnion_mono fun r => ?_
  rw [hW, ← Array.getElem!_toList]

theorem disjoint_j
    {j : ℕ} (hj : j < 10) :
    Pairwise (Function.onFun Disjoint fun r : Fin (nrec j) =>
      DoubleCoset.doubleCoset (wordLin (hW j r)) ((Jstar ⊓ Nfr : Subgroup _) : Set _)
        (wordGroup (bo j).U : Set _)) := by
  intro r r' hne
  have h := (orbitFacts hj).pairwise_disjoint_doubleCoset (U_mem_Jstar hj) (hs_mem_all hj)
    (i := (r : Fin ((bo j).h.toList.length))) (j := (r' : Fin ((bo j).h.toList.length))) hne
  simpa only [Function.onFun, hW, ← Array.getElem!_toList] using h

theorem natCard_j
    {j : ℕ} (hj : j < 10) (r : Fin (nrec j)) :
    Nat.card (DoubleCoset.doubleCoset (wordLin (hW j r)) ((Jstar ⊓ Nfr : Subgroup _) : Set _)
        (wordGroup (bo j).U : Set _)) = Nat.card (Jstar ⊓ Nfr : Subgroup _) * sz j r := by
  have h := (orbitFacts hj).natCard_doubleCoset (U_mem_Jstar hj) (hs_mem_all hj) r
  simpa only [hW, sz, ← Array.getElem!_toList] using h

theorem relIndex_Jstar_inf_Nfr_eq :
    (Jstar ⊓ Nfr).relIndex Jstar = 46575 :=
  (orbitFacts (j := 0) (by norm_num)).relIndex_Jstar_inf_Nfr (U_mem_Jstar (by norm_num))
    (hs_mem_all (by norm_num)) babyDelta_ncard_le

theorem wordLin_segsWord_mem_Cgen (segs : List Seg)
    (h : ∀ w, Seg.blk w ∈ segs → (∀ g ∈ w, g ≠ Native.Gen.tau) ∧ wordLin w aStar = aStar) :
    wordLin (segsWord segs) ∈ Cgen := by
  induction segs with
  | nil => exact Cgen.one_mem
  | cons s l ih =>
    rw [segsWord, List.flatMap_cons, wordLin_append]
    refine Cgen.mul_mem (ih fun w hw => h w (List.mem_cons_of_mem _ hw)) ?_
    cases s with
    | blk w =>
      obtain ⟨hτ, hfix⟩ := h w List.mem_cons_self
      exact Jstar_le_Cgen (mem_Jstar_of_fix (wordLin_mem_Gvis w hτ) hfix)
    | tau e =>
      show wordLin (Native.Gen.tauPow e) ∈ Cgen
      rw [wordLin_tauPow]
      exact Cgen.pow_mem tauB_mem_Cgen e

theorem vv_mem_orbit_Cgen
    {j : ℕ} (hj : j < 10) :
    vv j ∈ MulAction.orbit Cgen aStarMinus :=
  ⟨⟨wordLin (gW j), wordLin_segsWord_mem_Cgen _ (orbitIdent_all j hj).2.2.2⟩, rfl⟩

theorem vv_zero : vv 0 = aStarMinus := by
  have h : gW 0 = [] := rfl
  rw [vv, h, wordLin_nil]
  rfl

theorem tfin_val
    {j : ℕ} (hj : j < 10) {r : ℕ} (hr : r < nrec j) (ε : Bool) :
    ((tfin j r ε : Fin 10) : ℕ) = tgt j r ε :=
  Nat.mod_eq_of_lt (tgt_lt hj hr ε)

noncomputable def babySetup :
    Setup (SpaceB ≃ₗ[ℚ] SpaceB) SpaceB (Fin 10) (fun j => Fin (nrec j)) where
  H := Jstar
  N' := Jstar ⊓ Nfr'
  N := Jstar ⊓ Nfr
  τ := tauB
  a := hE0
  v := fun j => vv j
  U := fun j => wordGroup (bo j).U
  h := fun j r => wordLin (hW j r)
  κ := fun j r ε => wordLin (kW j r ε)
  t := fun j r ε => tfin j r ε
  N'_le_N := Jstar_inf_Nfr'_le
  N_le_H := Jstar_inf_Nfr_le_Jstar
  relIndex_N'_N := relIndex_Jstar_inf_Nfr'_Nfr
  conj_mem := fun _ hn => tauB_conj_mem_Jstar_inf_Nfr' hn
  conj_inv_mem := fun _ hn => tauB_inv_conj_mem_Jstar_inf_Nfr' hn
  a_mem := hE0_mem_Jstar_inf_Nfr
  a_notMem := hE0_notMem_Jstar_inf_Nfr'
  a_conj := hE0_inv_mul_tauB_mul_hE0
  U_le_H := fun j => wordGroup_le_of_mem (U_mem_Jstar j.2)
  U_le_stabilizer := fun j => wordGroup_le_stabilizer (U_fix j.2)
  h_mem := fun j r => hW_mem_Jstar j.2 r.2
  κ_mem := fun j r ε => kW_mem_Jstar j.2 r.2 ε
  cover := fun j => cover_j j.2
  spec := fun j r ε => by
    show (wordLin (kW j r ε) * tpow tauB ε * wordLin (hW j r)) • vv j = vv (tfin j r ε)
    rw [tfin_val j.2 r.2 ε]
    exact spec_j j.2 r.2 ε

instance :
    Finite babySetup.H := (inferInstance : Finite Jstar)

theorem babySetup_disjoint :
    ∀ i, Pairwise (Function.onFun Disjoint (babySetup.D i)) :=
  fun i => disjoint_j i.2

theorem babySetup_k
    {j : Fin 10} (r : Fin (nrec j)) : babySetup.k j r = sz j r :=
  babySetup.k_eq (natCard_j j.2 r)

theorem babyM_data : ∀ t i : Fin 10,
    (∑ r : Fin (nrec i), sz i r * ((if tfin i r true = t then 1 else 0) +
      (if tfin i r false = t then 1 else 0))) = babyM t i :=
  Certificates.certificate16026.2

theorem babySetup_M :
    babySetup.M = babyM := by
  funext t i
  rw [← babyM_data t i]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [babySetup_k r]
  rfl

theorem babySetup_L :
    babySetup.L = babyL :=
  babySetup.L_eq (two_mul_natCard_Jstar relIndex_Jstar_inf_Nfr_eq)

theorem babySetup_orb_injective :
    Function.Injective babySetup.orb := by
  refine babySetup.orb_injective_of_invariant (fun x => (xStarCoord x, trA2 x)) ?_ ?_
  · intro c hc x
    show (xStarCoord (c • x), trA2 (c • x)) = (xStarCoord x, trA2 x)
    rw [xStarCoord_smul_of_mem_Jstar hc, trA2_smul_of_mem_Gvis (Jstar_le_Gvis hc)]
  · exact baby_inv_injective

theorem babySetup_v_mem_orbit :
    ∀ i, babySetup.v i ∈ MulAction.orbit Cgen aStarMinus :=
  fun i => vv_mem_orbit_Cgen i.2

theorem natCard_Cgen :
    Nat.card Cgen = 11707448673375 * Nat.card Jstar :=
  natCard_Cgen_eq_babyTotal_mul_Jstar babySetup rfl rfl vv_zero babySetup_disjoint
    babySetup_orb_injective babySetup_M babySetup_L babySetup_v_mem_orbit

theorem natCard_orbit_Cgen_aStarMinus :
    Nat.card (MulAction.orbit Cgen aStarMinus) = 11707448673375 := by
  have h := natCard_Cgen_eq_orbit_mul_Jstar
  rw [natCard_Cgen] at h
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm

theorem natCard_Cbar :
    Nat.card Cbar = 4154781481226426191177580544000000 :=
  natCard_Cbar_of natCard_Cgen

theorem natCard_Cbar_eq_monsterBabyOrder :
    Nat.card Cbar = CFSG.Open.monsterBabyOrder :=
  natCard_Cbar.trans rfl

end CFSG.Monster.AxisCount.Baby
