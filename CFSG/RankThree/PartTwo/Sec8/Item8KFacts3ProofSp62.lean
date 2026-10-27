module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPerfect
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalElt

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

open Equiv Subgroup
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.RankThree.PartTwo.Sec4.Item434Kit

@[expose] def zMat (i : Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  dec6 (zCode i)

@[expose] def zAct (i : Fin 3) (n : ℕ) (y : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  (fun v => (zMat i).mulVec v)^[n] y

@[expose] def wAct (w : Fin 3 → ZMod 3) (y : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  zAct 0 (w 0).val (zAct 1 (w 1).val (zAct 2 (w 2).val y))

@[expose] def bF (x y : Fin 6 → ZMod 2) : ZMod 2 :=
  x ⬝ᵥ (CFSG.Quasithin.H13.KGCert.g22Form.mulVec y)

@[expose] def eV (j : Fin 6) : Fin 6 → ZMod 2 :=
  Pi.single j 1

@[expose] def pos (k : Fin 3) : Fin 6 :=
  ⟨k, by omega⟩

@[expose] def pos3 (k : Fin 3) : Fin 6 :=
  ⟨k + 3, by omega⟩

@[expose] def vAct : H6 →* Perm (Fin 6 → ZMod 2) where
  toFun g :=
    { toFun := fun y => (mat6 g).mulVec y
      invFun := fun y => (mat6 g⁻¹).mulVec y
      left_inv := fun y => by
        simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
      right_inv := fun y => by
        simp only [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec] }
  map_one' := by
    ext y
    simp
  map_mul' g h := by
    ext y
    simp [Matrix.mulVec_mulVec]

theorem vAct_apply (g : H6) (y : Fin 6 → ZMod 2) : vAct g y = (mat6 g).mulVec y :=
  rfl

theorem vAct_sub (g : H6) (x y : Fin 6 → ZMod 2) : vAct g (x - y) = vAct g x - vAct g y := by
  simp only [vAct_apply, Matrix.mulVec_sub]

theorem bF_vAct (g : H6) (x y : Fin 6 → ZMod 2) : bF (vAct g x) (vAct g y) = bF x y := by
  simp only [bF, vAct_apply]
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
    CFSG.AGLEmbedding.KFactProofs.Sp62Local.mat6_isIso, ← Matrix.dotProduct_mulVec]

theorem vAct_comm {h u : H6} (hh : h ∈ Subgroup.centralizer {u}) (y : Fin 6 → ZMod 2) :
    vAct h (vAct u y) = vAct u (vAct h y) := by
  rw [mem_centralizer_singleton_iff] at hh
  rw [← Perm.mul_apply, ← Perm.mul_apply, ← map_mul, ← map_mul, hh]

theorem vAct_vecElt (w : Fin 3 → ZMod 3) (y : Fin 6 → ZMod 2) :
    vAct (vecElt zH w) y = wAct w y := by
  have hz : ∀ (i : Fin 3) (n : ℕ) (y : Fin 6 → ZMod 2), vAct (zH i ^ n) y = zAct i n y := by
    intro i n y
    have h1 : ⇑(vAct (zH i)) = fun v => (zMat i).mulVec v := by
      funext v
      rw [vAct_apply, mat6_zH]
      rfl
    rw [map_pow, Perm.coe_pow, h1]
    rfl
  simp only [vecElt, map_mul, Perm.mul_apply, hz, wAct]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem gammaOne_check : ∀ x : Fin 3 → ZMod 3, ∀ k : Fin 3, x k ≠ 0 → (∀ i, i ≠ k → x i = 0) →
    (∀ y : Fin 6 → ZMod 2, ∀ r : Fin 6, r ≠ pos k → r ≠ pos3 k → (wAct x y - y) r = 0) ∧
    (∀ w : Fin 3 → ZMod 3, wAct w (wAct x (eV (pos k)) - eV (pos k)) =
      wAct x (eV (pos k)) - eV (pos k) → w k = 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem gammaTwo_check : ∀ x : Fin 3 → ZMod 3, ∀ l : Fin 3, x l = 0 → (∀ i, i ≠ l → x i ≠ 0) →
    (∀ y : Fin 6 → ZMod 2, wAct x y = y → ∀ r : Fin 6, r ≠ pos l → r ≠ pos3 l → y r = 0) ∧
    wAct x (eV (pos l)) = eV (pos l) ∧
    (∀ w : Fin 3 → ZMod 3, wAct w (eV (pos l)) = eV (pos l) → w l = 0) := by
  decide +kernel

@[expose] def frameP (x : Fin 3 → ZMod 3) (y y' : Fin 6 → ZMod 2) : Prop :=
  bF y' (wAct x y') = 1 ∧ ((bF y y' = 0 ∧ bF (wAct x y) y' = 0) ∨ y' = y ∨ y' = wAct x y ∨
    y' = wAct x (wAct x y))

instance (x : Fin 3 → ZMod 3) (y y' : Fin 6 → ZMod 2) : Decidable (frameP x y y') := by
  unfold frameP
  infer_instance

@[expose] def repF : Fin 4 → Fin 6 → ZMod 2 :=
  ![eV 0, eV 0 + eV 1 + eV 2, eV 1 + eV 2 + eV 3, eV 0 + eV 1 + eV 2 + eV 3]

@[expose] def baseG3 : Fin 2 → Fin 3 → ZMod 3 :=
  ![![1, 1, 1], ![1, 1, 2]]

@[expose] def rotV (v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  ![v 2, v 0, v 1]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem gammaThree_cases : ∀ x : Fin 3 → ZMod 3, x 0 ≠ 0 → x 1 ≠ 0 → x 2 ≠ 0 →
    ∃ j : Fin 2, ∃ r : Fin 3, x = rotV^[r] (baseG3 j) ∨
      x = rotV^[r] (baseG3 j) + rotV^[r] (baseG3 j) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem gammaThree_frames_check : ∀ j : Fin 2, ∀ y : Fin 6 → ZMod 2,
    bF y (wAct (baseG3 j) y) = 1 → ∃ i : Fin 4,
      ∀ y' : Fin 6 → ZMod 2, frameP (baseG3 j) y y' ↔ frameP (baseG3 j) (repF i) y' := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem gammaThree_planes_check : ∀ j : Fin 2,
    bF (eV 0) (wAct (baseG3 j) (eV 0)) = 1 ∧
    (∀ y : Fin 6 → ZMod 2, frameP (baseG3 j) (eV 0) y → ∃ k : Fin 3,
      y = eV (pos k) ∨ y = wAct (baseG3 j) (eV (pos k)) ∨
        y = wAct (baseG3 j) (wAct (baseG3 j) (eV (pos k)))) ∧
    (∀ k : Fin 3, frameP (baseG3 j) (eV 0) (eV (pos k))) ∧
    ∀ k : Fin 3, eV (pos3 k) = eV (pos k) ∨ eV (pos3 k) = wAct (baseG3 j) (eV (pos k)) ∨
      eV (pos3 k) = wAct (baseG3 j) (wAct (baseG3 j) (eV (pos k))) := by
  decide +kernel

theorem card_planeSet : ∀ k : Fin 3, (Finset.univ.filter fun y : Fin 6 → ZMod 2 =>
    ∀ r : Fin 6, r ≠ pos k → r ≠ pos3 k → y r = 0).card = 4 := by
  decide

theorem coord_eq_zero_of_gammaOne {x : Fin 3 → ZMod 3} {k : Fin 3} (hk : x k ≠ 0)
    (hx : ∀ i, i ≠ k → x i = 0) {H : Subgroup H6} (hP : Group.IsPerfect H)
    (hH : H ≤ Subgroup.centralizer {vecElt zH x}) {w : Fin 3 → ZMod 3} (hw : vecElt zH w ∈ H) :
    w k = 0 := by
  classical
  obtain ⟨hsub, hfix⟩ := gammaOne_check x k hk hx
  set u := vecElt zH x with hu
  set Y : Set (Fin 6 → ZMod 2) := Set.range fun y => vAct u y - y with hY
  set P : Finset (Fin 6 → ZMod 2) := Finset.univ.filter
    fun y => ∀ r : Fin 6, r ≠ pos k → r ≠ pos3 k → y r = 0 with hPdef
  have hP4 : P.card = 4 := card_planeSet k
  have hYP : Y ⊆ (P : Set (Fin 6 → ZMod 2)) := by
    rintro _ ⟨y, rfl⟩
    simp only [hPdef, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [hu, vAct_vecElt]
    exact hsub y
  have hY4 : Nat.card Y ≤ 4 := by
    rw [Nat.card_coe_set_eq, ← hP4, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hYP (Finset.finite_toSet P)
  have hHY : ∀ h ∈ H, ∀ y ∈ Y, vAct h y ∈ Y := by
    rintro h hh _ ⟨y, rfl⟩
    refine ⟨vAct h y, ?_⟩
    simp only
    rw [vAct_sub, vAct_comm (hH hh)]
  have h1 := fixes_of_isPerfect vAct hP hY4 hHY _ hw (vAct u (eV (pos k)) - eV (pos k))
    ⟨_, rfl⟩
  rw [vAct_vecElt, hu, vAct_vecElt] at h1
  exact hfix w h1

theorem coord_eq_zero_of_gammaTwo {x : Fin 3 → ZMod 3} {l : Fin 3} (hl : x l = 0)
    (hx : ∀ i, i ≠ l → x i ≠ 0) {H : Subgroup H6} (hP : Group.IsPerfect H)
    (hH : H ≤ Subgroup.centralizer {vecElt zH x}) {w : Fin 3 → ZMod 3} (hw : vecElt zH w ∈ H) :
    w l = 0 := by
  classical
  obtain ⟨hsub, hel, hfix⟩ := gammaTwo_check x l hl hx
  set u := vecElt zH x with hu
  set Y : Set (Fin 6 → ZMod 2) := {y | vAct u y = y} with hY
  set P : Finset (Fin 6 → ZMod 2) := Finset.univ.filter
    fun y => ∀ r : Fin 6, r ≠ pos l → r ≠ pos3 l → y r = 0 with hPdef
  have hP4 : P.card = 4 := card_planeSet l
  have hYP : Y ⊆ (P : Set (Fin 6 → ZMod 2)) := by
    intro y hy
    simp only [hPdef, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [hY, Set.mem_ofPred_eq, hu, vAct_vecElt] at hy
    exact hsub y hy
  have hY4 : Nat.card Y ≤ 4 := by
    rw [Nat.card_coe_set_eq, ← hP4, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hYP (Finset.finite_toSet P)
  have hHY : ∀ h ∈ H, ∀ y ∈ Y, vAct h y ∈ Y := by
    intro h hh y hy
    rw [hY, Set.mem_ofPred_eq] at hy ⊢
    rw [← vAct_comm (hH hh), hy]
  have heY : eV (pos l) ∈ Y := by
    rw [hY, Set.mem_ofPred_eq, hu, vAct_vecElt]
    exact hel
  have h1 := fixes_of_isPerfect vAct hP hY4 hHY _ hw _ heY
  rw [vAct_vecElt] at h1
  exact hfix w h1

@[expose] def sAct : H6 →* Perm (Set (Fin 6 → ZMod 2)) where
  toFun g :=
    { toFun := fun F => vAct g '' F
      invFun := fun F => vAct g⁻¹ '' F
      left_inv := fun F => by
        change vAct g⁻¹ '' (vAct g '' F) = F
        rw [← Set.image_comp, ← Perm.coe_mul, ← map_mul, inv_mul_cancel, map_one, Perm.coe_one,
          Set.image_id]
      right_inv := fun F => by
        change vAct g '' (vAct g⁻¹ '' F) = F
        rw [← Set.image_comp, ← Perm.coe_mul, ← map_mul, mul_inv_cancel, map_one, Perm.coe_one,
          Set.image_id] }
  map_one' := by
    refine Equiv.ext fun F => ?_
    change vAct 1 '' F = F
    rw [map_one, Perm.coe_one, Set.image_id]
  map_mul' g h := by
    refine Equiv.ext fun F => ?_
    change vAct (g * h) '' F = vAct g '' (vAct h '' F)
    rw [map_mul, Perm.coe_mul, Set.image_comp]

theorem sAct_apply (g : H6) (F : Set (Fin 6 → ZMod 2)) : sAct g F = vAct g '' F :=
  rfl

theorem ncard_triple_le_four {α : Type*} (a b c : α) : ({a, b, c} : Set α).ncard ≤ 4 := by
  have h1 := Set.ncard_insert_le a ({b, c} : Set α)
  have h2 := Set.ncard_insert_le b ({c} : Set α)
  rw [Set.ncard_singleton] at h2
  omega

theorem eq_bot_of_gammaThree_base (j : Fin 2) {H : Subgroup H6} (hP : Group.IsPerfect H)
    (hH : H ≤ Subgroup.centralizer {vecElt zH (baseG3 j)}) : H = ⊥ := by
  classical
  set x := baseG3 j with hxdef
  obtain ⟨he0, hpl, hpl0, h3⟩ := gammaThree_planes_check j
  have hu : ∀ y, vAct (vecElt zH x) y = wAct x y := vAct_vecElt x
  have hc : ∀ h ∈ H, ∀ z, vAct h (wAct x z) = wAct x (vAct h z) := fun h hh z => by
    rw [← hu, ← hu, vAct_comm (hH hh)]
  have hu3 : ∀ y, wAct x (wAct x (wAct x y)) = y := fun y => by
    have h3x : vecElt zH x ^ 3 = 1 := (isElemAbelian_baseA wreathFacts_zH).2 _
      (vecElt_mem_baseA wreathFacts_zH x)
    rw [← hu, ← hu, ← hu, ← Perm.mul_apply, ← Perm.mul_apply, ← map_mul, ← map_mul, ← pow_three',
      h3x, map_one, Perm.one_apply]
  have hfrm : ∀ h ∈ H, ∀ y y', frameP x y y' → frameP x (vAct h y) (vAct h y') := by
    intro h hh y y' hyy'
    obtain ⟨hn, hor⟩ := hyy'
    refine ⟨by rw [← hc h hh, bF_vAct]; exact hn, ?_⟩
    rcases hor with ⟨hb1, hb2⟩ | rfl | rfl | rfl
    · exact Or.inl ⟨by rw [bF_vAct]; exact hb1, by rw [← hc h hh, bF_vAct]; exact hb2⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl (hc h hh y)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hc h hh, hc h hh])))
  set frm : (Fin 6 → ZMod 2) → Set (Fin 6 → ZMod 2) := fun y => {y' | frameP x y y'} with hfrmdef
  have hfrmImg : ∀ h ∈ H, ∀ y, sAct h (frm y) = frm (vAct h y) := by
    intro h hh y
    rw [sAct_apply]
    ext y'
    constructor
    · rintro ⟨y'', hy'', rfl⟩
      exact hfrm h hh y y'' hy''
    · intro hy'
      refine ⟨vAct h⁻¹ y', ?_, ?_⟩
      · have h4 := hfrm h⁻¹ (inv_mem hh) _ _ hy'
        rwa [← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Perm.one_apply] at h4
      · rw [← Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Perm.one_apply]
  set Fr : Set (Set (Fin 6 → ZMod 2)) := frm '' {y | bF y (wAct x y) = 1} with hFrdef
  have hFr4 : Nat.card Fr ≤ 4 := by
    have hsub : Fr ⊆ Set.range fun i : Fin 4 => frm (repF i) := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨i, hi⟩ := gammaThree_frames_check j y hy
      exact ⟨i, Set.ext fun y' => (hi y').symm⟩
    calc Nat.card Fr ≤ Nat.card (Set.range fun i : Fin 4 => frm (repF i)) := by
          rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact Set.ncard_le_ncard hsub (Set.finite_range _)
      _ ≤ Nat.card (Fin 4) := Finite.card_range_le _
      _ = 4 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 4)
  have hFrH : ∀ h ∈ H, ∀ F ∈ Fr, sAct h F ∈ Fr := by
    rintro h hh _ ⟨y, hy, rfl⟩
    refine ⟨vAct h y, ?_, (hfrmImg h hh y).symm⟩
    rw [Set.mem_ofPred_eq] at hy ⊢
    rw [← hc h hh, bF_vAct]
    exact hy
  have hF0 : ∀ h ∈ H, ∀ y, frameP x (eV 0) y → frameP x (eV 0) (vAct h y) := by
    intro h hh y hy
    have h4 := fixes_of_isPerfect sAct hP hFr4 hFrH h hh (frm (eV 0)) ⟨eV 0, he0, rfl⟩
    have h5 : vAct h y ∈ sAct h (frm (eV 0)) := by
      rw [sAct_apply]
      exact ⟨y, hy, rfl⟩
    rw [h4] at h5
    exact h5
  set pl : (Fin 6 → ZMod 2) → Set (Fin 6 → ZMod 2) :=
    fun y => {y, wAct x y, wAct x (wAct x y)} with hpldef
  have hplImg : ∀ h ∈ H, ∀ y, sAct h (pl y) = pl (vAct h y) := by
    intro h hh y
    rw [sAct_apply, hpldef]
    simp only [Set.image_insert_eq, Set.image_singleton, hc h hh]
  have hplOrb : ∀ y y', y' ∈ pl y → pl y' = pl y := by
    intro y y' hy'
    rw [hpldef] at hy' ⊢
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
    rcases hy' with rfl | rfl | rfl
    · rfl
    · ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hu3]
      tauto
    · ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hu3]
      tauto
  set Pl : Set (Set (Fin 6 → ZMod 2)) := pl '' {y | frameP x (eV 0) y} with hPldef
  have hPl4 : Nat.card Pl ≤ 4 := by
    have hsub : Pl ⊆ Set.range fun k : Fin 3 => pl (eV (pos k)) := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hpl y hy
      refine ⟨k, (hplOrb _ y ?_).symm⟩
      rw [hpldef]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hk
    calc Nat.card Pl ≤ Nat.card (Set.range fun k : Fin 3 => pl (eV (pos k))) := by
          rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact Set.ncard_le_ncard hsub (Set.finite_range _)
      _ ≤ Nat.card (Fin 3) := Finite.card_range_le _
      _ ≤ 4 := by simp
  have hPlH : ∀ h ∈ H, ∀ F ∈ Pl, sAct h F ∈ Pl := by
    rintro h hh _ ⟨y, hy, rfl⟩
    exact ⟨vAct h y, hF0 h hh y hy, (hplImg h hh y).symm⟩
  have hvfix : ∀ k : Fin 3, ∀ h ∈ H, ∀ y ∈ pl (eV (pos k)), vAct h y = y := by
    intro k
    have hfixk : ∀ h ∈ H, sAct h (pl (eV (pos k))) = pl (eV (pos k)) := fun h hh =>
      fixes_of_isPerfect sAct hP hPl4 hPlH h hh _ ⟨_, hpl0 k, rfl⟩
    have hmaps : ∀ h ∈ H, ∀ y ∈ pl (eV (pos k)), vAct h y ∈ pl (eV (pos k)) := by
      intro h hh y hy
      rw [← hfixk h hh, sAct_apply]
      exact ⟨y, hy, rfl⟩
    have hcard : Nat.card (pl (eV (pos k))) ≤ 4 := by
      rw [Nat.card_coe_set_eq, hpldef]
      exact ncard_triple_le_four _ _ _
    exact fixes_of_isPerfect vAct hP hcard hmaps
  rw [eq_bot_iff]
  intro h hh
  rw [Subgroup.mem_bot]
  have hbasis : ∀ j : Fin 6, vAct h (eV j) = eV j := by
    intro j
    obtain ⟨k, rfl | rfl⟩ : ∃ k : Fin 3, j = pos k ∨ j = pos3 k := by
      refine ⟨⟨j % 3, by omega⟩, ?_⟩
      rcases Nat.lt_or_ge j 3 with hj | hj
      · left
        ext
        simp only [pos]
        omega
      · right
        ext
        simp only [pos3]
        omega
    · exact hvfix k h hh _ (by rw [hpldef]; exact Set.mem_insert _ _)
    · refine hvfix k h hh _ ?_
      rw [hpldef]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact h3 k
  apply mat6_injective
  ext i j
  have h4 := congrFun (hbasis j) i
  rw [vAct_apply, eV, Matrix.mulVec_single_one] at h4
  rw [map_one, Matrix.one_apply]
  simp only [Matrix.col_apply] at h4
  rw [h4, Pi.single_apply]

theorem eq_bot_of_gammaThree {x : Fin 3 → ZMod 3} (h0 : x 0 ≠ 0) (h1 : x 1 ≠ 0) (h2 : x 2 ≠ 0)
    {H : Subgroup H6} (hP : Group.IsPerfect H) (hH : H ≤ Subgroup.centralizer {vecElt zH x}) :
    H = ⊥ := by
  have hf := wreathFacts_zH
  have hrot : ∀ (r : ℕ) (v : Fin 3 → ZMod 3),
      vecElt zH (rotV^[r] v) = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ r * vecElt zH v * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ r)⁻¹ := by
    intro r
    induction r with
    | zero => intro v; simp
    | succ r ih =>
      intro v
      rw [Function.iterate_succ_apply', rotV, ← conj_vecElt hf, ih, pow_succ', mul_inv_rev]
      group
  have hsq : ∀ v : Fin 3 → ZMod 3, Subgroup.centralizer {vecElt zH (v + v)} ≤
      Subgroup.centralizer {vecElt zH v} := by
    intro v g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    have h3 : vecElt zH v ^ 3 = 1 := (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf v)
    have hv : vecElt zH v = vecElt zH (v + v) * vecElt zH (v + v) := by
      rw [vecElt_add hf, ← pow_two, ← pow_two, ← pow_mul,
        show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    rw [hv, ← mul_assoc, hg, mul_assoc, hg, mul_assoc]
  have hconj : ∀ (g : H6) (j : Fin 2) {H : Subgroup H6}, Group.IsPerfect H →
      H ≤ Subgroup.centralizer {g * vecElt zH (baseG3 j) * g⁻¹} → H = ⊥ := by
    intro g j H hP hH
    have hH' : H.map (MulAut.conj g⁻¹).toMonoidHom ≤
        Subgroup.centralizer {vecElt zH (baseG3 j)} := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hH hy
      rw [mem_centralizer_singleton_iff] at h1 ⊢
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * y * g * vecElt zH (baseG3 j)
          = g⁻¹ * (y * (g * vecElt zH (baseG3 j) * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * vecElt zH (baseG3 j) * g⁻¹) * y) * g := by rw [h1]
        _ = vecElt zH (baseG3 j) * (g⁻¹ * y * g) := by group
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp
      (eq_bot_of_gammaThree_base j (@Group.IsPerfect.map _ _ _ _ _ _ hP) hH')
  obtain ⟨j, r, hx | hx⟩ := gammaThree_cases x h0 h1 h2
  · rw [hx, hrot] at hH
    exact hconj _ j hP hH
  · rw [hx] at hH
    have h3 := hH.trans (hsq _)
    rw [hrot] at h3
    exact hconj _ j hP h3

theorem coords_cases : ∀ x : Fin 3 → ZMod 3, (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0) ∨
    (∃ k : Fin 3, x k ≠ 0 ∧ ∀ i, i ≠ k → x i = 0) ∨
    (∃ l : Fin 3, x l = 0 ∧ ∀ i, i ≠ l → x i ≠ 0) ∨ (x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ x 2 ≠ 0) := by
  decide

theorem card_filter_coord : ∀ l : Fin 3,
    (Finset.univ.filter fun w : Fin 3 → ZMod 3 => w l = 0).card = 9 := by
  decide

theorem card_filter_coord_two : ∀ k l : Fin 3, k ≠ l →
    (Finset.univ.filter fun w : Fin 3 → ZMod 3 => w k = 0 ∧ w l = 0).card = 3 := by
  decide

set_option synthInstance.maxSize 4096 in
theorem eq_or_eq_add_of_coord : ∀ x y : Fin 3 → ZMod 3, ∀ k : Fin 3, x k ≠ 0 →
    (∀ i, i ≠ k → x i = 0) → y k ≠ 0 → (∀ i, i ≠ k → y i = 0) → y = x ∨ y = x + x := by
  decide

theorem coord_eq_zero_of_perfect {S H : Subgroup H6} {x : Fin 3 → ZMod 3}
    (hSA : S ≤ baseA zH) (hS9 : Nat.card S = 9) (huS : vecElt zH x ∉ S) (hP : Group.IsPerfect H)
    (hSH : S ≤ H) (hH : H ≤ Subgroup.centralizer {vecElt zH x}) :
    ∃ k : Fin 3, x k ≠ 0 ∧ (∀ i, i ≠ k → x i = 0) ∧ ∀ w, vecElt zH w ∈ S → w k = 0 := by
  classical
  have hf := wreathFacts_zH
  have hSvec : ∀ s ∈ S, ∃ w, vecElt zH w = s := fun s hs => (mem_baseA_iff hf).mp (hSA hs)
  rcases coords_cases x with ⟨h0, h1, h2⟩ | ⟨k, hk, hx⟩ | ⟨l, hl, hx⟩ | ⟨h0, h1, h2⟩
  · exfalso
    apply huS
    have hx0 : x = 0 := by
      funext i
      fin_cases i <;> assumption
    have h1 : vecElt zH 0 = 1 := by simp [vecElt]
    rw [hx0, h1]
    exact S.one_mem
  · exact ⟨k, hk, hx, fun w hw => coord_eq_zero_of_gammaOne hk hx hP hH (hSH hw)⟩
  · exfalso
    set T : Finset H6 := (Finset.univ.filter fun w : Fin 3 → ZMod 3 => w l = 0).image
      (vecElt zH) with hTdef
    have hT9 : T.card = 9 := by
      rw [hTdef, Finset.card_image_of_injective _ (fun a b hab => vecElt_injective hf hab)]
      exact card_filter_coord l
    have hST : (S : Set H6) ⊆ T := by
      intro s hs
      obtain ⟨w, rfl⟩ := hSvec s hs
      have hwl := coord_eq_zero_of_gammaTwo hl hx hP hH (hSH hs)
      rw [hTdef, Finset.coe_image]
      exact ⟨w, by simp [hwl], rfl⟩
    have hSeq : (S : Set H6) = T := by
      refine Set.eq_of_subset_of_ncard_le hST ?_ (Finset.finite_toSet T)
      have hSn : (S : Set H6).ncard = 9 := by
        rw [← Nat.card_coe_set_eq]
        exact hS9
      rw [Set.ncard_coe_finset, hT9, hSn]
    apply huS
    have h1 : vecElt zH x ∈ (T : Set H6) := by
      rw [hTdef, Finset.coe_image]
      exact ⟨x, by simp [hl], rfl⟩
    rw [← hSeq] at h1
    exact h1
  · exfalso
    have hbot := eq_bot_of_gammaThree h0 h1 h2 hP hH
    have h1 := Subgroup.card_le_of_le (hSH.trans hbot.le)
    rw [hS9, Subgroup.card_bot] at h1
    omega

theorem mem_zpowers_of_baseA_zH {S H₁ H₂ : Subgroup H6} {u v : H6} (hSA : S ≤ baseA zH)
    (hS9 : Nat.card S = 9) (huA : u ∈ baseA zH) (hvA : v ∈ baseA zH) (huS : u ∉ S) (hvS : v ∉ S)
    (hP₁ : Group.IsPerfect H₁) (hP₂ : Group.IsPerfect H₂) (hSH₁ : S ≤ H₁) (hSH₂ : S ≤ H₂)
    (hH₁ : H₁ ≤ Subgroup.centralizer {u}) (hH₂ : H₂ ≤ Subgroup.centralizer {v}) :
    v ∈ Subgroup.zpowers u := by
  classical
  have hf := wreathFacts_zH
  obtain ⟨x, rfl⟩ := (mem_baseA_iff hf).mp huA
  obtain ⟨y, rfl⟩ := (mem_baseA_iff hf).mp hvA
  obtain ⟨k, hk, hxk, hSk⟩ := coord_eq_zero_of_perfect hSA hS9 huS hP₁ hSH₁ hH₁
  obtain ⟨l, hl, hyl, hSl⟩ := coord_eq_zero_of_perfect hSA hS9 hvS hP₂ hSH₂ hH₂
  have hkl : k = l := by
    by_contra hne
    set T : Finset H6 := (Finset.univ.filter fun w : Fin 3 → ZMod 3 => w k = 0 ∧ w l = 0).image
      (vecElt zH) with hTdef
    have hT3 : T.card = 3 := by
      rw [hTdef, Finset.card_image_of_injective _ (fun a b hab => vecElt_injective hf hab)]
      exact card_filter_coord_two k l hne
    have hST : (S : Set H6) ⊆ T := by
      intro s hs
      obtain ⟨w, rfl⟩ := (mem_baseA_iff hf).mp (hSA hs)
      rw [hTdef, Finset.coe_image]
      exact ⟨w, by simp [hSk w hs, hSl w hs], rfl⟩
    have h1 := Set.ncard_le_ncard hST (Finset.finite_toSet T)
    have hSn : (S : Set H6).ncard = 9 := by
      rw [← Nat.card_coe_set_eq]
      exact hS9
    rw [Set.ncard_coe_finset, hT3, hSn] at h1
    omega
  subst hkl
  have hyx : y = x ∨ y = x + x := eq_or_eq_add_of_coord x y k hk hxk hl hyl
  rcases hyx with rfl | rfl
  · exact Subgroup.mem_zpowers _
  · rw [vecElt_add hf]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3
