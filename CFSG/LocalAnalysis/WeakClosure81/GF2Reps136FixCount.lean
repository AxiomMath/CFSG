module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_stableUnder_sup {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊔ B) := by
  intro x hx u hu
  rw [Subgroup.sup_eq_closure] at hu ⊢
  refine Subgroup.closure_induction (p := fun u _ => x u ∈ Subgroup.closure (A ∪ B : Set W))
    ?_ ?_ ?_ ?_ hu
  · rintro u (huA | huB)
    · exact Subgroup.subset_closure (Or.inl (hA x hx u huA))
    · exact Subgroup.subset_closure (Or.inr (hB x hx u huB))
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb; rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha; rw [map_inv]; exact Subgroup.inv_mem _ ha

private theorem w1369_stableUnder_inf {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊓ B) :=
  fun x hx u hu => Subgroup.mem_inf.mpr ⟨hA x hx u hu.1, hB x hx u hu.2⟩

private theorem w1369_stableUnder_finsetSup {X : Subgroup (MulAut W)}
    {T : Finset (Subgroup W)} (h : ∀ M ∈ T, StableUnder X M) : StableUnder X (T.sup id) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty]
      intro x _ u hu
      rw [Subgroup.mem_bot] at hu
      subst hu
      rw [map_one]
      exact Subgroup.one_mem _
  | insert M T hMT ih =>
      rw [Finset.sup_insert]
      exact w1369_stableUnder_sup (h M (Finset.mem_insert_self M T))
        (ih fun P hP => h P (Finset.mem_insert_of_mem hP))

private lemma w1369_indep_insert {C X A B : Subgroup W}
    (hAB : A ⊓ (C ⊔ B) ≤ C) (hX : X ⊓ (C ⊔ A ⊔ B) ≤ C) :
    A ⊓ (C ⊔ (X ⊔ B)) ≤ C := by
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzA, hz⟩ := hz
  rw [show C ⊔ (X ⊔ B) = X ⊔ (C ⊔ B) by rw [← sup_assoc, sup_comm C X, sup_assoc]] at hz
  obtain ⟨x, hxX, t, htCB, hxt⟩ := Subgroup.mem_sup.mp hz
  have hx : x ∈ A ⊔ (C ⊔ B) := by
    have hx' : x = z * t⁻¹ := by rw [← hxt]; group
    rw [hx']
    exact (A ⊔ (C ⊔ B)).mul_mem (Subgroup.mem_sup_left hzA)
      (Subgroup.mem_sup_right ((C ⊔ B).inv_mem htCB))
  have hxCAB : x ∈ C ⊔ A ⊔ B := by
    rw [show C ⊔ A ⊔ B = A ⊔ (C ⊔ B) by rw [sup_comm C A, sup_assoc]]
    exact hx
  have hxC : x ∈ C := hX (Subgroup.mem_inf.mpr ⟨hxX, hxCAB⟩)
  have hzCB : z ∈ C ⊔ B := by
    rw [hxt.symm]
    exact (C ⊔ B).mul_mem (Subgroup.mem_sup_left hxC) htCB
  exact hAB (Subgroup.mem_inf.mpr ⟨hzA, hzCB⟩)

private lemma w1369_indep_insert_finset {C : Subgroup W} [DecidableEq (Subgroup W)]
    {T : Finset (Subgroup W)} {M : Subgroup W} (hM : M ∉ T)
    (hT : ∀ P ∈ T, P ⊓ (C ⊔ (T.erase P).sup id) ≤ C)
    (hMs : M ⊓ (C ⊔ T.sup id) ≤ C) :
    ∀ P ∈ insert M T, P ⊓ (C ⊔ ((insert M T).erase P).sup id) ≤ C := by
  classical
  intro P hP
  rw [Finset.mem_insert] at hP
  rcases hP with rfl | hPT
  · rw [Finset.erase_insert hM]
    exact hMs
  · have hPM : P ≠ M := fun h => hM (h ▸ hPT)
    rw [Finset.erase_insert_of_ne hPM.symm, Finset.sup_insert]
    have hTsup : T.sup id = P ⊔ (T.erase P).sup id := by
      conv_lhs => rw [← Finset.insert_erase hPT]
      rw [Finset.sup_insert]
      rfl
    have hX : M ⊓ (C ⊔ P ⊔ (T.erase P).sup id) ≤ C := by
      have hEq : C ⊔ P ⊔ (T.erase P).sup id = C ⊔ T.sup id := by
        rw [hTsup, sup_assoc]
      rw [hEq]
      exact hMs
    exact w1369_indep_insert (hT P hPT) hX

private lemma w1369_iSup_equivFin_erase {α : Type*} [CompleteLattice α] [DecidableEq α]
    {T : Finset α} (i : Fin T.card) :
    (⨆ (j : Fin T.card) (_ : j ≠ i), (T.equivFin.symm j : {x // x ∈ T}).val) =
      (T.erase (T.equivFin.symm i).val).sup id := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j => iSup_le fun hj => ?_
    have hJne : (T.equivFin.symm j).val ≠ (T.equivFin.symm i).val := fun h =>
      hj (T.equivFin.symm.injective (Subtype.ext h))
    exact Finset.le_sup (f := id)
      (Finset.mem_erase.mpr ⟨hJne, (T.equivFin.symm j).2⟩)
  · refine Finset.sup_le ?_
    intro M hM
    have hMT : M ∈ T := Finset.mem_of_mem_erase hM
    have hMne : M ≠ (T.equivFin.symm i).val := (Finset.mem_erase.mp hM).1
    let j : Fin T.card := T.equivFin ⟨M, hMT⟩
    have hjsymm : (T.equivFin.symm j : {x // x ∈ T}).val = M := by
      show (T.equivFin.symm (T.equivFin ⟨M, hMT⟩)).val = M
      rw [Equiv.symm_apply_apply]
    have hjne : j ≠ i := fun hji => hMne (by rw [← hjsymm, hji])
    have hle : (T.equivFin.symm j : {x // x ∈ T}).val ≤
        ⨆ (j : Fin T.card) (_ : j ≠ i), (T.equivFin.symm j : {x // x ∈ T}).val :=
      le_iSup_of_le j (le_iSup_of_le hjne le_rfl)
    simpa only [id_eq, ← hjsymm] using hle

theorem w1369_exists_indep_family {L : Subgroup (MulAut W)} {C : Subgroup W}
    (𝒮 : Set (Subgroup W)) (h𝒮 : 𝒮.Finite) (hC : ∀ M ∈ 𝒮, C ≤ M ∧ IsIrrOn L M C) :
    ∃ (r : ℕ) (J : Fin r → Subgroup W), (∀ i, J i ∈ 𝒮) ∧
      (∀ i, J i ⊓ (C ⊔ ⨆ (j : Fin r) (_ : j ≠ i), J j) ≤ C) ∧
      (C ⊔ ⨆ i, J i) = C ⊔ ⨆ M ∈ 𝒮, M := by
  classical
  let Indep : Finset (Subgroup W) → Prop :=
    fun T => ∀ M ∈ T, M ⊓ (C ⊔ (T.erase M).sup id) ≤ C
  have hsfin : ({T : Finset (Subgroup W) | T ⊆ h𝒮.toFinset ∧ Indep T}).Finite :=
    (h𝒮.toFinset.powerset).finite_toSet.subset fun T hT => Finset.mem_powerset.mpr hT.1
  obtain ⟨T, -, hTmax⟩ :=
    Set.Finite.exists_le_maximal hsfin (a := (∅ : Finset (Subgroup W)))
      ⟨Finset.empty_subset _, by intro M hM; exact absurd hM (Finset.notMem_empty M)⟩
  have hTsub : T ⊆ h𝒮.toFinset := hTmax.1.1
  have hTindep : Indep T := hTmax.1.2
  have hmemC : ∀ M ∈ T, C ≤ M ∧ IsIrrOn L M C := fun M hM =>
    hC M ((h𝒮.mem_toFinset).mp (hTsub hM))
  have hle_all : ∀ M ∈ 𝒮, M ≤ C ⊔ T.sup id := by
    intro M hM
    by_cases hMT : M ∈ T
    · exact (Finset.le_sup (f := id) hMT).trans le_sup_right
    · set S : Subgroup W := C ⊔ T.sup id with hS
      have hStableM : StableUnder L M := (hC M hM).2.2.1
      have hStableC : StableUnder L C := (hC M hM).2.2.2.1
      have hStableT : StableUnder L (T.sup id) := w1369_stableUnder_finsetSup fun P hP =>
        (hC P ((h𝒮.mem_toFinset).mp (hTsub hP))).2.2.1
      have hStableS : StableUnder L S := by
        rw [hS]; exact w1369_stableUnder_sup hStableC hStableT
      have hStableN : StableUnder L (M ⊓ S) := w1369_stableUnder_inf hStableM hStableS
      have hStableNC : StableUnder L ((M ⊓ S) ⊔ C) :=
        w1369_stableUnder_sup hStableN hStableC
      rcases (hC M hM).2.2.2.2 ((M ⊓ S) ⊔ C) hStableNC le_sup_right
        (sup_le inf_le_left (hC M hM).1) with hcase | hcase
      · have hMS : M ⊓ S ≤ C := by rw [← hcase]; exact le_sup_left
        exfalso
        have hIns : insert M T ∈ {T : Finset (Subgroup W) | T ⊆ h𝒮.toFinset ∧ Indep T} := by
          refine ⟨Finset.insert_subset ((h𝒮.mem_toFinset).mpr hM) hTsub, ?_⟩
          rw [show S = C ⊔ T.sup id from hS] at hMS
          exact w1369_indep_insert_finset hMT hTindep hMS
        have hle' : insert M T ≤ T := hTmax.2 hIns (Finset.subset_insert M T)
        exact hMT (hle' (Finset.mem_insert_self M T))
      · rw [← hcase]
        exact sup_le inf_le_right le_sup_left
  have hspan_le : C ⊔ T.sup id ≤ C ⊔ ⨆ M ∈ 𝒮, M := by
    refine sup_le le_sup_left (Finset.sup_le fun M hM => ?_)
    exact le_sup_of_le_right
      (le_iSup₂_of_le M ((h𝒮.mem_toFinset).mp (hTsub hM)) le_rfl)
  have hspan_ge : C ⊔ ⨆ M ∈ 𝒮, M ≤ C ⊔ T.sup id :=
    sup_le le_sup_left (iSup₂_le fun M hM => hle_all M hM)
  have hspan : C ⊔ T.sup id = C ⊔ ⨆ M ∈ 𝒮, M := le_antisymm hspan_le hspan_ge
  refine ⟨T.card, fun i => (T.equivFin.symm i : {x // x ∈ T}).val, ?_, ?_, ?_⟩
  · intro i
    exact (h𝒮.mem_toFinset).mp (hTsub (T.equivFin.symm i).2)
  · intro i
    rw [w1369_iSup_equivFin_erase i]
    exact hTindep (T.equivFin.symm i).val (T.equivFin.symm i).2
  · have hiSup : (⨆ i : Fin T.card, (T.equivFin.symm i : {x // x ∈ T}).val) = T.sup id := by
      refine le_antisymm ?_ ?_
      · refine iSup_le fun i => ?_
        exact Finset.le_sup (f := id) (T.equivFin.symm i).2
      · refine Finset.sup_le fun M hM => ?_
        let i : Fin T.card := T.equivFin ⟨M, hM⟩
        have hi : (T.equivFin.symm i : {x // x ∈ T}).val = M := by
          show (T.equivFin.symm (T.equivFin ⟨M, hM⟩)).val = M
          rw [Equiv.symm_apply_apply]
        rw [← hi]
        exact le_iSup (fun i : Fin T.card => (T.equivFin.symm i : {x // x ∈ T}).val) i
    rw [hiSup, hspan]

private lemma w1369_mQuot_eq_rk_map_mk (C V : Subgroup W) :
    E3.mQuot V C = rk ↥(V.map (QuotientGroup.mk' C)) := by
  have h := Subgroup.relIndex_ker (QuotientGroup.mk' C : W →* W ⧸ C) (K := V)
  rw [QuotientGroup.ker_mk'] at h
  rw [E3.mQuot, rk, h]

private lemma w1369_map_mk_inf_le_map_inf {C X Y : Subgroup W} (hC : C ≤ X) :
    (X.map (QuotientGroup.mk' C)) ⊓ (Y.map (QuotientGroup.mk' C)) ≤
      (X ⊓ Y).map (QuotientGroup.mk' C) := by
  intro z hz
  obtain ⟨hzX, hzY⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hzX
  obtain ⟨y, hyY, hyx⟩ := Subgroup.mem_map.mp hzY
  rw [← hyx]
  refine Subgroup.mem_map.mpr ⟨y, ⟨?_, hyY⟩, rfl⟩
  have hker : x⁻¹ * y ∈ (QuotientGroup.mk' C : W →* W ⧸ C).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx]
    simp
  rw [QuotientGroup.ker_mk'] at hker
  rw [show y = x * (x⁻¹ * y) by group]
  exact X.mul_mem hxX (hC hker)

private lemma w1369_iSupIndep_map_mk {C : Subgroup W} {ι : Type*} (B : ι → Subgroup W)
    (hCB : ∀ i, C ≤ B i) (hind : ∀ i, B i ⊓ (⨆ (j) (_ : j ≠ i), B j) ≤ C) :
    iSupIndep fun i => (B i).map (QuotientGroup.mk' C) := by
  classical
  intro i
  rw [disjoint_iff, ← le_bot_iff]
  have hmap_iSup : (⨆ (j) (_ : j ≠ i), (B j).map (QuotientGroup.mk' C)) =
      (⨆ (j) (_ : j ≠ i), B j).map (QuotientGroup.mk' C) := by
    rw [Subgroup.map_iSup]
    simp_rw [Subgroup.map_iSup]
  calc (B i).map (QuotientGroup.mk' C) ⊓
        (⨆ (j) (_ : j ≠ i), (B j).map (QuotientGroup.mk' C))
      = (B i).map (QuotientGroup.mk' C) ⊓
          (⨆ (j) (_ : j ≠ i), B j).map (QuotientGroup.mk' C) := by rw [hmap_iSup]
    _ ≤ (B i ⊓ (⨆ (j) (_ : j ≠ i), B j)).map (QuotientGroup.mk' C) :=
          w1369_map_mk_inf_le_map_inf (hCB i)
    _ ≤ C.map (QuotientGroup.mk' C) := Subgroup.map_mono (hind i)
    _ = ⊥ := by
          rw [eq_bot_iff]
          rintro x ⟨y, hy, rfl⟩
          rw [Subgroup.mem_bot]
          exact MonoidHom.mem_ker.mp (by rwa [QuotientGroup.ker_mk'])

private lemma w1369_mQuot_iSup_eq_sum_of_indep (hw2 : ∀ w : W, w ^ 2 = 1)
    {C : Subgroup W} {ι : Type*} [Fintype ι] (B : ι → Subgroup W)
    (hCB : ∀ i, C ≤ B i) (hind : ∀ i, B i ⊓ (⨆ (j) (_ : j ≠ i), B j) ≤ C) :
    E3.mQuot (⨆ i, B i) C = ∑ i, E3.mQuot (B i) C := by
  classical
  let p : W →* W ⧸ C := QuotientGroup.mk' C
  let F : ι → Subgroup (W ⧸ C) := fun i => (B i).map p
  have hind' : iSupIndep F := w1369_iSupIndep_map_mk B hCB hind
  have hq2 : ∀ x : W ⧸ C, x ^ 2 = 1 := by
    intro x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    change ((QuotientGroup.mk' C : W →* W ⧸ C) w) ^ 2 = 1
    rw [← map_pow (QuotientGroup.mk' C) w 2, hw2 w, map_one]
  have h1 : E3.mQuot (⨆ i, B i) C = rk ↥((⨆ i, B i).map p) :=
    w1369_mQuot_eq_rk_map_mk C (⨆ i, B i)
  rw [h1, Subgroup.map_iSup]
  change rk ↥(⨆ i, F i) = ∑ i, E3.mQuot (B i) C
  refine (w16g_rk_iSup_eq_sum (W := W ⧸ C) hq2 F hind').trans ?_
  exact Finset.sum_congr rfl fun i _ => (w1369_mQuot_eq_rk_map_mk C (B i)).symm

theorem w1369_tcost_sum_le (hw2 : ∀ w : W, w ^ 2 = 1) {t : MulAut W} {L : Subgroup (MulAut W)}
    {r : ℕ} {J : Fin r → Subgroup W} (hCJ : ∀ i, Cd L ≤ J i) (hJW : ∀ i, J i ≤ Wd L)
    (hst : ∀ i, StableUnder (Subgroup.zpowers t) (J i))
    (hind : ∀ i, J i ⊓ (Cd L ⊔ ⨆ (j : Fin r) (_ : j ≠ i), J j) ≤ Cd L)
    (hcost : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) :
    (∑ i, tcost t L (J i)) ≤ 3 := by
  classical
  let K : Fin r → Subgroup W := fun i => commSub (J i) (Subgroup.zpowers t)
  let B : Fin r → Subgroup W := fun i => K i ⊔ Cd L
  let A : Subgroup W := commSub ⊤ (Subgroup.zpowers t)
  have hKle : ∀ i, K i ≤ J i := fun i => commSub_le_of_invariant (hst i)
  have hCB : ∀ i, Cd L ≤ B i := fun _ => le_sup_right
  have hBind : ∀ i, B i ⊓ (⨆ (j) (_ : j ≠ i), B j) ≤ Cd L := by
    intro i
    have hBle : B i ≤ J i := sup_le (hKle i) (hCJ i)
    have hBsup : (⨆ (j) (_ : j ≠ i), B j) ≤ Cd L ⊔ ⨆ (j) (_ : j ≠ i), J j := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      exact (sup_le (hKle j) (hCJ j)).trans
        (le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le hj le_rfl)))
    calc B i ⊓ (⨆ (j) (_ : j ≠ i), B j)
        ≤ J i ⊓ (Cd L ⊔ ⨆ (j) (_ : j ≠ i), J j) := inf_le_inf hBle hBsup
      _ ≤ Cd L := hind i
  have hadd := w1369_mQuot_iSup_eq_sum_of_indep hw2 B hCB hBind
  have hBsupA : (⨆ i, B i) ≤ A ⊔ Cd L := by
    refine iSup_le fun i => ?_
    have hKi : K i ≤ A := commSub_mono (le_top : J i ≤ ⊤) le_rfl
    exact sup_le (hKi.trans le_sup_left) le_sup_right
  have hmono : E3.mQuot (⨆ i, B i) (Cd L) ≤ E3.mQuot (A ⊔ Cd L) (Cd L) := by
    rw [w1369_mQuot_eq_rk_map_mk (Cd L) (⨆ i, B i),
      w1369_mQuot_eq_rk_map_mk (Cd L) (A ⊔ Cd L)]
    exact rk_mono (Subgroup.map_mono hBsupA)
  have hCmap : (Cd L).map (QuotientGroup.mk' (Cd L)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_bot]
    exact MonoidHom.mem_ker.mp (by rwa [QuotientGroup.ker_mk'])
  have hfin : E3.mQuot (A ⊔ Cd L) (Cd L) ≤ 3 := by
    calc E3.mQuot (A ⊔ Cd L) (Cd L)
        = rk ↥((A ⊔ Cd L).map (QuotientGroup.mk' (Cd L))) :=
          w1369_mQuot_eq_rk_map_mk (Cd L) (A ⊔ Cd L)
      _ = rk ↥(A.map (QuotientGroup.mk' (Cd L))) := by
          rw [Subgroup.map_sup, hCmap, sup_bot_eq]
      _ ≤ rk ↥A :=
          padicValNat_two_le_of_dvd (card_subgroup_pos A).ne'
            (Subgroup.card_map_dvd (H := A) (QuotientGroup.mk' (Cd L)))
      _ ≤ 3 := hcost
  calc ∑ i, tcost t L (J i)
      = ∑ i, E3.mQuot (B i) (Cd L) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rfl
    _ = E3.mQuot (⨆ i, B i) (Cd L) := hadd.symm
    _ ≤ E3.mQuot (A ⊔ Cd L) (Cd L) := hmono
    _ ≤ 3 := hfin

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
