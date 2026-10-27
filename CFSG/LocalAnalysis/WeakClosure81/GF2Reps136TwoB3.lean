module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136S
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoB1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoA
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_le_stabSub_of_stableUnder {A : Subgroup (MulAut W)} {U : Subgroup W}
    (hA : StableUnder A U) : A ≤ stabSub U := by
  intro a ha
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by
      have h1 := hA a⁻¹ (A.inv_mem ha) (a u) hu
      simpa using h1,
    hA a ha u⟩

private theorem w1369_stableUnder_sup_of_stable {A B : Subgroup (MulAut W)} {U : Subgroup W}
    (hA : StableUnder A U) (hB : StableUnder B U) : StableUnder (A ⊔ B) U := by
  have hle : A ⊔ B ≤ stabSub U :=
    sup_le (w1369_le_stabSub_of_stableUnder hA) (w1369_le_stabSub_of_stableUnder hB)
  intro y hy u hu
  exact (mem_stabSub.mp (hle hy) u).2 hu

private theorem w1369_centralizer_sup_eq (A B : Subgroup (MulAut W)) :
    Subgroup.centralizer ((A ⊔ B : Subgroup (MulAut W)) : Set (MulAut W)) =
      Subgroup.centralizer (A : Set (MulAut W)) ⊓
        Subgroup.centralizer (B : Set (MulAut W)) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hg
    exact ⟨fun a ha => hg a (Set.mem_union_left _ ha),
      fun b hb => hg b (Set.mem_union_right _ hb)⟩
  · rintro ⟨hA', hB'⟩ c (hc | hc)
    · exact hA' c hc
    · exact hB' c hc

private theorem w1369_commSub_sup_right (X Y : Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (X ⊔ Y) = commSub ⊤ X ⊔ commSub ⊤ Y := by
  refine le_antisymm ?_ (sup_le (commSub_mono le_rfl le_sup_left)
    (commSub_mono le_rfl le_sup_right))
  let S : Subgroup W := commSub (⊤ : Subgroup W) X ⊔ commSub (⊤ : Subgroup W) Y
  let T : Subgroup (MulAut W) :=
    { carrier := {g | ∀ w, g w * w⁻¹ ∈ S}
      one_mem' := fun w => by
        show (1 : MulAut W) w * w⁻¹ ∈ S
        rw [MulAut.one_apply, mul_inv_cancel]
        exact S.one_mem
      mul_mem' := fun {a b} ha hb w => by
        have h1 := S.mul_mem (ha (b w)) (hb w)
        have h2 : (a * b) w * w⁻¹ = a (b w) * (b w)⁻¹ * (b w * w⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [h2]
        exact h1
      inv_mem' := fun {a} ha w => by
        have h1 := S.inv_mem (ha (a⁻¹ w))
        have h2 : a⁻¹ w * w⁻¹ = (a (a⁻¹ w) * (a⁻¹ w)⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]
          group
        rw [h2]
        exact h1 }
  have hT : X ⊔ Y ≤ T := sup_le
    (fun g hg w => Subgroup.mem_sup_left
      (Subgroup.subset_closure ⟨g, hg, w, Subgroup.mem_top w, rfl⟩))
    (fun g hg w => Subgroup.mem_sup_right
      (Subgroup.subset_closure ⟨g, hg, w, Subgroup.mem_top w, rfl⟩))
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨g, hg, w, -, rfl⟩
  exact hT hg w

private theorem w1369_commutator_self_of_isQuasisimple {G : Type*} [Group G]
    {L : Subgroup G} (h : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h.1] at h1
  rw [← h1, Subgroup.map_top, Subgroup.range_subtype]

private theorem w1369_commSub_commSub_eq_of_perfect {K : Subgroup (MulAut W)}
    (hKperf : ⁅K, K⁆ = K) :
    commSub (commSub ⊤ K) K = commSub ⊤ K := by
  have hKstab : StableUnder K (commSub ⊤ K) :=
    stableUnder_commSub (fun k hk x hx => K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk))
      (fun _ _ _ _ => Subgroup.mem_top _)
  exact le_antisymm (commSub_le_of_invariant hKstab)
    (s13_perfect_chain K hKperf (commSub (commSub ⊤ K) K) (commSub ⊤ K) ⊤ le_rfl le_rfl)

private theorem w1369_commSub_Wd_eq_bot_of_comm {L X K : Subgroup (MulAut W)}
    (hS : Strong3 L X) (hC : Cd L = ⊥) (hXL : ⁅X, L⁆ = ⊥)
    (hKstab : StableUnder K (Wd L)) (hKcomm : ⁅K, L ⊔ X⁆ = ⊥) :
    commSub (Wd L) K = ⊥ := by
  have hLstab : StableUnder L (Wd L) :=
    stableUnder_commSub (fun l hl x hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl))
      (fun _ _ _ _ => Subgroup.mem_top _)
  have hXstab : StableUnder X (Wd L) := by
    refine stableUnder_commSub (fun x hx l hl => ?_) (fun _ _ _ _ => Subgroup.mem_top _)
    have h1 : l * x = x * l := by
      have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXL
      exact Subgroup.mem_centralizer_iff.mp (h2 hx) l hl
    rw [← h1, mul_inv_cancel_right]
    exact hl
  have hLpstab : StableUnder (L ⊔ X) (Wd L) :=
    w1369_stableUnder_sup_of_stable hLstab hXstab
  have hKpair : StabPair K (Wd L) ⊥ := fun k hk =>
    ⟨hKstab k hk, fun z hz => by
      rw [Subgroup.mem_bot.mp hz, map_one]
      exact Subgroup.mem_bot.mpr rfl⟩
  have hLpPair : StabPair (L ⊔ X) (Wd L) ⊥ := fun a ha =>
    ⟨hLpstab a ha, fun z hz => by
      rw [Subgroup.mem_bot.mp hz, map_one]
      exact Subgroup.mem_bot.mpr rfl⟩
  have hsec : secSub (Wd L) ⊥ K ≤ Subgroup.centralizer (secSub (Wd L) ⊥ (L ⊔ X)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [secSub_commutator hKpair hLpPair, hKcomm, w1369_secSub_bot]
  have hcent := hS.1.2.2.2.1
  rw [hC] at hcent
  have hsec_bot : secSub (Wd L) ⊥ K = ⊥ := le_bot_iff.mp (hsec.trans (le_of_eq hcent))
  rw [commSub_eq_bot_iff]
  intro u hu
  rw [mem_fixV]
  intro k hk
  have hmem := (w1369_secSub_eq_bot_iff bot_le hKpair).mp hsec_bot k hk u hu
  simpa only [Subgroup.mem_bot, mul_inv_eq_one] using hmem

private theorem w1369_case_b_contra {L X K : Subgroup (MulAut W)} {Y : Subgroup (MulAut W)}
    (hS : Strong3 L X) (hC : Cd L = ⊥) (hXL : ⁅X, L⁆ = ⊥)
    (hKcomp : IsComponentOf K Y) (hKneL : K ≠ L) (hKneX : K ≠ X)
    (hKcomm : ⁅K, L ⊔ X⁆ = ⊥) (hKstab : StableUnder K (Wd L))
    (hK_Wd : commSub ⊤ K = Wd L) (hWd_ne_bot : Wd L ≠ ⊥) :
    False := by
  have hKperf : ⁅K, K⁆ = K := w1369_commutator_self_of_isQuasisimple hKcomp.2.2
  have htriv : commSub (Wd L) K = ⊥ :=
    w1369_commSub_Wd_eq_bot_of_comm hS hC hXL hKstab hKcomm
  have hperf : commSub (commSub ⊤ K) K = commSub ⊤ K :=
    w1369_commSub_commSub_eq_of_perfect hKperf
  have hWd_eq : commSub (Wd L) K = Wd L := by
    rw [← hK_Wd, hperf]
  exact hWd_ne_bot (hWd_eq.symm.trans htriv)

@[expose] def SwapT (Y L : Subgroup (MulAut W)) (g : MulAut W) : Prop :=
  ∀ h ∈ Y, h ∉ Subgroup.normalizer ((L ⊔ Lc L g : Subgroup (MulAut W)) : Set (MulAut W)) →
    ⁅L ⊔ Lc L g, (L ⊔ Lc L g).map (MulAut.conj h).toMonoidHom⁆ = ⊥ ∧
      commSub (commSub ⊤ (L ⊔ Lc L g)) ((L ⊔ Lc L g).map (MulAut.conj h).toMonoidHom) = ⊥

theorem swap_T (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {g : MulAut W} (S : Swap136 Y t L g)
    (hW : Wd (Lc L g) = Wd L) (hC : Cd L = ⊥) (hS : Strong3 L (Lc L g)) : SwapT Y L g := by
  intro h hhY hhN
  let X : Subgroup (MulAut W) := Lc L g
  let Lp : Subgroup (MulAut W) := L ⊔ X
  let A : Subgroup (MulAut W) := Lc L h
  let B : Subgroup (MulAut W) := Lc X h
  have hXcomp : IsComponentOf X Y := (swap_comp S).1
  have hAcomp : IsComponentOf A Y :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj S.ctx.comp hhY
  have hBcomp : IsComponentOf B Y :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hXcomp hhY
  have hmap : Lp.map (MulAut.conj h).toMonoidHom = A ⊔ B := by
    simp only [Lp, A, B, X, Lc, Subgroup.map_sup]
  have hAneB : A ≠ B := by
    intro hAB
    have h1 : L.map (MulAut.conj h).toMonoidHom = X.map (MulAut.conj h).toMonoidHom := hAB
    have h2 := congrArg (Subgroup.map (MulAut.conj h⁻¹).toMonoidHom) h1
    simp only [Subgroup.map_map] at h2
    have hcomp : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        MonoidHom.id (MulAut W) := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id, Subgroup.map_id] at h2
    exact (swap_comp S).2.1 h2.symm
  have hWd_ne_bot : Wd L ≠ ⊥ := by
    intro hbot
    refine S.nontriv ?_
    rw [hbot]
    exact commSub_eq_bot_iff.mpr bot_le
  have hXL : ⁅X, L⁆ = ⊥ := (swap_comp S).2.2.1
  have hXeq : commSub ⊤ X = Wd L := hW
  have hcaseB : ∀ K : Subgroup (MulAut W), IsComponentOf K Y → K ≠ L → K ≠ X →
      ⁅K, L ⊔ X⁆ = ⊥ → StableUnder K (Wd L) → commSub ⊤ K = Wd L → False := by
    intro K hKcomp hKneL hKneX hKcomm hKstab hK_Wd
    exact w1369_case_b_contra hS hC hXL hKcomp hKneL hKneX hKcomm hKstab hK_Wd hWd_ne_bot
  have hA_notin : ¬ (A = L ∨ A = X) := by
    intro hAin
    by_cases hBin : B = L ∨ B = X
    · exfalso
      have hsup : A ⊔ B = Lp := by
        rcases hAin with hAL | hAX <;> rcases hBin with hBL | hBX
        · exact absurd (hAL.trans hBL.symm) hAneB
        · rw [hAL, hBX]
        · rw [hAX, hBL, sup_comm]
        · exact absurd (hAX.trans hBX.symm) hAneB
      refine hhN ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr ?_)
      show Lp.map (MulAut.conj h).toMonoidHom = Lp
      rw [hmap]
      exact hsup
    · exfalso
      have hBL : B ≠ L := fun h => hBin (Or.inl h)
      have hBX : B ≠ X := fun h => hBin (Or.inr h)
      have hWdA : commSub ⊤ A = Wd L := by
        rcases hAin with hAL | hAX
        · rw [hAL]
        · rw [hAX]; exact hW
      have hWd_map : (Wd L).map h.toMonoidHom = Wd L := by
        have h1 : commSub ⊤ A = (Wd L).map h.toMonoidHom := by
          rw [show A = L.map (MulAut.conj h).toMonoidHom from rfl]
          exact w1369_commSub_top_map_conj L h
        exact h1.symm.trans hWdA
      have hBcommL : ⁅B, L⁆ = ⊥ :=
        CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hBcomp S.ctx.comp hBL
      have hBcommX : ⁅B, X⁆ = ⊥ :=
        CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hBcomp hXcomp hBX
      have hBcent : B ≤ Subgroup.centralizer ((L ⊔ X : Subgroup (MulAut W)) :
          Set (MulAut W)) := by
        rw [w1369_centralizer_sup_eq]
        exact le_inf (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBcommL)
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBcommX)
      have hBcommLp : ⁅B, L ⊔ X⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hBcent
      have hBstab : StableUnder B (Wd L) := by
        refine stableUnder_commSub (fun b hb l hl => ?_) (fun _ _ _ _ => Subgroup.mem_top _)
        have h1 : l * b = b * l := by
          have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBcommL
          exact Subgroup.mem_centralizer_iff.mp (h2 hb) l hl
        rw [← h1, mul_inv_cancel_right]
        exact hl
      have hB_Wd : commSub ⊤ B = Wd L := by
        have h1 : commSub ⊤ B = (Wd L).map h.toMonoidHom := by
          rw [show B = X.map (MulAut.conj h).toMonoidHom from rfl]
          rw [w1369_commSub_top_map_conj X h, hXeq]
        exact h1.trans hWd_map
      exact hcaseB B hBcomp hBL hBX hBcommLp hBstab hB_Wd
  have hB_notin : ¬ (B = L ∨ B = X) := by
    intro hBin
    exfalso
    have hWd_map : (Wd L).map h.toMonoidHom = Wd L := by
      have hWdB : commSub ⊤ B = Wd L := by
        rcases hBin with hBL' | hBX'
        · rw [hBL']
        · rw [hBX']; exact hW
      have h1 : commSub ⊤ B = (Wd L).map h.toMonoidHom := by
        rw [show B = X.map (MulAut.conj h).toMonoidHom from rfl]
        rw [w1369_commSub_top_map_conj X h, hXeq]
      exact h1.symm.trans hWdB
    have hAcommL : ⁅A, L⁆ = ⊥ :=
      CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hAcomp S.ctx.comp
        (fun h' => hA_notin (Or.inl h'))
    have hAcommX : ⁅A, X⁆ = ⊥ :=
      CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hAcomp hXcomp
        (fun h' => hA_notin (Or.inr h'))
    have hAcent : A ≤ Subgroup.centralizer ((L ⊔ X : Subgroup (MulAut W)) :
        Set (MulAut W)) := by
      rw [w1369_centralizer_sup_eq]
      exact le_inf (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAcommL)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAcommX)
    have hAcommLp : ⁅A, L ⊔ X⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAcent
    have hAstab : StableUnder A (Wd L) := by
      refine stableUnder_commSub (fun a ha l hl => ?_) (fun _ _ _ _ => Subgroup.mem_top _)
      have h1 : l * a = a * l := by
        have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAcommL
        exact Subgroup.mem_centralizer_iff.mp (h2 ha) l hl
      rw [← h1, mul_inv_cancel_right]
      exact hl
    have hA_Wd : commSub ⊤ A = Wd L := by
      have h1 : commSub ⊤ A = (Wd L).map h.toMonoidHom := by
        rw [show A = L.map (MulAut.conj h).toMonoidHom from rfl]
        exact w1369_commSub_top_map_conj L h
      exact h1.trans hWd_map
    exact hcaseB A hAcomp (fun h' => hA_notin (Or.inl h')) (fun h' => hA_notin (Or.inr h'))
      hAcommLp hAstab hA_Wd
  have hAL : A ≠ L := fun h => hA_notin (Or.inl h)
  have hAX : A ≠ X := fun h => hA_notin (Or.inr h)
  have hBL : B ≠ L := fun h => hB_notin (Or.inl h)
  have hBX : B ≠ X := fun h => hB_notin (Or.inr h)
  have hAcommL : ⁅A, L⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hAcomp S.ctx.comp hAL
  have hAcommX : ⁅A, X⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hAcomp hXcomp hAX
  have hBcommL : ⁅B, L⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hBcomp S.ctx.comp hBL
  have hBcommX : ⁅B, X⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hBcomp hXcomp hBX
  have hABcent : A ⊔ B ≤ Subgroup.centralizer ((L ⊔ X : Subgroup (MulAut W)) :
      Set (MulAut W)) := by
    rw [w1369_centralizer_sup_eq]
    refine le_inf (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAcommL
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBcommL
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAcommX
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBcommX
  have hABcomm : ⁅A ⊔ B, L ⊔ X⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hABcent
  have hAstab : StableUnder A (Wd L) := by
    refine stableUnder_commSub (fun a ha l hl => ?_) (fun _ _ _ _ => Subgroup.mem_top _)
    have h1 : l * a = a * l := by
      have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAcommL
      exact Subgroup.mem_centralizer_iff.mp (h2 ha) l hl
    rw [← h1, mul_inv_cancel_right]
    exact hl
  have hBstab : StableUnder B (Wd L) := by
    refine stableUnder_commSub (fun b hb l hl => ?_) (fun _ _ _ _ => Subgroup.mem_top _)
    have h1 : l * b = b * l := by
      have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBcommL
      exact Subgroup.mem_centralizer_iff.mp (h2 hb) l hl
    rw [← h1, mul_inv_cancel_right]
    exact hl
  have hABstab : StableUnder (A ⊔ B) (Wd L) :=
    w1369_stableUnder_sup_of_stable hAstab hBstab
  have htriv : commSub (Wd L) (A ⊔ B) = ⊥ :=
    w1369_commSub_Wd_eq_bot_of_comm hS hC hXL hABstab hABcomm
  have hcommLp : commSub ⊤ Lp = Wd L := by
    have h1 : commSub ⊤ Lp = commSub ⊤ L ⊔ commSub ⊤ X := by
      rw [show Lp = L ⊔ X from rfl]
      exact w1369_commSub_sup_right L X
    rw [h1, hXeq, show commSub ⊤ L = Wd L from rfl]
    exact sup_idem _
  refine ⟨?_, ?_⟩
  · rw [hmap, Subgroup.commutator_comm]
    exact hABcomm
  · rw [hmap, hcommLp]
    exact htriv

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
