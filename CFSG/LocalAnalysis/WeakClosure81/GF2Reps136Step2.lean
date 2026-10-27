module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136S
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13Stmts4
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_statedProj_equiv_of_card_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (hK : Nat.card K = 2) (H : Subgroup (GL ι K)) :
    Nonempty (StatedProj H ≃* H) := by
  have hbot : (StatedScalars ι K).subgroupOf H = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK ι, Subgroup.bot_subgroupOf]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot⟩

private theorem w1369_isSLn_three_of_isL3 {X : Type} [Group X] (h : IsL3 X 1) :
    IsSLn X 3 1 := by
  have hc : StatedClassicalModel X .PSL 3 2 1 :=
    LieModel.statedClassicalModel h (by decide)
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := hc
  obtain ⟨f⟩ := w1369_statedProj_equiv_of_card_two (K := K) (by simpa using hK) (StatedSL 3 K)
  exact ⟨K, hF, hfin, hK, ⟨e.trans f⟩⟩

private theorem w1369_commSub_map_conj (U : Subgroup W) (X : Subgroup (MulAut W))
    (g : MulAut W) :
    commSub (U.map g.toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) =
      (commSub U X).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    refine ⟨x₀ w₀ * w₀⁻¹, ⟨x₀, hx₀, w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, w₀, hw₀, rfl⟩ := hs
    refine ⟨MulAut.conj g x₀, ⟨x₀, hx₀, rfl⟩, g w₀, ⟨w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]

private theorem w1369_commSub_map_conj_inv (U : Subgroup W) (X : Subgroup (MulAut W))
    (g : MulAut W) :
    (commSub (U.map (g⁻¹).toMonoidHom) X).map g.toMonoidHom =
      commSub U (X.map (MulAut.conj g).toMonoidHom) := by
  have hcomp : ((U.map (g⁻¹).toMonoidHom).map g.toMonoidHom) = U := by
    rw [Subgroup.map_map,
      show g.toMonoidHom.comp (g⁻¹).toMonoidHom = MonoidHom.id W by ext x; simp,
      Subgroup.map_id]
  rw [← w1369_commSub_map_conj (U.map (g⁻¹).toMonoidHom) X g, hcomp]

private theorem w1369_stableUnder_sup {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊔ B) := by
  intro x hx u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA x hx a ha) (hB x hx b hb)

private theorem w1369_commSub_sup (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have h1 : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv_rev]
      calc x a * x b * (b⁻¹ * a⁻¹)
          = x a * x b * (a⁻¹ * b⁻¹) := by rw [mul_comm (b⁻¹) (a⁻¹)]
        _ = x a * (x b * (a⁻¹ * b⁻¹)) := by rw [mul_assoc]
        _ = x a * (a⁻¹ * (x b * b⁻¹)) := by
              rw [← mul_assoc (x b) (a⁻¹) (b⁻¹), mul_comm (x b) (a⁻¹), mul_assoc]
        _ = (x a * a⁻¹) * (x b * b⁻¹) := by rw [← mul_assoc]
    rw [h1]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
      (Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem w1369_false_of_component_le_both {Y : Subgroup (MulAut W)} {t : MulAut W}
    (S : Std136 Y t) {L : Subgroup (MulAut W)} {g : MulAut W} (hgY : g ∈ Y)
    (hWgL : commSub ((Wd L).map g.toMonoidHom) L = ⊥)
    {K₁ : Subgroup (MulAut W)} (hK₁ : IsComponentOf K₁ Y) (hK₁L : K₁ ≤ L)
    (hK₁Lg : K₁ ≤ L.map (MulAut.conj g).toMonoidHom) : False := by
  have hperf : ⁅K₁, K₁⁆ = K₁ :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK₁.2.2.1)
  have hle : commSub (commSub ⊤ K₁) K₁ ≤ commSub ((Wd L).map g.toMonoidHom) L := by
    refine commSub_mono ?_ hK₁L
    calc commSub ⊤ K₁ ≤ commSub ⊤ (L.map (MulAut.conj g).toMonoidHom) :=
          commSub_mono le_top hK₁Lg
      _ = (commSub ⊤ L).map g.toMonoidHom := w1369_commSub_top_map_conj L g
  have hbot : commSub (commSub ⊤ K₁) K₁ ≤ ⊥ := by rw [hWgL] at hle; exact hle
  have htopbot : commSub ⊤ K₁ ≤ ⊥ :=
    s13_perfect_chain K₁ hperf ⊥ (commSub ⊤ K₁) ⊤ hbot le_rfl
  have hK₁bot : K₁ = ⊥ := by
    have hfix : ⊤ ≤ fixV K₁ := commSub_eq_bot_iff.mp (le_bot_iff.mp htopbot)
    rw [eq_bot_iff]
    intro x hx
    have hx1 : x = 1 := by
      ext w
      exact mem_fixV.mp (hfix (Subgroup.mem_top w)) x hx
    rw [hx1]
    exact Subgroup.one_mem _
  haveI : Nontrivial ↥K₁ := CFSG.ComponentClassification.Quasisimple.nontrivial hK₁.2.2
  exact (K₁.nontrivial_iff_ne_bot.mp this) hK₁bot

private theorem w1369_commutator_components {Y : Subgroup (MulAut W)} {t : MulAut W}
    (S : Std136 Y t) {L : Subgroup (MulAut W)} {g : MulAut W} (hgY : g ∈ Y)
    (hWgL : commSub ((Wd L).map g.toMonoidHom) L = ⊥)
    {A B : Subgroup (MulAut W)} (hA : IsComponentOf A Y) (hB : IsComponentOf B Y)
    (hAL : A ≤ L) (hBLg : B ≤ L.map (MulAut.conj g).toMonoidHom) :
    ⁅A, B⁆ = ⊥ := by
  by_cases hAB : A = B
  · exfalso
    subst hAB
    exact w1369_false_of_component_le_both S hgY hWgL hA hAL hBLg
  · exact CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hA hB hAB

private theorem w1369_irrSet_eq_singleton {K : Subgroup (MulAut W)}
    (hI : commSub ⊤ K ∈ irrSet K) {J : Subgroup W} (hJ : J ∈ irrSet K) :
    J = commSub ⊤ K := by
  have hJIrr := hJ.2
  have hIIrr := hI.2
  have hJle : J ≤ commSub ⊤ K := by
    calc J = commSub J K := hJ.1.symm
      _ ≤ commSub ⊤ K := commSub_mono le_top le_rfl
  have hstable : StableUnder K (J ⊔ (commSub ⊤ K ⊓ fixV K)) :=
    w1369_stableUnder_sup hJIrr.2.1 hIIrr.2.2.1
  rcases hIIrr.2.2.2 (J ⊔ (commSub ⊤ K ⊓ fixV K)) hstable
      le_sup_right (sup_le hJle inf_le_left) with h | h
  · exfalso
    have hJfix : J ≤ fixV K := by
      calc J ≤ J ⊔ (commSub ⊤ K ⊓ fixV K) := le_sup_left
        _ = commSub ⊤ K ⊓ fixV K := h
        _ ≤ fixV K := inf_le_right
    have hJbot : J = ⊥ := by
      have hcomm : commSub J K = ⊥ := commSub_eq_bot_iff.mpr hJfix
      rw [hJ.1] at hcomm
      exact hcomm
    have hlt : J ⊓ fixV K < J := hJIrr.1
    rw [hJbot, bot_inf_eq] at hlt
    exact absurd hlt (lt_irrefl ⊥)
  · have hone : commSub ⊤ K = J := by
      have hstep : commSub (J ⊔ (commSub ⊤ K ⊓ fixV K)) K = commSub ⊤ K := by
        rw [h, hI.1]
      calc commSub ⊤ K = commSub (J ⊔ (commSub ⊤ K ⊓ fixV K)) K := hstep.symm
        _ = commSub J K ⊔ commSub (commSub ⊤ K ⊓ fixV K) K := w1369_commSub_sup _ _ K
        _ = J ⊔ ⊥ := by rw [hJ.1, (commSub_eq_bot_iff).mpr inf_le_right]
        _ = J := sup_bot_eq J
    exact hone.symm

theorem step2 (h134 : W4Lem13_4) (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} (S : Std136 Y t) {K : Subgroup (MulAut W)} (hK : IsComponentOf K Y)
    (hmove : K.map (MulAut.conj t).toMonoidHom ≠ K) :
    ∃ L : Subgroup (MulAut W), Conc4_136W Y t L := by
  classical
  obtain ⟨h134a, h134b⟩ | ⟨hL3, hIrr, hclause, hBNSL⟩ :=
    h134 W hw2 Y S.isK S.o2 t S.tY S.t2 S.cost K hK hmove
  ·
    set L : Subgroup (MulAut W) := K ⊔ K.map (MulAut.conj t).toMonoidHom with hLdef
    have hKg : IsComponentOf (K.map (MulAut.conj t).toMonoidHom) Y :=
      CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK S.tY
    have hspanK : (⨆ X ∈ conjSubs Y (commSub ⊤ K), X) = ⊤ :=
      lemmaS hK.1 (comm_top_of_component S hw2 hK)
    have hspan : (⨆ X ∈ conjSubs Y (commSub ⊤ L), X) = ⊤ := by
      have hle : (⨆ X ∈ conjSubs Y (commSub ⊤ K), X) ≤
          (⨆ X ∈ conjSubs Y (commSub ⊤ L), X) := by
        refine iSup₂_le fun X hX => ?_
        obtain ⟨φ, hφ, rfl⟩ := hX
        refine le_iSup₂_of_le ((commSub ⊤ L).map φ.toMonoidHom) ⟨φ, hφ, rfl⟩ ?_
        exact Subgroup.map_mono (commSub_mono le_top (by rw [hLdef]; exact le_sup_left))
      exact eq_top_iff.mpr (le_of_eq_of_le hspanK.symm hle)
    refine ⟨L, hspan, ?_, Or.inr (Or.inl ⟨K, hK, t, S.tY, Ne.symm hmove, hLdef, ?_⟩)⟩
    · intro g hg hgN
      have hgNinv : g⁻¹ ∉ Subgroup.normalizer (L : Set (MulAut W)) := fun h =>
        hgN (by simpa using (Subgroup.normalizer (L : Set (MulAut W))).inv_mem h)
      have hWgL : commSub (Wd L) (L.map (MulAut.conj g).toMonoidHom) = ⊥ := by
        have h := h134b g⁻¹ (Y.inv_mem hg) hgNinv
        rw [← w1369_commSub_map_conj_inv (Wd L) L g, h, Subgroup.map_bot]
      have hclg : commSub ((Wd L).map g.toMonoidHom) L = ⊥ := h134b g hg hgN
      have hKg' : IsComponentOf (K.map (MulAut.conj g).toMonoidHom) Y :=
        CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK hg
      have hKtg' : IsComponentOf ((K.map (MulAut.conj t).toMonoidHom).map
          (MulAut.conj g).toMonoidHom) Y :=
        CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hKg hg
      have hleKL : K ≤ L := by rw [hLdef]; exact le_sup_left
      have hleKtL : K.map (MulAut.conj t).toMonoidHom ≤ L := by
        rw [hLdef]; exact le_sup_right
      have hleKgLg : K.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom := by
        rw [hLdef]
        exact Subgroup.map_mono le_sup_left
      have hleKtgLg : (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
          L.map (MulAut.conj g).toMonoidHom := by
        rw [hLdef]
        exact Subgroup.map_mono le_sup_right
      have hKKg : ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
        w1369_commutator_components S hg hclg hK hKg' hleKL hleKgLg
      have hKKtg : ⁅K, (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
        w1369_commutator_components S hg hclg hK hKtg' hleKL hleKtgLg
      have hKtgKg : ⁅K.map (MulAut.conj t).toMonoidHom, K.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
        w1369_commutator_components S hg hclg hKg hKg' hleKtL hleKgLg
      have hKtgKtg : ⁅K.map (MulAut.conj t).toMonoidHom,
          (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
        w1369_commutator_components S hg hclg hKg hKtg' hleKtL hleKtgLg
      have hKKg' : K ≤ Subgroup.centralizer
          (K.map (MulAut.conj g).toMonoidHom : Set (MulAut W)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKKg
      have hKKtg' : K ≤ Subgroup.centralizer
          ((K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom :
            Set (MulAut W)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKKtg
      have hKtgKg' : K.map (MulAut.conj t).toMonoidHom ≤ Subgroup.centralizer
          (K.map (MulAut.conj g).toMonoidHom : Set (MulAut W)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKtgKg
      have hKtgKtg' : K.map (MulAut.conj t).toMonoidHom ≤ Subgroup.centralizer
          ((K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom :
            Set (MulAut W)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKtgKtg
      have hcomm : ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        rw [hLdef, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rw [← Subgroup.le_centralizer_iff]
          exact sup_le (Subgroup.le_centralizer_iff.mpr hKKg')
            (Subgroup.le_centralizer_iff.mpr hKKtg')
        · rw [← Subgroup.le_centralizer_iff]
          exact sup_le (Subgroup.le_centralizer_iff.mpr hKtgKg')
            (Subgroup.le_centralizer_iff.mpr hKtgKtg')
      exact ⟨hcomm, hWgL⟩
    ·
      have h134a' : ((IsL3 ↥K 1 ∧ NatTensor L (commSub ⊤ L) ⊥ 3 1) ∨
          (IsL2 ↥K 2 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 2) ∨
          (IsL2 ↥K 3 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 3)) := by
        simpa only [hLdef] using h134a
      exact h134a'
  ·
    have hSLn : IsSLn ↥K 3 1 := w1369_isSLn_three_of_isL3 hL3
    have hsum : SumOfAtMostThreeNat K (commSub ⊤ K) (commSub ⊤ K ⊓ fixV K) := by
      refine ⟨1, by norm_num, 3, Or.inl ⟨hSLn, ?_⟩⟩
      refine ⟨fun _ => commSub ⊤ K, ?_, ?_, ?_, ?_⟩
      · intro i
        exact inf_le_left
      · intro i
        have hzero : (⨆ (j : Fin 1) (_ : j ≠ i), (fun _ : Fin 1 => commSub ⊤ K) j) = ⊥ :=
          iSup_eq_bot.mpr fun j =>
            iSup_eq_bot.mpr fun hj => absurd (Subsingleton.elim j i) hj
        rw [hzero, sup_bot_eq]
        exact inf_le_right
      · have hsup : (⨆ i : Fin 1, (fun _ => commSub ⊤ K) i) = commSub ⊤ K := by
          apply le_antisymm
          · exact iSup_le fun i => le_rfl
          · exact le_iSup (fun _ : Fin 1 => commSub ⊤ K) 0
        rw [hsup]
        exact sup_eq_right.mpr inf_le_left
      · intro i
        exact hBNSL
    have htrans : ∀ I₁ ∈ irrSet K, ∀ I₂ ∈ irrSet K,
        ∃ g ∈ Y ⊓ Subgroup.normalizer (K : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom := by
      intro I₁ hI₁ I₂ hI₂
      refine ⟨1, ⟨Y.one_mem, Subgroup.one_mem _⟩, ?_⟩
      rw [w1369_irrSet_eq_singleton hIrr hI₁, w1369_irrSet_eq_singleton hIrr hI₂]
      exact (Subgroup.map_id (commSub ⊤ K)).symm
    refine ⟨K, ?_, ?_, Or.inr (Or.inr (Or.inl ⟨hK, hsum, htrans⟩))⟩
    · exact lemmaS hK.1 (comm_top_of_component S hw2 hK)
    · intro g hg hgN
      have hne : K.map (MulAut.conj g).toMonoidHom ≠ K := fun h =>
        hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
      exact ⟨CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hK
        (CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK hg) (Ne.symm hne), hclause g hg hgN⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
