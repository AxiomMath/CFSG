module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma s16h_comm_of_mem_cElt_bot {M : Subgroup G} {v : G} {m : G}
    (hm : m ∈ F11.CElt M ⊥ v) : m * v = v * m := by
  have h1 : m * v * m⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.1 hm.2.2
  refine mul_inv_eq_one.mp ?_
  rw [mul_inv_rev]
  simpa only [mul_assoc] using h1

theorem s16h_unique₁_of_mixed_of_Eb (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {q : ℕ} (hq : q ∈ D.sig)
    (hEb : ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian q E ∧
      q ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))))
    (hc : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L) = ⊥ ∨
        ∀ T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
          T ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
            normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
          (∀ g ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
            normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _),
              ∀ x ∈ T, g * x * g⁻¹ ∈ T) →
          (∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) →
          (∃ f ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
            normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _),
              ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
              f ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
                fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
              f ^ r ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
                fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) →
          T ≤ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨E, hEM, hE, hEX⟩ := hEb
  have hW := s16h_uniqueMax_of_card_le D S.h61 S.h127 h hq (S.hx.three_le q hq) hE hEX
  rcases hc with hZ | hO2
  · refine s16h_unique₁_of_wSub D h.hyp151 ?_ hW
    rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
    have hCW : wSub ⊥ V hV L ⊓ centralizer (L : Set G) = ⊥ := by
      refine le_bot_iff.1 fun x hx => ?_
      have hxV : x ∈ V := preTil_le ⊥ V hV _ hx.1
      have hx1 : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) = 1 := by
        have hmem : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈
            commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) := by
          refine ⟨?_, ?_⟩
          · have h1 : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈
                imgTil ⊥ V hV (wSub ⊥ V hV L) :=
              (mem_imgTil ⊥ V hV _ _).2 ⟨IntMod.mk hV ⟨x, hxV⟩, hx.1, rfl⟩
            rw [wSub, imgTil_preTil] at h1
            exact h1
          · change mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ fixV (lBar ⊥ V hV L)
            rw [mem_fixV]
            intro φ hφ
            obtain ⟨l, hl, rfl⟩ := (mem_barSub ⊥ V hV L φ).1 hφ
            rw [actTil_mk]
            congr 1
            refine IntMod.val_injective ?_
            rw [actStab_apply_val]
            have hc := (Subgroup.mem_centralizer_iff.1 hx.2) (l : G) hl
            show (l : G) * x * (l : G)⁻¹ = x
            rw [hc]
            group
        rw [hZ, Subgroup.mem_bot] at hmem
        exact hmem
      have hxpre : x ∈ preTil ⊥ V hV (⊥ : Subgroup (Vtil ⊥ V hV)) :=
        (mem_preTil_iff_of_mem ⊥ V hV ⊥ hxV).2 (by rw [hx1]; exact Subgroup.one_mem _)
      rw [preTil_bot, Subgroup.mem_inf] at hxpre
      exact hxpre.2
    rw [hCW]
    simp [conjSubgroup_eq_bot_iff]
  · have hpp := D.sig_prime q hq
    have hpp := D.sig_prime q hq
    set Eb : Subgroup G := E ⊓ preBarSub D.M ⊥ V hV (centSub (wTil ⊥ V hV L)) with hEbdef
    have hEbE : Eb ≤ E := by rw [hEbdef]; exact inf_le_left
    have hEbX : Eb ≤ preBarSub D.M ⊥ V hV (centSub (wTil ⊥ V hV L)) := by
      rw [hEbdef]; exact inf_le_right
    have hEbM : Eb ≤ D.M := hEbE.trans hEM
    have hEab : IsElemAbelian q Eb := by rw [hEbdef]; exact hE.mono inf_le_left
    have hcardEb : q ^ 2 ≤ Nat.card Eb := hEX
    have hEbc : ¬ IsCyclic ↥Eb := s16c7_not_isCyclic_of_elemAbelian hpp.1 hEab hcardEb
    intro w hw hw1
    by_cases hα : ∀ v ∈ v1Sub D.M ⊥ V hV L, ∀ e ∈ Eb, e * v = v * e
    · have hsup_cent : wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L ≤
          Subgroup.centralizer (Eb : Set G) := by
        refine sup_le ?_ ?_
        · intro u hu
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          exact s16h_comm_of_mem_cElt_bot
            (s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hu (hEbX he))
        · intro v hv
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          exact hα v hv e he
      have hle : Eb ≤ D.M ⊓ Subgroup.centralizer ({w} : Set G) := by
        intro e he
        refine ⟨hEbM he, ?_⟩
        refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (Subgroup.mem_centralizer_iff.1 (hsup_cent hw) e he).symm
      exact s16c34_uniqueMax_of_noncyclic D S.h61 hq (IsElemAbelian.isPGroup hEab) hEbc hle
        inf_le_left
    · obtain ⟨v, hv⟩ := not_forall.1 hα
      obtain ⟨hv1, hv2⟩ := Classical.not_imp.1 hv
      obtain ⟨e, he⟩ := not_forall.1 hv2
      obtain ⟨heE, hne⟩ := Classical.not_imp.1 he
      have heM : e ∈ D.M := hEbM heE
      have heq : e ^ q = 1 := hEab.2 e heE
      have heW : ∀ u ∈ wSub ⊥ V hV L, e * u = u * e := fun u hu =>
        s16h_comm_of_mem_cElt_bot
          (s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hu (hEbX heE))
      exact (s16h_false_of_mixed_beta D S h hs hq heM heq heW ⟨v, hv1, hne⟩ hO2).elim


theorem s16h_unique₁_of_mixed (D : Data G) (S : s16h_Std D)
    (h4 : 3 < CFSG.Open.evenRank G) (hσ : D.sig = D.sig1)
    {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {q : ℕ} (hq : q ∈ D.sig)
    (hb : s16h_BlockBound (Mbar D.M ⊥ V h.hyp151.isElemAbelian)
      (lBar ⊥ V h.hyp151.isElemAbelian L) q 2)
    (hc : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L) = ⊥ ∨
        ∀ T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
          T ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
            normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
          (∀ g ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
            normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _),
              ∀ x ∈ T, g * x * g⁻¹ ∈ T) →
          (∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) →
          (∃ f ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
            normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _),
              ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
              f ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
                fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
              f ^ r ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
                fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) →
          T ≤ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have h4' : 4 ≤ CFSG.Open.pRank q D.M := S.hx.four_le h4 q hq
  have hpp := D.sig_prime q hq
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 4) hpp.1
      (by rw [UC6.groupPRank_eq_pRank]; exact h4')
  have hEn := s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 hs.le
    (hpp.1.odd_of_ne_two hpp.2) hEM hE
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hb hEM hE hEn
  refine s16h_unique₁_of_mixed_of_Eb D S hσ h hs hq ⟨E, hEM, hE, ?_⟩ hc
  rw [hEcard] at hcard
  refine Nat.le_of_mul_le_mul_left (a := q ^ 2) ?_ (pow_pos hpp.1.pos 2)
  calc q ^ 2 * q ^ 2 = q ^ 4 := by ring
    _ ≤ _ := hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
