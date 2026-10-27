module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3FrameDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16k_preBarSub_le_stabTil (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (X : Subgroup (MulAut (Vtil V₀ V hV))) :
    preBarSub M V₀ V hV X ≤ stabTil V₀ V := by
  intro g hg
  exact Subgroup.map_subtype_le (X.comap (actTil V₀ V hV)) (Subgroup.mem_inf.1 hg).2

private theorem s16k_barSub_rechoice {D : Data G} (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {X : Subgroup (MulAut (Vtil V₀ V hV))} (hX : X ≤ Mbar D.M V₀ V hV)
    (hXp : IsPGroup 3 ↥X) :
    barSub V₀ V hV (twoResidual (preBarSub D.M V₀ V hV X)) = X := by
  have hle : preBarSub D.M V₀ V hV X ≤ stabTil V₀ V :=
    s16k_preBarSub_le_stabTil D.M V₀ V hV X
  rw [barSub_twoResidual V₀ V hV hle, barSub_preBarSub, inf_eq_left.2 hX]
  exact twoResidual_eq_self_of_isPGroup_three hXp

private theorem s16k_commSub_map_eq_of_map_conj {W : Type} [CommGroup W]
    {X Y : Subgroup (MulAut W)} {g : MulAut W}
    (h : X.map (MulAut.conj g).toMonoidHom = Y) :
    (commSub ⊤ X).map g.toMonoidHom = commSub ⊤ Y := by
  rw [← h]
  exact (s15_Infra_commSub_top_map_conj X g).symm

private theorem s16k_conjSubs_commSub_eq_range {W : Type} [CommGroup W]
    {A : Subgroup (MulAut W)} {E : Fin 3 → Subgroup (MulAut W)}
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (E i).map (MulAut.conj g).toMonoidHom = E j)
    (htrans : ∀ i j, ∃ g ∈ A, (E i).map (MulAut.conj g).toMonoidHom = E j) (i : Fin 3) :
    conjSubs A (commSub ⊤ (E i)) = Set.range (fun j => commSub ⊤ (E j)) := by
  ext Y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨j, hj⟩ := hperm g hg i
    exact ⟨j, (s16k_commSub_map_eq_of_map_conj hj).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨g, hg, hj⟩ := htrans i j
    exact ⟨g, hg, (s16k_commSub_map_eq_of_map_conj hj).symm⟩

variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16k_false_of_frame (h : S16kBase D V₀ V L hV)
    {E : Fin 3 → Subgroup (MulAut (Vtil V₀ V hV))}
    (hE : S16kFrame (Mbar D.M V₀ V hV) E) : False := by
  obtain ⟨t, htM, ht2, ht1, htrk, -⟩ := h.conc
  obtain ⟨i, hi⟩ := hE.noninvol t htM ht2 ht1
  let L' : Subgroup G := twoResidual (preBarSub D.M V₀ V hV (E i))
  have hXp : IsPGroup 3 ↥(E i) :=
    IsPGroup.of_card (n := 1) (by rw [(hE.cyc i).2, pow_one])
  have hbar : barSub V₀ V hV L' = E i := s16k_barSub_rechoice V₀ V hV (hE.le i) hXp
  have hL' : barSub V₀ V hV L' ≠ ⊥ := by
    rw [hbar]
    intro hbot
    have hcard := (hE.cyc i).2
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hconjSubs : conjSubs (Mbar D.M V₀ V hV) (commSub ⊤ (E i)) =
      Set.range (fun j => commSub ⊤ (E j)) :=
    s16k_conjSubs_commSub_eq_range hE.perm hE.trans i
  have hspan : (⨆ X ∈ conjSubs (Mbar D.M V₀ V hV) (commSub ⊤ (E i)), X) = ⊤ := by
    rw [hconjSubs, iSup_range, hE.span]
  have h133 : Conc4_133 (Mbar D.M V₀ V hV) t (E i) := by
    refine ⟨3, Nat.prime_three, hE.le_core i, hi, ?_,
      Or.inl ⟨hE.cyc i, Or.inl (hE.rk_two i)⟩⟩
    rw [hconjSubs]
    exact hE.indep
  have h136W : Conc4_136W (Mbar D.M V₀ V hV) t (E i) := by
    refine ⟨hspan, ?_, Or.inl h133⟩
    intro g hg hgn
    obtain ⟨j, hj⟩ := hE.perm g hg i
    have hji : j ≠ i := by
      intro hji'
      exact hgn (Subgroup.mem_normalizer_iff_map_conj_eq.2 (hji' ▸ hj))
    refine ⟨?_, ?_⟩
    · rw [hj]
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hE.comm i j x hx y hy).symm
    · rw [hj]
      exact hE.cent i j (Ne.symm hji)
  have h136 : Conc4_136 D V₀ V hV L' := by
    refine ⟨t, htM, ht2, ht1, htrk, ?_⟩
    show Conc4_136W (Mbar D.M V₀ V hV) t (lBar V₀ V hV L')
    simp only [lBar, hbar]
    exact h136W
  have hset' : Setting16 D V₀ V L' := by
    refine ⟨h.setting.hyp16, ?_⟩
    refine ⟨h.setting.hyp151.hyp125, ?_, twoResidual_twoResidual _, ?_, ?_⟩
    · exact (twoResidual_le _).trans inf_le_left
    · rw [hbar]
      exact fstar_eq_self_of_isPGroup (p := 3) hXp
    · intro g hg hgn
      have hgs : g ∈ stabTil V₀ V := s16g_le_stabTil h.setting hg
      let gb : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨g, hgs⟩
      have hgbM : gb ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV hg hgs
      have hgbN : gb ∉ Subgroup.normalizer (E i : Set (MulAut (Vtil V₀ V hV))) := by
        intro hgN
        exact hgn ((mem_preBarSub D.M V₀ V hV
          (Subgroup.normalizer (barSub V₀ V hV L' : Set (MulAut (Vtil V₀ V hV))))).2
          ⟨hg, hgs, by rw [hbar]; exact hgN⟩)
      obtain ⟨j, hj⟩ := hE.perm gb hgbM i
      have hji : j ≠ i := by
        intro hji'
        exact hgbN (Subgroup.mem_normalizer_iff_map_conj_eq.2 (hji' ▸ hj))
      obtain ⟨j', hj'⟩ := hE.perm gb⁻¹ ((Mbar D.M V₀ V hV).inv_mem hgbM) i
      have hbar' : barSub V₀ V hV (conjSubgroup L' g) = E j' := by
        rw [s15_Infra_barSub_conjSubgroup V₀ V hV hgs L', hbar, hj']
      have hj'i : j' ≠ i := by
        intro hji'
        exact hgbN ((Subgroup.normalizer _).inv_mem
          (Subgroup.mem_normalizer_iff_map_conj_eq.2 (hji' ▸ hj')))
      refine ⟨?_, ?_⟩
      · rw [hbar, hbar']
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hE.comm i j' x hx y hy).symm
      · rw [wTil, hbar, hbar']
        exact hE.cent i j' (Ne.symm hj'i)
  have hs : s15 D.M V₀ V hV L' = 1 :=
    s16f_s15_eq_one_of_four D h.std.hx h.std.h4 h.std.h61 h.std.h127 h.std.h1217
      h.std.h164 hV hset' hL' h136
  obtain ⟨j, hji⟩ : ∃ j : Fin 3, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
  obtain ⟨g, hg, hgj⟩ := hE.trans i j
  have hgc := lBar_conj_eq_of_s15_eq_one (D := D) (V₀ := V₀) (V := V) (L := L') (g := g) hs hg
  simp only [lBar, hbar, hgj] at hgc
  exact hji (hE.inj hgc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
