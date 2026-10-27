module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure S16kBase (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  std : S16gStd D
  setting : Setting16 D V₀ V L
  ne : barSub V₀ V hV L ≠ ⊥
  conc : Conc4_136 D V₀ V hV L
  s1 : s15 D.M V₀ V hV L = 1

variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem S16kBase.toRowCtx (h : S16kBase D V₀ V L hV)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) : S16gRowCtx D V₀ V L hV :=
  ⟨h.std, h.setting, h.conc, h.s1, hq⟩

theorem S16kBase.comm_top (h : S16kBase D V₀ V L hV) :
    commSub ⊤ (lBar V₀ V hV L) = ⊤ :=
  wTil_eq_top_of_case163_2 h.conc h.s1

theorem S16kBase.conj_eq (h : S16kBase D V₀ V L hV) {g : MulAut (Vtil V₀ V hV)}
    (hg : g ∈ Mbar D.M V₀ V hV) :
    (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L :=
  lBar_conj_eq_of_s15_eq_one h.s1 hg

theorem S16kBase.mBar_le_normalizer (h : S16kBase D V₀ V L hV) :
    Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
  fun _ hg => Subgroup.mem_normalizer_iff_map_conj_eq.2 (h.conj_eq hg)

theorem S16kBase.three_le_pRank (h : S16kBase D V₀ V L hV) {p : ℕ} (hpσ : p ∈ D.sig) :
    3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) :=
  s16c1610_three_le_pRank_mBar_of_four D h.std.hx h.std.h61 h.std.h127 h.setting.hyp16 hV
    h.std.h4 hpσ

theorem S16kBase.exists_sig (h : S16kBase D V₀ V L hV) : ∃ p : ℕ, p ∈ D.sig :=
  h.std.hx.sig_nonempty

section Sum

variable {W : Type} [CommGroup W]

theorem s16k_sumOfNat_one {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (hZ : Z ≤ U) (h : SumOfNat N H U Z 1) :
    N H U Z := by
  obtain ⟨I, hZI, -, hsup, hN⟩ := h
  have h0 : (⨆ i : Fin 1, I i) = I 0 := by
    refine le_antisymm (iSup_le fun i => ?_) (le_iSup I 0)
    rw [Subsingleton.elim i 0]
  have hU : I 0 = U := by
    rw [h0, sup_eq_right.2 (hZI 0)] at hsup
    exact hsup
  rw [← hU]
  exact hN 0

theorem s16k_sumOfNat_zero {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (h : SumOfNat N H U Z 0) : U = Z := by
  obtain ⟨I, -, -, hsup, -⟩ := h
  have h0 : (⨆ i : Fin 0, I i) = ⊥ := iSup_of_empty I
  rw [h0, sup_bot_eq] at hsup
  exact hsup.symm

end Sum

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
