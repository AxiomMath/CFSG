module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoB1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoA
public import CFSG.LargeExtraspecial.S5Gen2
public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_commSub_le_iff {U C : Subgroup W} {X : Subgroup (MulAut W)} :
    commSub U X ≤ C ↔ ∀ x ∈ X, ∀ u ∈ U, x u * u⁻¹ ∈ C := by
  constructor
  · intro h x hx u hu
    exact h (Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩)
  · intro h
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    exact h x hx u hu

private theorem w1369_stableUnder_commSub_self {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hU : StableUnder X U) : StableUnder X (commSub U X) := by
  intro x hx c hc
  refine Subgroup.closure_induction (p := fun c _ => x c ∈ commSub U X) ?_ ?_ ?_ ?_ hc
  · rintro c ⟨y, hy, u, hu, rfl⟩
    have hconj : x * y * x⁻¹ ∈ X := X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
    have hxu : x u ∈ U := hU x hx u hu
    have h1 : x (y u) = (x * y * x⁻¹) (x u) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [map_mul, map_inv, h1]
    exact Subgroup.subset_closure ⟨x * y * x⁻¹, hconj, x u, hxu, rfl⟩
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ iha ihb; rw [map_mul]; exact (commSub U X).mul_mem iha ihb
  · intro a _ iha; rw [map_inv]; exact (commSub U X).inv_mem iha

private theorem w1369_stableUnder_Wd (L : Subgroup (MulAut W)) : StableUnder L (Wd L) :=
  w1369_stableUnder_commSub_self (X := L) (U := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)

private theorem w1369_commSub_Wd_self {L : Subgroup (MulAut W)} (hLp : ⁅L, L⁆ = L) :
    commSub (Wd L) L = Wd L := by
  refine le_antisymm (commSub_le_of_invariant (w1369_stableUnder_Wd L)) ?_
  exact s13_perfect_chain L hLp (commSub (Wd L) L) (Wd L) ⊤ le_rfl le_rfl

theorem swap_structure (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} {g : MulAut W}
    (S : Swap136 Y t L g) :
    Wd (Lc L g) = Wd L ∧ Cd L = ⊥ ∧ Cd (Lc L g) = ⊥ ∧ Strong3 L (Lc L g) := by
  have hw2' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hw2 w
  have hLp : ⁅L, L⁆ = L :=
    CFSG.LargeExtraspecial.S5.commutator_eq_self_of_isQuasisimple S.ctx.comp.2.2
  obtain ⟨hcompX, hneX, hcommXL, hperfX, hXY⟩ := swap_comp S
  have hcommLX : ⁅L, Lc L g⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]; exact hcommXL
  have hcentXL : Lc L g ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommXL
  have hcentLX : L ≤ Subgroup.centralizer (Lc L g : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLX
  have hStrong : Strong3 L (Lc L g) := by
    rcases perfect_cent_dichotomy hw2 S.ctx S.hfix hXY hperfX hcommXL with h | h
    · exact absurd h (swap_nontriv hw2' S)
    · exact h
  have hGL3 : GL3Case L (Lc L g) (Wd L) (Cd L) := hStrong.1
  have hntriv : ¬ commSub (Wd L) (Lc L g) ≤ Cd L := by
    rw [w1369_commSub_le_iff]
    exact swap_nontriv hw2' S
  have hStableX_U : StableUnder (Lc L g) (Wd L) := by
    intro x hx u hu
    exact CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := L) (B := Lc L g) (M := ⊤)
      (fun y hy b hb => (Subgroup.mem_centralizer_iff.mp (hcentXL hb)) y hy)
      (fun b _ m _ => Subgroup.mem_top m) x hx u hu
  have hStableL_U : StableUnder L (Wd L) := w1369_stableUnder_Wd L
  have hStableL_cX : StableUnder L (commSub (Wd L) (Lc L g)) := by
    intro l hl c hc
    exact CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := Lc L g) (B := L) (M := Wd L)
      (fun y hy b hb => (Subgroup.mem_centralizer_iff.mp (hcentLX hb)) y hy)
      hStableL_U l hl c hc
  have hStableX_cX : StableUnder (Lc L g) (commSub (Wd L) (Lc L g)) :=
    w1369_stableUnder_commSub_self hStableX_U
  have hStableL_C : StableUnder L (Cd L) := by
    intro l hl c hc
    exact ⟨hStableL_U l hl c hc.1, by rw [hc.2 l hl]; exact hc.2⟩
  have hStableX_C : StableUnder (Lc L g) (Cd L) := by
    intro x hx c hc
    refine ⟨hStableX_U x hx c hc.1, ?_⟩
    intro l hl
    have hxl : l * x = x * l := (Subgroup.mem_centralizer_iff.mp (hcentXL hx)) l hl
    calc l (x c) = (l * x) c := rfl
      _ = (x * l) c := by rw [hxl]
      _ = x (l c) := rfl
      _ = x c := by rw [hc.2 l hl]
  have hStableL_fixX : StableUnder L (fixV (Lc L g)) := by
    intro l hl c hc
    rw [mem_fixV]
    intro x hx
    have hxl : x * l = l * x := (Subgroup.mem_centralizer_iff.mp (hcentLX hl)) x hx
    calc x (l c) = (x * l) c := rfl
      _ = (l * x) c := by rw [hxl]
      _ = l (x c) := rfl
      _ = l c := by rw [mem_fixV.mp hc x hx]
  have hMB_eq : commSub (Wd L) (Lc L g) ⊔ Cd L = Wd L := by
    have hStableL_MB : StableUnder L (commSub (Wd L) (Lc L g) ⊔ Cd L) := by
      intro l hl m hm
      rcases Subgroup.mem_sup.mp hm with ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mem_sup.mpr
        ⟨l a, hStableL_cX l hl a ha, l b, hStableL_C l hl b hb, by rw [map_mul]⟩
    have hStableX_MB : StableUnder (Lc L g) (commSub (Wd L) (Lc L g) ⊔ Cd L) := by
      intro x hx m hm
      rcases Subgroup.mem_sup.mp hm with ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mem_sup.mpr
        ⟨x a, hStableX_cX x hx a ha, x b, hStableX_C x hx b hb, by rw [map_mul]⟩
    rcases hGL3.1 _ le_sup_right (sup_le (commSub_le_of_invariant hStableX_U) inf_le_left)
      hStableL_MB hStableX_MB with h | h
    · exact absurd (h ▸ le_sup_left) hntriv
    · exact h
  have hWd_le : Wd L ≤ commSub (Wd L) (Lc L g) := by
    calc Wd L = commSub (Wd L) L := (w1369_commSub_Wd_self hLp).symm
      _ = commSub (commSub (Wd L) (Lc L g) ⊔ Cd L) L := by rw [hMB_eq]
      _ = commSub (commSub (Wd L) (Lc L g)) L ⊔ commSub (Cd L) L :=
            commSub_sup_left _ _ _
      _ ≤ commSub (Wd L) (Lc L g) := by
            refine sup_le (commSub_le_of_invariant hStableL_cX) ?_
            have hbot : commSub (Cd L) L = ⊥ := commSub_eq_bot_iff.mpr inf_le_right
            rw [hbot]
            exact bot_le
  have hWdX : Wd (Lc L g) = Wd L := by
    have hle : Wd L ≤ Wd (Lc L g) := hWd_le.trans (commSub_mono le_top le_rfl)
    have hcard : Nat.card (Wd (Lc L g)) = Nat.card (Wd L) := by
      rw [swap_Wd L g,
        Subgroup.card_map_of_injective (f := g.toMonoidHom) (MulEquiv.injective g)]
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
  have hCdX_le_C : Cd (Lc L g) ≤ Cd L := by
    have hStableL_MC : StableUnder L (Cd L ⊔ (Wd L ⊓ fixV (Lc L g))) := by
      intro l hl m hm
      rcases Subgroup.mem_sup.mp hm with ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mem_sup.mpr
        ⟨l a, hStableL_C l hl a ha,
          l b, ⟨hStableL_U l hl b hb.1, hStableL_fixX l hl b hb.2⟩, by rw [map_mul]⟩
    have hcomm_MC : commSub (Cd L ⊔ (Wd L ⊓ fixV (Lc L g))) (Lc L g) ≤ Cd L := by
      rw [commSub_sup_left]
      refine sup_le (commSub_le_of_invariant hStableX_C) ?_
      have hbot : commSub (Wd L ⊓ fixV (Lc L g)) (Lc L g) = ⊥ :=
        commSub_eq_bot_iff.mpr inf_le_right
      rw [hbot]
      exact bot_le
    have hMC_eq : Cd L ⊔ (Wd L ⊓ fixV (Lc L g)) = Cd L := by
      by_contra hne
      exact hGL3.2.1 _ (lt_of_le_of_ne le_sup_left (Ne.symm hne))
        (sup_le inf_le_left inf_le_left) hStableL_MC hcomm_MC
    have h1 : Wd L ⊓ fixV (Lc L g) ≤ Cd L := hMC_eq ▸ le_sup_right
    change Wd (Lc L g) ⊓ fixV (Lc L g) ≤ Cd L
    rw [hWdX]
    exact h1
  have hC_le_fixX : Cd L ≤ fixV (Lc L g) := by
    obtain ⟨hctxX, hfixX⟩ := swap_ctx hw2 S
    have hStrong' : Strong3 (Lc L g) L := by
      rcases perfect_cent_dichotomy hw2 hctxX hfixX S.ctx.comp.1 hLp hcommLX with h | h
      · exfalso
        have hle : commSub (Wd (Lc L g)) L ≤ Cd (Lc L g) := w1369_commSub_le_iff.mpr h
        have hWdX_le : Wd (Lc L g) ≤ Cd (Lc L g) := by
          have h1 : Wd (Lc L g) = commSub (Wd (Lc L g)) L := by
            rw [hWdX]
            exact (w1369_commSub_Wd_self hLp).symm
          rw [h1]
          exact hle
        have hU_le_fix : Wd (Lc L g) ≤ fixV (Lc L g) := hWdX_le.trans inf_le_right
        have hbot : commSub (Wd (Lc L g)) (Lc L g) = ⊥ := by
          refine le_bot_iff.mp ?_
          calc commSub (Wd (Lc L g)) (Lc L g) ≤ commSub (fixV (Lc L g)) (Lc L g) :=
                commSub_mono hU_le_fix le_rfl
            _ = ⊥ := commSub_eq_bot_iff.mpr le_rfl
        have hbot' : commSub (Wd L) (Lc L g) = ⊥ := by rwa [hWdX] at hbot
        exact hntriv (hbot'.le.trans bot_le)
      · exact h
    have hGL3' : GL3Case (Lc L g) L (Wd (Lc L g)) (Cd (Lc L g)) := hStrong'.1
    have hStableX_CdX : StableUnder (Lc L g) (Cd (Lc L g)) := by
      intro x hx c hc
      refine ⟨?_, ?_⟩
      · change x c ∈ Wd (Lc L g)
        rw [hWdX]
        exact hStableX_U x hx c (hWdX ▸ hc.1)
      · exact mem_fixV.mpr fun y hy => by
          rw [hc.2 x hx]
          exact hc.2 y hy
    have hStableL_CdX : StableUnder L (Cd (Lc L g)) := by
      intro l hl c hc
      refine ⟨?_, hStableL_fixX l hl c hc.2⟩
      change l c ∈ Wd (Lc L g)
      rw [hWdX]
      exact hStableL_U l hl c (hWdX ▸ hc.1)
    have hStableX_M' : StableUnder (Lc L g)
        (Cd (Lc L g) ⊔ (Cd L ⊓ Wd (Lc L g))) := by
      intro x hx m hm
      rcases Subgroup.mem_sup.mp hm with ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mem_sup.mpr
        ⟨x a, hStableX_CdX x hx a ha,
          x b, ⟨hStableX_C x hx b hb.1, w1369_stableUnder_Wd (Lc L g) x hx b hb.2⟩,
          by rw [map_mul]⟩
    have hcomm_M'_L : commSub (Cd (Lc L g) ⊔ (Cd L ⊓ Wd (Lc L g))) L ≤ Cd (Lc L g) := by
      rw [commSub_sup_left]
      refine sup_le (commSub_le_of_invariant hStableL_CdX) ?_
      have hbot : commSub (Cd L ⊓ Wd (Lc L g)) L = ⊥ :=
        commSub_eq_bot_iff.mpr (inf_le_left.trans inf_le_right)
      rw [hbot]
      exact bot_le
    have hM'_eq : Cd (Lc L g) ⊔ (Cd L ⊓ Wd (Lc L g)) = Cd (Lc L g) := by
      by_contra hne
      exact hGL3'.2.1 _ (lt_of_le_of_ne le_sup_left (Ne.symm hne))
        (sup_le inf_le_left inf_le_right) hStableX_M' hcomm_M'_L
    have hC_le_CdX : Cd L ≤ Cd (Lc L g) := by
      have h1 : Cd L ⊓ Wd (Lc L g) ≤ Cd (Lc L g) := hM'_eq ▸ le_sup_right
      have h2 : Cd L ≤ Wd (Lc L g) := by
        change Cd L ≤ Wd (Lc L g)
        rw [hWdX]
        exact inf_le_left
      rwa [inf_eq_left.mpr h2] at h1
    exact hC_le_CdX.trans inf_le_right
  have hCd_bot : Cd L = ⊥ := by
    obtain ⟨x, hxX, hxodd, hxfix⟩ := hGL3.2.2.1
    have hfix_eq : Wd L ⊓ fixV (Subgroup.zpowers x) = Cd L := by
      apply le_antisymm
      · intro u hu
        have hxu : x u = u := mem_fixV.mp hu.2 x (Subgroup.mem_zpowers x)
        exact hxfix u hu.1 (by rw [hxu, mul_inv_cancel]; exact (Cd L).one_mem)
      · intro c hc
        exact ⟨hc.1, mem_fixV.mpr fun y hy =>
          hC_le_fixX hc y (Subgroup.zpowers_le.mpr hxX hy)⟩
    have hStable_zpU : StableUnder (Subgroup.zpowers x) (Wd L) :=
      fun y hy u hu => hStableX_U y (Subgroup.zpowers_le.mpr hxX hy) u hu
    have hcomm_zpL : ∀ y ∈ Subgroup.zpowers x, ∀ b ∈ L, y * b = b * y :=
      fun y hy b hb =>
        ((Subgroup.mem_centralizer_iff.mp (hcentXL (Subgroup.zpowers_le.mpr hxX hy))) b hb).symm
    have hStableL_R : StableUnder L (commSub (Wd L) (Subgroup.zpowers x)) := by
      intro l hl c hc
      exact CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := Subgroup.zpowers x) (B := L)
        (M := Wd L) hcomm_zpL hStableL_U l hl c hc
    obtain ⟨hsup, hinf⟩ := CFSG.Quasithin.B1.coprime_decomp hw2 (Y := Subgroup.zpowers x)
      (by rw [Nat.card_zpowers]; exact hxodd) hStable_zpU
    rw [hfix_eq] at hsup hinf
    have hU_le_R : Wd L ≤ commSub (Wd L) (Subgroup.zpowers x) := by
      calc Wd L = commSub (Wd L) L := (w1369_commSub_Wd_self hLp).symm
        _ = commSub (Cd L ⊔ commSub (Wd L) (Subgroup.zpowers x)) L := by rw [hsup]
        _ = commSub (Cd L) L ⊔ commSub (commSub (Wd L) (Subgroup.zpowers x)) L :=
              commSub_sup_left _ _ _
        _ ≤ commSub (Wd L) (Subgroup.zpowers x) := by
              refine sup_le ?_ (commSub_le_of_invariant hStableL_R)
              have hbot : commSub (Cd L) L = ⊥ := commSub_eq_bot_iff.mpr inf_le_right
              rw [hbot]
              exact bot_le
    have hR_eq : commSub (Wd L) (Subgroup.zpowers x) = Wd L :=
      le_antisymm (commSub_le_of_invariant hStable_zpU) hU_le_R
    rw [hR_eq] at hinf
    rwa [inf_eq_left.mpr inf_le_left] at hinf
  refine ⟨hWdX, hCd_bot, ?_, hStrong⟩
  exact le_bot_iff.mp (hCdX_le_C.trans hCd_bot.le)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
