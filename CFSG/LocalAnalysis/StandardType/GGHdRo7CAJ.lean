module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

import CFSG.Quasithin.EmptyFaithful.S146zMListCl
import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7CAJAux_weylMatrix_nonempty {ι : Type} {M : CoxeterMatrix ι}
    (h : GGIsWeylMatrix M) : Nonempty ι := by
  rcases h with ⟨n, e, hn, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact ⟨e ⟨0, by omega⟩⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩

private theorem hdRo7CAJAux_refl_ne_one {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {φ : MulAut ↥Bs} (hφ : GGIsReflection p φ) : φ ≠ 1 := by
  intro h
  rw [GGIsReflection] at hφ
  obtain ⟨-, hcard⟩ := hφ
  have hfix : Nat.card {b : ↥Bs // φ b = b} = Nat.card ↥Bs :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun b => by rw [h]; simp)
  have hcard' : Nat.card ↥Bs * p = Nat.card ↥Bs := by
    rwa [hfix] at hcard
  have hpos : 0 < Nat.card ↥Bs := by
    haveI : Nonempty ↥Bs := ⟨1, Bs.one_mem⟩
    exact Nat.card_pos
  have hp1 : p = 1 := by
    have h' : Nat.card ↥Bs * p = Nat.card ↥Bs * 1 := by simpa using hcard'
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  exact (Fact.out : p.Prime).ne_one hp1

private theorem hdRo7CAJAux_iso_not_bc {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (hbc : lab.tag = .B ∨ lab.tag = .C)
    (hbc' : ¬ (lab'.tag = .B ∨ lab'.tag = .C)) : False := by
  rcases h with h | ⟨h1, h2, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
  · have : lab'.tag = .B ∨ lab'.tag = .C := by rw [← h]; exact hbc
    exact hbc' this
  · exact hbc' h2
  · rw [h1] at hbc; exact absurd hbc (by simp)
  · rw [h1] at hbc; exact absurd hbc (by simp)
  · rw [h1] at hbc; exact absurd hbc (by simp)
  · rw [h1] at hbc; exact absurd hbc (by simp)
  · rw [h1] at hbc; exact absurd hbc (by simp)
  · rw [h2] at hbc; exact absurd hbc (by simp)

private theorem hdRo7CAJAux_nonLevi_not_bc {p : ℕ} {J X : LargeEvenLabel}
    (h : ggRowNonLevi p J X) : ¬ (X.tag = .B ∨ X.tag = .C) := by
  rcases h with h | h | h | h | h | h
  · rcases h with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ <;>
      rw [hX] <;> simp
  · rcases h with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ <;> rw [hX] <;> simp
  · rcases h with ⟨-, -, hX⟩ | ⟨-, -, hX⟩ <;> rw [hX] <;> simp
  · obtain ⟨-, -, -, hX⟩ := h; rw [hX]; simp
  · rcases h.2 with hX | hX | hX | hX | hX <;> rw [hX] <;> simp
  · rw [h.2.2.2.1]; simp

private theorem hdRo7CAJAux_three_dvd_quotient {X : Type} [Group X] [Finite X]
    (tag : LargeEvenLieTag) (r n : ℕ)
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨tag, r, n⟩
      (fun R _ _ _ => Nonempty (X ≃* R)))
    (htag : tag = .B ∨ tag = .C) (hn : n = 1) (hr : 1 ≤ r) :
    3 ∣ Nat.card X := by
  rcases htag with hB | hC
  · subst hB
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeSymplectic] at h
    obtain ⟨K, hf, hfin, hK, ⟨e⟩⟩ := h
    have e' : X ≃* LargeEvenProj (LargeEvenSpGroup K r) := by simpa using e
    rw [Nat.card_congr e'.toEquiv]
    rw [largeEvenProj_eq_statedProj, largeEvenSpGroup_eq_statedSp]
    exact CFSG.Quasithin.three_dvd_card_psp hr
  · subst hC
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeSymplectic] at h
    obtain ⟨K, hf, hfin, hK, ⟨e⟩⟩ := h
    have e' : X ≃* LargeEvenProj (LargeEvenSpGroup K r) := by simpa using e
    rw [Nat.card_congr e'.toEquiv]
    rw [largeEvenProj_eq_statedProj, largeEvenSpGroup_eq_statedSp]
    exact CFSG.Quasithin.three_dvd_card_psp hr

theorem c2_aj_holds : C2AJLeaf := by
  intro hX hJ hRig hLB G _ _ p B Bs x L D J y K hH hfact hrow
  haveI : Fact p.Prime := hfact
  obtain ⟨labJ, labL, hΛJ, hΛL, hJlab, hLlab, hrowBC⟩ := hrow
  have hp3 : p = 3 := hrowBC.1
  have hBCJ : labJ.tag = .B ∨ labJ.tag = .C := hrowBC.2.1
  have hnJ : labJ.n = 1 := hrowBC.2.2.1
  have hBCL : labL.tag = .B ∨ labL.tag = .C := hrowBC.2.2.2.1
  have hJL : J ≤ L := by
    have hPre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
    exact hPre.2.2.2.2.2.1.1.trans inf_le_left
  have hrJ : 1 ≤ labJ.rank := by
    have h2 : 2 ≤ labJ.rank := by
      simp only [LargeEvenInLambda2] at hΛJ
      rcases hBCJ with hB | hC
      · rw [hB] at hΛJ; exact hΛJ.2.1
      · rw [hC] at hΛJ; exact hΛJ.2.1
    omega
  have h3Q : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    hdRo7CAJAux_three_dvd_quotient labJ.tag labJ.rank labJ.n hJlab hBCJ hnJ hrJ
  have h3J : 3 ∣ Nat.card ↥J :=
    h3Q.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))
  have hpJ : p ∣ Nat.card J := by rw [hp3]; exact h3J
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1
  constructor
  · have hXdat : GGResXDatum p Bs L := by
      rcases (hX G p B Bs x L D J y K hH).1 with hD | h7
      · exact hD
      · exfalso
        obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
        omega
    have hJD : GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J ∨
        GGResRowAt ggRowNonLevi p J L := (hJ G p B Bs x L D J y K hH).1 hXdat
    rcases hJD with hSD | hLE3 | hNL
    · obtain ⟨Λ, _, _, b, M, _, MJ, V, _, _, ι, φ, h, α, _, _, hMJ, _, _, hrefl, _, _, _, _, hgenJ,
        _⟩ := hSD
      haveI : Nonempty {j : Λ // j ≠ b} := hdRo7CAJAux_weylMatrix_nonempty hMJ
      let j0 : {j : Λ // j ≠ b} := Classical.choice (inferInstance : Nonempty _)
      have hmem : φ ↑j0 ∈ Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ ↑j) :=
        Subgroup.subset_closure (Set.mem_range_self j0)
      rw [← hgenJ] at hmem
      intro hbot
      have hbotmem : φ ↑j0 ∈ (⊥ : Subgroup (MulAut ↥Bs)) := by
        rw [← hbot]; exact hmem
      exact (hdRo7CAJAux_refl_ne_one (hrefl ↑j0)) (Subgroup.mem_bot.mp hbotmem)
    · obtain ⟨Λ, _, _, S, M, _, MJ, V, _, _, ι, φ, h, α, _, _, _, _, hMJ, _, _, hrefl, _, _, _, _,
        hgenJ, _⟩ := hLE3
      haveI : Nonempty {j : Λ // j ∉ S} := hdRo7CAJAux_weylMatrix_nonempty hMJ
      let j0 : {j : Λ // j ∉ S} := Classical.choice (inferInstance : Nonempty _)
      have hmem : φ ↑j0 ∈ Subgroup.closure (Set.range fun j : {j : Λ // j ∉ S} => φ ↑j) :=
        Subgroup.subset_closure (Set.mem_range_self j0)
      rw [← hgenJ] at hmem
      intro hbot
      have hbotmem : φ ↑j0 ∈ (⊥ : Subgroup (MulAut ↥Bs)) := by
        rw [← hbot]; exact hmem
      exact (hdRo7CAJAux_refl_ne_one (hrefl ↑j0)) (Subgroup.mem_bot.mp hbotmem)
    · exfalso
      obtain ⟨labJ', labL', hΛJ', hΛL', hJlab', hLlab', hnl⟩ := hNL
      have hIso : GGLabelIso labL labL' :=
        hRig labL labL' (↥L ⧸ Subgroup.center ↥L) hΛL hΛL' hLlab hLlab'
      exact hdRo7CAJAux_iso_not_bc hIso hBCL (hdRo7CAJAux_nonLevi_not_bc hnl)
  · exact le_inf (ggAutomizer_mono Bs hJL) (ggAutomizer_mono Bs hJK)

end CFSG.StandardType.HdRo7C
