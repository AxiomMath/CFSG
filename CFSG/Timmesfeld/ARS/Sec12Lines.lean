module

public import CFSG.Timmesfeld.ARS.Sec12Inter
public import CFSG.Timmesfeld.ARS.Sec13Commuting
public import CFSG.Timmesfeld.ARS.Sec8HypDegenLevi

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem deltaSet_inter_nonempty {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hBC : Commuting B C) :
    (deltaSet R A A₀ B ∩ deltaSet R A A₀ C).Nonempty := by
  by_cases he : B = C
  · subst he
    rw [Set.inter_self]
    exact deltaSet_nonempty hS.hyp hS.mem hS.sec8.2 hS.opp hB
  by_cases hCB : C ∈ lambdaSet R B
  · exact hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hC hCB
  · exact deltaSet_inter_nonempty_of_notMem_lambdaSet hS.hyp hS.mem hS.sec8 hS.opp hB hC hBC he
      hCB

theorem deltaSet_inter_inter_nonempty {B P P' : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPB : P ∈ lambdaSet R B)
    (hP'B : P' ∈ lambdaSet R B) :
    (deltaSet R A A₀ B ∩ deltaSet R A A₀ P ∩ deltaSet R A A₀ P').Nonempty := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hBR : B ∈ R := hB.1.1.1
  have hPR : P ∈ R := hP.1.1.1
  by_cases hP'le : P' ≤ B ⊔ P
  ·
    obtain ⟨Y, hYB, hYP⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hP hPB
    have h1 : Commuting Y (B ⊔ P) := Commuting.sup_right hYB.2.1.2.2.symm hYP.2.1.2.2.symm
    exact ⟨Y, ⟨hYB, hYP⟩, hS.mem_deltaSet_of_commuting hP' hYB.1 (h1.mono le_rfl hP'le).symm⟩
  have hPP'ne : P ≠ P' := fun e => hP'le (e ▸ le_sup_right)
  have hPP' : Commuting P P' := by
    rcases commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hBR hPB hP'B hPP'ne with
      hc | ⟨-, hc⟩
    · exact hc
    · exfalso
      have hle : B ≤ A := by
        rw [← hc, ← (Q_eq_M hS.hyp hA).2.2.1]
        exact Subgroup.commutator_mono (QD.le_M hP.1) (QD.le_M hP'.1)
      exact hB.1.1.2.1 (QD.eq_of_le_of_mem hR hiso hBR hA hle)
  obtain ⟨Z, hZP, hZP'⟩ := hS.deltaSet_inter_nonempty hP hP' hPP'
  refine ⟨Z, ⟨?_, hZP⟩, hZP'⟩
  rcases hS.mem_deltaSet_or_special hB hZP.1 with hZB | hs
  · exact hZB
  exfalso
  have hZR : Z ∈ R := hZP.1.1.1
  obtain ⟨hK, hKB, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB hZP.1 hs
  obtain ⟨z, hz, hz1⟩ := hR.exists_ne_one hZR
  have hBz : conjSub B z ≠ B := Sec3.conjSub_ne_of_special hR hiso hZR hBR hs.symm hz hz1
  have hBzle : conjSub B z ≤ B ⊔ ⁅B, Z⁆ :=
    (conjSub_le_commutator_sup (A := B) hz).trans (sup_comm _ _).le
  have hsupK : B ⊔ conjSub B z = B ⊔ ⁅B, Z⁆ :=
    (mem_lambdaSet_of_le_sup hR hiso hBR hKB hBR le_sup_left (hR.conjSub_mem hBR z) hBzle
      hBz.symm).2
  have key : ∀ {Q : Subgroup G}, Q ∈ lambdaStar R A A₀ → Q ∈ lambdaSet R B →
      Z ∈ deltaSet R A A₀ Q → B ⊔ Q = B ⊔ ⁅B, Z⁆ := by
    intro Q hQ hQB hZQ
    have hQR : Q ∈ R := hQ.1.1.1
    have hQz : conjSub Q z = Q := conjSub_of_forall_commute fun q hq =>
      (hZQ.2.1.2.2 q hq z hz).symm
    have hBQ : B ∈ lambdaSet R Q := mem_lambdaSet_comm hBR hQB
    have hBzQ : conjSub B z ∈ lambdaSet R Q := by
      have := conjSub_mem_lambdaSet hR hBQ z
      rwa [hQz] at this
    have hKM : ⁅B, Z⁆ ≤ M R Q := le_sup_right.trans
      (hsupK.symm.le.trans (sup_le (QD.le_M hBQ) (QD.le_M hBzQ)))
    by_cases hKQ : ⁅B, Z⁆ = Q
    · rw [hKQ]
    have hKQl : ⁅B, Z⁆ ∈ lambdaSet R Q :=
      mem_lambdaSet_of_le_M_of_hyp hS.hyp hQR hK.1.1.1 hKM hKQ
    have hKle : ⁅B, Z⁆ ≤ B ⊔ Q := hS.le_sup_of_mem_lambdaSet hB hQ hK hQB hKB hKQl
    exact (mem_lambdaSet_of_le_sup hR hiso hBR hQB hBR le_sup_left hK.1.1.1 hKle
      hKB.1.2.1.symm).2.symm
  have h1 := key hP hPB hZP
  have h2 := key hP' hP'B hZP'
  exact hP'le (le_sup_right.trans (h2.trans h1.symm).le)

theorem exists_ne_mem_deltaSet_inter {B C Y : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hCB : C ∈ lambdaSet R B)
    (hY : Y ∈ deltaSet R A A₀ B ∩ deltaSet R A A₀ C) :
    ∃ Y' ∈ deltaSet R A A₀ B ∩ deltaSet R A A₀ C, Y' ≠ Y := by
  have hR := hS.hyp.root
  obtain ⟨X, hX, hYX⟩ := Levi.exists_opposite_mem_leviSet hS.hyp hS.mem hS.sec8.2 hS.opp hY.1.1
  have hYne : Y ≠ ⊥ := hR.ne_bot Y hY.1.1.1.1
  have hXB : X ∉ deltaSet R A A₀ B := fun h =>
    hYX.not_commuting hYne (hS.commuting_of_mem_deltaSet' hB hY.1 h)
  have hs : Special R B X := (hS.mem_deltaSet_or_special hB hX).resolve_left hXB
  obtain ⟨hP, hPB, -⟩ := commutator_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hB hX hs
  have hYP : Y ∉ deltaSet R A A₀ ⁅B, X⁆ := fun h =>
    hYX.not_commuting hYne ((hS.commuting_iff_mem_deltaSet_commutator hB hX hs hY.1).2 h)
  obtain ⟨Y', ⟨hY'B, hY'C⟩, hY'P⟩ := hS.deltaSet_inter_inter_nonempty hB hC hP hCB hPB
  exact ⟨Y', ⟨hY'B, hY'C⟩, fun e => hYP (e ▸ hY'P)⟩

theorem mem_lambdaSet_of_commuting_of_not {B C E F D : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) (hBC : B ≠ C)
    (hE : E ∈ deltaSet R A A₀ B ∩ deltaSet R A A₀ C)
    (hF : F ∈ deltaSet R A A₀ B ∩ deltaSet R A A₀ C) (hD : D ∈ leviSet R A A₀)
    (hFD : Commuting F D) (hED : ¬ Commuting E D) : C ∈ lambdaSet R B := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  have hFR : F ∈ R := hF.1.1.1.1
  have hBCc : Commuting B C := by
    by_contra hnc
    obtain ⟨hs, -⟩ :=
      (commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hA hB.1 hC.1 hBC).resolve_left hnc
    have h0 := hS.deltaSet_inter_eq_empty_of_special hB hC hs
    rw [Set.eq_empty_iff_forall_notMem] at h0
    exact h0 E hE
  by_contra hCB
  have hDB : D ∉ deltaSet R A A₀ B := fun h =>
    hED (hS.commuting_of_mem_deltaSet' hB hE.1 h)
  have hs : Special R B D := (hS.mem_deltaSet_or_special hB hD).resolve_left hDB
  obtain ⟨hP, hPB, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB hD hs
  have hPR : ⁅B, D⁆ ∈ R := hP.1.1.1
  have hFP : F ∈ deltaSet R A A₀ ⁅B, D⁆ :=
    (hS.commuting_iff_mem_deltaSet_commutator hB hD hs hF.1).1 hFD
  have hEP : E ∉ deltaSet R A A₀ ⁅B, D⁆ := fun h =>
    hED ((hS.commuting_iff_mem_deltaSet_commutator hB hD hs hE.1).2 h)
  have hPC : Commuting ⁅B, D⁆ C := by
    rw [commuting_iff_commutator_eq_bot, eq_bot_iff,
      ← inf_eq_bot hR hiso hFR hA hF.1.1.1.2.1]
    refine le_inf ?_ ?_
    · rw [← (Q_eq_M hS.hyp hFR).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hPR hFP.2))
        (QD.le_M (mem_lambdaSet_comm hCR hF.2.2))
    · rw [← (Q_eq_M hS.hyp hA).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M hP.1) (QD.le_M hC.1)
  obtain ⟨B₀, hB₀R, hBB₀⟩ := hiso B hBR
  have hB₀ : B₀ ∈ omegaSet R B := ⟨hB₀R, hBB₀⟩
  have hS' := hS.of_mem_omegaSet hBR hB₀
  obtain ⟨m, hm, hCm⟩ := exists_mem_M_conjSub_mem_leviSet hS.hyp hBR hS'.sec8.2 hB₀
    ⟨hCR, hBC.symm, hBCc⟩ hCB
  obtain ⟨P', ⟨hP'R, hP'le, hP'ψ⟩, -⟩ :=
    existsUnique_mem_psiSet_of_le hR hiso hBR hB₀R hBB₀ hPB
  have hP'B : P' ≠ B := by
    rintro rfl
    exact Special.not_opposite hR hB₀R hP'ψ.2 hBB₀.symm
  have hBPM : B ⊔ ⁅B, D⁆ ≤ M R B := sup_le QD.le_M_self (QD.le_M hPB)
  have hP'l : P' ∈ lambdaStar R B B₀ :=
    ⟨mem_lambdaSet_of_le_M_of_hyp hS.hyp hBR hP'R (hP'le.trans hBPM) hP'B, hP'ψ⟩
  have hnorm : ∀ {g : G}, g ∈ M R B → conjSub (B ⊔ ⁅B, D⁆) g = B ⊔ ⁅B, D⁆ := fun hg =>
    conjSub_eq_self_iff.2 (le_normalizer_of_commutator_le hBPM
      ((Q_eq_M hS.hyp hBR).2.2.1.le.trans le_sup_left) hg)
  have hCmP' : Commuting P' (conjSub C m) := by
    have h1 : Commuting (B ⊔ ⁅B, D⁆) C := (Commuting.sup_right hBCc.symm hPC.symm).symm
    have h2 := h1.conjSub m
    rw [hnorm hm] at h2
    exact h2.mono hP'le le_rfl
  have hP'Cm : P' ∈ lambdaSet R (conjSub C m) := hS'.mem_lambdaSet_of_commuting hP'l hCm hCmP'
  have hminv : m⁻¹ ∈ M R B := (M R B).inv_mem hm
  have hLC : conjSub P' m⁻¹ ∈ lambdaSet R C := by
    have := conjSub_mem_lambdaSet hR hP'Cm m⁻¹
    rwa [Plane.conjSub_conjSub_inv] at this
  have hLle : conjSub P' m⁻¹ ≤ B ⊔ ⁅B, D⁆ := by
    rw [← hnorm hminv]
    exact Subgroup.map_mono hP'le
  have hmB : conjSub B m⁻¹ = B := conjSub_eq_self_iff.2 ((isPGroup_M hR hBR).2.1 hminv)
  have hLB : conjSub P' m⁻¹ ≠ B := fun e => hP'B (by
    calc P' = conjSub (conjSub P' m⁻¹) m⁻¹⁻¹ := (Plane.conjSub_conjSub_inv P' m⁻¹).symm
      _ = conjSub B m⁻¹⁻¹ := by rw [e]
      _ = B := by rw [inv_inv]; exact conjSub_eq_self_iff.2 ((isPGroup_M hR hBR).2.1 hm))
  have hLR : conjSub P' m⁻¹ ∈ R := hR.conjSub_mem hP'R m⁻¹
  have hLBl : conjSub P' m⁻¹ ∈ lambdaSet R B :=
    mem_lambdaSet_of_le_M_of_hyp hS.hyp hBR hLR (hLle.trans hBPM) hLB
  have hEL : ¬ Commuting E (conjSub P' m⁻¹) := by
    intro hc
    have hsup : B ⊔ conjSub P' m⁻¹ = B ⊔ ⁅B, D⁆ :=
      (mem_lambdaSet_of_le_sup hR hiso hBR hPB hBR le_sup_left hLR hLle hLB.symm).2
    have h1 : Commuting E (B ⊔ ⁅B, D⁆) := hsup ▸ Commuting.sup_right hE.1.2.1.2.2.symm hc
    exact hEP (hS.mem_deltaSet_of_commuting hP hE.1.1 (h1.mono le_rfl le_sup_right).symm)
  apply hEL
  rw [commuting_iff_commutator_eq_bot, eq_bot_iff, ← inf_eq_bot hR hiso hBR hCR hBC]
  refine le_inf ?_ ?_
  · rw [← (Q_eq_M hS.hyp hBR).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hE.1.2) (QD.le_M hLBl)
  · rw [← (Q_eq_M hS.hyp hCR).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hE.2.2) (QD.le_M hLC)

theorem mem_lambdaSet_of_mem_deltaSet_inter {B C E F : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) (hBC : B ≠ C)
    (hE : E ∈ deltaSet R A A₀ B ∩ deltaSet R A A₀ C)
    (hF : F ∈ deltaSet R A A₀ B ∩ deltaSet R A A₀ C) (hEF : E ≠ F) : C ∈ lambdaSet R B := by
  obtain ⟨D, hD, hDiff⟩ : ∃ D ∈ leviSet R A A₀, ¬ (Commuting E D ↔ Commuting F D) := by
    by_contra hc
    push Not at hc
    exact hEF (Levi.eq_of_commuting_iff_of_mem_leviSet' hS.hyp hS.mem hS.sec8.2 hS.opp hE.1.1
      hF.1.1 hc)
  by_cases hED : Commuting E D
  · exact hS.mem_lambdaSet_of_commuting_of_not hB hC hBC hF hE hD hED
      fun h => hDiff ⟨fun _ => h, fun _ => hED⟩
  · exact hS.mem_lambdaSet_of_commuting_of_not hB hC hBC hE hF hD
      (by by_contra h; exact hDiff ⟨fun h' => absurd h' hED, fun h' => absurd h' h⟩) hED

end Sec12

end CFSG.Timmesfeld.ARS
