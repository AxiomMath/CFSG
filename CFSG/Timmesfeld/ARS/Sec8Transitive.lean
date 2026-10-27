module

public import CFSG.Timmesfeld.ARS.Sec8Omega
public import CFSG.Timmesfeld.ARS.Sec3PlaneGroup
public import CFSG.Timmesfeld.ARS.Sec8Basic
public import CFSG.Timmesfeld.ARS.Sec8Planes

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace OmegaGraph

variable (h : Hyp G R)
include h

theorem false_of_special {A B₀ B C : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hB₀ : B₀ ∈ omegaSet R A) (hC : C ∈ omegaSet R A)
    (hCΔ : C ∉ component R A B₀) (hB : B ∈ component R A B₀) (hBC : Special R B C) : False := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBΩ := mem_omegaSet_of_reflTransGen hB₀ hB
  have hBR : B ∈ R := hBΩ.1
  have hCR : C ∈ R := hC.1
  set D := ⁅B, C⁆ with hD
  have hDR : D ∈ R := hBC.1
  obtain ⟨hBDl, hCDl⟩ := mem_lambdaSet_commutator hR hiso hBR hCR hBC
  have hDBl : D ∈ lambdaSet R B := mem_lambdaSet_comm hDR hBDl
  have hDCl : D ∈ lambdaSet R C := mem_lambdaSet_comm hDR hCDl
  have hDA : Special R A D := by
    have hnc := not_commuting_of_opposite_of_mem_lambdaSet hR hA hBΩ.2 hDBl
    have hDΩ : D ∉ omegaSet R A := fun hDΩ =>
      hCΔ ((hB.tail ⟨hBΩ, hDΩ, hDBl⟩).tail ⟨hDΩ, hC, hCDl⟩)
    rcases hR.rel A hA D hDR (fun e => hnc (e ▸ hR.commuting_self hA)) with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ⟨hDR, ho⟩ hDΩ
    · exact hs
  obtain ⟨E, hER, hEDB, hline⟩ := exists_plane_of_sigmaSet_ne h hDR hBDl
    (sigmaSet_ne_lambdaSet_of_mem hR hA hDR hAne)
  obtain ⟨hNab, -, -, -, hcoll, -⟩ := plane hR hiso hER hDR hBDl hline
  obtain ⟨-, -, htrans⟩ := plane_transitive hR hiso hER hDR hBDl hline
  set N := E ⊔ D ⊔ B with hN
  have hEN : E ≤ N := le_sup_left.trans le_sup_left
  have hDN : D ≤ N := le_sup_right.trans le_sup_left
  have hBN : B ≤ N := le_sup_right
  have hEDl : E ∈ lambdaSet R D := mem_lambdaSet_comm hER (hline D hDR le_sup_left)
  have hEBl : E ∈ lambdaSet R B := mem_lambdaSet_comm hER (hline B hBR le_sup_right)
  obtain ⟨-, -, hcommD, -, hP2⟩ := Q_eq_M h hDR
  have hNM : N ≤ M R D := sup_le (sup_le (QD.le_M hEDl) QD.le_M_self) (QD.le_M hBDl)
  have hCM : C ≤ M R D := QD.le_M hCDl
  have hnopp : ∀ Q ∈ R, Q ≤ N → ¬ Opposite Q C := fun Q hQ hQN =>
    Sec3.not_opposite_of_isPGroup_sup hR hQ hCR (hP2.to_le (sup_le (hQN.trans hNM) hCM))
  have F1 : ∀ X ∈ omegaSet R A, X ∉ component R A B₀ → ∀ Q ∈ R, Q ≤ N → Commuting Q X →
      Special R A Q := by
    intro X hX hXΔ Q hQ hQN hQX
    have hQB : Q ≠ B := by
      rintro rfl
      exact hXΔ (mem_component_of_commuting h hA hB₀ hB hX hQX)
    have hQl : Q ∈ lambdaSet R B := hcoll B hBR hBN Q hQ hQN hQB.symm
    have hQΩ : Q ∉ omegaSet R A := fun hQΩ =>
      hXΔ (mem_component_of_commuting h hA hB₀ (hB.tail ⟨hBΩ, hQΩ, hQl⟩) hX hQX)
    have hnc := not_commuting_of_opposite_of_mem_lambdaSet hR hA hBΩ.2 hQl
    rcases hR.rel A hA Q hQ (fun e => hnc (e ▸ hR.commuting_self hA)) with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ⟨hQ, ho⟩ hQΩ
    · exact hs
  obtain ⟨P, hPR, hPN, hPL, hPC⟩ : ∃ P ∈ R, P ≤ N ∧ ¬ P ≤ B ⊔ D ∧ Commuting P C := by
    have hEL : ¬ E ≤ B ⊔ D := fun hle => hEDB (hle.trans (sup_comm B D).le)
    by_cases hEC : Commuting E C
    · exact ⟨E, hER, hEN, hEL, hEC⟩
    have hEB : E ≠ B := fun e => hEDB (e ▸ le_sup_right)
    have hECs : Special R E C := by
      rcases hR.rel E hER C hCR (fun e => hEC (e ▸ hR.commuting_self hER)) with hc | ho | hs
      · exact absurd hc hEC
      · exact absurd ho (hnopp E hER hEN)
      · exact hs
    have hECD : ⁅E, C⁆ = D :=
      QD.eq_of_le_of_mem hR hiso hECs.1 hDR (hcommD ▸ Subgroup.commutator_mono (hEN.trans hNM) hCM)
    obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
    obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
    have hbc : ⁅b, c⁆ ∈ D := Subgroup.commutator_mem_commutator hb hc
    obtain ⟨e, he, hec⟩ := (bijOn_commutator_left hR hiso hER hCR hECs hc hc1).surjOn
      (show ⁅b, c⁆⁻¹ ∈ ((⁅E, C⁆ : Subgroup G) : Set G) from hECD ▸ D.inv_mem hbc)
    have hec' : ⁅e, c⁆ = ⁅b, c⁆⁻¹ := hec
    have hecD : ⁅e, c⁆ ∈ D := by
      rw [hec']
      exact D.inv_mem hbc
    have hz : ⁅b * e, c⁆ = 1 := by
      rw [Plane.commutatorElement_mul_left_of_commute (hBDl.1.2.2 _ hecD b hb).symm, hec',
        inv_mul_cancel]
    have hz1 : b * e ≠ 1 := by
      intro h1
      have hbE : b ∈ B ⊓ E := ⟨hb, by rw [eq_inv_of_mul_eq_one_left h1]; exact E.inv_mem he⟩
      rw [inf_eq_bot hR hiso hBR hER hEB.symm, Subgroup.mem_bot] at hbE
      exact hb1 hbE
    obtain ⟨P, hPR, hPle, hzP⟩ := hEBl.2 (b * e)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right he)) hz1
    have hPN : P ≤ N := hPle.trans (sup_le hBN hEN)
    have hPC : Commuting P C := by
      have hPC' : P ≠ C := fun e =>
        Special.not_commuting hR hBC (hNab.mono hBN (e ▸ hPN))
      rcases hR.rel P hPR C hCR hPC' with hcm | ho | hs
      · exact hcm
      · exact absurd ho (hnopp P hPR hPN)
      · exfalso
        have := (bijOn_commutator_left hR hiso hPR hCR hs hc hc1).injOn hzP P.one_mem
          (by rw [hz, commutatorElement_one_left])
        exact hz1 this
    have hPB : P ≠ B := fun e => Special.not_commuting hR hBC (e ▸ hPC)
    refine ⟨P, hPR, hPN, fun hPBD => ?_, hPC⟩
    have h1 := (mem_lambdaSet_of_le_sup hR hiso hBR hDBl hBR le_sup_left hPR hPBD hPB.symm).2
    have h2 := (mem_lambdaSet_of_le_sup hR hiso hBR hEBl hBR le_sup_left hPR hPle hPB.symm).2
    exact hEL (le_sup_right.trans (h2.symm.le.trans h1.le))
  have hPB : P ≠ B := fun e => hPL (e ▸ le_sup_left)
  have hPBl : P ∈ lambdaSet R B := hcoll B hBR hBN P hPR hPN hPB.symm
  have hPψ : Special R A P := F1 C hC hCΔ P hPR hPN hPC
  obtain ⟨P', hP'R, hP'le, hP'P, hP'B⟩ := exists_mem_le_sup_ne_ne hR hiso hBR hPBl P B
  have hP'N : P' ≤ N := hP'le.trans (sup_le hBN hPN)
  have hcontra : ∀ X ∈ omegaSet R A, X ∉ component R A B₀ → Commuting P' X → False := by
    intro X hX hXΔ hP'X
    have hP'ψ := F1 X hX hXΔ P' hP'R hP'N hP'X
    obtain ⟨D', -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hBR hA hBΩ.2.symm hPBl
    exact hP'P ((huniq P' ⟨hP'R, hP'le, hP'R, hP'ψ⟩).trans
      (huniq P ⟨hPR, le_sup_right, hPR, hPψ⟩).symm)
  have hBD : B ≠ D := fun e => hDBl.1.2.1 e.symm
  obtain ⟨T, hTR, hT⟩ := htrans B hBR D hDR hBN hDN hBD
  obtain ⟨t, ht, hPt⟩ := hT.2.2.2 P hPR hPN hPL P' hP'R (hP'le.trans (sup_comm B P).le) hP'B
  have hTB : Commuting B T := hT.2.2.1.mono le_sup_left le_rfl
  have hTD : Commuting D T := hT.2.2.1.mono le_sup_right le_rfl
  by_cases hCT : Commuting C T
  · refine hcontra C hC hCΔ ?_
    rw [← hPt, ← conjSub_of_forall_commute fun x hx => (hCT x hx t ht).symm]
    exact hPC.conjSub t
  have hCTs : Special R C T := by
    rcases hR.rel C hCR T hTR (fun e => hCT (e ▸ hR.commuting_self hCR)) with hc | ho | hs
    · exact absurd hc hCT
    · exact absurd hTD.symm (not_commuting_of_opposite_of_mem_lambdaSet hR hTR ho.symm hDCl)
    · exact hs
  set C' := ⁅C, T⁆ with hC'
  have hC'R : C' ∈ R := hCTs.1
  have hC'l : C' ∈ lambdaSet R C :=
    mem_lambdaSet_comm hC'R (mem_lambdaSet_commutator hR hiso hCR hTR hCTs).1
  have hC'B : Commuting B C' := by
    rw [commuting_iff_commutator_eq_bot, Subgroup.commutator_comm]
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · have hTB' : ⁅T, B⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact commuting_iff_commutator_eq_bot.1 hTB
      rw [hTB', Subgroup.commutator_bot_left]
    · exact commuting_iff_commutator_eq_bot.1 hTD
  by_cases hC'Ω : C' ∈ omegaSet R A
  · exact hCΔ ((mem_component_of_commuting h hA hB₀ hB hC'Ω hC'B).tail
      ⟨hC'Ω, hC, mem_lambdaSet_comm hCR hC'l⟩)
  have hAC' : Special R A C' := by
    have hnc := not_commuting_of_opposite_of_mem_lambdaSet hR hA hC.2 hC'l
    rcases hR.rel A hA C' hC'R (fun e => hnc (e ▸ hR.commuting_self hA)) with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ⟨hC'R, ho⟩ hC'Ω
    · exact hs
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hP'P (hPt.symm.trans (conjSub_one P))
  set Ct := conjSub C t with hCt
  have hCtR : Ct ∈ R := hR.conjSub_mem hCR t
  have hCtl : Ct ∈ lambdaSet R C :=
    QD.conjSub_mem_lambdaSet_of_special hR hiso hTR hCR hCTs.symm ht ht1
  have hCtle : Ct ≤ C ⊔ C' := (conjSub_le_commutator_sup ht).trans (sup_comm _ _).le
  have hCtC' : Ct ≠ C' := by
    intro e
    apply Special.ne_commutator hR hCTs
    calc C = conjSub Ct t⁻¹ := by rw [hCt, ← conjSub_mul, inv_mul_cancel, conjSub_one]
      _ = C' := by
        rw [e]
        exact conjSub_of_forall_commute fun x hx => (hCTs.2.2 x hx t⁻¹ (T.inv_mem ht)).symm
  have hCtΩ : Ct ∈ omegaSet R A := by
    have hnc := not_commuting_of_opposite_of_mem_lambdaSet hR hA hC.2 hCtl
    obtain ⟨D', -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hCR hA hC.2.symm hC'l
    rcases hR.rel A hA Ct hCtR (fun e => hnc (e ▸ hR.commuting_self hA)) with hc | ho | hs
    · exact absurd hc hnc
    · exact ⟨hCtR, ho⟩
    · exact absurd ((huniq Ct ⟨hCtR, hCtle, hCtR, hs⟩).trans
        (huniq C' ⟨hC'R, le_sup_right, hC'R, hAC'⟩).symm) hCtC'
  have hCtΔ : Ct ∉ component R A B₀ := fun hCtΔ =>
    hCΔ (hCtΔ.tail ⟨hCtΩ, hC, mem_lambdaSet_comm hCR hCtl⟩)
  exact hcontra Ct hCtΩ hCtΔ (hPt ▸ hPC.conjSub t)

theorem mem_component_of_sigmaSet_ne {A B₀ C : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hB₀ : B₀ ∈ omegaSet R A) (hC : C ∈ omegaSet R A) :
    C ∈ component R A B₀ := by
  have := h.finite
  have hR := h.root
  by_contra hCΔ
  have hnsub : ¬ component R A B₀ ⊆ omegaSet R C := by
    intro hsub
    have hMC := M_le_stabSet h hC.1 (hsub Relation.ReflTransGen.refl)
    rw [component_eq_of_subset h hA hC.1 hB₀ hsub] at hMC
    have htop : (⊤ : Subgroup G) ≤ stabSet (component R A B₀) := by
      rw [← gen_lambdaSet_sup_eq_top h hA hC]
      exact sup_le ((gen_le fun X hX => QD.le_M hX).trans (M_le_stabSet h hA hB₀))
        (QD.le_M_self.trans hMC)
    obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hB₀.1 hA
    have hAΔ := conjSub_mem_of_mem_stabSet (htop (Subgroup.mem_top g))
      (Relation.ReflTransGen.refl : B₀ ∈ component R A B₀)
    rw [hg] at hAΔ
    exact (mem_omegaSet_of_reflTransGen hB₀ hAΔ).2.ne rfl
  obtain ⟨B, hB, hBC⟩ : ∃ B ∈ component R A B₀, Special R B C := by
    obtain ⟨B, hB, hBC⟩ := Set.not_subset.1 hnsub
    have hBΩ := mem_omegaSet_of_reflTransGen hB₀ hB
    have hne : B ≠ C := fun e => hCΔ (e ▸ hB)
    rcases hR.rel B hBΩ.1 C hC.1 hne with hc | ho | hs
    · exact absurd (mem_component_of_commuting h hA hB₀ hB hC hc) hCΔ
    · exact absurd ⟨hBΩ.1, ho.symm⟩ hBC
    · exact ⟨B, hB, hs⟩
  exact false_of_special h hA hAne hB₀ hC hCΔ hB hBC

end OmegaGraph

open OmegaGraph

theorem exists_mem_M_conjSub_eq_of_mem_omegaSet (h : Hyp G R) {A A₀ B : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hB : B ∈ omegaSet R A) : ∃ m ∈ M R A, conjSub A₀ m = B :=
  (mem_component_iff h hA hA₀).1 (mem_component_of_sigmaSet_ne h hA hAne hA₀ hB)

theorem existsUnique_conj_of_sigmaSet_ne (h : Hyp G R) {A A₀ B : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) (hB : B ∈ omegaSet R A) :
    ∃! m : ↥(M R A), conjSub A₀ m = B := by
  obtain ⟨m, hm, hmB⟩ := exists_mem_M_conjSub_eq_of_mem_omegaSet h hA hAne hA₀ hB
  refine ⟨⟨m, hm⟩, hmB, fun m' hm'B => ?_⟩
  have h1 : conjSub A₀ ((m : G)⁻¹ * m') = A₀ := by
    rw [conjSub_mul, hm'B, ← hmB, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have h2 := eq_one_of_mem_M_of_conjSub_eq h hA hA₀ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm)
    m'.2) h1
  exact Subtype.ext (inv_mul_eq_one.1 h2).symm

theorem existsUnique_conj_of_mem_omegaSet (h : Hyp G R) {A A₀ B : Subgroup G} (hA : A ∈ R)
    (h8 : Sec8 R A) (hA₀ : A₀ ∈ omegaSet R A) (hB : B ∈ omegaSet R A) :
    ∃! m : ↥(M R A), conjSub A₀ m = B :=
  existsUnique_conj_of_sigmaSet_ne h hA h8.2 hA₀ hB

end CFSG.Timmesfeld.ARS
