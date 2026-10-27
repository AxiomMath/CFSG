module

public import CFSG.Timmesfeld.ARS.Sec8Natural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem mem_lambdaStar_of_mem_lambdaSet [Finite G] (hR : IsRootClass R) {A A₀ E B : Subgroup G}
    (hA₀ : A₀ ∈ omegaSet R A) (hE : E ∈ leviSet R A A₀) (hBA : B ∈ lambdaSet R A)
    (hBE : B ∈ lambdaSet R E) : B ∈ lambdaStar R A A₀ := by
  have hBR : B ∈ R := hBA.1.1
  have hnc := not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hBA
  refine ⟨hBA, hBR, ?_⟩
  rcases hR.rel A₀ hA₀.1 B hBR (fun e => hnc (e ▸ hR.commuting_self hA₀.1)) with hc | ho | hs
  · exact absurd hc hnc
  · exact absurd hE.2.2.2
      (not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 ho (mem_lambdaSet_comm hE.1.1 hBE))
  · exact hs

section Projection

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hA₀

omit hAne in
theorem sup_inf_levi_eq_of_mem_leviSet {B : Subgroup G} (hB : B ∈ leviSet R A A₀) :
    (M R A ⊔ B) ⊓ levi R A A₀ = B := by
  have := h.finite
  have hR := h.root
  have hBN : B ≤ Subgroup.normalizer ((M R A : Subgroup G) : Set G) :=
    QD.le_normalizer_M hR hA ⟨hB.1.1, hB.1.2.2⟩
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right (le_gen hB))
  have hx1 : x ∈ ((M R A ⊔ B : Subgroup G) : Set G) := hx.1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN] at hx1
  obtain ⟨m, hm, b, hb, rfl⟩ := hx1
  have hmV : m ∈ M R A ⊓ levi R A A₀ := by
    refine ⟨hm, ?_⟩
    have := (levi R A A₀).mul_mem hx.2 ((levi R A A₀).inv_mem (le_gen hB hb))
    rwa [mul_inv_cancel_right] at this
  rw [M_inf_levi_eq_bot h hA hA₀, Subgroup.mem_bot] at hmV
  show m * b ∈ B
  rw [hmV, one_mul]
  exact hb

theorem sup_inf_levi_mem_leviSet {B : Subgroup G} (hBs : B ∈ sigmaSet R A)
    (hBl : B ∉ lambdaSet R A) :
    (M R A ⊔ B) ⊓ levi R A A₀ ∈ leviSet R A A₀ ∧
      (∃ m ∈ M R A, conjSub B m = (M R A ⊔ B) ⊓ levi R A A₀) ∧
      M R A ⊔ (M R A ⊔ B) ⊓ levi R A A₀ = M R A ⊔ B := by
  obtain ⟨m, hm, hBm⟩ := exists_mem_M_conjSub_mem_leviSet h hA hAne hA₀ hBs hBl
  have hsup : M R A ⊔ conjSub B m = M R A ⊔ B := by
    refine le_antisymm (sup_le le_sup_left (conjSub_le le_sup_right (Subgroup.mem_sup_left hm)))
      (sup_le le_sup_left ?_)
    calc B = conjSub (conjSub B m) m⁻¹ := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
      _ ≤ M R A ⊔ conjSub B m :=
        conjSub_le le_sup_right (Subgroup.mem_sup_left (Subgroup.inv_mem _ hm))
  have heq : (M R A ⊔ B) ⊓ levi R A A₀ = conjSub B m := by
    rw [← hsup, sup_inf_levi_eq_of_mem_leviSet h hA hA₀ hBm]
  rw [heq]
  exact ⟨hBm, ⟨m, hm, rfl⟩, hsup⟩

theorem exists_mem_M_conjSub_eq_of_sup_eq {E F : Subgroup G} (hEs : E ∈ sigmaSet R A)
    (hEl : E ∉ lambdaSet R A) (hFs : F ∈ sigmaSet R A) (hFl : F ∉ lambdaSet R A)
    (hEF : M R A ⊔ E = M R A ⊔ F) : ∃ m ∈ M R A, conjSub E m = F := by
  obtain ⟨-, ⟨m₁, hm₁, hE₁⟩, -⟩ := sup_inf_levi_mem_leviSet h hA hAne hA₀ hEs hEl
  obtain ⟨-, ⟨m₂, hm₂, hF₂⟩, -⟩ := sup_inf_levi_mem_leviSet h hA hAne hA₀ hFs hFl
  rw [hEF, ← hF₂] at hE₁
  refine ⟨m₂⁻¹ * m₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hm₂) hm₁, ?_⟩
  rw [conjSub_mul, hE₁, ← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem coveredBy_sup_inf_levi {T : Subgroup G}
    (hTA : T ≤ Subgroup.centralizer (A : Set G)) (hT : CoveredBy R T) (hTM : T ⊓ M R A = ⊥) :
    (∀ x ∈ (M R A ⊔ T) ⊓ levi R A A₀, x ≠ 1 →
      ∃ B ∈ leviSet R A A₀, B ≤ (M R A ⊔ T) ⊓ levi R A A₀ ∧ x ∈ B) ∧
      M R A ⊔ (M R A ⊔ T) ⊓ levi R A A₀ = M R A ⊔ T := by
  have := h.finite
  have hR := h.root
  have hTN : T ≤ Subgroup.normalizer ((M R A : Subgroup G) : Set G) := by
    refine le_normalizer_of_conjSub_le fun g hg => le_of_eq ?_
    exact (isPGroup_M hR hA).2.2 g ((Subgroup.centralizer_le_normalizer _) (hTA hg))
  have hpt : ∀ B ∈ R, B ≤ T → B ∈ sigmaSet R A ∧ B ∉ lambdaSet R A := by
    intro B hB hBT
    have hBM : ¬ B ≤ M R A := fun hle => hR.ne_bot B hB (le_bot_iff.1 (hTM ▸ le_inf hBT hle))
    refine ⟨⟨hB, fun e => hBM (e ▸ QD.le_M_self), (commuting_iff_le_centralizer.2
      (hBT.trans hTA)).symm.symm⟩, fun hBl => hBM (QD.le_M hBl)⟩
  refine ⟨fun x hx hx1 => ?_, le_antisymm (sup_le le_sup_left (inf_le_left)) ?_⟩
  · have hx' : x ∈ ((M R A ⊔ T : Subgroup G) : Set G) := hx.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTN] at hx'
    obtain ⟨m, hm, y, hy, rfl⟩ := hx'
    have hy1 : y ≠ 1 := by
      rintro rfl
      have hmV : m ∈ M R A ⊓ levi R A A₀ := ⟨hm, by simpa using hx.2⟩
      rw [M_inf_levi_eq_bot h hA hA₀, Subgroup.mem_bot] at hmV
      exact hx1 (by simp [hmV])
    obtain ⟨B, hB, hBT, hyB⟩ := hT y hy hy1
    obtain ⟨hBs, hBl⟩ := hpt B hB hBT
    obtain ⟨hB', -, -⟩ := sup_inf_levi_mem_leviSet h hA hAne hA₀ hBs hBl
    refine ⟨_, hB', inf_le_inf_right _ (sup_le_sup_left hBT _), ⟨?_, hx.2⟩⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hyB)
  · refine sup_le le_sup_left fun y hy => ?_
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Subgroup.one_mem _
    obtain ⟨B, hB, hBT, hyB⟩ := hT y hy hy1
    obtain ⟨hBs, hBl⟩ := hpt B hB hBT
    obtain ⟨-, -, hsup⟩ := sup_inf_levi_mem_leviSet h hA hAne hA₀ hBs hBl
    have : B ≤ M R A ⊔ (M R A ⊔ T) ⊓ levi R A A₀ :=
      le_sup_right.trans (hsup.symm.le.trans (sup_le_sup_left
        (inf_le_inf_right _ (sup_le_sup_left hBT _)) _))
    exact this hyB

theorem exists_commutator_eq_of_mem_lambdaStar {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hBC : B ∈ lambdaSet R C) :
    ∃ D ∈ leviSet R A A₀, ⁅B, D⁆ = C := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hA
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  have hCBl : C ∈ lambdaSet R B := mem_lambdaSet_comm hCR hBC
  have huniq : ∀ {X Y : Subgroup G}, X ∈ lambdaStar R A A₀ → Y ∈ lambdaStar R A A₀ →
      Y ≤ A ⊔ X → Y = X := fun {X Y} hX hY hYle => by
    obtain ⟨D', -, hu⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hX.1
    exact (hu Y ⟨hY.1.1.1, hYle, hY.2⟩).trans (hu X ⟨hX.1.1.1, le_sup_right, hX.2⟩).symm
  have hBC' : B ≠ C := hBC.1.2.1
  have hline : ∀ X ∈ R, X ≤ B ⊔ C → X ∈ lambdaSet R A := by
    intro X hX hXle
    have hmem : X ∈ {Y | Y ∈ R ∧ Y ≤ M R A} :=
      ⟨hX, hXle.trans (sup_le (QD.le_M hB.1) (QD.le_M hC.1))⟩
    rw [(Q_eq_M h hA).2.1] at hmem
    refine hmem.resolve_left fun e => ?_
    rw [e] at hXle
    have h1 := (mem_lambdaSet_of_le_sup hR hiso hBR hCBl hBR le_sup_left hA hXle
      hB.1.1.2.1).2
    exact hBC' (huniq hB hC (le_sup_right.trans (h1.symm.le.trans (sup_comm B A).le))).symm
  obtain ⟨-, -, -, -, hcoll, -⟩ := plane hR hiso hA hBR hCBl hline
  obtain ⟨-, -, htrans⟩ := plane_transitive hR hiso hA hBR hCBl hline
  set N := A ⊔ B ⊔ C with hN
  have hAN : A ≤ N := le_sup_left.trans le_sup_left
  have hBN : B ≤ N := le_sup_right.trans le_sup_left
  have hCN : C ≤ N := le_sup_right
  have hCA : C ≠ A := hC.1.1.2.1
  have hBL : ¬ B ≤ C ⊔ A := fun hle => hBC' (huniq hC hB (hle.trans (sup_comm C A).le))
  obtain ⟨T, hTR, hT⟩ := htrans C hCR A hA hCN hAN hCA
  have hTA : Commuting A T := hT.2.2.1.mono le_sup_right le_rfl
  obtain ⟨P', hP'R, hP'le, hP'B, hP'C⟩ := exists_mem_le_sup_ne_ne hR hiso hBR hCBl B C
  obtain ⟨t, ht, hBt⟩ := hT.2.2.2 B hBR hBN hBL P' hP'R hP'le hP'C
  have htB : conjSub B t ≠ B := hBt ▸ hP'B
  have hTne : T ≠ A := by
    intro e
    rw [e] at ht
    exact htB (conjSub_of_forall_commute fun x hx => hB.1.1.2.2 t ht x hx)
  have hNM : N ≤ M R A := sup_le (sup_le QD.le_M_self (QD.le_M hB.1)) (QD.le_M hC.1)
  have hTnl : T ∉ lambdaSet R A := by
    intro hTl
    refine htB (conjSub_of_forall_commute fun x hx => ?_)
    have h1 : ⁅x, t⁆ ∈ A ⊓ C :=
      ⟨hcommA ▸ Subgroup.commutator_mem_commutator (hNM (hBN hx)) (QD.le_M hTl ht),
        hT.2.1 t ht x (hBN hx)⟩
    rw [inf_eq_bot hR hiso hA hCR hCA.symm, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  obtain ⟨m, hm, hTm⟩ := exists_mem_M_conjSub_mem_leviSet h hA hAne hA₀ ⟨hTR, hTne, hTA⟩ hTnl
  set D := conjSub T m with hD
  have hDR : D ∈ R := hTm.1.1
  have hMnorm : ∀ {X : Subgroup G}, A ≤ X → X ≤ M R A → conjSub X m = X := fun hAX hXM =>
    conjSub_eq_self_iff.2 (le_normalizer_of_commutator_le hXM (hcommA.le.trans hAX) hm)
  have hDel := hT.conj hR (hMnorm hAN hNM)
  rw [hMnorm (X := C ⊔ A) le_sup_right (sup_le (QD.le_M hC.1) QD.le_M_self)] at hDel
  have hDA : Commuting A D := hDel.2.2.1.mono le_sup_right le_rfl
  have hCmle : conjSub C m ≤ A ⊔ C := by
    rw [← hMnorm (X := A ⊔ C) le_sup_left (sup_le QD.le_M_self (QD.le_M hC.1))]
    exact Subgroup.map_mono le_sup_right
  have hCmR : conjSub C m ∈ R := hR.conjSub_mem hCR m
  have hBCm : B ≠ conjSub C m := fun e => hBL ((e ▸ hCmle).trans (sup_comm A C).le)
  have hCmBl : conjSub C m ∈ lambdaSet R B :=
    hcoll B hBR hBN _ hCmR (hCmle.trans (sup_le hAN hCN)) hBCm
  obtain ⟨P'', hP''R, hP''le, hP''B, hP''C⟩ :=
    exists_mem_le_sup_ne_ne hR hiso hBR hCmBl B (conjSub C m)
  obtain ⟨d, hd, hBd⟩ := hDel.2.2.2 B hBR hBN hBL P'' hP''R hP''le hP''C
  have hBD : ¬ Commuting B D := fun hc =>
    hP''B (hBd ▸ conjSub_of_forall_commute fun x hx => (hc x hx d hd).symm)
  have hBDs : Special R B D := by
    rcases hR.rel B hBR D hDR (fun e => hBD (e ▸ hR.commuting_self hBR)) with hc | ho | hs
    · exact absurd hc hBD
    · exact absurd hDA.symm (not_commuting_of_opposite_of_mem_lambdaSet hR hDR ho.symm
        (mem_lambdaSet_comm hA hB.1))
    · exact hs
  have hWle : ⁅B, D⁆ ≤ A ⊔ C := by
    refine le_trans ?_ hCmle
    rw [Subgroup.commutator_le]
    exact fun b hb d hd => hDel.2.1 d hd b (hBN hb)
  have hWst := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hTm hB hBDs).1 _ hBDs.1
    le_sup_right
  exact ⟨D, hTm, huniq hC hWst hWle⟩

end Projection

end CFSG.Timmesfeld.ARS
