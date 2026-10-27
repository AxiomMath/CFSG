module

public import CFSG.RankThree.PartTwo.Sec21.Item229
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)
open CFSG.Assembly (IsElemAbelian)
open Matrix

variable {G : Type} [Group G]

theorem item229_of_kOf_facts [Finite G] (h2130 : Item2130) (h2131 : Item2131One)
    (h222 : Item222) (h228 : Item228) (hKW : KOfWellDefinedAll) (h76 : CurtisTitsRankThree)
    (hR4 : Item229UnitaryRoots) (hZ : CentralExtensionTrivial229)
    (hLR : LocalRankLowerBound229) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    (hSL3 : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, orderOf (φ * ψ) = 3 → ∃ m : ℕ, 0 < m ∧ Even m ∧
      Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* SL3 m))
    (hcomm : ∀ f : Multiplicative (Fin 3 → ZMod 3) ≃* A, coordGL f '' dStar A = swapRefl →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ → ψ * φ = φ * ψ →
        ∀ x ∈ kOf A φ, ∀ y ∈ kOf A ψ, x * y = y * x) :
    (Nonempty (Subgroup.closure (dStar A) ≃* Equiv.Perm (Fin 4)) ∧
        Nonempty (iGroup A ≃* projSL 4 (GaloisField 2 2))) ∨
      (wStar A = Subgroup.closure (dStar A) ∧
        Nonempty (wStar A ≃* (ℤˣ × Equiv.Perm (Fin 4))) ∧
        Nonempty (iGroup A ≃* projSp 3 (GaloisField 2 2))) := by
  have hK := hKW G A E U c L hpair
  have hAI := le_iGroup h2130 h222 hpair hK
  have hG := hpair.standing.toTheoremFourHyp
  obtain ⟨f, hWf, himg⟩ := exists_coord_image_dStar h2131 h222 hpair hA27
  have hinj := coordGL_injective f
  have hmapcl : (Subgroup.closure (dStar A)).map (coordGL f) =
      Subgroup.closure (coordGL f '' dStar A) := MonoidHom.map_closure _ _
  have hloc : ∀ p : ℕ, p.Prime → 3 < p → 3 ≤ localRank p (iGroup A) → False :=
    fun p hp h3 hle => by
      have := (hle.trans (localRank_subgroup_le hp (iGroup A))).trans_lt
        (hG.localRank_lt p hp h3)
      omega
  rcases himg with hS | hM
  ·
    obtain ⟨t₁, h₁, t₂, h₂, t₃, h₃, h12, h23, hc13, hne13, -, hfuse, -, -, -⟩ :=
      exists_diagram_of_image_eq_swapRefl f hS
    have hne12 := ne_of_orderOf_mul_ne_one h₂ (by rw [h12]; norm_num)
    have hne23 := ne_of_orderOf_mul_ne_one h₃ (by rw [h23]; norm_num)
    have hIeq := iGroup_eq_sup_three h222 hpair hK h₁ h₂ h₃ fun φ hφ => by
      obtain ⟨g, hg, hgφ⟩ := hfuse φ hφ
      exact ⟨g, hg, t₁, by simp, hgφ⟩
    obtain ⟨m, hm0, hme, ⟨k₁⟩, ⟨k₂⟩, ⟨k₁₂⟩⟩ := hSL3 t₁ h₁ t₂ h₂ h12
    obtain ⟨m', hm'0, -, ⟨k₂'⟩, ⟨k₃⟩, ⟨k₂₃⟩⟩ := hSL3 t₂ h₂ t₃ h₃ h23
    have hmm : m' = m := eq_of_mulEquiv_projSL_two (by omega) (by omega) (k₂'.symm.trans k₂)
    subst hmm
    have hm2 : 2 ≤ m' := by obtain ⟨k, hk⟩ := hme; omega
    have hc := hcomm f hS t₁ h₁ t₃ h₃ hne13.symm hc13.symm
    have hinf := inf_eq_bot_of_commute k₁ hc
    have hch := isChainSystem_kOf h222 hpair hK h₁ h₂ h₃ hne12 hne13 hne23 (hIeq ▸ hAI) hc hinf
    have hX : (⨆ i, ![kOf A t₁, kOf A t₂, kOf A t₃] i) = kOf A t₁ ⊔ kOf A t₂ ⊔ kOf A t₃ := by
      rw [iSup_fin_three]
      rfl
    have hIX : iGroup A = ⨆ i, ![kOf A t₁, kOf A t₂, kOf A t₃] i := hIeq.trans hX.symm
    have hq := (h76 G A _ m' hm0 hme hch).1 (fun i => by
        fin_cases i
        · exact ⟨k₁⟩
        · exact ⟨k₂⟩
        · exact ⟨k₃⟩) (Or.inl ⟨k₁₂⟩) (Or.inl ⟨k₂₃⟩)
    obtain ⟨eq⟩ := hq
    have hc0 := center_eq_bot_of_sup hZ hX hm2 hm2 hm2 k₁ k₂ k₃ hm0 hme (Or.inl ⟨eq⟩)
    obtain ⟨eX⟩ := nonempty_mulEquiv_of_quotient_center hc0 eq
    have eI := (MulEquiv.subgroupCongr hIX).trans eX
    have hm22 : m' = 2 := by
      by_contra hne
      have h4 : 4 ≤ m' := by obtain ⟨k, hk⟩ := hme; omega
      obtain ⟨p, hp, hp3, hpl⟩ := hLR (iGroup A) m' hme (Or.inl ⟨h4, Or.inl ⟨eI⟩⟩)
      exact hloc p hp hp3 hpl
    subst hm22
    left
    refine ⟨?_, ⟨eI⟩⟩
    rw [hS] at hmapcl
    exact ⟨((Subgroup.closure (dStar A)).equivMapOfInjective _ hinj).trans
      ((MulEquiv.subgroupCongr hmapcl).trans swapReflEquiv)⟩
  ·
    obtain ⟨t₁, h₁, t₂, h₂, t₃, h₃, h12, h24, hc13, hne13, -, hfuse, hnconj, -, e₂M, e₃M⟩ :=
      exists_diagram_of_image_eq_monoRefl f hM
    have hne12 := ne_of_orderOf_mul_ne_one h₂ (by rw [h12]; norm_num)
    have hne23 := ne_of_orderOf_mul_ne_one h₃ (by rw [h24]; norm_num)
    have hIeq := iGroup_eq_sup_three h222 hpair hK h₁ h₂ h₃ fun φ hφ => by
      obtain ⟨g, hg, hgφ | hgφ⟩ := hfuse φ hφ
      · exact ⟨g, hg, t₁, by simp, hgφ⟩
      · exact ⟨g, hg, t₃, by simp, hgφ⟩
    obtain ⟨m, hm0, hme, ⟨k₁⟩, ⟨k₂⟩, ⟨k₁₂⟩⟩ := hSL3 t₁ h₁ t₂ h₂ h12
    have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hme; omega
    have hc := commute_kOf_of_not_conj h228 hpair hA27 h₁ h₃ hne13.symm hc13.symm
      fun w hw h => hnconj w (hWf ⟨w, hw, rfl⟩) h
    have hinf := inf_eq_bot_of_commute k₁ hc
    have hch := isChainSystem_kOf h222 hpair hK h₁ h₂ h₃ hne12 hne13 hne23 (hIeq ▸ hAI) hc hinf
    have hX : (⨆ i, ![kOf A t₁, kOf A t₂, kOf A t₃] i) = kOf A t₁ ⊔ kOf A t₂ ⊔ kOf A t₃ := by
      rw [iSup_fin_three]
      rfl
    have hIX : iGroup A = ⨆ i, ![kOf A t₁, kOf A t₂, kOf A t₃] i := hIeq.trans hX.symm
    rcases kOf_sup_cases_of_orderOf_eq_four h222 h228 hR4 hpair hA27 hK h₂ h₃ h24 hm0 hme k₂ with
      ⟨⟨k₂₃⟩, ⟨k₃⟩⟩ | ⟨⟨k₂₃⟩, ⟨k₃⟩⟩ | ⟨k, hk0, hke, rfl, ⟨k₂₃⟩, ⟨k₃⟩⟩
    ·
      have hq := (h76 G A _ m hm0 hme hch).2.1 (fun i => by
          fin_cases i
          · exact ⟨k₁⟩
          · exact ⟨k₂⟩
          · exact ⟨k₃⟩) (Or.inl ⟨k₁₂⟩) ⟨k₂₃⟩
      obtain ⟨eq⟩ := hq
      have hc0 := center_eq_bot_of_sup hZ hX hm2 hm2 hm2 k₁ k₂ k₃ hm0 hme
        (Or.inr (Or.inl ⟨eq⟩))
      obtain ⟨eX⟩ := nonempty_mulEquiv_of_quotient_center hc0 eq
      have eI := (MulEquiv.subgroupCongr hIX).trans eX
      have hm22 : m = 2 := by
        by_contra hne
        have h4 : 4 ≤ m := by obtain ⟨k, hk⟩ := hme; omega
        obtain ⟨p, hp, hp3, hpl⟩ := hLR (iGroup A) m hme (Or.inl ⟨h4, Or.inr ⟨eI⟩⟩)
        exact hloc p hp hp3 hpl
      subst hm22
      right
      rw [hM, closure_monoRefl] at hmapcl
      have hWD : wStar A ≤ Subgroup.closure (dStar A) := by
        rw [← Subgroup.map_le_map_iff_of_injective hinj, hmapcl]
        exact hWf
      have heq : wStar A = Subgroup.closure (dStar A) :=
        le_antisymm hWD (closure_dStar_le_wStar A)
      refine ⟨heq, ⟨((wStar A).equivMapOfInjective _ hinj).trans
        ((MulEquiv.subgroupCongr (by rw [heq, hmapcl])).trans monomialEquiv)⟩, ⟨eI⟩⟩
    ·
      exfalso
      have hst : ¬ A ⊓ kOf A t₂ ≤ Subgroup.centralizer (kOf A t₃ : Set G) :=
        not_inf_kOf_le_centralizer h222 hpair hK h₂ h₃
          (not_commOf_le_fixedSubgroupOf_of_coord f e₂M e₃M ![0, 1, 0] (by decide))
      have hq := (h76 G A _ m hm0 hme hch).2.2.1 ⟨k₁⟩ ⟨k₂⟩ ⟨k₃⟩ (Or.inl ⟨k₁₂⟩) ⟨k₂₃⟩ hst
      obtain ⟨b, c', hbc, ⟨eq⟩⟩ := hq
      have hc0 := center_eq_bot_of_sup hZ hX hm2 hm2 (by omega) k₁ k₂ k₃ hm0 hme
        (Or.inr (Or.inr (Or.inl ⟨b, c', hbc, ⟨eq⟩⟩)))
      obtain ⟨eX⟩ := nonempty_mulEquiv_of_quotient_center hc0 eq
      have eI := (MulEquiv.subgroupCongr hIX).trans eX
      obtain ⟨p, hp, hp3, hpl⟩ := hLR (iGroup A) m hme
        (Or.inr ⟨hm2, Or.inl ⟨b, c', hbc, ⟨eI⟩⟩⟩)
      exact hloc p hp hp3 hpl
    ·
      exfalso
      have hk2 : 2 ≤ k := by obtain ⟨j, hj⟩ := hke; omega
      have hst : ¬ A ⊓ kOf A t₃ ≤ Subgroup.centralizer (kOf A t₂ : Set G) :=
        not_inf_kOf_le_centralizer h222 hpair hK h₃ h₂
          (not_commOf_le_fixedSubgroupOf_of_coord f e₃M e₂M ![0, 0, 1] (by decide))
      have hq := (h76 G A _ k hk0 hke hch).2.2.2 ⟨k₁⟩ ⟨k₂⟩ ⟨k₃⟩ (Or.inl ⟨k₁₂⟩) ⟨k₂₃⟩ hst
      obtain ⟨eq⟩ := hq
      have hc0 := center_eq_bot_of_sup hZ hX hm2 hm2 hk2 k₁ k₂ k₃ hk0 hke
        (Or.inr (Or.inr (Or.inr ⟨eq⟩)))
      obtain ⟨eX⟩ := nonempty_mulEquiv_of_quotient_center hc0 eq
      have eI := (MulEquiv.subgroupCongr hIX).trans eX
      obtain ⟨p, hp, hp3, hpl⟩ := hLR (iGroup A) k hke (Or.inr ⟨hk2, Or.inr ⟨eI⟩⟩)
      exact hloc p hp hp3 hpl

end CFSG.RankThree.PartTwo.Sec21
