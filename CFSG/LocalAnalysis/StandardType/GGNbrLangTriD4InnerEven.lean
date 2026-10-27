module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisCases
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
public import CFSG.LocalAnalysis.StandardType.GGTriD4InnerCompDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
import CFSG.LocalAnalysis.StandardType.GGNbrInnerElem
import CFSG.LocalAnalysis.StandardType.GGStdSubNotLinearTwo
import CFSG.LocalAnalysis.StandardType.GGStdSubLinearThree
import CFSG.LocalAnalysis.StandardType.GGNbrLangTriD4Core
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneProof
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.StandardType.GGNbrLangRegStepZero
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggNbrLangTriD4InnerEvenAux_labelAll_innerComp (hIC : GGTriD4InnerCompInput)
    {n : ℕ} (hn : 1 ≤ n) (hdiv : 3 ∣ 2 ^ n - 1) :
    LargeEvenLabelAll ⟨.triD4, 0, n⟩ (LargeEvenSimpleGuard fun R _ _ _ =>
      ∀ h : R, h ≠ 1 → h ^ 3 = 1 →
      ∀ Q : Subgroup R, IsComponentOf Q (Subgroup.centralizer ({h} : Set R)) →
        (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 3 ≤ m ∧ Nat.card E = 2 ^ m ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) ∨
        (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 2 ≤ m ∧ Nat.card E = 2 ^ m ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 3) E)))) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeTwisted_and (m := 3) (n := n)
    (P := LargeEvenSimpleGuard fun R _ _ _ =>
      ∀ h : R, h ≠ 1 → h ^ 3 = 1 →
      ∀ Q : Subgroup R, IsComponentOf Q (Subgroup.centralizer ({h} : Set R)) →
        (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 3 ≤ m ∧ Nat.card E = 2 ^ m ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) ∨
        (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 2 ≤ m ∧ Nat.card E = 2 ^ m ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 3) E))))
    (fun K _ _ hKcard _ _ => by
      intro h h1 h3 Q' hQ'
      rcases hIC n hn (Or.inr hdiv) K (by simpa using hKcard) h h1 h3 Q' hQ' with
        ⟨E, hEfield, hEfin, hEcard, he⟩ | ⟨h2, E, hEfield, hEfin, hEcard, he⟩
      · left
        refine ⟨E, hEfield, hEfin, 3 * n, by omega, ?_, he⟩
        exact hEcard.trans (by rw [mul_comm, pow_mul])
      · right
        exact ⟨E, hEfield, hEfin, n, h2, hEcard, he⟩) hQ

private theorem ggNbrLangTriD4InnerEvenAux_labelAll_combined (hKG : GGTriD4KnownInput)
    (hIC : GGTriD4InnerCompInput) (hT3 : KGLangAxisT3Input)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : lab.tag = .triD4 ∧ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      GGTriD4InnDiag R I ∧ GGTriD4Schur R ∧
      (∀ h : R, h ≠ 1 → h ^ 3 = 1 →
        ∀ Q : Subgroup R, IsComponentOf Q (Subgroup.centralizer ({h} : Set R)) →
          (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 3 ≤ m ∧ Nat.card E = 2 ^ m ∧
            Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
              LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) ∨
          (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 2 ≤ m ∧ Nat.card E = 2 ^ m ∧
            Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
              LargeEvenProj (LargeEvenSLGroup (Fin 3) E)))) ∧
      GGRawPCyclic 3 R I F ∧ KGLangAxisT3Cont R I F) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hdiv⟩ := hS
  have hl0 : l = 0 := by
    have := hlab.2
    rw [ht] at this
    exact this
  dsimp only at ht hl0
  subst ht; subst hl0
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  refine largeEvenRawDatum_mono (fun R _ I F h => ?_)
    ((largeEvenLabelAll_and (largeEvenLabelAll_triD4_known hKG hlab rfl)
      (largeEvenLabelAll_and
        (ggNbrLangTriD4InnerEvenAux_labelAll_innerComp hIC hn hdiv)
        (largeEvenLabelAll_and
          (ggRawPCyclicOn_excCyclic 3 Nat.prime_three (by norm_num) ⟨.triD4, 0, n⟩ hlab
            (Or.inr (Or.inl rfl)))
          (hT3 ⟨.triD4, 0, n⟩ hlab rfl hdiv)))) Q hQ)
  obtain ⟨hQ', hKGg, hICg, hPCg, hTg⟩ := h
  refine ⟨hQ', fun hs hna => ?_⟩
  obtain ⟨hInn, hSchur, -, -⟩ := hKGg hs hna
  exact ⟨hs, hna, hInn, hSchur, hICg hs hna, hPCg, hTg⟩

theorem ggNbrLangAxisInnerOn_t3Even (hsub : GGNbrSubcomponentInput) (hKG : GGTriD4KnownInput)
    (hLID : GGBstarInnerDiagLInputOn fun _ _ => True) (hQ1 : GGBstarInnerDiagJInput)
    (hQ2 : GGBstarAbelianPreimageJLinInput) (hT3 : KGLangAxisT3Input)
    (hIC : GGTriD4InnerCompInput) :
    GGNbrLangAxisInnerOn fun p lab => GGNbrLangT3Label p lab ∧ 3 ∣ 2 ^ lab.n - 1 := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN P hP
  have hKperf : commutator K = ⊤ := hP.1
  have hM1 := largeEvenMarking_and_labelAll_simple_imp
    (S := fun lab => lab.tag = .triD4 ∧ 3 ∣ 2 ^ lab.n - 1)
    (P' := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      GGTriD4InnDiag R I ∧ GGTriD4Schur R ∧
      (∀ h : R, h ≠ 1 → h ^ 3 = 1 →
        ∀ Q : Subgroup R, IsComponentOf Q (Subgroup.centralizer ({h} : Set R)) →
          (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 3 ≤ m ∧ Nat.card E = 2 ^ m ∧
            Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
              LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) ∨
          (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 2 ≤ m ∧ Nat.card E = 2 ^ m ∧
            Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
              LargeEvenProj (LargeEvenSLGroup (Fin 3) E)))) ∧
      GGRawPCyclic 3 R I F ∧ KGLangAxisT3Cont R I F)
    (fun lab hlab hS => ggNbrLangTriD4InnerEvenAux_labelAll_combined hKG hIC hT3 hlab hS) hP
  refine largeEvenMarking_mono ?_ hM1
  rintro lab R _ I F θ ⟨hPθ, hfacts⟩
  refine ⟨hPθ, ?_⟩
  rintro hlab hxin hall b₀ hb₀ hb₀I
  obtain ⟨hs_R, hna_R, hInn, hSchur, hICR, hPC, hKGR⟩ := hfacts ⟨hlab.1.1, hlab.2⟩
  have hp3 : p = 3 := hlab.1.2
  subst hp3
  have hcfgcopy := hcfg
  obtain ⟨hI, hBstar, hDJ⟩ := hcfg
  have hSStar : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hSStar.2.1
  have hxBs : x ∈ Bs := hBstar.1 hxB
  have hZ : Subgroup.center K = ⊥ := hSchur K hKperf θ
  have hinn : ∀ r : R, MulAut.conj r ∈ I := by
    intro r
    rw [hInn]
    exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : R, MulAut.conj r = ggLAut K θ ⟨x, hN hxBs⟩ := by
    have hxI : ggLAut K θ ⟨x, hN hxBs⟩ ∈ I := hxin hxBs
    rw [hInn] at hxI
    exact hxI
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hxK
    have hcomm : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left ((Subgroup.mem_centralizer_iff.mp hxK k hk).symm) m).eq
    exact hK.2.2.2 (by rw [hcomm]; exact bot_le)
  obtain ⟨h, hh, h1, hhBs⟩ := exists_conj_eq_ggBsAut_of_ggLAut_eq_conj hBstar.2.1
    hBstar.2.2.2 hN hKperf hZ θ hxBs hxK hr.symm
  have hJK : J ≤ K := hsub G 3 B x L D J hI hDJ y K hK
  have hJc := isComponentOf_inf_centralizer_of_ggNbr hSStar hDJ hK hJK
  have hJ₀ := isComponentOf_subgroupOf_centralizer_of_conj_eq hN hxBs hh hJc
  obtain ⟨B₀, hB₀, hcard, hb₀', hmem⟩ := exists_index_prime_of_raw_pcyclic Nat.prime_three
    hBstar.2.1 hs_R hna_R hPC ((ggLAut K θ).comp (Subgroup.inclusion hN)) hb₀ hb₀I
  refine ⟨B₀, hB₀, hcard, hb₀', fun b hb h => (hmem b hb).2 h, ?_⟩
  have hIDL : GGInnerDiagOnLab (fun _ _ => True) 3 B L :=
    ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hI
  have hIDL' : GGInnerDiagOnLab (fun _ _ => True) 3 Bs L :=
    hLID G 3 B Bs x L D J ⟨hI, hBstar, hDJ⟩ hIDL
  have hID : GGInnerDiagOn Bs L := hIDL'.innerDiagOn
  have hIDJ : GGInnerDiagOn Bs J := hQ1 G 3 B Bs x L D J hcfgcopy hID
  have hcases : (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 3 ≤ m ∧
      Nat.card E = 2 ^ m ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) ∨
    (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 2 ≤ m ∧ Nat.card E = 2 ^ m ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E))) := by
    obtain ⟨Q, e, hQ⟩ := exists_component_fixed_of_centerless θ hZ (hN hxBs) hJc
    have hfix : ggAutFixedSubgroup (ggLAut K θ ⟨x, hN hxBs⟩) =
        Subgroup.centralizer ({r} : Set R) := by
      rw [← hr]
      ext y
      simp only [ggAutFixedSubgroup, Set.mem_setOf_eq, Subgroup.mem_centralizer_singleton_iff,
        MulAut.conj_apply]
      constructor
      · intro h
        calc y * r = r * y * r⁻¹ * r := by rw [h]
          _ = r * y := by group
      · intro h
        calc r * y * r⁻¹ = y * r * r⁻¹ := by rw [h]
          _ = y := by group
    have hQr : IsComponentOf Q (Subgroup.centralizer ({r} : Set R)) := hfix ▸ hQ
    have hx3 : x ^ 3 = 1 := hBstar.2.1.2 x hxBs
    have hσ3 : ggLAut K θ ⟨x, hN hxBs⟩ ^ 3 = 1 :=
      ggLAut_pow_eq_one_of_pow K θ (hN hxBs) hx3
    have hr3 : r ^ 3 = 1 := by
      have hconj : MulAut.conj (r ^ 3) = MulAut.conj (1 : R) := by
        rw [map_one, map_pow, hr]
        exact hσ3
      exact NbrLangRest.conj_injective_of_simple hs_R hna_R hconj
    have hr1 : r ≠ 1 := by
      rintro rfl
      exact hxK (mem_centralizer_of_ggLAut_eq_one K θ hKperf (g := ⟨x, hN hxBs⟩)
        (by rw [← hr, map_one]))
    rcases hICR r hr1 hr3 Q hQr with
      ⟨E, hEfield, hEfin, m, hm, hEcard, heQ⟩ | ⟨E, hEfield, hEfin, m, hm, hEcard, heQ⟩
    · left
      letI : Field E := hEfield
      letI : Finite E := hEfin
      obtain ⟨eQ⟩ := heQ
      let eJQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥Q ⧸ Subgroup.center ↥Q) :=
        QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
      exact ⟨E, hEfield, hEfin, m, hm, hEcard, ⟨eJQ.trans eQ⟩⟩
    · right
      letI : Field E := hEfield
      letI : Finite E := hEfin
      obtain ⟨eQ⟩ := heQ
      let eJQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥Q ⧸ Subgroup.center ↥Q) :=
        QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
      exact ⟨E, hEfield, hEfin, m, hm, hEcard, ⟨eJQ.trans eQ⟩⟩
  rcases hcases with ⟨E, _, _, m, hm, hE, ⟨σ⟩⟩ | ⟨E, _, _, m, hm, hE, ⟨σ⟩⟩
  · exact (ggConfig_false_of_innerDiagOn_psl_two hcfgcopy hIDJ hm hE σ).elim
  · obtain ⟨E', _, _, θJ, At, hAt, hAtJ⟩ :=
      ggConfig_exists_abelianPreimage_psl_three hcfgcopy hID hQ2 hIDJ hm hE σ
    exact ggNbrLangTriD4Core_of_hyperplane hBstar.2.1 hN hKperf θ hinn hKGR hall b₀ hb₀ hb₀I
      hB₀ hmem h1 hhBs ⟨⟨x, hxBs⟩, hh.symm⟩ hJK hJ₀ θJ hAt hAtJ

end CFSG.StandardType
