module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire16
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofRoute
public import CFSG.RankThree.PartTwo.Sec16.Item162ResProofOther
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofCover
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofConf
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162LPointA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ∀ (e : G) (Le : Subgroup G),
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e → MeetsY4 A (lB A) Le Y →
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A e →
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) →
        ∃ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A ∧ La ∈ lA A a ∧
          ∃ Y₀ ∈ scriptY0Star A (lB A), La ≤ Y₀

theorem step163Meets_of_point
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (h1411 : Item1411_1R) (hM : Step163MeetsPoint) : Step163Meets := by
  intro G _ _ A c L h Y hY hLY
  refine Res162.meetsY4_of_cover h h1514 h1523 h153 hobs h1411 hM hY ?_
  rw [inf_eq_right.mpr hLY, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]

namespace Res162d

theorem exists_point_le_of_mem
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h1411 : Item1411_1R) (h142 : Concl142R) (hU35 : Step163U35)
    (hM : Step163MeetsPoint) (hA7 : Step162LPointA7) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) :
    ∃ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A ∧ La ∈ lA A a ∧
      ∃ Y₀ ∈ scriptY0Star A (lB A), La ≤ Y₀ := by
  obtain ⟨e, Le, he, hLe, hm⟩ := exists_point_meetsY4 h (fun G _ _ A c' L' hR' _ =>
    h1514 G A c' L' hR') h1523 h153 hobs h1411 hM hY
  have he' : Sec15R G A e Le := sec15R_of_point h he hLe
  rcases h1514 G A e Le he' Y hY hm with ⟨-, -, hΩ, -⟩ | ⟨h7, hW, hT, hY'⟩ | h3
  · exact ⟨e, Le, he, hLe, Y, hY, le_of_omegaA_eq_singleton he' hΩ (h1514 G A e Le he') hU35
      (h142 G A e Le he') (h153 G A e Le he') (hobs G A e Le he') (h1411 G A e Le he') hY hm⟩
  · exact hA7 G A c L h Y hY e Le he hLe hm h7 hW hT hY'
  · exact (hU35 G A e Le he' Y hY hm h3).elim

end Res162d

open Proof162 Res162d in
theorem step162LR_of_point
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (hn : Claim153NormalR) (h1411 : Item1411_1R) (hWloc : Claim1411NonsolvWR)
    (h142 : Concl142R) (hU35 : Step163U35) (hM : Step163MeetsPoint) (hA7 : Step162LPointA7)
    (hO : Step162A7Other) : Step162LR := by
  intro G _ _ A c₀ L₀ _ c L hR Y₁ Y₂ S hmax
  have h153' := h153 G A c L hR
  have hobs' := hobs G A c L hR
  have hSG := mem_qStarTop_of_mem_qStarN h153' hobs' hmax.1.mem₁ hmax.1.s₁
  obtain ⟨a, La, ha, hLa, Y₀, hY₀, hLaY₀⟩ := exists_point_le_of_mem hR h1514 h1523 h153 hobs
    h1411 h142 hU35 hM hA7 hmax.1.mem₁
  obtain ⟨w, hw, hSw⟩ := exists_conj_mem_qStarN h153' hobs' (h1411 G A c L hR) hSG hY₀
  have hzc : Subgroup.zpowers (w * a * w⁻¹) =
      (Subgroup.zpowers a).map (MulAut.conj w).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hcΩ : Subgroup.zpowers (w * a * w⁻¹) ∈ omegaA A := by
    rw [hzc]
    exact (map_conj_mem_omegaA_iff hw).mpr ha
  have hLmem : La.map (MulAut.conj w).toMonoidHom ∈ lA A (w * a * w⁻¹) :=
    (map_conj_mem_lA_iff hw).mpr hLa
  have hR' : Sec15R G A (w * a * w⁻¹) (La.map (MulAut.conj w).toMonoidHom) :=
    sec15R_of_point hR hcΩ hLmem
  have hY₀w : Y₀.map (MulAut.conj w).toMonoidHom ∈ scriptY0Star A (lB A) :=
    map_conj_mem_scriptY0Star hw hY₀
  have hLY₀w : La.map (MulAut.conj w).toMonoidHom ≤ Y₀.map (MulAut.conj w).toMonoidHom :=
    Subgroup.map_mono hLaY₀
  have hpartner : ∃ Y₂' : Subgroup G, (Y₂' = Y₁ ∨ Y₂' = Y₂) ∧
      ¬ ∃ x ∈ xA A, Y₀.map (MulAut.conj w).toMonoidHom = Y₂'.map (MulAut.conj x).toMonoidHom := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x₁, hx₁, h₁⟩ := hcon Y₁ (Or.inl rfl)
    obtain ⟨x₂, hx₂, h₂⟩ := hcon Y₂ (Or.inr rfl)
    obtain ⟨y₁, hy₁, h₁'⟩ := conj_symm hx₁ h₁
    exact hmax.1.not_conj (conj_trans hy₁ hx₂ h₁' h₂)
  obtain ⟨Y₂', hY₂'eq, hnc'⟩ := hpartner
  have hY₂'mem : Y₂' ∈ scriptY0Star A (lB A) := by
    rcases hY₂'eq with rfl | rfl
    exacts [hmax.1.mem₁, hmax.1.mem₂]
  have hS₂' : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y₂' : Set G)) (piOf 2) := by
    rcases hY₂'eq with rfl | rfl
    exacts [hmax.1.s₁, hmax.1.s₂]
  have hmax' : MaxCE162 A (lB A) (Y₀.map (MulAut.conj w).toMonoidHom) Y₂' S S :=
    ⟨⟨hY₀w, hY₂'mem, hSw, hS₂', hmax.1.ne_bot, hnc'⟩, hmax.2⟩
  have hm₁ : MeetsY4 A (lB A) (La.map (MulAut.conj w).toMonoidHom)
      (Y₀.map (MulAut.conj w).toMonoidHom) :=
    step163Meets_of_point h1514 h1523 h153 hobs h1411 hM G A _ _ hR' _ hY₀w hLY₀w
  obtain ⟨f, Lf, hf, hLf, hmf⟩ := exists_point_meetsY4 hR' (fun G _ _ A c' L' hR'' _ =>
    h1514 G A c' L' hR'') h1523 h153 hobs h1411 hM hY₂'mem
  have hm₂ : MeetsY4 A (lB A) (La.map (MulAut.conj w).toMonoidHom) Y₂' := by
    by_cases hfc : Subgroup.zpowers f = Subgroup.zpowers (w * a * w⁻¹)
    · rwa [eq_of_zpowers_eq hR' hf hLf hfc] at hmf
    have hne : omegaA A ≠ {Subgroup.zpowers (w * a * w⁻¹)} := fun hΩ => hfc (by
      have := hΩ ▸ hf
      exact this)
    have hf' : Sec15R G A f Lf := sec15R_of_point hR' hf hLf
    have hne' : omegaA A ≠ {Subgroup.zpowers f} := fun hΩ => hfc (by
      have := hΩ ▸ hcΩ
      exact (Set.mem_singleton_iff.mp this).symm)
    rcases h1514 G A _ _ hR' _ hY₀w hm₁ with ⟨-, -, hΩ, -⟩ | ⟨h7, hW4, hT, hY⟩ |
        ⟨-, -, -, hΩ, -⟩
    · exact (hne hΩ).elim
    · rcases h1514 G A f Lf hf' Y₂' hY₂'mem hmf with ⟨-, -, hΩ', -⟩ | ⟨-, -, -, hY₂t⟩ |
          ⟨-, -, -, hΩ', -⟩
      · exact (hne' hΩ').elim
      · rcases hY₂t with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
        · exact (hO G A _ _ hR' _ Y₂' S hmax' hLY₀w hm₁ h7 hW4 hT hY
            (not_conj_normalizer hR' (h153 G A _ _ hR') (hobs G A _ _ hR') (hn G A _ _ hR')
              (hWloc G A _ _ hR') hmax'.1) f Lf hf hLf hfc hmf ⟨φ⟩
            (Res162.sectionCentralizer_eq_zpowers_of_meetsY4 hf' hY₂'mem hmf φ)).elim
        · exact Res162.meetsY4_of_alternating_ten hR' hT.1 hY₂'mem φ hf hLf hmf
      · exact (hne' hΩ').elim
    · exact (hne hΩ).elim
  exact ⟨w * a * w⁻¹, La.map (MulAut.conj w).toMonoidHom, Y₀.map (MulAut.conj w).toMonoidHom,
    Y₂', S, hcΩ, hLmem, hmax', hLY₀w, hm₁, hm₂⟩

end CFSG.RankThree.PartTwo.Sec16
