module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputK11
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDn
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDnBar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDnClassX
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDnParabolic
import CFSG.GroupTheory.AlternatingThreeRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

private theorem not_isQuasisimple_of_mulEquiv_alternatingGroup_of_le_four
    {X : Type*} [Group X] [Finite X] {n : ℕ} (hn : n ≤ 4)
    (e : X ≃* alternatingGroup (Fin n)) : ¬ CFSG.Open.IsQuasisimple X := by
  intro hq
  have hperm : Group.IsSolvable (Equiv.Perm (Fin n)) :=
    Equiv.Perm.isSolvable (α := Fin n) (by simpa using hn)
  haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
    Group.isSolvable_of_isSolvable_injective (f := (alternatingGroup (Fin n)).subtype)
      (Subgroup.subtype_injective _)
  haveI : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  haveI : Nontrivial (X ⧸ Subgroup.center X) := hq.2.toNontrivial
  haveI : Nontrivial X := (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := X)
  rw [hq.1] at hlt
  exact (lt_irrefl (⊤ : Subgroup X)) hlt

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem false_of_L3 (hNT : CFSG.AGLEmbedding.Asc81bNineThree) (hKF1 : L3NotEvenClassical)
    (hKF2 : L3EvenParabolic) (hK11 : K11) (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {N H S : Subgroup G}
    (hNIso : CFSG.Open.IsTwoLocal N) (hNM : ¬ N ≤ c.S.M) (hKN : t.Ky ≤ N) (hDH : t.Dn N ≤ H)
    (hHN : H ≤ N) (hHyp : CFSG.AGLEmbedding.Asc81bHyp H S)
    (hSM : Subgroup.normalizer (S : Set G) ≤ c.S.M)
    (hKS : t.Ky ≤ Subgroup.normalizer (S : Set G)) (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1)
    (hDM : ¬ t.Dn N ≤ c.S.M) (hO : t.On N ≤ c.S.M)
    (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N))
    (hL3 : (∃ ℓ f : ℕ, ℓ ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel (t.Dhat N) .PSL 3 ℓ f) ∨
      (∃ ℓ f : ℕ, ℓ ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel (t.Dhat N) .PSU 3 ℓ f)) : False := by
  classical
  haveI := c.standing.simple
  have hNtop : N ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top c.standing.nonab hNIso
  have hHtop : H ≠ ⊤ := fun h => hNtop (eq_top_iff.mpr (h ▸ hHN))
  have hK : CFSG.Open.IsKGroup ↥H := c.standing.kProper.isKGroup H hHtop
  have hWB : CFSG.AGLEmbedding.IsWeakSBlock H S (t.Dn N) :=
    t.isWeakSBlock_Dn hK32 hGA hSp hKN hDH hHN hrank hOc hSM hDM
  have hNT' : CFSG.AGLEmbedding.NineThreeConclusion H S (t.Dn N) :=
    hNT G H S (t.Dn N) hK hHyp hWB
  let X := ↥(CFSG.AGLEmbedding.barM H (t.Dn N))
  have hXq : CFSG.Open.IsQuasisimple X :=
    t.isQuasisimple_barM_Dn hK32 hGA hSp hKN hDH hHN hrank hOc
  obtain ⟨e⟩ := t.nonempty_barM_Dn_mulEquiv hK32 hGA hSp hKN hDH hHN hrank hOc
  have hnot3 := t.not_three_dvd_card_center_barM_Dn hK32 hGA hSp hKN hDH hrank
  have hcycX : ∀ P : Subgroup X, IsPGroup 3 P → IsCyclic ↥P :=
    fun P hP => t.isCyclic_of_isPGroup_barM_Dn hDH hrank hP
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hXq.2
  have hDsimple : IsSimpleGroup (t.Dhat N) := MulEquiv.isSimpleGroup e.symm
  have hDnonab : ∃ a b : t.Dhat N, a * b ≠ b * a :=
    t.exists_mul_ne_mul_Dhat hK32 hGA hSp hKN
  have hcycD : ∀ P : Subgroup (t.Dhat N), IsPGroup 3 P → IsCyclic ↥P :=
    fun P hP => t.isCyclic_of_isPGroup_Dhat hrank hP
  have hnotOrth : ¬ CFSG.AGLEmbedding.IsOrthogonalTwo X := by
    rcases hL3 with ⟨ℓ, f, hmod, hm⟩ | ⟨ℓ, f, hmod, hm⟩
    · exact (hKF1 X hXq ℓ f
        (Or.inl ⟨hmod, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩)).1
    · exact (hKF1 X hXq ℓ f
        (Or.inr ⟨hmod, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩)).1
  rcases hNT' with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hDM (t.Dn_le_of_inClassXBlock hK11 hK32 hGA hSp hp hN hZ hKN hrank hO h1)
  · rcases h2 with ⟨hclass, hpar, -⟩
    rcases hL3 with ⟨ℓ, f, hmod, hm⟩ | ⟨ℓ, f, hmod, hm⟩
    · by_cases hℓ : ℓ = 2
      · have hL3' : (∃ f : ℕ, 2 ^ f % 3 = 2 ∧
            CFSG.Blueprint.LieModel (t.Dhat N) .PSL 3 2 f) ∨
            (∃ f : ℕ, 2 ^ f % 3 = 1 ∧
              CFSG.Blueprint.LieModel (t.Dhat N) .PSU 3 2 f) :=
          Or.inl ⟨f, by simpa [hℓ] using hmod, by simpa [hℓ] using hm⟩
        exact t.false_of_parabolic hKF2 hK32 hGA hSp hNIso hNM hKN hO hDM
          (J := Subgroup.normalizer (S : Set G) ⊓ t.Dn N) inf_le_right
          (inf_le_left.trans hSM) (le_inf hKS (t.Ky_le_Dn hK32 hGA hSp hKN))
          (t.isParabolicTwo_Dhat_of_barM hK32 hGA hSp hKN hDH hHN hrank hOc
            (J := Subgroup.normalizer (S : Set G) ⊓ t.Dn N) inf_le_right hpar)
          hL3'
      · refine (hKF1 X hXq ℓ f ?_).2 hℓ hclass
        exact Or.inl ⟨hmod, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩
    · by_cases hℓ : ℓ = 2
      · have hL3' : (∃ f : ℕ, 2 ^ f % 3 = 2 ∧
            CFSG.Blueprint.LieModel (t.Dhat N) .PSL 3 2 f) ∨
            (∃ f : ℕ, 2 ^ f % 3 = 1 ∧
              CFSG.Blueprint.LieModel (t.Dhat N) .PSU 3 2 f) :=
          Or.inr ⟨f, by simpa [hℓ] using hmod, by simpa [hℓ] using hm⟩
        exact t.false_of_parabolic hKF2 hK32 hGA hSp hNIso hNM hKN hO hDM
          (J := Subgroup.normalizer (S : Set G) ⊓ t.Dn N) inf_le_right
          (inf_le_left.trans hSM) (le_inf hKS (t.Ky_le_Dn hK32 hGA hSp hKN))
          (t.isParabolicTwo_Dhat_of_barM hK32 hGA hSp hKN hDH hHN hrank hOc
            (J := Subgroup.normalizer (S : Set G) ⊓ t.Dn N) inf_le_right hpar)
          hL3'
      · refine (hKF1 X hXq ℓ f ?_).2 hℓ hclass
        exact Or.inr ⟨hmod, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩
  · rcases h3 with ⟨-, horth, -⟩
    exact hnotOrth horth
  · rcases h4 with ⟨-, hcard, -⟩
    exact hnot3 (by simpa [hcard] using (dvd_refl 3 : 3 ∣ 3))
  · rcases h5 with ⟨-, h5e, -⟩
    obtain ⟨e5⟩ := h5e
    obtain ⟨P, hP, hPc⟩ :=
      CFSG.GroupTheory.exists_isPGroup_three_not_isCyclic_of_mulEquiv_alternatingGroup
        (n := 7) (by norm_num) e5
    exact hPc (hcycX P hP)
  · rcases h6 with ⟨-, n, h6e, -⟩
    obtain ⟨e6⟩ := h6e
    have eD : t.Dhat N ≃* alternatingGroup (Fin (2 * n)) := e.symm.trans e6
    by_cases h2n : 6 ≤ 2 * n
    · obtain ⟨P, hP, hPc⟩ :=
        CFSG.GroupTheory.exists_isPGroup_three_not_isCyclic_of_mulEquiv_alternatingGroup h2n eD
      exact hPc (hcycD P hP)
    · exact CFSG.GroupTheory.false_of_isSimpleGroup_of_mulEquiv_alternatingGroup_of_le_four
        hDsimple hDnonab (by omega) eD
  · rcases h7 with ⟨-, n, h7e, -⟩
    obtain ⟨e7⟩ := h7e
    by_cases h4n : 8 ≤ 4 * n
    · obtain ⟨P, hP, hPc⟩ :=
        CFSG.GroupTheory.exists_isPGroup_three_not_isCyclic_of_mulEquiv_alternatingGroup
          (by omega) e7
      exact hPc (hcycX P hP)
    · exact not_isQuasisimple_of_mulEquiv_alternatingGroup_of_le_four (by omega) e7 hXq
  · obtain ⟨-, d, r, heven, h2r, hd0, hd2, hd4, ed, -⟩ := h8
    have hd6 : 6 ≤ d := by
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨ed'⟩ := ed
    obtain ⟨P, hP, hPc⟩ :=
      CFSG.GroupTheory.exists_isPGroup_three_not_isCyclic_of_mulEquiv_alternatingGroup hd6 ed'
    exact hPc (hcycX P hP)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
