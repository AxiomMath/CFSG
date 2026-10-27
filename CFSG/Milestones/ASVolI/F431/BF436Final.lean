module

public import CFSG.Milestones.ASVolI.F431.J3
public import CFSG.Milestones.ASVolI.F431.BF436U4C
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F436

set_option linter.unusedSectionVars false


@[expose] def burnsideF4m_F436U5 : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    ∀ hyp : HypF_4_31 .U5 f Gp M₁ M₂ β ε z, f = 1 →
    let chart := hyp.amalgam.toHypF_4_4g.chart
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
    ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb → chart.IsGraphInv (fb : E) →
      ¬ IsConj z (bM β ε fb)

theorem burnsideF4m_F_4_36_U4 :
    ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
      (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
      ∀ hyp : HypF_4_31 .U4 f Gp M₁ M₂ β ε z, f = 1 →
      let chart := hyp.amalgam.toHypF_4_4g.chart
      ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
      ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb → chart.IsGraphInv (fb : E) →
        ¬ IsConj z (bM β ε fb) := by
  intro f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hf1 chart Tb hTb fb hfbT hgraph hconj
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hclosed, hloc⟩ := burnsideF4m_f436Input_U4 hyp.amalgam hf1
  obtain ⟨r, hrT, ⟨g, hg⟩, hcases⟩ := hloc Tb hTb (fb : E) hfbT hgraph
  have hrM : r ∈ M₁ ⊓ M₂ := hTb.1 hrT
  set rr : ↥(M₁ ⊓ M₂) := ⟨r, hrM⟩ with hrr
  obtain ⟨h, hh⟩ := as_F_4_30 .U4 f E Gp M₁ M₂ hyp.amalgam Tb hTb Y β hyp.faithful {fb} {rr}
    (by rintro u rfl; exact hfbT) (by rintro u rfl; exact hrT) ⟨g, by
      rw [Set.image_singleton, Set.image_singleton, Set.image_singleton, hg]⟩
  rw [Set.image_singleton, Set.image_singleton, Set.image_singleton] at hh
  have hh' : h * bmap β fb * h⁻¹ = bmap β rr := Set.singleton_eq_singleton_iff.1 hh
  have hfr : IsConj (bM β ε fb) (bM β ε rr) := by
    refine isConj_iff.2 ⟨epsG β ε h, ?_⟩
    show epsG β ε h * epsG β ε (bmap β fb) * (epsG β ε h)⁻¹ = epsG β ε (bmap β rr)
    rw [← hh', map_mul, map_mul, map_inv]
  obtain ⟨y, hy⟩ := isConj_iff.1 (hconj.trans hfr)
  set H : Subgroup M := conjSub y (MiOne β ε) with hHdef
  have hCH : Subgroup.centralizer ({bM β ε rr} : Set M) ≤ H := by
    rw [← hy, burnsideF4j_centralizer_conj]
    exact conjSub_mono y hyp.hb
  have hb1 := burnsideF4j_bOne_injective hyp
  have hb2 := burnsideF4j_bTwo_injective hyp
  have hHcl : IsSylowTwoOf (pCoreOf 2 (oTwoRes H)) (oTwoRes H) := by
    have h0 : IsSylowTwoOf (pCoreOf 2 (oTwoRes (MiOne β ε))) (oTwoRes (MiOne β ε)) := by
      rw [burnsideF4d_MiOne_eq, burnsideF4j_oTwoRes_subImg _ hb1 le_rfl,
        subImg_pCoreOf hb1 (oTwoRes_le M₁)]
      exact (burnsideF4j_isSylow_subImg_iff _ hb1
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (oTwoRes_le M₁)) (oTwoRes_le M₁)).2
        hclosed
    have e1 : oTwoRes H = conjSub y (oTwoRes (MiOne β ε)) := by
      simp only [hHdef, conjSub]
      exact burnsideF4j_oTwoRes_map _ (MulAut.conj y).injective _
    have e2 : pCoreOf 2 (oTwoRes H) = conjSub y (pCoreOf 2 (oTwoRes (MiOne β ε))) := by
      rw [e1]
      exact burnsideF4j_pCoreOf_map _ (MulAut.conj y).injective _
    rw [e2, e1]
    exact F7.isSylowTwoOf_conj h0 y
  have hX1 : subImg (burnsideF4d_bOne β ε) (cenIn (Gp ⊓ M₁) r) ≤ H := by
    refine (burnsideF4j_subImg_cenIn_le _ _ hrM.1).trans ?_
    have e : burnsideF4d_bOne β ε ⟨r, hrM.1⟩ = bM β ε rr := (burnsideF4j_bM_eq_bOne β ε rr).symm
    rw [e]
    exact hCH
  have hX2 : subImg (burnsideF4d_bTwo β ε) (cenIn (Gp ⊓ M₂) r) ≤ H := by
    refine (burnsideF4j_subImg_cenIn_le _ _ hrM.2).trans ?_
    have e : burnsideF4d_bTwo β ε ⟨r, hrM.2⟩ = bM β ε rr :=
      (burnsideF4j_bOne_eq_bTwo β ε r hrM.1 hrM.2).symm.trans (burnsideF4j_bM_eq_bOne β ε rr).symm
    rw [e]
    exact hCH
  have hC1 : cenIn (Gp ⊓ M₁) r ≤ M₁ := inf_le_left.trans inf_le_right
  have hC2 : cenIn (Gp ⊓ M₂) r ≤ M₂ := inf_le_left.trans inf_le_right
  rcases hcases with ⟨hV, hVnot⟩ | ⟨hV, hVnot⟩
  · exact hVnot (burnsideF4j_F436_core _ _ hb1 hb2 (burnsideF4j_bOne_eq_bTwo β ε) hHcl hC1 hC2
      hX1 hX2 hV)
  · exact hVnot (burnsideF4j_F436_core _ _ hb2 hb1
      (fun x h2 h1 => (burnsideF4j_bOne_eq_bTwo β ε x h1 h2).symm) hHcl hC2 hC1 hX2 hX1 hV)

theorem burnsideF4m_F_4_36_of_U5 (h5 : burnsideF4m_F436U5) : F_4_36 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hκ hf1 chart Tb hTb fb hfbT hgraph
  rcases hκ with rfl | rfl
  · exact burnsideF4m_F_4_36_U4 f E Gp M₁ M₂ Y β M ε z hyp hf1 Tb hTb fb hfbT hgraph
  · exact h5 f E Gp M₁ M₂ Y β M ε z hyp hf1 Tb hTb fb hfbT hgraph

end F436

end CFSG.ASVolI
