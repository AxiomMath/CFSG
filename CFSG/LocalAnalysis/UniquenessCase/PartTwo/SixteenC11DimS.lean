module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c11_le_conjSubgroup_of_rk_barSub_lt (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {g : G} (hAM : conjSubgroup V g ≤ D.M)
    (hr : ((rk ↥(barSub V₀ V hV (conjSubgroup V g)) + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V) :
    V ≤ conjSubgroup D.M g := by
  have h62 : Hyp62 D.M V₀ V := h.hyp62
  have hP := h.pairFacts
  have hrk := rk_barSub_eq_mQuot_inf_cTilde (V₀ := V₀) (M := D.M) hV hP.le_normalizer
    hP.le_normalizer₀ hAM
  have hD' : conjSubgroup V g ⊓ F11.CTilde D.M V₀ V ≤ conjSubgroup V g ⊓ D.M :=
    inf_le_inf_left _ fun d hd => ((mem_cTilde_iff hV hP.le_normalizer).1 hd).1
  have hr' : ((E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ F11.CTilde D.M V₀ V) +
      mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    rw [← hrk]
    exact hr
  have h1 := six_two_one h62 hD' hr'
  have hst : conjSubgroup V g ⊓ F11.CTilde D.M V₀ V ≤ stabTil V₀ V := h62.le_stabTil hD'
  refine le_trans (fun u hu => ?_) h1
  refine (mem_preCTilde_iff hV hst hu).2 fun d hd => ?_
  obtain ⟨-, hds, hd1⟩ := (mem_cTilde_iff hV hP.le_normalizer).1 (Subgroup.mem_inf.1 hd).2
  have h2 := (actTil_eq_one_iff V₀ V hV ⟨d, hds⟩).1 hd1 u hu
  have h3 : ⁅u, d⁆ = (d * u * d⁻¹ * u⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h3]
  exact V₀.inv_mem h2

theorem s16c11_mSub_add_rk_fixV_le_rMV (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {B : Subgroup G}
    (hBM : B ≤ D.M) (hBp : IsPGroup p B) (hBc : ¬ IsCyclic B)
    (hV₀B : V₀ ≤ centralizer (B : Set G)) :
    ((mSub V₀ + rk ↥(fixV (barSub V₀ V hV B)) : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have h1 := rk_add_rk_fixV_barSub_le hV hP.le (D.sig_prime p hp).1 (D.sig_prime p hp).2 hBp
    (hBM.trans hMst) hV₀B
  have h2 := rk_inf_centralizer_le_rMV D h61 hp hBM hBp hBc hV
  exact le_trans (by exact_mod_cast h1) h2

theorem s16c11_rk_barSub_le_pRank {M V₀ V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAM : A ≤ M) (hAel : IsElemAbelian 2 A) :
    rk ↥(barSub V₀ V hV A) ≤ CFSG.Open.pRank 2 (Mbar M V₀ V hV) :=
  H.rk_le_pRank (barSub_mono V₀ V hV hAM) (isElemAbelian2_barSub hV hAel)

theorem s16c11_normalizer_le_of_forall_barSub_eq_bot (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V)
    (hbot : ∀ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A = ⊥)
    {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup (MulAut (Vtil V₀ V hV))}
    (hPM : P ≤ Mbar D.M V₀ V hV) (hPp : IsPGroup p ↥P) (hPc : ¬ IsCyclic ↥P) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hP := h.pairFacts
  have hTst : D.T ≤ stabTil V₀ V :=
    D.sylowM.le.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hW : barSub V₀ V hV (E3.wClos V 0 D.T) = ⊥ := by
    have hinner : ∀ A, (⨆ (_ : A ∈ E3.gammaSet V 0 D.T), A) ≤ stabTil V₀ V := fun A =>
      iSup_le fun hA' => hA'.1.trans hTst
    have h1 := barSub_iSup_of_le (V₀ := V₀) hV
      (K := fun A => ⨆ (_ : A ∈ E3.gammaSet V 0 D.T), A) hinner
    unfold E3.wClos
    rw [h1]
    refine le_bot_iff.1 (iSup_le fun A => ?_)
    have h2 := barSub_iSup_of_le (V₀ := V₀) hV (K := fun _ : A ∈ E3.gammaSet V 0 D.T => A)
      (fun hA' => hA'.1.trans hTst)
    rw [h2]
    exact iSup_le fun hAΓ => (hbot A hAΓ).le
  refine s16c11_normalizer_le_of_routeA D h61 hV h (fun A hA => Or.inl (hbot A hA)) hp hPM hPp
    hPc ?_
  rw [hW]
  exact bot_le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
