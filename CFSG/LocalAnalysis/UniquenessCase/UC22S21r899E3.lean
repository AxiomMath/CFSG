module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22r899e3_three_le_pRank {M : Subgroup G}
    {L : Fin 3 → Subgroup G} {n : Fin 3 → ℕ} {s r : ℕ} (hinj : Function.Injective L)
    (hL : ∀ i, L i ∈ calC M) (hshape : ∀ i, IsSz (Bar2 (L i)) (n i) ∨ IsL2 (Bar2 (L i)) (n i))
    (hsn : ∀ i, s ∣ n i) (hr : r.Prime) (hrd : r ∣ 2 ^ s - 1) (hr2 : r ≠ 2) :
    3 ≤ CFSG.Open.pRank r M := by
  have hdvd : ∀ i, r ∣ Nat.card (barImage M (L i)) := by
    intro i
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (hL i)
    rw [← Nat.card_congr e.toEquiv]
    exact PartTwo.s13_dvd_card_of_isL2_or_isSz (hshape i).symm (hsn i) hr hrd
  have hZ : ∀ i, center (Bar2 (L i)) = ⊥ := by
    intro i
    rcases hshape i with hX | hX
    · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
      exact uc22p21k_center_eq_bot (hL i).2.2
    · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
      exact uc22p21k_center_eq_bot (hL i).2.2
  have hcen : ∀ i, ∀ x ∈ barImage M (L i), (∀ y ∈ barImage M (L i), y * x = x * y) →
      x ^ r = 1 → x = 1 := by
    intro i x hx hxc _
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (hL i)
    have hu : e.symm ⟨x, hx⟩ ∈ center (Bar2 (L i)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hxc (e g : Bar2 M) (e g).2)
    rw [hZ i, Subgroup.mem_bot] at hu
    have h1 : (⟨x, hx⟩ : ↥(barImage M (L i))) = 1 := by
      rw [← e.apply_symm_apply ⟨x, hx⟩, hu, map_one]
    exact congrArg Subtype.val h1
  have hcb : ∀ i j, i ≠ j → ⁅barImage M (L i), barImage M (L j)⁆ = ⊥ := by
    intro i j hij
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (uc22p22l_barImage_commute (hL i) (hL j) (fun h => hij (hinj h)) a ha b hb).symm
  obtain ⟨E, -, hE, hEc⟩ :=
    CFSG.QuasithinUnique.Unc25G2.exists_elemAbelian_card_cube_of_commuting hr
      (hcb 0 1 (by decide)) (hcb 0 2 (by decide)) (hcb 1 2 (by decide)) (hcen 0) (hcen 1)
      (hdvd 0) (hdvd 1) (hdvd 2)
  have h3 : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup (Bar2 M)) :=
    UC6S846.le_pRank' hr le_top hE hEc
  rwa [pRank_bar2_eq_of_odd hr hr2] at h3

theorem uc22r899e3_of_sigmaStd (D : Data G)
    (hSg : UC6S846.SigmaStd D)
    (h3 : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig) :
    F08.R899 D := by
  intro L n s r hinj hL hshape hs hsn hr hrd _
  have hr7 : 7 ≤ r := PartTwo.s13_seven_le_of_dvd hs hr hrd
  have hrank := uc22r899e3_three_le_pRank hinj hL hshape hsn hr hrd (by omega)
  exact UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC (hL 0)) (h3 r hr hr7 hrank)

theorem uc22r899e3_dataOfSetup (hS : Standing G)
    (hUC : rankThreeUC G) (S : Setup G) : F08.R899 (PartTwo.Three.dataOfSetup hS S) :=
  uc22r899e3_of_sigmaStd _ (UC6S846.sigmaStd_dataOfSetup hS S)
    fun _ hr h7 h3 =>
      PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC S.witness.maxLocal hr h7 h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
