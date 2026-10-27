module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmDiag
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmDich
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmBlock
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmFix
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3OrthMinusBlock
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

theorem jcoreOm_center :
    ∀ n f, StatedLieAdmissible .POmegaPlus n 2 f → 3 ≤ bnRank .POmegaPlus n →
      Subgroup.center (ggU .POmegaPlus n f).K = ⊥ := by
  intro n f _ h3
  have hn : 3 ≤ n := h3
  rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
    plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
  exact RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn

theorem jcoreOm_hypVI :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs L : Subgroup G) (n f : ℕ)
      (ψ : (ggU .POmegaPlus n f).K →* G), GGKGPosLocalHyp p Bs L .POmegaPlus n f ψ →
        ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  intro G _ _ p Bs L n f ψ hloc b hb
  have hn : 3 ≤ n := hloc.1.2.2.2
  have hker := hloc.2.1.1
  have hc := hloc.2.2.2.1 b hb
  clear hloc
  revert ψ
  rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
    plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
  intro ψ hker hc
  exact PsiDiag.SpinP.exists_mem_centralizer (K := GaloisField 2 f) hn ψ hker hc

theorem jcore_POmegaPlus_torus :
    GGJRootCoreTorusAt .POmegaPlus := by
  intro n f hadm h3 p hp hp2 hpf
  have hn : 3 ≤ n := h3
  have hf : 1 ≤ f := hadm.2.1
  rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
    plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
  intro u hu hup J hJ
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h2f : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hple : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by omega) hpf
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hF : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hcard]
    omega
  have hpq : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [hcard]
    exact hpf
  have hrange : (spinAction (quadPlus n (GaloisField 2 f))).range =
      orthDerived (quadPlus n (GaloisField 2 f)) := range_spinAction_quadPlus_eq_commutator hn
  have hxΩ : spinAction (quadPlus n (GaloisField 2 f)) u ∈
      orthDerived (quadPlus n (GaloisField 2 f)) := hrange ▸ ⟨u, rfl⟩
  have hxp : (⟨_, hxΩ⟩ : ↥(orthDerived (quadPlus n (GaloisField 2 f)))) ^ p = 1 := by
    apply Subtype.ext
    change spinAction (quadPlus n (GaloisField 2 f)) u ^ p = 1
    rw [← map_pow, hup, map_one]
  have hx := LocalAnalysis.GLTheoremA.CanonU3.OrthMinus.oddOrderIsometry_of_pow_eq_one hp
    (by rw [ringChar.eq (GaloisField 2 f) 2]; exact hp2)
    (nondegenerate_polarBilin_quadPlus n (GaloisField 2 f)) _ hxp
  obtain ⟨a, hxa⟩ := jcoreOm_diag hn hu
  obtain ⟨T, hT, hcase⟩ := jcoreOm_dichotomy hadm.2.2 hp hp2 hup hJ
  refine jcoreOm_rootLevi hn (fun z hz => (hT z).mpr hz) ?_
  rcases hcase with ⟨h, hh, hne1, hq, rfl⟩ | ⟨hL, hTq, hTle, hTn⟩
  · exact jcoreOm_special hp hp2 hpq hxΩ hx hxa hh hne1 hq
  · exact jcoreOm_fixed hF hx hxa hL hTq hTle hTn

theorem ggJRootCoreAt_POmegaPlus :
    GGJRootCoreAt .POmegaPlus :=
  ggJRootCoreAt_of_torus jcoreOm_center jcoreOm_hypVI jcore_POmegaPlus_torus

end CFSG.StandardType

end
