module

public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOn
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Centre
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedSLTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggLieSU3FixedInputOn_offSUFour :
    GGLieSU3FixedInputOn (fun lab => ¬ GGLabelSUFour lab) := by
  intro X _ _ hX A δ J hl hZ hm hJ
  obtain ⟨-, lab, hlab, hraw⟩ := hm
  have hS : GGLabelTwClassical lab ∧ ¬ GGLabelSUFour lab := by
    have hrawc := hraw
    obtain ⟨R, _instR, I, F, hQ⟩ := largeEvenRawDatum_exists hrawc
    obtain ⟨-, -, θ, hP⟩ := hQ
    exact ⟨hP.1, hP.2.1⟩
  have hJperf : Group.IsPerfect J := ⟨hJ.1⟩
  have hJ3 : Nat.card (Subgroup.center ↥J) ∣ 3 := by
    obtain ⟨-, lab', hlab', hraw'⟩ := hJ
    obtain ⟨tag', rank', nn'⟩ := lab'
    have hlabprop : GGLabelA2 ⟨tag', rank', nn'⟩ ∧ tag' = .twA := by
      have hrawc := hraw'
      obtain ⟨R', _instR', I', F', hQ'⟩ := largeEvenRawDatum_exists hrawc
      obtain ⟨-, -, θ', hP'⟩ := hQ'
      exact hP'
    obtain ⟨hA2, htag'⟩ := hlabprop
    have hrank' : rank' = 2 := hA2.1
    subst htag'
    subst hrank'
    simp only [LargeEvenRawDatum] at hraw'
    obtain ⟨K', _instK', _instFinK', hK', hQK'⟩ := hraw'
    obtain ⟨-, -, θ', _hP'⟩ := hQK'
    exact gffa2_card_center_dvd_unitary hJperf hA2.2.1 hK' θ'
  obtain ⟨tag, rank, nn⟩ := lab
  obtain ⟨hTw, hnS⟩ := hS
  rcases hTw with htag | ⟨htag, hrank⟩
  · change tag = .twD at htag
    subst htag
    have hr3 : rank ≠ 3 := fun h => hnS (Or.inr ⟨rfl, h⟩)
    have hr2 : 2 ≤ rank := hlab.2
    by_cases hr : rank = 2
    ·
      subst hr
      simp only [LargeEvenRawDatum] at hraw
      obtain ⟨K, _instK, _instFinK, hK, hQK⟩ := hraw
      obtain ⟨-, -, θ, hP⟩ := hQK
      exact (ggLieSU3Fixed_false_of_slTwo hX hl hK θ hP.2.2).elim
    ·
      obtain ⟨r, rfl⟩ : ∃ r, rank = r + 4 := ⟨rank - 4, by omega⟩
      simp only [LargeEvenRawDatum] at hraw
      obtain ⟨K, _instK, _instFinK, hK, b, c, hbc, hQK⟩ := hraw
      obtain ⟨-, -, θ, hP⟩ := hQK
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Fintype K := Fintype.ofFinite K
      haveI : CharP K 2 :=
        charP_of_card_eq_prime_pow (p := 2) (f := nn) (by rw [← Nat.card_eq_fintype_card, hK])
      have hker : (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker =
          Subgroup.center X := by
        rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X)) θ.toMonoidHom
          θ.injective, QuotientGroup.ker_mk']
      have hcp : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
        CorFourTwoOpen.ggCenterPrime_omegaMinus (K := K) Nat.prime_three (by norm_num)
          (m := r + 3) (by omega) hbc X (θ.toMonoidHom.comp (QuotientGroup.mk' _))
          (θ.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le hX
      exact ggLieSU3Fixed_of_omegaMinus hX hl hZ hJ3 hcp hK (m := r + 3) (by omega)
        hbc θ hP.2.2
  · exact absurd (Or.inl ⟨htag, hrank⟩) hnS

end CFSG.StandardType
