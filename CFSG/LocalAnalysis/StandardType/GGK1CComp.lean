module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CCoBlocks
public import CFSG.LocalAnalysis.StandardType.GGK1CCoArith
public import CFSG.LocalAnalysis.StandardType.GGK1CCoLabel
public import CFSG.LocalAnalysis.StandardType.GGK1CCoComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

theorem ggK1C_core_comp {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hK : Nat.card K = 2 ^ nf)
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf d r K x m)
    (hx : x ^ p = 1) :
    GGK1Comps nf (ggMultDatumC p nf d m) (StatedProj (StatedSp r K))
      (MulAut.conj (proj r K x)) := by
  have hnf : 1 ≤ nf := by
    rcases Nat.eq_zero_or_pos nf with h0 | hpos
    · subst h0
      rw [pow_zero] at hK
      have h2 := Finite.one_lt_card (α := K)
      omega
    · exact hpos
  obtain ⟨B⟩ := ggK1CCo_blocks_exists hnf hp hp2 hdvd hK hm hx
  obtain ⟨F⟩ := ggK1CCo_family_of_blocks B hK
  refine ⟨?_, ?_⟩
  · intro J hJ
    obtain ⟨i, hq, hJeq⟩ := ggK1CCo_component_eq F hJ
    rw [hJeq]
    have hqs : (F.blk i).qs = true := F.hqs i hq
    obtain ⟨hdvdn, hlam⟩ := ggK1CCo_orbit_arith hnf (F.hmem i hq) hqs
    exact ⟨F.blk i, F.hmem i hq, hqs, hdvdn, hlam, F.hlab i hq⟩
  · intro o ho hqs
    obtain ⟨i, hq, hi⟩ := F.hreal o ho hqs
    refine ⟨(⁅F.A i, F.A i⁆).map (proj r K), ggK1CCo_factor_component F i hq, ?_⟩
    rw [← hi]
    exact F.hlab i hq

end CFSG.StandardType

end
