module

public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.Spectrum

public section

namespace CFSG.RankThree.PartOne.SEITZ9

open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne.CTP
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_S szFieldAut_D
  szFieldAut_W)

variable {a : ℕ} {K : Type} [Field K]

section Rational

theorem suzukiSElt_mem_fixed (σ : RingAut K) {u v : K} (hu : σ u = u) (hv : σ v = v) :
    suzukiSElt a K u v ∈ fixedSubgroup (szFieldAut a K σ) := by
  rw [mem_fixedSubgroup, szFieldAut_S, hu, hv]

theorem suzukiDElt_mem_fixed (σ : RingAut K) {l : Kˣ} (hl : σ (l : K) = l) :
    suzukiDElt a K l ∈ fixedSubgroup (szFieldAut a K σ) := by
  rw [mem_fixedSubgroup, szFieldAut_D]
  congr 1
  exact Units.ext hl

theorem suzukiWElt_mem_fixed (σ : RingAut K) :
    suzukiWElt a K ∈ fixedSubgroup (szFieldAut a K σ) := by
  rw [mem_fixedSubgroup, szFieldAut_W]

end Rational

end CFSG.RankThree.PartOne.SEITZ9
