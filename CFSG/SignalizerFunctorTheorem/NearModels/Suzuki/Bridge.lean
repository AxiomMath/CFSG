module

public import CFSG.Open.Catalog
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport

public section

namespace CFSG.SignalizerFunctorTheorem.NearModels.Suzuki

open CFSG.Open CFSG.Blueprint CFSG.ShultStronglyClosedTI

theorem nonempty_mulEquiv_sz_suzukiGroup (n : ℕ) :
    Nonempty (Sz n ≃* suzukiGroup n (GaloisField 2 (2 * n + 1))) :=
  ⟨(glaSzCanonicalEquivNative n).symm.trans
    (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup n _)).symm⟩

theorem nonempty_mulEquiv_suzukiGroup_zero_sz :
    Nonempty (suzukiGroup 0 (ZMod 2) ≃* Sz 0) :=
  ⟨(MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 0 (ZMod 2))).trans
    ((glaSzFieldEquiv (binaryFieldEquiv (2 * 0 + 1) (by omega) (by simp)) 0).trans
      (glaSzCanonicalEquivNative 0))⟩

end CFSG.SignalizerFunctorTheorem.NearModels.Suzuki
