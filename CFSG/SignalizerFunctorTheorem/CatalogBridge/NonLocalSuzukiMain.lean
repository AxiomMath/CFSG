module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldSuzuki
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSuzuki
import CFSG.RankThree.PartOne.KE.SuzukiFixedCard

public section

open CFSG.Blueprint CFSG.Open
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.RankThree.PartOne.KE (fixField fixed_szFieldAut_equiv card_fixField_suzuki_odd)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem subfieldNonLocalizedSuzuki : SubfieldNonLocalizedSuzuki := by
  intro a ha K _ _ hK p hp hp2 hpa σ hσ
  classical
  obtain ⟨b, m, hab, hbp, hk⟩ := card_fixField_suzuki_odd hp hp2 hK hσ
  have hb1 : 1 ≤ b := by
    by_contra hb0
    obtain rfl : b = 0 := by omega
    exact hpa (by omega)
  obtain ⟨e⟩ := fixed_szFieldAut_equiv hK hk hab
  let e' : signalizerFixedSubgroup (szFieldAut a K σ) ≃* suzukiGroup b (fixField σ) :=
    (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans e
  obtain ⟨hsC, -, hnsC⟩ := isSimpleGroup_and_not_isSolvable_of_equiv_suzukiGroup hb1 hk e'
  have hC := centralizer_signalizerFixedSubgroup_szFieldAut_eq_bot ha hK hnsC
  refine nonLocalized_suzuki_of_simple hK hsC hnsC fun x hx => ?_
  have hxc : x ∈ Subgroup.centralizer
      (signalizerFixedSubgroup (szFieldAut a K σ) : Set (suzukiGroup a K)) :=
    Subgroup.mem_centralizer_iff.2 fun j hj => (hx j hj).symm
  rw [hC, Subgroup.mem_bot] at hxc
  exact hxc

end CFSG.SignalizerFunctorTheorem.CatalogBridge
