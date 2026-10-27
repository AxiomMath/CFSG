module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.MPrime
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIHyp79
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNormLB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem isMaxTwoLocal_MbarPrime_of_ti (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hMA : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    IsMaxTwoLocalSubgroup (MbarPrime M Q Z Z0) := by
  haveI hFinH : Finite (Hbar M Q Z) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  let M' : Subgroup (Hbar M Q Z) := MbarPrime M Q Z Z0
  have hconf₀ := hc.tiConfig hs hZ0 hZt hZcard
    (sec7_CN_pgroup_bar h34 h311a hc hs) hMA hTI hF
  have hconf : TIConfig (⊤ : Subgroup (Hbar M Q Z)) V
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) := by
    simpa only [V, Subgroup.comap_subtype] using
      hconf₀.comap (bar M Q (H0 M Z)).subtype Subtype.val_injective
        (Subgroup.range_subtype _)
  have hNV : M' = Subgroup.normalizer (V : Set (Hbar M Q Z)) := by
    simpa only [M', V] using MbarPrime_eq_normalizer_bar_Z0 hc hs hZ0
  have hK : NormIn (⊤ : Subgroup (Hbar M Q Z)) V = M' := by
    rw [NormIn, top_inf_eq]
    exact hNV.symm
  refine ⟨isTwoLocal_MbarPrime hc hs hZ0 hZc, ?_⟩
  intro K hK2 hM'K
  obtain ⟨D, hDne, hD2, hKD⟩ := hK2
  have hNormD : NormIn (⊤ : Subgroup (Hbar M Q Z)) D = K := by
    rw [NormIn, top_inf_eq]
    exact hKD.symm
  have hle : NormIn (⊤ : Subgroup (Hbar M Q Z)) V ≤ NormIn ⊤ D := by
    rw [hK, hNormD]
    exact hM'K
  have hle' := TIConfig.maximal_local hconf le_top hDne hD2 hle
  rw [hNormD, hK] at hle'
  exact le_antisymm hle' hM'K

end CFSG.RankThree.GF2n.Stroth80
