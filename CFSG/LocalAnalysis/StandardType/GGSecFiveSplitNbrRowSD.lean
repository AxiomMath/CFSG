module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.Assembly.LargeEvenDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSCore
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Steinberg.CentralExt

theorem ggSplitLie_of_rowSD
    {G : Type} [Group G] [Finite G] {p : ℕ} {K : Subgroup G} (hp : p.Prime)
    (h : StandardType.LargeEvenMarking ↥K (fun lab _ _ _ _ _ => ggRowP_SD p lab)) :
    GGSplitLie p K := by
  obtain ⟨⟨tag, l, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ := largeEvenMarking_exists_markedModel h
  obtain ⟨rfl, hl, hpn⟩ : tag = .D ∧ 4 ≤ l ∧ p ∣ 2 ^ n - 1 := hrow
  have hl3 : 3 ≤ l := by omega
  have hX : LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus l 2 n := by
    have h3 : l ≠ 3 := by omega
    simpa [MarkedModel, markTag, markRank, markChar, markDeg, h3] using
      MarkedModel.of_mulEquiv θ.symm hm
  have hU : ggU .POmegaPlus l n =
      ⟨spinGroup (Spin.quadPlus l (GaloisField 2 n)), Spin.plusDatum l (GaloisField 2 n) hl3⟩ := by
    simp only [ggU, lieUniversal, hl3, ↓reduceDIte]
  haveI : Finite (ggU .POmegaPlus l n).K := by
    haveI : NeZero l := ⟨by omega⟩
    rw [hU]
    exact CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ Spin.coe_ker_spinMatrix_quadPlus
  refine ggSplitLie_of_lieModel hp (.inr (.inl rfl)) hpn (fun hf E _ _ => ?_) h.1 hX
  have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rw [hU]
  intro π hπ hcen
  exact SpinPlusClosed.spinPlus_exists_section_of_central hl3
    (by rw [hc]; exact four_le_two_pow hf) hπ hcen

end CFSG.StandardType

end
