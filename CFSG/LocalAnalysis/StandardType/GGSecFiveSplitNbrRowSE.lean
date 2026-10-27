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
import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule

theorem ggSplitLie_of_rowSE6
    {G : Type} [Group G] [Finite G] {p : ℕ} {K : Subgroup G} (hp : p.Prime)
    (h : StandardType.LargeEvenMarking ↥K (fun lab _ _ _ _ _ => ggRowP_SE6 p lab)) :
    GGSplitLie p K := by
  obtain ⟨⟨tag, _, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ := largeEvenMarking_exists_markedModel h
  obtain ⟨rfl, hpn⟩ : tag = .E6 ∧ p ∣ 2 ^ n - 1 := hrow
  haveI : Finite (ggU .E6 0 n).K := FieldFour.finite_minGroup' (K := GaloisField 2 n) e6Data_valid
  refine ggSplitLie_of_lieModel (t := .E6) (n := 0) hp (.inr (.inr (.inl rfl))) hpn
    (fun hf E _ _ π hπ hcen => ?_) h.1 (MarkedModel.of_mulEquiv θ.symm hm)
  have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · exact FieldFour.e6_four_exists_section hc E π hπ hcen
  · have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h3)
    exact MinusculeClosed.e6_exists_section_of_central (by omega) hπ hcen

theorem ggSplitLie_of_rowSE7
    {G : Type} [Group G] [Finite G] {p : ℕ} {K : Subgroup G} (hp : p.Prime)
    (h : StandardType.LargeEvenMarking ↥K (fun lab _ _ _ _ _ => ggRowP_SE7 p lab)) :
    GGSplitLie p K := by
  obtain ⟨⟨tag, _, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ := largeEvenMarking_exists_markedModel h
  obtain ⟨rfl, hpn⟩ : tag = .E7 ∧ p ∣ 2 ^ n - 1 := hrow
  haveI : Finite (ggU .E7 0 n).K := FieldFour.finite_minGroup' (K := GaloisField 2 n) e7Data_valid
  refine ggSplitLie_of_lieModel (t := .E7) (n := 0) hp (.inr (.inr (.inr (.inl rfl)))) hpn
    (fun hf E _ _ π hπ hcen => ?_) h.1 (MarkedModel.of_mulEquiv θ.symm hm)
  have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · exact FieldFour.e7_four_exists_section hc E π hπ hcen
  · have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h3)
    exact MinusculeClosed.e7_exists_section_of_central (by omega) hπ hcen

theorem ggSplitLie_of_rowSE8
    {G : Type} [Group G] [Finite G] {p : ℕ} {K : Subgroup G} (hp : p.Prime)
    (h : StandardType.LargeEvenMarking ↥K (fun lab _ _ _ _ _ => ggRowP_SE8 p lab)) :
    GGSplitLie p K := by
  obtain ⟨⟨tag, _, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ := largeEvenMarking_exists_markedModel h
  obtain ⟨rfl, hpn⟩ : tag = .E8 ∧ p ∣ 2 ^ n - 1 := hrow
  haveI : Finite (ggU .E8 0 n).K := by
    have : Finite (Module.End (GaloisField 2 n)
        (CFSG.Blueprint.Chevalley.RootModule .E8 (GaloisField 2 n))) :=
      Module.finite_of_finite (GaloisField 2 n)
    change Finite (CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 n))
    infer_instance
  refine ggSplitLie_of_lieModel (t := .E8) (n := 0) hp (.inr (.inr (.inr (.inr rfl)))) hpn
    (fun hf E _ _ π hπ hcen => ?_) h.1 (MarkedModel.of_mulEquiv θ.symm hm)
  have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · exact FieldFour.e8_four_exists_section hc E π hπ hcen
  · have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h3)
    exact AdjointClosed.e8_exists_section_of_central (by omega) hπ hcen

end CFSG.StandardType

end
