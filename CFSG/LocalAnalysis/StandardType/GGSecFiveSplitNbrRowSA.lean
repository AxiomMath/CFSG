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
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.LieType.Steinberg.CentralExt

theorem ggSplitLie_of_rowSA
    {G : Type} [Group G] [Finite G] {p : ℕ} {K : Subgroup G} (hp : p.Prime)
    (h : StandardType.LargeEvenMarking ↥K (fun lab _ _ _ _ _ => ggRowP_SA p lab)) :
    GGSplitLie p K := by
  obtain ⟨⟨tag, l, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ := largeEvenMarking_exists_markedModel h
  have hX := MarkedModel.of_mulEquiv θ.symm hm
  obtain ⟨hlab, hpn⟩ : (tag = .A ∧ 3 ≤ l ∨ tag = .D ∧ l = 3) ∧ p ∣ 2 ^ n - 1 := hrow
  suffices H : ∀ m, 3 ≤ m → LieModel (↥K ⧸ Subgroup.center ↥K) .PSL (m + 1) 2 n →
      GGSplitLie p K by
    rcases hlab with ⟨rfl, hl⟩ | ⟨rfl, rfl⟩
    · exact H l hl hX
    · exact H 3 le_rfl hX
  intro m hm hXm
  haveI : Finite (ggU .PSL (m + 1) n).K := by
    change Finite (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 n))
    infer_instance
  refine ggSplitLie_of_lieModel (t := .PSL) hp (.inl rfl) hpn
    (fun hf E _ _ π hπ hcen => ?_) h.1 hXm
  have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ 2 ^ n := four_le_two_pow hf
  exact SLClosed.sl_exists_section_of_separating (by omega)
    (SLClosed.separating_of_card (by omega) (by omega) (by omega) (by omega)) hπ hcen

end CFSG.StandardType

end
