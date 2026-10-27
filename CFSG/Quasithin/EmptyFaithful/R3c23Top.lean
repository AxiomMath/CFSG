module

public import CFSG.Quasithin.EmptyFaithful.R3c23Glue4
public import CFSG.Quasithin.EmptyFaithful.R3c23PairA
public import CFSG.Quasithin.EmptyFaithful.R3c23PairB2
public import CFSG.Quasithin.EmptyFaithful.R3c23NatSL2
public import CFSG.Quasithin.EmptyFaithful.R3c23NatSym

public section

namespace CFSG.Quasithin

namespace R3c23

theorem pairOutputOfAction_holds (h₁ : SL2PieceFacts) (h₂ : Sym5PieceFacts)
    (hA21 : AsA21SQTKSection) (h56 : AsB56) : PairOutputOfAction := by
  intro V _ _ Hg _ _ hS hV ρ K₁ t hqK hKn hcomm hQ h2 hperm hnt hFF hK
  obtain ⟨hq₁, hq₂, hc, hconj, hn, h2', hO2⟩ :=
    S153M.ar_facts_two ρ K₁ t hqK hKn hcomm hQ h2 hperm hnt
  have hτX : ρ t ∈ ρ.range := ⟨t, rfl⟩
  have hL₁X : K₁.map ρ ≤ ρ.range := Subgroup.map_le_range ρ K₁
  have hL₂X : (K₁.map (MulAut.conj t).toMonoidHom).map ρ ≤ ρ.range :=
    Subgroup.map_le_range ρ _
  obtain ⟨hL₁J, hL₂J⟩ := S153M.twoA_le_ffJ hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hO2 hFF
  have hB53 := S153M.b53Hyp_of_two hA21 hS ρ hq₁ hq₂ hc hL₁J hL₂J hn h2' hO2
  exact pairOutput_of_twoB56Gen h₁ h₂ hconj hq₁ hK
    (twoB56Gen_of_ffModule h56 hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hK hO2 hFF hB53)

theorem theoremC116L2_proved (hA21 : AsA21SQTKSection) (h56 : AsB56) (h38 : A38ForSQTK) :
    R3c20.TheoremC116L2 :=
  theoremC116L2_of_fixedVector
    (fixedVector_of_pairOutput (pairOutputOfAction_holds sl2PieceFacts sym5PieceFacts hA21 h56)
      h38)

end R3c23

end CFSG.Quasithin
