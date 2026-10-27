module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31M22HexModel
public import CFSG.Quasithin.Vol2.Ch12Sec6P31M22HexCover
public import CFSG.Quasithin.Vol2.Ch12Sec6P31M22HexHom
public import CFSG.Quasithin.Vol2.Ch12Sec6P31M22HexPush
public import CFSG.Quasithin.Vol2.Ch12Sec6P31M22HexResidual

public section

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Quasithin.H13.P31Sec.M22Hex

theorem m22Hexad_w31_holds :
    M22Hexad_w31 := by
  intro Γ _ _ X S₀ hS₀X hX hSyl
  obtain ⟨π, hπ, hKc, hKchar⟩ := exists_cover_hom hX
  have hPsyl := isSylowTwoOf_map π hπ hSyl
  have hsimple : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  obtain ⟨B, hPB, huniq, hself, f, hf, hker⟩ := hexad_of_sylow_of_eq
    CFSG.Blueprint.NativeSporadic.M22
    CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat.mGens_closure hsimple _ hPsyl
  obtain ⟨B', hSB', hNS, hφ, hself', hchar⟩ := cover_hexad π hπ hKc hKchar (S₀.subgroupOf X) B
    hPB huniq hself f hf hker
  obtain ⟨B₁, h1, h2, h3, ⟨φ, hφ'⟩, h5, h6⟩ :=
    push_to_gamma X S₀ hS₀X B' hSB' hNS hφ hself' hchar
  obtain ⟨ψ, hψ⟩ := exists_surj_oThreePrimeResidual B₁ φ hφ'
  exact ⟨B₁, h1, h2, h3, ⟨ψ, hψ⟩, h5, h6⟩

end CFSG.Quasithin.H13.P31Sec
