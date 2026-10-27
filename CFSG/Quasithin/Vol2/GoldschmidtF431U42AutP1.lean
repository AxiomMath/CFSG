module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Nrm
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Hat

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13

theorem u42AutNorm : U42AutNorm := by
  intro G _ _ hG hnab M₁ M₂ z hAm hO2 hz2 hz1 hzc hcz
  obtain ⟨Yb, _, Gh, _, ι, hY, hinj, hidx, T, N₁, N₂, hpair, ⟨iso0⟩⟩ := hAm
  rcases equiv_A_or_central_involution hY hinj hidx with ⟨⟨ε⟩⟩ | ⟨κ, hκ1, hκ2, hκc⟩
  swap
  · exact (no_central_involution hO2 hpair iso0 hκ1 hκ2 hκc).elim
  have hp₁ := IsYAmalgamPair.map ε hpair
  obtain ⟨c, hc⟩ := U42.exists_conj_isSylowTwoOf_top hp₁.1 isSylowTwoOf_That_top
  have hp₂ := IsYAmalgamPair.map (MulAut.conj c) hp₁
  rw [hc] at hp₂
  let iso1 := U42.Am.ofSubgroupsMapInj ε.toMonoidHom ε.injective N₁ N₂
  let iso2 := U42.Am.ofSubgroupsMapInj (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    (N₁.map ε.toMonoidHom) (N₂.map ε.toMonoidHom)
  rcases pair_eq_of_isYAmalgamPair_A hp₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨U42.Am.isoSymm (U42.Am.isoTrans iso0 (U42.Am.isoTrans iso1
      (U42.Am.isoTrans iso2 (U42.Am.ofSubgroupsCongr h1 h2))))⟩
  · exact (not_swapped_A (U42.Am.isoTrans iso0 (U42.Am.isoTrans iso1
      (U42.Am.isoTrans iso2 (U42.Am.ofSubgroupsCongr h1 h2)))) hz2 hz1 hzc hcz).elim

end CFSG.Quasithin.H13.F431.U42Aut
