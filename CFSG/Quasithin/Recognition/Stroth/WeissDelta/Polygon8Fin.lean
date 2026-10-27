module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Oct
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma3
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.DeltaEmbedding

public section

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

theorem weiss80Polygon8Fin : Weiss80Polygon8Fin := by
  intro X _ _ P1 P2 a m ha hm hK1 hK2 hSz hL2 hV1 hV2
  intro Y _ _ c hc hM hW hg
  have hv1 : 3 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have h : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    omega
  have hv2 : 3 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have h : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    omega
  have hne : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w :=
    exists_adj_ne c hc hv1 hv2
  have h4' : WeissLemma4' c.G0 c.graph 8 :=
    weissLemma4'_of_polygon8 c hc hM hW hg ha hm hK1 hK2 hSz hL2 hV1 hV2
  have hL : ∀ z, LocalFacts c.G0 c.graph z := fun z =>
    (localFacts_of_polygon8 c hc hM hW hg ha hm hSz hL2 hV1 hV2 z).1
  have h4 : WeissLemma4 c.G0 c.graph 8 :=
    weissLemma4_of_weissLemma4' (n := 8) (by norm_num) hM hW hne hL h4'
  have hG : GoodPathSystem c.G0 c.graph 8 (fun _ p => IsGoodPath c.G0 p) :=
    goodPathSystem_isGoodPath (n := 8) (by norm_num) hM hW hne hL h4
  obtain ⟨V, hVfin, Δ, hΔdec, D, hDgrp, hDfin, hDmul, hDfaith, hDGA, u, v, ψ₁, ψ₂, ι,
    hGP, hT, hadj, hMΔ, hstab1, hstab2, hE⟩ :=
    exists_delta_of_goodPathSystem (n := 8) (by norm_num) c hc hM hW hg hv1 hv2
      (fun _ p => IsGoodPath c.G0 p) hG
  letI : Fintype V := hVfin
  letI : DecidableRel Δ.Adj := hΔdec
  letI : Group D := hDgrp
  letI : Finite D := hDfin
  letI : MulAction D V := hDmul
  letI : FaithfulSMul D V := hDfaith
  letI : GraphAction D Δ := hDGA
  obtain ⟨hdu, hdv⟩ :=
    degree_eq_of_isWeissEmbedding (n := 8) (by norm_num) c hc hM hGP hT hMΔ hE hV1 hV2
  exact ⟨V, hVfin, Δ, hΔdec, D, hDgrp, hDfin, hDmul, hDfaith, hDGA, u, v, ψ₁, ψ₂, ι,
    hGP, hT, hadj, hMΔ, hstab1, hstab2, hE, hdu, hdv⟩

end CFSG.Quasithin.Stroth.WeissDelta

end
