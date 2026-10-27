module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Inn

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.TitsGeo CFSG.D4Hex

section Geometry

variable
  (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z)
  (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N)

include hZH hNN

theorem d3_exists_equiv : ∃ e : d3Setting.ι.Γ ≃ HexVtx, e d3Setting.ι.xv = Sum.inl pt0 ∧
    e d3Setting.ι.lv = Sum.inr 0 ∧
    (∀ (y : ↥(autStab d4H ⊔ autStab d4N)) (a : d3Setting.ι.Γ), e (d3Phi y • a) = y • e a) ∧
    ∀ a b, d3Setting.ι.graph.Adj a b ↔ hexGraph.Adj (e a) (e b) :=
  (d3XDatum hZH hNN).exists_equiv cover_K3 (fun _ ha => hexPtK3.flag d4_adj12 ha)

noncomputable def d3E : d3Setting.ι.Γ ≃ HexVtx := Classical.choose (d3_exists_equiv hZH hNN)

theorem d3E_xv : d3E hZH hNN d3Setting.ι.xv = Sum.inl pt0 :=
  (Classical.choose_spec (d3_exists_equiv hZH hNN)).1

theorem d3E_lv : d3E hZH hNN d3Setting.ι.lv = Sum.inr 0 :=
  (Classical.choose_spec (d3_exists_equiv hZH hNN)).2.1

theorem d3E_smul (g : ↥(autStab d4H ⊔ autStab d4N)) (a : d3Setting.ι.Γ) :
    d3E hZH hNN (d3Phi g • a) = g • d3E hZH hNN a :=
  (Classical.choose_spec (d3_exists_equiv hZH hNN)).2.2.1 g a

theorem d3E_adj (a b : d3Setting.ι.Γ) :
    d3Setting.ι.graph.Adj a b ↔ hexGraph.Adj (d3E hZH hNN a) (d3E hZH hNN b) :=
  (Classical.choose_spec (d3_exists_equiv hZH hNN)).2.2.2 a b

theorem d3EqData : EqData d3Phi (d3E hZH hNN) hexGraph d3Setting.ι.graph :=
  ⟨d3Phi_surjective, d3E_smul hZH hNN, d3E_adj hZH hNN⟩

omit
  hZH hNN in
theorem d3_dist_lay (p : Fin 819) : hexGraph.dist (Sum.inl pt0) (Sum.inl p) = lay0[(p : ℕ)]! :=
  hexLay0 p

theorem d3_hpoly : IsGenPolygon d3Setting.ι.graph 6 :=
  IsGenPolygon.of_iso
    (⟨d3E hZH hNN, fun {a b} => (d3E_adj hZH hNN a b).symm⟩ : d3Setting.ι.graph ≃g hexGraph)
    hexPolygonD

theorem d3_hexPt : HexPt d3Setting.ι.G0 d3Setting.ι.graph d3Setting.ι.xv
    ((d3E hZH hNN).symm (Sum.inl hexB0F)) :=
  HexPt.transport (d3EqData hZH hNN)
    (by rw [d3E_xv hZH hNN, Equiv.apply_symm_apply]; exact hexPtK3)

theorem d3_hexLn : HexLn d3Setting.ι.G0 d3Setting.ι.graph d3Setting.ι.lv
    ((d3E hZH hNN).symm (Sum.inl hexY0F)) ((d3E hZH hNN).symm (Sum.inr hexM0F)) :=
  HexLn.transport (d3EqData hZH hNN)
    (by rw [d3E_lv hZH hNN, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hexLnK3)

theorem d3_titsModel : TitsModel d3Setting.ι 4 :=
  titsModel_of_hex d3Setting.hι (d3_hpoly hZH hNN) (d3_hexPt hZH hNN) (d3_hexLn hZH hNN)

end Geometry

end CFSG.Quasithin.D4Hex
