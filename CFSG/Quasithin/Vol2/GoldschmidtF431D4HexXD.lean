module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexD
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexTits
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexTransport
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.TitsGeo CFSG.D4Hex

universe u w

section Cosets

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]

theorem d4_smul_xv_iff (c : α.Completion Y) (k : c.G0) :
    k • c.xv = c.xv ↔ (k : Y) ∈ c.φ1.range := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left]

theorem d4_smul_lv_iff (c : α.Completion Y) (k : c.G0) :
    k • c.lv = c.lv ↔ (k : Y) ∈ c.φ2.range := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right]

end Cosets

section Datum

theorem d4_adj12 : hexGraph.Adj (Sum.inl 0 : HexVtx) (Sum.inr 0 : HexVtx) :=
  hexGraph_adj_inl_inr.2 ((mem_hexLine_iff_lineSet _ _).2 (by rw [lineSet_zero]; simp [line0]))

theorem d4XDatum : XDatum d4Setting d4Phi hexGraph (Sum.inl 0 : HexVtx) (Sum.inr 0 : HexVtx) where
  inj := d4Phi_injective
  N_eq := (MonoidHom.range_eq_top.2 d4Phi_surjective).symm
  dec g := by
    obtain ⟨y, rfl⟩ := d4Phi_surjective g
    exact ⟨y, 1, one_smul _ _, one_smul _ _, (mul_one _).symm⟩
  stab1 y := by
    rw [d4_smul_xv_iff, mem_range_φ1_iff, d4ToD_d4Phi, mem_d4H_iff]
    constructor
    · intro h
      exact congrArg Sum.inl h
    · intro h
      exact Sum.inl.inj h
  stab2 y := by
    rw [d4_smul_lv_iff, mem_range_φ2_iff, d4ToD_d4Phi, mem_d4N_iff_image]
    constructor
    · intro h
      refine congrArg Sum.inr ?_
      apply lineSet_injective
      rw [lineSet_smul, lineSet_zero]
      exact h
    · intro h
      have h' : y • (0 : Fin 2457) = 0 := Sum.inr.inj h
      rw [← lineSet_zero, ← lineSet_smul, h']
  disj y z := Sum.inl_ne_inr
  noadj1 y z := hexGraph_not_adj_inl
  noadj2 y z := hexGraph_not_adj_inr
  adj12 := d4_adj12

end Datum

section Geometry

theorem d4_exists_equiv : ∃ e : d4Setting.ι.Γ ≃ HexVtx, e d4Setting.ι.xv = Sum.inl pt0 ∧
    e d4Setting.ι.lv = Sum.inr 0 ∧ (∀ (y : D) (a : d4Setting.ι.Γ), e (d4Phi y • a) = y • e a) ∧
    ∀ a b, d4Setting.ι.graph.Adj a b ↔ hexGraph.Adj (e a) (e b) :=
  d4XDatum.exists_equiv hexGeometryD.cover (fun _ ha => hexPtD.flag d4_adj12 ha)

noncomputable def d4E : d4Setting.ι.Γ ≃ HexVtx := Classical.choose d4_exists_equiv

theorem d4E_xv : d4E d4Setting.ι.xv = Sum.inl pt0 := (Classical.choose_spec d4_exists_equiv).1

theorem d4E_lv : d4E d4Setting.ι.lv = Sum.inr 0 := (Classical.choose_spec d4_exists_equiv).2.1

theorem d4E_smul (g : D) (a : d4Setting.ι.Γ) : d4E (d4Phi g • a) = g • d4E a :=
  (Classical.choose_spec d4_exists_equiv).2.2.1 g a

theorem d4E_adj (a b : d4Setting.ι.Γ) : d4Setting.ι.graph.Adj a b ↔ hexGraph.Adj (d4E a) (d4E b) :=
  (Classical.choose_spec d4_exists_equiv).2.2.2 a b

theorem d4EqData : EqData d4Phi d4E hexGraph d4Setting.ι.graph :=
  ⟨d4Phi_surjective, d4E_smul, d4E_adj⟩

theorem d4_dist_lay (p : Fin 819) : hexGraph.dist (Sum.inl pt0) (Sum.inl p) = lay0[(p : ℕ)]! :=
  hexLay0 p

theorem d4_hpoly : IsGenPolygon d4Setting.ι.graph 6 :=
  IsGenPolygon.of_iso (⟨d4E, fun {a b} => (d4E_adj a b).symm⟩ : d4Setting.ι.graph ≃g hexGraph)
    hexPolygonD

theorem d4_hexPt : HexPt d4Setting.ι.G0 d4Setting.ι.graph d4Setting.ι.xv
    (d4E.symm (Sum.inl hexB0F)) :=
  HexPt.transport d4EqData (by rw [d4E_xv, Equiv.apply_symm_apply]; exact hexPtD)

theorem d4_hexLn : HexLn d4Setting.ι.G0 d4Setting.ι.graph d4Setting.ι.lv
    (d4E.symm (Sum.inl hexY0F)) (d4E.symm (Sum.inr hexM0F)) :=
  HexLn.transport d4EqData
    (by rw [d4E_lv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hexLnD)

theorem d4_titsModel : TitsModel d4Setting.ι 4 :=
  titsModel_of_hex d4Setting.hι d4_hpoly d4_hexPt d4_hexLn

end Geometry

end CFSG.Quasithin.D4Hex
