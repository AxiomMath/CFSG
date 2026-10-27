module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbOrbitBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbPlane
public import CFSG.LocalAnalysis.StandardType.GGQTwoCell
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2_ambOrbit {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3) (hLN : GGLNoncyclicInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H)
    (hbas : GGQTwoAmbBasis M) (hnd : ((M.cartan.det : ℤ) : ZMod p) ≠ 0)
    (hA3 : Fintype.card M.ι = 4 → Nat.card (ggAutomizer L Bs) ≠ 24) :
    GGQ2Orbit p B Bs x D J := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨hpprime, -, -, -, h4card⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := by omega
  have hNT : GGNoTransvection p Bs := hS.1.2.2.2.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hxD : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod p) M.V := Module.Finite.of_finite
  have hcardV : Nat.card M.V = p ^ Module.finrank (ZMod p) M.V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M.V), Nat.card_zmod]
  have hcardM : Nat.card M.V = Nat.card ↥Bs := by
    calc Nat.card M.V = Nat.card (Additive ↥Bs) := (Nat.card_congr M.model.toEquiv).symm
      _ = Nat.card ↥Bs := Nat.card_congr Additive.toMul
  have hpowle : p ^ 4 ≤ p ^ Module.finrank (ZMod p) M.V := by
    calc p ^ 4 ≤ Nat.card ↥Bs := h4card
      _ = Nat.card M.V := hcardM.symm
      _ = p ^ Module.finrank (ZMod p) M.V := hcardV
  have hfin4 : 4 ≤ Module.finrank (ZMod p) M.V :=
    (Nat.pow_le_pow_iff_right hpprime.one_lt).mp hpowle
  have hcardι : Fintype.card M.toLin.ι = Fintype.card M.ι := rfl
  have h4 : 4 ≤ Fintype.card M.toLin.ι := by
    rw [hcardι, hbas.2]
    exact hfin4
  have hA3' : ¬ (Fintype.card M.toLin.ι = 4 ∧
      Nat.card (M.toLin.parab {k | k ≠ M.toLin.a}) = 24) := by
    rintro ⟨hcard4, hparab⟩
    have hcard4' : Fintype.card M.ι = 4 := by rw [← hcardι]; exact hcard4
    have hparab' : Nat.card (M.parabL {k | k ≠ M.a}) = 24 := hparab
    refine hA3 hcard4' ?_
    rw [M.card_L]
    exact hparab'
  have hHLinput : GGLineStabNormalizesInput := ggLineStabNormalizesInput_of_noncyclic hLN
  have hfix : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.toLin.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {M.xV} := fun v => M.fixed_lin v
  have hB := ggQ2_thmB_lin hp M.toLin hbas hnd h4 M.xV hfix M.linGroup M.weyl_le_lin
    (M.transvectionFree hNT) (M.HL_lin hHLinput hS) hA3'
  rcases hB with hP3 | hFcell
  ·
    refine Or.inl ⟨⟨x, M.hx⟩, hxD, ?_, ?_⟩
    · intro h
      exact hx1 (congrArg Subtype.val h)
    · rw [M.orbit_iff hp2 ⟨x, M.hx⟩]
      intro φ hφ
      obtain ⟨r, hr, hsp⟩ := hP3 φ hφ
      exact ⟨r, hr, hsp⟩
  ·
    obtain ⟨y', hy'0, hy'⟩ := M.exists_fixedLine_b hp hbas hnd
    have hxy : LinearIndependent (ZMod p) ![M.xV, M.yV] := M.linearIndependent_xV_yV hS hnb
    have hplane : Submodule.span (ZMod p) {M.xV, y'} = Submodule.span (ZMod p) {M.xV, M.yV} :=
      M.span_xV_fixedLine_eq hp hbas hnd hxy hy'0 hy'
    have hDspan : ∀ v : M.V, v ∈ Submodule.span (ZMod p) {M.xV, y'} ↔
        ∃ d : ↥Bs, (d : G) ∈ D ∧ M.model (Additive.ofMul d) = v := by
      intro v
      rw [hplane]
      exact M.D_eq_span hnb v
    rcases ggQ2_cell_lin hp M.toLin hbas hnd M.xV y' hfix hy' M.linGroup M.weyl_le_lin
        (M.transvectionFree hNT) hA3' hFcell with hcell1 | hcell2
    ·
      obtain ⟨u, hu, hu0, hcell⟩ := hcell1
      obtain ⟨d, hdD, hdu⟩ := (hDspan u).mp hu
      have hd1 : d ≠ 1 := by
        intro h
        apply hu0
        rw [← hdu, h]
        exact map_zero M.model
      have hstab : GGOrbitStableAt p Bs d := by
        rw [M.orbit_iff hp2 d]
        intro φ hφ
        obtain ⟨r, hr, hsp⟩ := hcell φ hφ
        rw [hdu]
        exact ⟨r, hr, hsp⟩
      exact Or.inl ⟨d, hdD, hd1, hstab⟩
    ·
      refine Or.inr ?_
      intro φ hφ u hu
      have hφlin : ggLin (p := p) M.model φ ∈ M.linGroup := by
        rw [GGQTwoAmbModel.linGroup]
        exact Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
      have huD : (u : G) ∈ D := by
        rcases hu with hux | ⟨y'', K', hnb', huy'⟩
        · rw [hux]; exact hxD
        · rw [huy', hnb'.2.1]
          exact Subgroup.subset_closure (by simp)
      have hu1 : u ≠ 1 := by
        intro h
        rcases hu with hux | ⟨y'', K', hnb', huy'⟩
        · exact hx1 (by rw [← hux, h]; rfl)
        · exact hnb'.1.2.2.1 (by rw [← huy', h]; rfl)
      have hw : M.model (Additive.ofMul u) ∈ Submodule.span (ZMod p) {M.xV, y'} :=
        (hDspan _).mpr ⟨u, huD, rfl⟩
      have hw0 : M.model (Additive.ofMul u) ≠ 0 := by
        intro h
        have h0 : Additive.ofMul u = 0 := M.model.injective (by rw [map_zero]; exact h)
        exact hu1 (Additive.ofMul.injective (by simpa using h0))
      obtain ⟨rlin, hrlin, w', hw', hw'0, hsp⟩ :=
        hcell2 (ggLin (p := p) M.model φ) hφlin (M.model (Additive.ofMul u)) hw hw0
      have hmap : (ggReflGp p Bs).map (ggLin (p := p) M.model) = reflGp M.linGroup :=
        M.reflGp_map hp2
      have hmem : rlin ∈ (ggReflGp p Bs).map (ggLin (p := p) M.model) := by
        rw [hmap]
        exact hrlin
      obtain ⟨ra, hra, hrm⟩ := Subgroup.mem_map.mp hmem
      obtain ⟨d, hdD, hdw⟩ := (hDspan w').mp hw'
      have hd1 : d ≠ 1 := by
        intro h
        apply hw'0
        rw [← hdw, h]
        exact map_zero M.model
      refine ⟨ra, hra, d, hdD, hd1, ?_⟩
      have hsp2 : Submodule.span (ZMod p) {M.model (Additive.ofMul (φ u))} =
          Submodule.span (ZMod p) {M.model (Additive.ofMul (ra d))} := by
        rw [← hdw] at hsp
        rw [← hrm] at hsp
        have hsp' : Submodule.span (ZMod p)
              {((ggLin (p := p) M.model) φ) (M.model (Additive.ofMul u))} =
            Submodule.span (ZMod p)
              {((ggLin (p := p) M.model) ra) (M.model (Additive.ofMul d))} := hsp
        rw [ggLin_apply_ofMul, ggLin_apply_ofMul] at hsp'
        exact hsp'
      exact (M.zpowers_iff_span (φ u) (ra d)).mpr hsp2

end CFSG.StandardType

end
