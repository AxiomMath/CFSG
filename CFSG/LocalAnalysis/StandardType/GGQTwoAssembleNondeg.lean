module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeHL
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeOrbit
public import CFSG.LocalAnalysis.StandardType.GGQTwoCell
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2x_nsmul_model {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

private lemma ggQ2x_zsmul_model {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (n : ℤ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_zsmul n (Additive.ofMul b)

private lemma ggQ2x_zp_span_iff {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (a b : ↥Bs) :
    Subgroup.zpowers a = Subgroup.zpowers b ↔
      Submodule.span (ZMod p) {M.model (Additive.ofMul a)} =
        Submodule.span (ZMod p) {M.model (Additive.ofMul b)} := by
  have key : ∀ c d : ↥Bs, c ∈ Subgroup.zpowers d →
      M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} := by
    intro c d h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← hm, ofMul_zpow]
    rw [ggQ2x_zsmul_model M m d]
    rw [← Int.cast_smul_eq_zsmul (R := ZMod p)]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have key' : ∀ c d : ↥Bs,
      M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} →
      c ∈ Subgroup.zpowers d := by
    intro c d h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨k, hk⟩ := h
    rw [← ZMod.natCast_zmod_val k, Nat.cast_smul_eq_nsmul,
      ← ggQ2x_nsmul_model M k.val d, ← ofMul_pow] at hk
    have h2 : Additive.ofMul (d ^ k.val) = Additive.ofMul c := M.model.injective hk
    have h3 : d ^ k.val = c := Additive.ofMul.injective h2
    rw [← h3]
    exact Subgroup.npow_mem_zpowers d k.val
  constructor
  · intro h
    have hab : a ∈ Subgroup.zpowers b := by rw [← h]; exact Subgroup.mem_zpowers a
    have hba : b ∈ Subgroup.zpowers a := by rw [h]; exact Subgroup.mem_zpowers b
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact key a b hab
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact key b a hba
  · intro h
    have hab : M.model (Additive.ofMul a) ∈
        Submodule.span (ZMod p) {M.model (Additive.ofMul b)} := by
      rw [← h]; exact Submodule.mem_span_singleton_self _
    have hba : M.model (Additive.ofMul b) ∈
        Submodule.span (ZMod p) {M.model (Additive.ofMul a)} := by
      rw [h]; exact Submodule.mem_span_singleton_self _
    refine le_antisymm ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact key' a b hab
    · rw [Subgroup.zpowers_le]
      exact key' b a hba

theorem ggQ2_caseI_nondeg_of_lin {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3) (hLN : GGLNoncyclicInput) (h3 : GGQTwoNoWeylA3) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (M : GGQTwoModel p Bs x y D L J K) (hbas : GGQTwoBasis M)
    (hnd : (M.cartan.det : ZMod p) ≠ 0) : GGQ2Orbit p B Bs x D J := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨hpprime, -, -, -, h4card⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := by omega
  have hNT : GGNoTransvection p Bs := hS.1.2.2.2.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hxD : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Module.Finite (ZMod p) M.V := Module.Finite.of_finite
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
  have hA3 : ¬ (Fintype.card M.toLin.ι = 4 ∧
      Nat.card (M.toLin.parab {k | k ≠ M.toLin.a}) = 24) := by
    rintro ⟨hcard4, hparab⟩
    have hcard4' : Fintype.card M.ι = 4 := by rw [← hcardι]; exact hcard4
    have hparab' : Nat.card (M.parabL {k | k ≠ M.a}) = 24 := hparab
    have hne := h3 G p B Bs x L D J hS y K hnb M hcard4'
    refine hne ?_
    rw [ggQ2_card_L M]
    exact hparab'
  have hHLinput : GGLineStabNormalizesInput := ggLineStabNormalizesInput_of_noncyclic hLN
  have hB := ggQ2_thmB_lin hp M.toLin hbas hnd h4 M.xV (ggQ2_fixed_lin M).1 M.linGroup
    (ggQ2_weyl_le_lin M) (ggQ2_transvectionFree M hNT)
    (ggQ2_HL_lin hHLinput hS M) hA3
  rcases hB with hP3 | hFcell
  ·
    refine Or.inl ⟨⟨x, M.hx⟩, hxD, ?_, ?_⟩
    · intro h
      exact hx1 (congrArg Subtype.val h)
    · rw [ggQ2_orbit_iff M hp2 ⟨x, M.hx⟩]
      intro φ hφ
      obtain ⟨r, hr, hsp⟩ := hP3 φ hφ
      exact ⟨r, hr, hsp⟩
  ·
    rcases ggQ2_cell_lin hp M.toLin hbas hnd M.xV M.yV (ggQ2_fixed_lin M).1 (ggQ2_fixed_lin M).2
        M.linGroup (ggQ2_weyl_le_lin M) (ggQ2_transvectionFree M hNT) hA3 hFcell with
      hcell1 | hcell2
    ·
      obtain ⟨u, hu, hu0, hcell⟩ := hcell1
      obtain ⟨d, hdD, hdu⟩ := (ggQ2_D_eq_span hnb M u).mp hu
      have hd1 : d ≠ 1 := by
        intro h
        apply hu0
        rw [← hdu, h]
        exact map_zero M.model
      have hstab : GGOrbitStableAt p Bs d := by
        rw [ggQ2_orbit_iff M hp2 d]
        intro φ hφ
        obtain ⟨r, hr, hsp⟩ := hcell φ hφ
        rw [hdu]
        exact ⟨r, hr, hsp⟩
      exact Or.inl ⟨d, hdD, hd1, hstab⟩
    ·
      refine Or.inr ?_
      intro φ hφ u hu
      have hφlin : ggLin (p := p) M.model φ ∈ M.linGroup := by
        rw [GGQTwoModel.linGroup]
        exact Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
      have huD : (u : G) ∈ D := by
        rcases hu with hux | ⟨y', K', hnb', huy'⟩
        · rw [hux]; exact hxD
        · rw [huy', hnb'.2.1]
          exact Subgroup.subset_closure (by simp)
      have hu1 : u ≠ 1 := by
        intro h
        rcases hu with hux | ⟨y', K', hnb', huy'⟩
        · exact hx1 (by rw [← hux, h]; rfl)
        · exact hnb'.1.2.2.1 (by rw [← huy', h]; rfl)
      have hw : M.model (Additive.ofMul u) ∈ Submodule.span (ZMod p) {M.xV, M.yV} :=
        (ggQ2_D_eq_span hnb M (M.model (Additive.ofMul u))).mpr ⟨u, huD, rfl⟩
      have hw0 : M.model (Additive.ofMul u) ≠ 0 := by
        intro h
        have h0 : Additive.ofMul u = 0 := M.model.injective (by rw [map_zero]; exact h)
        exact hu1 (Additive.ofMul.injective (by simpa using h0))
      obtain ⟨rlin, hrlin, w', hw', hw'0, hsp⟩ :=
        hcell2 (ggLin (p := p) M.model φ) hφlin (M.model (Additive.ofMul u)) hw hw0
      have hmap : (ggReflGp p Bs).map (ggLin (p := p) M.model) = reflGp M.linGroup :=
        ggQ2_reflGp_map M hp2
      have hmem : rlin ∈ (ggReflGp p Bs).map (ggLin (p := p) M.model) := by
        rw [hmap]
        exact hrlin
      obtain ⟨ra, hra, hrm⟩ := Subgroup.mem_map.mp hmem
      obtain ⟨d, hdD, hdw⟩ := (ggQ2_D_eq_span hnb M w').mp hw'
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
      exact (ggQ2x_zp_span_iff M (φ u) (ra d)).mpr hsp2

end CFSG.StandardType

end
