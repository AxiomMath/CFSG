module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeOrbit
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegenerate

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2_caseI_deg_of_lin {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) (hbas : GGQTwoBasis M)
    (hdeg : (M.cartan.det : ZMod p) = 0) : GGQ2Orbit p B Bs x D J := by
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Module.Finite (ZMod p) M.V := Module.Finite.of_finite
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  have hNT : GGNoTransvection p Bs := hS.1.2.2.2.1
  have hstdPre : LargeEvenStdSubPre p B x L D J := hS.1.1.2.2.1
  have hxD : x ∈ D := hstdPre.2.2.2.1
  have hSStar : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hcardV : Nat.card M.V = p ^ Fintype.card M.ι := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M.V), Nat.card_zmod, hbas.2]
  have hcardBs : Nat.card ↥Bs = p ^ Fintype.card M.ι :=
    (Nat.card_congr Additive.ofMul).trans
      ((Nat.card_congr M.model.toEquiv).trans hcardV)
  have h4 : 4 ≤ Fintype.card M.ι := by
    apply (Nat.pow_le_pow_iff_right hcfg.tableB_facts.1.one_lt).1
    rw [← hcardBs]
    exact hcfg.tableB_facts.2.2.2.2
  have hbasLin : M.toLin.Basis := hbas
  have hdegLin : (M.toLin.cartan.det : ZMod p) = 0 := hdeg
  have hxfix : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.toLin.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {M.xV} := (ggQ2_fixed_lin M).1
  have hW : M.toLin.weyl ≤ M.linGroup := ggQ2_weyl_le_lin M
  have hTF : TransvectionFree M.linGroup := ggQ2_transvectionFree M hNT
  have hfix := ggQ2_degenerate_lin hp M.toLin hbasLin hdegLin h4 M.xV hxfix M.linGroup hW hTF
  refine Or.inl ⟨(⟨x, M.hx⟩ : ↥Bs), hxD, ?_, ?_⟩
  · intro h
    apply hx1
    have := congrArg (fun t : ↥Bs => (t : G)) h
    simpa using this
  · rw [ggQ2_orbit_iff M (by rw [hp]; norm_num) (⟨x, M.hx⟩ : ↥Bs)]
    intro φ hφ
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    have hmemφ : φ M.xV ∈ Submodule.span (ZMod p) {M.xV} := hfix φ hφ
    have hmeminv : φ⁻¹ M.xV ∈ Submodule.span (ZMod p) {M.xV} :=
      hfix φ⁻¹ (Subgroup.inv_mem _ hφ)
    have hmemx : M.xV ∈ Submodule.span (ZMod p) {φ M.xV} := by
      rw [Submodule.mem_span_singleton] at hmeminv ⊢
      obtain ⟨c, hc⟩ := hmeminv
      refine ⟨c, ?_⟩
      rw [← LinearEquiv.map_smul, hc, ← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    change Submodule.span (ZMod p) {φ M.xV} = Submodule.span (ZMod p) {M.xV}
    exact le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr hmemφ)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hmemx)

end CFSG.StandardType

end
