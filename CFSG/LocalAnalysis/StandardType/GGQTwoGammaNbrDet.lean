module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPmWCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrAt
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishK
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoSwapAB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private theorem ggQ2nd_g1_stable {G : Type} [Group G] {Bs : Subgroup G} {y : G} (hy : y ∈ Bs)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) {φ : MulAut ↥Bs}
    (hφu : φ u ∈ Subgroup.zpowers u) :
    φ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hφu
  have hymem : y ∈ Subgroup.zpowers (u : G) := by
    rw [hu]
    exact Subgroup.mem_zpowers y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hymem
  have huy : (⟨y, hy⟩ : ↥Bs) = u ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, hk]
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨r, ?_⟩
  calc (⟨y, hy⟩ : ↥Bs) ^ r = (u ^ k) ^ r := by rw [huy]
    _ = u ^ (k * r) := (zpow_mul u k r).symm
    _ = u ^ (r * k) := by rw [mul_comm]
    _ = (u ^ r) ^ k := zpow_mul u r k
    _ = (φ u) ^ k := by rw [hr]
    _ = φ (u ^ k) := (map_zpow φ u k).symm
    _ = φ ⟨y, hy⟩ := by rw [← huy]

theorem ggQ2_gammaNbr_of_detModel (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : GGQTwoI1 Bs D J) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) (hb : ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0)
    (hdet0 : ((M.cartan.submatrix (fun i : {k // k ≠ M.b} => (i : M.ι))
      (fun i : {k // k ≠ M.b} => (i : M.ι))).det : ZMod p) = 0)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) :
    GGGammaAt p B Bs x L D J u := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  intro φ hφ hφu
  have hφy : φ ⟨y, M.hy⟩ ∈ Subgroup.zpowers (⟨y, M.hy⟩ : ↥Bs) := ggQ2nd_g1_stable M.hy hu hφu
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
    ggQ2_nbrLineStab_normalizes hLB hP hH hAJS hK1 hnb M.hy hφ hφy
  have hparK : M.parabL {k | k ≠ M.b} = (ggAutomizer K Bs).map (ggLin (p := 3) M.model) := by
    rw [ggQ2_parabL_eq_map, ← M.automizer_K]
  let T : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model φ
  have hTnorm : T ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.b} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [hparK]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model)
      (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  have hfix2 := (ggQ2_fixed_lin M).2
  have hy0 : M.yV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨y, M.hy⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1' : (⟨y, M.hy⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hnb.1.2.2.1 (Subtype.ext_iff.mp h1')
  have hker : ∃ κ : {k // k ≠ M.b} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {k // k ≠ M.b}, ∑ j : {k // k ≠ M.b}, (M.cartan i j : ZMod 3) * κ j = 0 := by
    have hdet' : ((Int.castRingHom (ZMod 3)).mapMatrix
        (M.cartan.submatrix (fun i : {k // k ≠ M.b} => (i : M.ι))
          (fun i : {k // k ≠ M.b} => (i : M.ι)))).det = 0 := by
      rw [← RingHom.map_det]
      exact hdet0
    obtain ⟨κ, hκ0, hκ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
    refine ⟨κ, hκ0, fun i => ?_⟩
    simpa [Matrix.mulVec, dotProduct] using congrFun hκ i
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hcard_bs : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
      _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) M.V := (FiniteField.pow_finrank_eq_natCard 3 M.V).symm
  have h4 : 4 ≤ Module.finrank (ZMod 3) M.V := by
    have hp4 : 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    rw [hcard_bs] at hp4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp4
  have : FiniteDimensional (ZMod 3) M.V := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional (ZMod 3) M.toLin.V := ‹FiniteDimensional (ZMod 3) M.V›
  have hb' : ∃! c, c ≠ M.toLin.b ∧ M.toLin.cartan M.toLin.b c ≠ 0 := hb
  have hdim : Module.finrank (ZMod 3) M.V ≤ Fintype.card {k // k ≠ M.b} + 1 :=
    GGQ2Lin.finrank_le_card_add_one_of_fix (M.toLin.swapAB hb') M.yV hfix2
  have hTF : TransvectionFree (M.parabL {k | k ≠ M.b}) := by
    intro g hg htr
    exact ggQ2_transvectionFree M hH.2.2.2.1 g (by
      change g ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
      rw [hparK] at hg
      exact Subgroup.map_mono (ggAutomizer_mono Bs le_top) hg) htr
  have hx0 : M.xV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1' : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hS.1.1.1.2.2.2.2.2.2.1.2.2.1 (Subtype.ext_iff.mp h1')
  have hpos : LinearIndependent (ZMod 3) (fun i : {k // k ≠ M.b} => M.coroot i) ∨
      Module.finrank (ZMod 3) M.V = Fintype.card {k // k ≠ M.b} + 1 :=
    Or.inr (GGQ2Lin.finrank_eq_card_compl_add_one M.toLin hb' hx0 hy0 (ggQ2_fixed_lin M).1
      hfix2 M.b)
  obtain ⟨w, hw, ε, -, hwε⟩ : ∃ w ∈ M.parabL {k | k ≠ M.b}, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {M.yV} :=
    GGQ2Lin.pmW_of_ker (M.toLin.swapAB hb') M.yV hy0 hfix2 hker hdim h4 hTF hpos T hTnorm
  have hw' : T * w * T⁻¹ ∈ M.parabL {k | k ≠ M.b} :=
    (Subgroup.mem_normalizer_iff.mp hTnorm w).mp hw
  have hstab : ∀ v ∈ Submodule.span (ZMod 3) {M.xV, M.yV},
      (T * w * T⁻¹) (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, M.yV} := by
    intro v hv
    have hTv : (T * w * T⁻¹) (T v) = T (w v) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      congr 2
      exact T.symm_apply_apply v
    change (T * w * T⁻¹) (T v) ∈ _
    rw [hTv]
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (hwε v)
    have hs' : T (w v) = ε • v + s • M.yV := by
      rw [hs]
      abel
    rw [hs']
    exact Submodule.add_mem _ (Submodule.smul_mem _ ε hv)
      (Submodule.smul_mem _ s (Submodule.subset_span (by simp)))
  obtain ⟨ψ, hψ, hD⟩ := ggQ2_yBridge M hnb.2.1 ⟨_, hw', hstab⟩
  exact ggQ2_finishK hLB hP hS hAJS hK1 hnb hφ hψ hD

theorem ggQ2_gammaNbrDetAt_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (P : GGQ2NbrPosPred) : GGQ2GammaNbrDetAt P := by
  intro G _ _ p B Bs x L D J hS hp hI1 _ _ y K hnb _ M hb hdet0 u hu
  exact ggQ2_gammaNbr_of_detModel hLB hP h5 hS hp hI1 hnb M hb hdet0 hu

theorem ggQ2_gammaNbrDet_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaNbrDetInput :=
  ggQ2_detAt_notInL.mpr (ggQ2_gammaNbrDetAt_holds hLB hP h5 GGQ2PosNotInL)

end CFSG.StandardType

end
