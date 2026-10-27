module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPmWCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXRes
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishD
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private theorem ggQ2xp_g1_stable {G : Type} [Group G] {Bs : Subgroup G} {x : G} (hx : x ∈ Bs)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers x) {φ : MulAut ↥Bs}
    (hφu : φ u ∈ Subgroup.zpowers u) :
    φ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hφu
  have hxmem : x ∈ Subgroup.zpowers (u : G) := by
    rw [hu]
    exact Subgroup.mem_zpowers x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hux : (⟨x, hx⟩ : ↥Bs) = u ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, hk]
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨r, ?_⟩
  calc (⟨x, hx⟩ : ↥Bs) ^ r = (u ^ k) ^ r := by rw [hux]
    _ = u ^ (k * r) := (zpow_mul u k r).symm
    _ = u ^ (r * k) := by rw [mul_comm]
    _ = (u ^ r) ^ k := zpow_mul u r k
    _ = (φ u) ^ k := by rw [hr]
    _ = φ (u ^ k) := (map_zpow φ u k).symm
    _ = φ ⟨x, hx⟩ := by rw [← hux]

theorem ggQ2_finrank_of_not_e6Heart {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) [Fact (Nat.Prime 3)] {y : G}
    {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) (M : GGQTwoModel 3 Bs x y D L J K)
    (hE6 : ¬ M.toLin.E6Heart) :
    FiniteDimensional (ZMod 3) M.V ∧ 4 ≤ Module.finrank (ZMod 3) M.V ∧ M.xV ≠ 0 ∧
      Module.finrank (ZMod 3) M.V = Fintype.card {k // k ≠ M.a} + 1 := by
  have hx0 : M.xV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1' : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hS.1.1.1.2.2.2.2.2.2.1.2.2.1 (Subtype.ext_iff.mp h1')
  have hy0 : M.yV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨y, M.hy⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1' : (⟨y, M.hy⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hnb.1.2.2.1 (Subtype.ext_iff.mp h1')
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hcard_bs : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
      _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) M.V := (FiniteField.pow_finrank_eq_natCard 3 M.V).symm
  have h4 : 4 ≤ Module.finrank (ZMod 3) M.V := by
    have hp4 : 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    rw [hcard_bs] at hp4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp4
  have hfd : FiniteDimensional (ZMod 3) M.V := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional (ZMod 3) M.toLin.V := hfd
  have h1 := GGQ2Lin.card_le_finrank_of_not_e6Heart M.toLin hE6 hx0 hy0 (ggQ2_fixed_lin M).1
    (ggQ2_fixed_lin M).2
  have h2 := GGQ2Lin.finrank_le_card_add_one_of_fix M.toLin M.xV (ggQ2_fixed_lin M).1
  have h3 : Fintype.card M.ι = 1 + Fintype.card {k // k ≠ M.a} := by
    rw [Fintype.card_eq_sum_ones, Fintype.card_eq_sum_ones (α := {k // k ≠ M.a}),
      Fintype.sum_eq_add_sum_subtype_ne _ M.a]
  change Fintype.card M.ι ≤ Module.finrank (ZMod 3) M.V at h1
  change Module.finrank (ZMod 3) M.V ≤ Fintype.card {k // k ≠ M.a} + 1 at h2
  exact ⟨hfd, h4, hx0, by omega⟩

theorem ggQ2_xV_coroots_span_of_not_e6Heart {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) [Fact (Nat.Prime 3)] {y : G}
    {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) (M : GGQTwoModel 3 Bs x y D L J K)
    (hE6 : ¬ M.toLin.E6Heart)
    (hdet0 : ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
      (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod 3) ≠ 0) :
    Submodule.span (ZMod 3) (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ := by
  classical
  obtain ⟨hfd, -, hx0, hdimeq⟩ := ggQ2_finrank_of_not_e6Heart hS hnb M hE6
  have hxα : ∀ j : {k // k ≠ M.a}, M.root j M.xV = 0 :=
    GGQ2Lin.root_eq_zero_of_fix rfl M.toLin M.xV (ggQ2_fixed_lin M).1
  have hdet' : ((Int.castRingHom (ZMod 3)).mapMatrix
      (M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι)))).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact hdet0
  have hker0 : ∀ κ : {k // k ≠ M.a} → ZMod 3,
      (∀ i : {k // k ≠ M.a}, ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0) →
        κ = 0 := by
    intro κ hκ
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet' (funext fun i => ?_)
    simpa [Matrix.mulVec, dotProduct] using hκ i
  have hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ M.a} => M.coroot i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgk : ∀ i : {k // k ≠ M.a},
        ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * g j = 0 := by
      intro i
      have h := congrArg (M.root i) hg
      simp only [map_sum, map_smul, smul_eq_mul, M.pairing, map_zero] at h
      simpa only [mul_comm] using h
    exact congrFun (hker0 g hgk)
  have hxs : M.xV ∉
      Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
    intro hmem
    obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3)).mp hmem
    have hκk : ∀ i : {k // k ≠ M.a},
        ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0 := by
      intro i
      have h := hxα i
      rw [← hκ, map_sum] at h
      simpa only [map_smul, smul_eq_mul, M.pairing, mul_comm] using h
    apply hx0
    rw [← hκ, hker0 κ hκk]
    simp
  have hspan := (hind.option hxs).span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_option, hdimeq])
  rw [Option.range_eq] at hspan
  exact hspan

theorem ggQ2_gammaX_of_detModel_of_not_e6Heart (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : GGQTwoI1 Bs D J) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) (hE6 : ¬ M.toLin.E6Heart)
    (hdet0 : ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
      (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) = 0)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers x) :
    GGGammaAt p B Bs x L D J u := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  obtain ⟨hfd, h4, hx0, hdimeq⟩ := ggQ2_finrank_of_not_e6Heart hS hnb M hE6
  have hfix1 := (ggQ2_fixed_lin M).1
  intro φ hφ hφu
  have hφx : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := ggQ2xp_g1_stable M.hx hu hφu
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggQ2_lineStab_normalizes_L hLB hP hH hAJS M.hx hφ hφx
  have hparL : M.parabL {k | k ≠ M.a} = (ggAutomizer L Bs).map (ggLin (p := 3) M.model) := by
    rw [ggQ2_parabL_eq_map, ← M.automizer_L]
  let T : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model φ
  have hTnorm : T ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [hparL]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model)
      (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  have hker : ∃ κ : {k // k ≠ M.a} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {k // k ≠ M.a}, ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0 := by
    have hdet' : ((Int.castRingHom (ZMod 3)).mapMatrix
        (M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
          (fun i : {k // k ≠ M.a} => (i : M.ι)))).det = 0 := by
      rw [← RingHom.map_det]
      exact hdet0
    obtain ⟨κ, hκ0, hκ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
    refine ⟨κ, hκ0, fun i => ?_⟩
    simpa [Matrix.mulVec, dotProduct] using congrFun hκ i
  have hTF : TransvectionFree (M.parabL {k | k ≠ M.a}) := by
    intro g hg htr
    exact ggQ2_transvectionFree M hH.2.2.2.1 g (by
      change g ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
      rw [hparL] at hg
      exact Subgroup.map_mono (ggAutomizer_mono Bs le_top) hg) htr
  obtain ⟨w, hw, ε, -, hwε⟩ : ∃ w ∈ M.parabL {k | k ≠ M.a}, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {M.xV} :=
    GGQ2Lin.pmW_of_ker M.toLin M.xV hx0 hfix1 hker hdimeq.le h4 hTF (Or.inr hdimeq) T hTnorm
  have hw' : T * w * T⁻¹ ∈ M.parabL {k | k ≠ M.a} :=
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
    have hs' : T (w v) = ε • v + s • M.xV := by
      rw [hs]
      abel
    rw [hs']
    exact Submodule.add_mem _ (Submodule.smul_mem _ ε hv)
      (Submodule.smul_mem _ s (Submodule.subset_span (by simp)))
  obtain ⟨ψ, hψ, hD⟩ := ggQ2_xBridge M hnb.2.1 ⟨_, hw', hstab⟩
  exact ggQ2_finishD hLB hP hS hAJS hK1 hnb hφ hψ hD

@[expose] def GGQ2GammaXPosE6Input : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime],
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))) →
    ¬ GGQ2XCovered p B Bs x L D J →
    (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ∀ M : GGQTwoModel p Bs x y D L J K,
      M.toLin.E6Heart) →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers x → GGGammaAt p B Bs x L D J u

theorem ggQ2_gammaXPos_of_e6 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hrest : GGQ2GammaXPosE6Input) : GGQ2GammaXPosInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ hrow hcov u hu
  by_cases hE : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ∃ M : GGQTwoModel p Bs x y D L J K, ¬ M.toLin.E6Heart
  swap
  · exact hrest hS hp hI1 hxL hrow hcov
      (fun y K hnb M => by_contra fun hM => hE ⟨y, K, hnb, M, hM⟩) hu
  obtain ⟨y, K, hnb, M, hME⟩ := hE
  by_cases hdet0 : ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
      (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) = 0
  · exact ggQ2_gammaX_of_detModel_of_not_e6Heart hLB hP h5 hS hp hI1 hnb M hME hdet0 hu
  · subst hp
    exact absurd ⟨y, K, hnb, M, hdet0, ggQ2_xV_coroots_span_of_not_e6Heart hS hnb M hME hdet0⟩
      hcov

end CFSG.StandardType

end
