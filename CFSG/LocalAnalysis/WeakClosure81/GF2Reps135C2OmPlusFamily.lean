module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFamGlue
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFamRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusEight
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusEightAut
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusOuterRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusAut
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQModelPlus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtisComp
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterInvolution
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

open CFSG.LieType.Universal.Spin CFSG.RankThree.GF2n.Smith81.D6Spin in
private theorem w135c2_omfPFam_graphSpin_graphSpin (n : ℕ) (K : Type*) [Field K]
    (i₀ : Fin n) (x : spinGroup (quadPlus n K)) :
    graphSpin n K i₀ (graphSpin n K i₀ x) = x := by
  apply Subtype.ext
  show CliffordAlgebra.map (swapIso n K i₀) (CliffordAlgebra.map (swapIso n K i₀)
    (x : CliffordAlgebra (quadPlus n K))) = x
  exact cliffMap_cliffMap _ (swapIso_swapIso n K i₀) _

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfPFam_mem_L_of_conj {F : Type} [Field F] {n : ℕ} {W : Type}
    [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}
    (hctx : Is135Context Y L) (htY : t ∈ Y) (hZ : Subgroup.center ↥L = ⊥)
    (e : spinGroup (quadPlus n F) ≃* ↥L) {α : MulAut (spinGroup (quadPlus n F))}
    (hα : ∀ s, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹)
    {k : spinGroup (quadPlus n F)} (hk : ∀ g, α g = k * g * k⁻¹) : t ∈ L := by
  refine w135c2_mem_of_conj_eq_conj hctx htY (e k).2 ?_ hZ
  intro l hl
  let s : spinGroup (quadPlus n F) := e.symm ⟨l, hl⟩
  have hes : (e s : MulAut W) = l := by simp [s]
  calc t * l * t⁻¹ = ((e (α s) : ↥L) : MulAut W) := by rw [← hes, ← hα s]
    _ = ((e (k * s * k⁻¹) : ↥L) : MulAut W) := by rw [hk s]
    _ = (e k : MulAut W) * l * (e k : MulAut W)⁻¹ := by simp [hes]

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfPFam_y_data {F : Type} [Field F] {n : ℕ} {W : Type} [CommGroup W]
    [Finite W] {L : Subgroup (MulAut W)} {t : MulAut W} (ht2 : orderOf t = 2)
    (e : spinGroup (quadPlus n F) ≃* ↥L) (htL : t ∈ L) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w)))) :
    ∃ y : spinGroup (quadPlus n F), ((e y : ↥L) : MulAut W) = t ∧ y * y = 1 ∧ ρ y ≠ 1 := by
  have ht : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  let y : spinGroup (quadPlus n F) := e.symm ⟨t, htL⟩
  have hey : e y = ⟨t, htL⟩ := e.apply_symm_apply _
  have hge : ((e y : ↥L) : MulAut W) = t := by rw [hey]
  have hy2 : y * y = 1 := by
    apply e.injective
    rw [map_mul, map_one, hey]
    exact Subtype.ext (by simpa using ht)
  exact ⟨y, hge, hy2, rho_ne_one_of_conj e hθ hge ht2⟩

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfPFam_inner_end {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n) {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (e : spinGroup (quadPlus n F) ≃* ↥L) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {y : spinGroup (quadPlus n F)} (hge : ((e y : ↥L) : MulAut W) = t)
    (hOr : (∃ (σ : MulAut (spinGroup (quadPlus n F))) (β : V ≃+ (Fin n ⊕ Fin n → F)),
        ∀ (g : spinGroup (quadPlus n F)) (v : V),
          β (ρ g v) = spinAction (quadPlus n F) (σ g) (β v)) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1))) :
    W4Lem13_5Concl W Y L t := by
  rcases hOr with ⟨σ, β, hβ⟩ | h4
  · exact w135c2_natural hctx htY ht2 hW
      (w135c2_omPlus_chev2Natural_of_equiv hF hn e hθ σ β hβ)
  · have hle : Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) ≤ 3 := by
      rw [← w135c2_omq_mQuot_eq e hθ hge]
      exact hm
    omega

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfPFam_outer_end {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n) {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (e : spinGroup (quadPlus n F) ≃* ↥L) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (σ : MulAut (spinGroup (quadPlus n F))) (T : V ≃ₗ[ZMod 2] V)
    (hTw : ∀ w : W, θ (t w) = Multiplicative.ofAdd (T (Multiplicative.toAdd (θ w))))
    (hOr : (∃ (β : V ≃+ (Fin n ⊕ Fin n → F)),
        ∀ (g : spinGroup (quadPlus n F)) (v : V),
          β (ρ g v) = spinAction (quadPlus n F) (σ g) (β v)) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (T.toLinearMap - 1))) :
    W4Lem13_5Concl W Y L t := by
  rcases hOr with ⟨β, hβ⟩ | h4
  · exact w135c2_natural hctx htY ht2 hW
      (w135c2_omPlus_chev2Natural_of_equiv hF hn e hθ σ β hβ)
  · have hle := w135c2_four_le_mQuot_of_finrank (t := t) θ T.toLinearMap hTw h4
    omega

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis in
private theorem w135c2_omfPFam_five_inner {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) {n : ℕ} (hn5 : 5 ≤ n)
    (e : spinGroup (quadPlus n F) ≃* ↥L) (hZ : Subgroup.center ↥L = ⊥) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {α : MulAut (spinGroup (quadPlus n F))}
    (hα : ∀ s, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹)
    {h : spinGroup (quadPlus n F)} (hinner : ∀ g, α g = h * g * h⁻¹) :
    W4Lem13_5Concl W Y L t := by
  have hn3 : 3 ≤ n := by omega
  have htL : t ∈ L := w135c2_omfPFam_mem_L_of_conj hctx htY hZ e hα hinner
  obtain ⟨y, hge, hy2, hρy⟩ := w135c2_omfPFam_y_data ht2 e htL hθ
  refine w135c2_omfPFam_inner_end hF hn3 hW hctx htY ht2 hm e hθ hge ?_
  rcases omPlus_two_natural_or_four_le hF hn5 hρ hy2 hρy with ⟨β, hβ⟩ | h4
  · exact Or.inl ⟨MulEquiv.refl _, β, fun g v => by simpa using hβ g v⟩
  · exact Or.inr h4

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfPFam_rho_ne_one {F : Type} [Field F] {n : ℕ} {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (e : spinGroup (quadPlus n F) ≃* ↥L) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w)))) :
    ∃ g, ρ g ≠ 1 := by
  obtain ⟨y, hyL, hy1, hyy, -⟩ := w135c2_psu_outer_involution hW hctx htY ht2
  let s : spinGroup (quadPlus n F) := e.symm ⟨y, hyL⟩
  have hge : ((e s : ↥L) : MulAut W) = y := by simp [s]
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  exact ⟨s, rho_ne_one_of_conj e hθ hge hy2⟩

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.RankThree.GF2n.Smith81.D6Spin in
private theorem w135c2_omfPFam_graph_core {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n) {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (e : spinGroup (quadPlus n F) ≃* ↥L) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {α : MulAut (spinGroup (quadPlus n F))}
    (hα : ∀ s, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹)
    {h : spinGroup (quadPlus n F)}
    (hgraph : ∀ g, α g = h * graphSpin n F ⟨n - 1, by omega⟩ g * h⁻¹) :
    ∃ T : V ≃ₗ[ZMod 2] V,
      (∀ w : W, θ (t w) = Multiplicative.ofAdd (T (Multiplicative.toAdd (θ w)))) ∧
      ((∃ β : V ≃+ (Fin n ⊕ Fin n → F),
          ∀ (g : spinGroup (quadPlus n F)) (v : V),
            β (ρ g v) = spinAction (quadPlus n F) g (β v)) ∨
        4 ≤ Module.finrank (ZMod 2) (LinearMap.range (T.toLinearMap - 1))) := by
  have hn3 : 3 ≤ n := by omega
  have ht : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have hα2 : α * α = 1 := w135c2_mulAut_mul_self_of_conj e ht hα
  obtain ⟨T, hTw, hT⟩ := w135c2_exists_linearEquiv_of_conj e hθ hα
  have hgon : Subgroup.center (spinGroup (quadPlus n F)) = ⊥ :=
    CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (n := n) (K := F) hn3
  have hβg : ∀ g : spinGroup (quadPlus n F),
      graphSpin n F ⟨n - 1, by omega⟩ (graphSpin n F ⟨n - 1, by omega⟩ g) = g :=
    fun g => w135c2_omfPFam_graphSpin_graphSpin n F ⟨n - 1, by omega⟩ g
  have hh : h * graphSpin n F ⟨n - 1, by omega⟩ h = 1 :=
    w135c2_mul_apply_eq_one_of_mul_self hgon hα2 hβg hgraph
  have hρ1 : ∃ g, ρ g ≠ 1 := w135c2_omfPFam_rho_ne_one hW hctx htY ht2 e hθ
  have hT' : ∀ g v, T (ρ g v) =
      ρ (h * graphSpin n F ⟨n - 1, by omega⟩ g * h⁻¹) (T v) :=
    fun g v => by rw [← hgraph g]; exact hT g v
  rcases omPlus_two_outer_natural_or_four_le hF hn hρ hρ1 T hh hT' with hnat | h4
  · exact ⟨T, hTw, Or.inl hnat⟩
  · exact ⟨T, hTw, Or.inr h4⟩

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.RankThree.GF2n.Smith81.D6Spin in
private theorem w135c2_omfPFam_five_graph {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) {n : ℕ} (hn5 : 5 ≤ n)
    (e : spinGroup (quadPlus n F) ≃* ↥L) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {α : MulAut (spinGroup (quadPlus n F))}
    (hα : ∀ s, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹)
    {h : spinGroup (quadPlus n F)}
    (hgraph : ∀ g, α g = h * graphSpin n F ⟨n - 1, by omega⟩ g * h⁻¹) :
    W4Lem13_5Concl W Y L t := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨T, hTw, hOr⟩ :=
    w135c2_omfPFam_graph_core hF (by omega : 4 ≤ n) hW hctx htY ht2 e hρ hθ hα hgraph
  exact w135c2_omfPFam_outer_end hF hn3 hW hctx htY ht2 hm e hθ (MulEquiv.refl _) T hTw hOr

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis in
private theorem w135c2_omfPFam_five_le {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) {n : ℕ} (hn5 : 5 ≤ n)
    (e : spinGroup (quadPlus n F) ≃* ↥L) (hZ : Subgroup.center ↥L = ⊥) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w)))) :
    W4Lem13_5Concl W Y L t := by
  obtain ⟨α, hα⟩ := w135c2_exists_mulAut_of_mem hctx htY e
  obtain ⟨h, hinner | hgraph⟩ := omPlus_two_aut_inner_or_graph (n := n) hn5 hF α
  · exact w135c2_omfPFam_five_inner hW hctx htY ht2 hm hF hn5 e hZ hρ hθ hα hinner
  · exact w135c2_omfPFam_five_graph hW hctx htY ht2 hm hF hn5 e hρ hθ hα hgraph

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis in
private theorem w135c2_omfPFam_four_inner {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) (e : spinGroup (quadPlus 4 F) ≃* ↥L)
    (hZ : Subgroup.center ↥L = ⊥) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} (hρ : IsSimpleRep ρ)
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus 4 F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {α : MulAut (spinGroup (quadPlus 4 F))}
    (hα : ∀ s, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹)
    {θ₀ : MulAut (spinGroup (quadPlus 4 F))} {h : spinGroup (quadPlus 4 F)}
    (hinner : ∀ g, θ₀ (α (θ₀.symm g)) = h * g * h⁻¹) :
    W4Lem13_5Concl W Y L t := by
  have hinner' : ∀ g, α g = θ₀.symm h * g * (θ₀.symm h)⁻¹ := by
    intro g
    have h1 : θ₀ (α g) = h * θ₀ g * h⁻¹ := by simpa using hinner (θ₀ g)
    have h2 := congrArg θ₀.symm h1
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using h2
  have htL : t ∈ L := w135c2_omfPFam_mem_L_of_conj hctx htY hZ e hα hinner'
  obtain ⟨y, hge, hy2, hρy⟩ := w135c2_omfPFam_y_data ht2 e htL hθ
  refine w135c2_omfPFam_inner_end hF (by norm_num : 3 ≤ 4) hW hctx htY ht2 hm e hθ hge ?_
  exact omPlus8_two_natural_or_four_le hF hρ hy2 hρy

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.RankThree.GF2n.Smith81.D6Spin in
private theorem w135c2_omfPFam_four_graph {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) (e : spinGroup (quadPlus 4 F) ≃* ↥L) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} (hρ : IsSimpleRep ρ)
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus 4 F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {α : MulAut (spinGroup (quadPlus 4 F))}
    (hα : ∀ s, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹)
    {θ₀ : MulAut (spinGroup (quadPlus 4 F))} {h : spinGroup (quadPlus 4 F)}
    (hgraph : ∀ g, θ₀ (α (θ₀.symm g)) = h * graphSpin 4 F ⟨3, by norm_num⟩ g * h⁻¹) :
    W4Lem13_5Concl W Y L t := by
  let e' : spinGroup (quadPlus 4 F) ≃* ↥L := θ₀.symm.trans e
  let ρ' : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V := ρ.comp θ₀.symm.toMonoidHom
  let α' : MulAut (spinGroup (quadPlus 4 F)) := (θ₀.symm.trans α).trans θ₀
  have hρ' : IsSimpleRep ρ' := isSimpleRep_comp_mulEquiv hρ θ₀.symm
  have hθ' : ∀ (s : spinGroup (quadPlus 4 F)) (w : W),
      θ ((e' s : MulAut W) w) = Multiplicative.ofAdd (ρ' s (Multiplicative.toAdd (θ w))) := by
    intro s w
    simpa [e', ρ', MulEquiv.trans_apply] using hθ (θ₀.symm s) w
  have hα' : ∀ s, ((e' (α' s) : ↥L) : MulAut W) = t * (e' s : MulAut W) * t⁻¹ := by
    intro s
    simpa [e', α', MulEquiv.trans_apply] using hα (θ₀.symm s)
  have hgraph' : ∀ g, α' g = h * graphSpin 4 F ⟨4 - 1, by omega⟩ g * h⁻¹ := by
    intro g
    simpa [α', MulEquiv.trans_apply] using hgraph g
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨T, hTw, hOr⟩ :=
    w135c2_omfPFam_graph_core hF (by norm_num : 4 ≤ 4) hW hctx htY ht2 e' hρ' hθ' hα' hgraph'
  refine w135c2_omfPFam_outer_end hF hn3 hW hctx htY ht2 hm e hθ θ₀ T hTw ?_
  rcases hOr with ⟨β, hβ⟩ | h4
  · exact Or.inl ⟨β, fun g v => by simpa [ρ'] using hβ (θ₀ g) v⟩
  · exact Or.inr h4

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis in
private theorem w135c2_omfPFam_four {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) (e : spinGroup (quadPlus 4 F) ≃* ↥L)
    (hZ : Subgroup.center ↥L = ⊥) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} (hρ : IsSimpleRep ρ)
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus 4 F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {α : MulAut (spinGroup (quadPlus 4 F))}
    (hα : ∀ s, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹) :
    W4Lem13_5Concl W Y L t := by
  have ht : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have hα2 : α * α = 1 := w135c2_mulAut_mul_self_of_conj e ht hα
  obtain ⟨θ₀, h, hinner | hgraph⟩ := omPlus8_two_aut_inner_or_graph hF α hα2
  · exact w135c2_omfPFam_four_inner hW hctx htY ht2 hm hF e hZ hρ hθ hα hinner
  · exact w135c2_omfPFam_four_graph hW hctx htY ht2 hm hF e hρ hθ hα hgraph

theorem w135c2_omPlus_two
    {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 1) : W4Lem13_5Concl W Y L t := by
  classical
  have hn4 : 4 ≤ n := (LieModel.admissible hlie).2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨F, instF, instFin, instChar, hF, hZ, ⟨e⟩⟩ := w135c2_omPlus_model hctx hn3 hlie
  let instField : Field F := instF
  let instFiniteF : Finite F := instFin
  let instCharP : CharP F 2 := instChar
  have hF2 : Nat.card F = 2 := by simpa using hF
  obtain ⟨V, _, _, hVfin, ρ, θ, hρ, hθ⟩ := cu_binModel hW hctx.2.2.2.2.2 e
  let instFiniteV : Finite V := hVfin
  by_cases hn5 : 5 ≤ n
  · exact w135c2_omfPFam_five_le hW hctx htY ht2 hm hF2 hn5 e hZ hρ hθ
  · have hn_eq : n = 4 := by omega
    subst n
    obtain ⟨α, hα⟩ := w135c2_exists_mulAut_of_mem hctx htY e
    exact w135c2_omfPFam_four hW hctx htY ht2 hm hF2 e hZ hρ hθ hα

end CFSG.LocalAnalysis.WeakClosure81
