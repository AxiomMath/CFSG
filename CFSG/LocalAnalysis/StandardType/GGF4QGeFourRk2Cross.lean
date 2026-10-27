module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk1
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt
import CFSG.LieType.Universal.Spin.Twisted.Datum
import CFSG.LieType.Steinberg.Classical.SpinFrame.Weyl
import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOne
import CFSG.Adapters.SpecialLinearPerfect
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import CFSG.LieType.BorelTits.LeviOrder
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

private theorem ggPres_conj_conj {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (w w' t : M.Group) :
    (↑(e (w * w'⁻¹)) : MulAut ↥Bs) * ↑(e (w' * t * w'⁻¹)) * (↑(e (w * w'⁻¹)))⁻¹ =
      (↑(e (w * t * w⁻¹)) : MulAut ↥Bs) := by
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
  congr 1
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

private theorem cartanC_three_eq : Symplectic.cartanC 3 = CartanMatrix.B 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem isQuasisimple_range_of_sl2 {G : Type} [Group G] {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) {θ : Matrix.SpecialLinearGroup (Fin 2) F →* G}
    (hθinj : Function.Injective θ) : CFSG.Assembly.IsQuasisimple ↥θ.range := by
  have hSL : CFSG.Assembly.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨(CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4).commutator_eq_top,
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hθinj).symm hSL

section Inputs

theorem ggF4QGeFourCross_of_rePair {row : GGF4QGeFourRow} (hL1 : GGF4QGeFourL1Input row)
    (hRk2 : GGF4QGeFourRk2Input row)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hp : p ∣ 2 ^ f - 1) (hrow : GGF4QGeFourRowHyp row f L K)
    {X Y Z : Subgroup G} (hX : X = L ∨ X = K) (hY : Y = L ∨ Y = K) (hZ : Z = L ∨ Z = K)
    {w w' : CoxeterMatrix.F₄.Group} {i j : Fin 4} (hij : CoxeterMatrix.F₄ i j = 3)
    (hi : (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs)
    (hi' : (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs)
    (hj' : (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
      LinearBlockStandardPair F W
        (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)))
        (ggRankOneIn Y Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹))) := by
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  have hL1' := hL1 G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow
  obtain ⟨F, _, _, W, hF2, hW⟩ :=
    (hRk2 G p B Bs x L D J y K hcfg e hpres f hf hp hrow Z hZ w' i j hi' hj').2.1 hij
  rw [← hL1' Z hZ _ hi' ⟨w', i, rfl⟩, ← hL1' Z hZ _ hj' ⟨w', j, rfl⟩] at hW
  obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (hAH (e (w * w'⁻¹)).2)
  have hW' := ggLinearBlockPair_map_conj hW g
  rw [ggRankOnePerf_map_conj hg, ggRankOnePerf_map_conj hg, ggPres_conj_conj e w w',
    ggPres_conj_conj e w w', hL1' X hX _ hi ⟨w, i, rfl⟩, hL1' Y hY _ hj ⟨w, j, rfl⟩] at hW'
  exact ⟨F, inferInstance, inferInstance, _, hF2, hW'⟩

@[expose] def GGF4QGeFourRk2MissedInput (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    GGSecFiveRouteCfg p B Bs x L D J {K} →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      (row = .S2 → GGCentralImage .POmegaMinus 4 f K) →
      ∀ X Y : Subgroup G, (X = L ∧ Y = K ∨ X = K ∧ Y = L) →
      ∀ (w : CoxeterMatrix.F₄.Group) (i j : Fin 4), CoxeterMatrix.F₄ i j = 3 →
        (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
        (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs →
        (∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup G), (Z = L ∨ Z = K) →
          (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs →
          (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∉ ggAutomizer Z Bs) →
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
            LinearBlockStandardPair F W
              (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)))
              (ggRankOneIn Y Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)))

theorem coxeterMatrix_POmegaMinus_four (f : ℕ) :
    coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType = CoxeterMatrix.B 3 := by
  have hC : GGIntCartan (CoxeterMatrix.B 3) (Spin.cartanB 3) := by
    rw [Spin.cartanB_eq]
    exact ggIntCartan_C 3
  exact coxeterMatrix_eq_of_ggIntCartan _ hC

theorem exists_coxeterMatrix_PSU_six {f : ℕ} (hf : 1 ≤ f) :
    ∃ σ : Fin 3 ≃ Fin (ggU .PSU 6 f).D.rank, (∀ k, (σ k).val = k.val) ∧
      ∀ k l, coxeterMatrix (ggU .PSU 6 f).D.isFiniteType (σ k) (σ l) = CoxeterMatrix.B 3 k l := by
  have e : ggU .PSU 6 f =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf) 6⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [e]
  refine ⟨Equiv.refl _, fun k => rfl, fun k l => ?_⟩
  have hC : GGIntCartan (CoxeterMatrix.B 3) (Unitary.cartan 6) := by
    rw [show Unitary.cartan 6 = Symplectic.cartanC 3 from if_pos (by decide), cartanC_three_eq]
    exact ggIntCartan_B 3
  have h := coxeterMatrix_eq_of_ggIntCartan (Unitary.isFiniteType_cartan 6) hC
  change coxeterMatrix (Unitary.isFiniteType_cartan 6) k l = _
  rw [h]

theorem ggF4QGeFour_rePair_S2_PSU (hL1 : GGF4QGeFourL1Input .S2)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hp : p ∣ 2 ^ f - 1) (hrow : GGF4QGeFourRowHyp .S2 f L K)
    (hL : GGTableBPosImage p Bs .POmegaMinus 4 f L) (hK : GGTableBPosImage p Bs .PSU 6 f K)
    {i j : Fin 4} (hij : CoxeterMatrix.F₄ i j = 3) :
    ∃ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup G), (Z = L ∨ Z = K) ∧
      (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs ∧
      (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs := by
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  have hL1' := hL1 G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow
  have hf1 : 1 ≤ f := by omega
  obtain ⟨ψL, hkerL, -, εL, hεL, hlevL, -⟩ := hL
  have hML : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  obtain ⟨φL, hφL, haR, ha01, ha12, ha02, haL⟩ :=
    exists_f4Triple_map_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_left εL hεL (Equiv.refl _) hML
  obtain ⟨ψK, hkerK, -, εK, hεK, hlevK, -⟩ := hK
  obtain ⟨σK, hσK, hMK⟩ := exists_coxeterMatrix_PSU_six hf1
  obtain ⟨φK, hφK, hbR, hb01, hb12, hb02, hbK⟩ :=
    exists_f4Triple_map_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_right εK hεK σK hMK
  set a : Fin 3 → CoxeterMatrix.F₄.Group :=
    fun k => φL ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
      ((Equiv.refl (Fin 3)) k)) with ha
  set b : Fin 3 → CoxeterMatrix.F₄.Group :=
    fun k => φK ((coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple (σK k)) with hb
  have hcoxRefl : ∀ t : CoxeterMatrix.F₄.Group, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection t →
      (↑(e t) : MulAut ↥Bs) ∈ ggCoxRefl CoxeterMatrix.F₄ e := by
    rintro t ⟨u, k, rfl⟩
    exact ⟨u, k, by rw [CoxeterMatrix.toCoxeterSystem_simple]⟩
  obtain ⟨FL, _, _, θL, -, hθL, hθLr, hcL⟩ :=
    exists_sl2_ggRankOneIn_node_POmegaMinus hf1 hkerL hlevL 1 ((Equiv.refl (Fin 3)) 0)
  obtain ⟨FK, _, _, θK, -, hθK, hθKr, hcK⟩ :=
    exists_sl2_ggRankOneIn_node_PSU hf1 hkerK hlevK 1 (σK 0)
  simp only [one_mul, inv_one, mul_one] at hθLr hθKr
  have hcardL : Nat.card (ggRankOnePerf Bs ↑(e (a 0))) = Nat.card SL(2, FL) := by
    have hmem : (↑(e (a 0)) : MulAut ↥Bs) ∈ ggAutomizer L Bs := by
      rw [hφL]; exact (εL _).2
    rw [hL1' L (Or.inl rfl) _ hmem (hcoxRefl _ (haR 0)), hφL, ← hθLr]
    exact (Nat.card_congr (MonoidHom.ofInjective hθL).toEquiv).symm
  have hcardK : Nat.card (ggRankOnePerf Bs ↑(e (b 0))) = Nat.card SL(2, FK) := by
    have hmem : (↑(e (b 0)) : MulAut ↥Bs) ∈ ggAutomizer K Bs := by
      rw [hφK]; exact (εK _).2
    rw [hL1' K (Or.inr rfl) _ hmem (hcoxRefl _ (hbR 0)), hφK, ← hθKr]
    exact (Nat.card_congr (MonoidHom.ofInjective hθK).toEquiv).symm
  have hcL' : Nat.card FL = 2 ^ f := by rw [hcL]; rfl
  have hcK' : Nat.card FK = 2 ^ (2 * f) := by rw [hcK, hσK]; rfl
  have hnc : ∀ u : CoxeterMatrix.F₄.Group, u * a 0 * u⁻¹ ≠ b 0 := by
    intro u hu
    obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (hAH (e u).2)
    have hconj : (↑(e u) : MulAut ↥Bs) * ↑(e (a 0)) * (↑(e u))⁻¹ = ↑(e (b 0)) := by
      rw [← hu, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv,
        ← map_mul, ← map_mul]
    have h1 := ggRankOnePerf_map_conj hg (↑(e (a 0)) : MulAut ↥Bs)
    rw [hconj] at h1
    have h2 : Nat.card (ggRankOnePerf Bs ↑(e (b 0))) = Nat.card (ggRankOnePerf Bs ↑(e (a 0))) := by
      rw [← h1]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    rw [hcardL, hcardK] at h2
    have h3 := ggSL2_card_inj h2
    rw [hcK', hcL'] at h3
    have h4 := Nat.pow_right_injective (le_refl 2) h3
    omega
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hsimp : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k; rw [hRs k, CoxeterMatrix.toCoxeterSystem_simple]
  have haR' : ∀ k, R.IsRefl (a k) := fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (haR k)
  have hbR' : ∀ k, R.IsRefl (b k) := fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hbR k)
  have haL' : ∀ z, z ∈ Subgroup.closure (Set.range a) ↔
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs := haL
  have hbK' : ∀ z, z ∈ Subgroup.closure (Set.range b) ↔
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer K Bs := hbK
  have hin : ∀ (c : Fin 3 → CoxeterMatrix.F₄.Group) (Z : Subgroup G) (w' : CoxeterMatrix.F₄.Group),
      (∀ z, z ∈ Subgroup.closure (Set.range c) ↔
        ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs) →
      w' * R.s i * w'⁻¹ ∈ Subgroup.closure (Set.range c) →
      w' * R.s j * w'⁻¹ ∈ Subgroup.closure (Set.range c) →
      (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs ∧
      (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs := by
    intro c Z w' hc h1 h2
    rw [hsimp] at h1 h2
    exact ⟨(hc _).mp h1, (hc _).mp h2⟩
  have hij' : ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ∨ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
    fin_cases i <;> fin_cases j <;> first | decide | exact absurd hij (by decide)
  obtain ⟨ga, hga | hga⟩ := R.classify (haR' 0) (haR' 1) (haR' 2) ha01 ha12 ha02 <;>
    obtain ⟨gb, hgb | hgb⟩ := R.classify (hbR' 0) (hbR' 1) (hbR' 2) hb01 hb12 hb02
  ·
    exfalso
    apply hnc (gb⁻¹ * ga)
    rw [show gb⁻¹ * ga * a 0 * (gb⁻¹ * ga)⁻¹ = gb⁻¹ * (ga * a 0 * ga⁻¹) * gb by group, hga.1,
      ← hgb.1]
    group
  ·
    rcases hij' with h01 | h23
    · have h23 : ¬ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
        rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      obtain ⟨w', h1, h2⟩ := R.exists_conj_of_B hga h23
      exact ⟨w', L, Or.inl rfl, hin a L w' haL' h1 h2⟩
    · have h01 : ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
        rcases h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      obtain ⟨w', h1, h2⟩ := R.exists_conj_of_C hgb h01
      exact ⟨w', K, Or.inr rfl, hin b K w' hbK' h1 h2⟩
  ·
    rcases hij' with h01 | h23
    · have h23 : ¬ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
        rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      obtain ⟨w', h1, h2⟩ := R.exists_conj_of_B hgb h23
      exact ⟨w', K, Or.inr rfl, hin b K w' hbK' h1 h2⟩
    · have h01 : ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
        rcases h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      obtain ⟨w', h1, h2⟩ := R.exists_conj_of_C hga h01
      exact ⟨w', L, Or.inl rfl, hin a L w' haL' h1 h2⟩
  ·
    exfalso
    apply hnc (gb⁻¹ * ga)
    rw [show gb⁻¹ * ga * a 0 * (gb⁻¹ * ga)⁻¹ = gb⁻¹ * (ga * a 0 * ga⁻¹) * gb by group, hga.1,
      ← hgb.1]
    group

theorem ggF4QGeFourRk2CrossInput_S2_of_missed (hKG : GGF4QGeFourKGPosInput .S2)
    (hL1 : GGF4QGeFourL1Input .S2) (hRk2 : GGF4QGeFourRk2Input .S2)
    (hM : GGF4QGeFourRk2MissedInput .S2) : GGF4QGeFourRk2CrossInput .S2 := by
  intro G _ _ p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow X Y hXY w i j hij hi hj
  have hX : X = L ∨ X = K := by
    rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hY : Y = L ∨ Y = K := by
    rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases hmiss : ∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup G), (Z = L ∨ Z = K) →
      (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs →
      (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∉ ggAutomizer Z Bs
  · have hpos := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
    rcases hpos.2 with hKpsu | hKom
    · exfalso
      obtain ⟨w', Z, hZ, h1, h2⟩ :=
        ggF4QGeFour_rePair_S2_PSU hL1 hcfg hRC e hpres hf hp hrow hpos.1 hKpsu hij
      exact hmiss w' Z hZ h1 h2
    · obtain ⟨ψ, hker, hrange, -⟩ := hKom
      have hadm : StatedLieAdmissible .POmegaMinus 4 2 f := ⟨Nat.prime_two, by omega, le_rfl⟩
      exact hM G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow
        (fun _ => ⟨ψ, hadm, hker, hrange⟩) X Y hXY w i j hij hi hj hmiss
  · push Not at hmiss
    obtain ⟨w', Z, hZ, h1, h2⟩ := hmiss
    exact ggF4QGeFourCross_of_rePair hL1 hRk2 hcfg hRC e hpres hf hp hrow hX hY hZ hij hi hj h1 h2

theorem isQuasisimple_ggRankOneIn_of_tableBPosImage_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {f : ℕ} (hf : 2 ≤ f) (hX : GGTableBPosImage p Bs .PSp 3 f X)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs r) := by
  obtain ⟨F, _, _, θ, -, hθinj, hθ, hcard⟩ :=
    exists_sl2_ggRankOneIn_of_tableBPosImage_PSp hp hp2 hEl hNT (by omega) hX hrA hr
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [← hθ]
  exact isQuasisimple_range_of_sl2 h4 hθinj

@[expose] def GGF4QGeFourS1ThirdInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp .S1 f L K →
      ∀ X Y : Subgroup G, (X = L ∧ Y = K ∨ X = K ∧ Y = L) →
      ∀ (w : CoxeterMatrix.F₄.Group) (i j : Fin 4), CoxeterMatrix.F₄ i j = 3 →
        (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
        (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs →
        (∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup G), Z = L ∨ Z = K →
          (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs →
          (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∉ ggAutomizer Z Bs) →
          ∃ (z : G) (A : Subgroup G), z ∈ Bs ∧
            CFSG.Assembly.IsComponentOf A (Subgroup.centralizer ({z} : Set G)) ∧
            Bs ≤ Subgroup.normalizer (A : Set G) ∧
            ggAutomizer A Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs ∧
            GGTableBPosImage p Bs .PSp 3 f A ∧
            (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer A Bs ∧
            (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer A Bs

theorem ggF4QGeFourRk2Missed_S1_of_third (hKG : GGF4QGeFourKGPosInput .S1)
    (hThird : GGF4QGeFourS1ThirdInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
      ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
        GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
      ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp .S1 f L K →
        ∀ X Y : Subgroup G, (X = L ∧ Y = K ∨ X = K ∧ Y = L) →
        ∀ (w : CoxeterMatrix.F₄.Group) (i j : Fin 4), CoxeterMatrix.F₄ i j = 3 →
          (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
          (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs →
          (∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup G), Z = L ∨ Z = K →
            (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs →
            (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∉ ggAutomizer Z Bs) →
            ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
              LinearBlockStandardPair F W
                (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)))
                (ggRankOneIn Y Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹))) := by
  intro G _ _ p B Bs x L D J y K hcfg e hpres f hf hp hrow X Y hXY w i j hij hi hj hmiss
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hodd : Odd p := hpp.odd_of_ne_two hp2
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hpos := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  obtain ⟨hDB, -, -, hxD, -⟩ := hcfg.1.1.2.2.1
  have hxB : x ∈ Bs := hcfg.1.1.2.1.1 (hDB hxD)
  have hyB : y ∈ Bs := by
    refine hcfg.1.1.2.1.1 (hDB ?_)
    rw [hcfg.2.2.2.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmem : ∀ Z : Subgroup G, Z = L ∨ Z = K → ∃ z, z ∈ Bs ∧
      CFSG.Assembly.IsSubnormal Z (Subgroup.centralizer ({z} : Set G)) ∧
      GGTableBPosImage p Bs .PSp 3 f Z := by
    rintro Z (rfl | rfl)
    · exact ⟨x, hxB, hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1, hpos.1⟩
    · exact ⟨y, hyB, hcfg.2.2.2.1.2.2.2.2.1.2.1, hpos.2⟩
  have hXm : X = L ∨ X = K := by rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hYm : Y = L ∨ Y = K := by rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  obtain ⟨xX, hxXB, hXx, hXpos⟩ := hmem X hXm
  obtain ⟨yY, hyYB, hYy, hYpos⟩ := hmem Y hYm
  have hrefl : ∀ (v : CoxeterMatrix.F₄.Group) (k : Fin 4), GGIsReflection p
      ((e (v * CoxeterMatrix.F₄.simple k * v⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) :=
    fun v k => ggCoxRefl_isReflection hpres.2 ⟨v, k, rfl⟩
  have hq : ∀ Z : Subgroup G, GGTableBPosImage p Bs .PSp 3 f Z →
      ∀ (v : CoxeterMatrix.F₄.Group) (k : Fin 4),
        ((e (v * CoxeterMatrix.F₄.simple k * v⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) ∈ ggAutomizer Z Bs →
        CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn Z Bs
          ((e (v * CoxeterMatrix.F₄.simple k * v⁻¹) :
            ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)) :=
    fun Z hZpos v k hk =>
      isQuasisimple_ggRankOneIn_of_tableBPosImage_PSp hpp hp2 hEl hNT hf hZpos hk (hrefl v k)
  obtain ⟨z, A, hzB, hA, hBA, hAW, hApos, hrA, hr'A⟩ :=
    hThird G p B Bs x L D J y K hcfg e hpres f hf hp hrow X Y hXY w i j hij hi hj hmiss
  obtain ⟨F, hFf, hFfin, W₀, hF2, hW₀⟩ :=
    (ggF4QGeFourRk2_of_tableBPos_PSp hpp hp2 hEl hNT hAind hpres hAW hf hApos w i j hrA
      hr'A).2.1 hij
  have hSX := ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hxXB hzB hXx hA.2.1 hBA hi hrA
    (hq X hXpos w i hi) (hq A hApos w i hrA) (hrefl w i).1
    (GGIsReflection.ne_one hpp (hrefl w i))
  have hSY := ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hyYB hzB hYy hA.2.1 hBA hj hr'A
    (hq Y hYpos w j hj) (hq A hApos w j hr'A) (hrefl w j).1
    (GGIsReflection.ne_one hpp (hrefl w j))
  refine ⟨F, hFf, hFfin, W₀, hF2, ?_⟩
  rw [hSX, hSY]
  exact hW₀

theorem ggF4QGeFourRk2MissedInput_S1_of_third (hKG : GGF4QGeFourKGPosInput .S1)
    (hThird : GGF4QGeFourS1ThirdInput) : GGF4QGeFourRk2MissedInput .S1 := by
  intro G _ _ p B Bs x L D J y K hcfg _ e hpres f hf hp hrow _ X Y hXY w i j hij hi hj hmiss
  exact ggF4QGeFourRk2Missed_S1_of_third hKG hThird G p B Bs x L D J y K hcfg e hpres f hf hp
    hrow X Y hXY w i j hij hi hj hmiss

theorem ggF4QGeFourRk2CrossInput_S1_of_missed (hL1 : GGF4QGeFourL1Input .S1)
    (hRk2 : GGF4QGeFourRk2Input .S1) (hM : GGF4QGeFourRk2MissedInput .S1) :
    GGF4QGeFourRk2CrossInput .S1 := by
  intro G _ _ p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow X Y hXY w i j hij hi hj
  have hX : X = L ∨ X = K := by
    rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hY : Y = L ∨ Y = K := by
    rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases hmiss : ∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup G), (Z = L ∨ Z = K) →
      (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs →
      (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∉ ggAutomizer Z Bs
  · exact hM G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow (fun h => nomatch h) X Y hXY w
      i j hij hi hj hmiss
  · push Not at hmiss
    obtain ⟨w', Z, hZ, h1, h2⟩ := hmiss
    exact ggF4QGeFourCross_of_rePair hL1 hRk2 hcfg hRC e hpres hf hp hrow hX hY hZ hij hi hj h1 h2

theorem isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {f : ℕ} (hf : 2 ≤ f)
    (hX : GGTableBPosImage p Bs .POmegaMinus 4 f X ∨ GGTableBPosImage p Bs .PSU 6 f X)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs r) := by
  obtain ⟨F, _, _, θ, -, hθinj, hθ, hcard⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧ Function.Injective θ ∧
        θ.range = ggRankOneIn X Bs r ∧ (Nat.card F = 2 ^ f ∨ Nat.card F = 2 ^ (2 * f)) := by
    rcases hX with hX | hX
    · exact exists_sl2_ggRankOneIn_of_tableBPosImage_POmegaMinus hp hp2 hEl hNT (by omega) hX
        hrA hr
    · exact exists_sl2_ggRankOneIn_of_tableBPosImage_PSU hp hp2 hEl hNT (by omega) hX hrA hr
  have h2f : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h4 : 4 ≤ Nat.card F := by
    rcases hcard with h | h
    · rw [h]; exact h2f
    · rw [h]; exact h2f.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [← hθ]
  exact isQuasisimple_range_of_sl2 h4 hθinj

theorem dvd_card_ggRankOneIn_of_tableBPosImage_S2 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {f : ℕ} (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hX : GGTableBPosImage p Bs .POmegaMinus 4 f X ∨ GGTableBPosImage p Bs .PSU 6 f X)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    p ∣ Nat.card ↥(ggRankOneIn X Bs r) := by
  obtain ⟨F, _, _, θ, -, hθinj, hθ, hcard⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧ Function.Injective θ ∧
        θ.range = ggRankOneIn X Bs r ∧ (Nat.card F = 2 ^ f ∨ Nat.card F = 2 ^ (2 * f)) := by
    rcases hX with hX | hX
    · exact exists_sl2_ggRankOneIn_of_tableBPosImage_POmegaMinus hp hp2 hEl hNT hf hX hrA hr
    · exact exists_sl2_ggRankOneIn_of_tableBPosImage_PSU hp hp2 hEl hNT hf hX hrA hr
  rw [← hθ, ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv]
  rcases hcard with h | h
  · rw [CFSG.LieType.BorelTits.card_specialLinearGroup_fin_two h]
    exact Dvd.dvd.mul_left (hpf.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2)) _
  · rw [CFSG.LieType.BorelTits.card_specialLinearGroup_fin_two h]
    have h4 : 2 ^ f - 1 ∣ (2 ^ (2 * f)) ^ 2 - 1 := by
      rw [show (2 ^ (2 * f)) ^ 2 = (2 ^ f) ^ 4 by rw [← pow_mul, ← pow_mul]; congr 1; ring]
      exact Nat.sub_one_dvd_pow_sub_one (2 ^ f) 4
    exact Dvd.dvd.mul_left (hpf.trans h4) _

theorem ggF4QGeFourOppPumpup_rankOne_POmegaMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) {ψ : (ggU .POmegaMinus 4 f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K) (hrange : ψ.range = L)
    (hpos : GGTableBPos p Bs L .POmegaMinus 4 f ψ) (w : CoxeterMatrix.F₄.Group)
    {u : MulAut ↥Bs}
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (huL : u ∈ ggAutomizer L Bs) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs u) ∧ p ∣ Nat.card ↥(ggRankOneIn L Bs u) := by
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have huR : GGIsReflection p u := ggCoxRefl_isReflection hpres.2 ⟨w, 1, hu⟩
  have hL : GGTableBPosImage p Bs .POmegaMinus 4 f L := ⟨ψ, hker, hrange, hpos⟩
  exact ⟨isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT hf (Or.inl hL) huL huR,
    dvd_card_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT (by omega) hpf (Or.inl hL) huL huR⟩

theorem exists_conj_ggAutomizer_of_tableBPos_POmegaMinus {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A₀ : Subgroup (MulAut ↥Bs)} (hAind : A₀ ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A₀} (hpres : GGCoxeterPres p A₀ CoxeterMatrix.F₄ e)
    {X Z : Subgroup G} {x z : G} (hxB : x ∈ Bs) (hzB : z ∈ Bs)
    (hX : CFSG.Assembly.IsSubnormal X (Subgroup.centralizer ({x} : Set G)))
    (hZ : CFSG.Assembly.IsSubnormal Z (Subgroup.centralizer ({z} : Set G)))
    (hBZ : Bs ≤ Subgroup.normalizer (Z : Set G))
    (hXA : ggAutomizer X Bs ≤ A₀) (hZA : ggAutomizer Z Bs ≤ A₀) {f : ℕ} (hf : 2 ≤ f)
    (hXpos : GGTableBPosImage p Bs .POmegaMinus 4 f X)
    (hZpos : GGTableBPosImage p Bs .POmegaMinus 4 f Z) {t : MulAut ↥Bs}
    (htX : t ∈ ggAutomizer X Bs) (htZ : t ∈ ggAutomizer Z Bs) (ht : GGIsReflection p t) :
    ∃ u : CoxeterMatrix.F₄.Group, ∀ v : CoxeterMatrix.F₄.Group,
      ((e v : ↥A₀) : MulAut ↥Bs) ∈ ggAutomizer Z Bs ↔
        ((e (u * v * u⁻¹) : ↥A₀) : MulAut ↥Bs) ∈ ggAutomizer X Bs := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hf1 : 1 ≤ f := by omega
  have hqX := isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hp hp2 hEl hNT hf (Or.inl hXpos)
    htX ht
  have hqZ := isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hp hp2 hEl hNT hf (Or.inl hZpos)
    htZ ht
  obtain ⟨ψX, hkerX, -, εX, hεX, hlevX, -⟩ := hXpos
  obtain ⟨ψZ, hkerZ, -, εZ, hεZ, hlevZ, -⟩ := hZpos
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  obtain ⟨φX, hφX, haR, ha01, ha12, ha02, haX⟩ :=
    exists_f4Triple_map_of_weyl hp hp2 hEl hNT hAind hpres hXA εX hεX (Equiv.refl _) hM
  obtain ⟨φZ, hφZ, hcR, hc01, hc12, hc02, hcZ⟩ :=
    exists_f4Triple_map_of_weyl hp hp2 hEl hNT hAind hpres hZA εZ hεZ (Equiv.refl _) hM
  set a : Fin 3 → CoxeterMatrix.F₄.Group :=
    fun k => φX ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
      ((Equiv.refl (Fin 3)) k)) with ha
  set c : Fin 3 → CoxeterMatrix.F₄.Group :=
    fun k => φZ ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
      ((Equiv.refl (Fin 3)) k)) with hc
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hposn : ∀ b : Fin 3 → CoxeterMatrix.F₄.Group,
      (∀ k, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection (b k)) →
      orderOf (b 0 * b 1) = 3 → orderOf (b 1 * b 2) = 4 → orderOf (b 0 * b 2) = 2 →
      ∃ (g : CoxeterMatrix.F₄.Group) (σ : Fin 3 → Fin 4),
        (σ = F4Model.posB ∨ σ = F4Model.posC) ∧ ∀ k, g * b k * g⁻¹ = R.s (σ k) := by
    intro b hb h01 h12 h02
    have hb' : ∀ k, R.IsRefl (b k) := fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hb k)
    obtain ⟨g, ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩⟩ := R.classify (hb' 0) (hb' 1) (hb' 2) h01 h12 h02
    · refine ⟨g, F4Model.posB, Or.inl rfl, fun k => ?_⟩
      fin_cases k
      exacts [e0, e1, e2]
    · refine ⟨g, F4Model.posC, Or.inr rfl, fun k => ?_⟩
      fin_cases k
      exacts [e0, e1, e2]
  obtain ⟨ga, σa, hσa, hga⟩ := hposn a haR ha01 ha12 ha02
  obtain ⟨gc, σc, hσc, hgc⟩ := hposn c hcR hc01 hc12 hc02
  by_cases hσ : σa = σc
  ·
    refine ⟨ga⁻¹ * gc, fun v => ?_⟩
    have hca : ∀ k, (ga⁻¹ * gc) * c k * (ga⁻¹ * gc)⁻¹ = a k := by
      intro k
      have h1 := hga k
      have h2 := hgc k
      rw [← hσ] at h2
      calc (ga⁻¹ * gc) * c k * (ga⁻¹ * gc)⁻¹ = ga⁻¹ * (gc * c k * gc⁻¹) * ga := by group
        _ = ga⁻¹ * (ga * a k * ga⁻¹) * ga := by rw [h2, h1]
        _ = a k := by group
    have hmap : (Subgroup.closure (Set.range c)).map (MulAut.conj (ga⁻¹ * gc)).toMonoidHom ≤
        Subgroup.closure (Set.range a) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨k, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hca k).symm
    have hmap' : (Subgroup.closure (Set.range a)).map (MulAut.conj (ga⁻¹ * gc)⁻¹).toMonoidHom ≤
        Subgroup.closure (Set.range c) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨k, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← hca k]
      group
    constructor
    · intro hv
      have h := (haX _).1 (hmap ⟨v, (hcZ v).2 hv, rfl⟩)
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
    · intro hv
      have h := hmap' ⟨_, (haX _).2 hv, rfl⟩
      have h' : v ∈ Subgroup.closure (Set.range c) := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
          show (ga⁻¹ * gc)⁻¹ * ((ga⁻¹ * gc) * v * (ga⁻¹ * gc)⁻¹) * (ga⁻¹ * gc) = v by group]
          using h
      exact (hcZ v).1 h'
  ·
    exfalso
    obtain ⟨k, wX, hkX⟩ := exists_node_of_tableBPos_POmegaMinus hp hp2 hEl hNT hεX htX ht
    obtain ⟨l, wZ, hlZ⟩ := exists_node_of_tableBPos_POmegaMinus hp hp2 hEl hNT hεZ htZ ht
    obtain ⟨FX, _, _, θX, -, hθX, hθXr, hcX⟩ :=
      exists_sl2_ggRankOneIn_node_POmegaMinus hf1 hkerX hlevX wX k
    obtain ⟨FZ, _, _, θZ, -, hθZ, hθZr, hcZ'⟩ :=
      exists_sl2_ggRankOneIn_node_POmegaMinus hf1 hkerZ hlevZ wZ l
    rw [← hkX] at hθXr
    rw [← hlZ] at hθZr
    have hS : ggRankOneIn X Bs t = ggRankOneIn Z Bs t :=
      ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hxB hzB hX hZ hBZ htX htZ hqX hqZ ht.1
        (GGIsReflection.ne_one hp ht)
    have hcard : Nat.card FX = Nat.card FZ := by
      apply ggSL2_card_inj
      rw [Nat.card_congr (MonoidHom.ofInjective hθX).toEquiv,
        Nat.card_congr (MonoidHom.ofInjective hθZ).toEquiv, hθXr, hθZr, hS]
    have hkl : k.val < 2 ↔ l.val < 2 := by
      rw [hcX, hcZ'] at hcard
      have h := Nat.pow_right_injective (le_refl 2) hcard
      split_ifs at h with h1 h2 h2
      · exact iff_of_true h1 h2
      · exfalso; omega
      · exfalso; omega
      · exact iff_of_false h1 h2
    have hv : φX (wX * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple k * wX⁻¹) =
        φZ (wZ * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple l * wZ⁻¹) := by
      apply e.injective
      apply Subtype.ext
      rw [hφX, hφZ, ← hkX, ← hlZ]
    have h3 : φX wX * a k * (φX wX)⁻¹ = φZ wZ * c l * (φZ wZ)⁻¹ := by
      have hak : a k = φX ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple k) := rfl
      have hcl : c l = φZ ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple l) := rfl
      rw [hak, hcl]
      simpa only [map_mul, map_inv] using hv
    have hconj : (gc * (φZ wZ)⁻¹ * φX wX * ga⁻¹) * R.s (σa k) *
        (gc * (φZ wZ)⁻¹ * φX wX * ga⁻¹)⁻¹ = R.s (σc l) := by
      rw [← hga k, ← hgc l]
      calc gc * (φZ wZ)⁻¹ * φX wX * ga⁻¹ * (ga * a k * ga⁻¹) *
            (gc * (φZ wZ)⁻¹ * φX wX * ga⁻¹)⁻¹
          = gc * (φZ wZ)⁻¹ * (φX wX * a k * (φX wX)⁻¹) * φZ wZ * gc⁻¹ := by group
        _ = gc * (φZ wZ)⁻¹ * (φZ wZ * c l * (φZ wZ)⁻¹) * φZ wZ * gc⁻¹ := by rw [h3]
        _ = gc * c l * gc⁻¹ := by group
    have hlen : F4Model.IsLongM (F4Model.Sm (σa k)) ↔ F4Model.IsLongM (F4Model.Sm (σc l)) := by
      obtain ⟨y, hy, hyl⟩ := F4Model.Sm_mem_R (σc l)
      have hρ : R.ρ ((gc * (φZ wZ)⁻¹ * φX wX * ga⁻¹) * R.s (σa k) *
          (gc * (φZ wZ)⁻¹ * φX wX * ga⁻¹)⁻¹) = (F4Model.Rm y).toMat := by
        rw [hconj, R.hs, hyl]
      have h := R.isLongM_of_conj _ (σa k) hy hρ
      rw [← hyl] at h
      exact h.symm
    have hdec : ∀ k l : Fin 3, (k.val < 2 ↔ l.val < 2) →
        ¬ (F4Model.IsLongM (F4Model.Sm (F4Model.posB k)) ↔
          F4Model.IsLongM (F4Model.Sm (F4Model.posC l))) := by
      decide +kernel
    rcases hσa with rfl | rfl <;> rcases hσc with rfl | rfl
    · exact hσ rfl
    · exact hdec k l hkl hlen
    · exact hdec l k hkl.symm hlen.symm
    · exact hσ rfl

theorem exists_mem_zpowers_of_tableBPos_POmegaMinus {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A₀ : Subgroup (MulAut ↥Bs)} (hAind : A₀ ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A₀} (hpres : GGCoxeterPres p A₀ CoxeterMatrix.F₄ e)
    {X Z : Subgroup G} {x z : G} (hXfix : GGFixLineComp Bs x X) (hZfix : GGFixLineComp Bs z Z)
    (hBZ : Bs ≤ Subgroup.normalizer (Z : Set G))
    (hXA : ggAutomizer X Bs ≤ A₀) (hZA : ggAutomizer Z Bs ≤ A₀) {f : ℕ} (hf : 2 ≤ f)
    (hXpos : GGTableBPosImage p Bs .POmegaMinus 4 f X)
    (hZpos : GGTableBPosImage p Bs .POmegaMinus 4 f Z) {t : MulAut ↥Bs}
    (htX : t ∈ ggAutomizer X Bs) (htZ : t ∈ ggAutomizer Z Bs) (ht : GGIsReflection p t) :
    ∃ w ∈ A₀, ∀ b : ↥Bs, (b : G) = z → ((w b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
  obtain ⟨u, hu⟩ := exists_conj_ggAutomizer_of_tableBPos_POmegaMinus hp hp2 hEl hNT hAind hpres
    hXfix.mem hZfix.mem hXfix.isComponentOf.2.1 hZfix.isComponentOf.2.1 hBZ hXA hZA hf hXpos
    hZpos htX htZ ht
  refine ⟨((e u : ↥A₀) : MulAut ↥Bs), (e u).2, fun b hb => ?_⟩
  refine (hXfix.fix_iff _).1 fun φ hφ => ?_
  set v' : CoxeterMatrix.F₄.Group := e.symm ⟨φ, hXA hφ⟩ with hv'
  have hφv : φ = ((e v' : ↥A₀) : MulAut ↥Bs) := by rw [hv', MulEquiv.apply_symm_apply]
  have hZv : ((e (u⁻¹ * v' * u) : ↥A₀) : MulAut ↥Bs) ∈ ggAutomizer Z Bs := by
    refine (hu _).2 ?_
    rw [show u * (u⁻¹ * v' * u) * u⁻¹ = v' by group, ← hφv]
    exact hφ
  have hfixb := (hZfix.fix_iff b).2 (by rw [hb]; exact Subgroup.mem_zpowers z) _ hZv
  have he : ((e (u⁻¹ * v' * u) : ↥A₀) : MulAut ↥Bs) =
      ((e u : ↥A₀) : MulAut ↥Bs)⁻¹ * φ * ((e u : ↥A₀) : MulAut ↥Bs) := by
    rw [hφv, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [he, MulAut.mul_apply, MulAut.mul_apply] at hfixb
  have h2 := congrArg (fun y => ((e u : ↥A₀) : MulAut ↥Bs) y) hfixb
  simp only [MulAut.apply_inv_self] at h2
  exact h2

@[expose] def GGF4QGeFourPSUPairInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G), p.Prime → p ≠ 2 →
    IsElemAbelian p Bs → GGNoTransvection p Bs →
    ∀ A : Subgroup (MulAut ↥Bs), A ≤ ggInduced ⊤ Bs →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥A, GGCoxeterPres p A CoxeterMatrix.F₄ e →
    ∀ X : Subgroup G, ggAutomizer X Bs ≤ A → ∀ f, 2 ≤ f → GGTableBPosImage p Bs .PSU 6 f X →
    ∀ (w : CoxeterMatrix.F₄.Group) (i j : Fin 4), CoxeterMatrix.F₄ i j = 3 →
      ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
      ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
          LinearBlockStandardPair F W
            (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
            (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs))

@[expose] def GGF4QGeFourS2ThirdInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    GGSecFiveRouteCfg p B Bs x L D J {K} →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp .S2 f L K →
      GGCentralImage .POmegaMinus 4 f K →
      ∀ X Y : Subgroup G, (X = L ∧ Y = K ∨ X = K ∧ Y = L) →
      ∀ (w : CoxeterMatrix.F₄.Group) (i j : Fin 4), CoxeterMatrix.F₄ i j = 3 →
        (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
        (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs →
        (∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup G), (Z = L ∨ Z = K) →
          (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs →
          (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∉ ggAutomizer Z Bs) →
          ∃ (z : G) (A : Subgroup G), z ∈ Bs ∧
            CFSG.Assembly.IsComponentOf A (Subgroup.centralizer ({z} : Set G)) ∧
            Bs ≤ Subgroup.normalizer (A : Set G) ∧
            ggAutomizer A Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs ∧
            (GGTableBPosImage p Bs .PSU 6 f A ∨ GGTableBPosImage p Bs .POmegaMinus 4 f A) ∧
            (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer A Bs ∧
            (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer A Bs

theorem ggF4QGeFourRk2MissedInput_S2_of_third (hKG : GGF4QGeFourKGPosInput .S2)
    (hU : GGF4QGeFourPSUPairInput) (hThird : GGF4QGeFourS2ThirdInput) :
    GGF4QGeFourRk2MissedInput .S2 := by
  intro G _ _ p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow hKom X Y hXY w i j hij hi hj hmiss
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hodd : Odd p := hpp.odd_of_ne_two hp2
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hpos := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  obtain ⟨hDB, -, -, hxD, -⟩ := hcfg.1.1.2.2.1
  have hxB : x ∈ Bs := hcfg.1.1.2.1.1 (hDB hxD)
  have hyB : y ∈ Bs := by
    refine hcfg.1.1.2.1.1 (hDB ?_)
    rw [hcfg.2.2.2.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmem : ∀ Z : Subgroup G, Z = L ∨ Z = K → ∃ z, z ∈ Bs ∧
      CFSG.Assembly.IsSubnormal Z (Subgroup.centralizer ({z} : Set G)) ∧
      (GGTableBPosImage p Bs .POmegaMinus 4 f Z ∨ GGTableBPosImage p Bs .PSU 6 f Z) := by
    rintro Z (rfl | rfl)
    · exact ⟨x, hxB, hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1, Or.inl hpos.1⟩
    · exact ⟨y, hyB, hcfg.2.2.2.1.2.2.2.2.1.2.1, Or.symm hpos.2⟩
  have hXm : X = L ∨ X = K := by rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hYm : Y = L ∨ Y = K := by rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  obtain ⟨xX, hxXB, hXx, hXpos⟩ := hmem X hXm
  obtain ⟨yY, hyYB, hYy, hYpos⟩ := hmem Y hYm
  have hrefl : ∀ (v : CoxeterMatrix.F₄.Group) (k : Fin 4), GGIsReflection p
      ((e (v * CoxeterMatrix.F₄.simple k * v⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) :=
    fun v k => ggCoxRefl_isReflection hpres.2 ⟨v, k, rfl⟩
  obtain ⟨z, A, hzB, hA, hBA, hAW, hApos', hrA, hr'A⟩ :=
    hThird G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow (hKom rfl) X Y hXY w i j hij hi hj
      hmiss
  have hApos : GGTableBPosImage p Bs .PSU 6 f A := by
    rcases hApos' with hApos | hApos
    · exact hApos
    · exfalso
      obtain ⟨m, hmL, hmA⟩ : ∃ m : Fin 4,
          (↑(e (w * CoxeterMatrix.F₄.simple m * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer L Bs ∧
          (↑(e (w * CoxeterMatrix.F₄.simple m * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer A Bs := by
        rcases hXY with ⟨hXL, -⟩ | ⟨-, hYL⟩
        · exact ⟨i, (congrArg (fun Z : Subgroup G =>
            (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs) hXL).mp
              hi, hrA⟩
        · exact ⟨j, (congrArg (fun Z : Subgroup G =>
            (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs) hYL).mp
              hj, hr'A⟩
      obtain ⟨u, hu⟩ := exists_conj_ggAutomizer_of_tableBPos_POmegaMinus hpp hp2 hEl hNT hAind
        hpres hxB hzB hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1 hA.2.1 hBA le_sup_left hAW hf hpos.1
        hApos hmL hmA (hrefl w m)
      have hconj : ∀ k : Fin 4, u * (w * CoxeterMatrix.F₄.simple k * w⁻¹) * u⁻¹ =
          (u * w) * CoxeterMatrix.F₄.simple k * (u * w)⁻¹ := fun k => by group
      have h1 := (hu _).1 hrA
      have h2 := (hu _).1 hr'A
      rw [hconj] at h1 h2
      exact hmiss (u * w) L (Or.inl rfl) h1 h2
  obtain ⟨F, hFf, hFfin, W₀, hF2, hW₀⟩ :=
    hU G p Bs hpp hp2 hEl hNT _ hAind e hpres A hAW f hf hApos w i j hij hrA hr'A
  have hSX := ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hxXB hzB hXx hA.2.1 hBA hi hrA
    (isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT hf hXpos hi (hrefl w i))
    (isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT hf (Or.inr hApos) hrA
      (hrefl w i))
    (hrefl w i).1 (GGIsReflection.ne_one hpp (hrefl w i))
  have hSY := ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hyYB hzB hYy hA.2.1 hBA hj hr'A
    (isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT hf hYpos hj (hrefl w j))
    (isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT hf (Or.inr hApos) hr'A
      (hrefl w j))
    (hrefl w j).1 (GGIsReflection.ne_one hpp (hrefl w j))
  refine ⟨F, hFf, hFfin, W₀, hF2, ?_⟩
  rw [hSX, hSY]
  exact hW₀

end Inputs

end CFSG.StandardType

end
