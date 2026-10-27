module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal2.SpModel
public import CFSG.Fischer.Classification.Orthogonal2.Reflect
public import Mathlib.GroupTheory.Perm.Fin

import CFSG.LocalAnalysis.StandardType.ZS.DThreeWeyl
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTransport
import CFSG.LocalAnalysis.StandardType.ZS.DThreeSpFrame
import CFSG.LocalAnalysis.StandardType.ZS.DThreeSpWeyl
import CFSG.LocalAnalysis.StandardType.ZS.DThreeOrthFrame
import CFSG.LocalAnalysis.StandardType.ZS.DThreeOrthEight
import CFSG.LocalAnalysis.StandardType.ZS.DThreeOrthSix
import CFSG.LocalAnalysis.StandardType.ZS.DThreeObstruction
import CFSG.LocalAnalysis.StandardType.ZS.ReflHyp
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.LargeExtraspecial.S2Three
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Fischer.Classification.Orth2

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem za2_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b : α) :
    e.permCongr (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  ext z
  rw [Equiv.permCongr_apply, Equiv.swap_apply_def, Equiv.swap_apply_def]
  by_cases hza : z = e a
  · subst z
    simp
  · have hsa : e.symm z ≠ a := fun h => hza (by rw [← h, e.apply_symm_apply])
    by_cases hzb : z = e b
    · subst z
      have hne : b ≠ a := fun h => hza (by rw [h])
      simp [hne]
    · have hsb : e.symm z ≠ b := fun h => hzb (by rw [← h, e.apply_symm_apply])
      simp [hza, hzb, hsa, hsb]

private theorem za2_isSwap_permCongr {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (f : Equiv.Perm α) : (e.permCongr f).IsSwap ↔ f.IsSwap := by
  constructor
  · rintro ⟨x, y, hxy, hf⟩
    have h2 : e.permCongr.symm (Equiv.swap x y) =
        Equiv.swap (e.symm x) (e.symm y) := by
      rw [Equiv.permCongr_symm]
      exact za2_permCongr_swap e.symm x y
    refine ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h), ?_⟩
    have h : e.permCongr.symm (Equiv.swap x y) = f := by
      rw [← hf]
      exact Equiv.symm_apply_apply e.permCongr f
    rw [h2] at h
    exact h.symm
  · rintro ⟨x, y, hxy, rfl⟩
    exact ⟨e x, e y, fun h => hxy (e.injective h), za2_permCongr_swap e x y⟩

private theorem za2_closure_eq_top_of_image_eq (hp : p ≠ 2)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {Y : Type*} [Group Y] (Φ : ↥A ⧸ Subgroup.center ↥A ≃* Y) {F : Set Y}
    (hΦ : Φ '' reflImage p A = F) : Subgroup.closure F = ⊤ := by
  have hone : OneClass p A := oneClass_of_orderOf_mul_le_three hp hgen hirr h3
  have htop : Subgroup.closure (reflImage p A) = ⊤ :=
    (pair_reflImage hgen hirr hn hone h3).2.2.2.2
  rw [← hΦ, ← MulEquiv.coe_toMonoidHom Φ, ← MonoidHom.map_closure Φ.toMonoidHom, htop]
  exact Subgroup.map_top_of_surjective Φ.toMonoidHom Φ.surjective

private theorem za2_linWeyl_of_config_A (hp : p ≠ 2)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {Y : Type*} [Group Y] {Φ : ↥A ⧸ Subgroup.center ↥A ≃* Y} {F : Set Y}
    (hEF : ∀ g, g ∈ reflImage p A ↔ Φ g ∈ F)
    {l : ℕ} (hl : l + 1 = 3 ∨ 5 ≤ l + 1) {d : Fin l → Y}
    (h : CoxeterConfig F (CoxeterMatrix.A l) d)
    (hgenD : Subgroup.closure (Set.range d) = ⊤) : LinWeyl p A := by
  have hone : OneClass p A := oneClass_of_orderOf_mul_le_three hp hgen hirr h3
  exact linWeyl_of_coxeterConfig_A (l := l) hgen hirr hn hone hl
    (CoxeterConfig.comap Φ hEF h) (closure_range_symm_comp_eq_top Φ hgenD)

private theorem za2_linWeyl_of_config_E (hp : p ≠ 2)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {Y : Type*} [Group Y] {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : (∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e) ∨
      (∃ e : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e) ∨
      (∃ e : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e))
    {Φ : ↥A ⧸ Subgroup.center ↥A ≃* Y} {F : Set Y}
    (hEF : ∀ g, g ∈ reflImage p A ↔ Φ g ∈ F)
    {d : ι → Y} (h : CoxeterConfig F M d)
    (hgenD : Subgroup.closure (Set.range d) = ⊤) : LinWeyl p A := by
  have hone : OneClass p A := oneClass_of_orderOf_mul_le_three hp hgen hirr h3
  exact linWeyl_of_coxeterConfig_E (ι := ι) (M := M) hp hgen hirr hn hone hM
    (CoxeterConfig.comap Φ hEF h) (closure_range_symm_comp_eq_top Φ hgenD)

private theorem za2_false_of_scalarFrame (hp : p ≠ 2)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {Y : Type*} [Group Y] {Φ : ↥A ⧸ Subgroup.center ↥A ≃* Y} {F : Set Y}
    (hEF : ∀ g, g ∈ reflImage p A ↔ Φ g ∈ F)
    {d : Fin 8 → Y} {e : Y} (h : ScalarFrame F d e)
    (hall : ∀ i, ¬ Commute e (d i)) : False := by
  have hframe : ScalarFrame (reflImage p A) (Φ.symm ∘ d) (Φ.symm e) :=
    ScalarFrame.comap Φ hEF h
  have hall' : ∀ i, ¬ Commute (Φ.symm e) ((Φ.symm ∘ d) i) := by
    intro i hc
    exact hall i ((commute_map_iff (f := Φ.symm) Φ.symm.injective).mp hc)
  exact false_of_scalarFrame_eight hp hirr hn h3 hframe hall'

private theorem za2_false_of_scalarFrame_spT {m : ℕ} (hm : 4 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hp : p ≠ 2) (hn : 3 ≤ Module.finrank (ZMod p) U) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {Φ : ↥A ⧸ Subgroup.center ↥A ≃* TauCeti.BilinForm.isometryGroup b}
    (hEF : ∀ g, g ∈ reflImage p A ↔
      Φ g ∈ {g | ∃ v, v ≠ 0 ∧ g = spT (f := b) halt v}) : False := by
  obtain ⟨d, e, hframe, hall⟩ := exists_scalarFrame_spT hm halt hnd
  exact za2_false_of_scalarFrame hp hn hirr h3 hEF hframe hall

private theorem za2_family_orth_of_normal_form (hp : p ≠ 2)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : 2 ≤ m) {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hts : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    {Φ : ↥A ⧸ Subgroup.center ↥A ≃* TauCeti.QuadraticMap.orthogonalGroup Q}
    (hEF : ∀ g, g ∈ reflImage p A ↔ Φ g ∈ reflClass Q)
    (htop : Subgroup.closure (reflClass Q) = ⊤)
    (hcases : (∃ b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (Fin (2 * m) → ZMod 2),
        ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) m (b.equivFun v)) ∨
      ∃ b : Module.Basis (CFSG.Open.GLAMinusIdx (m - 1)) (ZMod 2)
          (Fin (2 * m) → ZMod 2),
        ∀ v, Q v = CFSG.Open.GLAQMinus (m - 1) (1 : ZMod 2) 1 (b.equivFun v)) :
    Family p A := by
  rcases eq_or_lt_of_le hm with hm2 | hm3
  · obtain rfl : m = 2 := hm2.symm
    rcases hcases with ⟨b, hb⟩ | ⟨b, hb⟩
    · obtain ⟨W, hW, hWQ⟩ := exists_totallySingular_plane_of_GLAQPlus_two b hb
      exact False.elim (hts rfl ⟨W, hW, hWQ⟩)
    · obtain ⟨d, hconf, hgenD⟩ := exists_coxeterConfig_A₄_reflClass_minus b hb htop
      exact Family.weyl (za2_linWeyl_of_config_A hp hn hgen hirr h3 hEF (l := 4)
        (Or.inr (by norm_num)) hconf hgenD)
  · rcases eq_or_lt_of_le (by omega : 3 ≤ m) with hm3e | hm4
    · obtain rfl : m = 3 := hm3e.symm
      rcases hcases with ⟨b, hb⟩ | ⟨b, hb⟩
      · obtain ⟨d, hconf, hgenD⟩ := exists_coxeterConfig_A₇_reflClass_plus b hb htop
        exact Family.weyl (za2_linWeyl_of_config_A hp hn hgen hirr h3 hEF (l := 7)
          (Or.inr (by norm_num)) hconf hgenD)
      · obtain ⟨d, hconf, hgenD⟩ := exists_coxeterConfig_E₆_reflClass_minus b hb htop
        exact Family.weyl (za2_linWeyl_of_config_E hp hn hgen hirr h3
          (Or.inl ⟨Equiv.refl _, (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm⟩)
          hEF hconf hgenD)
    · rcases eq_or_lt_of_le (by omega : 4 ≤ m) with hm4e | hm5
      · obtain rfl : m = 4 := hm4e.symm
        rcases hcases with ⟨b, hb⟩ | ⟨b, hb⟩
        · obtain ⟨d, hconf, hgenD⟩ := exists_coxeterConfig_E₈_reflClass_plus b hb htop
          exact Family.weyl (za2_linWeyl_of_config_E hp hn hgen hirr h3
            (Or.inr (Or.inr ⟨Equiv.refl _,
              (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm⟩)) hEF hconf hgenD)
        · obtain ⟨d, e, hframe, hall⟩ :=
            exists_scalarFrame_reflClass_minus (m := 4) (by norm_num) b hb
          exact False.elim (za2_false_of_scalarFrame hp hn hirr h3 hEF hframe hall)
      · have hm5' : 5 ≤ m := by omega
        rcases hcases with ⟨b, hb⟩ | ⟨b, hb⟩
        · obtain ⟨d, e, hframe, hall⟩ := exists_scalarFrame_reflClass_plus hm5' b hb
          exact False.elim (za2_false_of_scalarFrame hp hn hirr h3 hEF hframe hall)
        · obtain ⟨d, e, hframe, hall⟩ :=
            exists_scalarFrame_reflClass_minus (by omega : 4 ≤ m) b hb
          exact False.elim (za2_false_of_scalarFrame hp hn hirr h3 hEF hframe hall)

private theorem za2_family_orth (hp : p ≠ 2)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : 2 ≤ m) {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hts : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    {Φ : ↥A ⧸ Subgroup.center ↥A ≃* TauCeti.QuadraticMap.orthogonalGroup Q}
    (hEF : ∀ g, g ∈ reflImage p A ↔ Φ g ∈ reflClass Q)
    (htop : Subgroup.closure (reflClass Q) = ⊤) : Family p A := by
  have hnd' : (QuadraticMap.polarBilin Q).Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => hnd x fun y => by
      rw [← QuadraticMap.polarBilin_apply_apply]
      exact hx y
  have hdim : Module.finrank (ZMod 2) (Fin (2 * m) → ZMod 2) = 2 * m :=
    Module.finrank_fin_fun _
  exact za2_family_orth_of_normal_form hp hn hgen hirr h3 hm hts hEF htop
    (CFSG.HardMathSupport.Solomon.Coordinator.mclt_exists_basis_quadratic Q hnd'
      (n := m) (by omega) hdim)

theorem family_of_mulEquiv_perm (hp : p ≠ 2) (hn : 4 ≤ Module.finrank (ZMod p) U)
    (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : m = 3 ∨ 5 ≤ m) (φ : ↥A ⧸ Subgroup.center ↥A ≃* Equiv.Perm (Fin m))
    (hφ : ∀ g, g ∈ reflImage p A ↔ (φ g).IsSwap) : Family p A := by
  have hn3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  obtain ⟨l, hl1⟩ : ∃ l : ℕ, l + 1 = m := ⟨m - 1, by omega⟩
  have hl : l + 1 = 3 ∨ 5 ≤ l + 1 := by
    rcases hm with hm3 | hm5
    · left; omega
    · right; omega
  let e : Fin m ≃ Fin (l + 1) := (finCongr hl1).symm
  let φ' : ↥A ⧸ Subgroup.center ↥A ≃* Equiv.Perm (Fin (l + 1)) :=
    φ.trans e.permCongrHom
  have hφ' : ∀ g, g ∈ reflImage p A ↔ (φ' g).IsSwap := by
    intro g
    have h1 : (φ' g).IsSwap ↔ (φ g).IsSwap := by
      simpa only [φ', MulEquiv.trans_apply, Equiv.permCongrHom_coe] using
        za2_isSwap_permCongr e (φ g)
    exact (hφ g).trans h1.symm
  exact Family.weyl (za2_linWeyl_of_config_A (Φ := φ')
    (F := {σ : Equiv.Perm (Fin (l + 1)) | σ.IsSwap}) hp hn3 hgen hirr h3 hφ'
    (l := l) hl (coxeterConfig_swap l) (closure_range_swap_eq_top l))

theorem family_of_mulEquiv_isometryGroup (hp : p ≠ 2) (hn : 4 ≤ Module.finrank (ZMod p) U)
    (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : 2 ≤ m) {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (Φ : ↥A ⧸ Subgroup.center ↥A ≃* TauCeti.BilinForm.isometryGroup b)
    (hΦ : ∀ g, g ∈ reflImage p A ↔ ∃ v, v ≠ 0 ∧ Φ g = spT (f := b) halt v) : Family p A := by
  have hn3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  let F : Set (TauCeti.BilinForm.isometryGroup b) :=
    {g | ∃ v, v ≠ 0 ∧ g = spT (f := b) halt v}
  have hΦ' : Φ '' reflImage p A = F := image_eq_of_forall_mem_iff Φ hΦ
  have htop : Subgroup.closure F = ⊤ :=
    za2_closure_eq_top_of_image_eq hp hn3 hgen hirr h3 Φ hΦ'
  rcases eq_or_lt_of_le hm with hm2 | hm3
  · obtain rfl : m = 2 := hm2.symm
    obtain ⟨d, hconf, hgenD⟩ := exists_coxeterConfig_A₅_spT halt hnd htop
    exact Family.weyl (za2_linWeyl_of_config_A hp hn3 hgen hirr h3 hΦ (l := 5)
      (Or.inr (by norm_num)) hconf hgenD)
  · rcases eq_or_lt_of_le (by omega : 3 ≤ m) with hm3e | hm4
    · obtain rfl : m = 3 := hm3e.symm
      obtain ⟨d, hconf, hgenD⟩ := exists_coxeterConfig_E₇_spT halt hnd htop
      exact Family.weyl (za2_linWeyl_of_config_E hp hn3 hgen hirr h3
        (Or.inr (Or.inl ⟨Equiv.refl _,
          (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm⟩)) hΦ hconf hgenD)
    · exact False.elim (za2_false_of_scalarFrame_spT (by omega : 4 ≤ m) halt hnd hp hn3
        hirr h3 hΦ)

theorem family_of_mulEquiv_orthogonalGroup (hp : p ≠ 2) (hn : 4 ≤ Module.finrank (ZMod p) U)
    (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : 2 ≤ m) {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hts : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (Φ : ↥A ⧸ Subgroup.center ↥A ≃* TauCeti.QuadraticMap.orthogonalGroup Q)
    (hΦ : Φ '' reflImage p A = reflClass Q) : Family p A := by
  have hn3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  have hEF : ∀ g, g ∈ reflImage p A ↔ Φ g ∈ reflClass Q :=
    mem_iff_of_image_eq Φ hΦ
  have htop : Subgroup.closure (reflClass Q) = ⊤ :=
    za2_closure_eq_top_of_image_eq hp hn3 hgen hirr h3 Φ hΦ
  exact za2_family_orth hp hn3 hgen hirr h3 hm hnd hts hEF htop

end CFSG.StandardType.ZS
