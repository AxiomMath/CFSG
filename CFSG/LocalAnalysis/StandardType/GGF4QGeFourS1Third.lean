module

public import CFSG.LocalAnalysis.StandardType.GGF4MissedFrame
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem F4Model

section Third


theorem ggF4QGeFourS1Third_of_BB (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) (hLim : GGCentralImage .PSp 3 f L)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (he : ∀ i, GGIsReflection p
      ((e (CoxeterMatrix.F₄.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i)
    {a b : Fin 3 → CoxeterMatrix.F₄.Group} {ga gb : CoxeterMatrix.F₄.Group}
    (hga : ga * a 0 * ga⁻¹ = R.s 0 ∧ ga * a 1 * ga⁻¹ = R.s 1 ∧ ga * a 2 * ga⁻¹ = R.s 2)
    (hgb : gb * b 0 * gb⁻¹ = R.s 0 ∧ gb * b 1 * gb⁻¹ = R.s 1 ∧ gb * b 2 * gb⁻¹ = R.s 2)
    (haL : ∀ z, z ∈ Subgroup.closure (Set.range a) →
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs)
    {w₀ : CoxeterMatrix.F₄.Group} (h2 : w₀ * R.s 2 * w₀⁻¹ ∈ Subgroup.closure (Set.range a))
    (h3a : w₀ * R.s 3 * w₀⁻¹ ∉ Subgroup.closure (Set.range a))
    (h3 : w₀ * R.s 3 * w₀⁻¹ ∈ Subgroup.closure (Set.range b))
    (h2b : w₀ * R.s 2 * w₀⁻¹ ∉ Subgroup.closure (Set.range b)) :
    ∃ (z : G) (A : Subgroup G), z ∈ Bs ∧
      CFSG.Assembly.IsComponentOf A (Subgroup.centralizer ({z} : Set G)) ∧
      Bs ≤ Subgroup.normalizer (A : Set G) ∧
      ggAutomizer A Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs ∧
      GGTableBPosImage p Bs .PSp 3 f A ∧
      ((e (w₀ * CoxeterMatrix.F₄.simple 2 * w₀⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) ∈ ggAutomizer A Bs ∧
      ((e (w₀ * CoxeterMatrix.F₄.simple 3 * w₀⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) ∈ ggAutomizer A Bs := by
  obtain ⟨y', a'', hy2a, hy1a, -, -, ha'a, hP2, hP3, hv⟩ := R.exists_frame hga hgb h2 h3a h3 h2b
  have hgfix := (R.mem_closure_iff_of_B hga (w₀ * a'' * w₀⁻¹)⁻¹).1 (inv_mem ha'a)
  have hvw : (R.ρ (ga * (w₀ * a'' * y'))⁻¹).mulVec f4E1.toFun =
      (R.ρ (ga * (w₀ * y'))⁻¹).mulVec f4E1.toFun := by
    rw [show (ga * (w₀ * a'' * y'))⁻¹ = (w₀ * y')⁻¹ * ((w₀ * a'' * w₀⁻¹)⁻¹ * ga⁻¹) by group,
      show (ga * (w₀ * y'))⁻¹ = (w₀ * y')⁻¹ * ga⁻¹ by group]
    simp only [map_mul, ← Matrix.mulVec_mulVec]
    rw [hgfix]
  have hv' : (R.ρ (ga * (w₀ * a'' * y'))⁻¹).mulVec f4E1.toFun = f4E1.toFun ∨
      (R.ρ (ga * (w₀ * a'' * y'))⁻¹).mulVec f4E1.toFun = f4E1.neg.toFun ∨
      (R.ρ (ga * (w₀ * a'' * y'))⁻¹).mulVec f4E1.toFun = f4E2.toFun ∨
      (R.ρ (ga * (w₀ * a'' * y'))⁻¹).mulVec f4E1.toFun = f4E2.neg.toFun := by
    rw [hvw]
    exact hv
  have hconj : ∀ k : Fin 4, w₀ * a'' * y' * R.s k * (w₀ * a'' * y')⁻¹ =
      w₀ * a'' * w₀⁻¹ * (w₀ * y' * R.s k * (w₀ * y')⁻¹) * (w₀ * a'' * w₀⁻¹)⁻¹ := fun k => by
    group
  have hrL : ((e (w₀ * a'' * y' * CoxeterMatrix.F₄.simple 2 * (w₀ * a'' * y')⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs := by
    apply haL
    rw [← hRs 2, hconj]
    exact mul_mem (mul_mem ha'a hy2a) (inv_mem ha'a)
  have huL : ((e (w₀ * a'' * y' * CoxeterMatrix.F₄.simple 1 * (w₀ * a'' * y')⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs := by
    apply haL
    rw [← hRs 1, hconj]
    exact mul_mem (mul_mem ha'a hy1a) (inv_mem ha'a)
  obtain ⟨z, A, hEnd, -, hTB, hPC⟩ := ggF4QGeFourS1Endpoint_of_frame hLB hB3 hNPLA hcfg hf hpf
    hLim he R hRs haL hga (w₀ * a'' * y') hv' hrL huL
  have hpair : ∀ k : Fin 4, (a'' * y')⁻¹ * R.s k * (a'' * y') ∈
      Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set CoxeterMatrix.F₄.Group) →
      ((e (w₀ * CoxeterMatrix.F₄.simple k * w₀⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) ∈ ggAutomizer A Bs := by
    intro k hk
    have h := hPC _ hk
    rwa [show w₀ * a'' * y' * ((a'' * y')⁻¹ * R.s k * (a'' * y')) * (w₀ * a'' * y')⁻¹ =
      w₀ * R.s k * w₀⁻¹ by group, hRs] at h
  exact ⟨z, A, hEnd.1.mem, hEnd.1.isComponentOf, hEnd.2.2.1, hEnd.2.2.2.1, hTB, hpair 2 hP2,
    hpair 3 hP3⟩

theorem ggF4QGeFourS1ThirdInput_of_inputs (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput) : GGF4QGeFourS1ThirdInput := by
  intro G _ _ p B Bs x L D J y K hcfg e hpres f hf hpf hrow X Y hXY w i j hij htX htY hmiss
  classical
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
  obtain ⟨ψL0, hlocL⟩ := ggKGPosLocalHypSp_of_f4_mp_of_centralImage ggInnerDiagMpInput_holds hcfg
    hf hpf L (Or.inl rfl) hrow.1
  obtain ⟨ψL, -, -, hposL, -⟩ := ggKGPosSp_tableBPos_torus hlocL
  obtain ⟨εL, hεL, -, -⟩ := hposL
  obtain ⟨ψK0, hlocK⟩ := ggKGPosLocalHypSp_of_f4_mp_of_centralImage ggInnerDiagMpInput_holds hcfg
    hf hpf K (Or.inr rfl) hrow.2
  obtain ⟨ψK, -, -, hposK, -⟩ := ggKGPosSp_tableBPos_torus hlocK
  obtain ⟨εK, hεK, -, -⟩ := hposK
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_PSp_three]
    rfl
  obtain ⟨a, ha, ha01, ha12, ha02, haL⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_left εL hεL (Equiv.refl _) hM
  obtain ⟨b, hb, hb01, hb12, hb02, hbK⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_right εK hεK (Equiv.refl _) hM
  obtain ⟨R, hRs0⟩ := exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hRs : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k
    rw [hRs0 k, CoxeterMatrix.toCoxeterSystem_simple]
  have haR : ∀ k, R.IsRefl (a k) := fun k => (F4Rep.isRefl_iff hRs0).2 (ha k)
  have hbR : ∀ k, R.IsRefl (b k) := fun k => (F4Rep.isRefl_iff hRs0).2 (hb k)
  have key : ∀ i' j' : Fin 4, CoxeterMatrix.F₄ i' j' = 3 →
      ((e (w * CoxeterMatrix.F₄.simple i' * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) ∈ ggAutomizer L Bs →
      ((e (w * CoxeterMatrix.F₄.simple j' * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) ∈ ggAutomizer K Bs →
      (∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup (MulAut ↥Bs)),
        (Z = ggAutomizer L Bs ∨ Z = ggAutomizer K Bs) →
        ((e (w' * CoxeterMatrix.F₄.simple i' * w'⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) ∈ Z →
        ((e (w' * CoxeterMatrix.F₄.simple j' * w'⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) ∉ Z) →
      ∃ (z : G) (A : Subgroup G), z ∈ Bs ∧
        CFSG.Assembly.IsComponentOf A (Subgroup.centralizer ({z} : Set G)) ∧
        Bs ≤ Subgroup.normalizer (A : Set G) ∧
        ggAutomizer A Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs ∧
        GGTableBPosImage p Bs .PSp 3 f A ∧
        ((e (w * CoxeterMatrix.F₄.simple i' * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) ∈ ggAutomizer A Bs ∧
        ((e (w * CoxeterMatrix.F₄.simple j' * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) ∈ ggAutomizer A Bs := by
    intro i' j' hij' hi hj hm
    obtain ⟨e', a', b', ga, gb, w₀, he', haL', hbK', hga, hgb, h2, h3, hiK, hjL⟩ :=
      exists_missed_framePos e hpres.2 R hRs haR ha01 ha12 ha02 hbR hb01 hb12 hb02 haL hbK w hij'
        hi hj hm
    have h2a : w₀ * R.s 2 * w₀⁻¹ ∈ Subgroup.closure (Set.range a') := by
      rw [haL', h2]
      exact hi
    have h3b : w₀ * R.s 3 * w₀⁻¹ ∈ Subgroup.closure (Set.range b') := by
      rw [hbK', h3]
      exact hj
    have h3a : w₀ * R.s 3 * w₀⁻¹ ∉ Subgroup.closure (Set.range a') := by
      rw [haL', h3]
      exact hjL
    have h2b : w₀ * R.s 2 * w₀⁻¹ ∉ Subgroup.closure (Set.range b') := by
      rw [hbK', h2]
      exact hiK
    obtain ⟨z, A, hz, hAc, hAN, hAW, hTB, h2A, h3A⟩ := ggF4QGeFourS1Third_of_BB hLB hB3 hNPLA
      hcfg hf hpf hrow.1 he' R hRs hga hgb (fun z hz => (haL' z).1 hz) h2a h3a h3b h2b
    rw [← hRs 2, h2] at h2A
    rw [← hRs 3, h3] at h3A
    exact ⟨z, A, hz, hAc, hAN, hAW, hTB, h2A, h3A⟩
  rcases hXY with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · rw [hX] at htX
    rw [hY] at htY
    refine key i j hij htX htY fun w' Z hZ h1 h2 => ?_
    rcases hZ with rfl | rfl
    · exact hmiss w' L (Or.inl rfl) h1 h2
    · exact hmiss w' K (Or.inr rfl) h1 h2
  · rw [hX] at htX
    rw [hY] at htY
    obtain ⟨z, A, hz, hAc, hAN, hAW, hTB, hjA, hiA⟩ :=
      key j i ((CoxeterMatrix.F₄.symmetric j i).trans hij) htY htX fun w' Z hZ h1 h2 => by
        rcases hZ with rfl | rfl
        · exact hmiss w' L (Or.inl rfl) h2 h1
        · exact hmiss w' K (Or.inr rfl) h2 h1
    exact ⟨z, A, hz, hAc, hAN, hAW, hTB, hiA, hjA⟩

end Third

end CFSG.StandardType
