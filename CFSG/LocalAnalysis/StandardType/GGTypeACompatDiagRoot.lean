module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SLOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

theorem exists_twoSubgroup_le_map_blockSpecialLinear {X : Type} [Group X] {F : Type} [Field F]
    [CharP F 2] {m : ℕ} {φ : SpecialLinearGroup (Fin (m + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {B : Subgroup X} (hB : ∀ b ∈ B, GGActsDiag φ b) {I : Finset (Fin (m + 1))}
    (hI : 2 ≤ I.card) :
    ∃ T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      T ≤ (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I).map φ ∧
      B ≤ Subgroup.normalizer (T : Set X) := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  let rootHom : Multiplicative F →* SpecialLinearGroup (Fin (m + 1)) F :=
    { toFun := fun c => SpecialLinearGroup.transvection hij (Multiplicative.toAdd c)
      map_one' := by simp only [toAdd_one, SpecialLinearGroup.transvection_coeff_zero]
      map_mul' := fun c d => by
        simp only [toAdd_mul, SpecialLinearGroup.transvection_add] }
  let R : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) := rootHom.range
  let T : Subgroup X := R.map φ
  have hroot_mem : ∀ c : Multiplicative F,
      rootHom c ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I := fun c =>
    CFSG.SeitzReduction.LinearPilot.transvection_mem_blockSpecialLinear hij hi hj _
  have hconj_root : ∀ (t : Fin (m + 1) → Fˣ) (c : Multiplicative F),
      ggDiagConj t (rootHom c) ∈ R := by
    intro t c
    refine ⟨Multiplicative.ofAdd ((t i : F) * Multiplicative.toAdd c * (((t j)⁻¹ : Fˣ) : F)), ?_⟩
    change SpecialLinearGroup.transvection hij
        (Multiplicative.toAdd (Multiplicative.ofAdd
          ((t i : F) * Multiplicative.toAdd c * (((t j)⁻¹ : Fˣ) : F)))) =
      ggDiagConj t (SpecialLinearGroup.transvection hij (Multiplicative.toAdd c))
    rw [toAdd_ofAdd, ggDiagConj_transvection]
  have hTne : T ≠ ⊥ := by
    intro hT
    have h1R : SpecialLinearGroup.transvection hij (1 : F) ∈ R :=
      ⟨Multiplicative.ofAdd (1 : F), rfl⟩
    have hmem : φ (SpecialLinearGroup.transvection hij (1 : F)) ∈ T :=
      Subgroup.mem_map.mpr ⟨_, h1R, rfl⟩
    rw [hT, Subgroup.mem_bot] at hmem
    exact one_ne_zero (eq_zero_of_transvection_mem_center hij (hker (by
      rw [MonoidHom.mem_ker]; exact hmem)))
  have hTp : IsPGroup 2 T := (isPGroup_two_range_of_charTwo rootHom).map φ
  have hTle : T ≤ (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I).map φ := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_range] at hr
    obtain ⟨c, hc⟩ := hr
    rw [← hc]
    exact Subgroup.mem_map.mpr ⟨rootHom c, hroot_mem c, rfl⟩
  have hconj_mem : ∀ b ∈ B, ∀ x ∈ T, b * x * b⁻¹ ∈ T := by
    intro b hb x hx
    obtain ⟨hvec, hact⟩ := hB b hb
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_range] at hr
    obtain ⟨c, hc⟩ := hr
    rw [← hc]
    exact Subgroup.mem_map.mpr
      ⟨ggDiagConj hvec (rootHom c), hconj_root hvec c, (hact (rootHom c)).symm⟩
  refine ⟨T, hTne, hTp, hTle, ?_⟩
  intro b hb
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hconj_mem b hb x hx
  · intro hx
    have hx' : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ ∈ T :=
      hconj_mem b⁻¹ (B.inv_mem hb) (b * x * b⁻¹) hx
    have e : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x := by group
    rwa [e] at hx'


theorem prime_dvd_card_range_comp_slLowerBlockHom {X : Type} [Group X] [Finite X] {F : Type}
    [Field F] [Finite F] {p n : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card Fˣ) (hn : 2 ≤ n)
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    p ∣ Nat.card (φ.comp (slLowerBlockHom n F)).range := by
  have hdvd : p ∣ Nat.card (SpecialLinearGroup (Fin n) F) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.dvd_card_SL_of_dvd_card_sub_one
      (E := F) hp hn (by rwa [Nat.card_units] at hpF)
  have hinj : Function.Injective (φ.comp (slLowerBlockHom n F)) :=
    injective_comp_slLowerBlockHom (n := n) (F := F) hker
  have heq : Nat.card (SpecialLinearGroup (Fin n) F) =
      Nat.card (φ.comp (slLowerBlockHom n F)).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rwa [heq] at hdvd

end CFSG.StandardType

end
