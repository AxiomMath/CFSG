module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqPar
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructStab
import CFSG.LieType.Chevalley.GraphFixedParabolicPointwiseRigidity

public section

namespace CFSG.Quasithin.H13.F431.D4q.NFq

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

theorem fieldActor_Qg (δ : K ≃+* K) {x : ModGL TwistTag.D4.tag K} (hx : x ∈ d4Vr K σ) :
    Units.map (entrywiseHom δ.toRingHom) x ∈ d4Vr K σ := by
  have hδ : ∀ c, δ (σ c) = σ (δ c) := ringEquiv_comm_of_finite σ δ
  have hS : ∀ γ ∈ simpleComplementRoots TwistTag.D4 (⟨0, by decide⟩ :
      Fin TwistTag.D4.foldedTag.rank), IsRoot TwistTag.D4.tag γ :=
    fun γ hγ => (simpleComplementRoots_pos _ γ hγ).1
  have h := map_diagFieldAut_rootSpan_inf (t := TwistTag.D4) (σ := σ.toRingHom) (b := 1)
    (δ := δ) (fun i => by simp) hδ hS
  have hx' : x ∈ rootSpan TwistTag.D4.tag K (simpleComplementRoots TwistTag.D4
      (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) ⊓
        twistedFixedGroup TwistTag.D4 K σ.toRingHom := hx
  have h2 := Subgroup.mem_map_of_mem (diagFieldAut TwistTag.D4.tag 1 δ).toMonoidHom hx'
  rw [h] at h2
  have e : (diagFieldAut TwistTag.D4.tag 1 δ) x = Units.map (entrywiseHom δ.toRingHom) x := by
    rw [diagFieldAut_apply, rootDiagUnit_one]
    simp
  exact e ▸ h2

include hf hK hσq in
theorem Ust_ne_bot : Ust σ ≠ ⊥ := by
  intro h
  have h1 := card_U σ hf hK hσq
  have h2 : Nat.card (Ust σ) = Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)).toEquiv
  rw [h, Subgroup.card_bot, h1] at h2
  have : 1 < (2 ^ f) ^ 12 :=
    Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) (by norm_num))
  omega

include hf hK hσq in
theorem mem_Pst0_of_mem_normalizer {g : Cm σ} (hg : g ∈ Subgroup.normalizer (Pst0 σ : Set (Cm σ))) :
    g ∈ Pst0 σ := by
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσq
  have hsimp := CFSG.Quasithin.H13.F431.D4q.Hex.d4_fixed_isSimpleGroup σ hf hK hσq
  rcases hS.coatom₀.le_iff.mp (Subgroup.le_normalizer (H := Pst0 σ)) with h | h
  · have hn : (Pst0 σ).Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Pst0 σ) with h0 | h0
    · exfalso
      refine Ust_ne_bot σ hf hK hσq (eq_bot_iff.mpr fun u hu => ?_)
      have h1 := hS.le₀ (Subgroup.le_normalizer hu)
      have h2 : u ∈ Pst0 σ := h1
      rw [h0] at h2
      exact h2
    · exact absurd h0 hS.coatom₀.1
  · have hg' := hg
    rw [h] at hg'
    exact hg'

include hf hK hσq in
theorem exists_conj_of_autStab_Pst0 {φ : MulAut (Cm σ)} (hφ : φ ∈ autStab (Pst0 σ)) :
    ∃ g ∈ Pst0 σ, ∃ δ : K ≃+* K, φ = MulAut.conj g * fieldActor σ δ := by
  obtain ⟨g, hg⟩ := exists_conj_fieldActor σ hf hK hσq φ
  generalize theta σ hf hK hσq φ = δ at hg
  have h1 : MulAut.conj g ∈ autStab (Pst0 σ) := by
    have : MulAut.conj g = φ * (fieldActor σ δ)⁻¹ := by
      rw [hg]
      group
    rw [this]
    exact mul_mem hφ (inv_mem (fieldActor_mem_autStab_Pst0 σ hf hK hσq _))
  refine ⟨g, mem_Pst0_of_mem_normalizer σ hf hK hσq ?_, _, hg⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h2 := h1 x
  rw [MulAut.conj_apply] at h2
  exact h2

include hf hK hσq in
theorem aut_Qg {φ : MulAut (Cm σ)} (hφ : φ ∈ autStab (Pst0 σ)) {x : Cm σ}
    (hx : (x : ModGL TwistTag.D4.tag K) ∈ d4Vr K σ) :
    ((φ x : Cm σ) : ModGL TwistTag.D4.tag K) ∈ d4Vr K σ := by
  obtain ⟨g, hg, δ, rfl⟩ := exists_conj_of_autStab_Pst0 σ hf hK hσq hφ
  have h1 := fieldActor_Qg σ δ hx
  rw [← coe_fieldActor] at h1
  have h2 := Pst0_conj_Qg σ hg h1
  exact h2

include hf hK hσq in
theorem aut_Zg {φ : MulAut (Cm σ)} (hφ : φ ∈ autStab (Pst0 σ)) {x : Cm σ}
    (hx : (x : ModGL TwistTag.D4.tag K) ∈ d4Zz K σ) :
    ((φ x : Cm σ) : ModGL TwistTag.D4.tag K) ∈ d4Zz K σ := by
  have hσ := sigma_cube σ hK hσq
  refine (Zg_iff_center σ hσ).1 ⟨aut_Qg σ hf hK hσq hφ (Zg_le_Qg σ hσ hx), fun y hy => ?_⟩
  have hyC : y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (graphFixedSimpleComplement_le _ hy)
  have hy' := aut_Qg σ hf hK hσq (inv_mem hφ) (x := ⟨y, hyC⟩) hy
  have hxx : x * (φ⁻¹ ⟨y, hyC⟩) = (φ⁻¹ ⟨y, hyC⟩) * x :=
    Subtype.ext (Zg_central_Qg σ hσ hy' hx).symm
  have h2 := congrArg φ hxx
  rw [map_mul, map_mul, MulAut.apply_inv_self] at h2
  exact congrArg Subtype.val h2

end CFSG.Quasithin.H13.F431.D4q.NFq
