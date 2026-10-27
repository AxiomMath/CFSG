module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LongPairFinish

@[expose] public section

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal

open CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem Matrix

open CFSG.SeitzReduction.F4Pilot

open CFSG.Timmesfeld.ARS.CaseM

open CFSG.StandardType.F4ExplicitPos.Sp6PairDescent

open CFSG.StandardType.F4ExplicitPos.LongPairFinish

namespace CFSG.StandardType.F4ExplicitPos.SingleRootRecognition

theorem caseM_spForm_eq_bilin {k : Type} [Field k] [CharP k 2]
    (x y : Fin 3 ⊕ Fin 3 → k) :
    spForm x y = CFSG.ClassicalGroups.Symplectic.spForm 3 k x y := by
  rw [CFSG.ClassicalGroups.Symplectic.spForm_apply]
  rfl

theorem exists_rational_dual {k : Type} [Field k] [CharP k 2]
    {v : Fin 3 ⊕ Fin 3 → k} (hv : v ≠ 0) :
    ∃ w : Fin 3 ⊕ Fin 3 → k, spForm v w = 1 := by
  obtain ⟨y, hy⟩ := CFSG.Timmesfeld.Transvection.ModelRank.exists_spForm_ne_zero hv
  refine ⟨(spForm v y)⁻¹ • y, ?_⟩
  rw [CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right']
  exact inv_mul_cancel₀ hy

theorem alternating_frame_completion {k : Type} [Field k] [CharP k 2]
    {a1 a2 : Fin 3 ⊕ Fin 3 → k} (hli : LinearIndependent k ![a1, a2])
    (h12 : spForm a1 a2 = 0) :
    ∃ b1 b2 : Fin 3 ⊕ Fin 3 → k,
      spForm a1 b1 = 1 ∧ spForm a2 b2 = 1 ∧
      spForm b1 b2 = 0 ∧ spForm a1 b2 = 0 ∧ spForm a2 b1 = 0 := by
  have hnd : (CFSG.ClassicalGroups.Symplectic.spForm 3 k).Nondegenerate :=
    CFSG.ClassicalGroups.Symplectic.spForm_nondegenerate
  have hsurj := CFSG.ClassicalGroups.Alternating.alternating_pairing_surjectivity
    (B := CFSG.ClassicalGroups.Symplectic.spForm 3 k) hnd hli
  obtain ⟨b1, hb1⟩ := hsurj ![1, 0]
  obtain ⟨b2', hb2'⟩ := hsurj ![0, 1]
  have hb1a : spForm a1 b1 = 1 := by
    rw [caseM_spForm_eq_bilin]
    exact congrFun hb1 0
  have hb1b : spForm a2 b1 = 0 := by
    rw [caseM_spForm_eq_bilin]
    exact congrFun hb1 1
  have hb2a : spForm a1 b2' = 0 := by
    rw [caseM_spForm_eq_bilin]
    exact congrFun hb2' 0
  have hb2b : spForm a2 b2' = 1 := by
    rw [caseM_spForm_eq_bilin]
    exact congrFun hb2' 1
  refine ⟨b1, b2' + (spForm b1 b2') • a1, hb1a, ?_, ?_, ?_, hb1b⟩
  · rw [CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right', hb2b]
    have h21 : spForm a2 a1 = 0 := by rw [spForm_comm, h12, neg_zero]
    rw [h21, mul_zero, add_zero]
  · rw [CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right']
    have hb1a' : spForm b1 a1 = 1 := by rw [spForm_comm, hb1a, CharTwo.neg_eq]
    rw [hb1a', mul_one]
    exact CharTwo.add_self_eq_zero _
  · rw [CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right', hb2a, spForm_self, mul_zero,
      add_zero]

theorem single_long_root_recognition {k Ω : Type} [Field k] [Finite k] [CharP k 2]
    [Field Ω] [Algebra k Ω] [CharP Ω 2]
    {P : Subgroup (StatedSp 3 k)} (hP : Nat.card P = Nat.card k)
    {β : Fin 3 → ℤ} (hβ : β ∈ (Symplectic.rootDatum 3 Ω).roots)
    (hl : GGLongRoot (Symplectic.rootDatum 3 Ω) β) (vΩ : StatedSp 3 Ω)
    (hplus : P.map (statedSpMap (algebraMap k Ω) 3) ≤
      ((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom) :
    ∃ β' ∈ (Symplectic.rootDatum 3 k).roots, ∃ u : StatedSp 3 k,
      P = ((Symplectic.rootDatum 3 k).rootGroup β').map (MulAut.conj u).toMonoidHom := by
  obtain ⟨v, w, hvw, hXplus, -⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_matTransvGroup_eq_conj_rootGroup_Sp 3 Ω hβ hl vΩ
  have hv : v ≠ 0 := by
    intro h0
    rw [h0] at hvw
    simp at hvw
  have hXv : IsTransGroup v
      (((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom) :=
    isTransGroup_of_map_subtype_eq_matTransvGroup hXplus
  obtain ⟨v₀, hv₀, hPv, μ, _hμ, _hvrel⟩ := long_case_recognition hP hv hXv hplus
  obtain ⟨w₀, hw0⟩ := exists_rational_dual hv₀
  obtain ⟨β', hβ', _hl', u, hu1, -⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSp 3 k (by norm_num) v₀ w₀ hw0
  refine ⟨β', hβ', u, ?_⟩
  have h1 : P.map (StatedSp 3 k).subtype =
      matTransvGroup v₀ (Matrix.mulVec (spGram 3 k) v₀) :=
    map_subtype_eq_matTransvGroup_of_isTransGroup hPv
  exact Subgroup.map_injective (f := (StatedSp 3 k).subtype)
    (Subgroup.subtype_injective (StatedSp 3 k)) (h1.trans hu1.symm)

theorem single_short_root_recognition {k : Type} [Field k] [CharP k 2]
    {P : Subgroup (StatedSp 3 k)} {a1 a2 : Fin 3 ⊕ Fin 3 → k}
    (hli : LinearIndependent k ![a1, a2])
    (h12 : spForm a1 a2 = 0)
    (hP : P.map (StatedSp 3 k).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) a1 a2) :
    ∃ β' ∈ (Symplectic.rootDatum 3 k).roots, ∃ u : StatedSp 3 k,
      P = ((Symplectic.rootDatum 3 k).rootGroup β').map (MulAut.conj u).toMonoidHom := by
  obtain ⟨b1, b2, h11, h22, h00, h12b, h21b⟩ := alternating_frame_completion hli h12
  obtain ⟨β', hβ', -, u, hu1, -⟩ :=
    exists_conj_rootGroup_eq_altSiegelGroup_PSp 3 k (by norm_num) a1 a2 b1 b2
      h11 h22 ⟨h12, h00, h12b, h21b⟩
  refine ⟨β', hβ', u, ?_⟩
  exact Subgroup.map_injective (f := (StatedSp 3 k).subtype)
    (Subgroup.subtype_injective (StatedSp 3 k)) (hP.trans hu1.symm)

theorem singleRootRecognition {k Ω : Type} [Field k] [Finite k] [CharP k 2]
    [Field Ω] [Algebra k Ω] [CharP Ω 2]
    {P : Subgroup (StatedSp 3 k)} (hP : Nat.card P = Nat.card k)
    {β : Fin 3 → ℤ} (hβ : β ∈ (Symplectic.rootDatum 3 Ω).roots)
    (vΩ : StatedSp 3 Ω)
    (hplus : P.map (statedSpMap (algebraMap k Ω) 3) ≤
      ((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom)
    (hshort : ¬ GGLongRoot (Symplectic.rootDatum 3 Ω) β →
      ∃ (a1 a2 : Fin 3 ⊕ Fin 3 → k), LinearIndependent k ![a1, a2] ∧
        spForm a1 a2 = 0 ∧
        P.map (StatedSp 3 k).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) a1 a2) :
    ∃ β' ∈ (Symplectic.rootDatum 3 k).roots, ∃ u : StatedSp 3 k,
      P = ((Symplectic.rootDatum 3 k).rootGroup β').map (MulAut.conj u).toMonoidHom := by
  by_cases hl : GGLongRoot (Symplectic.rootDatum 3 Ω) β
  · exact single_long_root_recognition hP hβ hl vΩ hplus
  · obtain ⟨a1, a2, hli, h12, hPalt⟩ := hshort hl
    exact single_short_root_recognition hli h12 hPalt

end CFSG.StandardType.F4ExplicitPos.SingleRootRecognition

end

end
