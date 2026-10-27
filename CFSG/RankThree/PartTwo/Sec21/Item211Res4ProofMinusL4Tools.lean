module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusL4
public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusCore
public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusQuat

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open scoped MatrixGroups

namespace Item211Res4Proof

open Item228Census3Proof Item228Census5Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def blkDiagHom : Matrix (Fin 2) (Fin 2) K →* Matrix V₄ V₄ K where
  toFun M := fromBlocks M 0 0 M
  map_one' := fromBlocks_one
  map_mul' M N := by
    rw [fromBlocks_multiply]
    simp

@[expose] noncomputable def blkDiag : SL(2, K) →* GL V₄ K :=
  (Units.map blkDiagHom).comp SpecialLinearGroup.toGL

theorem coe_blkDiag (B : SL(2, K)) :
    ((blkDiag B : GL V₄ K) : Matrix V₄ V₄ K) = fromBlocks (B : Matrix (Fin 2) (Fin 2) K) 0 0 B :=
  rfl

theorem blkDiag_mem_ker (B : SL(2, K)) :
    blkDiag B ∈ (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_blkDiag, det_fromBlocks_zero₂₁, B.2, mul_one,
    Units.val_one]

theorem eq_one_or_neg_one_of_mk_blkDiag {B : SL(2, K)}
    (h : ProjGenLinGroup.mk (blkDiag B) = 1) : B = 1 ∨ B = -1 := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨s, hs⟩ := h
  have e := congrArg (fun x : GL V₄ K => (x : Matrix V₄ V₄ K)) hs
  simp only [GeneralLinearGroup.coe_scalar, coe_blkDiag, scalar_eq_fromBlocks] at e
  obtain ⟨e1, -, -, -⟩ := Matrix.fromBlocks_inj.mp e
  apply sl2_eq_one_or_neg_one_of_mem_center
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨s, ?_, e1⟩
  have hdet := B.2
  rw [← e1, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ] at hdet
  exact hdet

theorem quat_elem_commute {a c : K} {x : Matrix V₄ V₄ K}
    (hx : x = 1 ∨ x = quatBlockU a c ∨ x = quatBlockV ∨ x = quatBlockU a c * quatBlockV)
    (M : Matrix (Fin 2) (Fin 2) K) : x * fromBlocks M 0 0 M = fromBlocks M 0 0 M * x := by
  rcases hx with rfl | rfl | rfl | rfl
  · rw [Matrix.one_mul, Matrix.mul_one]
  · exact (quatBlockU_commute a c M).symm
  · exact (quatBlockV_commute M).symm
  · rw [Matrix.mul_assoc, ← quatBlockV_commute M, ← Matrix.mul_assoc, ← quatBlockU_commute a c M,
      Matrix.mul_assoc]

theorem quat_centralizer_decomp (h2 : (2 : K) ≠ 0) {a c : K} (hac : a * a + c * c = -1)
    (g : GL V₄ K)
    (hgU : (g : Matrix V₄ V₄ K) * quatBlockU a c = quatBlockU a c * (g : Matrix V₄ V₄ K) ∨
      (g : Matrix V₄ V₄ K) * quatBlockU a c = -(quatBlockU a c * (g : Matrix V₄ V₄ K)))
    (hgV : (g : Matrix V₄ V₄ K) * quatBlockV = quatBlockV * (g : Matrix V₄ V₄ K) ∨
      (g : Matrix V₄ V₄ K) * quatBlockV = -(quatBlockV * (g : Matrix V₄ V₄ K))) :
    ∃ (x : Matrix V₄ V₄ K) (Y : GL (Fin 2) K),
      (x = 1 ∨ x = quatBlockU a c ∨ x = quatBlockV ∨ x = quatBlockU a c * quatBlockV) ∧
        (g : Matrix V₄ V₄ K) = x * fromBlocks (Y : Matrix (Fin 2) (Fin 2) K) 0 0 Y := by
  obtain ⟨x, x', hxx', hx, hc1, hc2⟩ := quat_sign_decomp (quatBlockU_mul_self hac)
    quatBlockV_mul_self (quatBlockU_mul_V a c) hgU hgV
  have hX := eq_fromBlocks_of_commute_quat h2 hac hc1 hc2
  set Y0 := (x' * (g : Matrix V₄ V₄ K)).toBlocks₁₁ with hY0
  have hdetY : Y0.det ≠ 0 := by
    have hx'x : x' * x = 1 := mul_eq_one_comm.mp hxx'
    have hdx' : x'.det ≠ 0 := by
      intro h
      have := congrArg Matrix.det hx'x
      rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hdg : (g : Matrix V₄ V₄ K).det ≠ 0 := by
      have := (GeneralLinearGroup.det g).ne_zero
      rwa [GeneralLinearGroup.val_det_apply] at this
    have e := congrArg Matrix.det hX
    rw [Matrix.det_mul, det_fromBlocks_zero₂₁] at e
    intro h0
    rw [h0, zero_mul] at e
    exact mul_ne_zero hdx' hdg e
  refine ⟨x, GeneralLinearGroup.mkOfDetNeZero Y0 hdetY, hx, ?_⟩
  change (g : Matrix V₄ V₄ K) = x * fromBlocks Y0 0 0 Y0
  rw [← hX, ← Matrix.mul_assoc, hxx', Matrix.one_mul]

theorem cubeBlockHom_algebraMap (M : Matrix (Fin 2) (Fin 2) K) :
    cubeBlockHom (M.map (algebraMap K (cubeAlg K))) =
      fromBlocks (M 0 0 • 1) (M 0 1 • 1) (M 1 0 • 1) (M 1 1 • 1) := by
  simp [cubeBlockHom, Algebra.algebraMap_eq_smul_one]

theorem cubeBlockHom_commute (M : Matrix (Fin 2) (Fin 2) (cubeAlg K)) :
    cubeBlockHom M * fromBlocks (cubeMat K) 0 0 (cubeMat K) =
      fromBlocks (cubeMat K) 0 0 (cubeMat K) * cubeBlockHom M := by
  change fromBlocks _ _ _ _ * _ = _ * fromBlocks _ _ _ _
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [mem_cubeAlg.mp (M 0 0).2, mem_cubeAlg.mp (M 0 1).2, mem_cubeAlg.mp (M 1 0).2,
    mem_cubeAlg.mp (M 1 1).2]

theorem commute_or_anticommute_of_mk {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (G : Subgroup (GL n K)) {g h : G}
    (hc : projRestrict G g * projRestrict G h = projRestrict G h * projRestrict G g)
    (hh : ((h : GL n K) : Matrix n n K) * (h : GL n K) = -1) :
    ((g : GL n K) : Matrix n n K) * (h : GL n K) = (h : GL n K) * (g : GL n K) ∨
      ((g : GL n K) : Matrix n n K) * (h : GL n K) = -((h : GL n K) * (g : GL n K)) := by
  have hc' : projRestrict G (h * g) = projRestrict G (g * h) := by
    rw [map_mul, map_mul, hc]
  obtain ⟨s, hs⟩ := (projRestrict_eq_iff G).mp hc'
  set gm := ((g : GL n K) : Matrix n n K)
  set hm := ((h : GL n K) : Matrix n n K)
  have e : gm * hm = (s : K) • (hm * gm) := by
    have := congrArg (fun x : GL n K => (x : Matrix n n K)) hs
    simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [← this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
  have e2 : gm * (hm * hm) = ((s : K) * s) • (hm * hm * gm) := by
    calc gm * (hm * hm) = (gm * hm) * hm := (Matrix.mul_assoc _ _ _).symm
      _ = ((s : K) • (hm * gm)) * hm := by rw [e]
      _ = (s : K) • (hm * (gm * hm)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (s : K) • (hm * ((s : K) • (hm * gm))) := by rw [e]
      _ = ((s : K) * s) • (hm * hm * gm) := by
          rw [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hh, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, smul_neg, neg_inj] at e2
  have hg0 : gm ≠ 0 := by
    intro h0
    have h1 : gm * ((g⁻¹ : G) : GL n K) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    rw [h0, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hs2 : (s : K) * s = 1 := by
    have h3 : (1 - (s : K) * s) • gm = 0 := by rw [sub_smul, one_smul, ← e2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact (sub_eq_zero.mp h4).symm
    · exact absurd h4 hg0
  rcases mul_self_eq_one_iff.mp hs2 with h5 | h5
  · left
    rw [e, h5, one_smul]
  · right
    rw [e, h5, neg_one_smul]

theorem exists_ne_one_ne {M : Type} [Group M] {T : Subgroup M} (hT4 : Nat.card T = 4) (u : M) :
    ∃ t ∈ T, t ≠ 1 ∧ t ≠ u := by
  classical
  by_contra h
  push Not at h
  have hsub : ∀ t ∈ T, t = 1 ∨ t = u := fun t ht => by
    by_cases h1 : t = 1
    · exact Or.inl h1
    · exact Or.inr (h t ht h1)
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT4]; norm_num)
  have : Fintype T := Fintype.ofFinite T
  have hle : Fintype.card T ≤ 2 := by
    calc Fintype.card T ≤ Fintype.card ({1, u} : Finset M) := by
          refine Fintype.card_le_of_injective (fun t => ⟨t.1, ?_⟩) ?_
          · rcases hsub t.1 t.2 with h | h
            · simp [h]
            · simp [h]
          · intro a b hab
            exact Subtype.ext (by simpa using congrArg Subtype.val hab)
      _ ≤ 2 := by
          rw [Fintype.card_coe]
          exact Finset.card_le_two
  rw [← Nat.card_eq_fintype_card, hT4] at hle
  omega

theorem quat_of_commuting_involutions {M : Type} [Group M] {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (ι : SL(2, R) →* M) (hιker : ∀ x, ι x = 1 ↔ x = 1 ∨ x = -1)
    {U V : SL(2, R)} (hU2 : ι U * ι U = 1) (hV2 : ι V * ι V = 1)
    (hUV : ι U * ι V = ι V * ι U) (hU1 : ι U ≠ 1) (hV1 : ι V ≠ 1) (hVU : ι V ≠ ι U) :
    (U : Matrix (Fin 2) (Fin 2) R) * U = -1 ∧ (V : Matrix (Fin 2) (Fin 2) R) * V = -1 ∧
      (U : Matrix (Fin 2) (Fin 2) R) * V = -((V : Matrix (Fin 2) (Fin 2) R) * U) := by
  have hneg : ∀ x : SL(2, R), ι (-1 * x) = ι x := fun x => by
    rw [map_mul, (hιker _).mpr (Or.inr rfl), one_mul]
  have hsq : ∀ x : SL(2, R), ι x * ι x = 1 → ι x ≠ 1 → x * x = -1 := by
    intro x hx hx1
    have h1 : ι (x * x) = 1 := by rw [map_mul, hx]
    rcases (hιker _).mp h1 with h | h
    · exfalso
      apply hx1
      rcases sl2_eq_one_or_neg_one_of_sq h2 (by rw [sq]; exact h) with h' | h'
      · rw [h', map_one]
      · rw [h']
        exact (hιker _).mpr (Or.inr rfl)
    · exact h
  have hU := hsq U hU2 hU1
  have hV := hsq V hV2 hV1
  have hc : ι (U * V * U⁻¹ * V⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hUV]
    group
  have hUVa : U * V = -1 * (V * U) := by
    rcases (hιker _).mp hc with h | h
    · exfalso
      have hcomm : U * V = V * U := by
        have e : U * V = U * V * U⁻¹ * V⁻¹ * (V * U) := by group
        rw [e, h, one_mul]
      have hUV2 : (U * V) * (U * V) = 1 := by
        calc (U * V) * (U * V) = (U * U) * (V * V) := by
              rw [mul_assoc, ← mul_assoc V U V, ← hcomm]; group
          _ = 1 := by
              rw [hU, hV]
              apply Subtype.ext
              simp
      rcases sl2_eq_one_or_neg_one_of_sq h2 (by rw [sq]; exact hUV2) with h' | h'
      · apply hVU
        have e : V = U⁻¹ := eq_inv_of_mul_eq_one_right h'
        rw [e, map_inv]
        exact inv_eq_of_mul_eq_one_right hU2
      · apply hVU
        have e : V = -1 * U⁻¹ := by
          have e1 : U * V = -1 := h'
          calc V = U⁻¹ * (U * V) := by group
            _ = U⁻¹ * -1 := by rw [e1]
            _ = -1 * U⁻¹ := by
                apply Subtype.ext
                simp
        rw [e, hneg, map_inv]
        exact inv_eq_of_mul_eq_one_right hU2
    · calc U * V = U * V * U⁻¹ * V⁻¹ * (V * U) := by group
        _ = -1 * (V * U) := by rw [h]
  refine ⟨?_, ?_, ?_⟩
  · have e := congrArg (fun x : SL(2, R) => (x : Matrix (Fin 2) (Fin 2) R)) hU
    simpa using e
  · have e := congrArg (fun x : SL(2, R) => (x : Matrix (Fin 2) (Fin 2) R)) hV
    simpa using e
  · have e := congrArg (fun x : SL(2, R) => (x : Matrix (Fin 2) (Fin 2) R)) hUVa
    simpa using e

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
