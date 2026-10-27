module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime

public section

namespace CFSG.RankThree.GF2n.Smith81.S81C

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n.Smith81
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.ComponentClassification.RankTwoClassical.URigid CFSG.SeitzReduction.UnitaryPilot
  CFSG.LinearGroups

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem su_transv_form {g : GL (Fin n) K} (hg : g ∈ StatedSU n (2 ^ f) K)
    (hg2 : ((g : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1) = 0)
    (hr : ((g : Matrix (Fin n) (Fin n) K) - 1).rank = 1) :
    ∃ b : Fin n → K, b ≠ 0 ∧ (h.bar ∘ b) ⬝ᵥ b = 0 ∧
      (g : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec b (h.bar ∘ b) := by
  haveI := h.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadd : ∀ M : Matrix (Fin n) (Fin n) K, M + M = 0 := fun M => by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  have hsum : (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) + 1 = 0 := by
    have e : ((g : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1)
        = (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)
          - ((g : Matrix (Fin n) (Fin n) K) + (g : Matrix (Fin n) (Fin n) K)) + 1 := by
      simp only [sub_mul, mul_sub, mul_one, one_mul]
      abel
    rw [e, hadd (g : Matrix (Fin n) (Fin n) K), sub_zero] at hg2
    exact hg2
  have hgg : (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    calc (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)
        = (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)
          + ((1 : Matrix (Fin n) (Fin n) K) + 1) := by
          rw [hadd (1 : Matrix (Fin n) (Fin n) K), add_zero]
      _ = ((g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) + 1) + 1 := by
          rw [add_assoc]
      _ = 1 := by rw [hsum, zero_add]
  have hgone : g ≠ 1 := by
    intro h1
    rw [h1, Units.val_one, sub_self, Matrix.rank_zero] at hr
    exact zero_ne_one hr
  have hg2' : g ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
    exact hgg
  have hord : orderOf g = 2 := orderOf_eq_prime hg2' hgone
  obtain ⟨u, c, hu, hc0, hcσ, huu, huc⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.URigid.exists_transvection_eq h hg hord hr
  have huu' : (h.bar ∘ u) ⬝ᵥ u = 0 := huu
  obtain ⟨l, hl⟩ := h.normHom_surjective ⟨c, h.mem_fixedField.2 hcσ⟩
  have hlc : l * h.bar l = c := by
    have := congrArg Subtype.val hl
    simpa [UnitaryFieldData.norm] using this
  have hl0 : l ≠ 0 := by
    intro h0
    apply hc0
    rw [← hlc, h0, zero_mul]
  refine ⟨l • u, smul_ne_zero hl0 hu, ?_, ?_⟩
  · have hdot : (h.bar ∘ (l • u)) ⬝ᵥ (l • u) = (h.bar l * l) * ((h.bar ∘ u) ⬝ᵥ u) := by
      simp only [dotProduct, Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hdot, huu', mul_zero]
  · have hmat : vecMulVec (l • u) (h.bar ∘ (l • u)) = c • vecMulVec u (h.bar ∘ u) := by
      ext i j
      simp only [vecMulVec_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul,
        Matrix.smul_apply]
      rw [← hlc]
      ring
    rw [hmat]
    exact sub_eq_iff_eq_add'.mp huc

private theorem s81c_mulVecLin_eq (b : Fin n → K) :
    (1 + vecMulVec b (h.bar ∘ b) : Matrix (Fin n) (Fin n) K).mulVecLin =
      hermTransvection (stdHermForm h n) b 1 := by
  refine LinearMap.ext fun x => ?_
  rw [hermTransvection_apply, one_mul, Matrix.mulVecLin_apply, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rfl

private theorem s81c_mulVecLin_iff (b : Fin n → K) (M : Matrix (Fin n) (Fin n) K) :
    M.mulVecLin = hermTransvection (stdHermForm h n) b 1 ↔
      M = 1 + vecMulVec b (h.bar ∘ b) :=
  ⟨fun hM => CFSG.SeitzReduction.UnitaryPilot.eq_of_mulVecLin_eq
      (hM.trans (s81c_mulVecLin_eq h b).symm),
    fun hM => by subst hM; exact s81c_mulVecLin_eq h b⟩

theorem su_conj_tvMat (hn : 3 ≤ n) {b b' : Fin n → K} (hb0 : b ≠ 0) (hb : (h.bar ∘ b) ⬝ᵥ b = 0)
    (hb0' : b' ≠ 0) (hb' : (h.bar ∘ b') ⬝ᵥ b' = 0) {g g' : GL (Fin n) K}
    (hgS : g ∈ StatedSU n (2 ^ f) K) (hgS' : g' ∈ StatedSU n (2 ^ f) K)
    (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec b (h.bar ∘ b))
    (hg' : (g' : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec b' (h.bar ∘ b')) :
    ∃ W : GL (Fin n) K, W ∈ StatedSU n (2 ^ f) K ∧ W * g * W⁻¹ = g' := by
  have hbb : stdHermForm h n b b = 0 := by
    rw [stdHermForm_apply]
    exact hb
  have hbb' : stdHermForm h n b' b' = 0 := by
    rw [stdHermForm_apply]
    exact hb'
  obtain ⟨W0, hW0⟩ :=
    CFSG.SeitzReduction.UnitaryPilot.exists_unitarySU_mulVec_eq h hn hb0 hbb hb0' hbb'
  have hW0b : W0 • b = b' := hW0
  obtain ⟨x, rfl⟩ : ∃ x : unitarySU 2 f K n, (x : GL (Fin n) K) = g := ⟨⟨g, hgS⟩, rfl⟩
  obtain ⟨y, rfl⟩ : ∃ y : unitarySU 2 f K n, (y : GL (Fin n) K) = g' := ⟨⟨g', hgS'⟩, rfl⟩
  have hx : mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hermTransvection (stdHermForm h n) b 1 := (s81c_mulVecLin_iff h b _).2 hg
  have hy : mulVecLin ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hermTransvection (stdHermForm h n) b' 1 := (s81c_mulVecLin_iff h b' _).2 hg'
  have hconj := CFSG.SeitzReduction.UnitaryPilot.mulVecLin_conj_hermTransvection_unitarySU h W0 hx
  rw [hW0b] at hconj
  have heq : ((W0 * x * W0⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) = (y : GL (Fin n) K) :=
    Units.ext (CFSG.SeitzReduction.UnitaryPilot.eq_of_mulVecLin_eq (hconj.trans hy.symm))
  refine ⟨(W0 : GL (Fin n) K), W0.2, ?_⟩
  exact heq

end CFSG.RankThree.GF2n.Smith81.S81C

