module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Plane

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}

omit [CharP K 2] in
theorem eq_hyp_of_coord_two (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (ha2 : a 2 = 0) (hb2 : b 2 = 0)
    (hP : a 0 * b 1 - a 1 * b 0 ≠ 0) (w : Fin 3 → K) :
    w = (w 2) • (Pi.single 2 1 : Fin 3 → K) + herm σ b w • a + herm σ a w • b := by
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ, hab, map_one]
  have hae : herm σ a (Pi.single 2 1 : Fin 3 → K) = 0 := by
    rw [herm_single_right, ha2, map_zero, zero_mul]
  have hbe : herm σ b (Pi.single 2 1 : Fin 3 → K) = 0 := by
    rw [herm_single_right, hb2, map_zero, zero_mul]
  set d : Fin 3 → K := w - ((w 2) • (Pi.single 2 1 : Fin 3 → K) + herm σ b w • a +
    herm σ a w • b) with hd
  have hda : herm σ a d = 0 := by
    rw [hd]
    simp only [herm_sub_right, herm_add_right, herm_smul_right, hae, ha, hab]
    ring
  have hdb : herm σ b d = 0 := by
    rw [hd]
    simp only [herm_sub_right, herm_add_right, herm_smul_right, hbe, hb, hba]
    ring
  have hd2 : d 2 = 0 := by
    rw [hd]
    simp [ha2, hb2]
  have hda' : σ (a 0) * d 0 + σ (a 1) * d 1 = 0 := by
    have := hda
    rw [herm_def, Fin.sum_univ_three, hd2, mul_zero, add_zero] at this
    exact this
  have hdb' : σ (b 0) * d 0 + σ (b 1) * d 1 = 0 := by
    have := hdb
    rw [herm_def, Fin.sum_univ_three, hd2, mul_zero, add_zero] at this
    exact this
  have hσP : σ (a 0) * σ (b 1) - σ (a 1) * σ (b 0) ≠ 0 := by
    have : σ (a 0) * σ (b 1) - σ (a 1) * σ (b 0) = σ (a 0 * b 1 - a 1 * b 0) := by
      simp only [map_sub, map_mul]
    rw [this]
    exact (map_ne_zero σ).2 hP
  have hd0 : d 0 = 0 := by
    have : (σ (a 0) * σ (b 1) - σ (a 1) * σ (b 0)) * d 0 = 0 := by
      linear_combination σ (b 1) * hda' - σ (a 1) * hdb'
    exact (mul_eq_zero.1 this).resolve_left hσP
  have hd1 : d 1 = 0 := by
    have : (σ (a 0) * σ (b 1) - σ (a 1) * σ (b 0)) * d 1 = 0 := by
      linear_combination σ (a 0) * hdb' - σ (b 0) * hda'
    exact (mul_eq_zero.1 this).resolve_left hσP
  have hdz : d = 0 := by
    funext i
    fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
  rw [hd, sub_eq_zero] at hdz
  exact hdz

theorem exists_planeElt_of_fix (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (ha2 : a 2 = 0) (hb2 : b 2 = 0)
    (hP : a 0 * b 1 - a 1 * b 0 ≠ 0) (g : SUid σ 3)
    (hg : g • (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1) :
    ∃ M : SpecialLinearGroup (Fin 2) (fixSub σ), planeElt hσ ha hb hab M = g := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ, hab, map_one]
  have hcomp := eq_hyp_of_coord_two hσ ha hb hab ha2 hb2 hP
  set e : Fin 3 → K := Pi.single 2 1 with he
  have hge : ∀ w : Fin 3 → K, (g • w) 2 = w 2 := by
    intro w
    have h1 : herm σ e (g • w) = (g • w) 2 := by
      rw [he, herm_single_left, map_one, one_mul]
    have h2' : herm σ e w = w 2 := by
      rw [he, herm_single_left, map_one, one_mul]
    rw [← h1, ← h2', ← hg, herm_smul_smul, hg]
  set α := herm σ b (g • a) with hα
  set γ := herm σ a (g • a) with hγ
  set β := herm σ b (g • b) with hβ
  set δ := herm σ a (g • b) with hδ
  have hga : g • a = α • a + γ • b := by
    have := hcomp (g • a)
    rw [hge, ha2] at this
    simpa using this
  have hgb : g • b = β • a + δ • b := by
    have := hcomp (g • b)
    rw [hge, hb2] at this
    simpa using this
  have e1 : σ α * γ + σ γ * α = 0 := by
    have := herm_smul_smul σ g a a
    rw [hga, ha] at this
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
      hba] at this
    linear_combination this
  have e2 : σ β * δ + σ δ * β = 0 := by
    have := herm_smul_smul σ g b b
    rw [hgb, hb] at this
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
      hba] at this
    linear_combination this
  have e3 : σ α * δ + σ γ * β = 1 := by
    have := herm_smul_smul σ g a b
    rw [hga, hgb, hab] at this
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
      hba] at this
    linear_combination this
  have e3' : α * σ δ + γ * σ β = 1 := by
    have := congrArg σ e3
    simp only [map_add, map_mul, hσ, map_one] at this
    linear_combination this
  have e4 : α * δ - β * γ = 1 := by
    let Pc : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![a, b, e] j i
    let D : Matrix (Fin 3) (Fin 3) K := !![α, β, 0; γ, δ, 0; 0, 0, 1]
    have hdet : (g : GL (Fin 3) K).val.det = 1 := ((mem_SUid_iff σ).1 g.2).1
    have hgP : (g : GL (Fin 3) K).val * Pc = Pc * D := by
      ext i j
      have hg_a : ((g : GL (Fin 3) K).val *ᵥ a) = α • a + γ • b := hga
      have hg_b : ((g : GL (Fin 3) K).val *ᵥ b) = β • a + δ • b := hgb
      have hg_e : ((g : GL (Fin 3) K).val *ᵥ e) = e := hg
      fin_cases j
      · have := congrFun hg_a i
        simpa [Pc, D, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct,
          mul_comm] using this
      · have := congrFun hg_b i
        simpa [Pc, D, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct,
          mul_comm] using this
      · have := congrFun hg_e i
        simpa [Pc, D, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct,
          mul_comm] using this
    have hPc : Pc.det = a 0 * b 1 - a 1 * b 0 := by
      simp [Pc, Matrix.det_fin_three, he, ha2, hb2]
      ring
    have hD : D.det = α * δ - β * γ := by
      simp [D, Matrix.det_fin_three]
    have := congrArg Matrix.det hgP
    rw [Matrix.det_mul, Matrix.det_mul, hdet, hPc, hD, one_mul] at this
    exact mul_left_cancel₀ hP (by linear_combination -this)
  have hσγ : σ γ = -γ := by linear_combination (-σ γ) * e4 + δ * e1 - γ * e3
  have hσα : σ α = α := by linear_combination (-σ α) * e4 + α * e3 - β * e1
  have hσδ : σ δ = δ := by linear_combination (-σ δ) * e4 + δ * e3' - γ * e2
  have hσβ : σ β = -β := by linear_combination (-σ β) * e4 + α * e2 - β * e3'
  rw [CharTwo.neg_eq] at hσγ hσβ
  let M : SpecialLinearGroup (Fin 2) (fixSub σ) :=
    ⟨!![⟨α, mem_fixSub.2 hσα⟩, ⟨β, mem_fixSub.2 hσβ⟩; ⟨γ, mem_fixSub.2 hσγ⟩,
        ⟨δ, mem_fixSub.2 hσδ⟩], by
      rw [Matrix.det_fin_two_of]
      apply Subtype.ext
      simpa using e4⟩
  refine ⟨M, ?_⟩
  have hent : ent M 0 0 = α ∧ ent M 0 1 = β ∧ ent M 1 0 = γ ∧ ent M 1 1 = δ := by
    simp [ent, M]
  obtain ⟨h00, h01, h10, h11⟩ := hent
  apply ext_smul σ
  intro v
  have hv : v = (v 2) • e + herm σ b v • a + herm σ a v • b := hcomp v
  have hgv : g • v = (v 2) • e + herm σ b v • (g • a) + herm σ a v • (g • b) := by
    conv_lhs => rw [hv]
    rw [smul_add, smul_add, smul_comm g (v 2), smul_comm g (herm σ b v),
      smul_comm g (herm σ a v), hg]
  rw [planeElt_smul, hgv, hga, hgb, h00, h01, h10, h11]
  generalize herm σ b v = s at hv ⊢
  generalize herm σ a v = t at hv ⊢
  generalize v 2 = w at hv ⊢
  rw [hv]
  module

end CFSG.RankThree.PartOne.SEITZ2
