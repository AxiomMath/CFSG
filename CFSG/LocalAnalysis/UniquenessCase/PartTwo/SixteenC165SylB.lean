module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165SylA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

@[expose] def tAut : MulAut W :=
  MulAut.congr S.matEquiv.symm
    (AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin 2) (Fin 2) S.K))

theorem vec_tAut (w : W) : S.vec (tAut S w) = ofMat (toMat (S.vec w))ᵀ := by
  simp [tAut, matEquiv, MulAut.congr, vec_ofVec]

theorem tAut_smul (c : S.K) (w : W) : tAut S (S.smul c w) = S.smul c (tAut S w) := by
  apply S.vec_injective
  rw [vec_tAut, vec_smul, toMat_smul, Matrix.transpose_smul, ofMat_smul]
  rw [vec_smul, vec_tAut]

theorem Q_tAut (w : W) : S.Q (tAut S w) = S.Q w := by
  simp only [S.Q_eq_det, vec_tAut, toMat_ofMat, Matrix.det_transpose]

theorem tAut_mem_isoSub : tAut S ∈ isoSub S := by
  refine (mem_isoSub_iff S).mpr ⟨?_, Q_tAut S⟩
  exact (mem_linSub_iff S).mpr (tAut_smul S)

theorem tAut_mul_self : tAut S * tAut S = 1 := by
  ext w
  rw [MulAut.mul_apply, MulAut.one_apply]
  apply S.vec_injective
  rw [vec_tAut, vec_tAut, toMat_ofMat, Matrix.transpose_transpose, ofMat_toMat]

private theorem tAut_inv : (tAut S)⁻¹ = tAut S :=
  inv_eq_of_mul_eq_one_right (tAut_mul_self S)

theorem tAut_mul_jHom (p : SL(2, S.K) × SL(2, S.K)) :
    tAut S * S.jHom p * (tAut S)⁻¹ = S.jHom (p.2, p.1) := by
  rw [tAut_inv S]
  ext w
  apply S.vec_injective
  rw [MulAut.mul_apply, MulAut.mul_apply]
  simp only [S.vec_tAut, S.vec_jHom, toMat_ofMat, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

private theorem tAut_conj_mem_u0Sub {h : MulAut W} (hh : h ∈ u0Sub S) :
    tAut S * h * (tAut S)⁻¹ ∈ u0Sub S := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hh
  obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
  rw [tAut_mul_jHom S p]
  exact Subgroup.mem_map.mpr ⟨(p.2, p.1), Subgroup.mem_prod.mpr ⟨hp2, hp1⟩, rfl⟩

private theorem uHom_coe {K : Type} [Field K] (a : Multiplicative K) :
    ((uHom K a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![1, Multiplicative.toAdd a; 0, 1] := rfl

theorem tAut_not_mem_u0Sub : tAut S ∉ u0Sub S := by
  intro hmem
  obtain ⟨p, hp, hpj⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hp1
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hp2
  have hp_eq : S.jHom (uHom S.K a, uHom S.K b) = tAut S := by
    have h1 : p = (uHom S.K a, uHom S.K b) := by rw [ha, hb, Prod.mk.eta]
    rwa [h1] at hpj
  let M : Matrix (Fin 2) (Fin 2) S.K := !![0, 1; 0, 0]
  let w0 : W := S.ofVec (ofMat M)
  have hmat : (uHom S.K a : Matrix (Fin 2) (Fin 2) S.K) * M *
      ((uHom S.K b : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K)ᵀ = Mᵀ := by
    have hw : toMat (S.vec (S.jHom (uHom S.K a, uHom S.K b) w0)) =
        toMat (S.vec (tAut S w0)) := by rw [hp_eq]
    simpa [M, w0, S.vec_jHom, S.vec_tAut, toMat_ofMat, vec_ofVec] using hw
  have h01 := congrFun (congrFun hmat 0) 1
  have h10 : (1 : S.K) = 0 := by
    simpa [uHom_coe, M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using h01
  exact one_ne_zero h10

@[expose] def t0Sub : Subgroup (MulAut W) := u0Sub S ⊔ Subgroup.zpowers (tAut S)

private theorem mul_t_eq (ht : tAut S * tAut S = 1) (x y : MulAut W) :
    (x * y) * tAut S = (x * tAut S) * (tAut S * y * tAut S) := by
  rw [show (x * tAut S) * (tAut S * y * tAut S) =
      x * (tAut S * tAut S) * y * tAut S by simp only [mul_assoc], ht]
  simp

private theorem mul_eq_mul_t (ht : tAut S * tAut S = 1) (x y : MulAut W) :
    x * y = (x * tAut S) * (tAut S * (y * tAut S) * tAut S) := by
  rw [show (x * tAut S) * (tAut S * (y * tAut S) * tAut S) =
      x * (tAut S * tAut S) * y * (tAut S * tAut S) by simp only [mul_assoc], ht]
  simp

private theorem inv_mul_t_eq (ht : tAut S * tAut S = 1) (x : MulAut W) :
    x⁻¹ * tAut S = tAut S * (tAut S * x⁻¹) * tAut S := by
  rw [show tAut S * (tAut S * x⁻¹) * tAut S =
      (tAut S * tAut S) * x⁻¹ * tAut S by simp only [mul_assoc], ht]
  simp

theorem card_t0Sub (hK : Nat.card S.K = 8) : Nat.card (t0Sub S) = 128 := by
  have ht : tAut S * tAut S = 1 := tAut_mul_self S
  have hconj : ∀ u ∈ u0Sub S, tAut S * u * tAut S ∈ u0Sub S := by
    intro u hu
    have := tAut_conj_mem_u0Sub S hu
    rwa [tAut_inv S] at this
  let T : Subgroup (MulAut W) :=
    { carrier := {x | x ∈ u0Sub S ∨ x * tAut S ∈ u0Sub S}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
        · refine Or.inr ?_
          rw [mul_t_eq S ht x y]
          exact mul_mem hx (hconj y hy)
        · refine Or.inl ?_
          rw [mul_eq_mul_t S ht x y]
          exact mul_mem hx (hconj (y * tAut S) hy)
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ?_
          have hx' : tAut S * x⁻¹ ∈ u0Sub S := by
            have := inv_mem hx
            rwa [mul_inv_rev, tAut_inv S] at this
          rw [inv_mul_t_eq S ht x]
          exact hconj (tAut S * x⁻¹) hx' }
  have hHT : t0Sub S ≤ T := by
    change u0Sub S ⊔ Subgroup.zpowers (tAut S) ≤ T
    refine sup_le ?_ ?_
    · intro x hx; exact Or.inl hx
    · rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [ht]; exact one_mem _)
  have hTH : T ≤ t0Sub S := by
    intro x hx
    change x ∈ u0Sub S ∨ x * tAut S ∈ u0Sub S at hx
    rcases hx with hx | hx
    · exact Subgroup.mem_sup_left hx
    · have hxt : x * tAut S ∈ t0Sub S := Subgroup.mem_sup_left hx
      have htH : tAut S ∈ t0Sub S :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers (tAut S))
      have hmem : (x * tAut S) * (tAut S)⁻¹ ∈ t0Sub S := mul_mem hxt (inv_mem htH)
      rwa [mul_inv_cancel_right] at hmem
  have hdesc : ∀ x : MulAut W, x ∈ t0Sub S ↔ x ∈ u0Sub S ∨ x * tAut S ∈ u0Sub S := by
    intro x
    exact ⟨fun hx => hHT hx, fun hx => hTH hx⟩
  set U' : Subgroup (↥(t0Sub S)) := (u0Sub S).subgroupOf (t0Sub S)
  have hU'ind : U'.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨tAut S, Subgroup.mem_sup_right (Subgroup.mem_zpowers (tAut S))⟩, ?_, ?_⟩
    · intro hmem
      rw [Subgroup.mem_subgroupOf] at hmem
      exact tAut_not_mem_u0Sub S hmem
    · intro b
      have hbH : (b : MulAut W) ∈ t0Sub S := b.2
      rcases (hdesc (b : MulAut W)).mp hbH with hb | hb
      · exact Or.inr (by rwa [Subgroup.mem_subgroupOf])
      · refine Or.inl ?_
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
        simpa using hb
  have hcardU' : Nat.card U' = Nat.card (u0Sub S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show u0Sub S ≤ t0Sub S from le_sup_left)).toEquiv
  rw [← Subgroup.card_mul_index (H := U')]
  rw [hU'ind, hcardU', card_u0Sub S hK]

theorem isPGroup_two_t0Sub (hK : Nat.card S.K = 8) : IsPGroup 2 (t0Sub S) := by
  exact IsPGroup.of_card (n := 7) (by rw [card_t0Sub S hK]; norm_num)

theorem t0Sub_le_isoSub : t0Sub S ≤ isoSub S := by
  change u0Sub S ⊔ Subgroup.zpowers (tAut S) ≤ isoSub S
  refine sup_le ?_ ?_
  · exact le_trans (u0Sub_le_omega0 S) (le_trans (omega0_le_omega S) (omega_le_isoSub S))
  · exact Subgroup.zpowers_le.mpr (tAut_mem_isoSub S)

theorem commute_jHom_diag_tAut (d : SL(2, S.K)) : Commute (S.jHom (d, d)) (tAut S) := by
  have h := tAut_mul_jHom S (d, d)
  have hjt : tAut S * S.jHom (d, d) = S.jHom (d, d) * tAut S :=
    (mul_inv_eq_iff_eq_mul).mp h
  rw [commute_iff_eq]
  exact hjt.symm

theorem mem_normalizer_t0Sub_of_commute {x : MulAut W}
    (hx : x ∈ Subgroup.normalizer (u0Sub S : Set (MulAut W))) (hc : Commute x (tAut S)) :
    x ∈ Subgroup.normalizer (t0Sub S : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  have hfix : MulAut.conj x (tAut S) = tAut S := by
    rw [MulAut.conj_apply]
    exact hc.mul_inv_cancel
  change ((u0Sub S ⊔ Subgroup.zpowers (tAut S)).map (MulAut.conj x) =
    u0Sub S ⊔ Subgroup.zpowers (tAut S))
  rw [Subgroup.map_sup, hx, MonoidHom.map_zpowers]
  exact congrArg (fun z => u0Sub S ⊔ Subgroup.zpowers z) hfix

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
