module

public import CFSG.Milestones.ASVolI.A3L3.L3Data
public import CFSG.Milestones.ASVolI.A3L3.Finish

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.ASVolI.ChA
open scoped MatrixGroups

section Diag

variable {F : Type} [Field F]

@[expose] noncomputable def burnsideA315y_diag3 (a b c : Fˣ) : GL (Fin 3) F :=
  ⟨diagonal ![(a : F), b, c], diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F)], by
    rw [diagonal_mul_diagonal]
    convert diagonal_one (n := Fin 3) (α := F) using 2
    funext i
    fin_cases i <;> simp, by
    rw [diagonal_mul_diagonal]
    convert diagonal_one (n := Fin 3) (α := F) using 2
    funext i
    fin_cases i <;> simp⟩

theorem burnsideA315y_diag3_val (a b c : Fˣ) :
    ((burnsideA315y_diag3 a b c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(a : F), b, c] :=
  rfl

theorem burnsideA315y_diag3_comm_blk (u w : Fˣ) (A : Matrix (Fin 2) (Fin 2) F) (d : F) :
    diagonal ![(u : F), u, w] * blkMat A d = blkMat A d * diagonal ![(u : F), u, w] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_three, diagonal] <;> ring

end Diag

section L3

variable {F : Type} [Field F] [Finite F] {x y : F} {hxy : x ^ 2 + y ^ 2 = -1}
  {two_ne : (2 : F) ≠ 0}

theorem burnsideA315y_l3Model_L :
    (burnsideA315y_l3Model x y hxy two_ne).L =
      (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)).range := by
  ext φ
  rw [burnsideA315y_Model.mem_L]
  constructor
  · rintro ⟨g, hg, rfl⟩
    let s : SL(3, F) := ⟨((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hg⟩
    refine ⟨QuotientGroup.mk s, ?_⟩
    rw [burnsideA315h_conj_mk s, burnsideA315y_l3Model_c]
    congr 1
    exact Units.ext rfl
  · rintro ⟨q, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL s, trivial⟩, ?_, ?_⟩
    · show ((Matrix.SpecialLinearGroup.toGL s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact s.2
    · rw [burnsideA315y_l3Model_c, burnsideA315h_conj_mk]

theorem burnsideA315y_l3_ringAut_eq_one {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (σ : RingAut F) : σ = 1 := by
  haveI := Fintype.ofFinite F
  set e := ZMod.ringEquivOfPrime F (Fact.out : p.Prime) (by rw [← Nat.card_eq_fintype_card, hF])
  have h1 : (σ.toRingHom.comp e.toRingHom) = e.toRingHom := Subsingleton.elim _ _
  apply RingEquiv.ext
  intro a
  obtain ⟨b, rfl⟩ := e.surjective a
  have := congrArg (fun f : ZMod p →+* F => f b) h1
  simpa using this

theorem burnsideA315y_l3_odd {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (φ : MulAut PSL(3, F)) (hφ : Odd (orderOf φ)) :
    φ ∈ (burnsideA315y_l3Model x y hxy two_ne).c.range := by
  have hrange : ∀ g : GL (Fin 3) F,
      psl3DiagAut g ∈ (burnsideA315y_l3Model x y hxy two_ne).c.range :=
    fun g => ⟨⟨g, trivial⟩, rfl⟩
  obtain ⟨g, σ, ε, hε, hφeq⟩ := burnsideA315h_classification φ
  rw [burnsideA315y_l3_ringAut_eq_one hF σ, burnsideA315h_field_one, mul_one] at hφeq
  have hsq : φ ^ 2 ∈ (burnsideA315y_l3Model x y hxy two_ne).c.range := by
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · rw [pow_zero, mul_one] at hφeq
      rw [hφeq]
      exact Subgroup.pow_mem _ (hrange g) 2
    · rw [pow_one] at hφeq
      rw [hφeq, sq]
      have h1 : psl3DiagAut g * psl3GraphAut * (psl3DiagAut g * psl3GraphAut) =
          psl3DiagAut g * (psl3GraphAut * psl3DiagAut g * psl3GraphAut) := by
        simp only [mul_assoc]
      rw [h1, burnsideA315h_graph_diag]
      exact Subgroup.mul_mem _ (hrange g) (hrange _)
  obtain ⟨j, hj⟩ := hφ
  have h2 : φ = (φ ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = orderOf φ + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h2]
  exact Subgroup.pow_mem _ hsq _

@[expose] noncomputable def burnsideA315y_l3K (F : Type) [Field F] [Finite F] (x y : F)
    (hxy : x ^ 2 + y ^ 2 = -1) (two_ne : (2 : F) ≠ 0) :
    SL(2, F) →* ↥(burnsideA315y_l3Model x y hxy two_ne).Γ :=
  ((blk : GL (Fin 2) F →* GL (Fin 3) F).comp Matrix.SpecialLinearGroup.toGL).codRestrict _
    (fun _ => trivial)

theorem burnsideA315y_l3K_val (k : SL(2, F)) :
    (((burnsideA315y_l3K F x y hxy two_ne k : ↥(burnsideA315y_l3Model x y hxy two_ne).Γ) :
      GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat (k : Matrix (Fin 2) (Fin 2) F) 1 := by
  show ((blk (Matrix.SpecialLinearGroup.toGL k) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_blk, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, k.2, inv_one]

theorem burnsideA315y_l3K_injective :
    Function.Injective (burnsideA315y_l3K F x y hxy two_ne) := by
  intro a b hab
  have h := congrArg (fun g : ↥(burnsideA315y_l3Model x y hxy two_ne).Γ =>
    ulBlock ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hab
  simp only [burnsideA315y_l3K_val, ulBlock_blkMat] at h
  exact Subtype.ext h

theorem burnsideA315y_l3K_range :
    (burnsideA315y_l3K F x y hxy two_ne).range = (burnsideA315y_l3Model x y hxy two_ne).K₀ := by
  ext g
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [burnsideA315y_l3K_val, det_blkMat, k.2, mul_one]
    · rw [burnsideA315y_l3K_val]
      simp [burnsideA315y_Model.burnsideA315y_IsK, blkMat]
  · rintro ⟨hd, h02, h12, h20, h21, h22⟩
    set G := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hG
    have hA : (ulBlock G).det = 1 := by
      rw [← hd, Matrix.det_fin_three, Matrix.det_fin_two, h02, h12, h20, h21, h22]
      simp [ulBlock]
    let k : SL(2, F) := ⟨ulBlock G, hA⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [burnsideA315y_l3K_val]
    show blkMat (ulBlock G) 1 = G
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkMat, ulBlock, h02, h12, h20, h21, h22]

@[expose] noncomputable def burnsideA315y_l3K₀Equiv :
    ↥(burnsideA315y_l3Model x y hxy two_ne).K₀ ≃* SL(2, F) :=
  ((MonoidHom.ofInjective (burnsideA315y_l3K_injective (x := x) (hxy := hxy)
    (two_ne := two_ne))).trans (MulEquiv.subgroupCongr burnsideA315y_l3K_range)).symm

theorem burnsideA315y_l3_K {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    Nonempty (↥(burnsideA315y_l3Model x y hxy two_ne).K ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  haveI := Fintype.ofFinite F
  set e := ZMod.ringEquivOfPrime F (Fact.out : p.Prime) (by rw [← Nat.card_eq_fintype_card, hF])
  exact ⟨((burnsideA315y_l3Model x y hxy two_ne).K₀EquivK.symm.trans burnsideA315y_l3K₀Equiv).trans
    (CFSG.ClassicalModels.specialLinearFieldEquiv e.symm (Fin 2))⟩

theorem burnsideA315y_l3_Γ₁_eq :
    (burnsideA315y_l3Model x y hxy two_ne).Γ₁ =
      ((Matrix.GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).comp
        (burnsideA315y_l3Model x y hxy two_ne).Γ.subtype).ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
  show ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 ↔ _
  constructor
  · intro h
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one])
  · intro h
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]

theorem burnsideA315y_l3_index_Γ₁ :
    (burnsideA315y_l3Model x y hxy two_ne).Γ₁.index = Nat.card Fˣ := by
  rw [burnsideA315y_l3_Γ₁_eq, Subgroup.index_ker]
  have hr : ((Matrix.GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).comp
      (burnsideA315y_l3Model x y hxy two_ne).Γ.subtype).range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 3) u
    exact ⟨⟨g, trivial⟩, hg⟩
  rw [hr, Subgroup.card_top]

theorem burnsideA315y_l3_Γ₁ {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    ¬ p ∣ (burnsideA315y_l3Model x y hxy two_ne).Γ₁.index := by
  rw [burnsideA315y_l3_index_Γ₁, Nat.card_units, hF]
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

theorem burnsideA315y_l3_e22_range :
    (burnsideA315y_l3Model x y hxy two_ne).e22.range = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have hmem : (⟨burnsideA315y_diag3 1 u⁻¹ u, trivial⟩ : ↥(burnsideA315y_l3Model x y hxy two_ne).Γ) ∈
      (burnsideA315y_l3Model x y hxy two_ne).C₁ := by
    refine ⟨?_, ?_⟩
    · show (diagonal ![((1 : Fˣ) : F), ((u⁻¹ : Fˣ) : F), (u : F)]).det = 1
      simp [Matrix.det_diagonal, Fin.prod_univ_three]
    · apply Subtype.ext
      apply Units.ext
      show diagonal ![((1 : Fˣ) : F), ((u⁻¹ : Fˣ) : F), (u : F)] * diagonal ![-1, -1, 1] =
        diagonal ![-1, -1, 1] * diagonal ![((1 : Fˣ) : F), ((u⁻¹ : Fˣ) : F), (u : F)]
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Units.ext
  rw [burnsideA315y_Model.e22_apply]
  rfl

theorem burnsideA315y_l3_card_D₀C₁ :
    Nat.card ↥((burnsideA315y_l3Model x y hxy two_ne).D₀ ⊓
      (burnsideA315y_l3Model x y hxy two_ne).C₁) = Nat.card Fˣ := by
  set M := burnsideA315y_l3Model x y hxy two_ne with hM
  have h00 : ∀ d : ↥(M.D₀ ⊓ M.C₁),
      (((d : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
    intro d h0
    obtain ⟨h01, h10, h11, h02, h12, h20, h21⟩ := M.D₀_form d.2.1
    have hdet := d.2.2.1
    rw [Matrix.det_fin_three, h01, h10, h11, h02, h12, h20, h21, h0] at hdet
    simp at hdet
  let f : ↥(M.D₀ ⊓ M.C₁) → Fˣ := fun d => Units.mk0 _ (h00 d)
  have hf : Function.Bijective f := by
    constructor
    · intro d d' hdd'
      have he : (((d : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 =
          (((d' : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 :=
        congrArg Units.val hdd'
      obtain ⟨a01, a10, a11, a02, a12, a20, a21⟩ := M.D₀_form d.2.1
      obtain ⟨b01, b10, b11, b02, b12, b20, b21⟩ := M.D₀_form d'.2.1
      have ha := d.2.2.1
      have hb := d'.2.2.1
      rw [Matrix.det_fin_three, a01, a10, a11, a02, a12, a20, a21] at ha
      rw [Matrix.det_fin_three, b01, b10, b11, b02, b12, b20, b21] at hb
      have h22 : (((d : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
          (((d' : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 := by
        have hne := h00 d
        rw [he] at ha
        have : (((d' : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 *
            (((d' : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 *
            ((((d : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 -
              (((d' : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2) = 0 := by
          linear_combination ha - hb
        rcases mul_eq_zero.mp this with h | h
        · exfalso
          rw [he] at hne
          exact hne (mul_self_eq_zero.mp h)
        · exact sub_eq_zero.mp h
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a01, a10, a11, a02, a12, a20, a21, b01, b10, b11,
        b02, b12, b20, b21, he, h22]
    · intro u
      have hmem : (⟨burnsideA315y_diag3 u u (u⁻¹ * u⁻¹), trivial⟩ : ↥M.Γ) ∈ M.D₀ ⊓ M.C₁ := by
        refine ⟨?_, ?_, ?_⟩
        · show _ ∈ Subgroup.centralizer ({M.zh, M.Da, M.Db} : Set ↥M.Γ)
          rw [Subgroup.mem_centralizer_iff]
          have hblk : ∀ (A : Matrix (Fin 2) (Fin 2) F) (d : F) (h : ↥M.Γ),
              ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat A d →
              h * ⟨burnsideA315y_diag3 u u (u⁻¹ * u⁻¹), trivial⟩ =
                ⟨burnsideA315y_diag3 u u (u⁻¹ * u⁻¹), trivial⟩ * h := by
            intro A d h hA
            apply Subtype.ext
            apply Units.ext
            simp only [Subgroup.coe_mul, Units.val_mul, hA, burnsideA315y_diag3_val]
            exact (burnsideA315y_diag3_comm_blk u (u⁻¹ * u⁻¹) A d).symm
          rintro h (rfl | rfl | rfl)
          · refine hblk (-1) 1 M.zh ?_
            rw [M.zh_val, coe_negDiag3, burnsideA315y_blkMat_neg_one]
          · exact hblk _ 1 M.Da M.Da_val
          · exact hblk _ 1 M.Db M.Db_val
        · show (diagonal ![(u : F), (u : F), ((u⁻¹ * u⁻¹ : Fˣ) : F)]).det = 1
          simp only [Matrix.det_diagonal, Fin.prod_univ_three]
          simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          rw [← Units.val_mul, ← Units.val_mul]
          have hu : u * u * (u⁻¹ * u⁻¹) = 1 := by group
          rw [hu, Units.val_one]
        · apply Subtype.ext
          apply Units.ext
          show diagonal ![(u : F), (u : F), ((u⁻¹ * u⁻¹ : Fˣ) : F)] * diagonal ![-1, -1, 1] =
            diagonal ![-1, -1, 1] * diagonal ![(u : F), (u : F), ((u⁻¹ * u⁻¹ : Fˣ) : F)]
          rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
          congr 1
          funext i
          fin_cases i <;> simp [mul_comm]
      exact ⟨⟨_, hmem⟩, Units.ext rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).trans rfl

theorem burnsideA315y_l3_e22 :
    Nat.card ↥(burnsideA315y_l3Model x y hxy two_ne).e22.range =
      Nat.card ↥((burnsideA315y_l3Model x y hxy two_ne).D₀ ⊓
        (burnsideA315y_l3Model x y hxy two_ne).C₁) := by
  rw [burnsideA315y_l3_card_D₀C₁, burnsideA315y_l3_e22_range, Subgroup.card_top]

theorem burnsideA315y_l3_arith {p R : ℕ} (hp : 3 ≤ p)
    (h : R * ((p ^ 2 - 1) * (p ^ 2 - p)) * (p - 1) =
      (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2)) :
    R = p ^ 2 * (p ^ 2 + p + 1) := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  have h3 : 1 ≤ p := by omega
  have h4 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h5 : p ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
  have h6 : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  zify [h1, h2, h3, h4, h5, h6] at h
  have hP : (3 : ℤ) ≤ p := by exact_mod_cast hp
  have hne : ((p : ℤ) * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) ^ 2 - 1)) ≠ 0 := by
    have ha : (0 : ℤ) < p := by linarith
    have hb : (0 : ℤ) < ((p : ℤ) - 1) ^ 2 := by
      have : (0 : ℤ) < (p : ℤ) - 1 := by linarith
      positivity
    have hc : (0 : ℤ) < (p : ℤ) ^ 2 - 1 := by nlinarith
    exact mul_ne_zero (mul_ne_zero ha.ne' hb.ne') hc.ne'
  have h7 : ((R : ℤ) - (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 + p + 1)) *
      ((p : ℤ) * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) ^ 2 - 1)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h7 with h8 | h8
  · have h9 : (R : ℤ) = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 + p + 1) := sub_eq_zero.mp h8
    exact_mod_cast h9
  · exact absurd h8 hne

theorem burnsideA315y_l3_C₁ {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp2 : p ≠ 2) :
    ¬ 2 ∣ (burnsideA315y_l3Model x y hxy two_ne).C₁.relIndex
      (burnsideA315y_l3Model x y hxy two_ne).Γ₁ := by
  set M := burnsideA315y_l3Model x y hxy two_ne with hM
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  haveI := Fintype.ofFinite F
  have hFc : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card, hF]
  set R := M.C₁.relIndex M.Γ₁ with hR
  have e1 : R * Nat.card ↥M.C₁ = Nat.card ↥M.Γ₁ := by
    have := Subgroup.relIndex_mul_card M.C₁ M.Γ₁
    rwa [inf_eq_left.mpr M.C₁_le_Γ₁] at this
  have e2 : Nat.card ↥M.Γ₁ * (p - 1) = (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2) := by
    have := Subgroup.card_mul_index M.Γ₁
    rw [burnsideA315y_l3_index_Γ₁, Nat.card_units, hF] at this
    rw [this]
    show Nat.card ↥(⊤ : Subgroup (GL (Fin 3) F)) = _
    rw [Subgroup.card_top, Matrix.card_GL_field, hFc, Fin.prod_univ_three]
    simp
  have e3 : Nat.card ↥M.C₁ = Nat.card ↥M.K₀ * (p - 1) := by
    rw [M.card_C₁, burnsideA315y_l3_e22_range, Subgroup.card_top, Nat.card_units, hF]
  have e4 : Nat.card ↥M.K₀ * (p - 1) = (p ^ 2 - 1) * (p ^ 2 - p) := by
    have h1 := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
    rw [Matrix.card_GL_field, Nat.card_units, hF, hFc, Fin.prod_univ_two] at h1
    rw [Nat.card_congr burnsideA315y_l3K₀Equiv.toEquiv, h1]
    simp
  have e5 : R * ((p ^ 2 - 1) * (p ^ 2 - p)) * (p - 1) =
      (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2) := by
    rw [← e4, ← e2, ← e1, e3]
  have hRv := burnsideA315y_l3_arith hp3 e5
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hodd : Odd R := by
    rw [hRv]
    refine Nat.odd_mul.mpr ⟨hpodd.pow, ?_⟩
    obtain ⟨k, rfl⟩ := hpodd
    exact ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩
  exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)

@[expose] noncomputable def burnsideA315y_dglHom (F : Type) [Field F] : Fˣ →* GL (Fin 3) F where
  toFun := burnsideA315y_dgl
  map_one' := Units.ext (by
    rw [burnsideA315y_dgl_val, Units.val_one, Units.val_one, one_smul, blkMat_one])
  map_mul' s t := Units.ext (by
    rw [Units.val_mul, burnsideA315y_dgl_val, burnsideA315y_dgl_val, burnsideA315y_dgl_val,
      blkMat_mul, smul_mul_smul_comm, Matrix.one_mul, mul_one, Units.val_mul])

theorem burnsideA315y_l3_D₀ {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    IsCyclic ↥((burnsideA315y_l3Model x y hxy two_ne).D₀.map
      (burnsideA315y_l3Model x y hxy two_ne).c) ∧
    Nat.card ↥((burnsideA315y_l3Model x y hxy two_ne).D₀.map
      (burnsideA315y_l3Model x y hxy two_ne).c) ∣ p - 1 := by
  set M := burnsideA315y_l3Model x y hxy two_ne with hM
  let ψ : Fˣ →* ↥M.Γ := (burnsideA315y_dglHom F).codRestrict M.Γ (fun _ => trivial)
  have hψ : ∀ s, ψ s ∈ M.D₀ := by
    intro s
    show ψ s ∈ Subgroup.centralizer ({M.zh, M.Da, M.Db} : Set ↥M.Γ)
    rw [Subgroup.mem_centralizer_iff]
    have hblk : ∀ (A : Matrix (Fin 2) (Fin 2) F) (h : ↥M.Γ),
        ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat A 1 → h * ψ s = ψ s * h := by
      intro A h hA
      apply Subtype.ext
      apply Units.ext
      show ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * blkMat ((s : F) • 1) 1 =
        blkMat ((s : F) • 1) 1 * ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      rw [hA, blkMat_mul, blkMat_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, mul_one]
    rintro h (rfl | rfl | rfl)
    · refine hblk (-1) M.zh ?_
      rw [M.zh_val, coe_negDiag3, burnsideA315y_blkMat_neg_one]
    · exact hblk _ M.Da M.Da_val
    · exact hblk _ M.Db M.Db_val
  have hsurj : ∀ d ∈ M.D₀, ∃ s, M.c (ψ s) = M.c d := by
    intro d hd
    obtain ⟨h01, h10, h11, h02, h12, h20, h21⟩ := M.D₀_form hd
    set D := ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hD
    have hdet : D.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det D).mp (d : GL (Fin 3) F).isUnit).ne_zero
    rw [Matrix.det_fin_three, h01, h10, h11, h02, h12, h20, h21] at hdet
    have ha : D 0 0 ≠ 0 := by
      intro h0
      apply hdet
      rw [h0]
      ring
    have hw : D 2 2 ≠ 0 := by
      intro h0
      apply hdet
      rw [h0]
      ring
    set a : Fˣ := Units.mk0 (D 0 0) ha
    set w : Fˣ := Units.mk0 (D 2 2) hw
    refine ⟨a / w, ?_⟩
    have hd' : (d : GL (Fin 3) F) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) w * burnsideA315y_dgl (a / w) := by
      apply Units.ext
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, burnsideA315y_dgl_val]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [blkMat, Matrix.mul_apply, Fin.sum_univ_three, a, w, ← hD, h01, h10, h11, h02, h12,
          h20, h21, hw, mul_div_cancel₀]
    have hsc : M.c ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) w, trivial⟩ = 1 :=
      (M.ker_c _).mpr ⟨w, rfl⟩
    have h1 : d = ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) w, trivial⟩ * ψ (a / w) :=
      Subtype.ext hd'
    rw [h1, map_mul, hsc, one_mul]
  obtain ⟨hcyc, hdvd⟩ := M.D₀_cyclic ψ hψ hsurj
  refine ⟨hcyc, ?_⟩
  rwa [Nat.card_units, hF] at hdvd

end L3

end CFSG.ASVolI
