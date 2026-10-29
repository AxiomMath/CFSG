module

public import CFSG.RankThree.PartTwo.Sec17.F174L3AutFlag
public import CFSG.RankThree.PartTwo.Sec17.F174L3AutTv
public import CFSG.RankThree.PartTwo.Sec17.F174L3AutAux
public import CFSG.RankThree.PartTwo.Sec17.F174L3AutCls
public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutNatFour

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Core

open CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatI

variable {F : Type} [Field F] [CharP F 2]

@[expose] def tvSL (φ v : Fin 3 → F) (h : φ ⬝ᵥ v = 0) : SL(3, F) := ⟨tvM φ v, det_tvM h⟩

@[simp] theorem coe_tvSL (φ v : Fin 3 → F) (h : φ ⬝ᵥ v = 0) :
    ((tvSL φ v h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = tvM φ v := rfl

theorem tvSL_mul_self {φ v : Fin 3 → F} (h : φ ⬝ᵥ v = 0) : tvSL φ v h * tvSL φ v h = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, Tv.tvM_mul_self h,
      Matrix.SpecialLinearGroup.coe_one])

theorem exists_tvSL_of_invol {z : SL(3, F)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ (φ v : Fin 3 → F) (h : φ ⬝ᵥ v = 0), v ≠ 0 ∧ φ ≠ 0 ∧ z = tvSL φ v h := by
  have hzz : (z : Matrix (Fin 3) (Fin 3) F) * (z : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) hz
    simpa using this
  have hz1' : (z : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h =>
    hz1 (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one]))
  obtain ⟨v, φ, hv, hφ, h, hmul⟩ := exists_transvection_of_sq_eq_one hzz hz1'
  have hmat : (z : Matrix (Fin 3) (Fin 3) F) = tvM φ v :=
    CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatE.matrix_eq_of_mulVec_aux
      (fun u => by rw [hmul u, tvM_mulVec])
  exact ⟨φ, v, h, hv, hφ, Subtype.ext hmat⟩

theorem coe_conj_tvSL (t : SL(3, F)) (φ v : Fin 3 → F) (h : φ ⬝ᵥ v = 0) :
    ((t * tvSL φ v h * t⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      tvM (φ ᵥ* ((t⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))
        ((t : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
  have h1 := Tv.conj_tvM (Matrix.SpecialLinearGroup.toGL t) φ v
  have e1 : ((Matrix.SpecialLinearGroup.toGL t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (t : Matrix (Fin 3) (Fin 3) F) := rfl
  have e2 : (((Matrix.SpecialLinearGroup.toGL t)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((t⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← map_inv]
    rfl
  rw [e1, e2] at h1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL]
  exact h1

section Eig

variable {g gi : Matrix (Fin 3) (Fin 3) F}

theorem eig_or (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (hg : g * gi = 1) (hgi : gi * g = 1)
    (hg3 : g * g * g = 1) {φ v : Fin 3 → F} (hv : v ≠ 0) (hφ : φ ≠ 0) (h : φ ⬝ᵥ v = 0)
    (hc : tvM φ v * tvM (φ ᵥ* gi) (g *ᵥ v) = tvM (φ ᵥ* gi) (g *ᵥ v) * tvM φ v) :
    g *ᵥ v = v ∨ φ ᵥ* g = φ := by
  have hcube : ∀ r : F, r ^ 3 = 1 → r = 1 := fun r hr => Flag.eq_one_of_pow_three hω hr
  have hv1 : g *ᵥ v ≠ 0 := Vec.mulVec_ne_zero_of hgi hv
  have hφ1 : φ ᵥ* gi ≠ 0 := Vec.vecMul_ne_zero_of hg hφ
  have h1 : (φ ᵥ* gi) ⬝ᵥ (g *ᵥ v) = 0 := by
    rw [Vec.dot_vecMul_mulVec_cancel hgi]
    exact h
  obtain ⟨o1, o2⟩ := Tv.orth_of_commute_tvM hφ hv hφ1 hv1 h h1 hc
  by_cases hpar : ∃ c : F, g *ᵥ v = c • v
  · obtain ⟨c, hc'⟩ := hpar
    exact Or.inl (Vec.eig_vec_one hg3 hcube hv c hc')
  · right
    push Not at hpar
    obtain ⟨c, hcc⟩ := Tv.parallel_of_orth_three hv hpar hφ hφ1 h o1 o2 h1
    exact Vec.eig_covec_one hg hgi hg3 hcube hφ c hcc

theorem no_commuting_tv (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (hg : g * gi = 1) (hgi : gi * g = 1)
    (hg3 : g * g * g = 1) (hg1 : g ≠ 1) {φ v : Fin 3 → F} (hv : v ≠ 0) (hφ : φ ≠ 0)
    (h : φ ⬝ᵥ v = 0) (hc : g * tvM φ v = tvM φ v * g) : False := by
  have hcube : ∀ r : F, r ^ 3 = 1 → r = 1 := fun r hr => Flag.eq_one_of_pow_three hω hr
  have h1 : g * tvM φ v * gi = tvM (φ ᵥ* gi) (g *ᵥ v) :=
    Tv.conj_tvM (⟨g, gi, hg, hgi⟩ : GL (Fin 3) F) φ v
  have hconj : tvM (φ ᵥ* gi) (g *ᵥ v) = tvM φ v := by
    rw [← h1, hc, mul_assoc, hg, mul_one]
  have hv1 : g *ᵥ v ≠ 0 := Vec.mulVec_ne_zero_of hgi hv
  have hφ1 : φ ᵥ* gi ≠ 0 := Vec.vecMul_ne_zero_of hg hφ
  obtain ⟨c, hc0, hcv, hcφ⟩ := Tv.tvM_inj hφ1 hv1 hφ hv hconj
  have hgv : g *ᵥ v = c⁻¹ • v := by
    have : g *ᵥ v = c⁻¹ • (c • (g *ᵥ v)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this, ← hcv]
  have hgv1 : g *ᵥ v = v := Vec.eig_vec_one hg3 hcube hv c⁻¹ hgv
  have hgφ : φ ᵥ* g = φ := Vec.eig_covec_one hg hgi hg3 hcube hφ c hcφ
  exact Flag.no_fixed_flag hω hg3 hg1 hv hφ h hgv1 hgφ

theorem cross_false (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hg3 : g * g * g = 1) (hg1 : g ≠ 1) {φ v φ' v' : Fin 3 → F} (hv : v ≠ 0) (hφ : φ ≠ 0)
    (hv' : v' ≠ 0) (hφ' : φ' ≠ 0) (h : φ ⬝ᵥ v = 0) (h' : φ' ⬝ᵥ v' = 0)
    (hc : tvM φ v * tvM φ' v' = tvM φ' v' * tvM φ v) (hgv : g *ᵥ v = v)
    (hgφ : φ' ᵥ* g = φ') : False := by
  obtain ⟨-, o2⟩ := Tv.orth_of_commute_tvM hφ hv hφ' hv' h h' hc
  exact Flag.no_fixed_flag hω hg3 hg1 hv hφ' o2 hgv hgφ

end Eig

section Main

theorem matrix_facts (t : SL(3, F)) (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    (t : Matrix (Fin 3) (Fin 3) F) * ((t⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      ((t⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      (t : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F) *
        (t : Matrix (Fin 3) (Fin 3) F) = 1 ∧ (t : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  · have h := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) ht3
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
    rw [← h]
    noncomm_ring
  · intro h
    exact ht1 (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one]))

theorem no_type_one (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (t : SL(3, F)) (ht3 : t ^ 3 = 1)
    (ht1 : t ≠ 1) (σ : MulAut SL(3, F)) (B : GL (Fin 3) F)
    (hσB : ∀ s : SL(3, F), ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hσt : σ t = t) (S : Set SL(3, F)) (hne : S.Nonempty)
    (hS1 : ∀ z ∈ S, z * z = 1 ∧ z ≠ 1) (hS2 : ∀ z ∈ S, ∀ z' ∈ S, z * z' = z' * z)
    (hS3 : ∀ z ∈ S, t * z * t⁻¹ ∈ S) (hS4 : ∀ z ∈ S, σ z ∈ S) : False := by
  classical
  obtain ⟨hgg, hgig, hg3, hg1⟩ := matrix_facts t ht3 ht1
  set g : Matrix (Fin 3) (Fin 3) F := (t : Matrix (Fin 3) (Fin 3) F) with hg
  set gi : Matrix (Fin 3) (Fin 3) F := ((t⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hgi
  set Bm : Matrix (Fin 3) (Fin 3) F := (B : Matrix (Fin 3) (Fin 3) F) with hBm
  set Bi : Matrix (Fin 3) (Fin 3) F := ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hBi
  have hBB : Bm * Bi = 1 := Units.mul_inv B
  have hBBi : Bi * Bm = 1 := Units.inv_mul B
  have hgB : g * Bm = Bm * gi.transpose := by
    have h1 := hσB t
    rw [hσt] at h1
    calc g * Bm = Bm * gi.transpose * Bi * Bm := by rw [← h1]
      _ = Bm * gi.transpose := by rw [mul_assoc, hBBi, mul_one]
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨hz₀2, hz₀1⟩ := hS1 z₀ hz₀
  obtain ⟨φ₀, v₀, h₀, hv₀, hφ₀, rfl⟩ := exists_tvSL_of_invol hz₀2 hz₀1
  have hz₁ := hS4 _ hz₀
  have hinv : (tvSL φ₀ v₀ h₀)⁻¹ = tvSL φ₀ v₀ h₀ := inv_eq_of_mul_eq_one_right (tvSL_mul_self h₀)
  have hσz₀ : ((σ (tvSL φ₀ v₀ h₀) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      tvM (v₀ ᵥ* Bi) (Bm *ᵥ φ₀) := by
    rw [hσB, hinv, coe_tvSL, Tv.transpose_tvM]
    exact Tv.conj_tvM B v₀ φ₀
  have h₁ : (v₀ ᵥ* Bi) ⬝ᵥ (Bm *ᵥ φ₀) = 0 := by
    rw [Vec.dot_vecMul_mulVec_cancel hBBi, dotProduct_comm]
    exact h₀
  have hv₁ : Bm *ᵥ φ₀ ≠ 0 := Vec.mulVec_ne_zero_of hBBi hφ₀
  have hφ₁ : v₀ ᵥ* Bi ≠ 0 := Vec.vecMul_ne_zero_of hBB hv₀
  have hz₁eq : σ (tvSL φ₀ v₀ h₀) = tvSL (v₀ ᵥ* Bi) (Bm *ᵥ φ₀) h₁ := Subtype.ext hσz₀
  have hcomm₀ : tvM φ₀ v₀ * tvM (φ₀ ᵥ* gi) (g *ᵥ v₀) =
      tvM (φ₀ ᵥ* gi) (g *ᵥ v₀) * tvM φ₀ v₀ := by
    have h2 := hS2 _ hz₀ _ (hS3 _ hz₀)
    have hL : ((tvSL φ₀ v₀ h₀ * (t * tvSL φ₀ v₀ h₀ * t⁻¹) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) = tvM φ₀ v₀ * tvM (φ₀ ᵥ* gi) (g *ᵥ v₀) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, coe_conj_tvSL]
    have hR : (((t * tvSL φ₀ v₀ h₀ * t⁻¹) * tvSL φ₀ v₀ h₀ : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) = tvM (φ₀ ᵥ* gi) (g *ᵥ v₀) * tvM φ₀ v₀ := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_conj_tvSL, coe_tvSL]
    rw [← hL, ← hR]
    exact congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h2
  have heig := eig_or hω hgg hgig hg3 hv₀ hφ₀ h₀ hcomm₀
  have hcorr := Vec.eig_corr hgg hgig hBB hBBi hgB φ₀ v₀
  have hcomm₁ : tvM φ₀ v₀ * tvM (v₀ ᵥ* Bi) (Bm *ᵥ φ₀) =
      tvM (v₀ ᵥ* Bi) (Bm *ᵥ φ₀) * tvM φ₀ v₀ := by
    have h2 := hS2 _ hz₀ _ hz₁
    rw [hz₁eq] at h2
    have h3 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h2
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL] at h3
    exact h3
  rcases heig with hgv | hgφ
  · have hgφ₁ : (v₀ ᵥ* Bi) ᵥ* g = v₀ ᵥ* Bi := hcorr.2.mpr hgv
    exact cross_false hω hg3 hg1 hv₀ hφ₀ hv₁ hφ₁ h₀ h₁ hcomm₁ hgv hgφ₁
  · have hgv₁ : g *ᵥ (Bm *ᵥ φ₀) = Bm *ᵥ φ₀ := hcorr.1.mpr hgφ
    exact cross_false hω hg3 hg1 hv₁ hφ₁ hv₀ hφ₀ h₁ h₀ hcomm₁.symm hgv₁ hgφ

theorem type_zero_trivial [Finite F] (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (t : SL(3, F))
    (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) (σ : MulAut SL(3, F)) (k : ℕ) (hk : σ ^ (2 ^ k) = 1)
    (B : GL (Fin 3) F)
    (hσB : ∀ s : SL(3, F), ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hσt : σ t = t) : σ = 1 := by
  classical
  have hcube : ∀ r : F, r ^ 3 = 1 → r = 1 := fun r hr => Flag.eq_one_of_pow_three hω hr
  obtain ⟨hgg, hgig, hg3, hg1⟩ := matrix_facts t ht3 ht1
  obtain ⟨b, hb⟩ := Grp.exists_sl_conj hcube B
  have hσb : ∀ s : SL(3, F), σ s = b * s * b⁻¹ := fun s =>
    Subtype.ext (by
      rw [hσB, hb, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul])
  have hconj : σ = MulAut.conj b := MulEquiv.ext fun s => by rw [hσb, MulAut.conj_apply]
  have hbk : b ^ (2 ^ k) = 1 := by
    have hc : MulAut.conj (b ^ (2 ^ k)) = 1 := by rw [map_pow, ← hconj]; exact hk
    have hcen : b ^ (2 ^ k) ∈ Subgroup.center SL(3, F) := by
      rw [Subgroup.mem_center_iff]
      intro s
      have h1 := MulEquiv.congr_fun hc s
      rw [MulAut.conj_apply] at h1
      have h2 : b ^ (2 ^ k) * s = s * b ^ (2 ^ k) := by
        have := congrArg (fun x => x * b ^ (2 ^ k)) h1
        simpa [mul_assoc] using this
      exact h2.symm
    rw [CFSG.RankThree.PartTwo.Sec4.center_specialLinearGroup_eq_bot hcube] at hcen
    exact Subgroup.mem_bot.1 hcen
  have hbt : b * t = t * b := by
    have h1 := hσb t
    rw [hσt] at h1
    calc b * t = (b * t * b⁻¹) * b := by group
      _ = t * b := by rw [← h1]
  by_contra hne
  have hb1 : b ≠ 1 := fun h => hne (by rw [hconj, h, map_one])
  obtain ⟨j, hj1, hj2⟩ := Grp.exists_involution_pow hb1 hbk
  obtain ⟨φ, v, h, hv, hφ, hy⟩ := exists_tvSL_of_invol hj1 hj2
  have hcomm : t * b ^ (2 ^ j) = b ^ (2 ^ j) * t :=
    ((Commute.pow_right (show Commute t b from hbt.symm) _).eq)
  rw [hy] at hcomm
  have h3 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) hcomm
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL] at h3
  exact no_commuting_tv hω hgg hgig hg3 hg1 hv hφ h h3

theorem l3Aut_core [Fintype F] {n : ℕ} (hn : Odd n) (hF : Fintype.card F = 2 ^ n)
    (σ : MulAut SL(3, F)) (hσk : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (t : SL(3, F)) (ht : orderOf t = 3) (hσt : σ t = t)
    (D : Subgroup SL(3, F)) (hD0 : D ≠ ⊥) (hD2 : IsPGroup 2 D) (hσD : ∀ d ∈ D, σ d ∈ D)
    (hDt : ∀ d ∈ D, t * d * t⁻¹ ∈ D) : σ = 1 := by
  classical
  have hω := Flag.hω_of_card hn hF
  have hcube : ∀ r : F, r ^ 3 = 1 → r = 1 := fun r hr => Flag.eq_one_of_pow_three hω hr
  have ht3 : t ^ 3 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht] at h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  rcases Tr.classification_sl hn hF hcube σ hσk with ⟨B, hB⟩ | ⟨B, hB⟩
  · obtain ⟨k, hk⟩ := hσk
    exact type_zero_trivial hω t ht3 ht1 σ k hk B hB hσt
  · exfalso
    have htinv : t⁻¹ = t * t := by
      refine inv_eq_of_mul_eq_one_right ?_
      calc t * (t * t) = t ^ 3 := (pow_three t).symm
        _ = 1 := ht3
    have e1 : t * t = t⁻¹ := htinv.symm
    have e2 : t⁻¹ * t⁻¹ = t := by rw [← mul_inv_rev, e1, inv_inv]
    have hDt' : ∀ d ∈ D, t⁻¹ * d * t ∈ D := by
      intro d hd
      have h2 := hDt _ (hDt d hd)
      have : t⁻¹ * d * t = t * (t * d * t⁻¹) * t⁻¹ := by
        calc t⁻¹ * d * t = (t * t) * d * (t⁻¹ * t⁻¹) := by rw [e1, e2]
          _ = t * (t * d * t⁻¹) * t⁻¹ := by group
      rw [this]
      exact h2
    obtain ⟨z, hzD, hz2, hz1, hzc⟩ := Grp.exists_central_involution D hD0 hD2
    refine no_type_one hω t ht3 ht1 σ B hB hσt
      {z | z ∈ D ∧ z * z = 1 ∧ z ≠ 1 ∧ ∀ d ∈ D, z * d = d * z} ⟨z, hzD, hz2, hz1, hzc⟩ ?_ ?_ ?_ ?_
    · rintro z' ⟨-, h2, h1, -⟩
      exact ⟨h2, h1⟩
    · rintro z' ⟨-, -, -, hc1⟩ z'' ⟨hD2', -, -, -⟩
      exact hc1 z'' hD2'
    · rintro z' ⟨hD1, h2, h1, hc⟩
      refine ⟨hDt z' hD1, ?_, ?_, ?_⟩
      · calc t * z' * t⁻¹ * (t * z' * t⁻¹) = t * (z' * z') * t⁻¹ := by group
          _ = 1 := by rw [h2]; group
      · intro h
        apply h1
        have h5 : z' = t⁻¹ * (t * z' * t⁻¹) * t := by group
        rw [h5, h]
        group
      · intro d hd
        have hc' := hc _ (hDt' d hd)
        calc t * z' * t⁻¹ * d = t * (z' * (t⁻¹ * d * t)) * t⁻¹ := by group
          _ = t * ((t⁻¹ * d * t) * z') * t⁻¹ := by rw [hc']
          _ = d * (t * z' * t⁻¹) := by group
    · rintro z' ⟨hD1, h2, h1, hc⟩
      refine ⟨hσD z' hD1, ?_, ?_, ?_⟩
      · rw [← map_mul, h2, map_one]
      · intro h
        exact h1 (σ.injective (by rw [h, map_one]))
      · intro d hd
        obtain ⟨d', hd', rfl⟩ := Grp.map_surj_of_injective D σ hσD d hd
        rw [← map_mul, ← map_mul, hc d' hd']

end Main

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Core
