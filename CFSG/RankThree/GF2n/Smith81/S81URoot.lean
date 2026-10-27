module

public import CFSG.RankThree.GF2n.Smith81.S81UFrame
public import CFSG.RankThree.GF2n.Smith81.S81NBasis

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

@[expose] def partner (i : Fin 6) : Fin 6 :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by have := i.isLt; split_ifs <;> omega⟩

theorem partner_partner (i : Fin 6) : partner (partner i) = i := by
  fin_cases i <;> rfl

theorem partner_ne (i : Fin 6) : partner i ≠ i := by
  fin_cases i <;> decide

theorem partner_ne_partner {a b : Fin 6} (h : a ≠ b) : partner b ≠ partner a := by
  intro hc
  apply h
  have h2 := congrArg partner hc
  rw [partner_partner, partner_partner] at h2
  exact h2.symm

theorem hypGram_apply (i j : Fin 6) : hypGram F i j = if j = partner i then 1 else 0 := by
  have key : (i.val / 2 = j.val / 2 ∧ i.val % 2 ≠ j.val % 2) ↔ j = partner i := by
    fin_cases i <;> fin_cases j <;> decide
  simp only [hypGram, Matrix.of_apply]
  by_cases h : j = partner i
  · rw [if_pos h, if_pos (key.mpr h)]
  · rw [if_neg h, if_neg (fun hk => h (key.mp hk))]

private theorem h49_eq_partner_iff (x i : Fin 6) : x = partner i ↔ partner x = i :=
  ⟨fun h => by rw [h, partner_partner], fun h => by rw [← h, partner_partner]⟩

private theorem h49_hypGram_apply (i x : Fin 6) :
    hypGram F i x = if partner x = i then 1 else 0 := by
  rw [hypGram_apply]
  by_cases h : x = partner i
  · rw [if_pos h, if_pos ((h49_eq_partner_iff x i).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((h49_eq_partner_iff x i).mpr h'))]

private theorem h49_hypGram_mul_single (x y : Fin 6) (d : F) :
    hypGram F * Matrix.single x y d = Matrix.single (partner x) y d := by
  ext i k
  by_cases hk : k = y
  · rw [hk, Matrix.mul_single_apply_same, h49_hypGram_apply, Matrix.single_apply]
    by_cases hi : partner x = i <;> simp [hi]
  · simp [hk, Ne.symm hk, Matrix.single_apply]

private theorem h49_single_mul_hypGram (x y : Fin 6) (d : F) :
    Matrix.single x y d * hypGram F = Matrix.single x (partner y) d := by
  ext i k
  by_cases hi : i = x
  · rw [hi, Matrix.single_mul_apply_same, hypGram_apply, Matrix.single_apply]
    by_cases hk : k = partner y
    · simp [hk]
    · simp [hk, Ne.symm hk]
  · simp [hi, Ne.symm hi, Matrix.single_apply]

private theorem h49_single_add_self (i j : Fin 6) (d : F) :
    Matrix.single i j d + Matrix.single i j d = 0 := by
  rw [← Matrix.single_add, CharTwo.add_self_eq_zero, Matrix.single_zero]

private theorem h49_char_two_cancel (x y : Matrix (Fin 6) (Fin 6) F)
    (hx : x + x = 0) (hy : y + y = 0) : x + y + (y + x) = 0 := by
  calc x + y + (y + x) = (x + x) + (y + y) := by abel
    _ = 0 := by rw [hx, hy, add_zero]

private theorem h49_short_core (P X G : Matrix (Fin 6) (Fin 6) F)
    (h : P * G + G * X + P * G * X = 0) : (1 + P) * G * (1 + X) = G := by
  have e : (1 + P) * G * (1 + X) = G + (P * G + G * X + P * G * X) := by noncomm_ring
  rw [e, h, add_zero]

theorem transvection_long_unitary (hσ : ∀ c, σ (σ c) = c) (a : Fin 6) {c : F} (hc : σ c = c) :
    conjTr σ (Matrix.transvection a (partner a) c) * hypGram F *
      Matrix.transvection a (partner a) c = hypGram F := by
  have hT : conjTr σ (Matrix.transvection a (partner a) c) = 1 + Matrix.single (partner a) a c := by
    rw [Matrix.transvection, conjTr_add, conjTr_one, conjTr_single, hc]
  have h1 : Matrix.single (partner a) a c * hypGram F = Matrix.single (partner a) (partner a) c :=
    h49_single_mul_hypGram (partner a) a c
  have h2 : hypGram F * Matrix.single a (partner a) c = Matrix.single (partner a) (partner a) c :=
    h49_hypGram_mul_single a (partner a) c
  have h3 : Matrix.single (partner a) (partner a) c * Matrix.single a (partner a) c = 0 := by
    simp [partner_ne a]
  rw [hT, Matrix.transvection]
  apply h49_short_core
  rw [h1, h2, h3, add_zero, h49_single_add_self]

theorem transvection_short_unitary (hσ : ∀ c, σ (σ c) = c) {a b : Fin 6} (hab : a ≠ b)
    (hb : b ≠ partner a) (c : F) :
    conjTr σ (Matrix.transvection a b c * Matrix.transvection (partner b) (partner a) (σ c)) *
        hypGram F * (Matrix.transvection a b c * Matrix.transvection (partner b) (partner a) (σ c)) =
      hypGram F := by
  have h0 : Matrix.single a b c * Matrix.single (partner b) (partner a) (σ c) = 0 := by
    simp [(partner_ne b).symm]
  have hprod : Matrix.transvection a b c * Matrix.transvection (partner b) (partner a) (σ c) =
      1 + (Matrix.single a b c + Matrix.single (partner b) (partner a) (σ c)) := by
    simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one, h0, add_zero]
    abel
  have hconj : conjTr σ (1 + (Matrix.single a b c + Matrix.single (partner b) (partner a) (σ c))) =
      1 + (Matrix.single b a (σ c) + Matrix.single (partner a) (partner b) c) := by
    rw [conjTr_add, conjTr_one, conjTr_add, conjTr_single, conjTr_single, hσ]
  have hPH : (Matrix.single b a (σ c) + Matrix.single (partner a) (partner b) c) * hypGram F =
      Matrix.single b (partner a) (σ c) + Matrix.single (partner a) b c := by
    rw [add_mul, h49_single_mul_hypGram, h49_single_mul_hypGram, partner_partner]
  have hHX : hypGram F * (Matrix.single a b c + Matrix.single (partner b) (partner a) (σ c)) =
      Matrix.single (partner a) b c + Matrix.single b (partner a) (σ c) := by
    rw [mul_add, h49_hypGram_mul_single, h49_hypGram_mul_single, partner_partner]
  have hPHX : (Matrix.single b (partner a) (σ c) + Matrix.single (partner a) b c) *
      (Matrix.single a b c + Matrix.single (partner b) (partner a) (σ c)) = 0 := by
    have p1 : Matrix.single b (partner a) (σ c) * Matrix.single a b c = 0 := by
      simp [partner_ne a]
    have p2 : Matrix.single b (partner a) (σ c) *
        Matrix.single (partner b) (partner a) (σ c) = 0 := by
      simp [(partner_ne_partner hab).symm]
    have p3 : Matrix.single (partner a) b c * Matrix.single a b c = 0 := by
      simp [hab.symm]
    have p4 : Matrix.single (partner a) b c * Matrix.single (partner b) (partner a) (σ c) = 0 := by
      simp [(partner_ne b).symm]
    simp only [add_mul, mul_add, p1, p2, p3, p4, add_zero]
  rw [hprod, hconj]
  apply h49_short_core
  rw [hPH, hHX, hPHX, add_zero]
  exact h49_char_two_cancel _ _ (h49_single_add_self _ _ _) (h49_single_add_self _ _ _)

theorem frameConj_long_mem (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (a : Fin 6)
    {c : F} (hc : σ c = c) :
    frameGL σ ω hω * transvGL F a (partner a) (partner_ne a).symm c * (frameGL σ ω hω)⁻¹ ∈
      SUid σ 6 := by
  have hdet : ((transvGL F a (partner a) (partner_ne a).symm c : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F).det = 1 := by
    rw [transvGL_val, Matrix.det_transvection_of_ne a (partner a) (partner_ne a).symm c]
  have hu : conjTr σ ((transvGL F a (partner a) (partner_ne a).symm c : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) * hypGram F *
      ((transvGL F a (partner a) (partner_ne a).symm c : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) = hypGram F := by
    rw [transvGL_val]
    exact transvection_long_unitary hσ.invol a hc
  exact frame_conj_mem_SUid hσ.invol hω hdet hu

theorem frameConj_short_mem (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) {a b : Fin 6}
    (hab : a ≠ b) (hb : b ≠ partner a) (c : F) :
    frameGL σ ω hω * (transvGL F a b hab c *
        transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) *
      (frameGL σ ω hω)⁻¹ ∈ SUid σ 6 := by
  have hdet : ((transvGL F a b hab c *
      transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, transvGL_val, transvGL_val,
      Matrix.det_transvection_of_ne a b hab c,
      Matrix.det_transvection_of_ne (partner b) (partner a) (partner_ne_partner hab) (σ c), one_mul]
  have hu : conjTr σ ((transvGL F a b hab c *
      transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) * hypGram F *
      ((transvGL F a b hab c *
      transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) = hypGram F := by
    simp only [Units.val_mul, transvGL_val]
    exact transvection_short_unitary hσ.invol hab hb c
  exact frame_conj_mem_SUid hσ.invol hω hdet hu

private theorem h50_transvection_mulVec (i j : Fin 6) (c : F) (v : Fin 6 → F) (hv : v j = 0) :
    (Matrix.transvection i j c).mulVec v = v := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, hv,
    mul_zero, zero_smul, add_zero]

private theorem h50_short_fix_even (c : F) {a b : Fin 6} (ha : a.val % 2 = 0)
    (hb : b.val % 2 = 1) (hab : a ≠ b) (hpab : partner b ≠ partner a) (k : Fin 6)
    (hk : k.val % 2 = 0) :
    ((transvGL F a b hab c * transvGL F (partner b) (partner a) hpab (σ c) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F).mulVec (Pi.single k (1 : F)) = Pi.single k (1 : F) := by
  have hpa : (partner a).val = a.val + 1 := by simp [partner, ha]
  have hbk : b ≠ k := by
    intro h
    have h' := congrArg Fin.val h
    omega
  have hpk : partner a ≠ k := by
    intro h
    have h' := congrArg Fin.val h
    omega
  have hv1 : (Pi.single k (1 : F) : Fin 6 → F) b = 0 := by rw [Pi.single_apply, if_neg hbk]
  have hv2 : (Pi.single k (1 : F) : Fin 6 → F) (partner a) = 0 := by
    rw [Pi.single_apply, if_neg hpk]
  simp only [Units.val_mul, transvGL_val]
  rw [← Matrix.mulVec_mulVec, h50_transvection_mulVec _ _ _ _ hv2,
    h50_transvection_mulVec _ _ _ _ hv1]

private theorem h50_frameConj_fixes_T0 {x : GL (Fin 6) F} {ω : F} (hω : ω + σ ω = 1)
    (hx : ∀ k : Fin 6, k.val % 2 = 0 →
      ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (Pi.single k (1 : F)) =
        Pi.single k (1 : F))
    (i : Fin 3) :
    ((frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec
      (e3uT0Vec i) = e3uT0Vec i := by
  have hval : ((frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹ : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) =
      frameMat σ ω * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * frameInv σ ω := by
    rw [Units.val_mul, Units.val_mul]
    rfl
  have hSi : frameInv σ ω * frameMat σ ω = 1 := frameInv_mul_frameMat hω
  have hk : (⟨2 * i.val, by omega⟩ : Fin 6).val % 2 = 0 := by simp
  have hfix := hx ⟨2 * i.val, by omega⟩ hk
  have hmid : frameMat σ ω * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * frameInv σ ω *
      frameMat σ ω = frameMat σ ω * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    simp only [Matrix.mul_assoc, hSi, Matrix.mul_one]
  rw [hval, ← frameMat_mulVec_even (σ := σ) ω i, Matrix.mulVec_mulVec, hmid,
    ← Matrix.mulVec_mulVec, hfix]

theorem frameConj_short_mem_U0 (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    {a b : Fin 6} (ha : a.val % 2 = 0) (hb : b.val % 2 = 1) (hab : a ≠ b) (hbp : b ≠ partner a)
    (c : F) :
    ∃ g : SUid σ 6, g ∈ e3uU0Sub σ ∧ (g : GL (Fin 6) F) =
      frameGL σ ω hω * (transvGL F a b hab c *
        transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) *
      (frameGL σ ω hω)⁻¹ := by
  have hmem := frameConj_short_mem hσ hω hab hbp c
  refine ⟨⟨_, hmem⟩, ?_, rfl⟩
  intro i
  exact h50_frameConj_fixes_T0 (x := transvGL F a b hab c *
      transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) hω
    (fun k hk => h50_short_fix_even c ha hb hab (partner_ne_partner hab) k hk) i

@[expose] noncomputable def Nop (F : Type) [Field F] [CharP F 2] (a b : Fin 6) (hab : a ≠ b) :
    Cube F →ₗ[F] Cube F :=
  rho F (transvGL F a b hab 1) - 1

theorem rho_transvGL_eq_add_Nop {a b : Fin 6} (hab : a ≠ b) (c : F) (ξ : Cube F) :
    rho F (transvGL F a b hab c) ξ = ξ + c • Nop F a b hab ξ := by
  have hN : Nop F a b hab ξ = rho F (transvGL F a b hab 1) ξ - ξ := by
    simp only [Nop, LinearMap.sub_apply, Module.End.one_apply]
  refine (cubeBasis F).ext_elem fun I => ?_
  change coord F _ I = coord F _ I
  rw [hN, coord_add, coord_smul, coord_sub, coord_rho_transvGL_gen a b hab c ξ I,
    coord_rho_transvGL_gen a b hab (1 : F) ξ I]
  by_cases h : a ∈ I.val ∧ b ∉ I.val
  · rw [dif_pos h, dif_pos h]
    ring
  · rw [dif_neg h, dif_neg h]
    ring

theorem coord_Nop {a b : Fin 6} (hab : a ≠ b) (ξ : Cube F) (J : Set.powersetCard (Fin 6) 3) :
    coord F (Nop F a b hab ξ) J =
      if h : a ∈ J.val ∧ b ∉ J.val then coord F ξ (replSet J b a h.1 h.2) else 0 := by
  rw [Nop, LinearMap.sub_apply, Module.End.one_apply, coord_sub,
    coord_rho_transvGL_gen a b hab (1 : F) ξ J]
  by_cases h : a ∈ J.val ∧ b ∉ J.val
  · rw [dif_pos h, dif_pos h]
    ring
  · rw [dif_neg h, dif_neg h]
    ring

theorem Nop_cubeBasis {a b : Fin 6} (hab : a ≠ b) (I : Set.powersetCard (Fin 6) 3) :
    Nop F a b hab (cubeBasis F I) =
      if h : b ∈ I.val ∧ a ∉ I.val then cubeBasis F (replSet I a b h.1 h.2) else 0 := by
  rw [Nop, LinearMap.sub_apply, Module.End.one_apply,
    rho_transvGL_cubeBasis_gen a b hab (1 : F) I]
  by_cases h : b ∈ I.val ∧ a ∉ I.val
  · rw [dif_pos h, dif_pos h, one_smul]
    abel
  · rw [dif_neg h, dif_neg h, sub_self]

theorem coord_eq_zero_of_Nop_eq_zero {a b : Fin 6} (hab : a ≠ b) {ξ : Cube F}
    (h : Nop F a b hab ξ = 0) {I : Set.powersetCard (Fin 6) 3} (hb : b ∈ I.val) (ha : a ∉ I.val) :
    coord F ξ I = 0 := by
  have hJ := replSet_eq_imp hab hb ha rfl
  have key := coord_Nop hab ξ (replSet I a b hb ha)
  rw [h, coord_zero, dif_pos hJ] at key
  have hI : I = replSet (replSet I a b hb ha) b a hJ.1 hJ.2 :=
    (replSet_eq_iff hb ha hJ.1 hJ.2).mp rfl
  rw [← hI] at key
  exact key.symm

theorem rho_shortRoot_sub {a b : Fin 6} (hab : a ≠ b) (c : F) (ξ : Cube F) :
    rho F (transvGL F a b hab c *
        transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) ξ - ξ =
      c • Nop F a b hab ξ + σ c • Nop F (partner b) (partner a) (partner_ne_partner hab) ξ +
        (c * σ c) • Nop F a b hab (Nop F (partner b) (partner a) (partner_ne_partner hab) ξ) := by
  rw [rho_mul, Module.End.mul_apply, rho_transvGL_eq_add_Nop hab c,
    rho_transvGL_eq_add_Nop (partner_ne_partner hab) (σ c) ξ, map_add, map_smul, smul_add,
    smul_smul]
  abel

theorem three_vectors (hσ : IsUnitaryInvolution σ) {V : Type*} [AddCommGroup V] [Module F V]
    (S : Submodule F V) {x y z : V}
    (h : ∀ c : F, c • x + σ c • y + (c * σ c) • z ∈ S) : x ∈ S ∧ y ∈ S ∧ z ∈ S := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hσω : σ ω = ω + 1 := by linear_combination hω - ω * h2
  have hσω1 : σ (ω + 1) = ω := by
    rw [← hσω]
    exact hσ.invol ω
  have hA : ω • x + (ω + 1) • y + (ω * (ω + 1)) • z ∈ S := by
    have := h ω
    rwa [hσω] at this
  have hB : (ω + 1) • x + ω • y + ((ω + 1) * ω) • z ∈ S := by
    have := h (ω + 1)
    rwa [hσω1] at this
  have e1 : ω + (ω + 1) = 1 := by linear_combination ω * h2
  have e2 : ω + 1 + ω = 1 := by linear_combination ω * h2
  have e3 : ω * (ω + 1) + (ω + 1) * ω = 0 := by linear_combination (ω ^ 2 + ω) * h2
  have hsum : (ω • x + (ω + 1) • y + (ω * (ω + 1)) • z) +
      ((ω + 1) • x + ω • y + ((ω + 1) * ω) • z) =
        (ω + (ω + 1)) • x + (ω + 1 + ω) • y + (ω * (ω + 1) + (ω + 1) * ω) • z := by
    simp only [add_smul]
    abel
  rw [e1, e2, e3, one_smul, one_smul, zero_smul, add_zero] at hsum
  have hxy : x + y ∈ S := by
    rw [← hsum]
    exact S.add_mem hA hB
  have hz : z ∈ S := by
    have h1 : x + y + z ∈ S := by
      simpa only [map_one, one_smul, one_mul] using h 1
    have h3 := S.sub_mem h1 hxy
    simpa using h3
  have hy : y ∈ S := by
    have key := S.sub_mem (S.sub_mem hA (S.smul_mem ω hxy)) (S.smul_mem (ω * (ω + 1)) hz)
    have eq : ω • x + (ω + 1) • y + (ω * (ω + 1)) • z - ω • (x + y) - (ω * (ω + 1)) • z = y := by
      simp only [smul_add, add_smul, one_smul]
      abel
    rwa [eq] at key
  have hx : x ∈ S := by
    have key := S.sub_mem hxy hy
    simpa using key
  exact ⟨hx, hy, hz⟩

end CFSG.RankThree.GF2n.Smith81.U6Cube
