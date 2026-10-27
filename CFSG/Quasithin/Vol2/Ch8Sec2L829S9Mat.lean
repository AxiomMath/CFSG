module

public import CFSG.Milestones.ASVolI.A3Lie

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix
open scoped MatrixGroups Pointwise

@[expose] def s9M1 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def s9P1 {R : Type*} [Ring R] (x : R) : R := x * x * x + x + 1

@[expose] def s9P2 {R : Type*} [Ring R] (x : R) : R := x * x * x + x * x + 1

theorem s9M1_det : s9M1.det = 1 := by
  simp [s9M1, Matrix.det_fin_three]

theorem s9P1_M1 : s9P1 s9M1 = 0 := by
  first
    | (unfold s9P1; decide)
    | (unfold s9P1
       ext i j
       fin_cases i <;> fin_cases j <;> simp [s9M1, Matrix.mul_apply, Fin.sum_univ_three] <;> decide)

theorem s9_P2_of_P1 (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hM : M.det = 1) (h : s9P1 M = 0) :
    s9P2 (M⁻¹)ᵀ = 0 := by
  have hunit : IsUnit M.det := by rw [hM]; exact isUnit_one
  have h' : M * M * M + M + 1 = 0 := h
  set N : Matrix (Fin 3) (Fin 3) (ZMod 2) := M⁻¹ with hNdef
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul M hunit
  have h1 : N * N * (M * M) = 1 := by
    calc N * N * (M * M) = N * (N * M) * M := by simp only [mul_assoc]
      _ = 1 := by rw [hNM, mul_one, hNM]
  have h2 : N * N * N * (M * M * M) = 1 := by
    calc N * N * N * (M * M * M) = N * N * (N * M) * (M * M) := by simp only [mul_assoc]
      _ = N * N * (M * M) := by rw [hNM, mul_one]
      _ = 1 := h1
  have h3 : N * N * N * M = N * N := by
    rw [mul_assoc, hNM, mul_one]
  have key : N * N * N * (M * M * M + M + 1) = 1 + N * N + N * N * N := by
    rw [mul_add, mul_add, mul_one, h2, h3]
  have hP2 : s9P2 N = 0 := by
    have h0 : N * N * N * (M * M * M + M + 1) = 0 := by rw [h', mul_zero]
    rw [key] at h0
    unfold s9P2
    calc N * N * N + N * N + 1 = 1 + N * N + N * N * N := by abel
      _ = 0 := h0
  have ht : s9P2 Nᵀ = (s9P2 N)ᵀ := by
    simp [s9P2, Matrix.transpose_add, Matrix.transpose_mul, mul_assoc]
  rw [ht, hP2, Matrix.transpose_zero]

theorem s9_mul_P1_of_P2 {R : Type*} [Ring R] (h2 : (2 : R) = 0) (M : R) (h : s9P2 M = 0) :
    s9P1 M * M = 1 := by
  have hx : ∀ x : R, x + x = 0 := fun x => by rw [← two_mul, h2, zero_mul]
  have h' : M * M * M + M * M + 1 = 0 := h
  have hA : M * M * M = M * M + 1 := by
    calc M * M * M = (M * M * M + M * M + 1) + (M * M + 1) := by
          have e : (M * M * M + M * M + 1) + (M * M + 1) =
              M * M * M + (M * M + M * M) + (1 + 1) := by abel
          rw [e, hx (M * M), hx 1, add_zero, add_zero]
      _ = M * M + 1 := by rw [h', zero_add]
  have hAM : M * M * M * M = M * M + 1 + M := by
    calc M * M * M * M = M * (M * M * M) := by simp only [mul_assoc]
      _ = M * (M * M + 1) := by rw [hA]
      _ = M * M * M + M := by rw [mul_add, mul_one, ← mul_assoc]
      _ = M * M + 1 + M := by rw [hA]
  have hfin : s9P1 M * M = M * M * M * M + M * M + M := by
    unfold s9P1
    noncomm_ring
  rw [hfin, hAM]
  have e2 : M * M + 1 + M + M * M + M = (M * M + M * M) + (M + M) + 1 := by abel
  rw [e2, hx (M * M), hx M, zero_add, zero_add]

theorem s9_coe_inv_SL (M : SL(3, ZMod 2)) :
    ((M⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (M : Matrix (Fin 3) (Fin 3) (ZMod 2))⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, Matrix.SpecialLinearGroup.det_coe,
    Ring.inverse_one, one_smul]

private theorem s9_mk_injective (x y : SL(3, ZMod 2))
    (h : (QuotientGroup.mk x : PSL(3, ZMod 2)) = QuotientGroup.mk y) : x = y := by
  rw [QuotientGroup.eq, CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot,
    Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h

private theorem s9_ringAut_zmod_two (σ : RingAut (ZMod 2)) : σ = 1 := by
  apply RingEquiv.ext
  intro x
  have h := RingHom.ext_zmod (σ.toRingHom) (RingHom.id (ZMod 2))
  exact congrFun (congrArg DFunLike.coe h) x

theorem s9_aut_form (α : MulAut SL(3, ZMod 2)) :
    (∃ A : SL(3, ZMod 2), ∀ M : SL(3, ZMod 2),
        ((α M : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (A⁻¹ : SL(3, ZMod 2))) ∨
    (∃ A : SL(3, ZMod 2), ∀ M : SL(3, ZMod 2),
        ((α M : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((M : Matrix (Fin 3) (Fin 3) (ZMod 2))⁻¹)ᵀ * (A⁻¹ : SL(3, ZMod 2))) := by
  obtain ⟨e, he⟩ : ∃ e : SL(3, ZMod 2) ≃* PSL(3, ZMod 2),
      ∀ M : SL(3, ZMod 2), e M = (QuotientGroup.mk M : PSL(3, ZMod 2)) :=
    ⟨MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(3, ZMod 2)))
      ⟨fun x y h => s9_mk_injective x y h, fun y => QuotientGroup.mk_surjective y⟩,
      fun M => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : MulAut PSL(3, ZMod 2), ∀ M : SL(3, ZMod 2),
      β (QuotientGroup.mk M) = QuotientGroup.mk (α M) := by
    refine ⟨(e.symm.trans α).trans e, fun M => ?_⟩
    show e (α (e.symm (QuotientGroup.mk M))) = QuotientGroup.mk (α M)
    rw [← he M, MulEquiv.symm_apply_apply, he]
  obtain ⟨g, σ, ε, hε, hβeq⟩ := CFSG.ASVolI.burnsideA315h_classification (F := ZMod 2) β
  rw [s9_ringAut_zmod_two σ, CFSG.ASVolI.burnsideA315h_field_one, mul_one] at hβeq
  obtain ⟨A, hA⟩ := CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two.2 g
  have hAcoe : ∀ X : SL(3, ZMod 2),
      ((Matrix.SpecialLinearGroup.toGL X : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    fun X => rfl
  have hAm : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [← hAcoe A, hA]
  have hAinv : ((A⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [← hAcoe (A⁻¹), map_inv, hA]
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    left
    refine ⟨A, fun M => ?_⟩
    have h1 : (QuotientGroup.mk (α M) : PSL(3, ZMod 2)) =
        CFSG.ASVolI.ChA.psl3DiagAut g (QuotientGroup.mk M) := by
      rw [← hβ M, hβeq, MulAut.mul_apply, pow_zero, MulAut.one_apply]
    have h2 : CFSG.ASVolI.ChA.psl3DiagAut g (QuotientGroup.mk M) =
        QuotientGroup.mk (CFSG.ASVolI.ChA.slConj g M) :=
      CFSG.ASVolI.burnsideA315h_pslOfSL_mk (CFSG.ASVolI.ChA.slConj g) M
    have h3 : α M = CFSG.ASVolI.ChA.slConj g M := s9_mk_injective _ _ (h1.trans h2)
    calc ((α M : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
        = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
          rw [h3]; rfl
      _ = (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((A⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
          rw [hAm, hAinv]
  ·
    right
    refine ⟨A, fun M => ?_⟩
    have h1 : (QuotientGroup.mk (α M) : PSL(3, ZMod 2)) =
        CFSG.ASVolI.ChA.psl3DiagAut g
          (CFSG.ASVolI.ChA.psl3GraphAut (QuotientGroup.mk M)) := by
      rw [← hβ M, hβeq, MulAut.mul_apply, pow_one]
    have h2 : CFSG.ASVolI.ChA.psl3GraphAut (QuotientGroup.mk M) =
        QuotientGroup.mk (CFSG.ASVolI.ChA.slGraph M) :=
      CFSG.ASVolI.burnsideA315h_pslOfSL_mk CFSG.ASVolI.ChA.slGraph M
    have h3 : CFSG.ASVolI.ChA.psl3DiagAut g (QuotientGroup.mk (CFSG.ASVolI.ChA.slGraph M)) =
        QuotientGroup.mk (CFSG.ASVolI.ChA.slConj g (CFSG.ASVolI.ChA.slGraph M)) :=
      CFSG.ASVolI.burnsideA315h_pslOfSL_mk (CFSG.ASVolI.ChA.slConj g) (CFSG.ASVolI.ChA.slGraph M)
    have h4 : α M = CFSG.ASVolI.ChA.slConj g (CFSG.ASVolI.ChA.slGraph M) :=
      s9_mk_injective _ _ (h1.trans ((congrArg (CFSG.ASVolI.ChA.psl3DiagAut g) h2).trans h3))
    have hcoe : ((CFSG.ASVolI.ChA.slGraph M : SL(3, ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = ((M : Matrix (Fin 3) (Fin 3) (ZMod 2))⁻¹)ᵀ := by
      show (((M⁻¹ : SL(3, ZMod 2)).transpose : SL(3, ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
      rw [Matrix.SpecialLinearGroup.coe_transpose, s9_coe_inv_SL]
    calc ((α M : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
        = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((CFSG.ASVolI.ChA.slGraph M : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
          rw [h4]; rfl
      _ = (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * ((M : Matrix (Fin 3) (Fin 3) (ZMod 2))⁻¹)ᵀ *
            ((A⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
          rw [hAm, hAinv, hcoe]

theorem s9_card_SL3_F2 : Nat.card SL(3, ZMod 2) = 168 := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_three]
  norm_num

private abbrev s9e1 : Fin 3 → ZMod 2 := ![1, 0, 0]

private theorem s9_vec_eq_e1 (w : Fin 3 → ZMod 2) (hw : w ≠ 0) (h1 : w 1 = 0) (h2 : w 2 = 0) :
    w = s9e1 := by
  have key : ∀ w : Fin 3 → ZMod 2, w ≠ 0 → w 1 = 0 → w 2 = 0 → w = ![1, 0, 0] := by decide
  exact key w hw h1 h2

private def s9Wit (a b c : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if a = 1 then !![1, 0, 0; b, 1, 0; c, 0, 1]
  else if b = 1 then !![0, 1, 0; 1, 0, 0; c, 0, 1]
  else !![0, 1, 0; 0, 0, 1; 1, 0, 0]

private theorem s9Wit_det (a b c : ZMod 2) : (s9Wit a b c).det = 1 := by
  unfold s9Wit
  split_ifs <;> simp [Matrix.det_fin_three] <;> decide

private theorem s9Wit_mulVec : ∀ a b c : ZMod 2, ![a, b, c] ≠ 0 →
    s9Wit a b c *ᵥ s9e1 = ![a, b, c] := by
  decide

private theorem s9_transitive (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    ∃ A : SL(3, ZMod 2), A • s9e1 = v := by
  have hv' : (![v 0, v 1, v 2] : Fin 3 → ZMod 2) = v := by
    funext i; fin_cases i <;> simp
  have key := s9Wit_mulVec (v 0) (v 1) (v 2) (by rw [hv']; exact hv)
  refine ⟨⟨s9Wit (v 0) (v 1) (v 2), s9Wit_det _ _ _⟩, ?_⟩
  change s9Wit (v 0) (v 1) (v 2) *ᵥ s9e1 = v
  rw [key, hv']

private theorem s9_smul_ne_zero (A : SL(3, ZMod 2)) (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    A • v ≠ 0 := by
  intro h
  apply hv
  have h2 := congrArg (fun x => A⁻¹ • x) h
  simpa using h2

private theorem s9_orbit_e1 :
    (MulAction.orbit SL(3, ZMod 2) s9e1).ncard = 7 := by
  have hset : MulAction.orbit SL(3, ZMod 2) s9e1 =
      ↑(Finset.univ.erase (0 : Fin 3 → ZMod 2)) := by
    ext v
    rw [MulAction.mem_orbit_iff, Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨s9_smul_ne_zero A _ (by decide), Finset.mem_univ _⟩
    · rintro ⟨hv, -⟩
      exact s9_transitive v hv
  rw [hset, Set.ncard_coe_finset]
  first
    | decide
    | simp [Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fun, ZMod.card]

private def s9E01 : SL(3, ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by
    first
      | (rw [Matrix.det_fin_three]; decide)
      | simp [Matrix.det_fin_three]⟩

private def s9E12 : SL(3, ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by
    first
      | (rw [Matrix.det_fin_three]; decide)
      | simp [Matrix.det_fin_three]⟩

private theorem s9E01_mem :
    s9E01 ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 (ZMod 2) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [s9E01]
  · fin_cases i <;> simp [s9E01]

private theorem s9E12_mem :
    s9E12 ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 (ZMod 2) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [s9E12]
  · fin_cases i <;> simp [s9E12]

private theorem s9_U_fix (u : SL(3, ZMod 2))
    (hu : u ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 (ZMod 2)) :
    u • s9e1 = s9e1 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular] at hu
  obtain ⟨hlow, hdiag⟩ := hu
  have h10 : (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 := hlow 1 0 (by decide)
  have h20 : (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 := hlow 2 0 (by decide)
  have h00 : (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 := hdiag 0
  funext i
  fin_cases i <;>
    simp [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, s9e1, h10, h20, h00]

private theorem s9E01_fix (w : Fin 3 → ZMod 2) (h : s9E01 • w = w) : w 1 = 0 := by
  have h0 : (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w := h
  have h1 := congrFun h0 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
  linear_combination h1

private theorem s9E12_fix (w : Fin 3 → ZMod 2) (h : s9E12 • w = w) : w 2 = 0 := by
  have h0 : (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w := h
  have h1 := congrFun h0 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
  linear_combination h1

theorem s9_exists_parabolic (S : Subgroup SL(3, ZMod 2))
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ P : Subgroup SL(3, ZMod 2), IsMaxParabolic2 ⊤ P ∧
      ⊤ ⊓ Subgroup.normalizer (S : Set SL(3, ZMod 2)) ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : Nat.card SL(3, ZMod 2) = 168 := s9_card_SL3_F2
  haveI : Finite SL(3, ZMod 2) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have hdvd : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h
  have hSord : Nat.card S = 8 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS.2.1
    have hmul : S.index * Nat.card S = 168 := by
      rw [← hG]; exact Subgroup.index_mul_card (H := S)
    rw [hn] at hmul ⊢
    have hle : 2 ^ n ≤ 168 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ hmul)
    have hn8 : n < 8 := by
      by_contra hc
      have hc' : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (by omega)
      norm_num at hc'
      omega
    interval_cases n
    all_goals first
      | rfl
      | (exfalso; norm_num at hmul; omega)
  have hPS : ((hS.2.1.toSylow hdvd : Sylow 2 SL(3, ZMod 2)) : Subgroup SL(3, ZMod 2)) = S := rfl
  obtain ⟨PU, hPU⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
    (K := ZMod 2) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(3, ZMod 2) PU (hS.2.1.toSylow hdvd)
  have hgU : MulAut.conj g • (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3
      (ZMod 2)) = S := by
    have h : MulAut.conj g • (PU : Subgroup SL(3, ZMod 2)) = S := by
      rw [← Sylow.coe_subgroup_smul, hg]
      exact hPS
    rw [hPU] at h
    exact h
  have hmemS : ∀ s : SL(3, ZMod 2), s ∈ S ↔
      g⁻¹ * s * g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 (ZMod 2) := by
    intro s
    have hc : (MulAut.conj g)⁻¹ • s = g⁻¹ * s * g := MulAut.conj_inv_apply g s
    rw [← hgU, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hc]
  have hUS : ∀ u ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 (ZMod 2),
      g * u * g⁻¹ ∈ S := by
    intro u hu
    rw [hmemS]
    have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [e]
    exact hu
  have hSU : ∀ s ∈ S,
      g⁻¹ * s * g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 (ZMod 2) :=
    fun s hs => (hmemS s).1 hs
  have hfix : ∀ s ∈ S, s • (g • s9e1) = g • s9e1 := by
    intro s hs
    have hue := s9_U_fix _ (hSU s hs)
    calc s • (g • s9e1) = (s * g) • s9e1 := (mul_smul _ _ _).symm
      _ = (g * (g⁻¹ * s * g)) • s9e1 := by rw [show g * (g⁻¹ * s * g) = s * g by group]
      _ = g • ((g⁻¹ * s * g) • s9e1) := mul_smul _ _ _
      _ = g • s9e1 := by rw [hue]
  have hnorm : ∀ x ∈ Subgroup.normalizer (S : Set SL(3, ZMod 2)),
      x • (g • s9e1) = g • s9e1 := by
    intro x hx
    have hxS : ∀ s ∈ S, x⁻¹ * s * x ∈ S := by
      intro s hs
      refine (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * s * x)).2 ?_
      have e : x * (x⁻¹ * s * x) * x⁻¹ = s := by group
      rw [e]
      exact hs
    obtain ⟨v, hv⟩ : ∃ v, v = x • (g • s9e1) := ⟨_, rfl⟩
    have hv_fix : ∀ s ∈ S, s • v = v := by
      intro s hs
      rw [hv]
      calc s • (x • (g • s9e1)) = (s * x) • (g • s9e1) := (mul_smul _ _ _).symm
        _ = (x * (x⁻¹ * s * x)) • (g • s9e1) := by
            rw [show x * (x⁻¹ * s * x) = s * x by group]
        _ = x • ((x⁻¹ * s * x) • (g • s9e1)) := mul_smul _ _ _
        _ = x • (g • s9e1) := by rw [hfix _ (hxS s hs)]
    have hv0 : v ≠ 0 := by
      rw [hv]
      exact s9_smul_ne_zero _ _ (s9_smul_ne_zero _ _ (by decide))
    have hw0 : g⁻¹ • v ≠ 0 := s9_smul_ne_zero _ _ hv0
    have hw01 : s9E01 • (g⁻¹ • v) = g⁻¹ • v := by
      have h1 := hv_fix _ (hUS s9E01 s9E01_mem)
      calc s9E01 • (g⁻¹ • v) = (s9E01 * g⁻¹) • v := (mul_smul _ _ _).symm
        _ = (g⁻¹ * (g * s9E01 * g⁻¹)) • v := by
            rw [show g⁻¹ * (g * s9E01 * g⁻¹) = s9E01 * g⁻¹ by group]
        _ = g⁻¹ • ((g * s9E01 * g⁻¹) • v) := mul_smul _ _ _
        _ = g⁻¹ • v := by rw [h1]
    have hw12 : s9E12 • (g⁻¹ • v) = g⁻¹ • v := by
      have h1 := hv_fix _ (hUS s9E12 s9E12_mem)
      calc s9E12 • (g⁻¹ • v) = (s9E12 * g⁻¹) • v := (mul_smul _ _ _).symm
        _ = (g⁻¹ * (g * s9E12 * g⁻¹)) • v := by
            rw [show g⁻¹ * (g * s9E12 * g⁻¹) = s9E12 * g⁻¹ by group]
        _ = g⁻¹ • ((g * s9E12 * g⁻¹) • v) := mul_smul _ _ _
        _ = g⁻¹ • v := by rw [h1]
    have hwe : g⁻¹ • v = s9e1 :=
      s9_vec_eq_e1 _ hw0 (s9E01_fix _ hw01) (s9E12_fix _ hw12)
    calc x • (g • s9e1) = v := hv.symm
      _ = g • (g⁻¹ • v) := (smul_inv_smul g v).symm
      _ = g • s9e1 := by rw [hwe]
  have hnormle : ⊤ ⊓ Subgroup.normalizer (S : Set SL(3, ZMod 2)) ≤
      MulAction.stabilizer SL(3, ZMod 2) (g • s9e1) := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff]
    exact hnorm x (Subgroup.mem_inf.1 hx).2
  have hindex : (MulAction.stabilizer SL(3, ZMod 2) (g • s9e1)).index = 7 := by
    rw [MulAction.index_stabilizer, MulAction.orbit_smul, s9_orbit_e1]
  have hcardP : Nat.card (MulAction.stabilizer SL(3, ZMod 2) (g • s9e1)) = 24 := by
    have h := Subgroup.index_mul_card (H := MulAction.stabilizer SL(3, ZMod 2) (g • s9e1))
    rw [hindex, hG] at h
    omega
  have hne : MulAction.stabilizer SL(3, ZMod 2) (g • s9e1) ≠ ⊤ := by
    intro h
    have h2 := Subgroup.card_top (G := SL(3, ZMod 2))
    rw [← h, hcardP, hG] at h2
    norm_num at h2
  have hmax : ∀ Q : Subgroup SL(3, ZMod 2), IsParabolic2 ⊤ Q → Q ≠ ⊤ →
      MulAction.stabilizer SL(3, ZMod 2) (g • s9e1) ≤ Q →
        Q = MulAction.stabilizer SL(3, ZMod 2) (g • s9e1) := by
    intro Q _ hQt hPQ
    have hd1 := Subgroup.card_dvd_of_le hPQ
    have hd2 := Subgroup.card_subgroup_dvd_card Q
    rw [hcardP] at hd1
    rw [hG] at hd2
    obtain ⟨k, hk⟩ := hd1
    have hk7 : k ∣ 7 := by
      have h168 : 24 * k ∣ 24 * 7 := by
        rw [← hk]
        exact hd2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h168
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hk7 with rfl | rfl
    · exact (Subgroup.eq_of_le_of_card_ge hPQ (le_of_eq (by rw [hcardP, hk]))).symm
    · exfalso
      apply hQt
      apply Subgroup.eq_top_of_card_eq
      rw [hk, hG]
  exact ⟨MulAction.stabilizer SL(3, ZMod 2) (g • s9e1),
    ⟨⟨le_top, S, hS, hnormle⟩, hne, hmax⟩, hnormle⟩

end CFSG.Quasithin.H13.L829N
