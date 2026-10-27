module

public import CFSG.Quasithin.MS93.MSPLevi

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

@[expose] def oTwo {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | g ∈ H ∧ ∃ n : ℕ, g ^ 2 ^ n = 1}

theorem oTwo_le {G : Type*} [Group G] (H : Subgroup G) : oTwo H ≤ H :=
  (Subgroup.closure_le _).2 fun _ hg => hg.1

theorem mem_oTwo_of {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H) {n : ℕ}
    (hn : g ^ 2 ^ n = 1) : g ∈ oTwo H :=
  Subgroup.subset_closure ⟨hg, n, hn⟩

theorem le_oTwo {G : Type*} [Group G] {H K : Subgroup G} (hKH : K ≤ H) (hK : IsPGroup 2 K) :
    K ≤ oTwo H := fun g hg => by
  obtain ⟨n, hn⟩ := hK ⟨g, hg⟩
  exact mem_oTwo_of (hKH hg) (n := n) (by simpa using congrArg Subtype.val hn)

theorem oTwo_map_conj {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    (oTwo H).map (MulAut.conj g).toMonoidHom = oTwo (H.map (MulAut.conj g).toMonoidHom) := by
  rw [oTwo, MonoidHom.map_closure, oTwo]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨hy, n, hn⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, n, by rw [conj_pow, hn, mul_one, mul_inv_cancel]⟩
  · rintro ⟨⟨y, hy, rfl⟩, n, hn⟩
    refine ⟨y, ⟨hy, n, ?_⟩, rfl⟩
    rw [conj_pow] at hn
    have := congrArg (fun z => g⁻¹ * z * g) hn
    simpa [mul_assoc] using this

@[expose] def IsFlag (p l : Submodule F (V4 F)) : Prop := IsPoint p ∧ IsLine l ∧ p ≤ l

theorem exists_map_flag {p l : Submodule F (V4 F)} (h : IsFlag p l) :
    ∃ g : Sp4 F, (pt₀ F).map (mulVecLin (mat g)) = p ∧ (ln₀ F).map (mulVecLin (mat g)) = l := by
  let Fl : ℕ → Submodule F (V4 F) := fun i => if i = 0 then ⊥ else if i = 1 then p else l
  have hFl : IsCompleteIsotropicFlag (pairedSympForm F 2) 2 Fl := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · interval_cases i
      · simp [Fl]
      · show Module.finrank F p = 1
        exact h.1
      · show Module.finrank F l = 2
        exact h.2.1.1
    · interval_cases i
      · simp [Fl]
      · simpa [Fl] using h.2.2
    · interval_cases i
      · intro x hx y hy
        have hx0 : x = 0 := (Submodule.mem_bot F).1 hx
        rw [hx0, map_zero, LinearMap.zero_apply]
      · intro x hx y hy
        exact h.2.1.2 x (h.2.2 hx) y (h.2.2 hy)
      · exact h.2.1.2
  obtain ⟨g, hg⟩ := exists_statedSp_map_flag
    (SymplecticHigher.unitriangular_invariant_isotropic_subspaces (r := 2) (K := F)).2.2.1 hFl
  exact ⟨g, by simpa [Fl] using hg 1 le_rfl (by norm_num),
    by simpa [Fl] using hg 2 (by norm_num) le_rfl⟩

theorem P₂_not_le_P₁ : ¬ P₂ F ≤ P₁ F := fun h =>
  levHom₂_wJ_not_mem_P₁ (h (lev₂_le_P₂ levHom₂_wJ_mem_lev₂))

theorem P₁_not_le_P₂ : ¬ P₁ F ≤ P₂ F := fun h =>
  levHom₁_wJ_not_mem_P₂ (h (lev₁_le_P₁ ⟨wJ F, rfl⟩))

theorem eq_top_of_P₂_lt {Y : Subgroup (Sp4 F)} (h : P₂ F < Y) : Y = ⊤ := by
  rcases overgroups_borel (borel_le_P₂.trans h.le) with h' | h' | h' | h'
  · exact absurd (h' ▸ h.le) not_P₂_le_borel
  · exact absurd (h' ▸ h.le) P₂_not_le_P₁
  · exact absurd h' (ne_of_gt h)
  · exact h'

theorem eq_top_of_P₁_lt {Y : Subgroup (Sp4 F)} (h : P₁ F < Y) : Y = ⊤ := by
  rcases overgroups_borel (borel_le_P₁.trans h.le) with h' | h' | h' | h'
  · exact absurd (h' ▸ h.le) not_P₁_le_borel
  · exact absurd h' (ne_of_gt h)
  · exact absurd (h' ▸ h.le) P₁_not_le_P₂
  · exact h'

theorem isCoatom_P₂ : IsCoatom (P₂ F) :=
  ⟨fun h => P₁_not_le_P₂ (by rw [h]; exact le_top), fun _ hY => eq_top_of_P₂_lt hY⟩

theorem isCoatom_P₁ : IsCoatom (P₁ F) :=
  ⟨fun h => P₂_not_le_P₁ (by rw [h]; exact le_top), fun _ hY => eq_top_of_P₁_lt hY⟩

section OTwo

variable [CharP F 2]

theorem spX_mem_L₂ (a b d : F) :
    (⟨(CFSG.Quasithin.JonesParshall.spX a b d : GL (Fin 2 ⊕ Fin 2) F), by
      rw [← Explicit.sp4_eq_statedSp]; exact (CFSG.Quasithin.JonesParshall.spX a b d).2⟩ :
        Sp4 F) ∈ L₂ F := by
  have : (⟨(CFSG.Quasithin.JonesParshall.spX a b d : GL (Fin 2 ⊕ Fin 2) F), by
      rw [← Explicit.sp4_eq_statedSp]; exact (CFSG.Quasithin.JonesParshall.spX a b d).2⟩ :
        Sp4 F) = transv (e₁ F) (a - b) * transv (e₂ F) (d - b) * transv (e₁ F + e₂ F) b :=
    Subtype.ext (spX_eq a b d)
  rw [this]
  exact mul_mem (mul_mem (transv_mem_L₂ (by simp) _) (transv_mem_L₂ (by simp) _))
    (transv_mem_L₂ (by simp) _)

omit [CharP F 2] in
theorem vec4_e₁ : CFSG.Quasithin.JonesParshall.vec4 (1 : F) 0 0 0 = e₁ F := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [CFSG.Quasithin.JonesParshall.vec4]

theorem mem_L₂_of_fix {g : Sp4 F} (hg : mat g *ᵥ e₁ F = e₁ F) : g ∈ L₂ F := by
  have hgsp : (g : GL (Fin 2 ⊕ Fin 2) F) ∈ Explicit.sp4 F := by
    rw [Explicit.sp4_eq_statedSp]
    exact g.2
  have hmem := CFSG.Quasithin.JonesParshall.mem_closure_of_fix hgsp (by
    change mat g *ᵥ CFSG.Quasithin.JonesParshall.vec4 1 0 0 0 =
      CFSG.Quasithin.JonesParshall.vec4 1 0 0 0
    rw [vec4_e₁]
    exact hg)
  have hle : Subgroup.closure (CFSG.Quasithin.JonesParshall.fixGens F) ≤
      (L₂ F).map (StatedSp 2 F).subtype := by
    rw [Subgroup.closure_le]
    rintro x (⟨a, b, d, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨_, spX_mem_L₂ a b d, rfl⟩
    · refine ⟨transv (e₁ F + f₂ F) t * transv (e₁ F) t * transv (f₂ F) t,
        mul_mem (mul_mem (transv_mem_L₂ (by simp) _) (transv_mem_L₂ (by simp) _))
          (transv_mem_L₂ (by simp) _), ?_⟩
      exact (spZ_eq t).symm
    · refine ⟨transv (f₂ F) t, transv_mem_L₂ (by simp) _, ?_⟩
      rw [spY_eq, sub_zero, sub_zero, transv_zero, transv_zero, one_mul, mul_one]
      rfl
  obtain ⟨g', hg', he⟩ := hle hmem
  rwa [show g = g' from Subtype.ext he.symm]

omit [CharP F 2] in
theorem eq_one_of_pow_two_pow [CharP F 2] {s : F} {n : ℕ} (h : s ^ 2 ^ n = 1) : s = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h' := sub_pow_char_pow (p := 2) s 1 n
  rw [h, one_pow, sub_self] at h'
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h')

theorem oTwo_P₂ [Finite F] : oTwo (P₂ F) = L₂ F := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) (sup_le ?_ ?_)
  · rintro g ⟨hg, n, hn⟩
    have he : e₁ F ∈ pt₀ F := by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _
    have hge := mulVec_mem_of_mem_stab hg he
    rw [pt₀_eq_span] at hge
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hge
    have hpow : ∀ k : ℕ, mat (g ^ k) *ᵥ e₁ F = s ^ k • e₁ F := by
      intro k
      induction k with
      | zero => rw [pow_zero, mat_one, one_mulVec, pow_zero, one_smul]
      | succ k ih => rw [pow_succ', mat_mul_mulVec, ih, mulVec_smul, ← hs, smul_smul, pow_succ,
          mul_comm]
    have h1 := hpow (2 ^ n)
    rw [hn, mat_one, one_mulVec] at h1
    have hs1 : s ^ 2 ^ n = 1 := by
      have := congrFun h1 (.inl 0)
      simpa using this.symm
    rw [eq_one_of_pow_two_pow hs1, one_smul] at hs
    exact mem_L₂_of_fix hs.symm
  · exact le_oTwo Q₂_le_P₂ (isPGroup_sylS.to_le Q₂_le_sylS)
  · rw [← range_levHom₂]
    rintro _ ⟨M, rfl⟩
    induction M using Matrix.SL2.transvection_induction with
    | htransvec i j h c =>
      refine mem_oTwo_of (lev₂_le_P₂ (by rw [← range_levHom₂]; exact ⟨_, rfl⟩)) (n := 1) ?_
      rw [pow_one, sq, ← map_mul]
      have : Matrix.SpecialLinearGroup.transvection h c *
          Matrix.SpecialLinearGroup.transvection h c = 1 := by
        rw [← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero]
        exact Subtype.ext (by
          rw [Matrix.SpecialLinearGroup.transvection_coe]
          simp)
      rw [this, map_one]
    | hmul A B hA hB =>
      rw [map_mul]
      exact mul_mem hA hB

omit [CharP F 2] in
theorem toBlocks₂₁_eq_zero_of_mem_P₁ {g : Sp4 F} (hg : g ∈ P₁ F) : (mat g).toBlocks₂₁ = 0 := by
  ext i j
  rw [toBlocks₂₁, of_apply, mat_apply_eq, Matrix.zero_apply]
  have hj : (Pi.single (.inl j) 1 : V4 F) ∈ ln₀ F := mem_ln₀.2 ⟨by simp, by simp⟩
  have := mem_ln₀.1 (mulVec_mem_of_mem_stab hg hj)
  fin_cases i
  · exact this.1
  · exact this.2

omit [CharP F 2] in
theorem toBlocks₁₁_mul_of {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hN : N.toBlocks₂₁ = 0) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁, hN, Matrix.mul_zero, add_zero]

omit [CharP F 2] in
theorem toBlocks₁₁_one : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = 1 := by
  rw [← fromBlocks_one, toBlocks_fromBlocks₁₁]

theorem oTwo_P₁ [Finite F] : oTwo (P₁ F) = L₁ F := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) (sup_le ?_ ?_)
  · rintro g ⟨hg, n, hn⟩
    have h21 := toBlocks₂₁_eq_zero_of_mem_P₁ hg
    obtain ⟨hdetU, C, hC, hgC⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
    obtain ⟨A, hA⟩ : ∃ A, A = (mat g).toBlocks₁₁ := ⟨_, rfl⟩
    have hgC' : mat g = blockMat A C := by rw [hA]; exact hgC
    rw [← hA] at hdetU
    have hpow : ∀ k : ℕ, (mat (g ^ k)).toBlocks₁₁ = A ^ k := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, mat_one, toBlocks₁₁_one]
      | succ k ih =>
        rw [pow_succ, mat_mul, toBlocks₁₁_mul_of (toBlocks₂₁_eq_zero_of_mem_P₁ hg), ih, pow_succ,
          ← hA]
    have hA1 : A ^ 2 ^ n = 1 := by
      rw [← hpow, hn, mat_one, toBlocks₁₁_one]
    have hdet : A.det = 1 := by
      have := congrArg Matrix.det hA1
      rw [det_pow, det_one] at this
      exact eq_one_of_pow_two_pow this
    obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Matrix.SpecialLinearGroup (Fin 2) F, (M₀ : Matrix _ _ F) = A :=
      ⟨⟨A, hdet⟩, rfl⟩
    have hyQ : (levHom₁ M₀)⁻¹ * g ∈ Q₁ F := by
      have hm : mat ((levHom₁ M₀)⁻¹ * g) = mat (tau hC) := by
        rw [mat_mul, ← map_inv, mat_levHom₁, inv_inv, mat_tau, hgC', blockMat, blockMat,
          unitri_zero, inv_one, transpose_one, Matrix.one_mul, fromBlocks_multiply]
        have h1 : ((M₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * A =
            1 := by
          rw [← hM₀, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one]
        have h2 : (M₀ : Matrix (Fin 2) (Fin 2) F)ᵀ * A⁻¹ᵀ = 1 := by
          rw [← transpose_mul, hM₀, Matrix.nonsing_inv_mul _ hdetU, transpose_one]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2,
          ← Matrix.mul_assoc, Matrix.one_mul]
      rw [mat_injective hm]
      exact tau_mem_Q₁ hC
    have : g = levHom₁ M₀ * ((levHom₁ M₀)⁻¹ * g) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right ⟨M₀, rfl⟩) (Subgroup.mem_sup_left hyQ)
  · exact le_oTwo Q₁_le_P₁ (isPGroup_sylS.to_le Q₁_le_sylS)
  · rintro _ ⟨M, rfl⟩
    induction M using Matrix.SL2.transvection_induction with
    | htransvec i j h c =>
      refine mem_oTwo_of (lev₁_le_P₁ ⟨_, rfl⟩) (n := 1) ?_
      rw [pow_one, sq, ← map_mul]
      have : Matrix.SpecialLinearGroup.transvection h c *
          Matrix.SpecialLinearGroup.transvection h c = 1 := by
        rw [← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero]
        exact Subtype.ext (by
          rw [Matrix.SpecialLinearGroup.transvection_coe]
          simp)
      rw [this, map_one]
    | hmul A B hA hB =>
      rw [map_mul]
      exact mul_mem hA hB

end OTwo

end CFSG.Quasithin.MS93.MSP
