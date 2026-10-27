module

public import CFSG.ClassicalGroups.Unitary.SmallOrbit
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Norm
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.Quasithin.Background.E3Restrict
public import CFSG.Quasithin.Background.HMultFix
public import CFSG.Quasithin.Background.HMultNorm
public import CFSG.Quasithin.Background.SmithD321Ext
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.E3
open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Matrix

variable {K : Type} [Field K] [Finite K]

theorem le_three_mul_of_mem_aSet_natNorm_su4 {m : ℕ}
    (hK : Nat.card K = (2 ^ m) ^ 2)
    {Y A : Subgroup (MulAut (StdMod (Fin 4) K))}
    (hY : Y ≤ natNorm (StatedSU 4 (2 ^ m) K)) {k : ℕ}
    (hA : A ∈ E3.aSet k Y) : k ≤ 3 * m := by
  classical
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmp
    · rw [hm0, pow_zero, one_pow] at hK
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact hmp
  by_cases hk : k ≤ 3 * m
  · exact hk
  have hk3 : 3 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hA1 : A ≠ ⊥ := hA.2.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hcard : Nat.card K = 2 ^ (2 * m) := by
    rw [hK, ← pow_mul]
    congr 1
    omega
  have hcomm : HasScalarCommutant (StatedSU 4 (2 ^ m) K) :=
    fun f hf => commutant_statedSU (n := m) hK f hf
  have hsemi : ∀ a ∈ A, ∃ σ : K ≃+* K, IsSemilinear a σ := fun a ha =>
    exists_semilinear hcomm (hY (hA.1 ha))
  have hlin : ∀ a ∈ A, IsSemilinear a (RingEquiv.refl K) :=
    forall_linear_of_mem_aSet (κ := Fin 4) (n := 2 * m) (by omega) hcard hk2 hA hsemi
  obtain ⟨σ, hσ, h2, hSU⟩ := statedSU_data (n := m) hK
  have hiso : ∀ a ∈ A, ∀ x y : Fin 4 → K,
      ClassicalGroups.Unitary.herm σ (toAddMap a x) (toAddMap a y) =
        ClassicalGroups.Unitary.herm σ x y := by
    intro a ha x y
    obtain ⟨M, hM⟩ := exists_matAut_of_mem_linSub (mem_linSub.mpr (hlin a ha))
    have hM2gl : M * M = 1 := by
      have h := hAel.2 a ha
      refine matHom_injective ?_
      rw [map_mul, map_one, matHom_apply, ← hM]
      simpa [pow_two] using h
    have hM2mat : (M : Matrix (Fin 4) (Fin 4) K) * (M : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, hM2gl, Units.val_one]
    have hMnorm : matAut M ∈ natNorm (StatedSU 4 (2 ^ m) K) := by
      rw [← hM]
      exact hY (hA.1 ha)
    have hN : ∀ g ∈ StatedSU 4 (2 ^ m) K,
        ∃ g' ∈ StatedSU 4 (2 ^ m) K,
          ∀ x : Fin 4 → K,
            ((M : Matrix (Fin 4) (Fin 4) K) *ᵥ
              (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x)) =
            ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
              ((M : Matrix (Fin 4) (Fin 4) K) *ᵥ x) := by
      intro g hg
      have hmem : matAut M * matAut g * (matAut M)⁻¹ ∈
          natImage (StatedSU 4 (2 ^ m) K) :=
        (Subgroup.mem_normalizer_iff.mp hMnorm (matAut g)).mp ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp hmem
      refine ⟨g'.1, g'.2, ?_⟩
      intro z
      have h2' := congrArg (fun t : MulAut (StdMod (Fin 4) K) =>
        toAddMap t ((M : Matrix (Fin 4) (Fin 4) K) *ᵥ z)) hg'
      have hinv : toAddMap ((matAut M)⁻¹) ((M : Matrix (Fin 4) (Fin 4) K) *ᵥ z) = z := by
        rw [← toAddMap_matAut M z]
        exact toAddMap_apply_inv (matAut M) z
      simpa [toAddMap_mul, toAddMap_natAut, toAddMap_matAut, hinv] using h2'.symm
    obtain ⟨g, hgSU, hgM⟩ := exists_mem_statedSU_of_normalizes (n := m) hK M hM2mat hN
    have hgSUid : g ∈ LieType.Universal.Unitary.SUid σ 4 := by
      rw [hSU]
      exact hgSU
    have hisog := (ClassicalGroups.Unitary.mem_SUid_iff σ).mp hgSUid
    have hisoM : ∀ x y : Fin 4 → K,
        ClassicalGroups.Unitary.herm σ
          (((M : Matrix (Fin 4) (Fin 4) K) *ᵥ x))
          (((M : Matrix (Fin 4) (Fin 4) K) *ᵥ y)) =
        ClassicalGroups.Unitary.herm σ x y := by
      intro x y
      have h := hisog.2 x y
      simpa [hgM] using h
    rw [hM, toAddMap_matAut, toAddMap_matAut]
    exact hisoM x y
  obtain ⟨w, hw, U, hUcard, hU⟩ :=
    ClassicalGroups.Unitary.exists_small_orbit_unitary (σ := σ) hσ (m := m) hK hAel hA1 hlin hiso
  have hle : k ≤ E3.mQuot A (stabAt A w) := le_mQuot_stabAt_of_mem_aSet hA hw
  have hpow : 2 ^ E3.mQuot A (stabAt A w) ≤ Nat.card U :=
    two_pow_mQuot_stabAt_le hAel hU
  have hbound : 2 ^ k ≤ 2 ^ (3 * m) := by
    calc 2 ^ k ≤ 2 ^ E3.mQuot A (stabAt A w) :=
          Nat.pow_le_pow_right (by norm_num) hle
      _ ≤ Nat.card U := hpow
      _ ≤ 2 ^ (3 * m) := hUcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hbound

theorem eight_le_rkIdx_of_normalForm_su4
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    {T : MulAut (StdMod (Fin 2 × Fin 4) K)}
    {A : MulAut (StdMod (Fin 4) K)} {σ : K ≃+* K} {B : GL (Fin 2) K}
    (hA : IsSemilinear A σ) (hTσ : IsSemilinear T σ)
    (hT : ∀ (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
      toAddMap T v p = toAddMap A (fun i => ∑ j, (B : Matrix (Fin 2) (Fin 2) K) p.1 j *
        v (j, i)) p.2)
    (hT2 : T ^ 2 = 1) (hT1 : T ≠ 1) :
    8 ≤ rkIdx (fixV (Subgroup.zpowers T)) := by
  classical
  have hK4 : Nat.card K = 2 ^ 4 := by
    rw [hK]
    norm_num
  by_cases hσ : σ = RingEquiv.refl K
  · subst hσ
    have hAlin : IsSemilinear A (RingEquiv.refl K) := hA
    by_cases hB : ∃ c : K, B = c • (1 : Matrix (Fin 2) (Fin 2) K)
    · obtain ⟨c, hBc⟩ := hB
      have hc : c ≠ 0 := by
        rintro rfl
        have hzero : (B : Matrix (Fin 2) (Fin 2) K) = 0 := by simpa using hBc
        have hone : ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [hzero, Matrix.mul_zero] at hone
        exact one_ne_zero hone.symm
      let u : Kˣ := Units.mk0 c hc
      let A' : MulAut (StdMod (Fin 4) K) :=
        A * matAut (Matrix.GeneralLinearGroup.scalar (Fin 4) u)
      have hscalar : ∀ w : Fin 4 → K,
          toAddMap (matAut (Matrix.GeneralLinearGroup.scalar (Fin 4) u)) w = c • w := by
        intro w
        rw [toAddMap_matAut, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
        funext i
        rw [Matrix.mulVec_diagonal]
        simp [Pi.smul_apply, smul_eq_mul, u]
      have hA'apply : ∀ w : Fin 4 → K, toAddMap A' w = c • toAddMap A w := by
        intro w
        change toAddMap (A * matAut (Matrix.GeneralLinearGroup.scalar (Fin 4) u)) w = _
        rw [toAddMap_mul, hscalar, hAlin]
        rfl
      have hA'lin : IsSemilinear A' (RingEquiv.refl K) := by
        have hsc : IsSemilinear (matAut (Matrix.GeneralLinearGroup.scalar (Fin 4) u))
            (RingEquiv.refl K) := isSemilinear_matAut _
        have h := hAlin.mul hsc
        have hrefl : (RingEquiv.refl K).trans (RingEquiv.refl K) = RingEquiv.refl K := by
          ext c
          rfl
        rw [hrefl] at h
        simpa [A'] using h
      have hformA' : ∀ (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
          toAddMap T v p = toAddMap A' (fun i => v (p.1, i)) p.2 := by
        intro v p
        rw [hT v p, hA'apply]
        rw [hBc]
        have hinner : (fun i => ∑ j, (c • (1 : Matrix (Fin 2) (Fin 2) K)) p.1 j *
            v (j, i)) = fun i => c * v (p.1, i) := by
          funext i
          rw [Finset.sum_eq_single p.1]
          · simp
          · intro b _ hb
            simp [Matrix.one_apply, Ne.symm hb]
          · intro hp
            exact (hp (Finset.mem_univ _)).elim
        rw [hinner]
        have hsmul : (fun i => c * v (p.1, i)) = c • (fun i => v (p.1, i)) := by
          funext i
          simp [Pi.smul_apply, smul_eq_mul]
        rw [hsmul, hAlin]
        rfl
      have hA'ne : A' ≠ 1 := by
        intro h1
        apply hT1
        apply toAddMap_injective
        intro v
        funext p
        rw [hformA', h1, toAddMap_one]
        rfl
      have hdiag := H.Mult.rkIdx_fixV_of_diag_formula (k := 2) (T := T) (A := A') hformA'
      have hle := H.le_rkIdx_fixV_of_linear (ι := Fin 4) hK4 hA'lin hA'ne
      rw [hdiag]
      omega
    · push Not at hB
      have hle := H.Mult.le_rkIdx_fixV_of_nonscalar (ι := Fin 4) (k := 2) hK4 hAlin hT hB
      exact le_trans (by norm_num : 8 ≤ 16) hle
  · have hres := H.rkIdx_fixV_of_semilinear_two (ι := Fin 2 × Fin 4) (n := 4)
      (by norm_num) hK4 hTσ hσ hT2
    have hcardι : Fintype.card (Fin 2 × Fin 4) = 8 := by simp
    rw [hcardι] at hres
    omega

theorem eight_le_mParam_natNorm_diag_su4
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    {Y : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K))}
    (hY : Y ≤ natNorm (H.Mult.diagSub 2 (StatedSU 4 (2 ^ 2) K))) :
    8 ≤ E3.mParam Y := by
  classical
  have hΓ : HasScalarCommutant (StatedSU 4 (2 ^ 2) K) :=
    fun f hf => commutant_statedSU (n := 2) hK f hf
  by_cases hev : Even (Nat.card Y)
  · obtain ⟨t, htY, ht2, htval⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam Y hev
    rw [← htval]
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      omega
    have ht2' : t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [ht2] at h
    obtain ⟨A, σ, B, -, hAσ, hTσ, hT, -⟩ :=
      H.Mult.exists_of_mem_normalizer_diag (k := 2) hΓ (hY htY)
    exact eight_le_rkIdx_of_normalForm_su4 hK hAσ hTσ hT ht2' ht1
  · unfold E3.mParam
    rw [if_neg hev]
    have hK4 : Nat.card K = 2 ^ 4 := by
      rw [hK]
      norm_num
    have hcard : Nat.card (StdMod (Fin 2 × Fin 4) K) = 2 ^ 32 := by
      rw [H.card_stdMod, hK4, ← pow_mul]
      norm_num
    unfold rk
    rw [hcard, padicValNat.prime_pow]
    norm_num

theorem aSet_seven_eq_empty_natNorm_diag_su4
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    {Y : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K))}
    (hY : Y ≤ natNorm (H.Mult.diagSub 2 (StatedSU 4 (2 ^ 2) K))) :
    E3.aSet 7 Y = ∅ := by
  classical
  let Γ : Subgroup (GL (Fin 4) K) := StatedSU 4 (2 ^ 2) K
  have hΓ : HasScalarCommutant Γ :=
    fun f hf => commutant_statedSU (n := 2) hK f hf
  have hK4 : Nat.card K = 2 ^ 4 := by
    rw [hK]
    norm_num
  have hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := 4) Nat.prime_two hK4
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  have hAle : A ≤ Y := hA.1
  have hA1 : A ≠ ⊥ := hA.2.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hApg : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hAel
  have hform : ∀ a ∈ A, ∃ (A' : MulAut (StdMod (Fin 4) K)) (σ : K ≃+* K) (B : GL (Fin 2) K),
      IsSemilinear A' σ ∧ ∀ (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
        toAddMap a v p = toAddMap A' (fun i => ∑ j, (B : Matrix (Fin 2) (Fin 2) K) p.1 j *
          v (j, i)) p.2 := by
    intro a ha
    obtain ⟨A', σ, B, -, hA'semi, -, hf, -⟩ :=
      H.Mult.exists_of_mem_normalizer_diag (k := 2) hΓ (hY (hAle ha))
    exact ⟨A', σ, B, hA'semi, hf⟩
  obtain ⟨u, hu, hufix⟩ := H.Mult.exists_fixed_lineSub (ι := Fin 4) (K := K) hApg hform
  let J : Subgroup (StdMod (Fin 2 × Fin 4) K) := H.Mult.lineSub (ι := Fin 4) u
  have hI_A : ∀ a ∈ A, ∀ w ∈ J, a w ∈ J := by
    intro a ha w hw
    have hmem : a w ∈ J.map a.toMonoidHom := Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    rw [show J.map a.toMonoidHom = J from hufix a ha] at hmem
    exact hmem
  have hTdiag : ∀ (γ : GL (Fin 4) K) (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
      toAddMap (matAut (H.Mult.diagGL 2 γ)) v p =
        toAddMap (matAut γ) (fun i => ∑ j, (1 : Matrix (Fin 2) (Fin 2) K) p.1 j *
          v (j, i)) p.2 := by
    intro γ v p
    obtain ⟨p1, p2⟩ := p
    rw [toAddMap_matAut, toAddMap_matAut, H.Mult.diagGL_mulVec]
    congr 1
    funext i
    rw [Finset.sum_eq_single p1]
    · simp
    · intro b _ hb
      simp [Matrix.one_apply, Ne.symm hb]
    · intro hp
      exact (hp (Finset.mem_univ _)).elim
  have hI_X : ∀ x ∈ natImage (H.Mult.diagSub 2 Γ), ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    obtain ⟨y, hy⟩ := hw
    have hw_eq : w = H.Mult.lineEmb (ι := Fin 4) u (Multiplicative.ofAdd y) := by
      apply Multiplicative.toAdd.injective
      rw [H.Mult.lineEmb_toAdd]
      simpa using hy
    rw [hw_eq]
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨γ₀, -, hγ₀⟩ := Subgroup.mem_map.mp γ.2
    have hxmat : x = matAut (H.Mult.diagGL 2 γ₀) := by
      rw [← hγ]
      change matAut (γ : GL (Fin 2 × Fin 4) K) = matAut (H.Mult.diagGL 2 γ₀)
      rw [hγ₀]
    have hNF := H.Mult.normalForm_lineEmb (k := 2) (T := matAut (H.Mult.diagGL 2 γ₀))
      (A := matAut γ₀) (σ := RingEquiv.refl K) (B := 1)
      (isSemilinear_matAut γ₀) (hTdiag γ₀) u (Multiplicative.ofAdd y)
    rw [hxmat, hNF]
    have hmem : H.Mult.lineEmb (ι := Fin 4) u (matAut γ₀ (Multiplicative.ofAdd y)) ∈ J :=
      ⟨matAut γ₀ (Multiplicative.ofAdd y), by rw [H.Mult.lineEmb_toAdd]; rfl⟩
    simpa [Matrix.one_mulVec] using hmem
  have hfaith : ∀ x ∈ natImage (H.Mult.diagSub 2 Γ), (∀ w ∈ J, x w = w) → x = 1 := by
    intro x hx hfix
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨γ₀, -, hγ₀⟩ := Subgroup.mem_map.mp γ.2
    have hγfix : matAut γ₀ = 1 := by
      refine H.eq_one_of_linear_of_fix_basis (ι := Fin 4)
        (isSemilinear_matAut γ₀) (Pi.basisFun K (Fin 4)) ?_
      intro i
      have hmemJ : H.Mult.lineEmb (ι := Fin 4) u
          (Multiplicative.ofAdd ((Pi.basisFun K (Fin 4)) i)) ∈ J := by
        exact ⟨(Pi.basisFun K (Fin 4)) i, by rw [H.Mult.lineEmb_toAdd]; rfl⟩
      have hNF := H.Mult.normalForm_lineEmb (k := 2)
        (T := matAut (H.Mult.diagGL 2 γ₀))
        (A := matAut γ₀) (σ := RingEquiv.refl K) (B := 1)
        (isSemilinear_matAut γ₀) (hTdiag γ₀) u
        (Multiplicative.ofAdd ((Pi.basisFun K (Fin 4)) i))
      have hfixline := hfix _ hmemJ
      rw [show x = matAut (H.Mult.diagGL 2 γ₀) from by
        rw [← hγ]
        change matAut (γ : GL (Fin 2 × Fin 4) K) = matAut (H.Mult.diagGL 2 γ₀)
        rw [hγ₀]] at hfixline
      rw [hNF] at hfixline
      have hline : H.Mult.lineEmb (ι := Fin 4) u
          (matAut γ₀ (Multiplicative.ofAdd ((Pi.basisFun K (Fin 4)) i))) =
          H.Mult.lineEmb (ι := Fin 4) u
            (Multiplicative.ofAdd ((Pi.basisFun K (Fin 4)) i)) := by
        simpa [Matrix.one_mulVec] using hfixline
      exact H.Mult.lineEmb_injective hu hline
    have hγ1 : γ₀ = 1 := by
      apply matHom_injective
      rwa [matHom_apply, map_one]
    rw [← hγ]
    change matAut (γ : GL (Fin 2 × Fin 4) K) = 1
    rw [← hγ₀, hγ1]
    simpa [H.matHom_apply] using (map_one H.matHom)
  by_cases htriv : ∀ a ∈ A, ∀ w ∈ J, a w = w
  · have hAc : A ≤ Subgroup.centralizer
        (natImage (H.Mult.diagSub 2 Γ) : Set (MulAut (StdMod (Fin 2 × Fin 4) K))) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have haP : ∀ v ∈ J, a⁻¹ v ∈ J := fun v hv => hI_A a⁻¹ (A.inv_mem ha) v hv
      exact (CFSG.Quasithin.SmithD321.comm_of_trivial_on (hY (hAle ha)) hI_X hfaith
        (htriv a ha) haP x hx).symm
    have hcardA : Nat.card A ≤ Nat.card K :=
      H.Mult.card_le_of_isElemAbelian_two_centralizer_diag (ι := Fin 4) hΓ
        (H.isElemAbelian2_iff.mp hAel) hAc
    have h7 : 7 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
    have h128 : 128 ≤ Nat.card A := by
      have hp : 7 ≤ padicValNat 2 (Nat.card A) := by
        simpa [E3.mQuot, Subgroup.relIndex_bot_left] using h7
      have hdvd : 2 ^ 7 ∣ Nat.card A := by
        rw [Nat.pow_dvd_iff_le_padicValNat (by norm_num) (Nat.card_pos.ne')]
        exact hp
      have hle := Nat.le_of_dvd Nat.card_pos hdvd
      norm_num at hle ⊢
      exact hle
    have hK16 : Nat.card K = 16 := by
      rw [hK]
      norm_num
    omega
  · push Not at htriv
    obtain ⟨a₀, ha₀, w₀, hw₀, hne₀⟩ := htriv
    let Ā : Subgroup (MulAut ↥J) :=
      (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_A).range
    have hne : Ā ≠ ⊥ := by
      intro hbot
      have hmem : (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_A)
          ⟨a₀, ha₀⟩ ∈ Ā := MonoidHom.mem_range.mpr ⟨⟨a₀, ha₀⟩, rfl⟩
      rw [hbot] at hmem
      rw [Subgroup.mem_bot] at hmem
      apply hne₀
      have h2 := congrArg (fun f : MulAut ↥J =>
        (f ⟨w₀, hw₀⟩ : StdMod (Fin 2 × Fin 4) K)) hmem
      simpa [CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply] using h2
    obtain ⟨e, he⟩ := H.Mult.exists_lineSub_equiv (k := 2) (ι := Fin 4) u hu
    let XJ : Subgroup (MulAut ↥J) :=
      (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_X).range
    have hXJ_eq : XJ.map (H.congrHom e) = natImage Γ := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz
        obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp x.2
        obtain ⟨γ₀, hγ₀Γ, hγ₀⟩ := Subgroup.mem_map.mp γ.2
        have hxval : (x : MulAut (StdMod (Fin 2 × Fin 4) K)) =
            matAut (H.Mult.diagGL 2 γ₀) := by
          rw [← hγ]
          change matAut (γ : GL (Fin 2 × Fin 4) K) = matAut (H.Mult.diagGL 2 γ₀)
          rw [hγ₀]
        refine ⟨⟨γ₀, hγ₀Γ⟩, ?_⟩
        apply MulEquiv.ext
        intro v
        obtain ⟨w, rfl⟩ := e.surjective v
        rw [H.congrHom_apply, e.symm_apply_apply]
        have hmemX : (matAut (H.Mult.diagGL 2 γ₀)) w ∈ J := by
          rw [← hxval]
          exact hI_X _ x.2 w w.2
        have hsub : ((CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_X) x)
            ⟨w, w.2⟩ = ⟨matAut (H.Mult.diagGL 2 γ₀) w, hmemX⟩ := by
          apply Subtype.ext
          change ((x : MulAut (StdMod (Fin 2 × Fin 4) K)) w : StdMod (Fin 2 × Fin 4) K) =
            (matAut (H.Mult.diagGL 2 γ₀) w : StdMod (Fin 2 × Fin 4) K)
          rw [hxval]
        rw [hsub]
        exact (he γ₀ w hmemX).symm
      · rintro ⟨γ, rfl⟩
        have hxmem : matAut (H.Mult.diagGL 2 (γ : GL (Fin 4) K)) ∈
            natImage (H.Mult.diagSub 2 Γ) := by
          rw [H.natImage_eq_map]
          exact Subgroup.mem_map.mpr
            ⟨H.Mult.diagGL 2 (γ : GL (Fin 4) K),
              Subgroup.mem_map.mpr ⟨(γ : GL (Fin 4) K), γ.2, rfl⟩, rfl⟩
        refine ⟨(CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_X)
          ⟨matAut (H.Mult.diagGL 2 (γ : GL (Fin 4) K)), hxmem⟩, ?_, ?_⟩
        · exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
        · apply MulEquiv.ext
          intro v
          obtain ⟨w, rfl⟩ := e.surjective v
          rw [H.congrHom_apply, e.symm_apply_apply]
          have hsub : ((CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_X)
              ⟨matAut (H.Mult.diagGL 2 (γ : GL (Fin 4) K)), hxmem⟩) ⟨w, w.2⟩ =
              ⟨matAut (H.Mult.diagGL 2 (γ : GL (Fin 4) K)) w,
                hI_X _ hxmem w w.2⟩ := by
            apply Subtype.ext
            rfl
          rw [hsub]
          exact he (γ : GL (Fin 4) K) w (hI_X _ hxmem w w.2)
    have hnorm_a : ∀ (a : MulAut (StdMod (Fin 2 × Fin 4) K)) (ha : a ∈ A),
        (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_A) ⟨a, ha⟩ ∈
          Subgroup.normalizer (XJ : Set (MulAut ↥J)) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hle : XJ.map (MulAut.conj
          ((CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_A) ⟨a, ha⟩)) ≤ XJ := by
        intro z hz
        rw [Subgroup.mem_map] at hz
        obtain ⟨z₀, hz₀, rfl⟩ := hz
        obtain ⟨x₀, rfl⟩ := MonoidHom.mem_range.mp hz₀
        have hx₀' : a * (x₀ : MulAut (StdMod (Fin 2 × Fin 4) K)) * a⁻¹ ∈
            natImage (H.Mult.diagSub 2 Γ) :=
          (Subgroup.mem_normalizer_iff.mp (hY (hAle ha)) (x₀ : MulAut _)).mp x₀.2
        refine MonoidHom.mem_range.mpr ⟨⟨a * (x₀ : MulAut _) * a⁻¹, hx₀'⟩, ?_⟩
        apply MulEquiv.ext
        intro w
        apply Subtype.ext
        simp [CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply,
          MulAut.mul_apply]
        rfl
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective
        (MulAut.conj ((CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_A)
          ⟨a, ha⟩)).injective]
    have hAmap_le : Ā.map (H.congrHom e) ≤ natNorm Γ := by
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨a, haeq⟩ := MonoidHom.mem_range.mp hz
      rw [← haeq]
      have hnorm := hnorm_a a.1 a.2
      have hmem : H.congrHom e
          ((CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI_A) a) ∈
          (Subgroup.normalizer (XJ : Set (MulAut ↥J))).map (H.congrHom e) :=
        Subgroup.mem_map.mpr ⟨_, hnorm, rfl⟩
      rwa [Subgroup.map_equiv_normalizer_eq XJ (MulAut.congr e), hXJ_eq] at hmem
    have hĀ_aSet : Ā ∈ E3.aSet 7 ⊤ :=
      E3.mem_aSet_actOnSub hA hI_A (Y := ⊤) le_top hne
    have hĀmap_aSet : Ā.map (H.congrHom e) ∈ E3.aSet 7 (natNorm Γ) := by
      have h1 : Ā.map (H.congrHom e) ∈
          E3.aSet 7 (Subgroup.map (H.congrHom e) ⊤) :=
        (H.map_mem_aSet_iff e).mpr hĀ_aSet
      rw [Subgroup.map_top] at h1
      exact ⟨hAmap_le, h1.2.1, h1.2.2.1, h1.2.2.2⟩
    have hbound : 7 ≤ 3 * 2 :=
      le_three_mul_of_mem_aSet_natNorm_su4 (m := 2) (Y := natNorm Γ)
        (A := Ā.map (H.congrHom e)) (k := 7) hK le_rfl hĀmap_aSet
    omega

theorem eight_le_mParam_of_sumOfNatVia_su4 {W : Type} [CommGroup W] [Finite W]
    {X Y : Subgroup (MulAut W)} (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    {π : ↥(StatedSU 4 (2 ^ 2) K) →* ↥X}
    (h : SumOfNatVia (FFModel.nat (StatedSU 4 (2 ^ 2) K)) X ⊤ ⊥ 2 π) :
    8 ≤ E3.mParam Y := by
  classical
  let Γ : Subgroup (GL (Fin 4) K) := StatedSU 4 (2 ^ 2) K
  obtain ⟨I, e, -, he, -⟩ := exists_coords_of_sumOfNatVia Γ h
  have hπ : Function.Surjective π := by
    obtain ⟨I, -, -, -, hreal⟩ := h
    exact (hreal 0).1
  have hXmap : X.map (H.congrHom e) = natImage (H.Mult.diagSub 2 Γ) :=
    map_congrHom_eq_natImage_diag Γ hπ e he
  have hYmap : Y.map (H.congrHom e) ≤ natNorm (H.Mult.diagSub 2 Γ) := by
    have h1 : (Subgroup.normalizer (X : Set (MulAut W))).map (H.congrHom e) =
        Subgroup.normalizer ((X.map (H.congrHom e) :
          Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K))) : Set _) :=
      Subgroup.map_equiv_normalizer_eq X (MulAut.congr e)
    have h2 := Subgroup.map_mono (f := H.congrHom e) hYN
    rwa [h1, hXmap] at h2
  have h8 := eight_le_mParam_natNorm_diag_su4 hK hYmap
  rwa [H.mParam_map_congrHom e Y] at h8

theorem aSet_seven_eq_empty_of_sumOfNatVia_su4 {W : Type} [CommGroup W] [Finite W]
    {X Y : Subgroup (MulAut W)} (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    {π : ↥(StatedSU 4 (2 ^ 2) K) →* ↥X}
    (h : SumOfNatVia (FFModel.nat (StatedSU 4 (2 ^ 2) K)) X ⊤ ⊥ 2 π) :
    E3.aSet 7 Y = ∅ := by
  classical
  let Γ : Subgroup (GL (Fin 4) K) := StatedSU 4 (2 ^ 2) K
  obtain ⟨I, e, -, he, -⟩ := exists_coords_of_sumOfNatVia Γ h
  have hπ : Function.Surjective π := by
    obtain ⟨I, -, -, -, hreal⟩ := h
    exact (hreal 0).1
  have hXmap : X.map (H.congrHom e) = natImage (H.Mult.diagSub 2 Γ) :=
    map_congrHom_eq_natImage_diag Γ hπ e he
  have hYmap : Y.map (H.congrHom e) ≤ natNorm (H.Mult.diagSub 2 Γ) := by
    have h1 : (Subgroup.normalizer (X : Set (MulAut W))).map (H.congrHom e) =
        Subgroup.normalizer ((X.map (H.congrHom e) :
          Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K))) : Set _) :=
      Subgroup.map_equiv_normalizer_eq X (MulAut.congr e)
    have h2 := Subgroup.map_mono (f := H.congrHom e) hYN
    rwa [h1, hXmap] at h2
  have hempty := aSet_seven_eq_empty_natNorm_diag_su4 hK hYmap
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  have hA' : A.map (H.congrHom e) ∈ E3.aSet 7 (Y.map (H.congrHom e)) :=
    (H.map_mem_aSet_iff e).mpr hA
  rw [hempty] at hA'
  exact hA'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
