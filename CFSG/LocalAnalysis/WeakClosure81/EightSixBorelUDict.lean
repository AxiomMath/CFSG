module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofHermitian
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUFix
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutModel
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSetup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.RankTwoClassical
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)

variable {m n : ℕ} {F : Type} [Field F] [Finite F]

private theorem borel86_ud_val_mul_self {G : StatedSU m (2 ^ n) F} (hG : G * G = 1) :
    (G : GL (Fin m) F).val * (G : GL (Fin m) F).val = 1 := by
  have h := congrArg (fun x : StatedSU m (2 ^ n) F => (x : GL (Fin m) F).val) hG
  simpa using h

private theorem borel86_ud_adjM_eq (h : UnitaryFieldData 2 n F) {G : StatedSU m (2 ^ n) F}
    (hG : G * G = 1) :
    adjM h.bar (G : GL (Fin m) F).val = (G : GL (Fin m) F).val := by
  have hval := borel86_ud_val_mul_self hG
  have h1 := adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply G.2
  calc adjM h.bar (G : GL (Fin m) F).val
      = adjM h.bar (G : GL (Fin m) F).val *
          ((G : GL (Fin m) F).val * (G : GL (Fin m) F).val) := by rw [hval, mul_one]
    _ = (adjM h.bar (G : GL (Fin m) F).val * (G : GL (Fin m) F).val) *
          (G : GL (Fin m) F).val := by rw [mul_assoc]
    _ = (G : GL (Fin m) F).val := by rw [h1, one_mul]

private theorem borel86_ud_one_le_of_ne_zero {u : Fin m → F} (hu : u ≠ 0) : 1 ≤ m := by
  by_contra h
  have hm0 : m = 0 := by omega
  subst hm0
  exact hu (funext fun i => i.elim0)

private theorem borel86_ud_one_add_sq (h : UnitaryFieldData 2 n F) (hm : 1 ≤ m) {u : Fin m → F}
    (huu : hform h.bar u u = 0) {b : F} :
    (1 + b • vecMulVec u (h.bar ∘ u)) * (1 + b • vecMulVec u (h.bar ∘ u)) = 1 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  haveI := h.charP
  have hW2 : vecMulVec u (h.bar ∘ u) * vecMulVec u (h.bar ∘ u) = 0 :=
    CFSG.ComponentClassification.RankTwoClassical.URigid.vecMulVec_mul_self h huu
  have hc2 : (b • vecMulVec u (h.bar ∘ u)) * (b • vecMulVec u (h.bar ∘ u)) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hW2, smul_zero, smul_zero]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hc2, add_zero, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

private theorem borel86_ud_pow_two_pow_add_one {G : Type*} [Group G] {g : G} (hg : g ^ 2 = 1)
    {n : ℕ} (hn : 1 ≤ n) : g ^ (2 ^ n + 1) = g := by
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ']; simp
  rw [pow_succ, h2n, pow_mul, hg, one_pow, one_mul]

theorem borel86_ud_exists_lift (h : UnitaryFieldData 2 n F) (hm : 1 ≤ m)
    {g : StatedProj (StatedSU m (2 ^ n) F)} (hg : g * g = 1) :
    ∃ G : StatedSU m (2 ^ n) F,
      (QuotientGroup.mk G : StatedProj (StatedSU m (2 ^ n) F)) = g ∧ G * G = 1 := by
  obtain ⟨G₁, rfl⟩ := QuotientGroup.mk_surjective g
  have hmk : (QuotientGroup.mk (G₁ * G₁) : StatedProj (StatedSU m (2 ^ n) F)) = 1 := by
    rw [QuotientGroup.mk_mul, hg]
  have hmem : G₁ * G₁ ∈ (StatedScalars (Fin m) F).subgroupOf (StatedSU m (2 ^ n) F) :=
    (QuotientGroup.eq_one_iff (G₁ * G₁)).mp hmk
  have hmem' : ((G₁ * G₁ : StatedSU m (2 ^ n) F) : GL (Fin m) F) ∈
      (GeneralLinearGroup.scalar (Fin m)).range := hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem'
  have hcSU : c ^ (2 ^ n + 1) = 1 :=
    ((CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := n) (n := m) Nat.prime_two
      h.card_eq_sq hm c).mp (by rw [hc]; exact (G₁ * G₁).2)).2
  have hg2 : (QuotientGroup.mk G₁ : StatedProj (StatedSU m (2 ^ n) F)) ^ 2 = 1 := by
    rw [pow_two]; exact hg
  have hpow2 : (QuotientGroup.mk G₁ : StatedProj (StatedSU m (2 ^ n) F)) ^ (2 ^ n + 1) =
      QuotientGroup.mk G₁ :=
    borel86_ud_pow_two_pow_add_one hg2 h.one_le
  refine ⟨G₁ ^ (2 ^ n + 1), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, hpow2]
  · apply Subtype.ext
    change ((G₁ : GL (Fin m) F) ^ (2 ^ n + 1) * (G₁ : GL (Fin m) F) ^ (2 ^ n + 1)) = 1
    have hmulpow : (G₁ : GL (Fin m) F) ^ (2 ^ n + 1) * (G₁ : GL (Fin m) F) ^ (2 ^ n + 1) =
        ((G₁ : GL (Fin m) F) * (G₁ : GL (Fin m) F)) ^ (2 ^ n + 1) := by
      rw [← pow_add, ← pow_two, ← pow_mul, two_mul]
    rw [hmulpow, ← Subgroup.coe_mul, ← hc, ← map_pow, hcSU, map_one]

private theorem borel86_ud_conj_val (h : UnitaryFieldData 2 n F) {σ : F ≃+* F}
    {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    {u : Fin m → F} {b : F} {N : StatedSU m (2 ^ n) F}
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u)) :
    (A * glAut σ (N : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
      1 + σ b • vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))
        (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))) := by
  have hAinv : (A⁻¹ : GL (Fin m) F).val =
      ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ := by
    calc (A⁻¹ : GL (Fin m) F).val
        = ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ *
            (A : GL (Fin m) F).val * (A⁻¹ : GL (Fin m) F).val := by rw [hA, one_mul]
      _ = ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ *
            ((A : GL (Fin m) F).val * (A⁻¹ : GL (Fin m) F).val) := by rw [mul_assoc]
      _ = ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hAmulT : (A : Matrix (Fin m) (Fin m) F) *
      ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ = 1 := by
    rw [← hAinv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hWmap : (vecMulVec u (h.bar ∘ u)).map σ =
      vecMulVec (σ ∘ u) (σ ∘ (h.bar ∘ u)) := by
    ext i j
    simp [Matrix.map_apply, vecMulVec_apply]
  have hσbar : σ ∘ (h.bar ∘ u) = h.bar ∘ (σ ∘ u) := by
    funext i
    simp only [Function.comp_apply]
    rw [h.bar_apply, map_pow, h.bar_apply]
  have hmapN : ((N : GL (Fin m) F).val.map σ) =
      1 + σ b • vecMulVec (σ ∘ u) (σ ∘ (h.bar ∘ u)) := by
    rw [hN, Matrix.map_add σ (fun a b => map_add σ a b),
      Matrix.map_one σ (map_zero σ) (map_one σ),
      Matrix.map_smul' σ b (vecMulVec u (h.bar ∘ u)) (fun a b => map_mul σ a b), hWmap]
  have hmapmul : (A : Matrix (Fin m) (Fin m) F).map h.bar *ᵥ (h.bar ∘ (σ ∘ u)) =
      h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) := by
    funext i
    exact (RingHom.map_mulVec h.bar (A : Matrix (Fin m) (Fin m) F) (σ ∘ u) i).symm
  have key : (A : Matrix (Fin m) (Fin m) F) * vecMulVec (σ ∘ u) (σ ∘ (h.bar ∘ u)) *
      ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ =
      vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))
        (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))) := by
    rw [hσbar, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hmapmul]
  have hcoe : (A * glAut σ (N : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
      (A : Matrix (Fin m) (Fin m) F) * ((N : GL (Fin m) F).val.map σ) *
        ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ := by
    rw [Units.val_mul, Units.val_mul,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, hAinv]
  rw [hcoe, hmapN, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul,
    Matrix.smul_mul, hAmulT, key]

theorem borel86_ud_fix_iff (h : UnitaryFieldData 2 n F) {σ : F ≃+* F} {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    {α : MulAut (StatedProj (StatedSU m (2 ^ n) F))}
    (hα : ∀ g : StatedSU m (2 ^ n) F,
      ∃ hg : A * glAut σ (g : GL (Fin m) F) * A⁻¹ ∈ StatedSU m (2 ^ n) F,
        α (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    {u : Fin m → F} (hu : u ≠ 0) (huu : hform h.bar u u = 0) {b : F} (hb0 : b ≠ 0)
    {N : StatedSU m (2 ^ n) F} (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u)) :
    α (QuotientGroup.mk N) = QuotientGroup.mk N ↔
      ∃ κ : F, (A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u) = κ • u ∧ σ b * (h.bar κ * κ) = b := by
  haveI := h.charP
  have hm : 1 ≤ m := borel86_ud_one_le_of_ne_zero hu
  have hN2 : N * N = 1 := mul_self_eq_one_of_val hN (borel86_ud_one_add_sq h hm huu (b := b))
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra hc
    rw [not_exists] at hc
    exact hu (funext fun i => not_not.mp (hc i))
  have hbaruj : h.bar (u j) ≠ 0 := fun h0 => hj ((h.bar_eq_zero_iff).mp h0)
  have hW0 : vecMulVec u (h.bar ∘ u) ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun h0 j) j
    simp only [vecMulVec_apply, Function.comp, Matrix.zero_apply] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hj h2
    · exact hbaruj h2
  have hVvec : ∀ κ : F, vecMulVec (κ • u) (h.bar ∘ (κ • u)) =
      (h.bar κ * κ) • vecMulVec u (h.bar ∘ u) := by
    intro κ
    ext i j'
    simp only [vecMulVec_apply, Function.comp_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      map_mul]
    ring
  constructor
  · intro hfix
    obtain ⟨hg, hαN⟩ := hα N
    have hπeq : (QuotientGroup.mk (⟨A * glAut σ (N : GL (Fin m) F) * A⁻¹, hg⟩ :
        StatedSU m (2 ^ n) F) : StatedProj (StatedSU m (2 ^ n) F)) = QuotientGroup.mk N := by
      rw [← hαN, hfix]
    have hsqGL : (A * glAut σ (N : GL (Fin m) F) * A⁻¹) *
        (A * glAut σ (N : GL (Fin m) F) * A⁻¹) = 1 := by
      have hNGL : (N : GL (Fin m) F) * (N : GL (Fin m) F) = 1 := by
        have h1 := congrArg (fun y : StatedSU m (2 ^ n) F => (y : GL (Fin m) F)) hN2
        simpa using h1
      calc (A * glAut σ (N : GL (Fin m) F) * A⁻¹) *
              (A * glAut σ (N : GL (Fin m) F) * A⁻¹)
          = A * (glAut σ (N : GL (Fin m) F) * glAut σ (N : GL (Fin m) F)) * A⁻¹ := by group
        _ = A * glAut σ ((N : GL (Fin m) F) * (N : GL (Fin m) F)) * A⁻¹ := by rw [← map_mul]
        _ = A * 1 * A⁻¹ := by rw [hNGL, map_one]
        _ = 1 := by group
    have hsq : (⟨A * glAut σ (N : GL (Fin m) F) * A⁻¹, hg⟩ : StatedSU m (2 ^ n) F) *
        ⟨A * glAut σ (N : GL (Fin m) F) * A⁻¹, hg⟩ = 1 := Subtype.ext hsqGL
    have heq := eq_of_uProj_eq_of_mul_self hm hπeq hsq hN2
    have heqval : (A * glAut σ (N : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
        (N : GL (Fin m) F).val :=
      congrArg (fun y : GL (Fin m) F => (y : Matrix (Fin m) (Fin m) F))
        (congrArg (fun y : StatedSU m (2 ^ n) F => (y : GL (Fin m) F)) heq)
    have hV : σ b • vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))
        (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))) =
        b • vecMulVec u (h.bar ∘ u) := by
      have h1 : 1 + σ b • vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))
              (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))) =
          1 + b • vecMulVec u (h.bar ∘ u) := by
        calc 1 + σ b • vecMulVec ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u))
                (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)))
            = (A * glAut σ (N : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val :=
              (borel86_ud_conj_val h hA hN).symm
          _ = (N : GL (Fin m) F).val := heqval
          _ = 1 + b • vecMulVec u (h.bar ∘ u) := hN
      exact add_left_cancel h1
    have hentry : ∀ i j', σ b * (((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) i *
        h.bar (((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) j')) =
        b * (u i * h.bar (u j')) := by
      intro i j'
      have h1 := congrFun (congrFun hV i) j'
      simpa [Matrix.smul_apply, Matrix.vecMulVec_apply, Function.comp, mul_assoc] using h1
    have hxbar : ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) j *
        h.bar (((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) j) ≠ 0 := by
      intro h0
      have hjj := hentry j j
      rw [h0, mul_zero] at hjj
      exact (mul_ne_zero hb0 (mul_ne_zero hj hbaruj)) hjj.symm
    have hxj : ((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) j ≠ 0 :=
      fun h0 => hxbar (by rw [h0, map_zero, mul_zero])
    have hbarxj : h.bar (((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) j) ≠ 0 :=
      fun h0 => hxj ((h.bar_eq_zero_iff).mp h0)
    have hden : σ b * h.bar (((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) j) ≠ 0 :=
      mul_ne_zero (fun h0 => hb0 (σ.injective (h0.trans (map_zero σ).symm))) hbarxj
    set kap : F := b * h.bar (u j) /
        (σ b * h.bar (((A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u)) j)) with hkap
    have hxκ : (A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u) = kap • u := by
      funext i
      have hi := hentry i j
      rw [hkap, Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hden]
      linear_combination hi
    refine ⟨kap, hxκ, ?_⟩
    have hV' : σ b • vecMulVec (kap • u) (h.bar ∘ (kap • u)) =
        b • vecMulVec u (h.bar ∘ u) := by
      rw [← hxκ]; exact hV
    have hV'' : (σ b * (h.bar kap * kap)) • vecMulVec u (h.bar ∘ u) =
        b • vecMulVec u (h.bar ∘ u) := by
      rw [hVvec kap, smul_smul (σ b) (h.bar kap * kap)
        (vecMulVec u (h.bar ∘ u))] at hV'
      exact hV'
    have h0 : (σ b * (h.bar kap * kap) - b) • vecMulVec u (h.bar ∘ u) = 0 := by
      rw [sub_smul, hV'', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hW0)
  · rintro ⟨κ, hxκ, hbκ⟩
    obtain ⟨hg, hαN⟩ := hα N
    have hconj : (A * glAut σ (N : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
        1 + b • vecMulVec u (h.bar ∘ u) := by
      have hcv := borel86_ud_conj_val (σ := σ) h hA hN
      rw [hxκ, hVvec κ, smul_smul (σ b) (h.bar κ * κ)
        (vecMulVec u (h.bar ∘ u)), hbκ] at hcv
      exact hcv
    have heq : (⟨A * glAut σ (N : GL (Fin m) F) * A⁻¹, hg⟩ : StatedSU m (2 ^ n) F) = N := by
      apply Subtype.ext
      apply Units.ext
      change (A * glAut σ (N : GL (Fin m) F) * A⁻¹ : GL (Fin m) F).val =
        (N : GL (Fin m) F).val
      rw [hconj, hN]
    rw [hαN, heq]

theorem borel86_ud_commute_iff (h : UnitaryFieldData 2 n F) {G : StatedSU m (2 ^ n) F}
    (hG : G * G = 1) {u : Fin m → F} (hu : u ≠ 0) (huu : hform h.bar u u = 0) {b : F}
    (hb0 : b ≠ 0) {N : StatedSU m (2 ^ n) F}
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u)) :
    (QuotientGroup.mk G * QuotientGroup.mk N : StatedProj (StatedSU m (2 ^ n) F)) =
        QuotientGroup.mk N * QuotientGroup.mk G ↔
      (G : GL (Fin m) F).val *ᵥ u = u := by
  haveI := h.charP
  have hm : 1 ≤ m := borel86_ud_one_le_of_ne_zero hu
  have hN2 : N * N = 1 := mul_self_eq_one_of_val hN (borel86_ud_one_add_sq h hm huu (b := b))
  constructor
  · intro hcomm
    have hGN : G * N = N * G := commute_of_uProj_commute hm hN2 hcomm
    have hmat : (G : GL (Fin m) F).val * (N : GL (Fin m) F).val =
        (N : GL (Fin m) F).val * (G : GL (Fin m) F).val := by
      have h1 := congrArg (fun x : StatedSU m (2 ^ n) F => (x : GL (Fin m) F).val) hGN
      simpa using h1
    have hGW : (G : GL (Fin m) F).val * vecMulVec u (h.bar ∘ u) =
        vecMulVec u (h.bar ∘ u) * (G : GL (Fin m) F).val := by
      have h1 : (G : GL (Fin m) F).val * (1 + b • vecMulVec u (h.bar ∘ u)) =
          (1 + b • vecMulVec u (h.bar ∘ u)) * (G : GL (Fin m) F).val := by
        rw [← hN]; exact hmat
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul,
        Matrix.smul_mul] at h1
      exact smul_right_injective _ hb0 (add_left_cancel h1)
    have hpow : (G : GL (Fin m) F).val ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]; exact borel86_ud_val_mul_self hG
    exact CFSG.ComponentClassification.RankTwoClassical.URigid.mulVec_eq_of_commute_of_pow
      h hu hGW hpow
  · intro hGu
    have hGN : G * N = N * G := by
      apply Subtype.ext
      apply Units.ext
      change (G : GL (Fin m) F).val * (N : GL (Fin m) F).val =
        (N : GL (Fin m) F).val * (G : GL (Fin m) F).val
      rw [hN, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul,
        Matrix.smul_mul]
      rw [CFSG.ComponentClassification.RankTwoClassical.URigid.commute_vecMulVec_of_mulVec
        h G.2 hGu]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hGN]

theorem borel86_ud_hform_mulVec_left (h : UnitaryFieldData 2 n F) {G : StatedSU m (2 ^ n) F}
    (hG : G * G = 1) (v w : Fin m → F) :
    hform h.bar ((G : GL (Fin m) F).val *ᵥ v) w = hform h.bar v ((G : GL (Fin m) F).val *ᵥ w) := by
  rw [hform_mulVec, borel86_ud_adjM_eq h hG]

theorem borel86_ud_mulVec_add_self {G : StatedSU m (2 ^ n) F} (hG : G * G = 1) (v : Fin m → F) :
    (G : GL (Fin m) F).val *ᵥ ((G : GL (Fin m) F).val *ᵥ v + v) =
      (G : GL (Fin m) F).val *ᵥ v + v := by
  have h2 : (G : GL (Fin m) F).val *ᵥ ((G : GL (Fin m) F).val *ᵥ v) = v := by
    calc (G : GL (Fin m) F).val *ᵥ ((G : GL (Fin m) F).val *ᵥ v)
        = ((G : GL (Fin m) F).val * (G : GL (Fin m) F).val) *ᵥ v :=
          Matrix.mulVec_mulVec v (G : GL (Fin m) F).val (G : GL (Fin m) F).val
      _ = v := by rw [borel86_ud_val_mul_self hG, one_mulVec]
  rw [mulVec_add, h2, add_comm]

theorem borel86_ud_hform_add_self (h : UnitaryFieldData 2 n F) {G : StatedSU m (2 ^ n) F}
    (hG : G * G = 1) (v w : Fin m → F) :
    hform h.bar ((G : GL (Fin m) F).val *ᵥ v + v) ((G : GL (Fin m) F).val *ᵥ w + w) = 0 := by
  haveI := h.charP
  rw [hform_add_left, hform_add_right, hform_add_right,
    hform_mulVec_mulVec h G v w, borel86_ud_hform_mulVec_left h hG v w]
  have key : ∀ a b : F, (a + b) + (b + a) = 0 := by
    intro a b
    rw [show (a + b) + (b + a) = (a + a) + (b + b) by ac_rfl,
      CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  exact key _ _

theorem borel86_ud_exists_fixed_isotropic (h : UnitaryFieldData 2 n F)
    {G : StatedSU m (2 ^ n) F} (hG : G * G = 1) (hG1 : G ≠ 1) :
    ∃ a : Fin m → F, a ≠ 0 ∧ hform h.bar a a = 0 ∧ (G : GL (Fin m) F).val *ᵥ a = a ∧
      ∀ u : Fin m → F, (G : GL (Fin m) F).val *ᵥ u = u → hform h.bar a u = 0 := by
  haveI := h.charP
  have hmat_ne : (G : GL (Fin m) F).val ≠ 1 := by
    intro h1
    exact hG1 (Subtype.ext (Units.ext h1))
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin m → F, (G : GL (Fin m) F).val *ᵥ v₀ ≠ v₀ := by
    by_contra hcon
    rw [not_exists] at hcon
    exact hmat_ne (Matrix.ext_iff_mulVec.mpr fun v => by
      rw [not_not.mp (hcon v), one_mulVec])
  refine ⟨(G : GL (Fin m) F).val *ᵥ v₀ + v₀, ?_, ?_, ?_, ?_⟩
  · intro h0
    exact hv₀ (funext fun i => by
      have h1 := congrFun h0 i
      simp only [Pi.add_apply, Pi.zero_apply] at h1
      exact CharTwo.add_eq_zero.mp h1)
  · exact borel86_ud_hform_add_self h hG v₀ v₀
  · exact borel86_ud_mulVec_add_self hG v₀
  · intro u hu
    rw [hform_add_left, borel86_ud_hform_mulVec_left h hG v₀ u, hu, CharTwo.add_self_eq_zero]

end CFSG.LocalAnalysis.WeakClosure81

end
