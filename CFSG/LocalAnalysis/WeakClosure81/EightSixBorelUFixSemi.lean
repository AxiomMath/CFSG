module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofHermitian
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUDict
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM
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
open CFSG.ComponentClassification.RankTwoClassical (hform hform_add_left hform_add_right
  hform_smul_left hform_smul_right hform_comm hform_mulVec_mulVec eq_zero_of_hform_left
  hform_single_one_left hform_single_add_single exists_statedSU_mulVec_eq exists_statedSU_eq_of_bar)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)

variable {m n : ℕ} {F : Type} [Field F] [Finite F]

private lemma borel86_ufs_hform_add_smul (h : UnitaryFieldData 2 n F) {a b : Fin m → F} (l : F)
    (haa : hform h.bar a a = 0) (hbb : hform h.bar b b = 0) (hab : hform h.bar a b = 0) :
    hform h.bar (a + l • b) (a + l • b) = 0 := by
  rw [hform_add_left, hform_add_right, hform_add_right]
  rw [hform_smul_right, hform_smul_left, hform_smul_left, hform_smul_right]
  rw [haa, hform_comm h.bar_bar a b, hab, hbb, map_zero]
  simp

theorem borel86_ufs_refl_or_bar (h : UnitaryFieldData 2 n F) {σ : F ≃+* F} {A : GL (Fin m) F}
    {u : Fin m → F} (hu : u ≠ 0)
    (hE : ∀ b : F, b ≠ 0 → h.bar b = b →
      ∃ κ : F, (A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u) = κ • u ∧ σ b * (h.bar κ * κ) = b) :
    σ = RingEquiv.refl F ∨ ∀ c, σ c = h.bar c := by
  obtain ⟨κ₁, hκ₁, h1⟩ := hE 1 one_ne_zero (map_one h.bar)
  have hκ₁bar : h.bar κ₁ * κ₁ = 1 := by simpa using h1
  refine CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.ringEquiv_eq_refl_or_bar_of_fixes h ?_
  intro c hc
  rw [h.mem_fixedField] at hc
  by_cases hc0 : c = 0
  · subst hc0
    exact map_zero σ
  · obtain ⟨κ, hκ, hb⟩ := hE c hc0 hc
    have hκeq : κ = κ₁ := by
      have huu : κ • u = κ₁ • u := by rw [← hκ, hκ₁]
      exact smul_left_injective F hu huu
    rw [hκeq, hκ₁bar, mul_one] at hb
    exact hb

theorem borel86_ufs_exists_pair (h : UnitaryFieldData 2 n F) (hm : 4 ≤ m)
    {G : StatedSU m (2 ^ n) F} (hG : G * G = 1) (hG1 : G ≠ 1) :
    ∃ a b : Fin m → F, (G : GL (Fin m) F).val *ᵥ a = a ∧ (G : GL (Fin m) F).val *ᵥ b = b ∧
      hform h.bar a a = 0 ∧ hform h.bar b b = 0 ∧ hform h.bar a b = 0 ∧
      ∀ x y : F, x • a + y • b = 0 → x = 0 ∧ y = 0 := by
  haveI := h.charP
  obtain ⟨a, ha0, haa, hGa, hperp⟩ := borel86_ud_exists_fixed_isotropic h hG hG1
  by_cases hcase : ∃ x : Fin m → F, ∀ μ : F, (G : GL (Fin m) F).val *ᵥ x + x ≠ μ • a
  · obtain ⟨x, hx⟩ := hcase
    refine ⟨a, (G : GL (Fin m) F).val *ᵥ x + x, hGa, ?_, haa,
      borel86_ud_hform_add_self h hG x x, hperp _ (borel86_ud_mulVec_add_self hG x), ?_⟩
    · exact borel86_ud_mulVec_add_self hG x
    · intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨smul_left_injective F ha0 (by simp [hst]), rfl⟩
      · exfalso
        apply hx (-(t⁻¹ * s))
        calc (G : GL (Fin m) F).val *ᵥ x + x
            = t⁻¹ • (t • ((G : GL (Fin m) F).val *ᵥ x + x)) :=
              (inv_smul_smul₀ ht _).symm
          _ = t⁻¹ • (-(s • a)) := by rw [eq_neg_of_add_eq_zero_right hst]
          _ = (-(t⁻¹ * s)) • a := by simp [smul_neg, smul_smul, neg_smul]
  · have hcase' : ∀ x : Fin m → F, ∃ μ : F, (G : GL (Fin m) F).val *ᵥ x + x = μ • a := by
      intro x
      by_contra hx
      exact hcase ⟨x, fun μ hμ => hx ⟨μ, hμ⟩⟩
    have hfix : ∀ w : Fin m → F, hform h.bar a w = 0 →
        (G : GL (Fin m) F).val *ᵥ w = w := by
      intro w haw
      have hzero : (G : GL (Fin m) F).val *ᵥ w + w = 0 := by
        apply eq_zero_of_hform_left (σ := h.bar)
        intro x
        obtain ⟨μ, hμ⟩ := hcase' x
        calc hform h.bar x ((G : GL (Fin m) F).val *ᵥ w + w)
            = hform h.bar x ((G : GL (Fin m) F).val *ᵥ w) + hform h.bar x w :=
              hform_add_right x _ _
          _ = hform h.bar ((G : GL (Fin m) F).val *ᵥ x) w + hform h.bar x w := by
              rw [borel86_ud_hform_mulVec_left h hG x w]
          _ = hform h.bar ((G : GL (Fin m) F).val *ᵥ x + x) w :=
              (hform_add_left ((G : GL (Fin m) F).val *ᵥ x) x w).symm
          _ = hform h.bar (μ • a) w := by rw [hμ]
          _ = h.bar μ * hform h.bar a w := hform_smul_left μ a w
          _ = 0 := by rw [haw, mul_zero]
      funext i
      exact CharTwo.add_eq_zero.mp (congrFun hzero i)
    let idx : Fin 4 → Fin m := Fin.castLE hm
    have hidx : Function.Injective idx := Fin.castLE_injective hm
    have hne : ∀ a b : Fin 4, a ≠ b → idx a ≠ idx b := fun a b hab h => hab (hidx h)
    obtain ⟨i₀, i₁, i₂, i₃, h01, h02, h03, h12, h13, h23⟩ :
        ∃ i₀ i₁ i₂ i₃ : Fin m, i₀ ≠ i₁ ∧ i₀ ≠ i₂ ∧ i₀ ≠ i₃ ∧ i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧
          i₂ ≠ i₃ :=
      ⟨idx 0, idx 1, idx 2, idx 3, hne 0 1 (by decide), hne 0 2 (by decide),
        hne 0 3 (by decide), hne 1 2 (by decide), hne 1 3 (by decide), hne 2 3 (by decide)⟩
    set e : Fin m → F := Pi.single i₀ (1 : F) + Pi.single i₁ (1 : F) with he
    set e' : Fin m → F := Pi.single i₂ (1 : F) + Pi.single i₃ (1 : F) with he'
    have he0 : e ≠ 0 := by
      rw [he]
      intro h0
      have h1 := congrFun h0 i₀
      rw [Pi.add_apply, Pi.zero_apply, Pi.single_eq_same, Pi.single_eq_of_ne h01, add_zero] at h1
      exact one_ne_zero h1
    have hee : hform h.bar e e = 0 := by
      rw [he]
      exact hform_single_add_single h.bar h01
    have he'e' : hform h.bar e' e' = 0 := by
      rw [he']
      exact hform_single_add_single h.bar h23
    have hee' : hform h.bar e e' = 0 := by
      rw [he, he']
      simp only [hform_add_left, hform_add_right, hform_single_one_left]
      simp [Pi.single_eq_of_ne, h02, h03, h12, h13]
    obtain ⟨S, hS⟩ := exists_statedSU_mulVec_eq h (n := m) (by omega) he0 hee ha0 haa
    set b : Fin m → F := (S : GL (Fin m) F).val *ᵥ e' with hb
    have hbb : hform h.bar b b = 0 := by
      rw [hb, hform_mulVec_mulVec h S]
      exact he'e'
    have hab : hform h.bar a b = 0 := by
      rw [hb, ← hS, hform_mulVec_mulVec h S]
      exact hee'
    refine ⟨a, b, hGa, hfix b hab, haa, hbb, hab, ?_⟩
    have hSS : ((S⁻¹ : StatedSU m (2 ^ n) F) : GL (Fin m) F).val *
        (S : GL (Fin m) F).val = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    have hSinv_a : ((S⁻¹ : StatedSU m (2 ^ n) F) : GL (Fin m) F).val *ᵥ a = e := by
      rw [← hS, Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
    have hSinv_b : ((S⁻¹ : StatedSU m (2 ^ n) F) : GL (Fin m) F).val *ᵥ b = e' := by
      rw [hb, Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
    intro x y hxy
    have h0 : x • e + y • e' = 0 := by
      have h1 := congrArg (fun v => ((S⁻¹ : StatedSU m (2 ^ n) F) : GL (Fin m) F).val *ᵥ v)
        hxy
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_zero,
        hSinv_a, hSinv_b] at h1
      exact h1
    have he_i₀ : e i₀ = 1 := by
      rw [he, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h01, add_zero]
    have he'_i₀ : e' i₀ = 0 := by
      rw [he', Pi.add_apply, Pi.single_eq_of_ne h02, Pi.single_eq_of_ne h03, add_zero]
    have he_i₂ : e i₂ = 0 := by
      rw [he, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm h02), Pi.single_eq_of_ne (Ne.symm h12),
        add_zero]
    have he'_i₂ : e' i₂ = 1 := by
      rw [he', Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h23, add_zero]
    have hx0 : x = 0 := by
      have h1 := congrFun h0 i₀
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, smul_eq_mul,
        he_i₀, he'_i₀, mul_one, mul_zero, add_zero] at h1
      exact h1
    have hy0 : y = 0 := by
      have h1 := congrFun h0 i₂
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, smul_eq_mul,
        he_i₂, he'_i₂, mul_zero, mul_one, zero_add] at h1
      exact h1
    exact ⟨hx0, hy0⟩

theorem borel86_ufs_false_of_pencil (h : UnitaryFieldData 2 n F) (A : GL (Fin m) F)
    {a b : Fin m → F} (hab : ∀ x y : F, x • a + y • b = 0 → x = 0 ∧ y = 0)
    (hb : ∃ κ : F, (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ b) = κ • b)
    (hl : ∀ l : F, ∃ κ : F,
      (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ (a + l • b)) = κ • (a + l • b)) :
    False := by
  obtain ⟨κb, hκb⟩ := hb
  obtain ⟨κ₀, hκ₀⟩ := hl 0
  have hκ₀' : (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ a) = κ₀ • a := by
    simpa using hκ₀
  have hsplit : ∀ l : F, h.bar ∘ (a + l • b) = (h.bar ∘ a) + h.bar l • (h.bar ∘ b) := by
    intro l
    ext i
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  have hAbar : ∀ l : F, (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ (a + l • b)) =
      κ₀ • a + (h.bar l * κb) • b := by
    intro l
    rw [hsplit l, Matrix.mulVec_add, Matrix.mulVec_smul, hκ₀', hκb, smul_smul]
  have hrel : ∀ l : F, κ₀ * l = h.bar l * κb := by
    intro l
    obtain ⟨κl, hκl⟩ := hl l
    have h1 : κl • a + (κl * l) • b = κ₀ • a + (h.bar l * κb) • b := by
      rw [← smul_smul, ← smul_add, ← hκl, hAbar l]
    have h2 : (κl - κ₀) • a + (κl * l - h.bar l * κb) • b = 0 := by
      rw [sub_smul, sub_smul]
      rw [show κl • a - κ₀ • a + ((κl * l) • b - (h.bar l * κb) • b) =
          (κl • a + (κl * l) • b) - (κ₀ • a + (h.bar l * κb) • b) by abel]
      rw [h1, sub_self]
    obtain ⟨h3, h4⟩ := hab (κl - κ₀) (κl * l - h.bar l * κb) h2
    rw [sub_eq_zero.mp h3] at h4
    exact sub_eq_zero.mp h4
  have hκbκ₀ : κb = κ₀ := by simpa using (hrel 1).symm
  have hκ₀_ne : κ₀ ≠ 0 := by
    intro h0
    have hza : h.bar ∘ a = 0 := by
      have h : (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ a) = 0 := by
        rw [hκ₀', h0, zero_smul]
      have h2 := congrArg
        (fun v => ((A⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ v) h
      rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have ha0 : a = 0 := by
      funext i
      have h2 := congrArg h.bar (congrFun hza i)
      simpa [Function.comp_apply, h.bar_bar] using h2
    exact one_ne_zero (hab 1 0 (by rw [one_smul, zero_smul, ha0, add_zero])).1
  have hfix : ∀ l : F, h.bar l = l := by
    intro l
    have h1 := hrel l
    rw [hκbκ₀] at h1
    have h2 : (h.bar l - l) * κ₀ = 0 := by
      rw [sub_mul, mul_comm l κ₀, ← h1, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hκ₀_ne)
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact hc (hfix c)

theorem borel86_ufs_false_of_bar (h : UnitaryFieldData 2 n F) (hm : 4 ≤ m)
    {G : StatedSU m (2 ^ n) F} (hG : G * G = 1) (hG1 : G ≠ 1) (A : GL (Fin m) F)
    (hE : ∀ u : Fin m → F, u ≠ 0 → hform h.bar u u = 0 → (G : GL (Fin m) F).val *ᵥ u = u →
      ∃ κ : F, (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ u) = κ • u) :
    False := by
  obtain ⟨a, b, hGa, hGb, haa, hbb, hab, hind⟩ := borel86_ufs_exists_pair h hm hG hG1
  have hb0 : b ≠ 0 := by
    intro hb
    exact one_ne_zero (hind 0 1 (by rw [zero_smul, one_smul, hb, add_zero])).2
  refine borel86_ufs_false_of_pencil h A hind (hE b hb0 hbb hGb) ?_
  intro l
  have hv0 : a + l • b ≠ 0 := by
    intro hv
    exact one_ne_zero (hind 1 l (by simpa using hv)).1
  have hviso : hform h.bar (a + l • b) (a + l • b) = 0 :=
    borel86_ufs_hform_add_smul h l haa hbb hab
  have hGv : (G : GL (Fin m) F).val *ᵥ (a + l • b) = a + l • b := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hGa, hGb]
  exact hE (a + l • b) hv0 hviso hGv

theorem borel86_ufs_mem_range_conj_of_refl (h : UnitaryFieldData 2 n F) {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    {α : MulAut (StatedProj (StatedSU m (2 ^ n) F))}
    (hα : ∀ g : StatedSU m (2 ^ n) F,
      ∃ hg : A * glAut (RingEquiv.refl F) (g : GL (Fin m) F) * A⁻¹ ∈ StatedSU m (2 ^ n) F,
        α (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (hα2 : α * α = 1) :
    α ∈ (MulAut.conj : StatedProj (StatedSU m (2 ^ n) F) →*
      MulAut (StatedProj (StatedSU m (2 ^ n) F))).range := by
  have hglAut_refl : ∀ g : GL (Fin m) F, glAut (RingEquiv.refl F) g = g := by
    intro g
    apply Units.ext
    ext i j
    rfl
  have hdetA : h.bar (A : Matrix (Fin m) (Fin m) F).det * (A : Matrix (Fin m) (Fin m) F).det =
      1 := by
    have hh := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hh
    rwa [show ((A : Matrix (Fin m) (Fin m) F).map h.bar).det =
        h.bar (A : Matrix (Fin m) (Fin m) F).det from
      (RingHom.map_det h.bar (A : Matrix (Fin m) (Fin m) F)).symm] at hh
  set M : Matrix (Fin m) (Fin m) F := (A : Matrix (Fin m) (Fin m) F) ^ (2 ^ n + 1) with hM
  have hMdet : M.det = 1 := by
    rw [hM, Matrix.det_pow, pow_succ, ← h.bar_apply]
    exact hdetA
  have hMu : (M.map h.bar)ᵀ * M = 1 := by
    rw [hM, Matrix.map_pow, Matrix.transpose_pow]
    exact pow_mul_pow_eq_one (2 ^ n + 1) hA
  obtain ⟨S', hS'⟩ := exists_statedSU_eq_of_bar h hMdet hMu
  have hαq : α ^ (2 ^ n) = 1 := by
    have hα2' : α ^ 2 = 1 := by rw [pow_two]; exact hα2
    refine (orderOf_dvd_iff_pow_eq_one (x := α)).mp (dvd_trans (orderOf_dvd_of_pow_eq_one hα2') ?_)
    exact ⟨2 ^ (n - 1), by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel h.one_le]⟩
  have hαq1 : α ^ (2 ^ n + 1) = α := by rw [pow_succ, hαq, one_mul]
  let u : ℕ → StatedSU m (2 ^ n) F → GL (Fin m) F :=
    fun j g => A ^ j * (g : GL (Fin m) F) * (A ^ j)⁻¹
  have hmain : ∀ j : ℕ, ∀ g : StatedSU m (2 ^ n) F,
      ∃ hg : u j g ∈ StatedSU m (2 ^ n) F,
        (α ^ j) (QuotientGroup.mk g) = QuotientGroup.mk ⟨u j g, hg⟩ := by
    intro j
    induction j with
    | zero =>
      intro g
      have hg0 : u 0 g = (g : GL (Fin m) F) := by
        simp only [u, pow_zero, one_mul, inv_one, mul_one]
      refine ⟨by rw [hg0]; exact g.2, ?_⟩
      rw [pow_zero, MulAut.one_apply]
      exact congrArg QuotientGroup.mk (Subtype.ext hg0.symm)
    | succ j ih =>
      intro g
      obtain ⟨hg, hge⟩ := ih g
      obtain ⟨hg2, hge2⟩ := hα ⟨u j g, hg⟩
      have heq : u (j + 1) g = A * u j g * A⁻¹ := by
        simp only [u, pow_succ']
        group
      have hmemb : u (j + 1) g ∈ StatedSU m (2 ^ n) F := by
        rw [heq]
        simpa only [hglAut_refl, Subtype.coe_mk] using hg2
      refine ⟨hmemb, ?_⟩
      rw [pow_succ', MulAut.mul_apply, hge, hge2]
      exact congrArg QuotientGroup.mk (by
        apply Subtype.ext
        simpa only [Subtype.coe_mk, hglAut_refl] using heq.symm)
  refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk S', ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨hg, hge⟩ := hmain (2 ^ n + 1) g
  have h1 : α (QuotientGroup.mk g) =
      QuotientGroup.mk (⟨u (2 ^ n + 1) g, hg⟩ : StatedSU m (2 ^ n) F) := by
    rw [← hαq1]
    exact hge
  have helem : (⟨u (2 ^ n + 1) g, hg⟩ : StatedSU m (2 ^ n) F) = S' * g * S'⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, u]
    rw [show (S' : GL (Fin m) F) = A ^ (2 ^ n + 1) by
      apply Units.ext
      rw [hS', Units.val_pow_eq_pow_val, hM]]
  rw [MulAut.conj_apply, h1, helem, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv]

end CFSG.LocalAnalysis.WeakClosure81

end
