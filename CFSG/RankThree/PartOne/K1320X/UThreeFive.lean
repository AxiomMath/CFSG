module

public import CFSG.RankThree.PartOne.K1320X.CommClause
public import CFSG.RankThree.PartOne.K1320X.U4Cover
public import CFSG.RankThree.PartOne.KF.F132Row6Qs

public section

namespace CFSG.RankThree.PartOne.K1320X

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K1320 CFSG.RankThree.PartOne.KF132
  CFSG.RankThree.PartOne.KFU
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ktLift_of_kfKt {p f : ℕ} {E : Subgroup G} {t : MulAut E} {K : Subgroup G}
    (h : KFKt p E f t K) : KtLift p E t K :=
  ⟨h.1, (S13K.isQuasisimple_and_center_of_model_psl_two h.2.2.1).1,
    (S13K.isQuasisimple_and_center_of_model_psl_two h.2.2.1).2, h.2.2.2.2.1, h.2.2.2.2.2⟩

omit [Finite G] in
theorem kfKt_of_conj {p f : ℕ} {E : Subgroup G} {t : MulAut E} {K : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (h : KFKt p E f (conjAut E w hw * t * (conjAut E w hw)⁻¹) K) : KFKt p E f t (conjBy w⁻¹ K) := by
  have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
  have h2 := kfKt_conj h hw'
  rw [Equivariance.conjAut_inv hw] at h2
  simpa [mul_assoc] using h2

omit [Finite G] in
theorem sup_model_of_conj {p : ℕ} {E : Subgroup G} {t₂ r₁ : MulAut E} {w x : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (h2 : conjAut E w hw * t₂ * (conjAut E w hw)⁻¹ = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹)
    {Kt : Subgroup G} {tag : LowTwoRank.StatedLieTag} {n f : ℕ}
    (hmod : StatedClassicalModel ↥(kZero p E r₁ ⊔ Kt) tag n 2 f) :
    StatedClassicalModel ↥(kZero p E t₂ ⊔ conjBy w⁻¹ (conjBy x Kt)) tag n 2 f := by
  have h1 : kZero p E t₂ = conjBy w⁻¹ (conjBy x (kZero p E r₁)) := by
    have := congrArg (kZero p E) h2
    rw [kZero_conj p t₂ hw, kZero_conj p r₁ hxE] at this
    rw [← this, Equivariance.conjBy_inv_conjBy]
  have h3 : kZero p E t₂ ⊔ conjBy w⁻¹ (conjBy x Kt) =
      conjBy w⁻¹ (conjBy x (kZero p E r₁ ⊔ Kt)) := by
    rw [h1, conjBy_sup, conjBy_sup]
  rw [h3]
  exact (Equivariance.statedClassicalModel_conjBy_iff w⁻¹ _).mpr
    ((Equivariance.statedClassicalModel_conjBy_iff x _).mpr hmod)

theorem kf1320UThreeAt_five
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two) (hDistX : KFCommDistinctX)
    (hdist : RowModelsDistinct) : KF1320UThreeAt 5 := by
  intro G _ _ p A c L E f h hF hF13 hT hf1 hpf hmodel hEA _ hweyl t₁ t₂ t₃ hch K₂ hK₂ hmod2
  obtain ⟨eX⟩ := hweyl
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hf3 := three_le_of_dvd_two_pow_sub_one hp5 hf1 hpf
  obtain ⟨z, hz⟩ := exists_inverter h hF13 eX
  have hn8 : ¬ ∃ f' : ℕ, 1 ≤ f' ∧ p ∣ 2 ^ f' + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f' :=
    fun ⟨_, _, _, h4⟩ => not_row8_of_psu hdist (Or.inr rfl) hmodel h4
  obtain ⟨w, hw, hs₁, hs₁L, hs₂, hs₂L, hord⟩ := chain_conj_into_L hp hch
  obtain ⟨K, hKf, hKfin, hchar, hK, ε, hε, r₀, r₁, Kt, hr₀s, hr₀L, hr₁s, hr₁L, -, hex₀, hKF₁, hKt,
    himgKt, himg₁, hpairs⟩ := row6_frame_kt hGA h hF hF13 hEA hf1 hpf hmodel
  have hq : IsCentralPQuot p (suQ 5 hK) := isCentralPQuot_suQ hp hp2 (by norm_num) hpf hf1 hK
  obtain ⟨x, -, hxE, hx⟩ := hpairs _ hs₁ hs₁L _ hs₂ hs₂L hord
  rcases hx with ⟨h1, h2⟩ | ⟨-, h2⟩
  ·
    have hA2 : KFAt p E (2 * f) (conjAut E w hw * t₂ * (conjAut E w hw)⁻¹) := h2 ▸ hKF₁.conj hxE
    have hKA₂ : KFAt p E (2 * f) t₂ := KFAt.of_conj hw hA2
    obtain ⟨w₃, hw₃, ht₃⟩ := chain_t₃_conj hch
    have hKA₃ : KFAt p E (2 * f) t₃ := by rw [ht₃]; exact hKA₂.conj hw₃
    have hKs₁ : KFKt p E f (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) (conjBy x Kt) :=
      h1 ▸ kfKt_conj hKt hxE
    have hk₁ : KFKt p E f t₁ (conjBy w⁻¹ (conjBy x Kt)) := kfKt_of_conj hw hKs₁
    have hexc₁ : kExceptional p (kZero p E (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹)) f :=
      h1 ▸ kExceptional_conj_of_normalizer hex₀ hxE
    have hq0 := kf132Row6_exc_quasisimple hGA h hF hF13 hEA hf1 hpf hmodel _ hs₁ hs₁L hexc₁
    have hK₁ : KtLift p E (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹)
        (conjBy w (conjBy w⁻¹ (conjBy x Kt))) := by
      rw [Equivariance.conjBy_conjBy_inv]
      exact ktLift_of_kfKt hKs₁
    have hcomm := chain_comm_clauseX hS h133 hDistX h hF hF13 hT hEA hn8 hz hch hw hs₁ hs₁L hK₁ hq0
      hKA₃ (hpf.trans (S13K.two_pow_sub_one_dvd_mul f 2))
    have hL3 := chain_pair_L3 hGA hS h133 h hF hF13 hT hEA hn8 hz hch hKA₂
      (PAIR22.pairLift_of_kfAt hKA₃)
    have hUr := row6_sup_model hGA hF13 (by omega : 2 ≤ f) hK ε hε hq hr₀s hr₀L hr₁s hr₁L hKF₁ hKt
      himgKt himg₁
    have hU4 := sup_model_of_conj hw hxE h2 hUr
    have hk₂ := kfKt_of_kfAt hKA₂
    have hk₃ := kfKt_of_kfAt hKA₃
    obtain ⟨hI, hEI, htor⟩ := Sec1320.package hp hp5 h.E_elem hF13.irreducible hch hk₁ hk₂ hk₃
    have hdE : RefFacts.ElemData p E :=
      RefFacts.ElemData.of_isElementaryAbelian hp (by omega) h.E_elem
    have hstd := not_le_centralizer_swap hdE hch hk₁ hk₂
    have h₃I : kZero p E t₃ ≤ lieGenerated p E := by rw [hI]; exact le_sup_left.trans le_sup_left
    have h₂I : kZero p E t₂ ≤ lieGenerated p E := by rw [hI]; exact le_sup_right.trans le_sup_left
    have h₁I : conjBy w⁻¹ (conjBy x Kt) ≤ lieGenerated p E := by rw [hI]; exact le_sup_right
    have hCT := extCurtisTitsCThreeU_ambient CFSG.RankThree.PartTwo.CTU6.extCurtisTitsCThreeU
      (by omega : 2 ≤ f) hp hpf h.E_elem hEI h₃I h₂I h₁I hI.symm hKA₃.2.1 hKA₂.2.1 hk₁.2.2.1
      (Sec1320.commuting_symm hcomm) hL3 hU4 htor hstd
    have hperf : Group.IsPerfect ↥(lieGenerated p E) := by
      rw [hI]
      exact isPerfect_sup_three (S13K.isQuasisimple_of_model_psl_two hKA₃.2.1).1
        (S13K.isQuasisimple_of_model_psl_two hKA₂.2.1).1
        (S13K.isQuasisimple_of_model_psl_two hk₁.2.2.1).1
    exact false_of_psu_six hGA hperf hf3 hCT h.setup.2.2.2.2.1
  ·
    have hEx₂ : kExceptional p (kZero p E (conjAut E w hw * t₂ * (conjAut E w hw)⁻¹)) f :=
      h2 ▸ kExceptional_conj_of_normalizer hex₀ hxE
    rw [kZero_conj p t₂ hw] at hEx₂
    have hEx' : kExceptional p (kZero p E t₂) f :=
      (Equivariance.kExceptional_conjBy_iff p f w (kZero p E t₂)).1 hEx₂
    obtain ⟨-, hmodK, -⟩ := hK₂.1 f hEx'
    have := psl_two_degree_eq hmodK hmod2
    omega

end CFSG.RankThree.PartOne.K1320X
