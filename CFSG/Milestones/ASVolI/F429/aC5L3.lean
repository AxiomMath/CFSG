module

public import CFSG.Milestones.ASVolI.F429.aR5Gen
public import CFSG.Milestones.ASVolI.F429.Defs
public import CFSG.Milestones.ASVolI.F4L3Aut

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34 CFSG.QuasithinUnique.Setup.X7a

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem burnsideF429a_L3_dMat_one_mem_oPPrime (a : Fˣ) :
    proj 3 F (dMat 1 a) ∈
      oPPrime 2 (Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) := by
  have hdet : ∀ c : Fˣ, (!![0, (c : F); ((c⁻¹ : Fˣ) : F), 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    intro c
    rw [Matrix.det_fin_two_of, zero_mul, zero_sub, Units.mul_inv, CharTwo.neg_eq]
  let w : Fˣ → Matrix.SpecialLinearGroup (Fin 2) F := fun c => ⟨_, hdet c⟩
  have hw2 : ∀ c, w c * w c = 1 := by
    intro c
    apply Subtype.ext
    show (!![0, (c : F); ((c⁻¹ : Fˣ) : F), 0] : Matrix (Fin 2) (Fin 2) F) *
      !![0, (c : F); ((c⁻¹ : Fˣ) : F), 0] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hwd : burnsideF447_dEl a = w a * w 1 := by
    apply Subtype.ext
    show !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] =
      (!![0, (a : F); ((a⁻¹ : Fˣ) : F), 0] : Matrix (Fin 2) (Fin 2) F) *
        !![0, ((1 : Fˣ) : F); (((1 : Fˣ)⁻¹ : Fˣ) : F), 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmem : ∀ c, burnsideF447_lv (w c) ∈
      oPPrime 2 (Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) :=
    fun c => burnsideF4gU4Inv_mem_oPPrime (burnsideF447_lv_mem_normalizer_V1 (w c)) (k := 1)
      (by rw [pow_one, pow_two, ← map_mul, hw2, map_one])
  have e : proj 3 F (dMat 1 a) = burnsideF447_lv (burnsideF447_dEl a) := by
    show _ = proj 3 F (burnsideF447_blk (burnsideF447_dEl a))
    rw [burnsideF447_blk_dEl]
  rw [e, hwd, map_mul]
  exact Subgroup.mul_mem _ (hmem a) (hmem 1)

theorem burnsideF429a_L3_dMat_inv_mem_oPPrime (a : Fˣ) :
    proj 3 F (dMat a a⁻¹) ∈
      oPPrime 2 (Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) := by
  have hdet : ∀ c : Fˣ, (!![0, (c : F), 0; ((c⁻¹ : Fˣ) : F), 0, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    intro c
    simp [Matrix.det_fin_three, CharTwo.neg_eq]
  let s : Fˣ → Matrix.SpecialLinearGroup (Fin 3) F := fun c => ⟨_, hdet c⟩
  have hs2 : ∀ c, s c * s c = 1 := by
    intro c
    apply Subtype.ext
    show (!![0, (c : F), 0; ((c⁻¹ : Fˣ) : F), 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
      !![0, (c : F), 0; ((c⁻¹ : Fˣ) : F), 0, 0; 0, 0, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hsd : dMat a a⁻¹ = s a * s 1 := by
    apply Subtype.ext
    rw [coe_dMat]
    show _ = (!![0, (a : F), 0; ((a⁻¹ : Fˣ) : F), 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
      !![0, ((1 : Fˣ) : F), 0; (((1 : Fˣ)⁻¹ : Fˣ) : F), 0, 0; 0, 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  have hsN : ∀ c, proj 3 F (s c) ∈
      Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
    intro c
    rw [normalizer_V2_eq]
    exact ⟨s c, mem_Q3_one_iff.mpr ⟨by simp [s], by simp [s]⟩, rfl⟩
  have hmem : ∀ c, proj 3 F (s c) ∈
      oPPrime 2 (Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) :=
    fun c => burnsideF4gU4Inv_mem_oPPrime (hsN c) (k := 1)
      (by rw [pow_one, pow_two, ← map_mul, hs2, map_one])
  rw [hsd, map_mul]
  exact Subgroup.mul_mem _ (hmem a) (hmem 1)

theorem burnsideF429a_L3_dMat_one_inj {u a : Fˣ}
    (h : proj 3 F (dMat 1 u) = proj 3 F (dMat 1 a)) : u = a := by
  have h1 : proj 3 F (dMat (1 * 1⁻¹) (u * a⁻¹)) = 1 := by
    have : proj 3 F (dMat 1 u) * (proj 3 F (dMat 1 a))⁻¹ = 1 := by rw [h]; group
    rwa [← map_inv, dMat_inv, ← map_mul, dMat_mul] at this
  obtain ⟨c, -, h2, h3⟩ := proj_dMat_eq_one h1
  have hc1 : (c : F) = 1 := by
    rw [← h2]
    simp
  have h4 : u * a⁻¹ = 1 := Units.ext (by rw [h3, hc1, Units.val_one])
  exact mul_inv_eq_one.mp h4

end Model

section Key

theorem burnsideF429a_L3_key_of_setup {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}
    (C : burnsideF447_Ctx f Φ ρ Gp)
    (hM12 : M₁ ⊓ M₂ = Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ)
    {M : Subgroup E} {R : Subgroup (projectiveSL 3 F)}
    (hMR : M = Subgroup.normalizer ((R.map Φ : Subgroup E) : Set E)) (hR : R = V1 ∨ R = V2) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr k hk hcomm
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ C.hΦ
  haveI : Φ.range.Normal := by rw [C.hrange]; infer_instance
  have hrN : r ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) := by
    rw [← hM12]
    exact hr
  have hGM : Gp ⊓ M = (Subgroup.normalizer (R : Set (projectiveSL 3 F))).map Φ := by
    rw [hMR, ← normalizer_map_inf_range Φ C.hΦ R, C.hrange, inf_comm]
  have hL : oPPrime 2 (Gp ⊓ M) = (oPPrime 2 (Subgroup.normalizer (R : Set (projectiveSL 3 F)))).map Φ := by
    rw [hGM, burnsideF4gU4Inv_oPPrime_map C.hΦ]
  obtain ⟨u, hu, b, hb, rfl⟩ := burnsideF447_frattini C.hq C.hΦ hrN
  obtain ⟨δ, t₁, t₂, σ, hρb⟩ := burnsideF447_diag C.hq C.hΦ C.hΦρ C.hE hb.1 hb.2
  have hfixd : ∀ d ∈ oPPrime 2 (Subgroup.normalizer (R : Set (projectiveSL 3 F))), d ∈ torus3 F →
      fieldAut 3 F σ d = d := by
    intro d hdo hdT
    have hdN := map_mem_normalizer_map Φ (torus3_le_normalizer hdT)
    have hΦd : Φ d ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂) := by
      refine ⟨?_, ?_⟩
      · rw [hL]
        exact ⟨d, hdo, rfl⟩
      · rw [hM12]
        exact hdN
    have h1 := hcomm _ hΦd
    rw [hS] at h1
    have h2 : b * Φ d * b⁻¹ * (Φ d)⁻¹ ∈ (projUnitriangular 3 F).map Φ := by
      have e : b * Φ d * b⁻¹ * (Φ d)⁻¹ =
          u⁻¹ * (u * b * Φ d * (u * b)⁻¹ * (Φ d)⁻¹) * (Φ d * u * (Φ d)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) h1)
        ((Subgroup.mem_normalizer_iff.mp hdN u).mp hu)
    obtain ⟨s₁, s₂, rfl⟩ := mem_torus3.mp hdT
    have hact : ρ b (proj 3 F (dMat s₁ s₂)) = fieldAut 3 F σ (proj 3 F (dMat s₁ s₂)) := by
      rw [hρb, MulAut.mul_apply, MulAut.mul_apply, burnsideF447_fieldAut_dMat,
        MulAut.conj_apply, burnsideF447_torus_conj_fix (dP_mem_torus3 _ _) (dP_mem_torus3 _ _),
        conjAut_nuDiag_dMat]
    have h3 : ρ b (proj 3 F (dMat s₁ s₂)) * (proj 3 F (dMat s₁ s₂))⁻¹ ∈
        projUnitriangular 3 F := by
      refine (Subgroup.mem_map_iff_mem C.hΦ).mp ?_
      rw [map_mul, map_inv, C.hΦρ]
      exact h2
    have h4 : ρ b (proj 3 F (dMat s₁ s₂)) * (proj 3 F (dMat s₁ s₂))⁻¹ ∈ torus3 F := by
      rw [hact, burnsideF447_fieldAut_dMat]
      exact Subgroup.mul_mem _ (dP_mem_torus3 _ _) (Subgroup.inv_mem _ hdT)
    have h5 := burnsideF447_two_odd (isSylowTwoOf_U (F := F)).2.1 (torus3_odd (F := F)) h3 h4
    rw [← hact]
    exact mul_inv_eq_one.mp h5
  have hfix : ∀ a : Fˣ, Units.map σ.toMonoidHom a = a := by
    intro a
    rcases hR with rfl | rfl
    · have h1 := hfixd _ (burnsideF429a_L3_dMat_one_mem_oPPrime a) (dP_mem_torus3 _ _)
      rw [burnsideF447_fieldAut_dMat, map_one] at h1
      exact burnsideF429a_L3_dMat_one_inj h1
    · have h1 := hfixd _ (burnsideF429a_L3_dMat_inv_mem_oPPrime a) (dP_mem_torus3 _ _)
      rw [burnsideF447_fieldAut_dMat, map_inv] at h1
      exact burnsideF447_dMat_inj h1
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun x => ?_
    show σ x = x
    by_cases hx : x = 0
    · rw [hx, map_zero]
    · have h1 : ((Units.map σ.toMonoidHom (Units.mk0 x hx) : Fˣ) : F) = x := by
        rw [hfix]
        rfl
      simpa using h1
  have hconjL : ∀ p : projectiveSL 3 F, MulAut.conj p ∈ linearAutGroup 3 F := by
    intro p
    obtain ⟨g, rfl⟩ := proj_surjective 3 F p
    rw [← conjAut_toGL]
    exact conjAut_mem_linearAutGroup _
  have hlin : ρ (u * b) ∈ linearAutGroup 3 F := by
    obtain ⟨p, -, rfl⟩ := hu
    rw [map_mul, burnsideF447_rho_Phi C.hΦ C.hΦρ, hρb, hσ, map_one, mul_one]
    exact Subgroup.mul_mem _ (hconjL p)
      (Subgroup.mul_mem _ (conjAut_mem_linearAutGroup _) (hconjL _))
  have hinn : ρ (u * b) ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
    refine CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two le_rfl (fun h => ?_) _
      hlin k ?_
    · have := h.trans (Nat.gcd_dvd_left 3 _)
      omega
    · rw [← map_pow, hk, map_one]
      exact Subgroup.one_mem _
  obtain ⟨g, hg⟩ := hinn
  have hrg : u * b = Φ g := C.hρ (by rw [burnsideF447_rho_Phi C.hΦ C.hΦρ, hg])
  rw [hrg, ← C.hrange]
  exact ⟨g, rfl⟩

theorem burnsideF429a_L3_setup5 {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} [Gp.Normal] (h : HypF_4_4g .L3 2 f Gp M₁ M₂) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (Φ : projectiveSL 3 F →* E)
      (ρ : E →* MulAut (projectiveSL 3 F)) (R₁ R₂ : Subgroup (projectiveSL 3 F)),
      burnsideF447_Ctx f Φ ρ Gp ∧
      M₁ ⊓ M₂ = Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ ∧
      M₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup E) : Set E) ∧
      M₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E) ∧
      (R₁ = V1 ∨ R₁ = V2) ∧ (R₂ = V1 ∨ R₂ = V2) ∧
      ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hρ, hΦρ, hE, hD, hO,
    h₁, h₂, hRv⟩ := burnsideF447_setup hf h
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hNp := burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ := by
    have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := burnsideF4d_Y2_pCore_le hf h
    rw [burnsideF4d_pCoreOf_inf_eq (M₁ ⊓ M₂) hle]
    exact hNp.2
  have hSG : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
    rw [hS, ← hrange, MonoidHom.range_eq_map]
    exact burnsideF429_isSylowOf_map Φ hΦ
      (isSylowTwoOf_U (F := F) : ChF.IsSylowOf 2 (projUnitriangular 3 F) ⊤)
  have hR1 : R₁ = V1 ∨ R₁ = V2 := by
    rcases hRv with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hR2 : R₂ = V1 ∨ R₂ = V2 := by
    rcases hRv with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2
  exact ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, ⟨hf, hFcard, hΦ, hρ, hrange, hΦρ, hE⟩, hNp.1, hS,
    h₁, h₂, hR1, hR2, hSG⟩

theorem burnsideF429a_key1_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₁) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, _, _, _, Φ, ρ, R₁, R₂, C, hM12, hS, h₁, -, hR1, -, -⟩ :=
    burnsideF429a_L3_setup5 hf hyp.toHypF_4_4g
  exact burnsideF429a_L3_key_of_setup C hM12 hS h₁ hR1

theorem burnsideF429a_key2_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₂) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, _, _, _, Φ, ρ, R₁, R₂, C, hM12, hS, -, h₂, -, hR2, -⟩ :=
    burnsideF429a_L3_setup5 hf hyp.toHypF_4_4g
  exact burnsideF429a_L3_key_of_setup C hM12 hS h₂ hR2

theorem burnsideF429a_c5_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C5 .L3 Gp M₁ M₂ hyp T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, _, _, _, Φ, ρ, R₁, R₂, -, -, -, -, -, -, -, hSG⟩ :=
    burnsideF429a_L3_setup5 hf hyp.toHypF_4_4g
  exact Or.inl ⟨burnsideF429a_c5_of_key hSG inf_le_left hT (burnsideF429a_key1_L3 hyp hf),
    burnsideF429a_c5_of_key hSG inf_le_right hT (burnsideF429a_key2_L3 hyp hf)⟩

end Key

end CFSG.ASVolI
