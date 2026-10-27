module

public import CFSG.Milestones.ASVolI.F4L3
public import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOrders
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCStdIso
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Levi
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FaithfulA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabB
public import CFSG.Walter.JRFacts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Gamma

public section

namespace CFSG.ASVolI

section Setup

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Borel252 CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.ASVolI.ChF

theorem burnsideF447_setup {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : HypF_4_4g .L3 2 f Gp M₁ M₂) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (Φ : projectiveSL 3 F →* E)
      (ρ : E →* MulAut (projectiveSL 3 F))
      (R₁ R₂ : Subgroup (projectiveSL 3 F)) (s₁ s₂ : projectiveSL 3 F),
      Nat.card F = 2 ^ f ∧ Function.Injective Φ ∧ Φ.range = Gp ∧ Function.Injective ρ ∧
      (∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹) ∧
      (∀ e : E, ρ e ∈ semilinearAutGroup 3 F) ∧
      L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂ ∧
      L3OutHyp Φ (projUnitriangular 3 F) R₁ R₂ (Nat.card F) ∧
      M₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup E) : Set E) ∧
      M₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E) ∧
      ((R₁ = V1 ∧ R₂ = V2) ∨ (R₁ = V2 ∧ R₂ = V1)) := by
  obtain ⟨TD, hyam⟩ := burnsideF4d_Y1_yam h
  have hmodel := burnsideF4d_Y1_lieModel h
  haveI := h.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective h.centralizer_trivial
  obtain ⟨F, hFf, hFfin, hFchar, E', hFcard, hP⟩ :=
    l3Amalgam_borel hmodel (burnsideF4d_amalgamExt h TD hyam)
  have hq4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdata := l3DData_projectiveSL hq4
  obtain ⟨R₁, R₂, s₁, s₂, hdat, hRv, h1, h2⟩ : ∃ (R₁ R₂ : Subgroup (projectiveSL 3 F))
      (s₁ s₂ : projectiveSL 3 F), L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂ ∧
      ((R₁ = V1 ∧ R₂ = V2) ∨ (R₁ = V2 ∧ R₂ = V1)) ∧
      (M₁.subgroupOf Gp).map E'.toMonoidHom = Subgroup.normalizer (R₁ : Set (projectiveSL 3 F)) ∧
      (M₂.subgroupOf Gp).map E'.toMonoidHom =
        Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)) := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, _, _, hdata, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
    · exact ⟨_, _, _, _, hdata.swap, Or.inr ⟨rfl, rfl⟩, h1, h2⟩
  haveI : Finite (projectiveSL 3 F) := Finite.of_equiv ↥Gp E'.toEquiv
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : projectiveSL 3 F →* E, ∀ p, Φ p = ((E'.symm p : ↥Gp) : E) :=
    ⟨Gp.subtype.comp E'.symm.toMonoidHom, fun p => rfl⟩
  have hΦinj : Function.Injective Φ := fun a b hab =>
    E'.symm.injective (Subtype.ext ((hΦdef a).symm.trans (hab.trans (hΦdef b))))
  have hΦapp : ∀ d : ↥Gp, Φ (E' d) = (d : E) := fun d => by
    rw [hΦdef, MulEquiv.symm_apply_apply]
  have hrange : Φ.range = Gp := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rw [hΦdef]
      exact (E'.symm p).2
    · intro hx
      exact ⟨E' ⟨x, hx⟩, hΦapp ⟨x, hx⟩⟩
  obtain ⟨ρ, hρcongr, hρinj⟩ : ∃ ρ : E →* MulAut (projectiveSL 3 F),
      (∀ e, ρ e = MulAut.congr E' (burnsideF4d_rho Gp e)) ∧ Function.Injective ρ :=
    ⟨(MulAut.congr E').toMonoidHom.comp (burnsideF4d_rho Gp), fun e => rfl,
      (MulAut.congr E').injective.comp hinj⟩
  have hρapp : ∀ (e : E) (p : projectiveSL 3 F),
      ρ e p = E' (burnsideF4d_rho Gp e (E'.symm p)) := fun e p => by
    rw [hρcongr]; rfl
  have hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹ := by
    intro e p
    rw [hρapp, hΦapp, burnsideF4d_rho_apply, hΦdef]
  have hN1 := burnsideF4d_N1_eq h hyam
  have hN2 := burnsideF4d_N2_eq h hyam
  have hiff1 := burnsideF4d_Y2_mem_iff_stab hinj M₁ hN1
  have hiff2 := burnsideF4d_Y2_mem_iff_stab hinj M₂ hN2
  have hsemi1 : ∀ e ∈ M₁, ρ e ∈ semilinearAutGroup 3 F := by
    intro e he
    have hst := autStab_transport E' h1 hdat.borel.core₁ ((hiff1 e).mp he)
    rw [hρcongr]
    rcases hRv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact P3.mem_semilinear_of_map_V1 fun g hg => (hst g).mp hg
    · exact P3.mem_semilinear_of_map_V2 fun g hg => (hst g).mp hg
  have hsemi2 : ∀ e ∈ M₂, ρ e ∈ semilinearAutGroup 3 F := by
    intro e he
    have hst := autStab_transport E' h2 hdat.borel.core₂ ((hiff2 e).mp he)
    rw [hρcongr]
    rcases hRv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact P3.mem_semilinear_of_map_V2 fun g hg => (hst g).mp hg
    · exact P3.mem_semilinear_of_map_V1 fun g hg => (hst g).mp hg
  have hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F := by
    have hle : (⊤ : Subgroup E) ≤ (semilinearAutGroup 3 F).comap ρ := by
      rw [← h.gen]
      exact sup_le (fun e he => hsemi1 e he) (fun e he => hsemi2 e he)
    exact fun e => hle (Subgroup.mem_top e)
  have hO := P3.l3OutHyp_of_action hf hFcard ρ hρinj Φ hΦinj hΦρ hE hRv
  have hconj : ∀ (e : E) (X : Subgroup (projectiveSL 3 F)),
      e ∈ Subgroup.normalizer ((X.map Φ : Subgroup E) : Set E) ↔ ∀ p, p ∈ X ↔ ρ e p ∈ X := by
    intro e X
    rw [Subgroup.mem_normalizer_iff]
    constructor
    · intro hh p
      have := hh (Φ p)
      rw [Subgroup.mem_map_iff_mem hΦinj, ← hΦρ, Subgroup.mem_map_iff_mem hΦinj] at this
      exact this
    · intro hh y
      by_cases hy : y ∈ Φ.range
      · obtain ⟨p, rfl⟩ := hy
        rw [Subgroup.mem_map_iff_mem hΦinj, ← hΦρ, Subgroup.mem_map_iff_mem hΦinj]
        exact hh p
      · have h1 : y ∉ X.map Φ := fun hyX => hy (Subgroup.map_le_range Φ X hyX)
        have h2 : e * y * e⁻¹ ∉ X.map Φ := by
          intro hmem
          obtain ⟨q', -, hq'⟩ := hmem
          apply hy
          refine ⟨ρ e⁻¹ q', ?_⟩
          rw [hΦρ, hq']
          group
        exact ⟨fun hh' => absurd hh' h1, fun hh' => absurd hh' h2⟩
  have key : ∀ (M : Subgroup E) (r : Subgroup (projectiveSL 3 F)),
      (∀ e : E, e ∈ M ↔ burnsideF4d_rho Gp e ∈ autStab (M.subgroupOf Gp)) →
      (M.subgroupOf Gp).map E'.toMonoidHom = Subgroup.normalizer (r : Set (projectiveSL 3 F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (projectiveSL 3 F))) = r →
      M = Subgroup.normalizer ((r.map Φ : Subgroup E) : Set E) := by
    intro M r hM hP hcore
    set S : Subgroup ↥Gp := r.map E'.symm.toMonoidHom with hS
    have hnS : (Subgroup.normalizer (r : Set (projectiveSL 3 F))).map E'.symm.toMonoidHom =
        Subgroup.normalizer (S : Set ↥Gp) := by
      ext g
      rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map_equiv E'.symm r g]
    have hPS : M.subgroupOf Gp = Subgroup.normalizer (S : Set ↥Gp) := by
      rw [← hnS, ← hP, Subgroup.map_map]
      ext g
      simp
    have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set ↥Gp)) = S := by
      rw [← hnS, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective E'.symm.toMonoidHom
        E'.symm.injective, hcore]
    have hmemS : ∀ x : ↥Gp, x ∈ S ↔ E' x ∈ r := fun x => by
      rw [hS, Subgroup.mem_map_equiv]
      simp
    ext e
    rw [hM e, hPS, mem_autStab_iff_of_normalizer hcoreS, hconj]
    constructor
    · intro H p
      have h3 := H (E'.symm p)
      rw [hmemS, hmemS, MulEquiv.apply_symm_apply, ← hρapp] at h3
      exact h3
    · intro H x
      have h3 := H (E' x)
      rw [hρapp, MulEquiv.symm_apply_apply] at h3
      rw [hmemS, hmemS]
      exact h3
  exact ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦinj, hrange, hρinj, hΦρ, hE,
    hdat, hO, key M₁ R₁ hiff1 h1 hdat.borel.core₁, key M₂ R₂ hiff2 h2 hdat.borel.core₂, hRv⟩

end Setup

section D1

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem burnsideF447_conjAut_scalar (u : Fˣ) :
    conjAut 3 F (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  have hcomm := Subgroup.mem_center_iff.mp hc (Matrix.SpecialLinearGroup.toGL g)
  rw [coe_slConjugation, ← Matrix.SpecialLinearGroup.coe_GL_coe_matrix g,
    ← Units.val_mul, ← Units.val_mul, ← hcomm, mul_inv_cancel_right]

theorem burnsideF447_fix_x_eq (A : GL (Fin 3) F) (σ : F ≃+* F) (a : F)
    (h : (conjAut 3 F A * fieldAut 3 F σ) (xP a) = xP a) :
    (A : Matrix (Fin 3) (Fin 3) F) * (xM a).map σ = xM a * (A : Matrix (Fin 3) (Fin 3) F) := by
  have h1 := QuasithinUnique.Fin257.L3.standard_apply_proj A σ 0 (xMat a)
  rw [pow_zero, mul_one] at h1
  have h2 : proj 3 F (QuasithinUnique.Fin257.L3.Phi A σ 0 (xMat a)) = proj 3 F (xMat a) := by
    rw [← h1]; exact h
  have hsq : xMat a * xMat a = 1 := by
    rw [← xMat_add, CharTwo.add_self_eq_zero, xMat_zero]
  have h3 : QuasithinUnique.Fin257.L3.Phi A σ 0 (xMat a) = xMat a :=
    QuasithinUnique.Fin257.L3.eq_of_proj_eq_of_sq (by rw [← map_mul, hsq, map_one]) hsq h2
  have h4 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F =>
    (x : Matrix (Fin 3) (Fin 3) F)) h3
  simp only [QuasithinUnique.Fin257.L3.coe_Phi_zero] at h4
  exact QuasithinUnique.Fin257.L3.mul_eq_of_phi h4

theorem burnsideF447_fix_y_eq (A : GL (Fin 3) F) (σ : F ≃+* F) (b : F)
    (h : (conjAut 3 F A * fieldAut 3 F σ) (yP b) = yP b) :
    (A : Matrix (Fin 3) (Fin 3) F) * (yM b).map σ = yM b * (A : Matrix (Fin 3) (Fin 3) F) := by
  have h1 := QuasithinUnique.Fin257.L3.standard_apply_proj A σ 0 (yMat b)
  rw [pow_zero, mul_one] at h1
  have h2 : proj 3 F (QuasithinUnique.Fin257.L3.Phi A σ 0 (yMat b)) = proj 3 F (yMat b) := by
    rw [← h1]; exact h
  have hsq : yMat b * yMat b = 1 := by
    rw [← yMat_add, CharTwo.add_self_eq_zero, yMat_zero]
  have h3 : QuasithinUnique.Fin257.L3.Phi A σ 0 (yMat b) = yMat b :=
    QuasithinUnique.Fin257.L3.eq_of_proj_eq_of_sq (by rw [← map_mul, hsq, map_one]) hsq h2
  have h4 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F =>
    (x : Matrix (Fin 3) (Fin 3) F)) h3
  simp only [QuasithinUnique.Fin257.L3.coe_Phi_zero] at h4
  exact QuasithinUnique.Fin257.L3.mul_eq_of_phi h4

theorem burnsideF447_fix_xy (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hx : ∀ a : F, (conjAut 3 F A * fieldAut 3 F σ) (xP a) = xP a)
    (hy : ∀ b : F, (conjAut 3 F A * fieldAut 3 F σ) (yP b) = yP b) :
    σ = 1 ∧ ∃ c : F, conjAut 3 F A = MulAut.conj (wP c) := by
  have ex1 := burnsideF447_fix_x_eq A σ 1 (hx 1)
  have ey1 := burnsideF447_fix_y_eq A σ 1 (hy 1)
  have e10 := congrFun (congrFun ex1 0) 0
  have e11 := congrFun (congrFun ex1 0) 1
  have e12 := congrFun (congrFun ex1 0) 2
  have e14 := congrFun (congrFun ex1 2) 1
  have f10 := congrFun (congrFun ey1 0) 2
  have f12 := congrFun (congrFun ey1 1) 1
  have f13 := congrFun (congrFun ey1 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply, xM, yM] at e10 e11 e12 e14 f10 f12 f13
  have h00 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 :=
    QuasithinUnique.Fin257.L3.entry00_ne_zero A e10 e14
  have hA11 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    linear_combination -e11
  have hA22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    linear_combination -f13 - e11
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun a => ?_
    have exa := burnsideF447_fix_x_eq A σ a (hx a)
    have e := congrFun (congrFun exa 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply, xM] at e
    rw [hA11] at e
    have : (A : Matrix (Fin 3) (Fin 3) F) 0 0 * (σ a - a) = 0 := by linear_combination e
    have h2 := (mul_eq_zero.mp this).resolve_left h00
    simpa [sub_eq_zero] using h2
  obtain ⟨c, hc⟩ : ∃ c : F, c = (A : Matrix (Fin 3) (Fin 3) F) 0 2 /
      (A : Matrix (Fin 3) (Fin 3) F) 0 0 := ⟨_, rfl⟩
  refine ⟨hσ, c, ?_⟩
  have hAeq : A = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ h00) *
      Matrix.SpecialLinearGroup.toGL (wMat c) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_three, coe_wMat, wM]
    all_goals first | (rw [hc]; field_simp) | simp [*]
  rw [hAeq, map_mul, burnsideF447_conjAut_scalar, one_mul, conjAut_toGL]
  rfl

end D1

section Model

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}

theorem burnsideF447_rho_Phi (hΦ : Function.Injective Φ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹)
    (g : projectiveSL 3 F) : ρ (Φ g) = MulAut.conj g := by
  refine MulEquiv.ext fun p => hΦ ?_
  rw [hΦρ, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem burnsideF447_comm_iff (hΦ : Function.Injective Φ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹)
    (e : E) (p : projectiveSL 3 F) : ρ e p = p ↔ e * Φ p = Φ p * e := by
  rw [← hΦ.eq_iff, hΦρ]
  constructor
  · intro h
    calc e * Φ p = (e * Φ p * e⁻¹) * e := by group
      _ = Φ p * e := by rw [h]
  · intro h
    rw [h]
    group

end Model

section CardIso

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts.OddChar
  CFSG.RankThree.PartTwo.Sec8.Item8ModelProof CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd

theorem burnsideF447_ordA_eq (K : Type) [Field K] [Finite K] :
    ordA 2 (Nat.card K) = Nat.card (StatedProj (StatedSL 3 K)) := by
  have h := card_statedProj_statedSL_three_mul (F := K)
  have hg : 0 < Nat.gcd 3 (Nat.card K - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  unfold ordA
  rw [show Finset.Icc 2 (2 + 1) = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
  apply Nat.div_eq_of_eq_mul_left (by norm_num [hg] : 0 < Nat.gcd (2 + 1) (Nat.card K - 1))
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num, show 2 + 1 = 3 by norm_num]
  rw [← mul_assoc]
  exact h.symm

theorem burnsideF447_card_eq_of_iso {F K : Type} [Field F] [Finite F] [Field K] [Finite K]
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (h : Nat.card (StatedProj (StatedSL 3 F)) = Nat.card (StatedProj (StatedSL 3 K))) :
    Nat.card K = Nat.card F := by
  have hordF := burnsideF447_ordA_eq F
  have hordK := burnsideF447_ordA_eq K
  have hFK : ordA 2 (Nat.card K) = ordA 2 (2 ^ f) := by rw [hordK, ← h, ← hordF, hF]
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hq'K : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  rcases hp.eq_two_or_odd' with h2 | hodd
  ·
    rw [h2] at hq'K
    rw [hq'K] at hFK
    rcases eq_of_ordA_eq_ordA_two (m := 2) (f := (n : ℕ)) (n := f) (by norm_num) n.pos hf hFK with
      ⟨-, hnf⟩ | ⟨h3, -⟩
    · rw [hq'K, hF, hnf]
    · omega
  ·
    exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hF3 := card_statedProj_statedSL_three_mul (F := F)
    have hK3 := card_statedProj_statedSL_three_mul (F := K)
    have hq'odd : Odd (Nat.card K) := by rw [hq'K]; exact hodd.pow
    have hq'3 : 3 ≤ Nat.card K := by
      have h3 : 3 ≤ ringChar K := by
        obtain ⟨k, hk⟩ := hodd
        have := hp.two_le
        omega
      calc 3 ≤ ringChar K := h3
        _ ≤ ringChar K ^ (n : ℕ) := Nat.le_self_pow n.ne_zero _
        _ = _ := hq'K.symm
    set NK := Nat.card (StatedProj (StatedSL 3 K)) with hNK
    set NF := Nat.card (StatedProj (StatedSL 3 F)) with hNF
    have hKF : NK = NF := h.symm
    have key := two_pow_le_of_mul_eq_slOrd hq'odd hq'3 (n := 3) (N := NK)
      (g := Nat.gcd 3 (Nat.card K - 1)) (le_refl 3) (by
        rw [show 3 * (3 - 1) / 2 = 3 by norm_num, show Finset.Icc 2 3 = {2, 3} by rfl,
          Finset.prod_pair (by norm_num), ← mul_assoc]
        exact hK3) (Nat.gcd_dvd_right _ _)
    set q := Nat.card F with hq
    have hq2 : 2 ≤ q := by
      rw [hF]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hodd1 : ∀ k : ℕ, 1 ≤ k → Odd (q ^ k - 1) := by
      intro k hk
      rw [hF, ← pow_mul]
      have h2 : 2 ∣ 2 ^ (f * k) := dvd_pow_self 2 (by positivity)
      have h1 : 1 ≤ 2 ^ (f * k) := Nat.one_le_two_pow
      rw [Nat.odd_iff]
      omega
    have hqm1 : Odd (q - 1) := by simpa using hodd1 1 le_rfl
    have hgodd : Odd (Nat.gcd 3 (q - 1)) := hqm1.of_dvd_nat (Nat.gcd_dvd_right _ _)
    have hgpos : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hv0 : ∀ m : ℕ, Odd m → padicValNat 2 m = 0 := fun m hm =>
      padicValNat.eq_zero_of_not_dvd (fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd))
    have hv : padicValNat 2 NF = 3 * f := by
      have hpos : NF ≠ 0 := by
        have : 0 < NF := Nat.card_pos
        omega
      have h1 := padicValNat.mul (p := 2) hpos hgpos.ne'
      have e := congrArg (padicValNat 2) hF3
      have hq3 : q ^ 3 ≠ 0 := by positivity
      have h2 := padicValNat.mul (p := 2) (mul_ne_zero hq3 (hodd1 2 (by norm_num)).pos.ne')
        (hodd1 3 (by norm_num)).pos.ne'
      have h3 := padicValNat.mul (p := 2) hq3 (hodd1 2 (by norm_num)).pos.ne'
      have h4 : padicValNat 2 (q ^ 3) = 3 * f := by
        rw [hF, ← pow_mul, padicValNat.prime_pow]
        ring
      rw [h1, hv0 _ hgodd] at e
      rw [h2, h3, hv0 _ (hodd1 2 (by norm_num)), hv0 _ (hodd1 3 (by norm_num)), h4] at e
      omega
    have hlt : NK ^ 3 < 2 ^ (8 * (3 * f)) := by
      have h1 : NF ≤ NF * Nat.gcd 3 (q - 1) := Nat.le_mul_of_pos_right _ hgpos
      rw [hF3] at h1
      have h2 : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) < q ^ 8 := by
        obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = a + 1 := ⟨q ^ 2 - 1, by have := Nat.one_le_pow 2 q (by omega); omega⟩
        obtain ⟨b, hb⟩ : ∃ b, q ^ 3 = b + 1 := ⟨q ^ 3 - 1, by have := Nat.one_le_pow 3 q (by omega); omega⟩
        have e8 : q ^ 8 = q ^ 3 * (a + 1) * (b + 1) := by
          rw [← ha, ← hb, ← pow_add, ← pow_add]
        rw [e8, ha, hb]
        simp only [Nat.add_sub_cancel]
        have : 0 < q ^ 3 := by positivity
        nlinarith
      have h3 : NK < 2 ^ (8 * f) := by
        rw [hKF]
        calc NF < q ^ 8 := lt_of_le_of_lt h1 h2
          _ = 2 ^ (8 * f) := by rw [hF, ← pow_mul]; ring_nf
      calc NK ^ 3 < (2 ^ (8 * f)) ^ 3 := Nat.pow_lt_pow_left h3 (by norm_num)
        _ = 2 ^ (8 * (3 * f)) := by rw [← pow_mul]; ring_nf
    rw [hKF, hv] at key
    exact absurd key (not_le.mpr (by rwa [hKF] at hlt))

end CardIso

section InnDiag

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}

noncomputable def burnsideF447_eΦ (hΦ : Function.Injective Φ) {Gp : Subgroup E}
    (hrange : Φ.range = Gp) : ↥Gp ≃* projectiveSL 3 F :=
  ((MonoidHom.ofInjective hΦ).trans (MulEquiv.subgroupCongr hrange)).symm

theorem burnsideF447_Phi_eΦ (hΦ : Function.Injective Φ) {Gp : Subgroup E}
    (hrange : Φ.range = Gp) (x : ↥Gp) : Φ (burnsideF447_eΦ hΦ hrange x) = (x : E) := by
  have h := ((MonoidHom.ofInjective hΦ).trans (MulEquiv.subgroupCongr hrange)).apply_symm_apply x
  exact congrArg Subtype.val h

theorem burnsideF447_eΦ_conj (hΦ : Function.Injective Φ) {Gp : Subgroup E}
    (hrange : Φ.range = Gp)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹) (b : E)
    (x y : ↥Gp) (hxy : (y : E) = b * (x : E) * b⁻¹) :
    ρ b (burnsideF447_eΦ hΦ hrange x) = burnsideF447_eΦ hΦ hrange y := by
  apply hΦ
  rw [hΦρ, burnsideF447_Phi_eΦ, burnsideF447_Phi_eΦ, hxy]

open CFSG.ASVolI.ChF in
theorem burnsideF447_innDiag_of_mem [Finite F] (hΦ : Function.Injective Φ) {Gp : Subgroup E}
    (hrange : Φ.range = Gp) (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹)
    {b : E} (hb : ρ b ∈ linearAutGroup 3 F) : InnDiag3 Gp b := by
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hb
  refine ⟨F, inferInstance, inferInstance,
    (burnsideF447_eΦ hΦ hrange).trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F),
    A, ?_⟩
  intro x y hxy
  have hy := burnsideF447_eΦ_conj hΦ hrange hΦρ b x y hxy
  obtain ⟨g, hg⟩ := proj_surjective 3 F (burnsideF447_eΦ hΦ hrange x)
  rw [← hA, ← hg, conjAut_proj] at hy
  refine ⟨specialLinearGroupEquivStatedSL 3 F g,
    specialLinearGroupEquivStatedSL 3 F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g),
    ?_, ?_, ?_⟩
  · show CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F (burnsideF447_eΦ hΦ hrange x) = _
    rw [← hg]
    rfl
  · show CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F (burnsideF447_eΦ hΦ hrange y) = _
    rw [← hy]
    rfl
  · show Matrix.SpecialLinearGroup.toGL (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g) = _
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
    rfl

end InnDiag

section Transport

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.QTGen4.DSGen4.L34

theorem burnsideF447_projIso_conj {F K : Type} [Field F] [Field K] (τ : F ≃+* K)
    (B : GL (Fin 3) K) (p : projectiveSL 3 F) :
    (projIso τ).symm (conjAut 3 K B (projIso τ p)) =
      conjAut 3 F (Matrix.GeneralLinearGroup.map (τ.symm : K →+* F) B) p := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 F p
  apply (projIso τ).injective
  rw [MulEquiv.apply_symm_apply, projIso_proj, conjAut_proj, conjAut_proj, projIso_proj]
  congr 1
  apply Subtype.ext
  have hB : ∀ C : GL (Fin 3) K,
      (τ.toRingHom.mapMatrix : Matrix (Fin 3) (Fin 3) F →+* Matrix (Fin 3) (Fin 3) K)
        ((Matrix.GeneralLinearGroup.map (τ.symm : K →+* F) C : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) = (C : Matrix (Fin 3) (Fin 3) K) := by
    intro C
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  have hB' : ∀ C : GL (Fin 3) K,
      (τ.toRingHom.mapMatrix : Matrix (Fin 3) (Fin 3) F →+* Matrix (Fin 3) (Fin 3) K)
        ((((Matrix.GeneralLinearGroup.map (τ.symm : K →+* F) C)⁻¹ : GL (Fin 3) F)) :
          Matrix (Fin 3) (Fin 3) F) = ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro C
    rw [← map_inv]
    exact hB C⁻¹
  simp only [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_mul, hB, hB']

end Transport

section InnDiag2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.QTGen4.DSGen4.L34

theorem burnsideF447_D_normal {F : Type} [Field F] [Finite F] :
    (linearAutGroup 3 F).Normal := by
  obtain ⟨-, -, hDn, -, -, -, -, -, -, -⟩ := standard_outer_quotients (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  refine ⟨fun d hd γ => ?_⟩
  have hγ : γ ∈ standardAutGroup 3 F := hR ▸ Subgroup.mem_top γ
  have hd' : d ∈ standardAutGroup 3 F := hR ▸ Subgroup.mem_top d
  have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem burnsideF447_projEquiv_symm_mk {K : Type} [Field K] [Finite K] (X : StatedSL 3 K) :
    (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm
        (QuotientGroup.mk X : StatedProj (StatedSL 3 K)) =
      proj 3 K ((specialLinearGroupEquivStatedSL 3 K).symm X) := by
  apply (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).injective
  rw [MulEquiv.apply_symm_apply]
  show _ = QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 K
    ((specialLinearGroupEquivStatedSL 3 K).symm X))
  rw [MulEquiv.apply_symm_apply]

theorem burnsideF447_mem_of_innDiag {F : Type} [Field F] [CharP F 2] [Finite F] {E : Type}
    [Group E] {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (hΦ : Function.Injective Φ) {Gp : Subgroup E} (hrange : Φ.range = Gp)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹)
    {b : E} (hb : CFSG.ASVolI.ChF.InnDiag3 Gp b) : ρ b ∈ linearAutGroup 3 F := by
  obtain ⟨K, hKf, hKfin, e, A, hA⟩ := hb
  let eP := CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K
  let ψ : projectiveSL 3 F ≃* projectiveSL 3 K :=
    ((burnsideF447_eΦ hΦ hrange).symm.trans e).trans eP.symm
  have hGL : ∀ X : StatedSL 3 K, Matrix.SpecialLinearGroup.toGL
      ((specialLinearGroupEquivStatedSL 3 K).symm X) = (X : GL (Fin 3) K) := fun X =>
    congrArg Subtype.val ((specialLinearGroupEquivStatedSL 3 K).apply_symm_apply X)
  have hψ : ∀ p, ψ (ρ b p) = conjAut 3 K A (ψ p) := by
    intro p
    set x := (burnsideF447_eΦ hΦ hrange).symm p with hx
    set y := (burnsideF447_eΦ hΦ hrange).symm (ρ b p) with hy
    have hxp : burnsideF447_eΦ hΦ hrange x = p := MulEquiv.apply_symm_apply _ _
    have hxE : (x : E) = Φ p := by rw [← burnsideF447_Phi_eΦ hΦ hrange x, hxp]
    have hyE : (y : E) = b * (x : E) * b⁻¹ := by
      have : burnsideF447_eΦ hΦ hrange y = ρ b p := MulEquiv.apply_symm_apply _ _
      rw [← burnsideF447_Phi_eΦ hΦ hrange y, this, hΦρ, hxE]
    obtain ⟨X, X', hX, hX', hXX⟩ := hA x y hyE
    show eP.symm (e y) = conjAut 3 K A (eP.symm (e x))
    rw [hX, hX', burnsideF447_projEquiv_symm_mk, burnsideF447_projEquiv_symm_mk, conjAut_proj]
    congr 1
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, hGL, hGL,
      hXX]
  have hcard : Nat.card (StatedProj (StatedSL 3 F)) = Nat.card (StatedProj (StatedSL 3 K)) := by
    rw [← Nat.card_congr (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F).toEquiv,
      ← Nat.card_congr eP.toEquiv]
    exact Nat.card_congr ψ.toEquiv
  have hKcard := burnsideF447_card_eq_of_iso hf hF hcard
  haveI := Fintype.ofFinite F
  haveI := Fintype.ofFinite K
  let τ : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard])
  let π := projIso τ
  let χ : MulAut (projectiveSL 3 F) := ψ.trans π.symm
  have hχ : ∀ p, χ (ρ b p) =
      conjAut 3 F (Matrix.GeneralLinearGroup.map (τ.symm : K →+* F) A) (χ p) := by
    intro p
    show π.symm (ψ (ρ b p)) = conjAut 3 F _ (π.symm (ψ p))
    rw [hψ, ← burnsideF447_projIso_conj τ A (π.symm (ψ p)), MulEquiv.apply_symm_apply]
  have hbD : ρ b = χ⁻¹ * conjAut 3 F (Matrix.GeneralLinearGroup.map (τ.symm : K →+* F) A) * χ := by
    refine MulEquiv.ext fun p => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, ← hχ]
    simp
  rw [hbD]
  have := (burnsideF447_D_normal (F := F)).conj_mem _ (conjAut_mem_linearAutGroup
    (Matrix.GeneralLinearGroup.map (τ.symm : K →+* F) A)) χ⁻¹
  simpa using this

end InnDiag2

section FieldPart

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F]

noncomputable def burnsideF447_fp (θ : ↥(semilinearAutGroup 3 F)) : F ≃+* F :=
  Classical.choose (Classical.choose_spec (mem_semilinearAutGroup_iff.mp θ.2))

theorem burnsideF447_fp_spec (θ : ↥(semilinearAutGroup 3 F)) :
    ∃ A : GL (Fin 3) F, (θ : MulAut (projectiveSL 3 F)) =
      conjAut 3 F A * fieldAut 3 F (burnsideF447_fp θ) :=
  ⟨Classical.choose (mem_semilinearAutGroup_iff.mp θ.2),
    Classical.choose_spec (Classical.choose_spec (mem_semilinearAutGroup_iff.mp θ.2))⟩

theorem burnsideF447_fp_unique {θ : ↥(semilinearAutGroup 3 F)} {A : GL (Fin 3) F}
    {σ : F ≃+* F} (h : (θ : MulAut (projectiveSL 3 F)) = conjAut 3 F A * fieldAut 3 F σ) :
    burnsideF447_fp θ = σ := by
  obtain ⟨A₀, hA₀⟩ := burnsideF447_fp_spec θ
  have h1 : conjAut 3 F (A₀⁻¹ * A) * fieldAut 3 F (σ * (burnsideF447_fp θ)⁻¹) = 1 := by
    have e : conjAut 3 F A₀ * fieldAut 3 F (burnsideF447_fp θ) = conjAut 3 F A * fieldAut 3 F σ :=
      hA₀.symm.trans h
    rw [map_mul, map_mul, map_inv]
    calc conjAut 3 F A₀⁻¹ * conjAut 3 F A * (fieldAut 3 F σ * (fieldAut 3 F (burnsideF447_fp θ))⁻¹)
        = (conjAut 3 F A₀)⁻¹ * (conjAut 3 F A * fieldAut 3 F σ) *
            (fieldAut 3 F (burnsideF447_fp θ))⁻¹ := by
          rw [map_inv]; group
      _ = 1 := by rw [← e]; group
  have h2 := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
    (le_refl 3) _ _ h1).1
  have h3 : σ = burnsideF447_fp θ := by
    have := congrArg (· * burnsideF447_fp θ) h2
    simpa using this
  exact h3.symm

noncomputable def burnsideF447_fpHom : ↥(semilinearAutGroup 3 F) →* (F ≃+* F) where
  toFun := burnsideF447_fp
  map_one' := burnsideF447_fp_unique (A := 1) (σ := 1) (by simp)
  map_mul' θ₁ θ₂ := by
    obtain ⟨A₁, h₁⟩ := burnsideF447_fp_spec θ₁
    obtain ⟨A₂, h₂⟩ := burnsideF447_fp_spec θ₂
    refine burnsideF447_fp_unique (A := A₁ * Matrix.GeneralLinearGroup.map
      ((burnsideF447_fp θ₁ : F ≃+* F) : F →+* F) A₂) ?_
    rw [Subgroup.coe_mul, h₁, h₂, conjAut_mul_fieldAut_mul]

variable {E : Type} [Group E] {ρ : E →* MulAut (projectiveSL 3 F)}

noncomputable def burnsideF447_fpE (hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F) :
    E →* (F ≃+* F) :=
  burnsideF447_fpHom.comp (ρ.codRestrict _ hE)

theorem burnsideF447_fpE_eq (hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F) {e : E}
    {A : GL (Fin 3) F} {σ : F ≃+* F} (h : ρ e = conjAut 3 F A * fieldAut 3 F σ) :
    burnsideF447_fpE hE e = σ :=
  burnsideF447_fp_unique (θ := ⟨ρ e, hE e⟩) h

theorem burnsideF447_fpE_one_iff (hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F) (e : E) :
    burnsideF447_fpE hE e = 1 ↔ ρ e ∈ linearAutGroup 3 F := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := burnsideF447_fp_spec (⟨ρ e, hE e⟩ : ↥(semilinearAutGroup 3 F))
    have : burnsideF447_fp (⟨ρ e, hE e⟩ : ↥(semilinearAutGroup 3 F)) = 1 := h
    rw [this, map_one, mul_one] at hA
    rw [show ρ e = conjAut 3 F A from hA]
    exact conjAut_mem_linearAutGroup A
  · intro h
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp h
    exact burnsideF447_fpE_eq hE (A := A) (σ := 1) (by rw [map_one, mul_one, hA])

end FieldPart

section Diag

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}

theorem burnsideF447_normalizer_iff (hΦ : Function.Injective Φ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹)
    (e : E) (X : Subgroup (projectiveSL 3 F)) :
    e ∈ Subgroup.normalizer ((X.map Φ : Subgroup E) : Set E) ↔ ∀ p, p ∈ X ↔ ρ e p ∈ X := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hh p
    have := hh (Φ p)
    rw [Subgroup.mem_map_iff_mem hΦ, ← hΦρ, Subgroup.mem_map_iff_mem hΦ] at this
    exact this
  · intro hh y
    by_cases hy : y ∈ Φ.range
    · obtain ⟨p, rfl⟩ := hy
      rw [Subgroup.mem_map_iff_mem hΦ, ← hΦρ, Subgroup.mem_map_iff_mem hΦ]
      exact hh p
    · have h1 : y ∉ X.map Φ := fun hyX => hy (Subgroup.map_le_range Φ X hyX)
      have h2 : e * y * e⁻¹ ∉ X.map Φ := by
        intro hmem
        obtain ⟨q', -, hq'⟩ := hmem
        apply hy
        refine ⟨ρ e⁻¹ q', ?_⟩
        rw [hΦρ, hq']
        group
      exact ⟨fun hh' => absurd hh' h1, fun hh' => absurd hh' h2⟩

theorem burnsideF447_pres_iff {P : Type} [Group P] [Finite P] {θ : MulAut P} {U : Subgroup P}
    (h : ∀ p ∈ U, θ p ∈ U) : ∀ p, p ∈ U ↔ θ p ∈ U := by
  have hle : U.map θ.toMonoidHom ≤ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp
  have hcard : Nat.card U ≤ Nat.card (U.map θ.toMonoidHom) :=
    (Subgroup.card_map_of_injective θ.injective).ge
  have heq : U.map θ.toMonoidHom = U := Subgroup.eq_of_le_of_card_ge hle hcard
  intro p
  constructor
  · exact h p
  · intro hp
    rw [← heq] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    have : q = p := θ.injective hqp
    rwa [← this]

theorem burnsideF447_fieldAut_dMat (σ : F ≃+* F) (t₁ t₂ : Fˣ) :
    fieldAut 3 F σ (proj 3 F (dMat t₁ t₂)) =
      proj 3 F (dMat (Units.map σ.toMonoidHom t₁) (Units.map σ.toMonoidHom t₂)) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dMat, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem burnsideF447_fieldAut_U (σ : F ≃+* F) {p : projectiveSL 3 F}
    (hp : p ∈ projUnitriangular 3 F) : fieldAut 3 F σ p ∈ projUnitriangular 3 F := by
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hp
  exact mem_Ubar.mpr ⟨σ c, σ a, σ b, by
    rw [map_mul, map_mul, fieldAut_wP, fieldAut_xP, fieldAut_yP]⟩

theorem burnsideF447_fieldAut_B0 (σ : F ≃+* F) {p : projectiveSL 3 F}
    (hp : p ∈ torus3 F) : fieldAut 3 F σ p ∈ torus3 F := by
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hp
  rw [burnsideF447_fieldAut_dMat]
  exact dP_mem_torus3 _ _

theorem burnsideF447_nuDiag_U (s t : Fˣ) {p : projectiveSL 3 F}
    (hp : p ∈ projUnitriangular 3 F) : conjAut 3 F (nuDiagGL s t) p ∈ projUnitriangular 3 F := by
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hp
  exact mem_Ubar.mpr ⟨(s : F) * t * c, s * a, t * b, by
    rw [map_mul, map_mul, conjAut_nuDiag_wP, conjAut_nuDiag_xP, conjAut_nuDiag_yP]⟩

theorem burnsideF447_nuDiag_B0 (s t : Fˣ) {p : projectiveSL 3 F}
    (hp : p ∈ torus3 F) : conjAut 3 F (nuDiagGL s t) p ∈ torus3 F := by
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hp
  rw [conjAut_nuDiag_dMat]
  exact dP_mem_torus3 _ _

theorem burnsideF447_two_odd {X : Type} [Group X] [Finite X] {P N : Subgroup X}
    (hP : IsPGroup 2 P) (hN : Odd (Nat.card N)) {x : X} (hxP : x ∈ P) (hxN : x ∈ N) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  have h3 : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hN)
  have : orderOf x ∣ Nat.gcd (2 ^ k) (Nat.card N) := Nat.dvd_gcd h1 h2
  rw [h3.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

variable [Finite F]

theorem burnsideF447_diag (hq : 2 < Nat.card F) (hΦ : Function.Injective Φ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹)
    (hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F) {b : E}
    (hbU : b ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hbT : b ∈ Subgroup.normalizer (((torus3 F).map Φ : Subgroup E) : Set E)) :
    ∃ (δ t₁ t₂ : Fˣ) (σ : F ≃+* F), ρ b = conjAut 3 F (nuDiagGL δ 1) *
      MulAut.conj (proj 3 F (dMat t₁ t₂)) * fieldAut 3 F σ := by
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp (hE b)
  have hρU := (burnsideF447_normalizer_iff hΦ hΦρ b _).mp hbU
  have hρT := (burnsideF447_normalizer_iff hΦ hΦρ b _).mp hbT
  set δ : Fˣ := Matrix.GeneralLinearGroup.det A with hδ
  set d : GL (Fin 3) F := nuDiagGL δ 1 with hdd
  have hdet_d : (d : Matrix (Fin 3) (Fin 3) F).det = (δ : F) := by
    simp [hdd, coe_nuDiagGL, Matrix.det_diagonal, Fin.prod_univ_three]
  have hdetA : (A : Matrix (Fin 3) (Fin 3) F).det = (δ : F) := by
    rw [hδ]; rfl
  have hdet : ((d⁻¹ * A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h1 : ((d⁻¹ * A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
        ((d⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
          (A : Matrix (Fin 3) (Fin 3) F).det := by
      rw [Units.val_mul, Matrix.det_mul]
    have h2 : ((d⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det * (d : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    rw [h1, hdetA]
    rw [hdet_d] at h2
    exact h2
  set g : Matrix.SpecialLinearGroup (Fin 3) F := ⟨((d⁻¹ * A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hdet⟩ with hgdef
  have hg : Matrix.SpecialLinearGroup.toGL g = d⁻¹ * A := Units.ext rfl
  have hconjg : MulAut.conj (proj 3 F g) = conjAut 3 F (d⁻¹ * A) := by
    rw [← hg, conjAut_toGL]
  have hρ : ρ b = conjAut 3 F d * MulAut.conj (proj 3 F g) * fieldAut 3 F σ := by
    rw [hAσ, hconjg, ← map_mul, mul_inv_cancel_left]
  have hW : ∀ p, p ∈ projUnitriangular 3 F ↔ (fieldAut 3 F σ) p ∈ projUnitriangular 3 F :=
    burnsideF447_pres_iff (fun p hp => burnsideF447_fieldAut_U σ hp)
  have hWT : ∀ p, p ∈ torus3 F ↔ (fieldAut 3 F σ) p ∈ torus3 F :=
    burnsideF447_pres_iff (fun p hp => burnsideF447_fieldAut_B0 σ hp)
  have hD : ∀ p, p ∈ projUnitriangular 3 F ↔ (conjAut 3 F d) p ∈ projUnitriangular 3 F :=
    burnsideF447_pres_iff (fun p hp => burnsideF447_nuDiag_U δ 1 hp)
  have hDT : ∀ p, p ∈ torus3 F ↔ (conjAut 3 F d) p ∈ torus3 F :=
    burnsideF447_pres_iff (fun p hp => burnsideF447_nuDiag_B0 δ 1 hp)
  have hρq : ∀ p, ρ b ((fieldAut 3 F σ)⁻¹ p) = conjAut 3 F d (MulAut.conj (proj 3 F g) p) := by
    intro p
    rw [hρ, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  have hΘU : ∀ p, p ∈ projUnitriangular 3 F ↔
      (MulAut.conj (proj 3 F g)) p ∈ projUnitriangular 3 F := by
    intro p
    have h1 := hW ((fieldAut 3 F σ)⁻¹ p)
    rw [MulAut.apply_inv_self] at h1
    have h2 := hρU ((fieldAut 3 F σ)⁻¹ p)
    have h3 := hD ((MulAut.conj (proj 3 F g)) p)
    rw [← hρq p] at h3
    exact h1.symm.trans (h2.trans h3.symm)
  have hΘT : ∀ p, p ∈ torus3 F ↔ (MulAut.conj (proj 3 F g)) p ∈ torus3 F := by
    intro p
    have h1 := hWT ((fieldAut 3 F σ)⁻¹ p)
    rw [MulAut.apply_inv_self] at h1
    have h2 := hρT ((fieldAut 3 F σ)⁻¹ p)
    have h3 := hDT ((MulAut.conj (proj 3 F g)) p)
    rw [← hρq p] at h3
    exact h1.symm.trans (h2.trans h3.symm)
  have hgU : proj 3 F g ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) :=
    Subgroup.mem_normalizer_iff.mpr (fun p => by rw [← MulAut.conj_apply]; exact hΘU p)
  have hgT : proj 3 F g ∈ Subgroup.normalizer ((torus3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) :=
    Subgroup.mem_normalizer_iff.mpr (fun p => by rw [← MulAut.conj_apply]; exact hΘT p)
  obtain ⟨u, hu, t, ht, hut⟩ := torus3_mul hgU
  have huT : u ∈ Subgroup.normalizer ((torus3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
    have : u = proj 3 F g * t⁻¹ := by rw [hut]; group
    rw [this]
    exact Subgroup.mul_mem _ hgT (Subgroup.inv_mem _ (Subgroup.le_normalizer ht))
  have hu1 : u = 1 := by
    refine torus3_centS hq hu (fun b₀ hb₀ => ?_)
    have hk1 : u * b₀ * u⁻¹ ∈ torus3 F := (Subgroup.mem_normalizer_iff.mp huT b₀).mp hb₀
    have hk2 : u * b₀ * u⁻¹ * b₀⁻¹ ∈ torus3 F := Subgroup.mul_mem _ hk1 (Subgroup.inv_mem _ hb₀)
    have hk3 : u * b₀ * u⁻¹ * b₀⁻¹ ∈ projUnitriangular 3 F := by
      have : u * b₀ * u⁻¹ * b₀⁻¹ = u * (b₀ * u⁻¹ * b₀⁻¹) := by group
      rw [this]
      refine Subgroup.mul_mem _ hu ?_
      have hb₀N := torus3_le_normalizer hb₀
      have := (Subgroup.mem_normalizer_iff.mp hb₀N u⁻¹).mp (Subgroup.inv_mem _ hu)
      exact this
    have hk := burnsideF447_two_odd (isSylowTwoOf_U (F := F)).2.1 (torus3_odd (F := F)) hk3 hk2
    calc u * b₀ = (u * b₀ * u⁻¹ * b₀⁻¹) * b₀ * u := by group
      _ = b₀ * u := by rw [hk]; group
  rw [hu1, one_mul] at hut
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp ht
  refine ⟨δ, t₁, t₂, σ, ?_⟩
  rw [hρ, hut]

theorem burnsideF447_U_inf_normB0 (hq : 2 < Nat.card F) {u : projectiveSL 3 F}
    (hu : u ∈ projUnitriangular 3 F)
    (huT : u ∈ Subgroup.normalizer ((torus3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F))) : u = 1 := by
  refine torus3_centS hq hu (fun b₀ hb₀ => ?_)
  have hk1 : u * b₀ * u⁻¹ ∈ torus3 F := (Subgroup.mem_normalizer_iff.mp huT b₀).mp hb₀
  have hk2 : u * b₀ * u⁻¹ * b₀⁻¹ ∈ torus3 F := Subgroup.mul_mem _ hk1 (Subgroup.inv_mem _ hb₀)
  have hk3 : u * b₀ * u⁻¹ * b₀⁻¹ ∈ projUnitriangular 3 F := by
    have : u * b₀ * u⁻¹ * b₀⁻¹ = u * (b₀ * u⁻¹ * b₀⁻¹) := by group
    rw [this]
    refine Subgroup.mul_mem _ hu ?_
    have hb₀N := torus3_le_normalizer hb₀
    exact (Subgroup.mem_normalizer_iff.mp hb₀N u⁻¹).mp (Subgroup.inv_mem _ hu)
  have hk := burnsideF447_two_odd (isSylowTwoOf_U (F := F)).2.1 (torus3_odd (F := F)) hk3 hk2
  calc u * b₀ = (u * b₀ * u⁻¹ * b₀⁻¹) * b₀ * u := by group
    _ = b₀ * u := by rw [hk]; group

end Diag

section Struct

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.H13.F431.L3.P3 CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E}

@[expose] def burnsideF447_Bt (Φ : projectiveSL 3 F →* E) : Subgroup E :=
  Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) ⊓
    Subgroup.normalizer (((torus3 F).map Φ : Subgroup E) : Set E)

theorem burnsideF447_Phi_mem_normalizer (hΦ : Function.Injective Φ) (X : Subgroup (projectiveSL 3 F))
    (u : projectiveSL 3 F) :
    Φ u ∈ Subgroup.normalizer ((X.map Φ : Subgroup E) : Set E) ↔
      u ∈ Subgroup.normalizer (X : Set (projectiveSL 3 F)) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (Φ x)
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hΦ,
      Subgroup.mem_map_iff_mem hΦ] at this
    exact this
  · intro h x
    by_cases hx : x ∈ Φ.range
    · obtain ⟨y, rfl⟩ := hx
      rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hΦ,
        Subgroup.mem_map_iff_mem hΦ]
      exact h y
    · have h1 : x ∉ X.map Φ := fun hxX => hx (Subgroup.map_le_range Φ X hxX)
      have h2 : Φ u * x * (Φ u)⁻¹ ∉ X.map Φ := by
        intro hmem
        obtain ⟨q, -, hq⟩ := hmem
        apply hx
        refine ⟨u⁻¹ * q * u, ?_⟩
        rw [map_mul, map_mul, map_inv, hq]
        group
      exact ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩

theorem burnsideF447_Bt_inf_U (hq : 2 < Nat.card F) (hΦ : Function.Injective Φ) {x : E}
    (hx : x ∈ (projUnitriangular 3 F).map Φ) (hxB : x ∈ burnsideF447_Bt Φ) : x = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  have huT := (burnsideF447_Phi_mem_normalizer hΦ (torus3 F) u).mp hxB.2
  have := burnsideF447_U_inf_normB0 hq hu huT
  rw [this, map_one]

theorem burnsideF447_frattini [Finite E] [Φ.range.Normal] (hq : 2 < Nat.card F)
    (hΦ : Function.Injective Φ) {n : E}
    (hn : n ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E)) :
    ∃ u ∈ (projUnitriangular 3 F).map Φ, ∃ b ∈ burnsideF447_Bt Φ, n = u * b := by
  have hU2 : IsPGroup 2 (projUnitriangular 3 F) := (isSylowTwoOf_U (F := F)).2.1
  have hdis : ∀ x ∈ projUnitriangular 3 F, x ∈ torus3 F → x = 1 := fun x hx hxB =>
    burnsideF447_two_odd hU2 (torus3_odd (F := F)) hx hxB
  set R : Subgroup E := (projUnitriangular 3 F).map Φ with hR
  set B : Subgroup E := (torus3 F).map Φ with hB
  set Rr : Subgroup E := Subgroup.normalizer (R : Set E) ⊓ Φ.range with hRr
  have hRr' : Rr = (Subgroup.normalizer ((projUnitriangular 3 F : Subgroup _) : Set _)).map Φ :=
    normalizer_map_inf_range Φ hΦ _
  have hR2 : IsPGroup 2 R := hU2.map Φ
  have hRle : R ≤ Rr := fun x hx => ⟨Subgroup.le_normalizer hx, Subgroup.map_le_range Φ _ hx⟩
  have hBle : B ≤ Rr := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨map_mem_normalizer_map Φ (torus3_le_normalizer hb), ⟨b, rfl⟩⟩
  have hnorm : ∀ g ∈ Rr, ∀ x ∈ Rr, g * x * g⁻¹ ∈ Rr := by
    intro g hg x hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx) (Subgroup.inv_mem _ hg)
  have hRn : ∀ r ∈ R, n * r * n⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.mp hn r).mp hr
  have hRn' : ∀ r ∈ R, n⁻¹ * r * n ∈ R := by
    intro r hr
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) r).mp hr
    simpa using this
  have hcard : Nat.card Rr = Nat.card (projUnitriangular 3 F) * Nat.card (torus3 F) := by
    rw [hRr', Subgroup.card_map_of_injective hΦ]
    exact card_eq_mul_of_split Subgroup.le_normalizer (torus3_le_normalizer) hdis
      (fun h hh => torus3_mul hh)
  have hrel : R.relIndex Rr = Nat.card (torus3 F) := by
    have h1 := Subgroup.relIndex_mul_card R Rr
    rw [inf_of_le_left hRle, hR, Subgroup.card_map_of_injective hΦ, hcard] at h1
    have hpos : 0 < Nat.card (projUnitriangular 3 F) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)
  have hodd : ¬ 2 ∣ R.relIndex Rr := by
    rw [hrel]
    intro h2
    exact (Nat.not_even_iff_odd.mpr (torus3_odd (F := F))) (even_iff_two_dvd.mpr h2)
  set B' : Subgroup E := B.map (MulAut.conj n).toMonoidHom with hB'
  have hB'le : B' ≤ Rr := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Rr := hBle hy
    refine ⟨?_, ?_⟩
    · show n * y * n⁻¹ ∈ Subgroup.normalizer (R : Set E)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hy'.1) (Subgroup.inv_mem _ hn)
    · show n * y * n⁻¹ ∈ Φ.range
      exact Subgroup.Normal.conj_mem inferInstance y hy'.2 n
  have hRB : R ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨u, hu, rfl⟩, ⟨b, hb, hbu⟩⟩
    have hbu' : b = u := hΦ hbu
    subst hbu'
    rw [hdis b hu hb, map_one]
    exact Subgroup.one_mem _
  have hRB' : R ⊓ B' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxR, ⟨b, hb, hbx⟩⟩
    have hbx' : n * b * n⁻¹ = x := hbx
    have h1 : n⁻¹ * x * n ∈ R := hRn' x hxR
    have h2 : n⁻¹ * x * n = b := by rw [← hbx']; group
    rw [h2] at h1
    have hb1 : b = 1 := by
      have : b ∈ R ⊓ B := ⟨h1, hb⟩
      rw [hRB] at this
      exact Subgroup.mem_bot.mp this
    rw [hb1] at hbx'
    have : x = 1 := by rw [← hbx']; group
    rw [this]
    exact Subgroup.one_mem _
  have hFB : ∀ f ∈ Rr, ∃ r ∈ R, ∃ b ∈ B, f = r * b := by
    intro f hf
    rw [hRr'] at hf
    obtain ⟨h, hh, rfl⟩ := hf
    obtain ⟨u, hu, t, ht, rfl⟩ := torus3_mul hh
    exact ⟨Φ u, ⟨u, hu, rfl⟩, Φ t, ⟨t, ht, rfl⟩, map_mul Φ u t⟩
  have hFB' : ∀ f ∈ Rr, ∃ r ∈ R, ∃ b ∈ B', f = r * b := by
    intro f hf
    have hf' : n⁻¹ * f * n ∈ Rr := by
      refine ⟨?_, ?_⟩
      · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hf.1) hn
        exact this
      · have := Subgroup.Normal.conj_mem (inferInstance : Φ.range.Normal) f hf.2 n⁻¹
        simpa using this
    obtain ⟨r, hr, b, hb, hrb⟩ := hFB _ hf'
    refine ⟨n * r * n⁻¹, hRn r hr, n * b * n⁻¹, ⟨b, hb, rfl⟩, ?_⟩
    calc f = n * (n⁻¹ * f * n) * n⁻¹ := by group
      _ = n * (r * b) * n⁻¹ := by rw [hrb]
      _ = n * r * n⁻¹ * (n * b * n⁻¹) := by group
  obtain ⟨r, hr, hB'eq⟩ := CFSG.QuasithinUnique.Lin2.exists_conj_of_complements hRle
    (inf_le_left : Rr ≤ Subgroup.normalizer (R : Set E)) hR2 hodd hBle hB'le hRB hRB' hFB hFB'
  have hgB : ∀ y, y ∈ B ↔ (r * n) * y * (r * n)⁻¹ ∈ B := by
    refine burnsideF447_pres_iff (θ := MulAut.conj (r * n)) (U := B) (fun y hy => ?_)
    have h1 : n * y * n⁻¹ ∈ B' := ⟨y, hy, rfl⟩
    rw [hB'eq, CFSG.QuasithinUnique.Lin2.mem_conjR] at h1
    rw [MulAut.conj_apply]
    have : r * n * y * (r * n)⁻¹ = r * (n * y * n⁻¹) * r⁻¹ := by group
    rw [this]
    exact h1
  have hgR : r * n ∈ Subgroup.normalizer (R : Set E) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer hr) hn
  refine ⟨r⁻¹, R.inv_mem hr, r * n, ⟨hgR, Subgroup.mem_normalizer_iff.mpr hgB⟩, by group⟩

theorem burnsideF447_card_Rr [Finite E] (hΦ : Function.Injective Φ) :
    Nat.card ↥(Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) ⊓
      Φ.range) = Nat.card (projUnitriangular 3 F) * Nat.card (torus3 F) := by
  have hdis : ∀ x ∈ projUnitriangular 3 F, x ∈ torus3 F → x = 1 := fun x hx hxB =>
    burnsideF447_two_odd (isSylowTwoOf_U (F := F)).2.1 (torus3_odd (F := F)) hx hxB
  rw [normalizer_map_inf_range Φ hΦ, Subgroup.card_map_of_injective hΦ]
  exact card_eq_mul_of_split Subgroup.le_normalizer (torus3_le_normalizer) hdis
    (fun h hh => torus3_mul hh)

theorem burnsideF447_card_N [Finite E] [Φ.range.Normal] (hq : 2 < Nat.card F)
    (hΦ : Function.Injective Φ) (hodd : Odd Φ.range.index) :
    Nat.card ↥(Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E)) =
      Nat.card ((projUnitriangular 3 F).map Φ) * Nat.card (burnsideF447_Bt Φ) ∧
    Odd (Nat.card (burnsideF447_Bt Φ)) := by
  set N := Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) with hNdef
  have hmul : Nat.card N = Nat.card ((projUnitriangular 3 F).map Φ) * Nat.card (burnsideF447_Bt Φ) :=
    card_eq_mul_of_split Subgroup.le_normalizer inf_le_left
      (fun x hx hxB => burnsideF447_Bt_inf_U hq hΦ hx hxB)
      (fun h hh => burnsideF447_frattini hq hΦ hh)
  refine ⟨hmul, ?_⟩
  have h1 := Subgroup.relIndex_mul_card Φ.range N
  rw [inf_comm, burnsideF447_card_Rr hΦ] at h1
  have hrel : Odd (Φ.range.relIndex N) :=
    hodd.of_dvd_nat (Subgroup.relIndex_dvd_index_of_normal Φ.range N)
  have hpos : 0 < Nat.card (projUnitriangular 3 F) := Nat.card_pos
  rw [Subgroup.card_map_of_injective hΦ] at hmul
  have h2 : Nat.card (burnsideF447_Bt Φ) = Φ.range.relIndex N * Nat.card (torus3 F) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← hmul, ← h1]
    ring
  rw [h2]
  exact hrel.mul (torus3_odd (F := F))

theorem burnsideF447_odd_part_eq {a k m m' : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : 2 ^ a * m = 2 ^ k * m') : m = m' := by
  have h1 : m ∣ m' := by
    have hd : m ∣ 2 ^ k * m' := ⟨2 ^ a, by rw [← h]; ring⟩
    exact (Nat.Coprime.pow_right k hm.coprime_two_left.symm).dvd_of_dvd_mul_left hd
  have h2 : m' ∣ m := by
    have hd : m' ∣ 2 ^ a * m := ⟨2 ^ k, by rw [h]; ring⟩
    exact (Nat.Coprime.pow_right a hm'.coprime_two_left.symm).dvd_of_dvd_mul_left hd
  exact Nat.dvd_antisymm h1 h2

open CFSG.ASVolI.ChF in
theorem burnsideF447_hall_conj [Finite E] [Φ.range.Normal] (hq : 2 < Nat.card F)
    (hΦ : Function.Injective Φ) (hodd : Odd Φ.range.index) {N Bbar : Subgroup E}
    (hN : N = Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hB : IsHallTwoPrime Bbar N) :
    ∃ u ∈ (projUnitriangular 3 F).map Φ, ∀ y : E, y ∈ Bbar ↔ u * y * u⁻¹ ∈ burnsideF447_Bt Φ := by
  subst hN
  have hU2 : IsPGroup 2 ((projUnitriangular 3 F).map Φ) := (isSylowTwoOf_U (F := F)).2.1.map Φ
  obtain ⟨hcardN, hBtodd⟩ := burnsideF447_card_N hq hΦ hodd
  obtain ⟨hBle, hBodd, k, hk⟩ := hB
  set R : Subgroup E := (projUnitriangular 3 F).map Φ with hR
  set Bt := burnsideF447_Bt Φ with hBt
  obtain ⟨a, ha⟩ := hU2.exists_card_eq
  have hRcard : Nat.card R = 2 ^ a := ha
  have hRB : R ⊓ Bbar = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (burnsideF447_two_odd hU2 hBodd hx.1 hx.2)
  have hdisj : ∀ x ∈ R, x ∈ Bbar → x = 1 := fun x hx hxB =>
    burnsideF447_two_odd hU2 hBodd hx hxB
  have hBcard : Nat.card Bbar = Nat.card Bt := by
    have h1 := Subgroup.relIndex_mul_card Bbar (Subgroup.normalizer (R : Set E))
    rw [inf_of_le_left hBle, hk] at h1
    rw [hcardN, hRcard] at h1
    exact burnsideF447_odd_part_eq hBodd hBtodd h1
  have hcardH : Nat.card (Subgroup.normalizer (R : Set E)) = Nat.card R * Nat.card Bbar := by
    rw [hcardN, hBcard]
  have hFB' : ∀ f ∈ Subgroup.normalizer (R : Set E), ∃ r ∈ R, ∃ b ∈ Bbar, f = r * b :=
    exists_mul_eq_of_card Subgroup.le_normalizer hBle hdisj hcardH
  have hrel : ¬ 2 ∣ R.relIndex (Subgroup.normalizer (R : Set E)) := by
    have h1 := Subgroup.relIndex_mul_card R (Subgroup.normalizer (R : Set E))
    rw [inf_of_le_left Subgroup.le_normalizer, hRcard, hcardN, hRcard] at h1
    have hpos : 0 < 2 ^ a := by positivity
    have h2 : R.relIndex (Subgroup.normalizer (R : Set E)) = Nat.card Bt :=
      Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)
    rw [h2]
    intro h2d
    exact (Nat.not_even_iff_odd.mpr hBtodd) (even_iff_two_dvd.mpr h2d)
  obtain ⟨u, hu, hconj⟩ := CFSG.QuasithinUnique.Lin2.exists_conj_of_complements
    (R := R) (F := Subgroup.normalizer (R : Set E)) (B := Bt) (B' := Bbar)
    Subgroup.le_normalizer le_rfl hU2 hrel (inf_le_left : Bt ≤ Subgroup.normalizer (R : Set E)) hBle
    (by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.mpr (burnsideF447_Bt_inf_U hq hΦ hx.1 hx.2)) hRB
    (fun f hf => burnsideF447_frattini hq hΦ hf) hFB'
  refine ⟨u, hu, fun y => ?_⟩
  rw [hconj, CFSG.QuasithinUnique.Lin2.mem_conjR]

end Struct

section BtDiag

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}

theorem burnsideF447_nuDiag_comm (s t s' t' : Fˣ) :
    (nuDiagGL (F := F) s t) * nuDiagGL s' t' = nuDiagGL s' t' * nuDiagGL s t := by
  apply Units.ext
  simp only [Units.val_mul, coe_nuDiagGL, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem burnsideF447_diag_comm (δ δ' : Fˣ) {g g' : projectiveSL 3 F} (hg : g ∈ torus3 F)
    (hg' : g' ∈ torus3 F) :
    Commute (conjAut 3 F (nuDiagGL δ 1) * MulAut.conj g)
      (conjAut 3 F (nuDiagGL δ' 1) * MulAut.conj g') := by
  have h1 : Commute (conjAut 3 F (nuDiagGL δ 1)) (conjAut 3 F (nuDiagGL δ' 1)) := by
    show _ = _
    rw [← map_mul, ← map_mul, burnsideF447_nuDiag_comm]
  have h2 : ∀ (δ : Fˣ) {g : projectiveSL 3 F}, g ∈ torus3 F →
      Commute (conjAut 3 F (nuDiagGL δ 1)) (MulAut.conj g) := by
    intro δ g hg
    obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hg
    refine MulEquiv.ext fun p => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, conjAut_nuDiag_dMat]
  have h3 : Commute (MulAut.conj g) (MulAut.conj g') := by
    obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hg
    obtain ⟨s₁, s₂, rfl⟩ := mem_torus3.mp hg'
    show _ = _
    rw [← map_mul, ← map_mul]
    congr 1
    rw [← map_mul, ← map_mul, dMat_mul, dMat_mul, mul_comm t₁ s₁, mul_comm t₂ s₂]
  exact ((h1.mul_right (h2 δ hg')).mul_left ((h2 δ' hg).symm.mul_right h3))

theorem burnsideF447_diag_fpE (hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F) {b : E}
    {δ t₁ t₂ : Fˣ} {σ : F ≃+* F}
    (h : ρ b = conjAut 3 F (nuDiagGL δ 1) * MulAut.conj (proj 3 F (dMat t₁ t₂)) *
      fieldAut 3 F σ) : burnsideF447_fpE hE b = σ :=
  burnsideF447_fpE_eq hE (A := nuDiagGL δ 1 * Matrix.SpecialLinearGroup.toGL (dMat t₁ t₂))
    (σ := σ) (by rw [h, map_mul, conjAut_toGL])

theorem burnsideF447_Bt_one_comm (hq : 2 < Nat.card F) (hΦ : Function.Injective Φ)
    (hρ : Function.Injective ρ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹)
    (hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F) {b₁ b₂ : E}
    (h₁ : b₁ ∈ burnsideF447_Bt Φ) (h₂ : b₂ ∈ burnsideF447_Bt Φ)
    (hf₁ : burnsideF447_fpE hE b₁ = 1) (hf₂ : burnsideF447_fpE hE b₂ = 1) :
    b₁ * b₂ = b₂ * b₁ := by
  obtain ⟨δ₁, t₁, t₁', σ₁, e₁⟩ := burnsideF447_diag hq hΦ hΦρ hE h₁.1 h₁.2
  obtain ⟨δ₂, t₂, t₂', σ₂, e₂⟩ := burnsideF447_diag hq hΦ hΦρ hE h₂.1 h₂.2
  have s₁ : σ₁ = 1 := by rw [← burnsideF447_diag_fpE hE e₁, hf₁]
  have s₂ : σ₂ = 1 := by rw [← burnsideF447_diag_fpE hE e₂, hf₂]
  apply hρ
  rw [map_mul, map_mul, e₁, e₂, s₁, s₂]
  simp only [map_one, mul_one]
  exact (burnsideF447_diag_comm δ₁ δ₂ (dP_mem_torus3 _ _) (dP_mem_torus3 _ _)).eq

end BtDiag

section Clause3

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF

structure burnsideF447_Ctx {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] (f : ℕ)
    (Φ : projectiveSL 3 F →* E) (ρ : E →* MulAut (projectiveSL 3 F)) (Gp : Subgroup E) :
    Prop where
  hf : 2 ≤ f
  hF : Nat.card F = 2 ^ f
  hΦ : Function.Injective Φ
  hρ : Function.Injective ρ
  hrange : Φ.range = Gp
  hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹
  hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E]
  {f : ℕ} {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_Ctx.hq (C : burnsideF447_Ctx f Φ ρ Gp) : 2 < Nat.card F := by
  rw [C.hF]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) C.hf

theorem burnsideF447_Ctx.fpE_Phi (C : burnsideF447_Ctx f Φ ρ Gp) (p : projectiveSL 3 F) :
    burnsideF447_fpE C.hE (Φ p) = 1 := by
  rw [burnsideF447_fpE_one_iff, burnsideF447_rho_Phi C.hΦ C.hΦρ]
  obtain ⟨g, rfl⟩ := proj_surjective 3 F p
  rw [← conjAut_toGL]
  exact conjAut_mem_linearAutGroup _

theorem burnsideF447_Ctx.innDiag_iff (C : burnsideF447_Ctx f Φ ρ Gp) (b : E) :
    InnDiag3 Gp b ↔ burnsideF447_fpE C.hE b = 1 := by
  rw [burnsideF447_fpE_one_iff]
  exact ⟨burnsideF447_mem_of_innDiag C.hf C.hF C.hΦ C.hrange C.hΦρ,
    burnsideF447_innDiag_of_mem C.hΦ C.hrange C.hΦρ⟩

theorem burnsideF447_B0_le [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) (hodd : Odd Gp.index)
    {N Bbar B0bar : Subgroup E}
    (hN : N = Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hB : IsHallTwoPrime Bbar N)
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    B0bar ≤ (fittingSubgroup ↥Bbar).map Bbar.subtype := by
  haveI : Φ.range.Normal := by rw [C.hrange]; infer_instance
  have hodd' : Odd Φ.range.index := by rw [C.hrange]; exact hodd
  set fp := burnsideF447_fpE C.hE with hfp
  have hB0' : ∀ b, b ∈ B0bar ↔ b ∈ Bbar ∧ fp b = 1 := fun b => by
    rw [hB0 b, C.innDiag_iff]
  obtain ⟨u, hu, hconj⟩ := burnsideF447_hall_conj C.hq C.hΦ hodd' hN hB
  have hfu : fp u = 1 := by
    obtain ⟨p, -, rfl⟩ := hu
    exact C.fpE_Phi p
  have hcomm : ∀ a ∈ B0bar, ∀ b ∈ B0bar, a * b = b * a := by
    intro a ha b hb
    have ha' := (hB0' a).mp ha
    have hb' := (hB0' b).mp hb
    have hfa : fp (u * a * u⁻¹) = 1 := by rw [map_mul, map_mul, hfu, ha'.2, map_inv, hfu]; simp
    have hfb : fp (u * b * u⁻¹) = 1 := by rw [map_mul, map_mul, hfu, hb'.2, map_inv, hfu]; simp
    have h := burnsideF447_Bt_one_comm C.hq C.hΦ C.hρ C.hΦρ C.hE ((hconj a).mp ha'.1)
      ((hconj b).mp hb'.1) hfa hfb
    have h2 : u * (a * b) * u⁻¹ = u * (b * a) * u⁻¹ := by
      calc u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
        _ = (u * b * u⁻¹) * (u * a * u⁻¹) := h
        _ = u * (b * a) * u⁻¹ := by group
    simpa using h2
  have hB0eq : B0bar = Bbar ⊓ fp.ker := by
    ext b
    rw [hB0' b, Subgroup.mem_inf, MonoidHom.mem_ker]
  have hnorm : (B0bar.subgroupOf Bbar).Normal := by
    rw [hB0eq]
    have : (Bbar ⊓ fp.ker).subgroupOf Bbar = fp.ker.subgroupOf Bbar := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [this]
    infer_instance
  haveI : IsMulCommutative ↥(B0bar.subgroupOf Bbar) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp a.2) _
      (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  have hle : B0bar.subgroupOf Bbar ≤ fittingSubgroup ↥Bbar := le_sSup ⟨hnorm, inferInstance⟩
  intro x hx
  have hxB : x ∈ Bbar := ((hB0' x).mp hx).1
  exact ⟨⟨x, hxB⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end Clause3

section NT

open CFSG.Timmesfeld

theorem burnsideF447_exists_prime {f m₁ r : ℕ} (hf : 2 ≤ f) (hm₁ : 1 < m₁) (hm₁f : m₁ ∣ f)
    (hmodd : Odd m₁) (hr : r.Prime) (hrm : r ∣ m₁) :
    ∃ s : ℕ, s.Prime ∧ s ∣ 2 ^ f - 1 ∧ ¬ s ∣ 2 ^ (f / m₁) - 1 ∧ s ≠ r := by
  by_cases hf6 : f = 6
  · subst hf6
    have hm3 : m₁ = 3 := by
      have hd : m₁ ∣ 6 := hm₁f
      have : m₁ ≤ 6 := Nat.le_of_dvd (by norm_num) hd
      obtain ⟨k, hk⟩ := hmodd
      interval_cases m₁ <;> omega
    subst hm3
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp hrm
    refine ⟨7, by norm_num, by norm_num, by norm_num, by omega⟩
  · obtain ⟨s, hs⟩ := exists_isPrimitivePrimeDivisor hf hf6
    have hfpos : 0 < f := by omega
    have hdlt : f / m₁ < f := Nat.div_lt_self hfpos hm₁
    have hdpos : 0 < f / m₁ := Nat.div_pos (Nat.le_of_dvd hfpos hm₁f) (by omega)
    refine ⟨s, hs.prime, hs.dvd, ?_, ?_⟩
    · rw [hs.dvd_sub_one_iff hfpos]
      intro h
      exact absurd (Nat.le_of_dvd hdpos h) (by omega)
    · intro hsr
      subst hsr
      have h2 : s ≠ 2 := hs.ne_two hfpos
      haveI : Fact s.Prime := ⟨hs.prime⟩
      have h3 : s ∣ 2 ^ (s - 1) - 1 := by
        rw [Bang.dvd_two_pow_sub_one_iff]
        exact ZMod.pow_card_sub_one_eq_one (by
          intro h0
          have := (ZMod.natCast_eq_zero_iff 2 s).mp (by simpa using h0)
          exact h2 ((Nat.prime_dvd_prime_iff_eq hs.prime Nat.prime_two).mp this))
      have h4 := (hs.dvd_sub_one_iff hfpos (s - 1)).mp h3
      have h5 : f ≤ s - 1 := Nat.le_of_dvd (by have := hs.prime.two_le; omega) h4
      have h6 : s ≤ m₁ := Nat.le_of_dvd (by omega) hrm
      have h7 : m₁ ≤ f := Nat.le_of_dvd hfpos hm₁f
      have := hs.prime.two_le
      omega

theorem burnsideF447_moved {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) {σ : F ≃+* F} {s : ℕ} (hs : s.Prime) (hsf : s ∣ 2 ^ f - 1)
    (hsd : ¬ s ∣ 2 ^ (f / orderOf σ) - 1) : ∃ a : Fˣ, orderOf a = s ∧ σ (a : F) ≠ a := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hdvd : s ∣ Nat.card Fˣ := by rw [Nat.card_units, hF]; exact hsf
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' s hdvd
  refine ⟨a, ha, fun hfix => hsd ?_⟩
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := F) Nat.prime_two hf hF
  obtain ⟨-, S, hS, hcardS⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hcardS
  have hmemS : (a : F) ∈ S := by
    rw [← SetLike.mem_coe, hS]
    intro τ hτ
    have hτ' : τ ∈ MulAction.stabilizer (F ≃+* F) (a : F) :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hfix) hτ
    exact MulAction.mem_stabilizer_iff.mp hτ'
  haveI : Fintype S := Fintype.ofFinite S
  have ha0 : (⟨(a : F), hmemS⟩ : S) ≠ 0 := by
    intro h
    have : (a : F) = 0 := congrArg Subtype.val h
    exact a.ne_zero this
  have h1 := FiniteField.pow_card_sub_one_eq_one (⟨(a : F), hmemS⟩ : S) ha0
  have h2 : (a : F) ^ (2 ^ (f / orderOf σ) - 1) = 1 := by
    have h3 := congrArg Subtype.val h1
    rw [← Nat.card_eq_fintype_card, hcardS] at h3
    simpa using h3
  have h3 : a ^ (2 ^ (f / orderOf σ) - 1) = 1 := Units.ext (by simpa using h2)
  rw [← ha]
  exact orderOf_dvd_of_pow_eq_one h3

end NT

section Clause3b

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E]
  {f : ℕ} {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_dMat_inj {u a : Fˣ}
    (h : proj 3 F (dMat u u⁻¹) = proj 3 F (dMat a a⁻¹)) : u = a := by
  have h1 : proj 3 F (dMat (u * a⁻¹) (u⁻¹ * a)) = 1 := by
    have : proj 3 F (dMat u u⁻¹) * (proj 3 F (dMat a a⁻¹))⁻¹ = 1 := by rw [h]; group
    rwa [← map_inv, dMat_inv, ← map_mul, dMat_mul] at this
  obtain ⟨c, hc3, h2, h3⟩ := proj_dMat_eq_one h1
  have hc1 : c = 1 := by
    by_contra hne
    have hsq := unit_ne_one_sq (F := F) hne
    apply hsq
    have h2' : (c : F) = (u : F) * (a : F)⁻¹ := by rw [← h2]; simp
    have h3' : (c : F) = (u : F)⁻¹ * (a : F) := by rw [← h3]; simp
    have e2 : (c : F) * (c : F) = 1 := by
      calc (c : F) * c = ((u : F) * (a : F)⁻¹) * ((u : F)⁻¹ * (a : F)) := by
            rw [← h2', ← h3']
        _ = 1 := by field_simp
    simpa [sq] using e2
  subst hc1
  have : (u : F) * (a : F)⁻¹ = 1 := by simpa using h2
  apply Units.ext
  field_simp at this
  simpa using this

theorem burnsideF447_torus_conj_fix {g h : projectiveSL 3 F} (hg : g ∈ torus3 F)
    (hh : h ∈ torus3 F) : g * h * g⁻¹ = h := by
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hg
  obtain ⟨s₁, s₂, rfl⟩ := mem_torus3.mp hh
  have : proj 3 F (dMat t₁ t₂) * proj 3 F (dMat s₁ s₂) =
      proj 3 F (dMat s₁ s₂) * proj 3 F (dMat t₁ t₂) := by
    rw [← map_mul, ← map_mul, dMat_mul, dMat_mul, mul_comm t₁ s₁, mul_comm t₂ s₂]
  rw [this]; group

theorem burnsideF447_Phi_torus_mem_Bt {g : projectiveSL 3 F} (hg : g ∈ torus3 F) :
    Φ g ∈ burnsideF447_Bt Φ :=
  ⟨map_mem_normalizer_map Φ (torus3_le_normalizer hg),
    map_mem_normalizer_map Φ (Subgroup.le_normalizer hg)⟩

theorem burnsideF447_orderOf_fitting {B : Subgroup E} (z : ↥B) (hz : z ∈ fittingSubgroup ↥B) :
    orderOf (⟨z, hz⟩ : ↥(fittingSubgroup ↥B)) = orderOf (z : E) := by
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]

theorem burnsideF447_fitting_le [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) (hodd : Odd Gp.index)
    {N Bbar B0bar : Subgroup E}
    (hN : N = Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hB : IsHallTwoPrime Bbar N)
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    (fittingSubgroup ↥Bbar).map Bbar.subtype ≤ B0bar := by
  haveI : Φ.range.Normal := by rw [C.hrange]; infer_instance
  have hodd' : Odd Φ.range.index := by rw [C.hrange]; exact hodd
  set fp := burnsideF447_fpE C.hE with hfp
  have hB0' : ∀ b, b ∈ B0bar ↔ b ∈ Bbar ∧ fp b = 1 := fun b => by rw [hB0 b, C.innDiag_iff]
  have hB0le := burnsideF447_B0_le C hodd hN hB hB0
  obtain ⟨u, hu, hconj⟩ := burnsideF447_hall_conj C.hq C.hΦ hodd' hN hB
  have hfu : fp u = 1 := by
    obtain ⟨p, -, rfl⟩ := hu
    exact C.fpE_Phi p
  rintro x ⟨⟨x, hxB⟩, hxF, rfl⟩
  show x ∈ B0bar
  rw [hB0']
  refine ⟨hxB, ?_⟩
  by_contra hσ
  have hord1 : orderOf (fp x) ≠ 1 := fun h => hσ (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrσ⟩ := Nat.exists_prime_and_dvd hord1
  have hxodd : Odd (orderOf x) := by
    have h1 : orderOf x ∣ Nat.card Bbar := by
      have := orderOf_dvd_natCard (⟨x, hxB⟩ : Bbar)
      rwa [Subgroup.orderOf_mk] at this
    exact hB.2.1.of_dvd_nat h1
  have hrx : r ∣ orderOf x := hrσ.trans (orderOf_map_dvd fp x)
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hxodd) (even_iff_two_dvd.mpr hrx)
  obtain ⟨e, m', hm'r, hm₀⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' r hr.ne_one
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, mul_zero] at hm₀; exact absurd hm₀ (orderOf_pos x).ne'
    · exact h
  set y := x ^ m' with hy
  have hyB : y ∈ Bbar := Bbar.pow_mem hxB m'
  have hyF : (⟨y, hyB⟩ : ↥Bbar) ∈ fittingSubgroup ↥Bbar := by
    have := pow_mem hxF m'
    exact this
  have hordy : orderOf y = r ^ e := by
    rw [hy, orderOf_pow_of_dvd hm'pos.ne' (Dvd.intro_left _ hm₀.symm), hm₀,
      Nat.mul_div_cancel _ hm'pos]
  have hσ'eq : fp y = (fp x) ^ m' := by rw [hy, map_pow]
  have hσ'1 : fp y ≠ 1 := by
    intro h
    rw [hσ'eq] at h
    exact hm'r (hrσ.trans (orderOf_dvd_of_pow_eq_one h))
  have hσ'ord : orderOf (fp y) ∣ r ^ e := hordy ▸ orderOf_map_dvd fp y
  obtain ⟨j, -, hσ'j⟩ := (Nat.dvd_prime_pow hr).mp hσ'ord
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hσ'j
    exact hσ'1 (orderOf_eq_one_iff.mp hσ'j)
  have hm₁gt : 1 < orderOf (fp y) := by
    rw [hσ'j]
    exact Nat.one_lt_pow hj0 hr.one_lt
  have hm₁odd : Odd (orderOf (fp y)) := by
    rw [hσ'j]
    exact (hr.odd_of_ne_two hr2).pow
  have hrm₁ : r ∣ orderOf (fp y) := by rw [hσ'j]; exact dvd_pow_self r hj0
  have hm₁f : orderOf (fp y) ∣ f :=
    orderOf_dvd_of_pow_eq_one (autField_pow_eq_one (by have := C.hf; omega) C.hF (fp y))
  obtain ⟨s, hs, hsf, hsd, hsr⟩ := burnsideF447_exists_prime C.hf hm₁gt hm₁f hm₁odd hr hrm₁
  obtain ⟨a, haord, hmov⟩ := burnsideF447_moved (by have := C.hf; omega) C.hF hs hsf hsd
  obtain ⟨da, hda⟩ : ∃ da : projectiveSL 3 F, da = proj 3 F (dMat a a⁻¹) := ⟨_, rfl⟩
  have hdaT : da ∈ torus3 F := by rw [hda]; exact dP_mem_torus3 _ _
  have has : a ^ s = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
  have hdaord : da ^ s = 1 := by
    rw [hda, ← map_pow, dMat_pow, has, inv_pow, has, inv_one, dMat_one, map_one]
  obtain ⟨τ, hτ⟩ : ∃ τ : E, τ = u⁻¹ * Φ da * u := ⟨_, rfl⟩
  have hτu : u * τ * u⁻¹ = Φ da := by rw [hτ]; group
  have hτB : τ ∈ Bbar :=
    (hconj τ).mpr (by rw [hτu]; exact burnsideF447_Phi_torus_mem_Bt hdaT)
  have hfτ : fp τ = 1 := by
    rw [hτ, map_mul, map_mul, map_inv, hfu, C.fpE_Phi da]; simp
  have hτ0 : τ ∈ B0bar := (hB0' τ).mpr ⟨hτB, hfτ⟩
  have hτF : (⟨τ, hτB⟩ : ↥Bbar) ∈ fittingSubgroup ↥Bbar := by
    obtain ⟨z, hz, hzτ⟩ := hB0le hτ0
    have : z = ⟨τ, hτB⟩ := Subtype.ext hzτ
    rwa [← this]
  have hτs : τ ^ s = 1 := by
    have h1 : τ = u⁻¹ * Φ da * (u⁻¹)⁻¹ := by rw [hτ, inv_inv]
    rw [h1, conj_pow, ← map_pow, hdaord, map_one]; group
  have hcop : Nat.Coprime (orderOf τ) (orderOf y) := by
    have h1 : orderOf τ ∣ s := orderOf_dvd_of_pow_eq_one hτs
    have h2 : Nat.Coprime s (r ^ e) :=
      Nat.Coprime.pow_right e ((Nat.coprime_primes hs hr).mpr hsr)
    rw [hordy]
    exact h2.coprime_dvd_left h1
  have hcomm : y * τ = τ * y := by
    have key := Group.IsNilpotent.commute_of_orderOf_coprime
      (G := ↥(fittingSubgroup ↥Bbar)) (x := ⟨⟨y, hyB⟩, hyF⟩) (y := ⟨⟨τ, hτB⟩, hτF⟩)
      (by rw [burnsideF447_orderOf_fitting, burnsideF447_orderOf_fitting]; exact hcop.symm)
    exact congrArg (fun z : ↥(fittingSubgroup ↥Bbar) => ((z : ↥Bbar) : E)) key.eq
  have hy' : u * y * u⁻¹ ∈ burnsideF447_Bt Φ := (hconj y).mp hyB
  have hy'comm : (u * y * u⁻¹) * Φ da = Φ da * (u * y * u⁻¹) := by
    calc (u * y * u⁻¹) * Φ da = u * (y * τ) * u⁻¹ := by rw [← hτu]; group
      _ = u * (τ * y) * u⁻¹ := by rw [hcomm]
      _ = Φ da * (u * y * u⁻¹) := by rw [← hτu]; group
  obtain ⟨δ, t₁, t₂, σ₀, hρy'⟩ := burnsideF447_diag C.hq C.hΦ C.hΦρ C.hE hy'.1 hy'.2
  have hσ₀ : fp (u * y * u⁻¹) = σ₀ := burnsideF447_diag_fpE C.hE hρy'
  have hfpy' : fp (u * y * u⁻¹) = fp y := by rw [map_mul, map_mul, map_inv, hfu]; simp
  have hfix : ρ (u * y * u⁻¹) da = da := by
    apply C.hΦ
    rw [C.hΦρ, hy'comm]
    group
  have hact : ρ (u * y * u⁻¹) da = proj 3 F (dMat (Units.map σ₀.toMonoidHom a)
      (Units.map σ₀.toMonoidHom a⁻¹)) := by
    rw [hρy', MulAut.mul_apply, MulAut.mul_apply, hda, burnsideF447_fieldAut_dMat,
      MulAut.conj_apply, burnsideF447_torus_conj_fix (dP_mem_torus3 _ _) (dP_mem_torus3 _ _),
      conjAut_nuDiag_dMat]
  have h1 : proj 3 F (dMat (Units.map σ₀.toMonoidHom a) (Units.map σ₀.toMonoidHom a⁻¹)) = da := by
    rw [← hact, hfix]
  have h3 : Units.map σ₀.toMonoidHom a⁻¹ = (Units.map σ₀.toMonoidHom a)⁻¹ := map_inv _ _
  have h2 : Units.map σ₀.toMonoidHom a = a := by
    apply burnsideF447_dMat_inj
    rw [← hda, ← h1, h3]
  apply hmov
  have h4 : ((Units.map σ₀.toMonoidHom a : Fˣ) : F) = (a : F) := by rw [h2]
  have h5 : σ₀ (a : F) = (a : F) := by simpa using h4
  rw [show fp y = σ₀ from hfpy'.symm.trans hσ₀]
  exact h5

end Clause3b

section Clause3E

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem burnsideF447_clause3_E {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {Bbar B0bar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    B0bar = (fittingSubgroup ↥Bbar).map Bbar.subtype := by
  haveI := hyp.amalgam.finite
  have hf : 2 ≤ f := burnsideF4d_L3_two_le_f hyp
  have hodd : Odd Gp.index := burnsideF4d_L3_odd hf hyp
  haveI := hyp.amalgam.toHypF_4_4g.normal
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hρ, hΦρ, hE, hD, hO,
    h₁, h₂, hRv⟩ := burnsideF447_setup hf hyp.amalgam.toHypF_4_4g
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hN := (burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).1
  have C : burnsideF447_Ctx f Φ ρ Gp := ⟨hf, hFcard, hΦ, hρ, hrange, hΦρ, hE⟩
  exact le_antisymm (burnsideF447_B0_le C hodd hN hB hB0) (burnsideF447_fitting_le C hodd hN hB hB0)

end Clause3E

section Transport2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

theorem burnsideF447_fitting_range {H M : Type} [Group H] [Group M] (ψ : H →* M)
    (hψ : Function.Injective ψ) :
    (fittingSubgroup ↥ψ.range).map ψ.range.subtype = (fittingSubgroup H).map ψ := by
  have e := CFSG.WholeGroup.fittingSubgroup_map_mulEquiv (MonoidHom.ofInjective hψ)
  rw [← e, Subgroup.map_map]
  rfl

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF447_imB_eq_map (β : Cpl M₁ M₂ Y) (ε : Y →* M) {Bbar K : Subgroup E}
    (hBle : Bbar ≤ M₁ ⊓ M₂) (hK : K ≤ Bbar) :
    imB β ε K = (K.subgroupOf Bbar).map
      ((burnsideF4d_bOne β ε).comp (Subgroup.inclusion (hBle.trans inf_le_left))) := by
  rw [burnsideF4d_Z4_imB_eq β ε (hK.trans hBle)]
  unfold subImg
  rw [← Subgroup.map_map]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨(x : E), hK hx⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem burnsideF447_transport_fitting (β : Cpl M₁ M₂ Y) (ε : Y →* M)
    (hb : Function.Injective (burnsideF4d_bOne β ε)) {Bbar B0bar : Subgroup E}
    (hBle : Bbar ≤ M₁ ⊓ M₂) (h0 : B0bar = (fittingSubgroup ↥Bbar).map Bbar.subtype) :
    imB β ε B0bar = (fittingSubgroup ↥(imB β ε Bbar)).map (imB β ε Bbar).subtype := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥Bbar →* M, ψ = (burnsideF4d_bOne β ε).comp
      (Subgroup.inclusion (hBle.trans inf_le_left)) := ⟨_, rfl⟩
  have hψinj : Function.Injective ψ := by
    rw [hψ]
    exact hb.comp (Subgroup.inclusion_injective _)
  have h1 : imB β ε Bbar = ψ.range := by
    rw [burnsideF447_imB_eq_map β ε hBle le_rfl, Subgroup.subgroupOf_self, ← hψ,
      ← MonoidHom.range_eq_map]
  have hB0le : B0bar ≤ Bbar := by
    rw [h0]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have h2 : imB β ε B0bar = (fittingSubgroup ↥Bbar).map ψ := by
    rw [burnsideF447_imB_eq_map β ε hBle hB0le, ← hψ, h0]
    congr 1
    exact Subgroup.comap_map_eq_self_of_injective Bbar.subtype_injective _
  rw [h2, h1]
  exact (burnsideF447_fitting_range ψ hψinj).symm

theorem burnsideF447_clause3 {f : ℕ} {Gp : Subgroup E} {β : Cpl M₁ M₂ Y} {ε : Y →* M} {z : M}
    [Finite M] (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {Bbar B0bar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    imB β ε B0bar = (fittingSubgroup ↥(imB β ε Bbar)).map (imB β ε Bbar).subtype :=
  burnsideF447_transport_fitting β ε (hyp.inj.comp (f1_injective β hyp.faithful)) hB.1
    (burnsideF447_clause3_E hyp hB hB0)

end Transport2

section Levi

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F]

@[expose] def burnsideF447_diagGL (a b c : Fˣ) : GL (Fin 3) F where
  val := Matrix.diagonal ![(a : F), (b : F), (c : F)]
  inv := Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

theorem burnsideF447_levi_V2_mat (a c : Fˣ) {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (h20 : (M : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (M : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    ∃ t s : F, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F
        (burnsideF447_diagGL a a c) M = yMat t * wMat s * M := by
  have hd : (M : Matrix (Fin 3) (Fin 3) F) 2 2 * ((M : Matrix (Fin 3) (Fin 3) F) 0 0 *
      (M : Matrix (Fin 3) (Fin 3) F) 1 1 - (M : Matrix (Fin 3) (Fin 3) F) 0 1 *
      (M : Matrix (Fin 3) (Fin 3) F) 1 0) = 1 := by
    have := M.2
    rw [Matrix.det_fin_three] at this
    rw [h20, h21] at this
    linear_combination this
  have hm22 : (M : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hd
    exact zero_ne_one hd
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hc : (c : F) ≠ 0 := c.ne_zero
  refine ⟨((a : F) * (c : F)⁻¹ - 1) * (M : Matrix (Fin 3) (Fin 3) F) 1 2 *
      ((M : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹,
    ((a : F) * (c : F)⁻¹ - 1) * (M : Matrix (Fin 3) (Fin 3) F) 0 2 *
      ((M : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹, ?_⟩
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change Matrix.diagonal _ * (M : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal _ = (yM _ * wM _) * (M : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, yM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, h20, h21] <;>
    field_simp <;> ring

theorem burnsideF447_levi_V1_mat (a b : Fˣ) {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (h10 : (M : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (M : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) :
    ∃ s₁ s₂ : F, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F
        (burnsideF447_diagGL a b b) M = xMat s₁ * wMat s₂ * M := by
  have hd : (M : Matrix (Fin 3) (Fin 3) F) 0 0 * ((M : Matrix (Fin 3) (Fin 3) F) 1 1 *
      (M : Matrix (Fin 3) (Fin 3) F) 2 2 - (M : Matrix (Fin 3) (Fin 3) F) 1 2 *
      (M : Matrix (Fin 3) (Fin 3) F) 2 1) = 1 := by
    have := M.2
    rw [Matrix.det_fin_three] at this
    rw [h10, h20] at this
    linear_combination this
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hb : (b : F) ≠ 0 := b.ne_zero
  refine ⟨((a : F) * (b : F)⁻¹ - 1) * (M : Matrix (Fin 3) (Fin 3) F) 0 0 *
      ((M : Matrix (Fin 3) (Fin 3) F) 0 1 * (M : Matrix (Fin 3) (Fin 3) F) 2 2 -
        (M : Matrix (Fin 3) (Fin 3) F) 0 2 * (M : Matrix (Fin 3) (Fin 3) F) 2 1),
    ((a : F) * (b : F)⁻¹ - 1) * (M : Matrix (Fin 3) (Fin 3) F) 0 0 *
      ((M : Matrix (Fin 3) (Fin 3) F) 0 2 * (M : Matrix (Fin 3) (Fin 3) F) 1 1 -
        (M : Matrix (Fin 3) (Fin 3) F) 0 1 * (M : Matrix (Fin 3) (Fin 3) F) 1 2), ?_⟩
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change Matrix.diagonal _ * (M : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal _ =
    (xM _ * wM _) * (M : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, xM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, h10, h20]
  · field_simp
  · linear_combination (-(((a : F) * (b : F)⁻¹ - 1) * (M : Matrix (Fin 3) (Fin 3) F) 0 1)) * hd
  · linear_combination (-(((a : F) * (b : F)⁻¹ - 1) * (M : Matrix (Fin 3) (Fin 3) F) 0 2)) * hd
  all_goals field_simp

theorem burnsideF447_levi_V1 [Finite F] [CharP F 2] (a b : Fˣ) {m : projectiveSL 3 F}
    (hm : m ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) :
    conjAut 3 F (burnsideF447_diagGL a b b) m * m⁻¹ ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  rw [normalizer_V1_eq] at hm
  obtain ⟨M, hM, rfl⟩ := hm
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  obtain ⟨s₁, s₂, h⟩ := burnsideF447_levi_V1_mat a b h10 h20
  rw [conjAut_proj, h, map_mul, map_mul, mul_inv_cancel_right]
  exact mem_V1.mpr ⟨s₁, s₂, rfl⟩

theorem burnsideF447_levi_V2 [Finite F] [CharP F 2] (a c : Fˣ) {m : projectiveSL 3 F}
    (hm : m ∈ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) :
    conjAut 3 F (burnsideF447_diagGL a a c) m * m⁻¹ ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  rw [normalizer_V2_eq] at hm
  obtain ⟨M, hM, rfl⟩ := hm
  obtain ⟨h20, h21⟩ := mem_Q3_one_iff.mp hM
  obtain ⟨t, s, h⟩ := burnsideF447_levi_V2_mat a c h20 h21
  rw [conjAut_proj, h, map_mul, map_mul, mul_inv_cancel_right]
  exact mem_V2.mpr ⟨t, s, rfl⟩

theorem burnsideF447_diagGL_mul (a b c a' b' c' : Fˣ) :
    burnsideF447_diagGL (F := F) a b c * burnsideF447_diagGL a' b' c' =
      burnsideF447_diagGL (a * a') (b * b') (c * c') := by
  apply Units.ext
  show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem burnsideF447_diagGL_inv (a b c : Fˣ) :
    (burnsideF447_diagGL (F := F) a b c)⁻¹ = burnsideF447_diagGL a⁻¹ b⁻¹ c⁻¹ := rfl

theorem burnsideF447_toGL_dMat (t₁ t₂ : Fˣ) :
    (Matrix.SpecialLinearGroup.toGL (dMat t₁ t₂) : GL (Fin 3) F) =
      burnsideF447_diagGL t₁ t₂ (t₁ * t₂)⁻¹ := by
  apply Units.ext
  show ((dMat t₁ t₂ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_dMat]
  show _ = Matrix.diagonal _
  congr 1

theorem burnsideF447_nuDiagGL_eq (s t : Fˣ) :
    CFSG.GH74.QTGen4.DSGen4.L34.nuDiagGL (F := F) s t = burnsideF447_diagGL (s * t) t 1 := by
  apply Units.ext
  show Matrix.diagonal _ = Matrix.diagonal _
  congr 1

end Levi

section YbarMem

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF

variable {E : Type} [Group E] [Finite E]

theorem burnsideF447_Ybar_mem (Gp Mi Bbar : Subgroup E) [Gp.Normal] {b : E} (hbB : b ∈ Bbar)
    (hbM : b ∈ Mi)
    (hcomm : ∀ x ∈ oPPrime 2 (Gp ⊓ Mi), b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (oPPrime 2 (Gp ⊓ Mi))) :
    b ∈ f447Ybar Gp Mi Bbar := by
  have h1 : b ∈ Subgroup.normalizer ((Gp ⊓ Mi : Subgroup E) : Set E) :=
    burnsideF4d_Z1_mem_normalizer_inf Gp hbM
  have h2 : b ∈ Subgroup.normalizer ((oPPrime 2 (Gp ⊓ Mi) : Subgroup E) : Set E) :=
    burnsideF4d_Z1_normalizer_oPPrime h1
  have h3 : b ∈ Subgroup.normalizer ((pCoreOf 2 (oPPrime 2 (Gp ⊓ Mi)) : Subgroup E) : Set E) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ h2
  exact ⟨hbB, h2, h3, hcomm⟩

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {Φ : projectiveSL 3 F →* E}
  {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_Ybar_conj [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp)
    {R : Subgroup (projectiveSL 3 F)} (hR2 : IsPGroup 2 R)
    (hUR : projUnitriangular 3 F ≤ Subgroup.normalizer (R : Set (projectiveSL 3 F)))
    {M₂ Bbar : Subgroup E} (h₂ : M₂ = Subgroup.normalizer ((R.map Φ : Subgroup E) : Set E))
    {u : E} (hu : u ∈ (projUnitriangular 3 F).map Φ)
    (hconj : ∀ y, y ∈ Bbar ↔ u * y * u⁻¹ ∈ burnsideF447_Bt Φ)
    {b : E} (hb : b ∈ burnsideF447_Bt Φ)
    (hlev : ∀ m ∈ Subgroup.normalizer (R : Set (projectiveSL 3 F)), ρ b m * m⁻¹ ∈ R)
    (hbM : b ∈ M₂) :
    u⁻¹ * b * u ∈ f447Ybar Gp M₂ Bbar := by
  obtain ⟨pu, hpu, rfl⟩ := hu
  have huM : Φ pu ∈ M₂ := by
    rw [h₂]
    exact map_mem_normalizer_map Φ (hUR hpu)
  have huGp : Φ pu ∈ Gp := by
    rw [← C.hrange]
    exact ⟨pu, rfl⟩
  have hyB : (Φ pu)⁻¹ * b * Φ pu ∈ Bbar := by
    refine (hconj _).mpr ?_
    have e : Φ pu * ((Φ pu)⁻¹ * b * Φ pu) * (Φ pu)⁻¹ = b := by group
    rw [e]
    exact hb
  have hyM : (Φ pu)⁻¹ * b * Φ pu ∈ M₂ := M₂.mul_mem (M₂.mul_mem (M₂.inv_mem huM) hbM) huM
  refine burnsideF447_Ybar_mem Gp M₂ Bbar hyB hyM fun x hx => ?_
  have hxI : x ∈ Gp ⊓ M₂ := burnsideF4d_oPPrime_le _ hx
  have hx'Gp : Φ pu * x * (Φ pu)⁻¹ ∈ Gp := Gp.mul_mem (Gp.mul_mem huGp hxI.1) (Gp.inv_mem huGp)
  have hx'M : Φ pu * x * (Φ pu)⁻¹ ∈ M₂ := M₂.mul_mem (M₂.mul_mem huM hxI.2) (M₂.inv_mem huM)
  obtain ⟨p', hp'⟩ : ∃ p', Φ p' = Φ pu * x * (Φ pu)⁻¹ := by
    have := hx'Gp
    rw [← C.hrange] at this
    exact this
  have hp'N : p' ∈ Subgroup.normalizer (R : Set (projectiveSL 3 F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    have hn := (Subgroup.mem_normalizer_iff.mp (h₂ ▸ hx'M) (Φ r))
    rw [← hp', Subgroup.mem_map_iff_mem C.hΦ, ← map_mul, ← map_inv, ← map_mul,
      Subgroup.mem_map_iff_mem C.hΦ] at hn
    exact hn
  have hkey : (Φ pu)⁻¹ * b * Φ pu * x * ((Φ pu)⁻¹ * b * Φ pu)⁻¹ * x⁻¹ =
      (Φ pu)⁻¹ * (b * Φ p' * b⁻¹ * (Φ p')⁻¹) * Φ pu := by
    rw [hp']
    group
  have hΦR : b * Φ p' * b⁻¹ * (Φ p')⁻¹ ∈ R.map Φ := by
    have := Subgroup.mem_map_of_mem Φ (hlev p' hp'N)
    rw [map_mul, map_inv, C.hΦρ] at this
    exact this
  have hconjR : (Φ pu)⁻¹ * (b * Φ p' * b⁻¹ * (Φ p')⁻¹) * Φ pu ∈ R.map Φ := by
    have hn := (Subgroup.mem_normalizer_iff.mp (h₂ ▸ M₂.inv_mem huM)
      (b * Φ p' * b⁻¹ * (Φ p')⁻¹)).mp hΦR
    simpa using hn
  have hle : (R.map Φ) ≤ Gp ⊓ M₂ := by
    intro g hg
    refine ⟨?_, ?_⟩
    · rw [← C.hrange]
      exact Subgroup.map_le_range Φ R hg
    · rw [h₂]
      obtain ⟨r, hr, rfl⟩ := hg
      exact map_mem_normalizer_map Φ (Subgroup.le_normalizer hr)
  have hnorm : Gp ⊓ M₂ ≤ Subgroup.normalizer ((R.map Φ : Subgroup E) : Set E) := by
    rw [← h₂]
    exact inf_le_right
  have hcore : R.map Φ ≤ pCoreOf 2 (Gp ⊓ M₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hnorm (hR2.map Φ)
  rw [hkey, burnsideF4d_pCoreOf_oPPrime]
  exact hcore hconjR

end YbarMem

section YbarBot

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E] {f : ℕ}
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_conj_V1_iff (a b : Fˣ) (p : projectiveSL 3 F) :
    p ∈ (V1 : Subgroup (projectiveSL 3 F)) ↔
      conjAut 3 F (burnsideF447_diagGL a b b) p ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  constructor
  · intro hp
    have h := burnsideF447_levi_V1 a b (Subgroup.le_normalizer hp)
    simpa using (V1 : Subgroup (projectiveSL 3 F)).mul_mem h hp
  · intro hq
    have h := burnsideF447_levi_V1 a⁻¹ b⁻¹ (Subgroup.le_normalizer hq)
    have e : conjAut 3 F (burnsideF447_diagGL a⁻¹ b⁻¹ b⁻¹)
        (conjAut 3 F (burnsideF447_diagGL a b b) p) = p := by
      rw [← burnsideF447_diagGL_inv, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    rw [e] at h
    simpa using (V1 : Subgroup (projectiveSL 3 F)).mul_mem h hq

theorem burnsideF447_conj_V2_iff (a c : Fˣ) (p : projectiveSL 3 F) :
    p ∈ (V2 : Subgroup (projectiveSL 3 F)) ↔
      conjAut 3 F (burnsideF447_diagGL a a c) p ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  constructor
  · intro hp
    have h := burnsideF447_levi_V2 a c (Subgroup.le_normalizer hp)
    simpa using (V2 : Subgroup (projectiveSL 3 F)).mul_mem h hp
  · intro hq
    have h := burnsideF447_levi_V2 a⁻¹ c⁻¹ (Subgroup.le_normalizer hq)
    have e : conjAut 3 F (burnsideF447_diagGL a⁻¹ a⁻¹ c⁻¹)
        (conjAut 3 F (burnsideF447_diagGL a a c) p) = p := by
      rw [← burnsideF447_diagGL_inv, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    rw [e] at h
    simpa using (V2 : Subgroup (projectiveSL 3 F)).mul_mem h hq

theorem burnsideF447_normalizer_of_diag (C : burnsideF447_Ctx f Φ ρ Gp) {R : Subgroup (projectiveSL 3 F)}
    {b : E} {x y z : Fˣ} (hρ : ρ b = conjAut 3 F (burnsideF447_diagGL x y z))
    (hmatch : (R = V1 ∧ y = z) ∨ (R = V2 ∧ x = y)) :
    b ∈ Subgroup.normalizer ((R.map Φ : Subgroup E) : Set E) := by
  rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (burnsideF447_normalizer_iff C.hΦ C.hΦρ b _).mpr fun p => by
      rw [hρ]; exact burnsideF447_conj_V1_iff _ _ p
  · exact (burnsideF447_normalizer_iff C.hΦ C.hΦρ b _).mpr fun p => by
      rw [hρ]; exact burnsideF447_conj_V2_iff _ _ p

theorem burnsideF447_hlev_of_diag {R : Subgroup (projectiveSL 3 F)}
    {b : E} {x y z : Fˣ} (hρ : ρ b = conjAut 3 F (burnsideF447_diagGL x y z))
    (hmatch : (R = V1 ∧ y = z) ∨ (R = V2 ∧ x = y)) :
    ∀ m ∈ Subgroup.normalizer (R : Set (projectiveSL 3 F)), ρ b m * m⁻¹ ∈ R := by
  rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro m hm
    rw [hρ]
    exact burnsideF447_levi_V1 x y hm
  · intro m hm
    rw [hρ]
    exact burnsideF447_levi_V2 x z hm

theorem burnsideF447_Ybar_of_diag [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp)
    {R₂ : Subgroup (projectiveSL 3 F)} (hR2 : IsPGroup 2 R₂)
    (hUR : projUnitriangular 3 F ≤ Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)))
    {M₂ Bbar : Subgroup E} (h₂ : M₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E))
    {u : E} (hu : u ∈ (projUnitriangular 3 F).map Φ)
    (hconj : ∀ y, y ∈ Bbar ↔ u * y * u⁻¹ ∈ burnsideF447_Bt Φ)
    {b : E} (hb : b ∈ burnsideF447_Bt Φ) {x y z : Fˣ}
    (hρ : ρ b = conjAut 3 F (burnsideF447_diagGL x y z))
    (hmatch : (R₂ = V1 ∧ y = z) ∨ (R₂ = V2 ∧ x = y)) :
    u⁻¹ * b * u ∈ f447Ybar Gp M₂ Bbar :=
  burnsideF447_Ybar_conj C hR2 hUR h₂ hu hconj hb (burnsideF447_hlev_of_diag hρ hmatch)
    (h₂ ▸ burnsideF447_normalizer_of_diag C hρ hmatch)

theorem burnsideF447_rho_Phi_dMat (hΦ : Function.Injective Φ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹) (t₁ t₂ : Fˣ) :
    ρ (Φ (proj 3 F (dMat t₁ t₂))) =
      conjAut 3 F (burnsideF447_diagGL t₁ t₂ (t₁ * t₂)⁻¹) := by
  rw [burnsideF447_rho_Phi hΦ hΦρ, ← burnsideF447_toGL_dMat, conjAut_toGL]

theorem burnsideF447_f_two_of_Ybar_bot [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp)
    {R₂ : Subgroup (projectiveSL 3 F)} (hRv : R₂ = V1 ∨ R₂ = V2) (hR2 : IsPGroup 2 R₂)
    (hUR : projUnitriangular 3 F ≤ Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)))
    {M₂ Bbar : Subgroup E} (h₂ : M₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E))
    {u : E} (hu : u ∈ (projUnitriangular 3 F).map Φ)
    (hconj : ∀ y, y ∈ Bbar ↔ u * y * u⁻¹ ∈ burnsideF447_Bt Φ)
    (hY : f447Ybar Gp M₂ Bbar = ⊥) : f = 2 := by
  have key : ∀ t₁ t₂ : Fˣ, ((R₂ = V1 ∧ t₂ = (t₁ * t₂)⁻¹) ∨ (R₂ = V2 ∧ t₁ = t₂)) →
      ∃ c : Fˣ, c ^ 3 = 1 ∧ (t₁ : F) = c ∧ (t₂ : F) = c := by
    intro t₁ t₂ hm
    have hb : Φ (proj 3 F (dMat t₁ t₂)) ∈ burnsideF447_Bt Φ :=
      burnsideF447_Phi_torus_mem_Bt (dP_mem_torus3 _ _)
    have hy := burnsideF447_Ybar_of_diag C hR2 hUR h₂ hu hconj hb
      (burnsideF447_rho_Phi_dMat C.hΦ C.hΦρ t₁ t₂) hm
    rw [hY, Subgroup.mem_bot] at hy
    have h1 : Φ (proj 3 F (dMat t₁ t₂)) = 1 := by
      have e : Φ (proj 3 F (dMat t₁ t₂)) =
          u * (u⁻¹ * Φ (proj 3 F (dMat t₁ t₂)) * u) * u⁻¹ := by group
      rw [e, hy]
      group
    have h2 : proj 3 F (dMat t₁ t₂) = 1 := C.hΦ (by rw [h1, map_one])
    exact proj_dMat_eq_one h2
  have hcube : ∀ t : Fˣ, t ^ 3 = 1 := by
    intro t
    rcases hRv with h | h
    · obtain ⟨c, hc3, h1, h2⟩ := key (t⁻¹ * t⁻¹) t (Or.inl ⟨h, by group⟩)
      have : t = c := Units.ext h2
      rw [this]
      exact hc3
    · obtain ⟨c, hc3, h1, h2⟩ := key t t (Or.inr ⟨h, rfl⟩)
      have : t = c := Units.ext h1
      rw [this]
      exact hc3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : Nat.card Fˣ ∣ 3 := hord ▸ orderOf_dvd_of_pow_eq_one (hcube g)
  rw [Nat.card_units] at hdvd
  have h4 : Nat.card F ≤ 4 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hf2 : 2 ^ f ≤ 4 := C.hF ▸ h4
  have hf := C.hf
  by_contra hne
  have hf3 : 3 ≤ f := by omega
  have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  omega

theorem burnsideF447_eq_one_of_conj_one {u b : E} (h : u⁻¹ * b * u = 1) : b = 1 := by
  have : b = u * (u⁻¹ * b * u) * u⁻¹ := by group
  rw [this, h]
  group

theorem burnsideF447_Bt_le_torus [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) (hf2 : f = 2)
    {R₂ : Subgroup (projectiveSL 3 F)} (hRv : R₂ = V1 ∨ R₂ = V2) (hR2 : IsPGroup 2 R₂)
    (hUR : projUnitriangular 3 F ≤ Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)))
    {M₂ Bbar : Subgroup E} (h₂ : M₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E))
    {u : E} (hu : u ∈ (projUnitriangular 3 F).map Φ)
    (hconj : ∀ y, y ∈ Bbar ↔ u * y * u⁻¹ ∈ burnsideF447_Bt Φ)
    (hBodd : ∀ y ∈ Bbar, Odd (orderOf y))
    (hY : f447Ybar Gp M₂ Bbar = ⊥) {b : E} (hb : b ∈ burnsideF447_Bt Φ) :
    b ∈ (torus3 F).map Φ := by
  obtain ⟨δ, t₁, t₂, σ, hdiag⟩ := burnsideF447_diag C.hq C.hΦ C.hΦρ C.hE hb.1 hb.2
  have hσ : burnsideF447_fpE C.hE b = σ := burnsideF447_diag_fpE C.hE hdiag
  have hbodd : Odd (orderOf b) := by
    have h1 : u⁻¹ * b * u ∈ Bbar := by
      refine (hconj _).mpr ?_
      have e : u * (u⁻¹ * b * u) * u⁻¹ = b := by group
      rw [e]
      exact hb
    have h2 := hBodd _ h1
    have h3 := MulEquiv.orderOf_eq (MulAut.conj u⁻¹) b
    simp only [MulAut.conj_apply, inv_inv] at h3
    rwa [h3] at h2
  have hσ1 : σ = 1 := by
    have h1 : orderOf σ ∣ orderOf b := hσ ▸ orderOf_map_dvd (burnsideF447_fpE C.hE) b
    have h2 : σ ^ 2 = 1 := by
      have := autField_pow_eq_one (by have := C.hf; omega) C.hF σ
      rwa [hf2] at this
    have h3 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hodd' : Odd (orderOf σ) := hbodd.of_dvd_nat h1
    have : orderOf σ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    exact orderOf_eq_one_iff.mp this
  set g₁ : projectiveSL 3 F := proj 3 F (dMat t₁ t₂) with hg₁
  have hg₁T : g₁ ∈ torus3 F := dP_mem_torus3 _ _
  have hρb : ρ b = conjAut 3 F (burnsideF447_diagGL δ 1 1) * MulAut.conj g₁ := by
    rw [hdiag, hσ1, map_one, mul_one, burnsideF447_nuDiagGL_eq, mul_one]
  have hΦ₁ : Φ g₁ ∈ burnsideF447_Bt Φ := burnsideF447_Phi_torus_mem_Bt hg₁T
  have hb₁ : b * (Φ g₁)⁻¹ ∈ burnsideF447_Bt Φ :=
    (burnsideF447_Bt Φ).mul_mem hb ((burnsideF447_Bt Φ).inv_mem hΦ₁)
  have hρb₁ : ρ (b * (Φ g₁)⁻¹) = conjAut 3 F (burnsideF447_diagGL δ 1 1) := by
    rw [map_mul, map_inv, burnsideF447_rho_Phi C.hΦ C.hΦρ, hρb]
    group
  rcases hRv with hV | hV
  ·
    have hy := burnsideF447_Ybar_of_diag C hR2 hUR h₂ hu hconj hb₁ hρb₁ (Or.inl ⟨hV, rfl⟩)
    rw [hY, Subgroup.mem_bot] at hy
    have h1 := burnsideF447_eq_one_of_conj_one hy
    refine ⟨g₁, hg₁T, ?_⟩
    have : b = Φ g₁ := by
      have := congrArg (· * Φ g₁) h1
      simpa using this
    exact this.symm
  ·
    set g₂ : projectiveSL 3 F := proj 3 F (dMat 1 δ) with hg₂
    have hg₂T : g₂ ∈ torus3 F := dP_mem_torus3 _ _
    have hΦ₂ : Φ g₂ ∈ burnsideF447_Bt Φ := burnsideF447_Phi_torus_mem_Bt hg₂T
    have hb₂ : b * (Φ g₁)⁻¹ * Φ g₂ ∈ burnsideF447_Bt Φ :=
      (burnsideF447_Bt Φ).mul_mem hb₁ hΦ₂
    have hρb₂ : ρ (b * (Φ g₁)⁻¹ * Φ g₂) =
        conjAut 3 F (burnsideF447_diagGL (δ * 1) (1 * δ) (1 * (1 * δ)⁻¹)) := by
      rw [map_mul, hρb₁, hg₂, burnsideF447_rho_Phi_dMat C.hΦ C.hΦρ, ← map_mul,
        burnsideF447_diagGL_mul]
    have hy := burnsideF447_Ybar_of_diag C hR2 hUR h₂ hu hconj hb₂ hρb₂
      (Or.inr ⟨hV, by simp⟩)
    rw [hY, Subgroup.mem_bot] at hy
    have h1 := burnsideF447_eq_one_of_conj_one hy
    refine ⟨g₂⁻¹ * g₁, (torus3 F).mul_mem ((torus3 F).inv_mem hg₂T) hg₁T, ?_⟩
    have : b * (Φ g₁)⁻¹ = (Φ g₂)⁻¹ := by
      have := congrArg (· * (Φ g₂)⁻¹) h1
      simpa using this
    rw [map_mul, map_inv, ← this]
    group

theorem burnsideF447_E_le_Gp [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp)
    (hN : ∀ n ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E),
      n ∈ Gp) (e : E) : e ∈ Gp := by
  have hS : IsSylowTwoOf ((projUnitriangular 3 F).map Φ) Gp := by
    rw [← C.hrange]
    exact CFSG.Quasithin.H13.F431.L3.isSylowTwoOf_map_range Φ C.hΦ (isSylowTwoOf_U (F := F))
  have hGp : Gp.map (MulAut.conj e).toMonoidHom = Gp := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance y hy e
    · intro hx
      refine ⟨e⁻¹ * x * e, ?_, ?_⟩
      · have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) x hx e⁻¹
        simpa using this
      · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
  have hS' := hS.map_equiv (MulAut.conj e)
  rw [hGp] at hS'
  obtain ⟨h, hh, hconj⟩ := hS.exists_conj hS'
  have hn : h⁻¹ * e ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : e * x * e⁻¹ ∈ ((projUnitriangular 3 F).map Φ).map (MulAut.conj h).toMonoidHom := by
        rw [← hconj]
        exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
      obtain ⟨s, hs, hsx⟩ := h1
      have hsx' : h * s * h⁻¹ = e * x * e⁻¹ := by
        simpa [MulAut.conj_apply] using hsx
      have : h⁻¹ * e * x * (h⁻¹ * e)⁻¹ = s := by
        calc h⁻¹ * e * x * (h⁻¹ * e)⁻¹ = h⁻¹ * (e * x * e⁻¹) * h := by group
          _ = h⁻¹ * (h * s * h⁻¹) * h := by rw [hsx']
          _ = s := by group
      rw [this]
      exact hs
    · intro hx
      have h1 : e * x * e⁻¹ ∈ ((projUnitriangular 3 F).map Φ).map (MulAut.conj h).toMonoidHom := by
        refine ⟨h⁻¹ * e * x * (h⁻¹ * e)⁻¹, hx, ?_⟩
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
      rw [← hconj] at h1
      obtain ⟨s, hs, hsx⟩ := h1
      have hsx' : e * s * e⁻¹ = e * x * e⁻¹ := by
        simpa [MulAut.conj_apply] using hsx
      have : s = x := by
        have := congrArg (fun y => e⁻¹ * y * e) hsx'
        simpa [mul_assoc] using this
      rw [← this]
      exact hs
  have he : e = h * (h⁻¹ * e) := by group
  rw [he]
  exact Gp.mul_mem hh (hN _ hn)

theorem burnsideF447_oPPrime_eq_self {P : Type} [Group P] [Finite P] (N : Subgroup P)
    (hs : IsSimpleGroup (CFSG.Quasithin.oTwoQuot ↥N))
    (h2 : 2 ∣ Nat.card (CFSG.Quasithin.oTwoQuot ↥N)) : oPPrime 2 N = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oPPrime 2 N with hK
  have hKN : K ≤ N := burnsideF4d_oPPrime_le N
  have hQK : pCoreOf 2 N ≤ K := burnsideF4d_Z1_le_oPPrime
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) (CFSG.LieType.BorelTits.pCoreOf_le 2 N)
  let π : ↥N →* CFSG.Quasithin.oTwoQuot ↥N := QuotientGroup.mk' (CFSG.pCore 2 ↥N)
  have hKnorm : (K.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr (burnsideF4d_le_normalizer_oPPrime N)
  have himgnorm : ((K.subgroupOf N).map π).Normal :=
    hKnorm.map π (QuotientGroup.mk'_surjective _)
  haveI := hs
  haveI := himgnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K.subgroupOf N).map π) with hbot | htop
  · exfalso
    have hKQ : K ≤ pCoreOf 2 N := by
      intro k hk
      have h1 : (⟨k, hKN hk⟩ : ↥N) ∈ K.subgroupOf N := hk
      have h2' : π ⟨k, hKN hk⟩ ∈ (K.subgroupOf N).map π := ⟨_, h1, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h2'
      have h3 : (⟨k, hKN hk⟩ : ↥N) ∈ CFSG.pCore 2 ↥N := (QuotientGroup.eq_one_iff _).mp h2'
      exact (CFSG.GH74.QTGen4.DSGen4.L34.mem_pCore_iff_mem_pCoreOf N _).mp h3
    obtain ⟨S, hS⟩ := exists_isSylowTwoOf N
    have hSK : S ≤ K := burnsideF4d_Z1_le_oPPrime hS.isPGroup hS.le
    have hSQ : S = pCoreOf 2 N := le_antisymm (hSK.trans hKQ) hS.pCoreOf_le
    have hindex : (S.subgroupOf N).index = Nat.card (CFSG.Quasithin.oTwoQuot ↥N) := by
      have : S.subgroupOf N = CFSG.pCore 2 ↥N := by
        rw [hSQ]
        exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
      rw [this]
      rfl
    exact hS.2.2 (hindex ▸ h2)
  · apply le_antisymm hKN
    intro x hx
    have h1 : π ⟨x, hx⟩ ∈ (K.subgroupOf N).map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := h1
    have h3 : k⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥N := by
      apply (QuotientGroup.eq_one_iff _).mp
      have : π (k⁻¹ * ⟨x, hx⟩) = 1 := by
        rw [map_mul, map_inv, hkx]
        group
      exact this
    have h4 : ((k⁻¹ * ⟨x, hx⟩ : ↥N) : P) ∈ pCoreOf 2 N :=
      (CFSG.GH74.QTGen4.DSGen4.L34.mem_pCore_iff_mem_pCoreOf N _).mp h3
    have h5 : (k : P) ∈ K := hk
    have h6 : (k : P)⁻¹ * x ∈ K := by
      have : (k : P)⁻¹ * x = ((k⁻¹ * ⟨x, hx⟩ : ↥N) : P) := rfl
      rw [this]
      exact hQK h4
    have : x = (k : P) * ((k : P)⁻¹ * x) := by group
    rw [this]
    exact K.mul_mem h5 h6

theorem burnsideF447_oPPrime_normalizer [Finite F] [CharP F 2] (hq : Nat.card F = 4)
    {R : Subgroup (projectiveSL 3 F)} (hR : R = V1 ∨ R = V2) :
    oPPrime 2 (Subgroup.normalizer (R : Set (projectiveSL 3 F))) =
      Subgroup.normalizer (R : Set (projectiveSL 3 F)) := by
  rcases hR with rfl | rfl
  · obtain ⟨hs, hc⟩ := CFSG.GH74.QTGen4.DSGen4.FaithfulA5.isSimpleGroup_and_card_of_isL2Quot
      (CFSG.GH74.QTGen4.DSGen4.L34.isL2Quot_normalizer_V1 (F := F) hq)
    exact burnsideF447_oPPrime_eq_self _ hs (by rw [hc]; norm_num)
  · obtain ⟨hs, hc⟩ := CFSG.GH74.QTGen4.DSGen4.FaithfulA5.isSimpleGroup_and_card_of_isL2Quot
      (CFSG.GH74.QTGen4.DSGen4.L34.isL2Quot_normalizer_V2 (F := F) hq)
    exact burnsideF447_oPPrime_eq_self _ hs (by rw [hc]; norm_num)

end YbarBot

section Clause1E

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem burnsideF447_M_eq_oPPrime {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E]
    {Φ : projectiveSL 3 F →* E} {Gp : Subgroup E} (hΦ : Function.Injective Φ)
    (hrange : Φ.range = Gp) (hGp : ∀ e : E, e ∈ Gp) (hq : Nat.card F = 4)
    {R : Subgroup (projectiveSL 3 F)} (hR : R = V1 ∨ R = V2) {M : Subgroup E}
    (hM : M = Subgroup.normalizer ((R.map Φ : Subgroup E) : Set E)) :
    M = oPPrime 2 (Gp ⊓ M) := by
  have hGpM : Gp ⊓ M = M := inf_of_le_right fun x _ => hGp x
  have htop : Φ.range = ⊤ := eq_top_iff.mpr fun x _ => hrange ▸ hGp x
  have hMeq : M = (Subgroup.normalizer (R : Set (projectiveSL 3 F))).map Φ := by
    rw [hM, ← normalizer_map_inf_range Φ hΦ R, htop, inf_top_eq]
  rw [hGpM]
  conv_lhs => rw [hMeq]
  rw [hMeq, burnsideF4d_oPPrime_map Φ hΦ 2, burnsideF447_oPPrime_normalizer hq hR]

theorem burnsideF447_clause1_E {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {Bbar B0bar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b)
    (hY : f447Ybar Gp M₂ Bbar = ⊥) :
    f = 2 ∧ M₁ = oPPrime 2 (Gp ⊓ M₁) ∧ M₂ = oPPrime 2 (Gp ⊓ M₂) ∧ B0bar = Bbar ∧
      Nat.card ↥Bbar = 3 := by
  haveI := hyp.amalgam.finite
  have hf : 2 ≤ f := burnsideF4d_L3_two_le_f hyp
  have hodd : Odd Gp.index := burnsideF4d_L3_odd hf hyp
  haveI := hyp.amalgam.toHypF_4_4g.normal
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hρ, hΦρ, hE, hD, hO,
    h₁, h₂, hRv⟩ := burnsideF447_setup hf hyp.amalgam.toHypF_4_4g
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hN := (burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).1
  have C : burnsideF447_Ctx f Φ ρ Gp := ⟨hf, hFcard, hΦ, hρ, hrange, hΦρ, hE⟩
  have hodd' : Odd Φ.range.index := by rw [hrange]; exact hodd
  obtain ⟨u, hu, hconj⟩ := burnsideF447_hall_conj C.hq C.hΦ hodd' hN hB
  have hR2 : IsPGroup 2 R₂ := hD.borel.isPGroup₂
  have hUR : projUnitriangular 3 F ≤ Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)) :=
    Subgroup.le_normalizer.trans hD.borel.lt₂.le
  have hRv₂ : R₂ = V1 ∨ R₂ = V2 := by
    rcases hRv with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hRv₁ : R₁ = V1 ∨ R₁ = V2 := by
    rcases hRv with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hf2 : f = 2 := burnsideF447_f_two_of_Ybar_bot C hRv₂ hR2 hUR h₂ hu hconj hY
  have hq4 : Nat.card F = 4 := by rw [hFcard, hf2]; norm_num
  have hBodd : ∀ y ∈ Bbar, Odd (orderOf y) := fun y hy => by
    have h1 : orderOf y ∣ Nat.card Bbar := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : Bbar)
      rwa [Subgroup.orderOf_mk] at this
    exact hB.2.1.of_dvd_nat h1
  have hBt : ∀ b ∈ burnsideF447_Bt Φ, b ∈ (torus3 F).map Φ := fun b hb =>
    burnsideF447_Bt_le_torus C hf2 hRv₂ hR2 hUR h₂ hu hconj hBodd hY hb
  have hNGp : ∀ n ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E),
      n ∈ Gp := by
    intro n hn
    obtain ⟨v, hv, b, hb, rfl⟩ := burnsideF447_frattini C.hq C.hΦ hn
    exact Gp.mul_mem (hrange ▸ Subgroup.map_le_range Φ _ hv)
      (hrange ▸ Subgroup.map_le_range Φ _ (hBt b hb))
  have hE' : ∀ e : E, e ∈ Gp := burnsideF447_E_le_Gp C hNGp
  have hInn : ∀ b : E, InnDiag3 Gp b := fun b => by
    refine (C.innDiag_iff b).mpr ?_
    obtain ⟨p, rfl⟩ : b ∈ Φ.range := hrange ▸ hE' b
    exact C.fpE_Phi p
  have hBtEq : burnsideF447_Bt Φ = (torus3 F).map Φ := by
    refine le_antisymm hBt ?_
    rintro _ ⟨g, hg, rfl⟩
    exact burnsideF447_Phi_torus_mem_Bt hg
  have hBbarEq : Bbar = (burnsideF447_Bt Φ).map (MulAut.conj u⁻¹).toMonoidHom := by
    ext y
    constructor
    · intro hy
      refine ⟨u * y * u⁻¹, (hconj y).mp hy, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      group
    · rintro ⟨b, hb, rfl⟩
      refine (hconj _).mpr ?_
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      have e : u * (u⁻¹ * b * u) * u⁻¹ = b := by group
      rw [e]
      exact hb
  refine ⟨hf2, burnsideF447_M_eq_oPPrime C.hΦ hrange hE' hq4 hRv₁ h₁,
    burnsideF447_M_eq_oPPrime C.hΦ hrange hE' hq4 hRv₂ h₂, ?_, ?_⟩
  · ext b
    rw [hB0 b]
    exact ⟨fun h => h.1, fun h => ⟨h, hInn b⟩⟩
  · rw [hBbarEq, Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective, hBtEq,
      Subgroup.card_map_of_injective C.hΦ]
    exact CFSG.GH74.QTGen4.DSGen4.L34.card_torus3 hq4

end Clause1E

section Clause1M

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

theorem burnsideF447_odd_centralizer {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {Bbar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂)) :
    Odd (Nat.card ↥(Subgroup.centralizer ((imB β ε Bbar : Subgroup M) : Set M))) := by
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  have hf : 2 ≤ f := burnsideF4d_L3_two_le_f hyp
  obtain ⟨D, hG, hz, hDS, hQ₁, hQ₂⟩ := burnsideF4d_L3_setup hf hyp
  obtain ⟨hBH, hBodd, k, hk⟩ := burnsideF4d_Z4_imB_hall β hyp.faithful ε hyp.inj hB
  by_contra hne
  have hev : 2 ∣ Nat.card ↥(Subgroup.centralizer ((imB β ε Bbar : Subgroup M) : Set M)) := by
    rcases Nat.even_or_odd (Nat.card ↥(Subgroup.centralizer ((imB β ε Bbar : Subgroup M) : Set M)))
      with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 2 hev
  have hjC : (j : M) ∈ Subgroup.centralizer ((imB β ε Bbar : Subgroup M) : Set M) := j.2
  have hj2 : (j : M) ^ 2 = 1 := by
    have : orderOf (j : M) = 2 := (Subgroup.orderOf_coe j).trans hj
    rw [← this]
    exact pow_orderOf_eq_one _
  have hj1 : (j : M) ≠ 1 := by
    intro h
    have : orderOf (j : M) = 2 := (Subgroup.orderOf_coe j).trans hj
    rw [h, orderOf_one] at this
    omega
  obtain ⟨a, haZ⟩ := hG.inv_conj_Z hj2 hj1
  obtain ⟨z', hz'⟩ : ∃ z' : M, z' = a⁻¹ * (j : M) * a := ⟨_, rfl⟩
  rw [← hz'] at haZ
  have hz'1 : z' ≠ 1 := by rw [hz']; exact conj_ne_one' hj1
  have hcomm : ∀ y ∈ conjSub a⁻¹ (imB β ε Bbar), y * z' = z' * y := by
    intro y hy
    rw [mem_conjSub, inv_inv] at hy
    have h1 := Subgroup.mem_centralizer_iff.mp hjC _ hy
    rw [hz']
    calc y * (a⁻¹ * (j : M) * a) = a⁻¹ * ((a * y * a⁻¹) * (j : M)) * a := by group
      _ = a⁻¹ * ((j : M) * (a * y * a⁻¹)) * a := by rw [h1]
      _ = (a⁻¹ * (j : M) * a) * y := by group
  have hB'H : conjSub a⁻¹ (imB β ε Bbar) ≤ MiOne β ε ⊓ MiTwo β ε := fun y hy =>
    hG.cent z' haZ hz'1 y (hcomm y hy)
  have hB'odd : Odd (Nat.card ↥(conjSub a⁻¹ (imB β ε Bbar))) := by
    rw [card_conjSub]
    exact hBodd
  have hcard : ∃ k : ℕ, Nat.card ↥(MiOne β ε ⊓ MiTwo β ε) =
      2 ^ k * Nat.card ↥(conjSub a⁻¹ (imB β ε Bbar)) := by
    refine ⟨k, ?_⟩
    rw [card_conjSub]
    exact hk
  obtain ⟨n, hn, hB'eq⟩ := burnsideF4d_Z4_exists_conj D hG hB'H hB'odd hcard
  have hnz : n * z' = z' * n := (D.mem_Z.mp haZ).2 n hn
  have hzc : ∀ b ∈ D.B, z' * b = b * z' := by
    intro b hb
    have hmem : n * b * n⁻¹ ∈ conjSub a⁻¹ (imB β ε Bbar) := by
      rw [hB'eq, mem_conjSub]
      have e : n⁻¹ * (n * b * n⁻¹) * n = b := by group
      rw [e]
      exact hb
    have h1 := hcomm _ hmem
    have hnz' : z' * n⁻¹ = n⁻¹ * z' := by
      calc z' * n⁻¹ = n⁻¹ * (n * z') * n⁻¹ := by group
        _ = n⁻¹ * (z' * n) * n⁻¹ := by rw [hnz]
        _ = n⁻¹ * z' := by group
    have h2 : n * b * n⁻¹ * z' = n * (b * z') * n⁻¹ := by
      calc n * b * n⁻¹ * z' = n * b * (n⁻¹ * z') := by group
        _ = n * b * (z' * n⁻¹) := by rw [hnz']
        _ = n * (b * z') * n⁻¹ := by group
    have h3 : z' * (n * b * n⁻¹) = n * (z' * b) * n⁻¹ := by
      calc z' * (n * b * n⁻¹) = (z' * n) * b * n⁻¹ := by group
        _ = (n * z') * b * n⁻¹ := by rw [hnz]
        _ = n * (z' * b) * n⁻¹ := by group
    rw [h2, h3] at h1
    have h4 : b * z' = z' * b := by
      have := congrArg (fun y => n⁻¹ * y * n) h1
      simpa [mul_assoc] using this
    exact h4.symm
  exact hz'1 (D.centS z' (D.Z_le_S haZ) hzc)

theorem burnsideF447_clause1 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {Bbar B0bar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    (imB β ε (f447Ybar Gp M₂ Bbar) ≠ ⊥ ∨
      (f = 2 ∧ MiOne β ε = oPPrime 2 (GiOne Gp β ε) ∧ MiTwo β ε = oPPrime 2 (GiTwo Gp β ε) ∧
        imB β ε B0bar = imB β ε Bbar ∧ Nat.card ↥(imB β ε Bbar) = 3 ∧
        Odd (Nat.card ↥(Subgroup.centralizer ((imB β ε Bbar : Subgroup M) : Set M))))) := by
  have hb1 : Function.Injective (burnsideF4d_bOne β ε) := hyp.inj.comp (f1_injective β hyp.faithful)
  have hb2 : Function.Injective (burnsideF4d_bTwo β ε) := hyp.inj.comp (f2_injective β hyp.faithful)
  by_cases hY : f447Ybar Gp M₂ Bbar = ⊥
  · right
    obtain ⟨hf2, h1, h2, hB0eq, hcard⟩ := burnsideF447_clause1_E hyp hB hB0 hY
    refine ⟨hf2, ?_, ?_, ?_, ?_, burnsideF447_odd_centralizer hyp hB⟩
    · rw [burnsideF4d_GiOne_eq, burnsideF4d_MiOne_eq,
        burnsideF4d_subImg_oPPrime _ hb1 (inf_le_right : Gp ⊓ M₁ ≤ M₁) 2, ← h1]
    · rw [burnsideF4d_GiTwo_eq, burnsideF4d_MiTwo_eq,
        burnsideF4d_subImg_oPPrime _ hb2 (inf_le_right : Gp ⊓ M₂ ≤ M₂) 2, ← h2]
    · rw [hB0eq]
    · rw [burnsideF4d_Z4_imB_eq β ε hB.1, card_subImg _ hb1 (hB.1.trans inf_le_left)]
      exact hcard
  · left
    intro hbot
    apply hY
    have hYB : f447Ybar Gp M₂ Bbar ≤ Bbar := fun b hb => hb.1
    have hYle : f447Ybar Gp M₂ Bbar ≤ M₁ ⊓ M₂ := hYB.trans hB.1
    rw [burnsideF4d_Z4_imB_eq β ε hYle] at hbot
    rw [eq_bot_iff]
    intro y hy
    have hyM : y ∈ M₁ := (hYle hy).1
    have h1 := mem_subImg_of_mem (burnsideF4d_bOne β ε) hyM hy
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨y, hyM⟩ : ↥M₁) = 1 := hb1 (h1.trans (map_one _).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)

end Clause1M

section Sl2

open CFSG.Open

variable {F : Type} [Field F]

@[expose] def burnsideF447_yEl (s : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def burnsideF447_dEl (c : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

theorem burnsideF447_coe_yEl (s : F) :
    ((burnsideF447_yEl s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; s, 1] := rfl

theorem burnsideF447_coe_dEl (c : Fˣ) :
    ((burnsideF447_dEl c : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] := rfl

@[expose] def burnsideF447_xEl (s : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem burnsideF447_coe_xEl (s : F) :
    ((burnsideF447_xEl s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, s; 0, 1] := rfl

theorem burnsideF447_xEl_mul (s t : F) :
    burnsideF447_xEl s * burnsideF447_xEl t = burnsideF447_xEl (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF447_coe_xEl, Matrix.mul_apply, Fin.sum_univ_two,
    add_comm]

theorem burnsideF447_xEl_zero : burnsideF447_xEl (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF447_coe_xEl]

theorem burnsideF447_xEl_sq [CharP F 2] (s : F) :
    burnsideF447_xEl s * burnsideF447_xEl s = 1 := by
  rw [burnsideF447_xEl_mul, CharTwo.add_self_eq_zero, burnsideF447_xEl_zero]

@[expose] def burnsideF447_wEl [CharP F 2] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    simp only [Matrix.det_fin_two_of]
    linear_combination -h2⟩

theorem burnsideF447_wEl_conj [CharP F 2] (s : F) :
    burnsideF447_wEl * burnsideF447_xEl s * burnsideF447_wEl⁻¹ = burnsideF447_yEl s := by
  have hw : (burnsideF447_wEl : Matrix.SpecialLinearGroup (Fin 2) F) *
      burnsideF447_wEl = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideF447_wEl, Matrix.mul_apply, Fin.sum_univ_two]
  rw [inv_eq_of_mul_eq_one_right hw]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideF447_wEl, burnsideF447_coe_xEl, burnsideF447_coe_yEl, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem burnsideF447_sl2_invol_conj [Finite F] [CharP F 2] {B : Matrix.SpecialLinearGroup (Fin 2) F}
    (hB : B * B = 1) (hB1 : B ≠ 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g * burnsideF447_yEl 1 * g⁻¹ = B := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (B : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe B
    rwa [hM, Matrix.det_fin_two_of] at this
  have hBB := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
    (X : Matrix (Fin 2) (Fin 2) F)) hB
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hM] at hBB
  have e00 := congrFun (congrFun hBB 0) 0
  have e11 := congrFun (congrFun hBB 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have h1 : a * (a - d) = 0 := by linear_combination e00 - hdet - (b * c) * h2
  have h3 : d * (d - a) = 0 := by linear_combination e11 - hdet - (b * c) * h2
  have hda : d = a := by
    by_contra hne
    have hne' : a - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hne'' : d - a ≠ 0 := sub_ne_zero.mpr hne
    have ha0 : a = 0 := (mul_eq_zero.mp h1).resolve_right hne'
    have hd0 : d = 0 := (mul_eq_zero.mp h3).resolve_right hne''
    exact hne (by rw [ha0, hd0])
  subst hda
  have hsq : d * d + b * c = 1 := by linear_combination hdet + (b * c) * h2
  haveI : Fintype F := Fintype.ofFinite F
  by_cases hc : c = 0
  ·
    have hd1 : d = 1 := by
      have h : (d - 1) * (d - 1) = 0 := by
        rw [hc] at hsq
        linear_combination hsq - d * h2 + h2
      have := mul_self_eq_zero.mp h
      linear_combination this
    have hb : b ≠ 0 := by
      intro hb0
      apply hB1
      apply Subtype.ext
      rw [hM, hb0, hc, hd1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) b⁻¹
    have hrb : r * r * b = 1 := by rw [← hr]; field_simp
    have hdetg : (!![0, r * b; r, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination (-1 : F) * hrb - h2
    obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
        (g : Matrix (Fin 2) (Fin 2) F) = !![0, r * b; r, 0] := ⟨⟨_, hdetg⟩, rfl⟩
    refine ⟨g, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hM, hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideF447_coe_yEl, Matrix.mul_apply, Fin.sum_univ_two, hc, hd1] <;> ring
  ·
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c⁻¹
    have hrc : r * r * c = 1 := by rw [← hr]; field_simp
    have hdetg : (!![r, r * (d + 1); 0, r * c] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hrc
    obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
        (g : Matrix (Fin 2) (Fin 2) F) = !![r, r * (d + 1); 0, r * c] := ⟨⟨_, hdetg⟩, rfl⟩
    refine ⟨g, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hM, hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideF447_coe_yEl, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination r * h2
    · linear_combination (-r) * hsq
    · ring
    · linear_combination (-(r * c * d)) * h2

theorem burnsideF447_sl2_invol_conj_x [Finite F] [CharP F 2]
    {B : Matrix.SpecialLinearGroup (Fin 2) F} (hB : B * B = 1) (hB1 : B ≠ 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g * burnsideF447_xEl 1 * g⁻¹ = B := by
  obtain ⟨g, hg⟩ := burnsideF447_sl2_invol_conj hB hB1
  refine ⟨g * burnsideF447_wEl, ?_⟩
  rw [← hg, ← burnsideF447_wEl_conj]
  group

theorem burnsideF447_sl2_not_solvable [Finite F] (hF : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro hsolv
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  haveI : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective
      (f := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨a, b, hab⟩ := CFSG.Walter.psl2_exists_mul_ne_mul F hF
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

theorem burnsideF447_sl2_cent_dEl {c : Fˣ} (hc : (c : F) ≠ ((c⁻¹ : Fˣ) : F))
    {B : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : B * burnsideF447_dEl c = burnsideF447_dEl c * B) : ∃ d : Fˣ, B = burnsideF447_dEl d := by
  obtain ⟨a, b, c', d', hM⟩ : ∃ a b c' d' : F, (B : Matrix (Fin 2) (Fin 2) F) = !![a, b; c', d'] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d' - b * c' = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe B
    rwa [hM, Matrix.det_fin_two_of] at this
  have hcomm := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
    (X : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, hM, burnsideF447_coe_dEl] at hcomm
  have e01 := congrFun (congrFun hcomm 0) 1
  have e10 := congrFun (congrFun hcomm 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  have hc2 : (c : F) ≠ (c : F)⁻¹ := by simpa using hc
  have hb : b = 0 := by
    have : b * ((c : F)⁻¹ - (c : F)) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hc2))
  have hc'0 : c' = 0 := by
    have : c' * ((c : F) - (c : F)⁻¹) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hc2)
  subst hb hc'0
  have ha : a ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  refine ⟨Units.mk0 a ha, ?_⟩
  apply Subtype.ext
  rw [hM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF447_coe_dEl]
  field_simp
  linear_combination hdet

end Sl2

section Blk

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.L3.P3

variable {F : Type} [Field F]

@[expose] def burnsideF447_blkMat (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

theorem burnsideF447_blkMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    burnsideF447_blkMat (A * B) = burnsideF447_blkMat A * burnsideF447_blkMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideF447_blkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem burnsideF447_blkMat_one : burnsideF447_blkMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF447_blkMat]

theorem burnsideF447_det_blkMat (B : Matrix (Fin 2) (Fin 2) F) :
    (burnsideF447_blkMat B).det = B.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [burnsideF447_blkMat]

@[expose] def burnsideF447_blk :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun B := ⟨burnsideF447_blkMat (B : Matrix (Fin 2) (Fin 2) F), by
    rw [burnsideF447_det_blkMat]; exact B.2⟩
  map_one' := Subtype.ext burnsideF447_blkMat_one
  map_mul' A B := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact burnsideF447_blkMat_mul _ _)

theorem burnsideF447_coe_blk (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((burnsideF447_blk B : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      burnsideF447_blkMat (B : Matrix (Fin 2) (Fin 2) F) := rfl

@[expose] noncomputable def burnsideF447_lv :
    Matrix.SpecialLinearGroup (Fin 2) F →* projectiveSL 3 F :=
  (proj 3 F).comp burnsideF447_blk

theorem burnsideF447_blk_scalar {C : Matrix.SpecialLinearGroup (Fin 2) F} {c : F}
    (h : ((burnsideF447_blk C : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) c) : C = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h12 := congrFun (congrFun h 1) 2
  have h21 := congrFun (congrFun h 2) 1
  have h22 := congrFun (congrFun h 2) 2
  simp [burnsideF447_coe_blk, burnsideF447_blkMat] at h00 h11 h12 h21 h22
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [← h00] using h11
  · simpa using h12
  · simpa using h21
  · simpa [← h00] using h22

theorem burnsideF447_lv_injective :
    Function.Injective (burnsideF447_lv (F := F)) := by
  intro A B h
  have h1 : proj 3 F (burnsideF447_blk (A * B⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv]
    have : proj 3 F (burnsideF447_blk A) = proj 3 F (burnsideF447_blk B) := h
    rw [this, mul_inv_cancel]
  obtain ⟨c, hc, hmat⟩ := mem_scalars.mp (proj_eq_one_iff.mp h1)
  have := burnsideF447_blk_scalar hmat
  exact mul_inv_eq_one.mp this

theorem burnsideF447_lv_mem_normalizer_V1 [Finite F] [CharP F 2]
    (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    burnsideF447_lv B ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  rw [normalizer_V1_eq]
  refine ⟨burnsideF447_blk B, mem_Q3_zero_iff.mpr ?_, rfl⟩
  simp [burnsideF447_coe_blk, burnsideF447_blkMat]

theorem burnsideF447_conj_lv (x y : Fˣ) (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    conjAut 3 F (burnsideF447_diagGL x y y) (burnsideF447_lv B) = burnsideF447_lv B := by
  have hy : (y : F) ≠ 0 := y.ne_zero
  have hx : (x : F) ≠ 0 := x.ne_zero
  show conjAut 3 F (burnsideF447_diagGL x y y) (proj 3 F (burnsideF447_blk B)) =
    proj 3 F (burnsideF447_blk B)
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  change Matrix.diagonal _ * burnsideF447_blkMat _ * Matrix.diagonal _ = burnsideF447_blkMat _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideF447_blkMat, Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

end Blk

section Lam

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.L3.P3

variable {F : Type} [Field F]

theorem burnsideF447_dEl_mul (c d : Fˣ) :
    burnsideF447_dEl c * burnsideF447_dEl d = burnsideF447_dEl (c * d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideF447_coe_dEl, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[expose] def burnsideF447_dElHom : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := burnsideF447_dEl
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideF447_coe_dEl]
  map_mul' c d := (burnsideF447_dEl_mul c d).symm

@[expose] noncomputable def burnsideF447_Lam : Subgroup (projectiveSL 3 F) :=
  (burnsideF447_lv (F := F)).range

@[expose] noncomputable def burnsideF447_Xroot [CharP F 2] : Subgroup (projectiveSL 3 F) where
  carrier := {p | ∃ s : F, p = burnsideF447_lv (burnsideF447_xEl s)}
  one_mem' := ⟨0, by rw [burnsideF447_xEl_zero, map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, by rw [← burnsideF447_xEl_mul, map_mul]⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    rw [← map_inv, inv_eq_of_mul_eq_one_right (burnsideF447_xEl_sq s)]

theorem burnsideF447_Xroot_le_Lam [CharP F 2] :
    burnsideF447_Xroot (F := F) ≤ burnsideF447_Lam := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, rfl⟩

theorem burnsideF447_Xroot_elemAbelian [CharP F 2] :
    IsElemAbelian 2 (burnsideF447_Xroot (F := F)) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, s, rfl⟩ ⟨_, t, rfl⟩
    apply Subtype.ext
    show burnsideF447_lv (burnsideF447_xEl s) * burnsideF447_lv (burnsideF447_xEl t) =
      burnsideF447_lv (burnsideF447_xEl t) * burnsideF447_lv (burnsideF447_xEl s)
    rw [← map_mul, ← map_mul, burnsideF447_xEl_mul, burnsideF447_xEl_mul, add_comm]
  · rintro _ ⟨s, rfl⟩
    rw [pow_two, ← map_mul, burnsideF447_xEl_sq, map_one]

theorem burnsideF447_Xroot_card [CharP F 2] :
    Nat.card (burnsideF447_Xroot (F := F)) = Nat.card F := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun s : F =>
    (⟨burnsideF447_lv (burnsideF447_xEl s), s, rfl⟩ : burnsideF447_Xroot (F := F))) ⟨?_, ?_⟩)
  · intro s t h
    have h1 := burnsideF447_lv_injective (congrArg Subtype.val h)
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
      (X : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simpa [burnsideF447_coe_xEl] using this
  · rintro ⟨_, s, rfl⟩
    exact ⟨s, rfl⟩

theorem burnsideF447_lv_xEl (s : F) : burnsideF447_lv (burnsideF447_xEl s) = yP s := by
  show proj 3 F (burnsideF447_blk (burnsideF447_xEl s)) = proj 3 F (yMat s)
  congr 1

theorem burnsideF447_Lam_invol_conj [Finite F] [CharP F 2] {p : projectiveSL 3 F}
    (hp : p ∈ burnsideF447_Lam) (hp2 : p * p = 1) (hp1 : p ≠ 1) :
    ∃ h ∈ burnsideF447_Lam, h * burnsideF447_lv (burnsideF447_xEl 1) * h⁻¹ = p := by
  obtain ⟨B, rfl⟩ := hp
  have hBB : B * B = 1 := burnsideF447_lv_injective (by rw [map_mul, hp2, map_one])
  have hB1 : B ≠ 1 := fun h => hp1 (by rw [h, map_one])
  obtain ⟨g, hg⟩ := burnsideF447_sl2_invol_conj_x hBB hB1
  exact ⟨burnsideF447_lv g, ⟨g, rfl⟩, by rw [← map_inv, ← map_mul, ← map_mul, hg]⟩

theorem burnsideF447_Lam_not_solvable [Finite F] (hF : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable ↥(burnsideF447_Lam (F := F)) := by
  intro h
  haveI : Group.IsSolvable ↥(burnsideF447_lv (F := F)).range := h
  apply burnsideF447_sl2_not_solvable hF
  exact Group.isSolvable_of_isSolvable_injective
    (f := (burnsideF447_lv (F := F)).rangeRestrict) (by
      intro a b hab
      exact burnsideF447_lv_injective (congrArg Subtype.val hab))

theorem burnsideF447_Lam_card [Finite F] :
    Nat.card (burnsideF447_Lam (F := F)) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [burnsideF447_Lam, ← Nat.card_congr (MonoidHom.ofInjective burnsideF447_lv_injective).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]

@[expose] noncomputable def burnsideF447_T0 : Subgroup (projectiveSL 3 F) :=
  ((burnsideF447_lv (F := F)).comp burnsideF447_dElHom).range

theorem burnsideF447_Lam_cent_T0 [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {p : projectiveSL 3 F} (hp : p ∈ burnsideF447_Lam)
    (h : ∀ x ∈ burnsideF447_T0 (F := F), p * x = x * p) : p ∈ burnsideF447_T0 (F := F) := by
  obtain ⟨B, rfl⟩ := hp
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hcard : 1 < Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  haveI : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨c, hc1⟩ := exists_ne (1 : Fˣ)
  have hc : (c : F) ≠ ((c⁻¹ : Fˣ) : F) := by
    intro hcc
    apply hc1
    have h1 : (c : F) * (c : F) = 1 := by
      have := congrArg (fun x : F => x * (c : F)) hcc
      simpa [mul_comm] using this
    have h3 : ((c : F) - 1) * ((c : F) - 1) = 0 := by linear_combination h1 - (c : F) * h2 + h2
    have := mul_self_eq_zero.mp h3
    exact Units.ext (by rw [Units.val_one]; linear_combination this)
  have hB : B * burnsideF447_dEl c = burnsideF447_dEl c * B :=
    burnsideF447_lv_injective (by
      rw [map_mul, map_mul]
      exact h _ ⟨c, rfl⟩)
  obtain ⟨d, rfl⟩ := burnsideF447_sl2_cent_dEl hc hB
  exact ⟨d, rfl⟩

end Lam

section YChar

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF

theorem burnsideF447_conj_diag_xP {F : Type} [Field F] (x y z : Fˣ) (t : F) :
    conjAut 3 F (burnsideF447_diagGL x y z) (xP t) = xP ((x : F) * ((y⁻¹ : Fˣ) : F) * t) := by
  show conjAut 3 F _ (proj 3 F (xMat t)) = proj 3 F (xMat _)
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  change Matrix.diagonal _ * xM t * Matrix.diagonal _ = xM _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xM, Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem burnsideF447_conj_diag_yP {F : Type} [Field F] (x y z : Fˣ) (t : F) :
    conjAut 3 F (burnsideF447_diagGL x y z) (yP t) = yP ((y : F) * ((z⁻¹ : Fˣ) : F) * t) := by
  show conjAut 3 F _ (proj 3 F (yMat t)) = proj 3 F (yMat _)
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  change Matrix.diagonal _ * yM t * Matrix.diagonal _ = yM _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yM, Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem burnsideF447_conj_diag_wP {F : Type} [Field F] (x y z : Fˣ) (t : F) :
    conjAut 3 F (burnsideF447_diagGL x y z) (wP t) = wP ((x : F) * ((z⁻¹ : Fˣ) : F) * t) := by
  show conjAut 3 F _ (proj 3 F (wMat t)) = proj 3 F (wMat _)
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  change Matrix.diagonal _ * wM t * Matrix.diagonal _ = wM _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

end YChar

section YChar2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E] {f : ℕ}
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_Qbar_eq (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E)) :
    pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂)) = (V1 : Subgroup (projectiveSL 3 F)).map Φ := by
  rw [burnsideF4d_pCoreOf_oPPrime]
  have : Gp ⊓ M₂ = (Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F))).map Φ := by
    rw [h₂, ← normalizer_map_inf_range Φ C.hΦ V1, C.hrange, inf_comm]
  rw [this, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective Φ C.hΦ,
    CFSG.GH74.QTGen4.DSGen4.L34.pCoreOf_normalizer_V1]

theorem burnsideF447_yP_mem_V1 {t : F} (h : yP t ∈ (V1 : Subgroup (projectiveSL 3 F))) :
    t = 0 := by
  obtain ⟨a, c, hac⟩ := mem_V1.mp h
  have h2 := xP_wP_eq_yP_wP (a := a) (b := t) (c := c) (c' := 0) (by rw [wP_zero, mul_one, ← hac])
  exact h2.2.1

theorem burnsideF447_Ybar_diag [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ Bbar : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E))
    (hB : Bbar = burnsideF447_Bt Φ) {y : E} (hy : y ∈ f447Ybar Gp M₂ Bbar) :
    ∃ x y' : Fˣ, ρ y = conjAut 3 F (burnsideF447_diagGL x y' y') := by
  have hyB : y ∈ burnsideF447_Bt Φ := hB ▸ hy.1
  obtain ⟨δ, t₁, t₂, σ, hdiag⟩ := burnsideF447_diag C.hq C.hΦ C.hΦρ C.hE hyB.1 hyB.2
  have hρ : ρ y = conjAut 3 F (burnsideF447_diagGL ((δ * 1) * t₁) (1 * t₂) (1 * (t₁ * t₂)⁻¹)) *
      fieldAut 3 F σ := by
    rw [hdiag, burnsideF447_nuDiagGL_eq, ← conjAut_toGL, burnsideF447_toGL_dMat, ← map_mul,
      burnsideF447_diagGL_mul]
  have htest : ∀ s : F, yP ((((1 * t₂ : Fˣ) : F) * (((1 * (t₁ * t₂)⁻¹ : Fˣ)⁻¹ : Fˣ) : F)) * σ s + s) ∈
      (V1 : Subgroup (projectiveSL 3 F)) := by
    intro s
    have hp : yP s ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) := yP_mem_normalizer_V1 s
    have hxM : Φ (yP s) ∈ M₂ := by
      rw [h₂]
      exact map_mem_normalizer_map Φ hp
    have hxG : Φ (yP s) ∈ Gp := by
      rw [← C.hrange]
      exact ⟨_, rfl⟩
    have hx2 : orderOf (Φ (yP s)) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two, ← map_mul, yP_mul_self, map_one]
    have hx2' : orderOf (Φ (yP s)) ∣ 2 ^ 1 := by simpa using hx2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx2'
    have hxL : Φ (yP s) ∈ oPPrime 2 (Gp ⊓ M₂) :=
      Subgroup.subset_closure ⟨⟨hxG, hxM⟩, k, hk⟩
    have hc := hy.2.2.2 _ hxL
    rw [burnsideF447_Qbar_eq C h₂] at hc
    have h1 : ρ y (yP s) * (yP s)⁻¹ ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
      apply (Subgroup.mem_map_iff_mem C.hΦ).mp
      rw [map_mul, map_inv, C.hΦρ]
      exact hc
    rw [hρ, MulAut.mul_apply, fieldAut_yP, burnsideF447_conj_diag_yP, yP_inv, ← yP_add] at h1
    exact h1
  have hlam : ∀ s : F, (((1 * t₂ : Fˣ) : F) * (((1 * (t₁ * t₂)⁻¹ : Fˣ)⁻¹ : Fˣ) : F)) * σ s = s := by
    intro s
    have := burnsideF447_yP_mem_V1 (htest s)
    linear_combination this - s * CharP.cast_eq_zero F 2
  have hl1 : ((1 * t₂ : Fˣ) : F) * (((1 * (t₁ * t₂)⁻¹ : Fˣ)⁻¹ : Fˣ) : F) = 1 := by
    have := hlam 1
    rwa [map_one, mul_one] at this
  have hσ1 : σ = 1 := by
    refine RingEquiv.ext fun s => ?_
    have := hlam s
    rw [hl1, one_mul] at this
    exact this
  have hd : (1 * (t₁ * t₂)⁻¹ : Fˣ) = 1 * t₂ := by
    have : (1 * t₂ : Fˣ) * (1 * (t₁ * t₂)⁻¹)⁻¹ = 1 := Units.ext hl1
    rw [mul_inv_eq_one] at this
    exact this.symm
  refine ⟨(δ * 1) * t₁, 1 * t₂, ?_⟩
  rw [hρ, hσ1, map_one, mul_one, hd]

end YChar2

section DiagLemmas

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E] {f : ℕ}
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_diagGL_scalar (x : Fˣ) :
    burnsideF447_diagGL (F := F) x x x = Matrix.GeneralLinearGroup.scalar (Fin 3) x := by
  apply Units.ext
  show Matrix.diagonal _ = (Matrix.scalar (Fin 3) (x : F))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem burnsideF447_conjAut_diagGL_scalar (x : Fˣ) :
    conjAut 3 F (burnsideF447_diagGL x x x) = 1 := by
  rw [burnsideF447_diagGL_scalar]
  exact burnsideF447_conjAut_scalar x

theorem burnsideF447_conj_diagGL_U (a b c : Fˣ) {p : projectiveSL 3 F}
    (hp : p ∈ projUnitriangular 3 F) :
    conjAut 3 F (burnsideF447_diagGL a b c) p ∈ projUnitriangular 3 F := by
  obtain ⟨c', a', b', rfl⟩ := mem_Ubar.mp hp
  rw [map_mul, map_mul, burnsideF447_conj_diag_wP, burnsideF447_conj_diag_xP,
    burnsideF447_conj_diag_yP]
  exact mem_Ubar.mpr ⟨_, _, _, rfl⟩

theorem burnsideF447_conj_diagGL_dMat (a b c t₁ t₂ : Fˣ) :
    conjAut 3 F (burnsideF447_diagGL a b c) (proj 3 F (dMat t₁ t₂)) = proj 3 F (dMat t₁ t₂) := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hb : (b : F) ≠ 0 := b.ne_zero
  have hc : (c : F) ≠ 0 := c.ne_zero
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_dMat]
  change Matrix.diagonal ![(a : F), (b : F), (c : F)] *
      Matrix.diagonal ![(t₁ : F), (t₂ : F), (((t₁ * t₂)⁻¹ : Fˣ) : F)] *
      Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F)] =
    Matrix.diagonal ![(t₁ : F), (t₂ : F), (((t₁ * t₂)⁻¹ : Fˣ) : F)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.mul_apply] <;> field_simp

theorem burnsideF447_mem_Bt_of_diag (C : burnsideF447_Ctx f Φ ρ Gp) {b : E} {x y z : Fˣ}
    (h : ρ b = conjAut 3 F (burnsideF447_diagGL x y z)) : b ∈ burnsideF447_Bt Φ := by
  refine ⟨(burnsideF447_normalizer_iff C.hΦ C.hΦρ b _).mpr fun p => ?_,
    (burnsideF447_normalizer_iff C.hΦ C.hΦρ b _).mpr fun p => ?_⟩
  · rw [h]
    constructor
    · exact burnsideF447_conj_diagGL_U x y z
    · intro hq
      have := burnsideF447_conj_diagGL_U x⁻¹ y⁻¹ z⁻¹ hq
      rwa [← burnsideF447_diagGL_inv, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply] at this
  · rw [h]
    constructor
    · intro hp
      obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hp
      rw [burnsideF447_conj_diagGL_dMat]
      exact dP_mem_torus3 _ _
    · intro hq
      have key : conjAut 3 F (burnsideF447_diagGL x y z) p ∈ torus3 F := hq
      have : p = conjAut 3 F (burnsideF447_diagGL x⁻¹ y⁻¹ z⁻¹)
          (conjAut 3 F (burnsideF447_diagGL x y z) p) := by
        rw [← burnsideF447_diagGL_inv, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          MulAut.one_apply]
      rw [this]
      obtain ⟨t₁, t₂, ht⟩ := mem_torus3.mp key
      rw [ht, burnsideF447_conj_diagGL_dMat]
      exact dP_mem_torus3 _ _

theorem burnsideF447_s12_diagGL (a b c : Fˣ) :
    Matrix.SpecialLinearGroup.toGL (s₁₂Mat : Matrix.SpecialLinearGroup (Fin 3) F) *
      burnsideF447_diagGL a b c *
      (Matrix.SpecialLinearGroup.toGL (s₁₂Mat : Matrix.SpecialLinearGroup (Fin 3) F))⁻¹ =
    burnsideF447_diagGL b a c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change s₁₂M * Matrix.diagonal _ = Matrix.diagonal _ * s₁₂M
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s₁₂M, Matrix.mul_apply, Matrix.diagonal_apply]

theorem burnsideF447_xP_yP_inj {a b a' b' : F} (h : xP a * yP b = xP a' * yP b') :
    a = a' ∧ b = b' := by
  have hU1 : xMat a * yMat b ∈ unitriangular 3 F :=
    mul_mem (xMat_mem_unitriangular a) (yMat_mem_unitriangular b)
  have hU2 : xMat a' * yMat b' ∈ unitriangular 3 F :=
    mul_mem (xMat_mem_unitriangular a') (yMat_mem_unitriangular b')
  have hh : proj 3 F (xMat a * yMat b) = proj 3 F (xMat a' * yMat b') := by
    rw [map_mul, map_mul]
    exact h
  have h' := LinearFlag.proj_injOn_unitriangular 3 hU1 hU2 hh
  have hm : (xM a * yM b) = (xM a' * yM b') := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) F =>
      (X : Matrix (Fin 3) (Fin 3) F)) h'
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have e01 := congrFun (congrFun hm 0) 1
  have e12 := congrFun (congrFun hm 1) 2
  simp [xM, yM, Matrix.mul_apply, Fin.sum_univ_three] at e01 e12
  exact ⟨e01, e12⟩

theorem burnsideF447_centralizer_diag_U {x₀ y₀ : Fˣ} (hxy : x₀ ≠ y₀) {v : projectiveSL 3 F}
    (hv : v ∈ projUnitriangular 3 F)
    (h : conjAut 3 F (burnsideF447_diagGL y₀ x₀ y₀) v = v) : ∃ c : F, v = wP c := by
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hv
  rw [map_mul, map_mul, burnsideF447_conj_diag_wP, burnsideF447_conj_diag_xP,
    burnsideF447_conj_diag_yP] at h
  have hc : (y₀ : F) * ((y₀⁻¹ : Fˣ) : F) * c = c := by
    have : (y₀ : F) * ((y₀⁻¹ : Fˣ) : F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, one_mul]
  rw [hc] at h
  have h2 : xP ((y₀ : F) * ((x₀⁻¹ : Fˣ) : F) * a) * yP ((x₀ : F) * ((y₀⁻¹ : Fˣ) : F) * b) =
      xP a * yP b := by
    exact mul_left_cancel (a := wP c) (by rw [← mul_assoc, ← mul_assoc]; exact h)
  obtain ⟨h3, h4⟩ := burnsideF447_xP_yP_inj h2
  have hx0 : (x₀ : F) ≠ 0 := x₀.ne_zero
  have hy0 : (y₀ : F) ≠ 0 := y₀.ne_zero
  have hne : (y₀ : F) * ((x₀⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h5
    apply hxy
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val] at h5
    field_simp at h5
    exact h5.symm
  have ha : a = 0 := by
    have : a * ((y₀ : F) * ((x₀⁻¹ : Fˣ) : F) - 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hne' : (x₀ : F) * ((y₀⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h5
    apply hxy
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val] at h5
    field_simp at h5
    exact h5
  have hb : b = 0 := by
    have : b * ((x₀ : F) * ((y₀⁻¹ : Fˣ) : F) - 1) = 0 := by linear_combination h4
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne')
  exact ⟨c, by rw [ha, hb, xP_zero, yP_zero]; group⟩

theorem burnsideF447_comm_split {G : Type*} [Group G] {S B : Subgroup G}
    (hSB : ∀ g, g ∈ S → g ∈ B → g = 1) (hSn : ∀ y ∈ B, ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    {u b y : G} (hu : u ∈ S) (hb : b ∈ B) (hy : y ∈ B)
    (h : (u * b) * y = y * (u * b)) : b * y = y * b ∧ u * y = y * u := by
  have h1 : y⁻¹ * (b * y * b⁻¹) = (y⁻¹ * u⁻¹ * y) * u := by
    have e : b * y * b⁻¹ = u⁻¹ * y * u := by
      calc b * y * b⁻¹ = u⁻¹ * ((u * b) * y) * b⁻¹ * 1 * b⁻¹⁻¹ * b⁻¹ := by group
        _ = u⁻¹ * (y * (u * b)) * b⁻¹ := by rw [h]; group
        _ = u⁻¹ * y * u := by group
    rw [e]
    group
  have h2 : y⁻¹ * (b * y * b⁻¹) ∈ B :=
    B.mul_mem (B.inv_mem hy) (B.mul_mem (B.mul_mem hb hy) (B.inv_mem hb))
  have h3 : (y⁻¹ * u⁻¹ * y) * u ∈ S := by
    refine S.mul_mem ?_ hu
    have := hSn y⁻¹ (B.inv_mem hy) u⁻¹ (S.inv_mem hu)
    simpa using this
  have h4 : y⁻¹ * (b * y * b⁻¹) = 1 := hSB _ (h1 ▸ h3) h2
  constructor
  · have : b * y * b⁻¹ = y := by
      have := congrArg (fun g => y * g) h4
      simpa using this
    calc b * y = (b * y * b⁻¹) * b := by group
      _ = y * b := by rw [this]
  · have h5 : (y⁻¹ * u⁻¹ * y) * u = 1 := h1 ▸ h4
    have h6 : u⁻¹ * y * u = y := by
      calc u⁻¹ * y * u = y * (y⁻¹ * u⁻¹ * y * u) := by group
        _ = y := by rw [h5]; group
    have h7 : y * u = u * y := by
      calc y * u = u * (u⁻¹ * y * u) := by group
        _ = u * y := by rw [h6]
    exact h7.symm

theorem burnsideF447_aut_eq_one {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) {σ : F ≃+* F}
    (hcubes : ∀ a : Fˣ, σ ((a ^ 3 : Fˣ) : F) = ((a ^ 3 : Fˣ) : F))
    (hlarge : 3 ≤ f ∨ (f = 2 ∧ ∃ a₀ : F, a₀ ≠ 0 ∧ a₀ ≠ 1 ∧ σ a₀ = a₀)) : σ = 1 := by
  by_contra hne
  have hσf : σ ^ f = 1 := autField_pow_eq_one hf hF σ
  have hord_dvd : orderOf σ ∣ f := orderOf_dvd_of_pow_eq_one hσf
  have hord2 : 2 ≤ orderOf σ := by
    have h1 : orderOf σ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    have h0 : 0 < orderOf σ := Nat.pos_of_dvd_of_pos hord_dvd (by omega)
    omega
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := F) Nat.prime_two hf hF
  obtain ⟨-, S, hS, hcardS⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hcardS
  have hmemS : ∀ a : F, σ a = a → a ∈ S := by
    intro a hfix
    rw [← SetLike.mem_coe, hS]
    intro τ hτ
    have hτ' : τ ∈ MulAction.stabilizer (F ≃+* F) a :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hfix) hτ
    exact MulAction.mem_stabilizer_iff.mp hτ'
  obtain ⟨h, hh⟩ : ∃ h, h = f / orderOf σ := ⟨_, rfl⟩
  rw [← hh] at hcardS
  have hh2 : 2 * h ≤ f := by
    have := Nat.div_mul_le_self f (orderOf σ)
    rw [← hh] at this
    nlinarith
  have hh1 : 1 ≤ h := by
    have : orderOf σ ≤ f := Nat.le_of_dvd (by omega) hord_dvd
    rw [hh]
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  rcases hlarge with hf3 | ⟨hf2, a₀, ha0, ha1, hfix⟩
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hn : Nat.card Fˣ = 2 ^ f - 1 := by rw [Nat.card_units, hF]
    have hog : orderOf g = 2 ^ f - 1 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hn]
    have hyS : ((g ^ 3 : Fˣ) : F) ∈ S := hmemS _ (hcubes g)
    haveI : Fintype S := Fintype.ofFinite S
    have hy0 : (⟨((g ^ 3 : Fˣ) : F), hyS⟩ : S) ≠ 0 := by
      intro h0
      have : ((g ^ 3 : Fˣ) : F) = 0 := congrArg Subtype.val h0
      exact (g ^ 3).ne_zero this
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨((g ^ 3 : Fˣ) : F), hyS⟩ : S) hy0
    have hpow : (g ^ 3) ^ (2 ^ h - 1) = 1 := by
      have h3 := congrArg Subtype.val h1
      rw [← Nat.card_eq_fintype_card, hcardS] at h3
      exact Units.ext (by simpa using h3)
    have hr : orderOf (g ^ 3) ∣ 2 ^ h - 1 := orderOf_dvd_of_pow_eq_one hpow
    have h2h1 : 2 ≤ 2 ^ h := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh1
    have hrle : orderOf (g ^ 3) ≤ 2 ^ h - 1 := Nat.le_of_dvd (by omega) hr
    have hrg : orderOf (g ^ 3) = orderOf g / Nat.gcd (orderOf g) 3 := orderOf_pow' g (by norm_num : (3 : ℕ) ≠ 0)
    have hmul : orderOf (g ^ 3) * Nat.gcd (orderOf g) 3 = orderOf g := by
      rw [hrg]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    have hgle : Nat.gcd (orderOf g) 3 ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)
    have key : 2 ^ f - 1 ≤ 3 * (2 ^ h - 1) := by
      calc 2 ^ f - 1 = orderOf g := hog.symm
        _ = orderOf (g ^ 3) * Nat.gcd (orderOf g) 3 := hmul.symm
        _ ≤ (2 ^ h - 1) * 3 := Nat.mul_le_mul hrle hgle
        _ = 3 * (2 ^ h - 1) := by ring
    have h4 : 2 ^ (2 * h) ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hh2
    have h2h : 2 ^ (2 * h) = 2 ^ h * 2 ^ h := by rw [two_mul, pow_add]
    rcases Nat.lt_or_ge h 2 with hh_lt | hh_ge
    · have : h = 1 := by omega
      rw [this] at key
      have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
      omega
    · have h5 : 4 ≤ 2 ^ h := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh_ge
      have h6 : 4 * 2 ^ h ≤ 2 ^ h * 2 ^ h := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ h5
      omega
  · have hh1' : h = 1 := by omega
    rw [hh1'] at hcardS
    have hsub : ({0, 1, a₀} : Set F) ⊆ (S : Set F) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact S.zero_mem
      · exact hmemS 1 (map_one σ)
      · exact hmemS _ hfix
    have h3 : ({0, 1, a₀} : Set F).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨0, 1, a₀, zero_ne_one, ha0.symm, ha1.symm, rfl⟩
    have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h3, ← _root_.Nat.card_coe_set_eq] at h4
    have : Nat.card (S : Set F) = 2 := by
      have e : Nat.card (S : Set F) = Nat.card S := rfl
      rw [e, hcardS]
      norm_num
    omega

theorem burnsideF447_rho_Bt (C : burnsideF447_Ctx f Φ ρ Gp) {b : E} (hb : b ∈ burnsideF447_Bt Φ) :
    ∃ (d₀ d₁ d₂ : Fˣ) (σ : F ≃+* F),
      ρ b = conjAut 3 F (burnsideF447_diagGL d₀ d₁ d₂) * fieldAut 3 F σ := by
  obtain ⟨δ, t₁, t₂, σ, hdiag⟩ := burnsideF447_diag C.hq C.hΦ C.hΦρ C.hE hb.1 hb.2
  refine ⟨(δ * 1) * t₁, 1 * t₂, 1 * (t₁ * t₂)⁻¹, σ, ?_⟩
  rw [hdiag, burnsideF447_nuDiagGL_eq, ← conjAut_toGL, burnsideF447_toGL_dMat, ← map_mul,
    burnsideF447_diagGL_mul]

theorem burnsideF447_wP_cent {v : projectiveSL 3 F} (hv : v ∈ projUnitriangular 3 F) (c : F) :
    v * wP c = wP c * v := by
  obtain ⟨c', a, b, rfl⟩ := mem_Ubar.mp hv
  calc wP c' * xP a * yP b * wP c = wP c' * xP a * (yP b * wP c) := by group
    _ = wP c' * xP a * (wP c * yP b) := by rw [wP_mul_yP]
    _ = wP c' * (xP a * wP c) * yP b := by group
    _ = wP c' * (wP c * xP a) * yP b := by rw [wP_mul_xP]
    _ = (wP c' * wP c) * xP a * yP b := by group
    _ = (wP c * wP c') * xP a * yP b := by rw [← wP_add, ← wP_add, add_comm]
    _ = wP c * (wP c' * xP a * yP b) := by group

theorem burnsideF447_rho_s12 (hΦ : Function.Injective Φ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹) :
    ρ (Φ s₁₂P) = conjAut 3 F (Matrix.SpecialLinearGroup.toGL (s₁₂Mat : Matrix.SpecialLinearGroup (Fin 3) F)) := by
  rw [burnsideF447_rho_Phi hΦ hΦρ, conjAut_toGL]
  rfl

theorem burnsideF447_rho_conj_s12 (hΦ : Function.Injective Φ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹) {y : E} {a b c : Fˣ}
    (hy : ρ y = conjAut 3 F (burnsideF447_diagGL a b c)) :
    ρ (Φ s₁₂P * y * (Φ s₁₂P)⁻¹) = conjAut 3 F (burnsideF447_diagGL b a c) := by
  rw [map_mul, map_mul, map_inv, burnsideF447_rho_s12 hΦ hΦρ, hy, ← map_inv, ← map_mul, ← map_mul,
    burnsideF447_s12_diagGL]

theorem burnsideF447_diagGL_inj {a b c a' b' c' : Fˣ}
    (h : burnsideF447_diagGL (F := F) a b c = burnsideF447_diagGL a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun X : GL (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F)) h
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · simpa [burnsideF447_diagGL] using congrFun (congrFun h' 0) 0
  · simpa [burnsideF447_diagGL] using congrFun (congrFun h' 1) 1
  · simpa [burnsideF447_diagGL] using congrFun (congrFun h' 2) 2

theorem burnsideF447_map_diagGL (σ : F ≃+* F) (a b c : Fˣ) :
    Matrix.GeneralLinearGroup.map (σ : F →+* F) (burnsideF447_diagGL a b c) =
      burnsideF447_diagGL (Units.map σ.toMonoidHom a) (Units.map σ.toMonoidHom b)
        (Units.map σ.toMonoidHom c) := by
  apply Units.ext
  show (σ : F →+* F).mapMatrix (Matrix.diagonal _) = Matrix.diagonal _
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp

theorem burnsideF447_diag_field_comm {d₀ d₁ d₂ e₀ e₁ e₂ : Fˣ} {σ : F ≃+* F}
    (h : conjAut 3 F (burnsideF447_diagGL d₀ d₁ d₂) * fieldAut 3 F σ *
        conjAut 3 F (burnsideF447_diagGL e₀ e₁ e₂) =
      conjAut 3 F (burnsideF447_diagGL e₀ e₁ e₂) *
        (conjAut 3 F (burnsideF447_diagGL d₀ d₁ d₂) * fieldAut 3 F σ)) :
    ∃ c : Fˣ, σ (e₀ : F) = c * (e₀ : F) ∧ σ (e₁ : F) = c * (e₁ : F) ∧
      σ (e₂ : F) = c * (e₂ : F) := by
  have h1 := conjAut_mul_fieldAut_mul (n := 3) (K := F)
    (burnsideF447_diagGL d₀ d₁ d₂) (burnsideF447_diagGL e₀ e₁ e₂) σ 1
  have h2 := conjAut_mul_fieldAut_mul (n := 3) (K := F)
    (burnsideF447_diagGL e₀ e₁ e₂) (burnsideF447_diagGL d₀ d₁ d₂) 1 σ
  simp only [map_one, mul_one, one_mul] at h1 h2
  have hid : Matrix.GeneralLinearGroup.map ((1 : F ≃+* F) : F →+* F)
      (burnsideF447_diagGL d₀ d₁ d₂) = burnsideF447_diagGL d₀ d₁ d₂ := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  rw [hid] at h2
  rw [h1, h2] at h
  have h3 := mul_right_cancel h
  have h4 : conjAut 3 F (((burnsideF447_diagGL e₀ e₁ e₂ * burnsideF447_diagGL d₀ d₁ d₂)⁻¹ *
      (burnsideF447_diagGL d₀ d₁ d₂ *
        Matrix.GeneralLinearGroup.map (σ : F →+* F) (burnsideF447_diagGL e₀ e₁ e₂)))) *
      fieldAut 3 F 1 = 1 := by
    rw [map_mul, map_inv, ← h3, map_one, mul_one, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h4
  have hc2 := hc
  rw [burnsideF447_map_diagGL, burnsideF447_diagGL_mul, burnsideF447_diagGL_inv,
    burnsideF447_diagGL_mul, burnsideF447_diagGL_mul, ← burnsideF447_diagGL_scalar] at hc2
  obtain ⟨k0, k1, k2⟩ := burnsideF447_diagGL_inj hc2
  have key : ∀ (d e : Fˣ), c = (e * d)⁻¹ * (d * Units.map σ.toMonoidHom e) →
      σ (e : F) = (c : F) * (e : F) := by
    intro d e hc
    have h1 : (c : F) = ((e : F) * d)⁻¹ * ((d : F) * σ (e : F)) := by
      have := congrArg (fun u : Fˣ => (u : F)) hc
      simpa using this
    have hd : (d : F) ≠ 0 := d.ne_zero
    have he : (e : F) ≠ 0 := e.ne_zero
    rw [h1]
    field_simp
  exact ⟨c, key d₀ e₀ k0, key d₁ e₁ k1, key d₂ e₂ k2⟩

theorem burnsideF447_Ybar_of_diag₁ [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E)) {b : E} {x y z : Fˣ}
    (hρ : ρ b = conjAut 3 F (burnsideF447_diagGL x y z)) (hyz : y = z) :
    b ∈ f447Ybar Gp M₂ (burnsideF447_Bt Φ) := by
  have hb : b ∈ burnsideF447_Bt Φ := burnsideF447_mem_Bt_of_diag C hρ
  have := burnsideF447_Ybar_of_diag C (R₂ := V1) isPGroup_V1 U_le_normalizer_V1 h₂
    (Subgroup.one_mem _) (Bbar := burnsideF447_Bt Φ) (fun y => by simp) hb hρ (Or.inl ⟨rfl, hyz⟩)
  simpa using this

theorem burnsideF447_LV7 [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E))
    (hY : f447Ybar Gp M₂ (burnsideF447_Bt Φ) ≠ ⊥)
    {w : E} (hw : w ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hz : w * Φ (wP 1) = Φ (wP 1) * w)
    (hy : ∀ y ∈ f447Ybar Gp M₂ (burnsideF447_Bt Φ),
      w * (Φ s₁₂P * y * (Φ s₁₂P)⁻¹) = (Φ s₁₂P * y * (Φ s₁₂P)⁻¹) * w) :
    ∃ c : F, ∃ b ∈ f447Ybar Gp M₂ (burnsideF447_Bt Φ),
      Φ s₁₂P * w * (Φ s₁₂P)⁻¹ = Φ (yP c) * b := by
  haveI : Φ.range.Normal := by rw [C.hrange]; infer_instance
  obtain ⟨u₁, hu₁, b, hb, rfl⟩ := burnsideF447_frattini C.hq C.hΦ hw
  obtain ⟨v, hv, rfl⟩ := hu₁
  have hSB : ∀ g, g ∈ (projUnitriangular 3 F).map Φ → g ∈ burnsideF447_Bt Φ → g = 1 :=
    fun g h1 h2 => burnsideF447_Bt_inf_U C.hq C.hΦ h1 h2
  have hSn : ∀ y ∈ burnsideF447_Bt Φ, ∀ s ∈ (projUnitriangular 3 F).map Φ,
      y * s * y⁻¹ ∈ (projUnitriangular 3 F).map Φ :=
    fun y hy s hs => (Subgroup.mem_normalizer_iff.mp hy.1 s).mp hs
  have hsplit : ∀ ŷ ∈ burnsideF447_Bt Φ, (Φ v * b) * ŷ = ŷ * (Φ v * b) →
      b * ŷ = ŷ * b ∧ Φ v * ŷ = ŷ * Φ v :=
    fun ŷ hŷ h => burnsideF447_comm_split (S := (projUnitriangular 3 F).map Φ)
      (B := burnsideF447_Bt Φ) hSB hSn ⟨v, hv, rfl⟩ hb hŷ h
  obtain ⟨d₀, d₁, d₂, σ, hbρ⟩ := burnsideF447_rho_Bt C hb
  have hd02 : d₀ = d₂ := by
    have hvz : Φ v * Φ (wP 1) = Φ (wP 1) * Φ v := by
      rw [← map_mul, ← map_mul, burnsideF447_wP_cent hv 1]
    have hbz : b * Φ (wP 1) = Φ (wP 1) * b := by
      apply mul_left_cancel (a := Φ v)
      calc Φ v * (b * Φ (wP 1)) = (Φ v * b) * Φ (wP 1) := by group
        _ = Φ (wP 1) * (Φ v * b) := hz
        _ = (Φ (wP 1) * Φ v) * b := by group
        _ = (Φ v * Φ (wP 1)) * b := by rw [hvz]
        _ = Φ v * (Φ (wP 1) * b) := by group
    have h1 : ρ b (wP 1) = wP 1 := by
      apply C.hΦ
      rw [C.hΦρ]
      calc b * Φ (wP 1) * b⁻¹ = Φ (wP 1) * b * b⁻¹ := by rw [hbz]
        _ = Φ (wP 1) := by group
    rw [hbρ, MulAut.mul_apply, fieldAut_wP, map_one, burnsideF447_conj_diag_wP] at h1
    have h2 := wP_injective h1
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val, mul_one] at h2
    field_simp at h2
    exact h2
  subst hd02
  obtain ⟨y₀, hy₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hY
  obtain ⟨x₀, y₀', hy₀ρ⟩ := burnsideF447_Ybar_diag C h₂ rfl y₀.2
  have hx₀ : x₀ ≠ y₀' := by
    intro h
    apply hy₀1
    apply Subtype.ext
    show (y₀ : E) = 1
    apply C.hρ
    rw [hy₀ρ, h, burnsideF447_conjAut_diagGL_scalar, map_one]
  have hfix : ∀ y ∈ f447Ybar Gp M₂ (burnsideF447_Bt Φ), ∀ x y' : Fˣ,
      ρ y = conjAut 3 F (burnsideF447_diagGL x y' y') →
      σ ((x : F) * ((y'⁻¹ : Fˣ) : F)) = (x : F) * ((y'⁻¹ : Fˣ) : F) := by
    intro y hy' x y' hρ
    have hρŷ := burnsideF447_rho_conj_s12 C.hΦ C.hΦρ hρ
    have hŷB : Φ s₁₂P * y * (Φ s₁₂P)⁻¹ ∈ burnsideF447_Bt Φ :=
      burnsideF447_mem_Bt_of_diag C hρŷ
    obtain ⟨hb1, -⟩ := hsplit _ hŷB (hy y hy')
    have hcomm : ρ b * ρ (Φ s₁₂P * y * (Φ s₁₂P)⁻¹) = ρ (Φ s₁₂P * y * (Φ s₁₂P)⁻¹) * ρ b := by
      rw [← map_mul, ← map_mul, hb1]
    rw [hbρ, hρŷ] at hcomm
    obtain ⟨c, c0, c1, c2⟩ := burnsideF447_diag_field_comm (σ := σ) hcomm
    have hy'0 : (y' : F) ≠ 0 := y'.ne_zero
    have hc0 : (c : F) ≠ 0 := c.ne_zero
    simp only [Units.val_inv_eq_inv_val]
    rw [map_mul, map_inv₀, c0, c1]
    field_simp
  have hcubes : ∀ a : Fˣ, σ ((a ^ 3 : Fˣ) : F) = ((a ^ 3 : Fˣ) : F) := by
    intro a
    have hρa := burnsideF447_rho_Phi_dMat C.hΦ C.hΦρ (a * a) a⁻¹
    have hz : (a * a * a⁻¹)⁻¹ = a⁻¹ := by group
    rw [hz] at hρa
    have hmem := burnsideF447_Ybar_of_diag₁ C h₂ hρa rfl
    have := hfix _ hmem (a * a) a⁻¹ hρa
    have e3 : (a ^ 3 : Fˣ) = (a * a) * (a⁻¹)⁻¹ := by
      rw [inv_inv, pow_succ, pow_two]
    have e : ((a ^ 3 : Fˣ) : F) = ((a * a : Fˣ) : F) * (((a⁻¹)⁻¹ : Fˣ) : F) := by
      rw [← Units.val_mul, e3]
    rw [e]
    exact this
  have hσ1 : σ = 1 := by
    refine burnsideF447_aut_eq_one (by have := C.hf; omega) C.hF hcubes ?_
    rcases Nat.lt_or_ge f 3 with hlt | hge
    · right
      refine ⟨by have := C.hf; omega, (x₀ : F) * ((y₀'⁻¹ : Fˣ) : F), ?_, ?_,
        hfix _ y₀.2 x₀ y₀' hy₀ρ⟩
      · exact mul_ne_zero x₀.ne_zero (y₀'⁻¹).ne_zero
      · intro h1
        apply hx₀
        apply Units.ext
        simp only [Units.val_inv_eq_inv_val] at h1
        have := y₀'.ne_zero
        field_simp at h1
        exact h1
    · left
      exact hge
  subst hσ1
  rw [map_one, mul_one] at hbρ
  have hvZ : ∃ c : F, v = wP c := by
    have hρŷ₀ := burnsideF447_rho_conj_s12 C.hΦ C.hΦρ hy₀ρ
    have hŷ₀B : Φ s₁₂P * (y₀ : E) * (Φ s₁₂P)⁻¹ ∈ burnsideF447_Bt Φ :=
      burnsideF447_mem_Bt_of_diag C hρŷ₀
    obtain ⟨-, hŷv⟩ := hsplit _ hŷ₀B (hy _ y₀.2)
    have hfixv : ρ (Φ s₁₂P * (y₀ : E) * (Φ s₁₂P)⁻¹) v = v := by
      apply C.hΦ
      rw [C.hΦρ]
      calc (Φ s₁₂P * (y₀ : E) * (Φ s₁₂P)⁻¹) * Φ v * (Φ s₁₂P * (y₀ : E) * (Φ s₁₂P)⁻¹)⁻¹ =
          (Φ v * (Φ s₁₂P * (y₀ : E) * (Φ s₁₂P)⁻¹)) *
            (Φ s₁₂P * (y₀ : E) * (Φ s₁₂P)⁻¹)⁻¹ := by rw [← hŷv]
        _ = Φ v := by group
    rw [hρŷ₀] at hfixv
    exact burnsideF447_centralizer_diag_U hx₀ hv hfixv
  obtain ⟨c, rfl⟩ := hvZ
  refine ⟨c, Φ s₁₂P * b * (Φ s₁₂P)⁻¹, ?_, ?_⟩
  · exact burnsideF447_Ybar_of_diag₁ C h₂ (burnsideF447_rho_conj_s12 C.hΦ C.hΦρ hbρ) rfl
  · have e1 : Φ s₁₂P * Φ (wP c) * (Φ s₁₂P)⁻¹ = Φ (yP c) := by
      rw [← map_inv, ← map_mul, ← map_mul, s12P_conj_wP']
    calc Φ s₁₂P * (Φ (wP c) * b) * (Φ s₁₂P)⁻¹ =
        (Φ s₁₂P * Φ (wP c) * (Φ s₁₂P)⁻¹) * (Φ s₁₂P * b * (Φ s₁₂P)⁻¹) := by group
      _ = Φ (yP c) * (Φ s₁₂P * b * (Φ s₁₂P)⁻¹) := by rw [e1]

end DiagLemmas

section PkgBasic

open CFSG.Open

theorem burnsideF447_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have := hAB a ha b hb
            calc b⁻¹ * a⁻¹ = (a * b)⁻¹ := by group
              _ = (b * a)⁻¹ := by rw [this]
              _ = a⁻¹ * b⁻¹ := by group }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

end PkgBasic

section PkgE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E] {f : ℕ}
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

@[expose] noncomputable def burnsideF447_Ibar (Φ : projectiveSL 3 F →* E) : Subgroup E :=
  (burnsideF447_Lam (F := F)).map Φ

@[expose] noncomputable def burnsideF447_Xbar (Φ : projectiveSL 3 F →* E) : Subgroup E :=
  (burnsideF447_Xroot (F := F)).map Φ

@[expose] noncomputable def burnsideF447_Tbar (Φ : projectiveSL 3 F →* E) : Subgroup E :=
  (burnsideF447_T0 (F := F)).map Φ

theorem burnsideF447_Ibar_le (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E)) : burnsideF447_Ibar Φ ≤ M₂ := by
  rintro _ ⟨p, ⟨B, rfl⟩, rfl⟩
  rw [h₂]
  exact map_mem_normalizer_map Φ (burnsideF447_lv_mem_normalizer_V1 B)

theorem burnsideF447_Ibar_comm [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ Bbar : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E)) (hB : Bbar = burnsideF447_Bt Φ) {y : E}
    (hy : y ∈ f447Ybar Gp M₂ Bbar) {i : E} (hi : i ∈ burnsideF447_Ibar Φ) :
    i * y = y * i := by
  obtain ⟨x, y', hρ⟩ := burnsideF447_Ybar_diag C h₂ hB hy
  obtain ⟨p, ⟨B, rfl⟩, rfl⟩ := hi
  have h1 : ρ y (burnsideF447_lv B) = burnsideF447_lv B := by
    rw [hρ]
    exact burnsideF447_conj_lv x y' B
  have h2 := C.hΦρ y (burnsideF447_lv B)
  rw [h1] at h2
  calc Φ (burnsideF447_lv B) * y = (y * Φ (burnsideF447_lv B) * y⁻¹) * y := by rw [← h2]
    _ = y * Φ (burnsideF447_lv B) := by group

end PkgE

section Pkg

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

structure burnsideF447_PkgOf {E : Type} [Group E] (Gp M₁ M₂ Bbar B0bar Ibar Xbar : Subgroup E)
    (xbar i₀ : E) : Prop where
  I_le : Ibar ≤ M₂
  X_le_I : Xbar ≤ Ibar
  X_le_M12 : Xbar ≤ M₁ ⊓ M₂
  I_nonsolv : ¬ Group.IsSolvable ↥Ibar
  I_comm : ∀ i ∈ Ibar, ∀ y ∈ f447Ybar Gp M₂ Bbar, i * y = y * i
  I_inf : f447Ybar Gp M₂ Bbar ⊓ Ibar = ⊥
  X_sq : ∀ x ∈ Xbar, x * x = 1
  X_klein : ∃ K : Subgroup E, K ≤ Xbar ∧ Nat.card K = 4
  X_odd : Odd (Xbar.relIndex (f447Ybar Gp M₂ Bbar ⊔ Ibar))
  i₀_mem : i₀ ∈ Xbar
  i₀_ne : i₀ ≠ 1
  I_conj : ∀ x ∈ Ibar, x * x = 1 → x ≠ 1 → ∃ m ∈ Ibar, m * i₀ * m⁻¹ = x
  x_mem : xbar ∈ M₁
  x_sq : xbar * xbar = 1
  x_ZZ : ∀ g : E, g ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ↔ xbar * g * xbar⁻¹ ∈ Xbar
  LV7 : f447Ybar Gp M₂ Bbar ≠ ⊥ → ∀ w ∈ M₁ ⊓ M₂,
    w * (xbar⁻¹ * i₀ * xbar) = (xbar⁻¹ * i₀ * xbar) * w →
    (∀ y ∈ f447Ybar Gp M₂ Bbar, w * (xbar⁻¹ * y * xbar) = (xbar⁻¹ * y * xbar) * w) →
    xbar * w * xbar⁻¹ ∈ Xbar ⊔ f447Ybar Gp M₂ Bbar
  noInv : ∀ w ∈ M₁ ⊓ M₂,
    (∀ y ∈ f447Ybar Gp M₂ Bbar, w * (xbar⁻¹ * y * xbar) * w⁻¹ = (xbar⁻¹ * y * xbar)⁻¹) →
    f447Ybar Gp M₂ Bbar = ⊥
  I_cent_B0 : ∀ i ∈ Ibar, (∀ b ∈ B0bar, i * b = b * i) → i ∈ B0bar
  B0_comm : ∀ a ∈ B0bar, ∀ b ∈ B0bar, a * b = b * a
  Y_le_B0 : f447Ybar Gp M₂ Bbar ≤ B0bar

end Pkg

section PkgE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E] {f : ℕ}
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_Ybar_inf_Ibar [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ Bbar : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E)) (hB : Bbar = burnsideF447_Bt Φ) :
    f447Ybar Gp M₂ Bbar ⊓ burnsideF447_Ibar Φ = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hy, ⟨p, ⟨B, rfl⟩, rfl⟩⟩
  obtain ⟨x, y', hρ⟩ := burnsideF447_Ybar_diag C h₂ hB hy
  have h1 : conjAut 3 F (burnsideF447_diagGL x y' y') =
      conjAut 3 F (Matrix.SpecialLinearGroup.toGL (burnsideF447_blk B)) := by
    rw [← hρ, conjAut_toGL, burnsideF447_rho_Phi C.hΦ C.hΦρ]
    rfl
  have h4 : conjAut 3 F ((burnsideF447_diagGL x y' y')⁻¹ *
      Matrix.SpecialLinearGroup.toGL (burnsideF447_blk B)) * fieldAut 3 F 1 = 1 := by
    rw [map_mul, map_inv, h1, map_one, mul_one, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h4
  have hc' : Matrix.SpecialLinearGroup.toGL (burnsideF447_blk B) =
      burnsideF447_diagGL x y' y' * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rw [hc, mul_inv_cancel_left]
  have hm := congrArg (fun X : GL (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F)) hc'
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    burnsideF447_coe_blk] at hm
  have e11 := congrFun (congrFun hm 1) 1
  have e12 := congrFun (congrFun hm 1) 2
  have e21 := congrFun (congrFun hm 2) 1
  have e22 := congrFun (congrFun hm 2) 2
  simp [burnsideF447_diagGL, Matrix.GeneralLinearGroup.scalar, burnsideF447_blkMat,
    Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three] at e11 e12 e21 e22
  have hdet := B.2
  rw [Matrix.det_fin_two, e11, e22, e12, e21] at hdet
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hu : (y' : F) * c = 1 := by
    have h3 : ((y' : F) * c - 1) * ((y' : F) * c - 1) = 0 := by
      linear_combination hdet - ((y' : F) * c) * h2 + h2
    have := mul_self_eq_zero.mp h3
    linear_combination this
  have hB1 : B = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e11, e12, e21, e22, hu]
  rw [hB1, map_one, map_one]
  exact Subgroup.one_mem _

theorem burnsideF447_Ctx.hq4 (C : burnsideF447_Ctx f Φ ρ Gp) : 4 ≤ Nat.card F := by
  rw [C.hF]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) C.hf

theorem burnsideF447_Ibar_not_solvable (hΦ : Function.Injective Φ) (hq : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable ↥(burnsideF447_Ibar Φ) := by
  intro h
  apply burnsideF447_Lam_not_solvable hq
  haveI : Group.IsSolvable ↥((burnsideF447_Lam (F := F)).map Φ) := h
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective _ Φ hΦ).toMonoidHom)
    (Subgroup.equivMapOfInjective _ Φ hΦ).injective

theorem burnsideF447_Xbar_le_Ibar : burnsideF447_Xbar Φ ≤ burnsideF447_Ibar Φ :=
  Subgroup.map_mono burnsideF447_Xroot_le_Lam

theorem burnsideF447_Xbar_sq {x : E} (hx : x ∈ burnsideF447_Xbar Φ) : x * x = 1 := by
  obtain ⟨p, hp, rfl⟩ := hx
  have := burnsideF447_Xroot_elemAbelian (F := F)
  have h2 := this.2 p hp
  rw [← map_mul, ← pow_two, h2, map_one]

theorem burnsideF447_Xbar_card (hΦ : Function.Injective Φ) :
    Nat.card ↥(burnsideF447_Xbar Φ) = Nat.card F := by
  rw [burnsideF447_Xbar, Subgroup.card_map_of_injective hΦ, burnsideF447_Xroot_card]

theorem burnsideF447_Ibar_card (hΦ : Function.Injective Φ) :
    Nat.card ↥(burnsideF447_Ibar Φ) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [burnsideF447_Ibar, Subgroup.card_map_of_injective hΦ, burnsideF447_Lam_card]

theorem burnsideF447_Xbar_le_U :
    burnsideF447_Xbar Φ ≤ (projUnitriangular 3 F).map Φ := by
  rintro _ ⟨p, ⟨s, rfl⟩, rfl⟩
  refine ⟨yP s, mem_Ubar.mpr ⟨0, 0, s, by rw [wP_zero, xP_zero]; group⟩, ?_⟩
  rw [burnsideF447_lv_xEl]

theorem burnsideF447_blk_dEl (c : Fˣ) :
    burnsideF447_blk (burnsideF447_dEl c) = dMat (F := F) 1 c := by
  apply Subtype.ext
  rw [burnsideF447_coe_blk, coe_dMat, burnsideF447_coe_dEl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF447_blkMat, Matrix.diagonal_apply]

theorem burnsideF447_T0_le_torus3 : burnsideF447_T0 (F := F) ≤ torus3 F := by
  rintro _ ⟨c, rfl⟩
  show proj 3 F (burnsideF447_blk (burnsideF447_dEl c)) ∈ torus3 F
  rw [burnsideF447_blk_dEl]
  exact dP_mem_torus3 _ _

theorem burnsideF447_Tbar_le_B0bar [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {Bbar B0bar : Subgroup E}
    (hB : Bbar = burnsideF447_Bt Φ) (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    burnsideF447_Tbar Φ ≤ B0bar := by
  rintro _ ⟨p, hp, rfl⟩
  have hpT : p ∈ torus3 F := burnsideF447_T0_le_torus3 hp
  refine (hB0 _).mpr ⟨?_, (C.innDiag_iff _).mpr (C.fpE_Phi p)⟩
  rw [hB]
  exact burnsideF447_Phi_torus_mem_Bt hpT

theorem burnsideF447_Ybar_le_B0bar [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ Bbar B0bar : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E)) (hB : Bbar = burnsideF447_Bt Φ)
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    f447Ybar Gp M₂ Bbar ≤ B0bar := by
  intro y hy
  obtain ⟨x, y', hρ⟩ := burnsideF447_Ybar_diag C h₂ hB hy
  refine (hB0 y).mpr ⟨hy.1, (C.innDiag_iff y).mpr ?_⟩
  rw [burnsideF447_fpE_one_iff, hρ]
  exact conjAut_mem_linearAutGroup _

theorem burnsideF447_B0bar_comm [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {Bbar B0bar : Subgroup E}
    (hB : Bbar = burnsideF447_Bt Φ) (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    ∀ a ∈ B0bar, ∀ b ∈ B0bar, a * b = b * a := by
  intro a ha b hb
  have ha' := (hB0 a).mp ha
  have hb' := (hB0 b).mp hb
  exact burnsideF447_Bt_one_comm C.hq C.hΦ C.hρ C.hΦρ C.hE (hB ▸ ha'.1) (hB ▸ hb'.1)
    ((C.innDiag_iff a).mp ha'.2) ((C.innDiag_iff b).mp hb'.2)

theorem burnsideF447_Ibar_cent_Tbar (C : burnsideF447_Ctx f Φ ρ Gp) {i : E} (hi : i ∈ burnsideF447_Ibar Φ)
    (h : ∀ b ∈ burnsideF447_Tbar Φ, i * b = b * i) : i ∈ burnsideF447_Tbar Φ := by
  obtain ⟨p, hp, rfl⟩ := hi
  refine ⟨p, burnsideF447_Lam_cent_T0 ?_ hp ?_, rfl⟩
  · exact C.hq4
  · intro x hx
    apply C.hΦ
    rw [map_mul, map_mul]
    exact h _ ⟨x, hx, rfl⟩

theorem burnsideF447_Ibar_invol_conj (hΦ : Function.Injective Φ) {x : E}
    (hx : x ∈ burnsideF447_Ibar Φ) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ m ∈ burnsideF447_Ibar Φ, m * Φ (yP 1) * m⁻¹ = x := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hpp : p * p = 1 := hΦ (by rw [map_mul, hx2, map_one])
  have hp1 : p ≠ 1 := fun h => hx1 (by rw [h, map_one])
  obtain ⟨h, hh, hhp⟩ := burnsideF447_Lam_invol_conj hp hpp hp1
  refine ⟨Φ h, ⟨h, hh, rfl⟩, ?_⟩
  rw [← burnsideF447_lv_xEl, ← map_inv, ← map_mul, ← map_mul, hhp]

theorem burnsideF447_i₀_ne (hΦ : Function.Injective Φ) : Φ (yP (1 : F)) ≠ 1 := by
  intro h
  have h1 : yP (1 : F) = 1 := hΦ (by rw [h, map_one])
  rw [← burnsideF447_lv_xEl] at h1
  have h2 : burnsideF447_xEl (1 : F) = 1 := burnsideF447_lv_injective (by rw [h1, map_one])
  have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 1) h2
  simp [burnsideF447_coe_xEl] at this

theorem burnsideF447_Xbar_klein (C : burnsideF447_Ctx f Φ ρ Gp) :
    ∃ K : Subgroup E, K ≤ burnsideF447_Xbar Φ ∧ Nat.card K = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : 2 ^ 2 ∣ Nat.card ↥(burnsideF447_Xbar Φ) := by
    rw [burnsideF447_Xbar_card C.hΦ, C.hF]
    exact pow_dvd_pow 2 C.hf
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hcard
  refine ⟨K.map (burnsideF447_Xbar Φ).subtype, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
    norm_num

theorem burnsideF447_Xbar_odd [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ Bbar : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E)) (hB : Bbar = burnsideF447_Bt Φ) (hBodd : Odd (Nat.card Bbar)) :
    Odd ((burnsideF447_Xbar Φ).relIndex (f447Ybar Gp M₂ Bbar ⊔ burnsideF447_Ibar Φ)) := by
  have hdisj : Disjoint (f447Ybar Gp M₂ Bbar) (burnsideF447_Ibar Φ) :=
    disjoint_iff.mpr (burnsideF447_Ybar_inf_Ibar C h₂ hB)
  have hnorm : burnsideF447_Ibar Φ ≤
      Subgroup.normalizer ((f447Ybar Gp M₂ Bbar : Subgroup E) : Set E) := fun i hi =>
    Subgroup.centralizer_le_normalizer ((f447Ybar Gp M₂ Bbar : Subgroup E) : Set E)
      (Subgroup.mem_centralizer_iff.mpr (fun y hy =>
        (burnsideF447_Ibar_comm C h₂ hB hy hi).symm))
  have hcardsup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (f447Ybar Gp M₂ Bbar) (burnsideF447_Ibar Φ) hnorm hdisj
  have hXle : burnsideF447_Xbar Φ ≤ f447Ybar Gp M₂ Bbar ⊔ burnsideF447_Ibar Φ :=
    burnsideF447_Xbar_le_Ibar.trans le_sup_right
  have h1 := Subgroup.relIndex_mul_card (H := burnsideF447_Xbar Φ)
    (K := f447Ybar Gp M₂ Bbar ⊔ burnsideF447_Ibar Φ)
  rw [inf_eq_left.mpr hXle, hcardsup, burnsideF447_Xbar_card C.hΦ, burnsideF447_Ibar_card C.hΦ]
    at h1
  have hYodd : Odd (Nat.card ↥(f447Ybar Gp M₂ Bbar)) :=
    hBodd.of_dvd_nat (Subgroup.card_dvd_of_le (fun b hb => hb.1))
  have hq0 : 0 < Nat.card F := Nat.card_pos
  have hq21 : Odd (Nat.card F ^ 2 - 1) := by
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by have := C.hf; omega⟩
    have hqe : Nat.card F = 2 * 2 ^ f' := by rw [C.hF, hf', pow_succ]; ring
    have hm : 1 ≤ 2 ^ f' := Nat.one_le_two_pow
    have hk : 1 ≤ 2 ^ f' * 2 ^ f' := Nat.mul_pos (by omega) (by omega)
    have e : Nat.card F ^ 2 = 4 * (2 ^ f' * 2 ^ f') := by rw [hqe]; ring
    rw [e]
    exact ⟨2 * (2 ^ f' * 2 ^ f') - 1, by omega⟩
  have hr : (burnsideF447_Xbar Φ).relIndex (f447Ybar Gp M₂ Bbar ⊔ burnsideF447_Ibar Φ) =
      Nat.card ↥(f447Ybar Gp M₂ Bbar) * (Nat.card F ^ 2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_right hq0
    calc _ = _ := h1
      _ = (Nat.card ↥(f447Ybar Gp M₂ Bbar) * (Nat.card F ^ 2 - 1)) * Nat.card F := by ring
  rw [hr]
  exact hYodd.mul hq21

theorem burnsideF447_x_ZZ [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₁ M₂ : Subgroup E}
    (hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ)
    (hZcard : Nat.card ↥(ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) = Nat.card F) (g : E) :
    g ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ↔
      Φ s₁₂P * g * (Φ s₁₂P)⁻¹ ∈ burnsideF447_Xbar Φ := by
  have hW : (burnsideF447_Xbar Φ).map (MulAut.conj (Φ s₁₂P)⁻¹).toMonoidHom ≤
      ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
    rintro _ ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩
    have e : (MulAut.conj (Φ s₁₂P)⁻¹).toMonoidHom (Φ (burnsideF447_lv (burnsideF447_xEl s))) =
        Φ (wP s) := by
      rw [burnsideF447_lv_xEl]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      have := s12P_conj_wP' (F := F) s
      calc (s₁₂P : projectiveSL 3 F)⁻¹ * yP s * s₁₂P =
          s₁₂P⁻¹ * (s₁₂P * wP s * s₁₂P⁻¹) * s₁₂P := by rw [this]
        _ = wP s := by group
    rw [e, hS]
    refine ⟨⟨wP s, mem_Ubar.mpr ⟨s, 0, 0, by rw [xP_zero, yP_zero]; group⟩, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, burnsideF447_wP_cent hv s]
  have hEq : (burnsideF447_Xbar Φ).map (MulAut.conj (Φ s₁₂P)⁻¹).toMonoidHom =
      ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
    refine Subgroup.eq_of_le_of_card_ge hW ?_
    rw [hZcard, Subgroup.card_map_of_injective (MulAut.conj (Φ s₁₂P)⁻¹).injective,
      burnsideF447_Xbar_card C.hΦ]
  constructor
  · intro hg
    rw [← hEq] at hg
    obtain ⟨u, hu, hug⟩ := hg
    have : g = (Φ s₁₂P)⁻¹ * u * Φ s₁₂P := by
      rw [← hug]
      simp [MulAut.conj_apply]
    rw [this]
    have e : Φ s₁₂P * ((Φ s₁₂P)⁻¹ * u * Φ s₁₂P) * (Φ s₁₂P)⁻¹ = u := by group
    rw [e]
    exact hu
  · intro hg
    rw [← hEq]
    refine ⟨Φ s₁₂P * g * (Φ s₁₂P)⁻¹, hg, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    group

theorem burnsideF447_xbar_inv : (Φ s₁₂P)⁻¹ = Φ (s₁₂P : projectiveSL 3 F) := by
  have h : (s₁₂P : projectiveSL 3 F)⁻¹ = s₁₂P :=
    inv_eq_of_mul_eq_one_right (s12P_mul_self (F := F))
  rw [← map_inv, h]

theorem burnsideF447_no_invert [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₂ : Subgroup E}
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E)) (hBodd : ∀ b ∈ burnsideF447_Bt Φ, Odd (orderOf b))
    {w : E} (hw : w ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hinv : ∀ y ∈ f447Ybar Gp M₂ (burnsideF447_Bt Φ),
      w * ((Φ s₁₂P)⁻¹ * y * Φ s₁₂P) * w⁻¹ = ((Φ s₁₂P)⁻¹ * y * Φ s₁₂P)⁻¹) :
    f447Ybar Gp M₂ (burnsideF447_Bt Φ) = ⊥ := by
  haveI : Φ.range.Normal := by rw [C.hrange]; infer_instance
  obtain ⟨u₁, hu₁, b, hb, rfl⟩ := burnsideF447_frattini C.hq C.hΦ hw
  obtain ⟨v, hv, rfl⟩ := hu₁
  have hSB : ∀ g, g ∈ (projUnitriangular 3 F).map Φ → g ∈ burnsideF447_Bt Φ → g = 1 :=
    fun g h1 h2 => burnsideF447_Bt_inf_U C.hq C.hΦ h1 h2
  have hSn : ∀ y ∈ burnsideF447_Bt Φ, ∀ s ∈ (projUnitriangular 3 F).map Φ,
      y * s * y⁻¹ ∈ (projUnitriangular 3 F).map Φ :=
    fun y hy s hs => (Subgroup.mem_normalizer_iff.mp hy.1 s).mp hs
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨x, y', hρ⟩ := burnsideF447_Ybar_diag C h₂ rfl hy
  have hρŷ := burnsideF447_rho_conj_s12 C.hΦ C.hΦρ hρ
  have hŷB : Φ s₁₂P * y * (Φ s₁₂P)⁻¹ ∈ burnsideF447_Bt Φ :=
    burnsideF447_mem_Bt_of_diag C hρŷ
  have hinv' := hinv y hy
  obtain ⟨ŷ, hŷ⟩ : ∃ ŷ : E, ŷ = Φ s₁₂P * y * (Φ s₁₂P)⁻¹ := ⟨_, rfl⟩
  have hŷB' : ŷ ∈ burnsideF447_Bt Φ := hŷ ▸ hŷB
  have hŷ' : (Φ s₁₂P)⁻¹ * y * Φ s₁₂P = ŷ := by
    rw [hŷ, burnsideF447_xbar_inv]
  rw [hŷ'] at hinv'
  have hbŷ : b * ŷ * b⁻¹ = ŷ⁻¹ := by
    have haB : b * ŷ * b⁻¹ ∈ burnsideF447_Bt Φ :=
      (burnsideF447_Bt Φ).mul_mem ((burnsideF447_Bt Φ).mul_mem hb hŷB')
        ((burnsideF447_Bt Φ).inv_mem hb)
    have h1 : Φ v * (b * ŷ * b⁻¹) * (Φ v)⁻¹ = ŷ⁻¹ := by
      have : (Φ v * b) * ŷ * (Φ v * b)⁻¹ = Φ v * (b * ŷ * b⁻¹) * (Φ v)⁻¹ := by group
      rw [← this]
      exact hinv'
    have h2 : (ŷ⁻¹ * (b * ŷ * b⁻¹)⁻¹) = Φ v * ((b * ŷ * b⁻¹) * (Φ v)⁻¹ * (b * ŷ * b⁻¹)⁻¹) := by
      rw [← h1]
      group
    have h3 : Φ v * ((b * ŷ * b⁻¹) * (Φ v)⁻¹ * (b * ŷ * b⁻¹)⁻¹) ∈
        (projUnitriangular 3 F).map Φ :=
      Subgroup.mul_mem _ ⟨v, hv, rfl⟩ (hSn _ haB _ (Subgroup.inv_mem _ ⟨v, hv, rfl⟩))
    have h4 : ŷ⁻¹ * (b * ŷ * b⁻¹)⁻¹ ∈ burnsideF447_Bt Φ :=
      (burnsideF447_Bt Φ).mul_mem ((burnsideF447_Bt Φ).inv_mem hŷB')
        ((burnsideF447_Bt Φ).inv_mem haB)
    have h5 := hSB _ (h2 ▸ h3) h4
    have h6 : ŷ⁻¹ = b * ŷ * b⁻¹ := by
      have := h5
      rw [mul_inv_eq_one] at this
      exact this
    exact h6.symm
  have hbc : b * ŷ = ŷ * b := by
    have hodd := hBodd b hb
    obtain ⟨m, hm⟩ := hodd
    have hb2 : b ^ 2 * ŷ = ŷ * b ^ 2 := by
      have e1 : b * ŷ⁻¹ = ŷ * b := by
        have h0 : b * ŷ⁻¹ * b⁻¹ = ŷ := by
          calc b * ŷ⁻¹ * b⁻¹ = (b * ŷ * b⁻¹)⁻¹ := by group
            _ = (ŷ⁻¹)⁻¹ := by rw [hbŷ]
            _ = ŷ := inv_inv _
        calc b * ŷ⁻¹ = (b * ŷ⁻¹ * b⁻¹) * b := by group
          _ = ŷ * b := by rw [h0]
      have e2 : b * ŷ = ŷ⁻¹ * b := by
        calc b * ŷ = (b * ŷ * b⁻¹) * b := by group
          _ = ŷ⁻¹ * b := by rw [hbŷ]
      calc b ^ 2 * ŷ = b * (b * ŷ) := by rw [pow_two, mul_assoc]
        _ = b * (ŷ⁻¹ * b) := by rw [e2]
        _ = (b * ŷ⁻¹) * b := by group
        _ = (ŷ * b) * b := by rw [e1]
        _ = ŷ * b ^ 2 := by rw [pow_two, mul_assoc]
    have hcomm : Commute (b ^ 2) ŷ := hb2
    have hpow : b = (b ^ 2) ^ (m + 1) := by
      have hn : b ^ orderOf b = 1 := pow_orderOf_eq_one b
      rw [hm] at hn
      calc b = b ^ (2 * m + 1) * b := by rw [hn, one_mul]
        _ = b ^ (2 * (m + 1)) := by
          rw [← pow_succ]
          congr 1
        _ = (b ^ 2) ^ (m + 1) := by rw [pow_mul]
    have hc2 : Commute b ŷ := by
      rw [hpow]
      exact hcomm.pow_left (m + 1)
    exact hc2
  have hŷsq : ŷ * ŷ = 1 := by
    have h1 : b * ŷ * b⁻¹ = ŷ := by
      rw [hbc]
      group
    rw [h1] at hbŷ
    have : ŷ * ŷ = ŷ * ŷ⁻¹ := by rw [← hbŷ]
    rw [this]
    group
  have hŷ1 : ŷ = 1 := by
    have h2 : orderOf ŷ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hŷsq)
    have hodd := hBodd ŷ hŷB'
    have h3 : orderOf ŷ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h3
  have : y = (Φ s₁₂P)⁻¹ * ŷ * Φ s₁₂P := by
    rw [hŷ]
    group
  rw [this, hŷ1]
  group

theorem burnsideF447_xbar_i₀ :
    (Φ s₁₂P)⁻¹ * Φ (yP (1 : F)) * Φ s₁₂P = Φ (wP (1 : F)) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  have := s12P_conj_wP' (F := F) 1
  calc (s₁₂P : projectiveSL 3 F)⁻¹ * yP 1 * s₁₂P =
      s₁₂P⁻¹ * (s₁₂P * wP 1 * s₁₂P⁻¹) * s₁₂P := by rw [this]
    _ = wP 1 := by group

theorem burnsideF447_pkgV1 [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) {M₁ M₂ Bbar B0bar : Subgroup E}
    (h₁ : M₁ = Subgroup.normalizer (((V2 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E))
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E))
    (hN : M₁ ⊓ M₂ = Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ)
    (hZcard : Nat.card ↥(ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) = Nat.card F)
    (hB : Bbar = burnsideF447_Bt Φ) (hBodd : Odd (Nat.card Bbar))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    burnsideF447_PkgOf Gp M₁ M₂ Bbar B0bar (burnsideF447_Ibar Φ) (burnsideF447_Xbar Φ) (Φ s₁₂P)
      (Φ (yP 1)) := by
  subst hB
  have hBelt : ∀ b ∈ burnsideF447_Bt Φ, Odd (orderOf b) := fun b hb => by
    have h1 : orderOf b ∣ Nat.card ↥(burnsideF447_Bt Φ) := by
      have := orderOf_dvd_natCard (⟨b, hb⟩ : ↥(burnsideF447_Bt Φ))
      rwa [Subgroup.orderOf_mk] at this
    exact hBodd.of_dvd_nat h1
  have hxinv : (Φ s₁₂P)⁻¹ = Φ (s₁₂P : projectiveSL 3 F) := burnsideF447_xbar_inv
  have hXmem : ∀ c : F, Φ (yP c) ∈ burnsideF447_Xbar Φ := fun c =>
    ⟨burnsideF447_lv (burnsideF447_xEl c), ⟨c, rfl⟩, by rw [burnsideF447_lv_xEl]⟩
  refine
    { I_le := burnsideF447_Ibar_le C h₂
      X_le_I := burnsideF447_Xbar_le_Ibar
      X_le_M12 := ?_
      I_nonsolv := burnsideF447_Ibar_not_solvable C.hΦ C.hq4
      I_comm := fun i hi y hy => burnsideF447_Ibar_comm C h₂ rfl hy hi
      I_inf := burnsideF447_Ybar_inf_Ibar C h₂ rfl
      X_sq := fun x hx => burnsideF447_Xbar_sq hx
      X_klein := burnsideF447_Xbar_klein C
      X_odd := burnsideF447_Xbar_odd C h₂ rfl hBodd
      i₀_mem := hXmem 1
      i₀_ne := burnsideF447_i₀_ne C.hΦ
      I_conj := fun x hx hx2 hx1 => burnsideF447_Ibar_invol_conj C.hΦ hx hx2 hx1
      x_mem := ?_
      x_sq := ?_
      x_ZZ := burnsideF447_x_ZZ C hS hZcard
      LV7 := ?_
      noInv := ?_
      I_cent_B0 := ?_
      B0_comm := burnsideF447_B0bar_comm C rfl hB0
      Y_le_B0 := burnsideF447_Ybar_le_B0bar C h₂ rfl hB0 }
  · rw [hN]
    exact burnsideF447_Xbar_le_U.trans Subgroup.le_normalizer
  · rw [h₁]
    exact map_mem_normalizer_map Φ s12P_mem_normalizer_V2
  · rw [← map_mul, s12P_mul_self, map_one]
  · intro hY w hw hz hy
    rw [hN] at hw
    rw [burnsideF447_xbar_i₀] at hz
    have hy' : ∀ y ∈ f447Ybar Gp M₂ (burnsideF447_Bt Φ),
        w * (Φ s₁₂P * y * (Φ s₁₂P)⁻¹) = (Φ s₁₂P * y * (Φ s₁₂P)⁻¹) * w := by
      intro y hyY
      have := hy y hyY
      have e : (Φ s₁₂P)⁻¹ * y * Φ s₁₂P = Φ s₁₂P * y * (Φ s₁₂P)⁻¹ := by rw [hxinv]
      rwa [e] at this
    obtain ⟨c, b, hb, hcb⟩ := burnsideF447_LV7 C h₂ hY hw hz hy'
    rw [hcb]
    exact Subgroup.mul_mem_sup (hXmem c) hb
  · intro w hw hinv
    rw [hN] at hw
    exact burnsideF447_no_invert C h₂ hBelt hw hinv
  · intro i hi h
    have hT := burnsideF447_Tbar_le_B0bar C rfl hB0
    exact hT (burnsideF447_Ibar_cent_Tbar C hi (fun b hb => h b (hT hb)))

end PkgE2

section Transp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3

variable {X G : Type} [Group X] [Group G] {N : Subgroup X}

theorem burnsideF447_relIndex_subImg [Finite X] (b : ↥N →* G) (hb : Function.Injective b)
    {A K : Subgroup X} (hAK : A ≤ K) (hKN : K ≤ N) :
    (subImg b A).relIndex (subImg b K) = A.relIndex K := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := K)
  have h2 := Subgroup.relIndex_mul_card (H := subImg b A) (K := subImg b K)
  have e1 : A ⊓ K = A := inf_eq_left.mpr hAK
  have e2 : subImg b A ⊓ subImg b K = subImg b A := inf_eq_left.mpr (subImg_mono b hAK)
  rw [e1] at h1
  rw [e2, card_subImg b hb (hAK.trans hKN), card_subImg b hb hKN] at h2
  have hpos : 0 < Nat.card A := Nat.card_pos
  have := h2.trans h1.symm
  exact Nat.eq_of_mul_eq_mul_right hpos this

end Transp

section SE

open CFSG.Open CFSG.BenderSuzuki CFSG.Semidihedral.ParameterFive

theorem burnsideF447_SE_solvable {M : Type} [Group M] [Finite M]
    {C H W : Subgroup M} (hHC : H ≤ C) {t : M} (htH : t ∈ H) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hcent : ∀ g ∈ C, g * t = t * g → g ∈ H)
    (hconj : ∀ x ∈ H, x * x = 1 → x ≠ 1 → ∃ m ∈ H, m * t * m⁻¹ = x)
    (hne : H ≠ C) (hWH : W ≤ H) (hWexp : ∀ x ∈ W, x ^ 2 = 1) (hWodd : Odd (W.relIndex H))
    (hE : ∃ E : Subgroup M, E ≤ C ∧ Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    Group.IsSolvable ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H' : Subgroup ↥C := H.subgroupOf C
  let W' : Subgroup ↥C := W.subgroupOf C
  let t' : ↥C := ⟨t, hHC htH⟩
  have ht' : orderOf t' = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simpa [pow_two] using ht2
    · intro h
      apply ht1
      exact congrArg Subtype.val h
  have hMtop : H' ≠ ⊤ := by
    intro htop
    apply hne
    apply le_antisymm hHC
    intro c hc
    have : (⟨c, hc⟩ : ↥C) ∈ H' := by rw [htop]; exact Subgroup.mem_top _
    exact this
  have hCM : Subgroup.centralizer {t'} ≤ H' := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hg' : g.1 * t = t * g.1 := congrArg Subtype.val hg
    exact hcent g.1 g.2 hg'
  have hconj' : ∀ x ∈ H', orderOf x = 2 → ∃ m ∈ H', m * t' * m⁻¹ = x := by
    intro x hx hx2
    have hxx : x.1 * x.1 = 1 := by
      have h1 : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
      have h2 := congrArg Subtype.val h1
      simpa [pow_two] using h2
    have hx1 : x.1 ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx2
      omega
    obtain ⟨m, hm, hmt⟩ := hconj x.1 hx hxx hx1
    refine ⟨⟨m, hHC hm⟩, hm, Subtype.ext ?_⟩
    simpa using hmt
  have hSE := isStronglyEmbedded_of_conj ht' hMtop hCM hconj'
  have hW'L : W' ≤ involutionCore ↥C := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · refine Subgroup.subset_closure ?_
      have hx2 : x.1 ^ 2 = 1 := hWexp x.1 hx
      have hx3 : x ^ 2 = 1 := Subtype.ext (by simpa using hx2)
      exact isInvolution_of_orderOf_eq_two (orderOf_eq_prime hx3 hx1)
  have hrel : (W').relIndex H' = W.relIndex H := Subgroup.relIndex_subgroupOf hHC
  have hodd : Odd ((involutionCore ↥C).relIndex H') := by
    have hdvd : (involutionCore ↥C).relIndex H' ∣ W'.relIndex H' :=
      Subgroup.relIndex_dvd_of_le_left H' hW'L
    rw [hrel] at hdvd
    exact hWodd.of_dvd_nat hdvd
  rcases theorem_SE H' hSE with hlow | hB
  · exfalso
    apply hlow
    obtain ⟨E, hEC, hE4, hE2⟩ := hE
    have hEL : E.subgroupOf C ≤ involutionCore ↥C := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · refine Subgroup.subset_closure ?_
        have hx2 : x.1 ^ 2 = 1 := hE2 x.1 hx
        have hx3 : x ^ 2 = 1 := Subtype.ext (by simpa using hx2)
        exact isInvolution_of_orderOf_eq_two (orderOf_eq_prime hx3 hx1)
    refine ⟨(E.subgroupOf C).subgroupOf (involutionCore ↥C), ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hE4]
    · rintro ⟨⟨⟨x, hxC⟩, hxL⟩, hxE⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hE2 x hxE
  · obtain ⟨-, -, hsolv, -⟩ := hB
    have hK : Group.IsSolvable ↥(H' ⊓ involutionCore ↥C) :=
      burnsideF4d_Z3_solvable_of_borel (K := H' ⊓ involutionCore ↥C) le_rfl hsolv
    have hH' : Group.IsSolvable ↥H' := burnsideF4d_Z3_solvable_of_normal hK hodd
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hHC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHC).symm.injective

end SE

section ClauseTwoM

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF447_clause2_M
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {Bbar B0bar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) {Ibar Xbar : Subgroup E} {xbar i₀ : E}
    (P : burnsideF447_PkgOf Gp M₁ M₂ Bbar B0bar Ibar Xbar xbar i₀)
    (hYM : imB β ε (f447Ybar Gp M₂ Bbar) ≠ ⊥) :
    imB β ε B0bar = Subgroup.centralizer ((imB β ε B0bar : Subgroup M) : Set M) ∧
      ¬ ∃ g : M, ∀ y ∈ imB β ε (f447Ybar Gp M₂ Bbar), g * y * g⁻¹ = y⁻¹ := by
  have hY : f447Ybar Gp M₂ Bbar ≠ ⊥ := fun h => hYM (by rw [h]; simp [imB])
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  have hf : 2 ≤ f := burnsideF4d_L3_two_le_f hyp
  have hb1 : Function.Injective (burnsideF4d_bOne β ε) :=
    hyp.inj.comp (f1_injective β hyp.faithful)
  have hb2 : Function.Injective (burnsideF4d_bTwo β ε) :=
    hyp.inj.comp (f2_injective β hyp.faithful)
  have hagree : ∀ g (h1 : g ∈ M₁) (h2 : g ∈ M₂),
      burnsideF4d_bOne β ε ⟨g, h1⟩ = burnsideF4d_bTwo β ε ⟨g, h2⟩ :=
    (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj).agree
  obtain ⟨D, hG, hz, hDS, hQ₁, hQ₂⟩ := burnsideF4d_L3_setup hf hyp
  have hBodd : ∀ y ∈ Bbar, Odd (orderOf y) := fun y hy => by
    have h1 : orderOf y ∣ Nat.card Bbar := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : Bbar)
      rwa [Subgroup.orderOf_mk] at this
    exact hB.2.1.of_dvd_nat h1
  have hYB : f447Ybar Gp M₂ Bbar ≤ Bbar := fun b hb => hb.1
  have hYM12 : f447Ybar Gp M₂ Bbar ≤ M₁ ⊓ M₂ := hYB.trans hB.1
  have hYM₁ : f447Ybar Gp M₂ Bbar ≤ M₁ := hYM12.trans inf_le_left
  have hYM₂ : f447Ybar Gp M₂ Bbar ≤ M₂ := hYM12.trans inf_le_right
  have hHM₂ : f447Ybar Gp M₂ Bbar ⊔ Ibar ≤ M₂ := sup_le hYM₂ P.I_le
  have hXM₁ : Xbar ≤ M₁ := P.X_le_M12.trans inf_le_left
  have hXM₂ : Xbar ≤ M₂ := P.X_le_M12.trans inf_le_right
  have hYim₁ : imB β ε (f447Ybar Gp M₂ Bbar) = subImg (burnsideF4d_bOne β ε) (f447Ybar Gp M₂ Bbar) :=
    burnsideF4d_Z4_imB_eq β ε hYM12
  have hYim₂ : imB β ε (f447Ybar Gp M₂ Bbar) = subImg (burnsideF4d_bTwo β ε) (f447Ybar Gp M₂ Bbar) :=
    hYim₁.trans (subImg_eq_of_agree hagree hYM₁ hYM₂)
  have hX₂ : subImg (burnsideF4d_bOne β ε) Xbar = subImg (burnsideF4d_bTwo β ε) Xbar :=
    subImg_eq_of_agree hagree hXM₁ hXM₂
  have hYcomm : ∀ a ∈ f447Ybar Gp M₂ Bbar, ∀ c ∈ f447Ybar Gp M₂ Bbar, a * c = c * a :=
    fun a ha c hc => P.B0_comm a (P.Y_le_B0 ha) c (P.Y_le_B0 hc)
  have hprod : ∀ h ∈ f447Ybar Gp M₂ Bbar ⊔ Ibar, ∃ a ∈ f447Ybar Gp M₂ Bbar, ∃ i ∈ Ibar, h = a * i :=
    fun h hh => burnsideF447_mem_sup_of_commute (fun a ha i hi => (P.I_comm i hi a ha).symm) hh
  obtain ⟨H, hH⟩ : ∃ H : Subgroup M, H = subImg (burnsideF4d_bTwo β ε)
      (f447Ybar Gp M₂ Bbar ⊔ Ibar) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Subgroup M,
      C = Subgroup.centralizer ((imB β ε (f447Ybar Gp M₂ Bbar) : Subgroup M) : Set M) := ⟨_, rfl⟩
  have hHC : H ≤ C := by
    intro g hg
    rw [hH] at hg
    obtain ⟨h, hh₂, hhH, rfl⟩ := mem_subImg.mp hg
    rw [hC, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hYim₂] at hy
    obtain ⟨c, hc₂, hcY, rfl⟩ := mem_subImg.mp hy
    rw [commute_iff_of_injective hb2 hh₂ hc₂]
    obtain ⟨a, ha, i, hi, rfl⟩ := hprod h hhH
    calc c * (a * i) = (c * a) * i := by group
      _ = (a * c) * i := by rw [hYcomm c hcY a ha]
      _ = a * (c * i) := by group
      _ = a * (i * c) := by rw [← P.I_comm i hi c hcY]
      _ = (a * i) * c := by group
  have hi₀I : i₀ ∈ Ibar := P.X_le_I P.i₀_mem
  have hi₀M₂ : i₀ ∈ M₂ := P.I_le hi₀I
  have hi₀H : i₀ ∈ f447Ybar Gp M₂ Bbar ⊔ Ibar := Subgroup.mem_sup_right hi₀I
  have hi₀sq : i₀ * i₀ = 1 := P.X_sq i₀ P.i₀_mem
  obtain ⟨t, ht⟩ : ∃ t : M, t = burnsideF4d_bTwo β ε ⟨i₀, hi₀M₂⟩ := ⟨_, rfl⟩
  have ht2 : t * t = 1 := by
    rw [ht, ← map_mul]
    have : (⟨i₀, hi₀M₂⟩ * ⟨i₀, hi₀M₂⟩ : ↥M₂) = 1 := Subtype.ext hi₀sq
    rw [this, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    apply P.i₀_ne
    rw [ht, ← map_one (burnsideF4d_bTwo β ε)] at h
    exact congrArg Subtype.val (hb2 h)
  have htH : t ∈ H := by
    rw [hH, ht]
    exact mem_subImg_of_mem _ hi₀M₂ hi₀H
  obtain ⟨X, hX⟩ : ∃ X : Subgroup M, X = subImg (burnsideF4d_bTwo β ε) Xbar := ⟨_, rfl⟩
  have hXH : X ≤ H := by
    rw [hX, hH]
    exact subImg_mono _ (P.X_le_I.trans le_sup_right)
  have hXexp : ∀ x ∈ X, x ^ 2 = 1 := by
    intro x hx
    rw [hX] at hx
    obtain ⟨u, hu₂, huX, rfl⟩ := mem_subImg.mp hx
    rw [sq_eq_one_iff_of_injective hb2 hu₂, pow_two]
    exact P.X_sq u huX
  have hXodd : Odd (X.relIndex H) := by
    rw [hX, hH, burnsideF447_relIndex_subImg _ hb2 (P.X_le_I.trans le_sup_right) hHM₂]
    exact P.X_odd
  have hKlein : ∃ K : Subgroup M, K ≤ C ∧ Nat.card K = 4 ∧ ∀ x ∈ K, x ^ 2 = 1 := by
    obtain ⟨K, hKX, hKc⟩ := P.X_klein
    refine ⟨subImg (burnsideF4d_bTwo β ε) K, ?_, ?_, ?_⟩
    · refine le_trans ?_ hHC
      rw [hH]
      exact subImg_mono _ (hKX.trans (P.X_le_I.trans le_sup_right))
    · rw [card_subImg _ hb2 (hKX.trans hXM₂), hKc]
    · intro x hx
      obtain ⟨u, hu₂, huK, rfl⟩ := mem_subImg.mp hx
      rw [sq_eq_one_iff_of_injective hb2 hu₂, pow_two]
      exact P.X_sq u (hKX huK)
  have hconj : ∀ x ∈ H, x * x = 1 → x ≠ 1 → ∃ m ∈ H, m * t * m⁻¹ = x := by
    intro x hx hxx hx1
    rw [hH] at hx
    obtain ⟨h, hh₂, hhH, rfl⟩ := mem_subImg.mp hx
    obtain ⟨a, ha, i, hi, rfl⟩ := hprod h hhH
    have hh2 : (a * i) * (a * i) = 1 := by
      have : (⟨a * i, hh₂⟩ * ⟨a * i, hh₂⟩ : ↥M₂) = 1 := by
        apply hb2
        rw [map_mul, hxx, map_one]
      exact congrArg Subtype.val this
    have hai : (a * a) * (i * i) = 1 := by
      calc (a * a) * (i * i) = a * (a * i) * i := by group
        _ = a * (i * a) * i := by rw [← P.I_comm i hi a ha]
        _ = (a * i) * (a * i) := by group
        _ = 1 := hh2
    have haaI : a * a ∈ f447Ybar Gp M₂ Bbar ⊓ Ibar := by
      refine ⟨(f447Ybar Gp M₂ Bbar).mul_mem ha ha, ?_⟩
      have : a * a = (i * i)⁻¹ := eq_inv_of_mul_eq_one_left hai
      rw [this]
      exact Ibar.inv_mem (Ibar.mul_mem hi hi)
    rw [P.I_inf] at haaI
    have haa : a * a = 1 := Subgroup.mem_bot.mp haaI
    have ha1 : a = 1 := by
      have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact haa)
      have hodd := hBodd a (hYB ha)
      have h3 : orderOf a = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      exact orderOf_eq_one_iff.mp h3
    have hai1 : a * i = i := by rw [ha1, one_mul]
    have hiM₂ : i ∈ M₂ := P.I_le hi
    have hxeq : burnsideF4d_bTwo β ε ⟨a * i, hh₂⟩ = burnsideF4d_bTwo β ε ⟨i, hiM₂⟩ := by
      congr 1
      exact Subtype.ext hai1
    have hii : i * i = 1 := by
      have := hh2
      rwa [hai1] at this
    have hi1 : i ≠ 1 := by
      intro h
      apply hx1
      rw [hxeq]
      subst h
      exact map_one _
    obtain ⟨m, hmI, hm⟩ := P.I_conj i hi hii hi1
    have hmM₂ : m ∈ M₂ := P.I_le hmI
    refine ⟨burnsideF4d_bTwo β ε ⟨m, hmM₂⟩, ?_, ?_⟩
    · rw [hH]
      exact mem_subImg_of_mem _ hmM₂ (Subgroup.mem_sup_right hmI)
    · rw [hxeq, ht, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hm
  have hP₁ : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_right.trans inf_le_left)
  have hi₀M₁ : i₀ ∈ M₁ := hXM₁ P.i₀_mem
  obtain ⟨x, hx⟩ : ∃ x : M, x = burnsideF4d_bOne β ε ⟨xbar, P.x_mem⟩ := ⟨_, rfl⟩
  have htb1 : t = burnsideF4d_bOne β ε ⟨i₀, hi₀M₁⟩ := by
    rw [ht]
    exact (hagree i₀ hi₀M₁ hi₀M₂).symm
  have hzbarM₁ : xbar⁻¹ * i₀ * xbar ∈ M₁ :=
    M₁.mul_mem (M₁.mul_mem (M₁.inv_mem P.x_mem) hi₀M₁) P.x_mem
  have hzbarZZ : xbar⁻¹ * i₀ * xbar ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
    rw [P.x_ZZ]
    have : xbar * (xbar⁻¹ * i₀ * xbar) * xbar⁻¹ = i₀ := by group
    rw [this]
    exact P.i₀_mem
  have hz₀ : x⁻¹ * t * x = burnsideF4d_bOne β ε ⟨xbar⁻¹ * i₀ * xbar, hzbarM₁⟩ := by
    rw [hx, htb1, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hDZ : D.Z = subImg (burnsideF4d_bOne β ε) (centerOf (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) := by
    show centerOf D.S = _
    rw [hDS, burnsideF4d_SinM_eq, subImg_centerOf hb1 hP₁]
  have hz₀D : x⁻¹ * t * x ∈ D.Z := by
    rw [hz₀, hDZ]
    exact mem_subImg_of_mem _ hzbarM₁ hzbarZZ
  have hcent : ∀ g ∈ C, g * t = t * g → g ∈ H := by
    intro g hgC hgt
    have hgC' := Subgroup.mem_centralizer_iff.mp (hC ▸ hgC)
    have hg'z : (x⁻¹ * g * x) * (x⁻¹ * t * x) = (x⁻¹ * t * x) * (x⁻¹ * g * x) :=
      conj_commute hgt
    have hz0ne : x⁻¹ * t * x ≠ 1 := conj_ne_one' ht1
    have hg'M12 : x⁻¹ * g * x ∈ MiOne β ε ⊓ MiTwo β ε := hG.cent _ hz₀D hz0ne _ hg'z
    rw [burnsideF4d_inter_eq β hyp.faithful ε hyp.inj] at hg'M12
    obtain ⟨w, hw₁, hwM12, hwg⟩ := mem_subImg.mp hg'M12
    have hwz : w * (xbar⁻¹ * i₀ * xbar) = (xbar⁻¹ * i₀ * xbar) * w := by
      have h1 : burnsideF4d_bOne β ε ⟨xbar⁻¹ * i₀ * xbar, hzbarM₁⟩ *
          burnsideF4d_bOne β ε ⟨w, hw₁⟩ =
          burnsideF4d_bOne β ε ⟨w, hw₁⟩ *
          burnsideF4d_bOne β ε ⟨xbar⁻¹ * i₀ * xbar, hzbarM₁⟩ := by
        rw [hwg, ← hz₀]
        exact hg'z.symm
      exact ((commute_iff_of_injective hb1 hw₁ hzbarM₁).mp h1).symm
    have hwy : ∀ y ∈ f447Ybar Gp M₂ Bbar,
        w * (xbar⁻¹ * y * xbar) = (xbar⁻¹ * y * xbar) * w := by
      intro y hy
      have hyM₁ : y ∈ M₁ := hYM₁ hy
      have hŷM₁ : xbar⁻¹ * y * xbar ∈ M₁ := M₁.mul_mem (M₁.mul_mem (M₁.inv_mem P.x_mem) hyM₁) P.x_mem
      have hyim : burnsideF4d_bOne β ε ⟨y, hyM₁⟩ ∈ imB β ε (f447Ybar Gp M₂ Bbar) := by
        rw [hYim₁]
        exact mem_subImg_of_mem _ hyM₁ hy
      have hcomm := conj_commute (g := x) (hgC' _ hyim)
      have e1 : x⁻¹ * burnsideF4d_bOne β ε ⟨y, hyM₁⟩ * x =
          burnsideF4d_bOne β ε ⟨xbar⁻¹ * y * xbar, hŷM₁⟩ := by
        rw [hx, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e1, ← hwg] at hcomm
      exact ((commute_iff_of_injective hb1 hw₁ hŷM₁).mp hcomm).symm
    have hLV := P.LV7 hY w hwM12 hwz hwy
    have hsupL : Xbar ⊔ f447Ybar Gp M₂ Bbar ≤ f447Ybar Gp M₂ Bbar ⊔ Ibar :=
      sup_le (P.X_le_I.trans le_sup_right) le_sup_left
    have hLV' := hsupL hLV
    have hgbM₂ : xbar * w * xbar⁻¹ ∈ M₂ := hHM₂ hLV'
    have hgbM₁ : xbar * w * xbar⁻¹ ∈ M₁ :=
      M₁.mul_mem (M₁.mul_mem P.x_mem hw₁) (M₁.inv_mem P.x_mem)
    have hgeq : g = burnsideF4d_bTwo β ε ⟨xbar * w * xbar⁻¹, hgbM₂⟩ := by
      rw [← hagree _ hgbM₁ hgbM₂]
      have e2 : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
      rw [e2, ← hwg, hx, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hgeq, hH]
    exact mem_subImg_of_mem _ hgbM₂ hLV'
  have hCH : C ≤ H := by
    by_contra hnot
    have hne : H ≠ C := fun h => hnot (le_of_eq h.symm)
    have hsolv := burnsideF447_SE_solvable (C := C) (H := H) (W := X) hHC htH ht2 ht1 hcent
      hconj hne hXH hXexp hXodd hKlein
    haveI : Group.IsSolvable ↥H := hsolv
    let f₀ : ↥Ibar →* M := (burnsideF4d_bTwo β ε).comp (Subgroup.inclusion P.I_le)
    have hf₀ : Function.Injective f₀ := hb2.comp (Subgroup.inclusion_injective _)
    have hf₀H : ∀ u, f₀ u ∈ H := fun u => by
      rw [hH]
      exact mem_subImg_of_mem _ (P.I_le u.2) (Subgroup.mem_sup_right u.2)
    exact P.I_nonsolv (Group.isSolvable_of_isSolvable_injective (f := f₀.codRestrict H hf₀H)
      (fun a b h => hf₀ (congrArg Subtype.val h)))
  have hHeq : H = C := le_antisymm hHC hCH
  have hB0M12 : B0bar ≤ M₁ ⊓ M₂ := fun b hb => hB.1 ((hB0 b).mp hb).1
  have hB0eq : imB β ε B0bar = subImg (burnsideF4d_bTwo β ε) B0bar :=
    (burnsideF4d_Z4_imB_eq β ε hB0M12).trans
      (subImg_eq_of_agree hagree (hB0M12.trans inf_le_left) (hB0M12.trans inf_le_right))
  refine ⟨?_, ?_⟩
  ·
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hB0eq] at hg hy
      obtain ⟨a, ha₂, haB, rfl⟩ := mem_subImg.mp hg
      obtain ⟨c, hc₂, hcB, rfl⟩ := mem_subImg.mp hy
      exact (commute_iff_of_injective hb2 ha₂ hc₂).mpr (P.B0_comm c hcB a haB)
    · intro g hg
      have hgY : g ∈ C := by
        rw [hC, Subgroup.mem_centralizer_iff]
        intro y hy
        refine Subgroup.mem_centralizer_iff.mp hg y ?_
        rw [hYim₂] at hy
        rw [hB0eq]
        obtain ⟨c, hc₂, hcY, rfl⟩ := mem_subImg.mp hy
        exact mem_subImg_of_mem _ hc₂ (P.Y_le_B0 hcY)
      have hgH := hCH hgY
      rw [hH] at hgH
      obtain ⟨h, hh₂, hhH, rfl⟩ := mem_subImg.mp hgH
      obtain ⟨a, ha, i, hi, rfl⟩ := hprod h hhH
      have hiB : i ∈ B0bar := by
        refine P.I_cent_B0 i hi (fun b hb => ?_)
        have hbM₂ : b ∈ M₂ := (hB0M12 hb).2
        have h1 := Subgroup.mem_centralizer_iff.mp hg (burnsideF4d_bTwo β ε ⟨b, hbM₂⟩)
          (by rw [hB0eq]; exact mem_subImg_of_mem _ hbM₂ hb)
        have h2 := (commute_iff_of_injective hb2 hh₂ hbM₂).mp h1
        have h3 : a * b = b * a := P.B0_comm a (P.Y_le_B0 ha) b hb
        have h4 : b * i = i * b := by
          apply mul_left_cancel (a := a)
          calc a * (b * i) = (a * b) * i := by group
            _ = (b * a) * i := by rw [h3]
            _ = b * (a * i) := by group
            _ = (a * i) * b := h2
            _ = a * (i * b) := by group
        exact h4.symm
      rw [hB0eq]
      exact mem_subImg_of_mem _ hh₂ (B0bar.mul_mem (P.Y_le_B0 ha) hiB)
  ·
    rintro ⟨g, hg⟩
    have hginv : ∀ y ∈ imB β ε (f447Ybar Gp M₂ Bbar), g * y⁻¹ * g⁻¹ = y := by
      intro y hy
      have := hg y⁻¹ (Subgroup.inv_mem _ hy)
      simpa using this
    have hginv' : ∀ y ∈ imB β ε (f447Ybar Gp M₂ Bbar), g⁻¹ * y * g = y⁻¹ := by
      intro y hy
      calc g⁻¹ * y * g = g⁻¹ * (g * y⁻¹ * g⁻¹) * g := by rw [hginv y hy]
        _ = y⁻¹ := by group
    have hHcomm : ∀ u ∈ H, ∀ y ∈ imB β ε (f447Ybar Gp M₂ Bbar), y * u = u * y := by
      intro u hu y hy
      have := hHC hu
      rw [hC, Subgroup.mem_centralizer_iff] at this
      exact this y hy
    have hXg : ∀ u ∈ X, g * u * g⁻¹ ∈ H := by
      intro u hu
      have huH := hXH hu
      rw [hHeq, hC, Subgroup.mem_centralizer_iff]
      intro y hy
      have e1 : y * (g * u * g⁻¹) = g * (g⁻¹ * y * g) * u * g⁻¹ := by group
      rw [e1, hginv' y hy]
      have hyinv : y⁻¹ ∈ imB β ε (f447Ybar Gp M₂ Bbar) := Subgroup.inv_mem _ hy
      have h2 := hHcomm u huH y⁻¹ hyinv
      calc g * y⁻¹ * u * g⁻¹ = g * (y⁻¹ * u) * g⁻¹ := by group
        _ = g * (u * y⁻¹) * g⁻¹ := by rw [h2]
        _ = (g * u * g⁻¹) * (g * y⁻¹ * g⁻¹) := by group
        _ = (g * u * g⁻¹) * y := by rw [hginv y hy]
    have hSyl : IsSylowTwoOf X H := by
      refine ⟨hXH, ?_, ?_⟩
      · intro x
        refine ⟨1, ?_⟩
        apply Subtype.ext
        simpa [pow_two] using hXexp x x.2
      · intro h2
        exact (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr h2)
    have hSyl' : IsSylowTwoOf (X.map (MulAut.conj g).toMonoidHom) H := by
      refine isSylowTwoOf_of_card_eq ?_ ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        exact hXg u hu
      · exact (isPGroup_map_equiv_iff 2 (MulAut.conj g) X).mpr hSyl.isPGroup
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
        exact hSyl.card_eq
    obtain ⟨h, hhH, hXh⟩ := IsSylowTwoOf.exists_conj hSyl hSyl'
    have hnX : ∀ u ∈ X, (h⁻¹ * g) * u * (h⁻¹ * g)⁻¹ ∈ X := by
      intro u hu
      have : g * u * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := ⟨u, hu, rfl⟩
      rw [hXh] at this
      obtain ⟨v, hv, hvu⟩ := this
      have hvu' : h * v * h⁻¹ = g * u * g⁻¹ := by simpa using hvu
      have : (h⁻¹ * g) * u * (h⁻¹ * g)⁻¹ = v := by
        calc (h⁻¹ * g) * u * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * u * g⁻¹) * h := by group
          _ = h⁻¹ * (h * v * h⁻¹) * h := by rw [hvu']
          _ = v := by group
      rw [this]
      exact hv
    have hnY : ∀ y ∈ imB β ε (f447Ybar Gp M₂ Bbar), (h⁻¹ * g) * y * (h⁻¹ * g)⁻¹ = y⁻¹ := by
      intro y hy
      have h1 := hHcomm h hhH y⁻¹ (Subgroup.inv_mem _ hy)
      calc (h⁻¹ * g) * y * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * y * g⁻¹) * h := by group
        _ = h⁻¹ * y⁻¹ * h := by rw [hg y hy]
        _ = y⁻¹ := by
          calc h⁻¹ * y⁻¹ * h = h⁻¹ * (y⁻¹ * h) := by group
            _ = h⁻¹ * (h * y⁻¹) := by rw [h1]
            _ = y⁻¹ := by group
    have hnZ : ∀ z' ∈ D.Z, (x⁻¹ * (h⁻¹ * g) * x) * z' * (x⁻¹ * (h⁻¹ * g) * x)⁻¹ ∈ D.Z := by
      intro z' hz'
      rw [hDZ] at hz'
      obtain ⟨gb, hgb₁, hgbZ, rfl⟩ := mem_subImg.mp hz'
      have hxgb : xbar * gb * xbar⁻¹ ∈ Xbar := (P.x_ZZ gb).mp hgbZ
      have hxgbM₁ : xbar * gb * xbar⁻¹ ∈ M₁ :=
        M₁.mul_mem (M₁.mul_mem P.x_mem hgb₁) (M₁.inv_mem P.x_mem)
      have hxz : x * burnsideF4d_bOne β ε ⟨gb, hgb₁⟩ * x⁻¹ ∈ X := by
        have e : x * burnsideF4d_bOne β ε ⟨gb, hgb₁⟩ * x⁻¹ =
            burnsideF4d_bOne β ε ⟨xbar * gb * xbar⁻¹, hxgbM₁⟩ := by
          rw [hx, ← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e, hX, ← hX₂]
        exact mem_subImg_of_mem _ hxgbM₁ hxgb
      have hv := hnX _ hxz
      rw [hX, ← hX₂] at hv
      obtain ⟨vb, hvb₁, hvbX, hvb⟩ := mem_subImg.mp hv
      have hvZ : xbar⁻¹ * vb * xbar ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
        rw [P.x_ZZ]
        have : xbar * (xbar⁻¹ * vb * xbar) * xbar⁻¹ = vb := by group
        rw [this]
        exact hvbX
      have hvM₁ : xbar⁻¹ * vb * xbar ∈ M₁ :=
        M₁.mul_mem (M₁.mul_mem (M₁.inv_mem P.x_mem) hvb₁) P.x_mem
      rw [hDZ]
      have e3 : (x⁻¹ * (h⁻¹ * g) * x) * burnsideF4d_bOne β ε ⟨gb, hgb₁⟩ *
          (x⁻¹ * (h⁻¹ * g) * x)⁻¹ = burnsideF4d_bOne β ε ⟨xbar⁻¹ * vb * xbar, hvM₁⟩ := by
        have e4 : (x⁻¹ * (h⁻¹ * g) * x) * burnsideF4d_bOne β ε ⟨gb, hgb₁⟩ *
            (x⁻¹ * (h⁻¹ * g) * x)⁻¹ =
            x⁻¹ * ((h⁻¹ * g) * (x * burnsideF4d_bOne β ε ⟨gb, hgb₁⟩ * x⁻¹) * (h⁻¹ * g)⁻¹) * x := by
          group
        rw [e4, ← hvb, hx, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e3]
      exact mem_subImg_of_mem _ hvM₁ hvZ
    have hwM12 : x⁻¹ * (h⁻¹ * g) * x ∈ MiOne β ε ⊓ MiTwo β ε := hG.normalizer_Z hnZ
    rw [burnsideF4d_inter_eq β hyp.faithful ε hyp.inj] at hwM12
    obtain ⟨w, hw₁, hwM, hwn⟩ := mem_subImg.mp hwM12
    apply hY
    refine P.noInv w hwM (fun y hy => ?_)
    have hyM₁ : y ∈ M₁ := hYM₁ hy
    have hŷM₁ : xbar⁻¹ * y * xbar ∈ M₁ := M₁.mul_mem (M₁.mul_mem (M₁.inv_mem P.x_mem) hyM₁) P.x_mem
    have hyim : burnsideF4d_bOne β ε ⟨y, hyM₁⟩ ∈ imB β ε (f447Ybar Gp M₂ Bbar) := by
      rw [hYim₁]
      exact mem_subImg_of_mem _ hyM₁ hy
    have e1 : x⁻¹ * burnsideF4d_bOne β ε ⟨y, hyM₁⟩ * x =
        burnsideF4d_bOne β ε ⟨xbar⁻¹ * y * xbar, hŷM₁⟩ := by
      rw [hx, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hkey : burnsideF4d_bOne β ε ⟨w, hw₁⟩ *
        burnsideF4d_bOne β ε ⟨xbar⁻¹ * y * xbar, hŷM₁⟩ * (burnsideF4d_bOne β ε ⟨w, hw₁⟩)⁻¹ =
        (burnsideF4d_bOne β ε ⟨xbar⁻¹ * y * xbar, hŷM₁⟩)⁻¹ := by
      rw [hwn, ← e1]
      calc x⁻¹ * (h⁻¹ * g) * x * (x⁻¹ * burnsideF4d_bOne β ε ⟨y, hyM₁⟩ * x) *
            (x⁻¹ * (h⁻¹ * g) * x)⁻¹ =
          x⁻¹ * ((h⁻¹ * g) * burnsideF4d_bOne β ε ⟨y, hyM₁⟩ * (h⁻¹ * g)⁻¹) * x := by group
        _ = x⁻¹ * (burnsideF4d_bOne β ε ⟨y, hyM₁⟩)⁻¹ * x := by rw [hnY _ hyim]
        _ = (x⁻¹ * burnsideF4d_bOne β ε ⟨y, hyM₁⟩ * x)⁻¹ := by group
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv] at hkey
    have := congrArg Subtype.val (hb1 hkey)
    exact this

end ClauseTwoM

section Twist

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E] {f : ℕ}
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_Ctx.twist (C : burnsideF447_Ctx f Φ ρ Gp) (α : E ≃* E) (hα : Gp.map α.toMonoidHom = Gp) :
    burnsideF447_Ctx f (α.toMonoidHom.comp Φ) (ρ.comp α.symm.toMonoidHom) Gp where
  hf := C.hf
  hF := C.hF
  hΦ := α.injective.comp C.hΦ
  hρ := C.hρ.comp α.symm.injective
  hrange := by rw [MonoidHom.range_comp, C.hrange, hα]
  hΦρ := fun e p => by
    have h := C.hΦρ (α.symm e) p
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  hE := fun e => C.hE _

theorem burnsideF447_norm_twist (α : E ≃* E) (X : Subgroup (projectiveSL 3 F)) :
    Subgroup.normalizer ((X.map (α.toMonoidHom.comp Φ) : Subgroup E) : Set E) =
      (Subgroup.normalizer ((X.map Φ : Subgroup E) : Set E)).map α.toMonoidHom := by
  have e : X.map (α.toMonoidHom.comp Φ) = (X.map Φ).map α.toMonoidHom :=
    (Subgroup.map_map _ _ _).symm
  rw [e, Subgroup.map_normalizer_eq_of_bijective _ α.bijective]

theorem burnsideF447_Bt_twist (α : E ≃* E) :
    burnsideF447_Bt (α.toMonoidHom.comp Φ) = (burnsideF447_Bt Φ).map α.toMonoidHom := by
  unfold burnsideF447_Bt
  rw [burnsideF447_norm_twist α (projUnitriangular 3 F), burnsideF447_norm_twist α (torus3 F),
    Subgroup.map_inf _ _ _ α.injective]

theorem burnsideF447_map_conj_self {H : Subgroup E} {u : E} (hu : u ∈ H) :
    H.map (MulAut.conj u⁻¹).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    exact H.mul_mem (H.mul_mem (H.inv_mem hu) hy) hu
  · intro hx
    refine ⟨u * x * u⁻¹, H.mul_mem (H.mul_mem hu hx) (H.inv_mem hu), ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    group

theorem burnsideF447_map_conj_normal (H : Subgroup E) [H.Normal] (u : E) :
    H.map (MulAut.conj u⁻¹).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    have := Subgroup.Normal.conj_mem inferInstance y hy u⁻¹
    simpa using this
  · intro hx
    refine ⟨u * x * u⁻¹, Subgroup.Normal.conj_mem inferInstance x hx u, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    group

theorem burnsideF447_pkgV1' [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) (hodd : Odd Gp.index)
    {M₁ M₂ Bbar B0bar : Subgroup E}
    (h₁ : M₁ = Subgroup.normalizer (((V2 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E))
    (h₂ : M₂ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E))
    (hN : M₁ ⊓ M₂ = Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ)
    (hZcard : Nat.card ↥(ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) = Nat.card F)
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    ∃ (Ibar Xbar : Subgroup E) (xbar i₀ : E),
      burnsideF447_PkgOf Gp M₁ M₂ Bbar B0bar Ibar Xbar xbar i₀ := by
  haveI : Φ.range.Normal := by rw [C.hrange]; infer_instance
  have hodd' : Odd Φ.range.index := by rw [C.hrange]; exact hodd
  obtain ⟨u, hu, hconj⟩ := burnsideF447_hall_conj C.hq C.hΦ hodd' hN hB
  have huN : u ∈ M₁ ⊓ M₂ := by
    rw [hN]
    exact Subgroup.le_normalizer hu
  have hα : Gp.map (MulAut.conj u⁻¹).toMonoidHom = Gp := burnsideF447_map_conj_normal Gp u
  have C' := C.twist (MulAut.conj u⁻¹) hα
  have hBeq : Bbar = burnsideF447_Bt ((MulAut.conj u⁻¹).toMonoidHom.comp Φ) := by
    rw [burnsideF447_Bt_twist]
    ext y
    constructor
    · intro hy
      refine ⟨u * y * u⁻¹, (hconj y).mp hy, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      group
    · rintro ⟨b, hb, rfl⟩
      refine (hconj _).mpr ?_
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      have e : u * (u⁻¹ * b * u) * u⁻¹ = b := by group
      rw [e]
      exact hb
  refine ⟨_, _, _, _, burnsideF447_pkgV1 (Φ := (MulAut.conj u⁻¹).toMonoidHom.comp Φ)
    (ρ := ρ.comp (MulAut.conj u⁻¹).symm.toMonoidHom) C' ?_ ?_ ?_ ?_ hZcard hBeq hB.2.1 hB0⟩
  · rw [burnsideF447_norm_twist, ← h₁, burnsideF447_map_conj_self huN.1]
  · rw [burnsideF447_norm_twist, ← h₂, burnsideF447_map_conj_self huN.2]
  · rw [burnsideF447_norm_twist, ← hN, burnsideF447_map_conj_self huN]
  · rw [hS, ← Subgroup.map_map, burnsideF447_map_conj_self hu]

theorem burnsideF447_gamma_semilinear {σ : MulAut (projectiveSL 3 F)}
    (hσ : σ ∈ semilinearAutGroup 3 F) :
    gammaAut F * σ * (gammaAut F)⁻¹ ∈ semilinearAutGroup 3 F := by
  have hγinv : (gammaAut F)⁻¹ = gammaAut F :=
    inv_eq_of_mul_eq_one_right (gammaAut_mul_self F)
  have hδδ : dualAut 3 F * dualAut 3 F = 1 :=
    (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
  have hδc : ∀ A : GL (Fin 3) F, dualAut 3 F * conjAut 3 F A * dualAut 3 F =
      conjAut 3 F (Matrix.GeneralLinearGroup.inverseTranspose A) :=
    (standard_automorphism_transport (K := F) (n := 3)).2.2.2.2.1
  have hsem : ∀ A : GL (Fin 3) F, conjAut 3 F A ∈ semilinearAutGroup 3 F := fun A =>
    linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A)
  rw [hγinv, gammaAut]
  have e : conjAut 3 F (gammaJ F) * dualAut 3 F * σ * (conjAut 3 F (gammaJ F) * dualAut 3 F) =
      conjAut 3 F (gammaJ F) * (dualAut 3 F * σ * dualAut 3 F) *
        (dualAut 3 F * conjAut 3 F (gammaJ F) * dualAut 3 F) := by
    calc conjAut 3 F (gammaJ F) * dualAut 3 F * σ * (conjAut 3 F (gammaJ F) * dualAut 3 F)
        = conjAut 3 F (gammaJ F) * dualAut 3 F * σ * 1 * conjAut 3 F (gammaJ F) * dualAut 3 F := by
          group
      _ = conjAut 3 F (gammaJ F) * dualAut 3 F * σ * (dualAut 3 F * dualAut 3 F) *
            conjAut 3 F (gammaJ F) * dualAut 3 F := by rw [hδδ]
      _ = _ := by group
  rw [e, hδc]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsem _) (dualAut_mul_mul_dualAut_mem hσ)) (hsem _)

theorem burnsideF447_Ctx.swap (C : burnsideF447_Ctx f Φ ρ Gp) :
    burnsideF447_Ctx f (Φ.comp (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F))
      ((MulAut.conj (gammaAut F)).toMonoidHom.comp ρ) Gp where
  hf := C.hf
  hF := C.hF
  hΦ := C.hΦ.comp (gammaAut F).injective
  hρ := (MulAut.conj (gammaAut F)).injective.comp C.hρ
  hrange := by
    rw [← C.hrange]
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨gammaAut F p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨gammaAut F p, by simp [gammaAut_gammaAut]⟩
  hΦρ := fun e p => by
    have h := C.hΦρ e (gammaAut F p)
    have hγinv : (gammaAut F)⁻¹ = gammaAut F :=
      inv_eq_of_mul_eq_one_right (gammaAut_mul_self F)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_coe,
      MulAut.conj_apply, hγinv, MulAut.mul_apply]
    rw [gammaAut_gammaAut F]
    exact h
  hE := fun e => by
    show (MulAut.conj (gammaAut F)) (ρ e) ∈ semilinearAutGroup 3 F
    rw [MulAut.conj_apply]
    exact burnsideF447_gamma_semilinear (C.hE e)

theorem burnsideF447_pkgV2 [Gp.Normal] (C : burnsideF447_Ctx f Φ ρ Gp) (hodd : Odd Gp.index)
    {M₁ M₂ Bbar B0bar : Subgroup E}
    (h₁ : M₁ = Subgroup.normalizer (((V1 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E))
    (h₂ : M₂ = Subgroup.normalizer (((V2 : Subgroup (projectiveSL 3 F)).map Φ : Subgroup E) :
      Set E))
    (hN : M₁ ⊓ M₂ = Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E))
    (hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ)
    (hZcard : Nat.card ↥(ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) = Nat.card F)
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    ∃ (Ibar Xbar : Subgroup E) (xbar i₀ : E),
      burnsideF447_PkgOf Gp M₁ M₂ Bbar B0bar Ibar Xbar xbar i₀ := by
  have C' := C.swap
  have hV1 : (V1 : Subgroup (projectiveSL 3 F)).map
      (Φ.comp (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F)) =
      (V2 : Subgroup (projectiveSL 3 F)).map Φ := by
    rw [← Subgroup.map_map, gammaAut_map_V1]
  have hV2 : (V2 : Subgroup (projectiveSL 3 F)).map
      (Φ.comp (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F)) =
      (V1 : Subgroup (projectiveSL 3 F)).map Φ := by
    rw [← Subgroup.map_map, gammaAut_map_V2]
  have hU : (projUnitriangular 3 F).map
      (Φ.comp (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F)) =
      (projUnitriangular 3 F).map Φ := by
    rw [← Subgroup.map_map, gammaAut_map_U]
  refine burnsideF447_pkgV1' C' hodd ?_ ?_ ?_ ?_ hZcard hB hB0
  · rw [hV2]
    exact h₁
  · rw [hV1]
    exact h₂
  · rw [hU]
    exact hN
  · rw [hU]
    exact hS

end Twist

section Final

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3

theorem burnsideF447_pkg {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {Bbar B0bar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂))
    (hB0 : ∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) :
    ∃ (Ibar Xbar : Subgroup E) (xbar i₀ : E),
      burnsideF447_PkgOf Gp M₁ M₂ Bbar B0bar Ibar Xbar xbar i₀ := by
  haveI := hyp.amalgam.finite
  have hf : 2 ≤ f := burnsideF4d_L3_two_le_f hyp
  have hodd : Odd Gp.index := burnsideF4d_L3_odd hf hyp
  haveI := hyp.amalgam.toHypF_4_4g.normal
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hρ, hΦρ, hE, hD, hO,
    h₁, h₂, hRv⟩ := burnsideF447_setup hf hyp.amalgam.toHypF_4_4g
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hNp := burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂
  have C : burnsideF447_Ctx f Φ ρ Gp := ⟨hf, hFcard, hΦ, hρ, hrange, hΦρ, hE⟩
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ := by
    have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := burnsideF4d_Y2_pCore_le hf hyp.amalgam.toHypF_4_4g
    rw [burnsideF4d_pCoreOf_inf_eq (M₁ ⊓ M₂) hle]
    exact hNp.2
  have hZcard : Nat.card ↥(ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) = Nat.card F := by
    rw [burnsideF4d_Y2_card_Z hf hyp.amalgam.toHypF_4_4g, hFcard]
  rcases hRv with ⟨hR₁, hR₂⟩ | ⟨hR₁, hR₂⟩
  · subst hR₁ hR₂
    exact burnsideF447_pkgV2 C hodd h₁ h₂ hNp.1 hS hZcard hB hB0
  · subst hR₁ hR₂
    exact burnsideF447_pkgV1' C hodd h₁ h₂ hNp.1 hS hZcard hB hB0

section Target

theorem as_F_4_47 : F_4_47 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL hκ Bbar B0bar hB hB0
  subst hκ
  haveI := hyp.finite_M
  refine ⟨burnsideF447_clause1 hyp hB hB0, ?_, burnsideF447_clause3 hyp hB hB0⟩
  intro hYM
  obtain ⟨Ibar, Xbar, xbar, i₀, P⟩ := burnsideF447_pkg hyp hB hB0
  exact burnsideF447_clause2_M hyp hB hB0 P hYM

end Target

end Final

end CFSG.ASVolI
