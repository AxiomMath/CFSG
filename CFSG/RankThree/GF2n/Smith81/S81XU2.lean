module

public import CFSG.RankThree.GF2n.Smith81.S81XU1
public import CFSG.RankThree.GF2n.Smith81.S81XUBeta
public import CFSG.RankThree.GF2n.Smith81.S81XUWitt
public import CFSG.RankThree.GF2n.Smith81.S81XUSupp
public import CFSG.RankThree.GF2n.Smith81.S81XUCard
public import CFSG.RankThree.GF2n.Smith81.S81XUFive
public import CFSG.RankThree.GF2n.Smith81.S81XCore

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

theorem u6_iotaMulti_ne_zero_of_li {F : Type} [Field F] {v : Fin 3 → Fin 6 → F}
    (h : LinearIndependent F v) : exteriorPower.ιMulti F 3 v ≠ 0 := by
  have hinj : LinearMap.ker (Fintype.linearCombination F v) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (LinearIndependent.fintypeLinearCombination_injective h)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F v) hinj
  have hφv : ∀ j, φ (v j) = Pi.single j 1 := by
    intro j
    have := LinearMap.congr_fun hφ (Pi.single j 1)
    simpa [Fintype.linearCombination_apply_single] using this
  let Λ : (Fin 6 → F) [⋀^Fin 3]→ₗ[F] F :=
    (Matrix.detRowAlternating : (Fin 3 → F) [⋀^Fin 3]→ₗ[F] F).compLinearMap φ
  intro h0
  have h1 : (exteriorPower.alternatingMapLinearEquiv Λ) (exteriorPower.ιMulti F 3 v) = Λ v :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti Λ v
  rw [h0, map_zero] at h1
  have h2 : Λ v = 1 := by
    show Matrix.det (Matrix.of fun j => φ (v j)) = 1
    have : (Matrix.of fun j => φ (v j)) = (1 : Matrix (Fin 3) (Fin 3) F) := by
      ext j i
      rw [Matrix.of_apply, hφv j, Pi.single_apply, Matrix.one_apply]
      simp [eq_comm]
    rw [this, Matrix.det_one]
  rw [h2] at h1
  exact one_ne_zero h1.symm

section Bridge2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {ω : F}

theorem imgS0_mul' (H G : GL (Fin 6) F) :
    imgS0 (H * G) = (imgS0 G).map (Matrix.mulVecLin (H : Matrix (Fin 6) (Fin 6) F)) := by
  unfold imgS0
  rw [← Submodule.map_comp, Units.val_mul, Matrix.mulVecLin_mul]

private theorem mulVecLin_injective (g : GL (Fin 6) F) :
    Function.Injective (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) F)) := by
  rw [Matrix.coe_mulVecLin]
  exact Matrix.mulVec_injective_iff_isUnit.2 g.isUnit

private theorem finrank_map_mulVecLin (g : GL (Fin 6) F) (X : Submodule F (Fin 6 → F)) :
    Module.finrank F ↥(X.map (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) F))) =
      Module.finrank F ↥X :=
  (Submodule.equivMapOfInjective _ (mulVecLin_injective g) X).finrank_eq.symm

theorem kdimU_eq (hω : ω + σ ω = 1) (g : GL (Fin 6) F) :
    kdimU σ hω g =
      Module.finrank F ↥(imgS0 (g * frameGL σ ω hω) ⊓ imgS0 (frameGL σ ω hω)) := by
  set S := frameGL σ ω hω with hS
  have h1 : S * ucF σ hω g = g * S := by
    simp only [ucF, hS]
    group
  have h2 : (imgS0 (ucF σ hω g)).map (Matrix.mulVecLin (S : Matrix (Fin 6) (Fin 6) F)) =
      imgS0 (g * S) := by
    rw [← imgS0_mul', h1]
  have h3 : (S0 F).map (Matrix.mulVecLin (S : Matrix (Fin 6) (Fin 6) F)) = imgS0 S := rfl
  unfold kdimU
  rw [← finrank_map_mulVecLin S (imgS0 (ucF σ hω g) ⊓ S0 F),
    Submodule.map_inf _ (mulVecLin_injective S), h2, h3]

theorem u3_val_wact_p0 {K : Type} [Field K] {e : K ≃+* Fσ σ} (h : SUid σ 6) :
    e3uVal (e3uWact σ e h (e3uP0 σ e)) = rho F (h : GL (Fin 6) F) (pt0 F) := by
  rw [e3uWact_val]
  rfl

theorem u6_not_mem_W0 {K : Type} [Field K] (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1)
    (e : K ≃+* Fσ σ) (g : SUid σ 6) (hk : kdimU σ hω (g : GL (Fin 6) F) ≤ 1) :
    e3uWact σ e g (e3uP0 σ e) ∉ Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e) := by
  intro hmem
  have hdet : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 :=
    ((CFSG.ClassicalGroups.Unitary.mem_SUid_iff σ).mp g.2).1
  have h1 : rho F (frameGL σ ω hω)⁻¹ (e3uVal (e3uWact σ e g (e3uP0 σ e))) =
      rho F (ucF σ hω (g : GL (Fin 6) F)) (p0 F) := by
    rw [u3_val_wact_p0, rho_pt0_ucF hω (g : GL (Fin 6) F), ← rho_mul_apply, inv_mul_cancel,
      rho_one]
    rfl
  have hc : ∀ I : Set.powersetCard (Fin 6) 3,
      2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card →
        coord F (rho F (ucF σ hω (g : GL (Fin 6) F)) (p0 F)) I = 0 := by
    intro I hI
    rw [← h1]
    exact coord_hat_eq_zero_of_mem_Wsp hσ hω hmem I hI
  have hW0 := a5_mem_W0_of_support hc
  have h2 := (rho_p0_mem_W0_iff (ucF_det hω hdet)).mp hW0
  unfold kdimU at hk
  omega

theorem specialAt_wact_iff {K : Type} [Field K] (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1)
    (e : K ≃+* Fσ σ) (g : SUid σ 6) :
    SpecialAt (betaU e hσ.invol) (e3uP0 σ e) (e3uU0 σ e) (e3uWact σ e g) ↔
      kdimU σ hω (g : GL (Fin 6) F) = 1 := by
  have hdet : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 :=
    ((CFSG.ClassicalGroups.Unitary.mem_SUid_iff σ).mp g.2).1
  have hbeta : betaU e hσ.invol (e3uP0 σ e) (e3uWact σ e g (e3uP0 σ e)) = 0 ↔
      1 ≤ kdimU σ hω (g : GL (Fin 6) F) := by
    rw [← beta_pt0_rho_eq_zero_iff hω hdet]
    constructor
    · intro h0
      have h1 := betaU_apply e hσ.invol (e3uP0 σ e) (e3uWact σ e g (e3uP0 σ e))
      rw [h0, map_zero] at h1
      rw [u3_val_wact_p0] at h1
      exact h1.symm
    · intro h0
      apply e.injective
      apply Subtype.ext
      rw [map_zero]
      show ((e (betaU e hσ.invol (e3uP0 σ e) (e3uWact σ e g (e3uP0 σ e))) : Fσ σ) : F) = 0
      rw [betaU_apply e hσ.invol, u3_val_wact_p0]
      exact h0
  constructor
  · rintro ⟨h0, hn⟩
    have h1 := hbeta.mp h0
    have h2 : ¬ 2 ≤ kdimU σ hω (g : GL (Fin 6) F) := fun h2 => hn (u6_wact_mem_W0 hσ hω g h2)
    omega
  · intro hk
    exact ⟨hbeta.mpr (by omega), u6_not_mem_W0 hσ hω e g (by omega)⟩

theorem kdimU_inv_mul (hω : ω + σ ω = 1) (x y : SUid σ 6) :
    kdimU σ hω ((x⁻¹ * y : SUid σ 6) : GL (Fin 6) F) =
      Module.finrank F ↥(imgS0 ((y : GL (Fin 6) F) * frameGL σ ω hω) ⊓
        imgS0 ((x : GL (Fin 6) F) * frameGL σ ω hω)) := by
  set S := frameGL σ ω hω with hS
  have e1 : imgS0 ((x : GL (Fin 6) F) * (((x⁻¹ * y : SUid σ 6) : GL (Fin 6) F) * S)) =
      imgS0 ((y : GL (Fin 6) F) * S) := by
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [kdimU_eq]
  rw [← finrank_map_mulVecLin (x : GL (Fin 6) F)
    (imgS0 (((x⁻¹ * y : SUid σ 6) : GL (Fin 6) F) * S) ⊓ imgS0 S),
    Submodule.map_inf _ (mulVecLin_injective (x : GL (Fin 6) F)), ← imgS0_mul', ← imgS0_mul', e1]

theorem two_le_finrank_of_li {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V] {A : Submodule F V} {x y : V}
    (hx : x ∈ A) (hy : y ∈ A) (hli : LinearIndependent F ![x, y]) : 2 ≤ Module.finrank F ↥A := by
  have hle : Submodule.span F (Set.range ![x, y]) ≤ A := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hx
    · exact hy
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli] at h1
  simpa using h1

theorem imgS0_frame_eq_span (hω : ω + σ ω = 1) :
    imgS0 (frameGL σ ω hω) = Submodule.span F (Set.range (e3uT0Vec (F := F))) := by
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    have hv0 : ∀ j : Fin 6, j.val % 2 = 1 → v j = 0 := hv
    have hv' : v = ∑ j : Fin 3, v ⟨2 * j.val, by omega⟩ •
        (Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F)) := by
      funext r
      fin_cases r <;>
        simp [Fin.sum_univ_three, Pi.single_apply, hv0 1 (by decide), hv0 3 (by decide),
          hv0 5 (by decide)]
    have h2 : (Matrix.mulVecLin ((frameGL σ ω hω : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) v =
        ∑ j : Fin 3, v ⟨2 * j.val, by omega⟩ • e3uT0Vec j := by
      conv_lhs => rw [hv']
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul]
      congr 1
      exact frameMat_mulVec_even (σ := σ) ω j
    rw [h2]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F),
      s81A12_single_mem_S0 (by simp) 1, ?_⟩
    rw [Matrix.mulVecLin_apply]
    exact frameMat_mulVec_even (σ := σ) ω j

theorem herm_e3uT0Vec (σ : F ≃+* F) (i j : Fin 3) :
    herm σ (e3uT0Vec (F := F) i) (e3uT0Vec j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [herm, e3uT0Vec, Fin.sum_univ_six, CharTwo.add_self_eq_zero]

theorem herm_T0_zero (σ : F ≃+* F) (hω : ω + σ ω = 1) {x y : Fin 6 → F}
    (hx : x ∈ imgS0 (frameGL σ ω hω)) (hy : y ∈ imgS0 (frameGL σ ω hω)) : herm σ x y = 0 := by
  rw [imgS0_frame_eq_span] at hx hy
  have key : ∀ i : Fin 3, ∀ y ∈ Submodule.span F (Set.range (e3uT0Vec (F := F))),
      herm σ (e3uT0Vec i) y = 0 := by
    intro i y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact herm_e3uT0Vec σ i j
    | zero => simp [herm]
    | add y y' _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
    | smul c y _ h => rw [herm_smul_right, h, mul_zero]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact key i y hy
  | zero => simp [herm]
  | add x x' _ _ h1 h2 => rw [herm_add_left, h1, h2, add_zero]
  | smul c x _ h => rw [herm_smul_left, h, mul_zero]

theorem herm_Tg_zero (σ : F ≃+* F) (hω : ω + σ ω = 1) (g : SUid σ 6) {x y : Fin 6 → F}
    (hx : x ∈ imgS0 ((g : GL (Fin 6) F) * frameGL σ ω hω))
    (hy : y ∈ imgS0 ((g : GL (Fin 6) F) * frameGL σ ω hω)) : herm σ x y = 0 := by
  rw [imgS0_mul'] at hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.mp hy
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  rw [((CFSG.ClassicalGroups.Unitary.mem_SUid_iff σ).mp g.2).2 x₀ y₀]
  exact herm_T0_zero σ hω hx₀ hy₀

theorem imgS0_su_eq_span (hω : ω + σ ω = 1) (h : SUid σ 6) {l : F} (hl : l ≠ 0)
    {v : Fin 3 → Fin 6 → F}
    (h0 : ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 0) = l • v 0)
    (h1 : ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 1) = v 1)
    (h2 : ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 2) = v 2) :
    imgS0 ((h : GL (Fin 6) F) * frameGL σ ω hω) = Submodule.span F (Set.range v) := by
  rw [imgS0_mul', imgS0_frame_eq_span, Submodule.map_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    show ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec j) ∈ _
    fin_cases j
    · show ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 0) ∈ _
      rw [h0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · show ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 1) ∈ _
      rw [h1]
      exact Submodule.subset_span ⟨1, rfl⟩
    · show ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 2) ∈ _
      rw [h2]
      exact Submodule.subset_span ⟨2, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hmem : ∀ k : Fin 3, ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec k) ∈
        Submodule.span F (((Matrix.mulVecLin ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) ''
          Set.range (e3uT0Vec (F := F)))) := fun k =>
      Submodule.subset_span ⟨e3uT0Vec k, ⟨k, rfl⟩, rfl⟩
    fin_cases j
    · have h' : v 0 = l⁻¹ • ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 0) := by
        rw [h0, smul_smul, inv_mul_cancel₀ hl, one_smul]
      show v 0 ∈ _
      rw [h']
      exact Submodule.smul_mem _ _ (hmem 0)
    · show v 1 ∈ _
      rw [← h1]
      exact hmem 1
    · show v 2 ∈ _
      rw [← h2]
      exact hmem 2

theorem finrank_inf_span_eq_one {a b c d e : Fin 6 → F} (hli : LinearIndependent F ![a, b, c, d, e]) :
    Module.finrank F ↥(Submodule.span F (Set.range ![a, c, e]) ⊓
      Submodule.span F (Set.range ![a, b, d])) = 1 := by
  have ha0 : a ≠ 0 := by
    intro h0
    have := hli.ne_zero 0
    simp [h0] at this
  have hle : Submodule.span F (Set.range ![a, c, e]) ⊓ Submodule.span F (Set.range ![a, b, d]) ≤
      Submodule.span F {a} := by
    intro y hy
    obtain ⟨hy2, hy1⟩ := Submodule.mem_inf.mp hy
    obtain ⟨c1, hc1⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hy1
    obtain ⟨c2, hc2⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hy2
    simp [Fin.sum_univ_three] at hc1 hc2
    have h0 : ∑ i : Fin 5, (![c1 0 - c2 0, c1 1, -c2 1, c1 2, -c2 2] i) •
        (![a, b, c, d, e] i) = 0 := by
      simp [Fin.sum_univ_five, sub_smul, neg_smul]
      have h3 : c1 0 • a + c1 1 • b + c1 2 • d = c2 0 • a + c2 1 • c + c2 2 • e := hc1.trans hc2.symm
      calc c1 0 • a - c2 0 • a + c1 1 • b + -(c2 1 • c) + c1 2 • d + -(c2 2 • e)
          = (c1 0 • a + c1 1 • b + c1 2 • d) - (c2 0 • a + c2 1 • c + c2 2 • e) := by abel
        _ = 0 := by rw [h3, sub_self]
    have hz := (Fintype.linearIndependent_iff.mp hli) _ h0
    have h1 : c1 1 = 0 := by simpa using hz 1
    have h2 : c1 2 = 0 := by simpa using hz 3
    rw [← hc1, h1, h2, zero_smul, zero_smul, add_zero, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  apply le_antisymm
  · have h := Submodule.finrank_mono hle
    rw [finrank_span_singleton ha0] at h
    exact h
  · refine Nat.succ_le_of_lt (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨a, ?_⟩, ?_⟩)
    · exact Submodule.mem_inf.mpr ⟨Submodule.subset_span ⟨0, rfl⟩, Submodule.subset_span ⟨0, rfl⟩⟩
    · intro h
      exact ha0 (congrArg Subtype.val h)

theorem u6_lemmaS_group (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1) (g : SUid σ 6)
    (hk : kdimU σ hω (g : GL (Fin 6) F) = 1) :
    ∃ h₁ h₂ : SUid σ 6, 2 ≤ kdimU σ hω (h₁ : GL (Fin 6) F) ∧ 2 ≤ kdimU σ hω (h₂ : GL (Fin 6) F) ∧
      2 ≤ kdimU σ hω ((g⁻¹ * h₁ : SUid σ 6) : GL (Fin 6) F) ∧
      2 ≤ kdimU σ hω ((g⁻¹ * h₂ : SUid σ 6) : GL (Fin 6) F) ∧
      kdimU σ hω ((h₁⁻¹ * h₂ : SUid σ 6) : GL (Fin 6) F) = 1 := by
  set S := frameGL σ ω hω with hS
  have hk' : Module.finrank F ↥(imgS0 ((g : GL (Fin 6) F) * S) ⊓ imgS0 S) = 1 := by
    rw [← kdimU_eq]
    exact hk
  obtain ⟨a, b, c, d, e, hli, haS, hbS, hcS, haT, hdT, heT, hbd, hce⟩ :=
    u6_exists_five hσ (finrank_imgS0 S) (finrank_imgS0 ((g : GL (Fin 6) F) * S))
      (fun x hx y hy => herm_T0_zero σ hω hx hy) (fun x hx y hy => herm_Tg_zero σ hω g hx hy)
      (by rw [inf_comm]; exact hk')
  have key : ∀ (x y z : Fin 6 → F), LinearIndependent F ![x, y, z] →
      (∀ i j, ∑ k, σ (![x, y, z] i k) * ![x, y, z] j k = 0) →
      ∃ h : SUid σ 6, imgS0 ((h : GL (Fin 6) F) * S) = Submodule.span F (Set.range ![x, y, z]) := by
    intro x y z hl ht
    obtain ⟨h, l, hl0, h0, h1, h2⟩ := u6_exists_su_of_ti hσ (u6_iotaMulti_ne_zero_of_li hl) ht
    exact ⟨h, imgS0_su_eq_span hω h hl0 h0 h1 h2⟩
  have hli1 : LinearIndependent F ![a, b, d] := by
    have h := hli.comp ![0, 1, 3] (by decide)
    have e1 : (![a, b, c, d, e] ∘ ![0, 1, 3] : Fin 3 → Fin 6 → F) = ![a, b, d] := by
      funext i
      fin_cases i <;> rfl
    rwa [e1] at h
  have hli2 : LinearIndependent F ![a, c, e] := by
    have h := hli.comp ![0, 2, 4] (by decide)
    have e1 : (![a, b, c, d, e] ∘ ![0, 2, 4] : Fin 3 → Fin 6 → F) = ![a, c, e] := by
      funext i
      fin_cases i <;> rfl
    rwa [e1] at h
  have hdb : herm σ d b = 0 := by
    rw [herm_conj σ hσ.invol b d, hbd, map_zero]
  have hec : herm σ e c = 0 := by
    rw [herm_conj σ hσ.invol c e, hce, map_zero]
  have hti1 : ∀ i j, ∑ k, σ (![a, b, d] i k) * ![a, b, d] j k = 0 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact herm_T0_zero σ hω haS haS
    · exact herm_T0_zero σ hω haS hbS
    · exact herm_Tg_zero σ hω g haT hdT
    · exact herm_T0_zero σ hω hbS haS
    · exact herm_T0_zero σ hω hbS hbS
    · exact hbd
    · exact herm_Tg_zero σ hω g hdT haT
    · exact hdb
    · exact herm_Tg_zero σ hω g hdT hdT
  have hti2 : ∀ i j, ∑ k, σ (![a, c, e] i k) * ![a, c, e] j k = 0 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact herm_T0_zero σ hω haS haS
    · exact herm_T0_zero σ hω haS hcS
    · exact herm_Tg_zero σ hω g haT heT
    · exact herm_T0_zero σ hω hcS haS
    · exact herm_T0_zero σ hω hcS hcS
    · exact hce
    · exact herm_Tg_zero σ hω g heT haT
    · exact hec
    · exact herm_Tg_zero σ hω g heT heT
  obtain ⟨h₁, hY₁⟩ := key a b d hli1 hti1
  obtain ⟨h₂, hY₂⟩ := key a c e hli2 hti2
  have hab : LinearIndependent F ![a, b] := by
    have h := hli.comp ![0, 1] (by decide)
    have e1 : (![a, b, c, d, e] ∘ ![0, 1] : Fin 2 → Fin 6 → F) = ![a, b] := by
      funext i
      fin_cases i <;> rfl
    rwa [e1] at h
  have had : LinearIndependent F ![a, d] := by
    have h := hli.comp ![0, 3] (by decide)
    have e1 : (![a, b, c, d, e] ∘ ![0, 3] : Fin 2 → Fin 6 → F) = ![a, d] := by
      funext i
      fin_cases i <;> rfl
    rwa [e1] at h
  have hac : LinearIndependent F ![a, c] := by
    have h := hli.comp ![0, 2] (by decide)
    have e1 : (![a, b, c, d, e] ∘ ![0, 2] : Fin 2 → Fin 6 → F) = ![a, c] := by
      funext i
      fin_cases i <;> rfl
    rwa [e1] at h
  have hae : LinearIndependent F ![a, e] := by
    have h := hli.comp ![0, 4] (by decide)
    have e1 : (![a, b, c, d, e] ∘ ![0, 4] : Fin 2 → Fin 6 → F) = ![a, e] := by
      funext i
      fin_cases i <;> rfl
    rwa [e1] at h
  have mem1 : ∀ {x : Fin 6 → F}, x ∈ Set.range ![a, b, d] → x ∈ imgS0 ((h₁ : GL (Fin 6) F) * S) :=
    fun hx => hY₁ ▸ Submodule.subset_span hx
  have mem2 : ∀ {x : Fin 6 → F}, x ∈ Set.range ![a, c, e] → x ∈ imgS0 ((h₂ : GL (Fin 6) F) * S) :=
    fun hx => hY₂ ▸ Submodule.subset_span hx
  refine ⟨h₁, h₂, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h := kdimU_inv_mul hω 1 h₁
    rw [inv_one, one_mul] at h
    rw [h]
    refine two_le_finrank_of_li (x := a) (y := b) ?_ ?_ hab
    · exact Submodule.mem_inf.mpr ⟨mem1 ⟨0, rfl⟩, by simpa using haS⟩
    · exact Submodule.mem_inf.mpr ⟨mem1 ⟨1, rfl⟩, by simpa using hbS⟩
  · have h := kdimU_inv_mul hω 1 h₂
    rw [inv_one, one_mul] at h
    rw [h]
    refine two_le_finrank_of_li (x := a) (y := c) ?_ ?_ hac
    · exact Submodule.mem_inf.mpr ⟨mem2 ⟨0, rfl⟩, by simpa using haS⟩
    · exact Submodule.mem_inf.mpr ⟨mem2 ⟨1, rfl⟩, by simpa using hcS⟩
  · rw [kdimU_inv_mul hω g h₁]
    refine two_le_finrank_of_li (x := a) (y := d) ?_ ?_ had
    · exact Submodule.mem_inf.mpr ⟨mem1 ⟨0, rfl⟩, haT⟩
    · exact Submodule.mem_inf.mpr ⟨mem1 ⟨2, rfl⟩, hdT⟩
  · rw [kdimU_inv_mul hω g h₂]
    refine two_le_finrank_of_li (x := a) (y := e) ?_ ?_ hae
    · exact Submodule.mem_inf.mpr ⟨mem2 ⟨0, rfl⟩, haT⟩
    · exact Submodule.mem_inf.mpr ⟨mem2 ⟨2, rfl⟩, heT⟩
  · rw [kdimU_inv_mul hω h₁ h₂, hY₁, hY₂]
    exact finrank_inf_span_eq_one hli

section WLevel

variable {K : Type} [Field K]

theorem u6_lemmaS_W (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1) (e : K ≃+* Fσ σ) :
    ∀ g ∈ e3uGam σ e, SpecialAt (betaU e hσ.invol) (e3uP0 σ e) (e3uU0 σ e) g →
      ∃ h₁ ∈ e3uGam σ e, ∃ h₂ ∈ e3uGam σ e,
        h₁ (e3uP0 σ e) ∈ Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e) ∧
        h₂ (e3uP0 σ e) ∈ Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e) ∧
        g⁻¹ (h₁ (e3uP0 σ e)) ∈ Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e) ∧
        g⁻¹ (h₂ (e3uP0 σ e)) ∈ Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e) ∧
        SpecialAt (betaU e hσ.invol) (e3uP0 σ e) (e3uU0 σ e) (h₁⁻¹ * h₂) := by
  intro g hg hs
  obtain ⟨ĝ, rfl⟩ := MonoidHom.mem_range.mp (show g ∈ (e3uWact σ e).range from hg)
  have hk := (specialAt_wact_iff hσ hω e ĝ).mp hs
  obtain ⟨ĥ₁, ĥ₂, hk₁, hk₂, hk₁', hk₂', hk₁₂⟩ := u6_lemmaS_group hσ hω ĝ hk
  have e1 : ∀ x : SUid σ 6, (e3uWact σ e ĝ)⁻¹ (e3uWact σ e x (e3uP0 σ e)) =
      e3uWact σ e (ĝ⁻¹ * x) (e3uP0 σ e) := by
    intro x
    rw [map_mul, map_inv, LinearEquiv.mul_apply]
  refine ⟨e3uWact σ e ĥ₁, ⟨ĥ₁, rfl⟩, e3uWact σ e ĥ₂, ⟨ĥ₂, rfl⟩, u6_wact_mem_W0 hσ hω ĥ₁ hk₁,
    u6_wact_mem_W0 hσ hω ĥ₂ hk₂, ?_, ?_, ?_⟩
  · rw [e1]
    exact u6_wact_mem_W0 hσ hω _ hk₁'
  · rw [e1]
    exact u6_wact_mem_W0 hσ hω _ hk₂'
  · have e2 : (e3uWact σ e ĥ₁)⁻¹ * e3uWact σ e ĥ₂ = e3uWact σ e (ĥ₁⁻¹ * ĥ₂) := by
      rw [map_mul, map_inv]
    rw [e2]
    exact (specialAt_wact_iff hσ hω e _).mpr hk₁₂

theorem u6_lemmaT_W (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1) (e : K ≃+* Fσ σ) :
    ∀ g ∈ e3uGam σ e, SpecialAt (betaU e hσ.invol) (e3uP0 σ e) (e3uU0 σ e) g →
      ∀ u ∈ e3uU0 σ e ⊓ conjSub g (e3uU0 σ e), u ≠ 1 →
        ∃ t : SUid σ 6, IsTransvec F (t : GL (Fin 6) F) ∧ u = e3uWact σ e t := by
  intro g hg hs u hu hu1
  obtain ⟨ĝ, rfl⟩ := MonoidHom.mem_range.mp (show g ∈ (e3uWact σ e).range from hg)
  have hk := (specialAt_wact_iff hσ hω e ĝ).mp hs
  obtain ⟨hu₁, hu₂⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨ũ, hũ, rfl⟩ := Subgroup.mem_map.mp (show u ∈ (e3uU0Sub σ).map (e3uWact σ e) from hu₁)
  obtain ⟨u₀, hu₀, hu₀eq⟩ := mem_conjSub.mp hu₂
  obtain ⟨ũ₂, hũ₂, rfl⟩ := Subgroup.mem_map.mp (show u₀ ∈ (e3uU0Sub σ).map (e3uWact σ e) from hu₀)
  have heq : e3uWact σ e ũ = e3uWact σ e (ĝ * ũ₂ * ĝ⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact hu₀eq.symm
  have hne : (ũ : GL (Fin 6) F) ≠ 1 := by
    intro h
    apply hu1
    have : ũ = 1 := Subtype.ext h
    rw [this, map_one]
  exact ⟨ũ, u6_transvec_of_kdim_one hσ hω e hũ hũ₂ heq hk hne, rfl⟩

theorem u6_transvec_conj (e : K ≃+* Fσ σ) {g : E3UWspace σ e ≃ₗ[K] E3UWspace σ e}
    (hg : g ∈ e3uGam σ e) {u : E3UWspace σ e ≃ₗ[K] E3UWspace σ e}
    (hu : ∃ t : SUid σ 6, IsTransvec F (t : GL (Fin 6) F) ∧ u = e3uWact σ e t) :
    ∃ t : SUid σ 6, IsTransvec F (t : GL (Fin 6) F) ∧ g * u * g⁻¹ = e3uWact σ e t := by
  obtain ⟨ĝ, rfl⟩ := MonoidHom.mem_range.mp (show g ∈ (e3uWact σ e).range from hg)
  obtain ⟨t, ht, rfl⟩ := hu
  refine ⟨ĝ * t * ĝ⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  have h := IsTransvec.conj' ht (ĝ : GL (Fin 6) F)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem u6_fe2Geom [Finite K] (hσ : IsUnitaryInvolution σ) (hF : Nat.card F = Nat.card K ^ 2)
    (e : K ≃+* Fσ σ) :
    Fe2Geom (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e) (betaU e hσ.invol) 10 := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  exact
    { geom := u6_MinuscGeom hσ hF
      β_inv := fun g hg v w => by
        obtain ⟨ĝ, rfl⟩ := MonoidHom.mem_range.mp (show g ∈ (e3uWact σ e).range from hg)
        exact betaU_wact e hσ.invol ĝ v w
      β_skew := fun v w => betaU_skew e hσ.invol v w
      U_card := u6_U_card hσ hF
      U_norm := u6_U_norm hσ hω e
      lemmaS := u6_lemmaS_W hσ hω e }

end WLevel

end Bridge2

end CFSG.RankThree.GF2n.Smith81
