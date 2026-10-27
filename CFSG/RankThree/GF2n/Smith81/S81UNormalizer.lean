module

public import CFSG.RankThree.GF2n.Smith81.S81UForm
public import CFSG.RankThree.GF2n.Smith81.S81UTrans
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSU

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

@[expose] noncomputable def sigmaC (τ : F ≃+* F) : Cube F →+ Cube F where
  toFun ξ := ∑ I : Set.powersetCard (Fin 6) 3, τ (coord F ξ I) • cubeBasis F I
  map_zero' := by simp [coord_zero]
  map_add' a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [coord_add, map_add, add_smul]

private theorem h55_sigmaC_apply (τ : F ≃+* F) (ξ : Cube F) :
    sigmaC τ ξ = ∑ I : Set.powersetCard (Fin 6) 3, τ (coord F ξ I) • cubeBasis F I := rfl

theorem coord_sigmaC (τ : F ≃+* F) (ξ : Cube F) (I : Set.powersetCard (Fin 6) 3) :
    coord F (sigmaC τ ξ) I = τ (coord F ξ I) := by
  rw [h55_sigmaC_apply]
  unfold coord
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single I]
  · simp [Finsupp.single_apply]
  · intro J _ hJ
    simp [Finsupp.single_apply, hJ]
  · intro h
    exact absurd (Finset.mem_univ I) h

theorem sigmaC_smul (τ : F ≃+* F) (c : F) (ξ : Cube F) : sigmaC τ (c • ξ) = τ c • sigmaC τ ξ := by
  apply (cubeBasis F).ext_elem
  intro I
  show coord F (sigmaC τ (c • ξ)) I = coord F (τ c • sigmaC τ ξ) I
  rw [coord_sigmaC, coord_smul, coord_smul, coord_sigmaC, map_mul]

private theorem h55_cmat_glAut (τ : F ≃+* F) (g : GL (Fin 6) F) (I J : Idx) :
    cmat (glAut τ g) I J = τ (cmat g I J) := by
  rw [cmat_apply_det, cmat_apply_det, RingEquiv.map_det]
  congr 1

theorem sigmaC_rho (τ : F ≃+* F) (g : GL (Fin 6) F) (ξ : Cube F) :
    sigmaC τ (rho F g ξ) = rho F (glAut τ g) (sigmaC τ ξ) := by
  apply (cubeBasis F).ext_elem
  intro I
  show coord F (sigmaC τ (rho F g ξ)) I = coord F (rho F (glAut τ g) (sigmaC τ ξ)) I
  rw [coord_sigmaC, coord_rho, coord_rho, map_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [coord_sigmaC, h55_cmat_glAut, map_mul]

theorem theta_sigmaC {τ : F ≃+* F} (hτ : ∀ c, σ (τ c) = τ (σ c)) (ξ : Cube F) :
    theta σ (sigmaC τ ξ) = sigmaC τ (theta σ ξ) := by
  apply (cubeBasis F).ext_elem
  intro a
  show coord F (theta σ (sigmaC τ ξ)) a = coord F (sigmaC τ (theta σ ξ)) a
  rw [coord_theta', coord_sigmaC, coord_sigmaC, coord_theta']
  exact hτ _

theorem sigmaC_sigmaC {τ τ' : F ≃+* F} (h : ∀ c, τ (τ' c) = c) (ξ : Cube F) :
    sigmaC τ (sigmaC τ' ξ) = ξ := by
  apply (cubeBasis F).ext_elem
  intro I
  show coord F (sigmaC τ (sigmaC τ' ξ)) I = coord F ξ I
  rw [coord_sigmaC, coord_sigmaC, h]

theorem sigmaC_refl (ξ : Cube F) : sigmaC (RingEquiv.refl F) ξ = ξ := by
  apply (cubeBasis F).ext_elem
  intro I
  show coord F (sigmaC (RingEquiv.refl F) ξ) I = coord F ξ I
  rw [coord_sigmaC, RingEquiv.refl_apply]

theorem det_norm_one {B : GL (Fin 6) F}
    (hB : conjTr σ (B : Matrix (Fin 6) (Fin 6) F) * (B : Matrix (Fin 6) (Fin 6) F) = 1) :
    σ (B : Matrix (Fin 6) (Fin 6) F).det * (B : Matrix (Fin 6) (Fin 6) F).det = 1 := by
  have h1 : σ (B : Matrix (Fin 6) (Fin 6) F).det =
      (conjTr σ (B : Matrix (Fin 6) (Fin 6) F)).det := by
    rw [conjTr, Matrix.det_transpose, RingEquiv.map_det]
    rfl
  rw [h1, ← Matrix.det_mul, hB, Matrix.det_one]

theorem exists_mu (hσ : ∀ c, σ (σ c) = c) {d : F} (hd : σ d * d = 1) :
    ∃ μ : F, μ ≠ 0 ∧ σ μ = d * μ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases h1 : d = 1
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [h1, map_one, mul_one]
  · refine ⟨1 + σ d, ?_, ?_⟩
    · intro hμ
      have hσd : σ d = 1 := by linear_combination hμ - h2
      rw [hσd, one_mul] at hd
      exact h1 hd
    · rw [map_add, map_one, hσ d]
      linear_combination (-1 : F) * hd

theorem conjTr_glAut_unitary {τ : F ≃+* F} (hτ : ∀ c, σ (τ c) = τ (σ c)) {P : GL (Fin 6) F}
    (hP : conjTr σ (P : Matrix (Fin 6) (Fin 6) F) * (P : Matrix (Fin 6) (Fin 6) F) = 1) :
    conjTr σ ((glAut τ P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((glAut τ P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
  have hc : ∀ M : Matrix (Fin 6) (Fin 6) F, conjTr σ (M.map τ) = (conjTr σ M).map τ := by
    intro M
    ext i j
    simp [conjTr, hτ]
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, hc, ← Matrix.map_mul, hP,
    Matrix.map_one (τ : F → F) (map_zero τ) (map_one τ)]

theorem tau_cases (hσ : IsUnitaryInvolution σ) {τ : F ≃+* F} (h : ∀ c, σ c = c → τ c = c) :
    τ = RingEquiv.refl F ∨ τ = σ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨om, hom⟩ := hσ.trace_surj 1 (map_one σ)
  have hq : om * om + om + om * σ om = 0 := by
    linear_combination om * hom + om * h2
  have hnfix : σ (om * σ om) = om * σ om := by
    rw [map_mul, hσ.invol]
    ring
  have hn : τ (om * σ om) = om * σ om := h _ hnfix
  have hx : τ om * τ om + τ om + om * σ om = 0 := by
    have e : τ (om * om + om + om * σ om) = τ om * τ om + τ om + om * σ om := by
      rw [map_add, map_add, map_mul τ om om, hn]
    rw [← e, hq, map_zero]
  have hfac : (τ om - om) * (τ om - σ om) = 0 := by
    linear_combination hx - (τ om) * hom - (τ om) * h2
  have h_fix_a : ∀ c : F, σ (c * σ om + σ c * om) = c * σ om + σ c * om := by
    intro c
    rw [map_add, map_mul, map_mul, hσ.invol, hσ.invol]
    ring
  have h_fix_b : ∀ c : F, σ (c + σ c) = c + σ c := by
    intro c
    rw [map_add, hσ.invol]
    ring
  have h_decomp : ∀ c : F, c = (c * σ om + σ c * om) + (c + σ c) * om := by
    intro c
    linear_combination (-c) * hom - (σ c * om) * h2
  have key : ∀ a b : F, σ a = a → σ b = b → τ (a + b * om) = a + b * τ om := by
    intro a b ha hb
    rw [map_add, map_mul, h a ha, h b hb]
  have key2 : ∀ c : F, τ c = (c * σ om + σ c * om) + (c + σ c) * τ om := fun c =>
    (congrArg τ (h_decomp c)).trans (key _ _ (h_fix_a c) (h_fix_b c))
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left
    have hx' : τ om = om := sub_eq_zero.mp h1
    ext c
    rw [key2 c, hx', RingEquiv.refl_apply]
    linear_combination c * hom + (σ c * om) * h2
  · right
    have hx' : τ om = σ om := sub_eq_zero.mp h1
    ext c
    rw [key2 c, hx']
    linear_combination (σ c) * hom + (c * σ om) * h2

@[expose] def NormalizesU (σ : F ≃+* F) (T : Wform σ ≃ₗ[Fσ σ] Wform σ) : Prop :=
  ∀ g : SUid σ 6, ∃ g' : SUid σ 6, T * Wact σ g = Wact σ g' * T

@[expose] def toStated [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (g : SUid (unitaryInvolution F 2 f) 6) :
    CFSG.Open.StatedSU 6 (2 ^ f) F :=
  ⟨(g : GL (Fin 6) F), (SUid_eq_statedSU hF 6).le g.2⟩

theorem wact_eq_of_twist {T : Wform σ ≃ₗ[Fσ σ] Wform σ} {g g₁ g₂ : SUid σ 6}
    (h₁ : T * Wact σ g = Wact σ g₁ * T) (h₂ : T * Wact σ g = Wact σ g₂ * T) :
    Wact σ g₁ = Wact σ g₂ := by
  exact mul_right_cancel (h₁.symm.trans h₂)

private theorem h57_cube_eq_one_of_sixth_eq_one {c : F} (h6 : c ^ 6 = 1) : c ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : (c ^ 3 - 1) * (c ^ 3 - 1) = 0 := by
    linear_combination h6 + (1 - c ^ 3) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)

private theorem h57_det {σ : F ≃+* F} (y : SUid σ 6) :
    ((y : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 :=
  (CFSG.LieType.Universal.Unitary.mem_SUid.mp y.2).1

private theorem h57_scalar_iff (y : GL (Fin 6) F)
    (hdet : (y : Matrix (Fin 6) (Fin 6) F).det = 1) :
    y ∈ CFSG.Open.StatedScalars (Fin 6) F ↔
      ∃ l : F, l ^ 3 = 1 ∧ (y : Matrix (Fin 6) (Fin 6) F) = l • 1 := by
  constructor
  · intro hy
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hy
    have hcoe : (y : Matrix (Fin 6) (Fin 6) F) = (u : F) • 1 := by
      rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
    have h6 : (u : F) ^ 6 = 1 := by
      rw [hcoe, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
      exact hdet
    exact ⟨(u : F), h57_cube_eq_one_of_sixth_eq_one h6, hcoe⟩
  · rintro ⟨l, hl3, hy⟩
    have hl0 : l ≠ 0 := by
      rintro rfl
      norm_num at hl3
    refine MonoidHom.mem_range.mpr ⟨Units.mk0 l hl0, ?_⟩
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hy, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]

private theorem h57_wact_one_iff {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ) (y : SUid σ 6) :
    Wact σ y = 1 ↔ (y : GL (Fin 6) F) ∈ CFSG.Open.StatedScalars (Fin 6) F := by
  rw [Wact_eq_one_iff hσ y]
  exact (h57_scalar_iff _ (h57_det y)).symm

theorem toStated_mk_eq_iff [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (g g' : SUid (unitaryInvolution F 2 f) 6) :
    (QuotientGroup.mk (toStated hF g) :
        CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F)) = QuotientGroup.mk (toStated hF g') ↔
      Wact (unitaryInvolution F 2 f) g = Wact (unitaryInvolution F 2 f) g' := by
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  change ((g⁻¹ * g' : SUid (unitaryInvolution F 2 f) 6) : GL (Fin 6) F) ∈
    CFSG.Open.StatedScalars (Fin 6) F ↔ _
  rw [← h57_wact_one_iff hσ, map_mul, map_inv, inv_mul_eq_one]

private theorem h57_mk_eq_one_iff [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (g : SUid (unitaryInvolution F 2 f) 6) :
    (QuotientGroup.mk (toStated hF g) : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F)) = 1 ↔
      Wact (unitaryInvolution F 2 f) g = 1 := by
  have h1 : toStated hF (1 : SUid (unitaryInvolution F 2 f) 6) = 1 := Subtype.ext rfl
  have key := toStated_mk_eq_iff hF g 1
  rw [map_one, h1] at key
  exact key

private theorem h57_twist_wact_one {σ : F ≃+* F} {T : Wform σ ≃ₗ[Fσ σ] Wform σ}
    {y y' : SUid σ 6} (h : T * Wact σ y = Wact σ y' * T) : Wact σ y = 1 ↔ Wact σ y' = 1 := by
  constructor
  · intro hy
    rw [hy, mul_one] at h
    exact mul_right_cancel (h.symm.trans (one_mul T).symm)
  · intro hy'
    rw [hy', one_mul] at h
    exact mul_left_cancel (h.trans (mul_one T).symm)

theorem exists_aut_of_normalizesU [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {T : Wform (unitaryInvolution F 2 f) ≃ₗ[Fσ (unitaryInvolution F 2 f)]
      Wform (unitaryInvolution F 2 f)} (hT : NormalizesU (unitaryInvolution F 2 f) T) :
    ∃ γ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F)),
      ∀ g g' : SUid (unitaryInvolution F 2 f) 6,
        T * Wact (unitaryInvolution F 2 f) g = Wact (unitaryInvolution F 2 f) g' * T →
          γ (QuotientGroup.mk (toStated hF g)) = QuotientGroup.mk (toStated hF g') := by
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hT' : ∀ g : SUid (unitaryInvolution F 2 f) 6, ∃ g' : SUid (unitaryInvolution F 2 f) 6,
      T * Wact (unitaryInvolution F 2 f) g = Wact (unitaryInvolution F 2 f) g' * T := hT
  choose a ha using hT'
  have hmul : ∀ g h : SUid (unitaryInvolution F 2 f) 6,
      (QuotientGroup.mk (toStated hF (a (g * h))) :
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F)) =
        QuotientGroup.mk (toStated hF (a g)) * QuotientGroup.mk (toStated hF (a h)) := by
    intro g h
    have htw : T * Wact (unitaryInvolution F 2 f) (g * h) =
        Wact (unitaryInvolution F 2 f) (a g * a h) * T := by
      rw [map_mul (Wact (unitaryInvolution F 2 f)) g h, ← mul_assoc, ha g, mul_assoc, ha h,
        ← mul_assoc, ← map_mul (Wact (unitaryInvolution F 2 f)) (a g) (a h)]
    have hprod : (QuotientGroup.mk (toStated hF (a g)) * QuotientGroup.mk (toStated hF (a h)) :
        CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F)) =
          QuotientGroup.mk (toStated hF (a g * a h)) := rfl
    rw [hprod, toStated_mk_eq_iff]
    exact wact_eq_of_twist (ha (g * h)) htw
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : SUid (unitaryInvolution F 2 f) 6 →*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F),
      ∀ g, φ₁ g = QuotientGroup.mk (toStated hF (a g)) :=
    ⟨MonoidHom.mk' (fun g => QuotientGroup.mk (toStated hF (a g))) hmul, fun g => rfl⟩
  obtain ⟨ιh, hιh⟩ : ∃ ιh : CFSG.Open.StatedSU 6 (2 ^ f) F →* SUid (unitaryInvolution F 2 f) 6,
      ∀ x, ((ιh x : SUid (unitaryInvolution F 2 f) 6) : GL (Fin 6) F) = (x : GL (Fin 6) F) :=
    ⟨MonoidHom.mk' (fun x : CFSG.Open.StatedSU 6 (2 ^ f) F =>
        (⟨(x : GL (Fin 6) F), (SUid_eq_statedSU hF 6).ge x.2⟩ : SUid (unitaryInvolution F 2 f) 6))
      (fun x y => rfl), fun x => rfl⟩
  have hιτ : ∀ x : CFSG.Open.StatedSU 6 (2 ^ f) F, toStated hF (ιh x) = x :=
    fun x => Subtype.ext (hιh x)
  have hτι : ∀ g : SUid (unitaryInvolution F 2 f) 6, ιh (toStated hF g) = g :=
    fun g => Subtype.ext (hιh (toStated hF g))
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : CFSG.Open.StatedSU 6 (2 ^ f) F →*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F),
      ∀ x, φ₂ x = QuotientGroup.mk (toStated hF (a (ιh x))) :=
    ⟨φ₁.comp ιh, fun x => hφ₁ (ιh x)⟩
  have hker : (CFSG.Open.StatedScalars (Fin 6) F).subgroupOf
      (CFSG.Open.StatedSU 6 (2 ^ f) F) ≤ φ₂.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hφ₂, h57_mk_eq_one_iff hF]
    have hscal : ((ιh x : SUid (unitaryInvolution F 2 f) 6) : GL (Fin 6) F) ∈
        CFSG.Open.StatedScalars (Fin 6) F := by
      rw [hιh x]
      exact Subgroup.mem_subgroupOf.mp hx
    exact (h57_twist_wact_one (ha (ιh x))).mp ((h57_wact_one_iff hσ (ιh x)).mpr hscal)
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F) →*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F),
      ∀ x, α₀ (QuotientGroup.mk x) = φ₂ x :=
    ⟨QuotientGroup.lift _ φ₂ hker, fun x => rfl⟩
  have hinj : Function.Injective α₀ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hα₀, hφ₂, h57_mk_eq_one_iff hF] at hz
    have hWx : Wact (unitaryInvolution F 2 f) (ιh x) = 1 :=
      (h57_twist_wact_one (ha (ιh x))).mpr hz
    have h3 := (h57_mk_eq_one_iff hF (ιh x)).mpr hWx
    rw [hιτ] at h3
    exact h3
  have hfin : Finite (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) F)) :=
    Finite.of_surjective _ QuotientGroup.mk_surjective
  have hbij : Function.Bijective α₀ := Finite.injective_iff_bijective.mp hinj
  refine ⟨MulEquiv.ofBijective α₀ hbij, fun g g' hgg' => ?_⟩
  show α₀ (QuotientGroup.mk (toStated hF g)) = QuotientGroup.mk (toStated hF g')
  rw [hα₀, hφ₂, hτι, toStated_mk_eq_iff]
  exact wact_eq_of_twist (ha g) hgg'

theorem exists_twist_form [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {T : Wform (unitaryInvolution F 2 f) ≃ₗ[Fσ (unitaryInvolution F 2 f)]
      Wform (unitaryInvolution F 2 f)} (hT : NormalizesU (unitaryInvolution F 2 f) T) :
    ∃ (B : GL (Fin 6) F) (τ : F ≃+* F),
      conjTr (unitaryInvolution F 2 f) (B : Matrix (Fin 6) (Fin 6) F) *
        (B : Matrix (Fin 6) (Fin 6) F) = 1 ∧
      ∀ g : SUid (unitaryInvolution F 2 f) 6, ∃ gB : SUid (unitaryInvolution F 2 f) 6,
        (gB : GL (Fin 6) F) = B * glAut τ (g : GL (Fin 6) F) * B⁻¹ ∧
          T * Wact (unitaryInvolution F 2 f) g = Wact (unitaryInvolution F 2 f) gB * T := by
  obtain ⟨γ, hγ⟩ := exists_aut_of_normalizesU hF hT
  obtain ⟨τ, B, hB, hBg⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.l212in_aut_su (n := 6) (r := 2) (f := f) (by norm_num) hF γ
  refine ⟨B, τ, hB, fun g => ?_⟩
  obtain ⟨g', hg'⟩ := hT g
  obtain ⟨hmem, hγB⟩ := hBg (toStated hF g)
  have key : Wact (unitaryInvolution F 2 f) g' = Wact (unitaryInvolution F 2 f)
      ⟨B * glAut τ (g : GL (Fin 6) F) * B⁻¹, (SUid_eq_statedSU hF 6).ge hmem⟩ :=
    (toStated_mk_eq_iff hF g' ⟨B * glAut τ (g : GL (Fin 6) F) * B⁻¹,
      (SUid_eq_statedSU hF 6).ge hmem⟩).mp ((hγ g g' hg').symm.trans hγB)
  refine ⟨⟨B * glAut τ (g : GL (Fin 6) F) * B⁻¹, (SUid_eq_statedSU hF 6).ge hmem⟩, rfl, ?_⟩
  rw [hg', key]

private theorem h58_rho_conj_transv (P : GL (Fin 6) F) {a b : Fin 6} (hab : a ≠ b) (d : F)
    (ξ : Cube F) :
    rho F (P * transvGL F a b hab d * P⁻¹) ξ =
      ξ + d • rho F P (Nop F a b hab (rho F P⁻¹ ξ)) := by
  rw [rho_mul_apply, rho_mul_apply, rho_transvGL_eq_add_Nop, map_add, map_smul]
  congr 1
  rw [← rho_mul_apply, mul_inv_cancel, rho_one, Module.End.one_apply]

private theorem h58_glAut_transv (τ : F ≃+* F) {a b : Fin 6} (hab : a ≠ b) (d : F) :
    glAut τ (transvGL F a b hab d) = transvGL F a b hab (τ d) := by
  apply Units.ext
  rw [coe_glAut, transvGL_val, transvGL_val]
  ext i j
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, apply_ite τ]

private theorem h58_conj_scalar (P X : GL (Fin 6) F) (l : F)
    (h : ((P * X * P⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = l • 1) :
    (X : Matrix (Fin 6) (Fin 6) F) = l • 1 := by
  have h1 : P⁻¹ * (P * X * P⁻¹) * P = X := by group
  rw [← h1, Units.val_mul, Units.val_mul, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Units.inv_mul]

theorem tau_fixes_Fq (hσ : IsUnitaryInvolution σ) {T : Wform σ ≃ₗ[Fσ σ] Wform σ}
    {B : GL (Fin 6) F} {τ : F ≃+* F}
    (hB : conjTr σ (B : Matrix (Fin 6) (Fin 6) F) * (B : Matrix (Fin 6) (Fin 6) F) = 1)
    (htw : ∀ g : SUid σ 6, ∃ gB : SUid σ 6, (gB : GL (Fin 6) F) = B * glAut τ (g : GL (Fin 6) F) * B⁻¹ ∧
      T * Wact σ g = Wact σ gB * T) :
    ∀ c : F, σ c = c → τ c = c := by
  clear hB
  intro c hc
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  obtain ⟨Sf, hSf⟩ : ∃ Sf : GL (Fin 6) F, Sf = frameGL σ ω hω := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 6) F, P = B * glAut τ Sf := ⟨_, rfl⟩
  have hab : (0 : Fin 6) ≠ partner 0 := (partner_ne 0).symm
  have hmemS : ∀ d : F, σ d = d → Sf * transvGL F 0 (partner 0) hab d * Sf⁻¹ ∈ SUid σ 6 := by
    intro d hd
    rw [hSf]
    exact frameConj_long_mem hσ hω 0 hd
  have htwist : ∀ (d : F) (hd : σ d = d), ∃ gB : SUid σ 6,
      (gB : GL (Fin 6) F) = P * transvGL F 0 (partner 0) hab (τ d) * P⁻¹ ∧
      T * Wact σ ⟨_, hmemS d hd⟩ = Wact σ gB * T := by
    intro d hd
    obtain ⟨gB, hgB, hTg⟩ := htw ⟨_, hmemS d hd⟩
    refine ⟨gB, ?_, hTg⟩
    rw [hgB, hP]
    show B * glAut τ (Sf * transvGL F 0 (partner 0) hab d * Sf⁻¹) * B⁻¹ = _
    rw [map_mul, map_mul, map_inv, h58_glAut_transv]
    simp only [_root_.mul_inv_rev, _root_.mul_assoc]
  have hW : ∀ (d : F) (hd : σ d = d) (w : Wform σ),
      ((Wact σ ⟨_, hmemS d hd⟩ w : Wform σ) : Cube F) =
        (w : Cube F) + d • rho F Sf (Nop F 0 (partner 0) hab (rho F Sf⁻¹ (w : Cube F))) := by
    intro d hd w
    rw [Wact_apply]
    exact h58_rho_conj_transv Sf hab d _
  have hÑmem : ∀ w : Wform σ,
      rho F Sf (Nop F 0 (partner 0) hab (rho F Sf⁻¹ (w : Cube F))) ∈ Wform σ := by
    intro w
    have h1 := hW 1 (map_one σ) w
    have h2 : ((Wact σ ⟨_, hmemS 1 (map_one σ)⟩ w - w : Wform σ) : Cube F) =
        rho F Sf (Nop F 0 (partner 0) hab (rho F Sf⁻¹ (w : Cube F))) := by
      rw [Submodule.coe_sub, h1, one_smul]
      abel
    rw [← h2]
    exact (Wact σ ⟨_, hmemS 1 (map_one σ)⟩ w - w).2
  have hWy : ∀ (d : F) (hd : σ d = d) (w : Wform σ),
      Wact σ ⟨_, hmemS d hd⟩ w =
        w + (⟨d, (mem_Fσ_iff).mpr hd⟩ : Fσ σ) • (⟨_, hÑmem w⟩ : Wform σ) := by
    intro d hd w
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hW d hd w]
    rfl
  have hT1 : ∀ (d : F) (hd : σ d = d) (w : Wform σ),
      ((T (Wact σ ⟨_, hmemS d hd⟩ w) : Wform σ) : Cube F) =
        ((T w : Wform σ) : Cube F) + d • ((T (⟨_, hÑmem w⟩ : Wform σ) : Wform σ) : Cube F) := by
    intro d hd w
    rw [hWy d hd w, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul]
    rfl
  have hT2 : ∀ (d : F) (hd : σ d = d) (w : Wform σ),
      ((T (Wact σ ⟨_, hmemS d hd⟩ w) : Wform σ) : Cube F) =
        ((T w : Wform σ) : Cube F) +
          τ d • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w : Wform σ) : Cube F))) := by
    intro d hd w
    obtain ⟨gB, hgB, hTg⟩ := htwist d hd
    have h1 := congrArg (fun φ : Wform σ ≃ₗ[Fσ σ] Wform σ => φ w) hTg
    simp only [LinearEquiv.mul_apply] at h1
    rw [h1, Wact_apply, hgB, h58_rho_conj_transv P hab (τ d)]
  have hT3 : ∀ (d : F) (hd : σ d = d) (w : Wform σ),
      d • ((T (⟨_, hÑmem w⟩ : Wform σ) : Wform σ) : Cube F) =
        τ d • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w : Wform σ) : Cube F))) := by
    intro d hd w
    exact add_left_cancel ((hT1 d hd w).symm.trans (hT2 d hd w))
  have hT4 : ∀ w : Wform σ,
      ((T (⟨_, hÑmem w⟩ : Wform σ) : Wform σ) : Cube F) =
        rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w : Wform σ) : Cube F))) := by
    intro w
    have h := hT3 1 (map_one σ) w
    rwa [one_smul, map_one, one_smul] at h
  have hT5 : ∀ (d : F) (hd : σ d = d) (w : Wform σ),
      d • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w : Wform σ) : Cube F))) =
        τ d • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w : Wform σ) : Cube F))) := by
    intro d hd w
    have h := hT3 d hd w
    rwa [hT4 w] at h
  have hex : ∃ w0 : Wform σ,
      rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w0 : Wform σ) : Cube F))) ≠ 0 := by
    by_contra hne
    simp only [not_exists, ne_eq, not_not] at hne
    have hN0 : ∀ x : Wform σ, rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ (x : Cube F))) = 0 := by
      intro x
      have h := hne (T.symm x)
      rwa [LinearEquiv.apply_symm_apply] at h
    obtain ⟨gB1, hgB1, _⟩ := htwist 1 (map_one σ)
    have hid : Wact σ gB1 = 1 := by
      apply LinearEquiv.ext
      intro x
      apply Subtype.ext
      rw [Wact_apply, hgB1, map_one τ, h58_rho_conj_transv P hab 1, one_smul, hN0 x, add_zero]
      rfl
    obtain ⟨l, -, hl⟩ := (Wact_eq_one_iff hσ gB1).mp hid
    rw [hgB1, map_one τ] at hl
    have hl' := h58_conj_scalar P (transvGL F 0 (partner 0) hab 1) l hl
    have h01 := congrFun (congrFun hl' 0) (partner 0)
    simp [transvGL_val, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, hab] at h01
  obtain ⟨w0, hw0⟩ := hex
  have h' : (c - τ c) • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w0 : Wform σ) : Cube F))) =
      0 := by
    have hh := hT5 c hc w0
    have e1 : (c - τ c) • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w0 : Wform σ) : Cube F))) +
        τ c • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w0 : Wform σ) : Cube F))) =
        c • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w0 : Wform σ) : Cube F))) := by
      rw [← add_smul, sub_add_cancel]
    have e2 : (c - τ c) • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w0 : Wform σ) : Cube F))) +
        τ c • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w0 : Wform σ) : Cube F))) =
        0 + τ c • rho F P (Nop F 0 (partner 0) hab (rho F P⁻¹ ((T w0 : Wform σ) : Cube F))) := by
      rw [e1, hh, zero_add]
    exact add_right_cancel e2
  rcases smul_eq_zero.mp h' with h'' | h''
  · exact (sub_eq_zero.mp h'').symm
  · exact absurd h'' hw0

private theorem h59_conj {B g gB : GL (Fin 6) F} {τ : F ≃+* F}
    (hgB : gB = B * glAut τ g * B⁻¹) (ξ : Cube F) :
    rho F B (sigmaC τ (rho F g ξ)) = rho F gB (rho F B (sigmaC τ ξ)) := by
  have key : gB * B = B * glAut τ g := by rw [hgB, inv_mul_cancel_right]
  have e1 : rho F B (rho F (glAut τ g) (sigmaC τ ξ)) = rho F (B * glAut τ g) (sigmaC τ ξ) := by
    rw [rho_mul, Module.End.mul_apply]
  have e2 : rho F gB (rho F B (sigmaC τ ξ)) = rho F (B * glAut τ g) (sigmaC τ ξ) := by
    rw [← key, rho_mul, Module.End.mul_apply]
  rw [sigmaC_rho, e1, e2]

private theorem h59_mem {B : GL (Fin 6) F} {τ : F ≃+* F} {μ₀ : F}
    (hB : conjTr σ (B : Matrix (Fin 6) (Fin 6) F) * (B : Matrix (Fin 6) (Fin 6) F) = 1)
    (hτ : ∀ c, σ (τ c) = τ (σ c)) (hμ : σ μ₀ = (B : Matrix (Fin 6) (Fin 6) F).det * μ₀)
    (w : Wform σ) :
    theta σ (μ₀ • rho F B (sigmaC τ (w : Cube F))) = μ₀ • rho F B (sigmaC τ (w : Cube F)) := by
  have hw : theta σ (w : Cube F) = (w : Cube F) := mem_Wsub_iff.mp (mem_Wform_iff.mp w.2)
  rw [theta_smul, hμ, mul_comm (B : Matrix (Fin 6) (Fin 6) F).det μ₀, mul_smul,
    theta_rho_unitary hB, theta_sigmaC hτ, hw]

private theorem h59_rho_eq_zero {B : GL (Fin 6) F} {y : Cube F} (h : rho F B y = 0) : y = 0 := by
  have h1 : rho F (B⁻¹) (rho F B y) = y := by
    rw [← Module.End.mul_apply, ← rho_mul, inv_mul_cancel, rho_one, Module.End.one_apply]
  rw [h, map_zero] at h1
  exact h1.symm

private theorem h59_nz {B : GL (Fin 6) F} {τ : F ≃+* F} {μ₀ : F} (hμ₀ : μ₀ ≠ 0) {x : Cube F}
    (hx : x ≠ 0) : μ₀ • rho F B (sigmaC τ x) ≠ 0 := by
  intro h
  rcases smul_eq_zero.mp h with h1 | h1
  · exact hμ₀ h1
  · apply hx
    have h2 : sigmaC τ x = 0 := h59_rho_eq_zero h1
    have h3 : sigmaC τ.symm (sigmaC τ x) = x :=
      sigmaC_sigmaC (τ := τ.symm) (τ' := τ) (fun c => τ.symm_apply_apply c) x
    rw [h2, map_zero] at h3
    exact h3.symm

theorem eq_smul_phi_of_twist [Finite F] (hσ : IsUnitaryInvolution σ) {T : Wform σ ≃ₗ[Fσ σ] Wform σ}
    {B : GL (Fin 6) F} {τ : F ≃+* F} (hτ : τ = RingEquiv.refl F ∨ τ = σ)
    (hB : conjTr σ (B : Matrix (Fin 6) (Fin 6) F) * (B : Matrix (Fin 6) (Fin 6) F) = 1)
    (htw : ∀ g : SUid σ 6, ∃ gB : SUid σ 6, (gB : GL (Fin 6) F) = B * glAut τ (g : GL (Fin 6) F) * B⁻¹ ∧
      T * Wact σ g = Wact σ gB * T) :
    ∃ μ : F, ∀ w : Wform σ, ((T w : Wform σ) : Cube F) = μ • rho F B (sigmaC τ (w : Cube F)) := by
  have hcomm : ∀ c : F, σ (τ c) = τ (σ c) := by
    intro c
    rcases hτ with h | h <;> simp [h]
  have hfix : ∀ c : F, σ c = c → τ c = c := by
    intro c hc
    rcases hτ with h | h <;> simp [h, hc]
  have hdet : σ (B : Matrix (Fin 6) (Fin 6) F).det * (B : Matrix (Fin 6) (Fin 6) F).det = 1 :=
    det_norm_one hB
  obtain ⟨μ₀, hμ₀, hσμ₀⟩ := exists_mu hσ.invol hdet
  have hmem : ∀ w : Wform σ, μ₀ • rho F B (sigmaC τ (w : Cube F)) ∈ Wform σ :=
    fun w => mem_Wform_iff.mpr (mem_Wsub_iff.mpr (h59_mem hB hcomm hσμ₀ w))
  obtain ⟨Ph, hPh⟩ : ∃ Ph : Wform σ →ₗ[Fσ σ] Wform σ,
      ∀ w : Wform σ, ((Ph w : Wform σ) : Cube F) = μ₀ • rho F B (sigmaC τ (w : Cube F)) := by
    let f : Wform σ → Wform σ := fun w => ⟨μ₀ • rho F B (sigmaC τ (w : Cube F)), hmem w⟩
    have hf : ∀ w : Wform σ, ((f w : Wform σ) : Cube F) = μ₀ • rho F B (sigmaC τ (w : Cube F)) :=
      fun w => rfl
    have hadd : ∀ w₁ w₂ : Wform σ, f (w₁ + w₂) = f w₁ + f w₂ := by
      intro w₁ w₂
      apply Subtype.ext
      change μ₀ • rho F B (sigmaC τ ((w₁ : Cube F) + (w₂ : Cube F))) =
        μ₀ • rho F B (sigmaC τ (w₁ : Cube F)) + μ₀ • rho F B (sigmaC τ (w₂ : Cube F))
      rw [map_add, map_add, smul_add]
    have hsmul : ∀ (r : Fσ σ) (w : Wform σ), f (r • w) = (RingHom.id (Fσ σ)) r • f w := by
      intro r w
      apply Subtype.ext
      change μ₀ • rho F B (sigmaC τ ((r : F) • (w : Cube F))) =
        (r : F) • (μ₀ • rho F B (sigmaC τ (w : Cube F)))
      rw [sigmaC_smul, hfix (r : F) (mem_Fσ_iff.mp r.2), map_smul, smul_comm]
    exact ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, hf⟩
  have hconjPh : ∀ (g gB : SUid σ 6) (v : Wform σ),
      (gB : GL (Fin 6) F) = B * glAut τ (g : GL (Fin 6) F) * B⁻¹ →
        Ph (Wact σ g v) = Wact σ gB (Ph v) := by
    intro g gB v hgB
    apply Subtype.ext
    rw [hPh, Wact_apply, Wact_apply, h59_conj hgB, hPh, map_smul]
  obtain ⟨Sg, hSg⟩ : ∃ Sg : Wform σ →ₗ[Fσ σ] Wform σ, ∀ v, Sg v = T.symm (Ph v) :=
    ⟨T.symm.toLinearMap.comp Ph, fun v => rfl⟩
  have hScomm : ∀ (g : SUid σ 6) (v : Wform σ), Sg (Wact σ g v) = Wact σ g (Sg v) := by
    intro g v
    obtain ⟨gB, hgB, hTg⟩ := htw g
    have h2 : ∀ u : Wform σ, T (Wact σ g u) = Wact σ gB (T u) := fun u =>
      LinearEquiv.congr_fun hTg u
    have h4 := h2 (T.symm (Ph v))
    rw [T.apply_symm_apply] at h4
    rw [hSg, hSg, hconjPh g gB v hgB, ← h4, T.symm_apply_apply]
  obtain ⟨c, hc⟩ := schur_W hσ Sg hScomm
  have hPhc : ∀ v : Wform σ, Ph v = c • T v := by
    intro v
    have h1 : T.symm (Ph v) = c • v := by rw [← hSg, hc v]
    calc Ph v = T (T.symm (Ph v)) := (T.apply_symm_apply _).symm
      _ = T (c • v) := by rw [h1]
      _ = c • T v := map_smul T c v
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : Ph (pt0W σ) = 0 := by rw [hPhc, h0, zero_smul]
    have h2 : μ₀ • rho F B (sigmaC τ ((pt0W σ : Wform σ) : Cube F)) = 0 := by
      rw [← hPh, h1, Submodule.coe_zero]
    exact h59_nz (B := B) (τ := τ) hμ₀ (pt0_ne_zero (K := F)) h2
  refine ⟨(c : F)⁻¹ * μ₀, fun w => ?_⟩
  have hTw : T w = (c⁻¹ : Fσ σ) • Ph w := by
    rw [hPhc w, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hTw]
  change ((c⁻¹ : Fσ σ) : F) • ((Ph w : Wform σ) : Cube F) = _
  rw [hPh, smul_smul]
  rfl

theorem u6_normalizer_dichotomy [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (hσF : σ = unitaryInvolution F 2 f) {T : Wform σ ≃ₗ[Fσ σ] Wform σ} (hT : NormalizesU σ T) :
    ∃ (P : GL (Fin 6) F) (μ : F) (τ : F ≃+* F), (τ = RingEquiv.refl F ∨ τ = σ) ∧
      conjTr σ (P : Matrix (Fin 6) (Fin 6) F) * (P : Matrix (Fin 6) (Fin 6) F) = 1 ∧
      ∀ w : Wform σ, ((T w : Wform σ) : Cube F) = μ • rho F P (sigmaC τ (w : Cube F)) := by
  subst hσF
  obtain ⟨B, τ, hB, htw⟩ := exists_twist_form hF hT
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hτ := tau_cases hσ (tau_fixes_Fq hσ hB htw)
  obtain ⟨μ, hμ⟩ := eq_smul_phi_of_twist hσ hτ hB htw
  exact ⟨B, μ, τ, hτ, hB, hμ⟩

private theorem h60_pow_unitary {A : Matrix (Fin 6) (Fin 6) F} (hA : conjTr σ A * A = 1) (n : ℕ) :
    conjTr σ (A ^ n) * A ^ n = 1 := by
  induction n with
  | zero => simp [conjTr_one]
  | succ n ih =>
    have e : conjTr σ (A ^ (n + 1)) * A ^ (n + 1) =
        conjTr σ A * ((conjTr σ (A ^ n) * A ^ n) * A) := by
      rw [pow_succ, conjTr_mul]
      simp only [Matrix.mul_assoc]
    rw [e, ih, Matrix.one_mul, hA]

theorem mem_Gam_of_innerTypeU_pow [Finite F] (hσ : IsUnitaryInvolution σ)
    {T : Wform σ ≃ₗ[Fσ σ] Wform σ} {P : GL (Fin 6) F} {μ : F}
    (hP : conjTr σ (P : Matrix (Fin 6) (Fin 6) F) * (P : Matrix (Fin 6) (Fin 6) F) = 1)
    (hT : ∀ w : Wform σ, ((T w : Wform σ) : Cube F) = μ • rho F P (w : Cube F)) {k : ℕ}
    (hk : T ^ (2 ^ k) = 1) : ∃ g : SUid σ 6, T = Wact σ g := by
  haveI : Fintype F := Fintype.ofFinite F
  have hpow : ∀ (n : ℕ) (w : Wform σ),
      (((T ^ n) w : Wform σ) : Cube F) = μ ^ n • rho F (P ^ n) (w : Cube F) := by
    intro n
    induction n with
    | zero => intro w; simp [rho_one]
    | succ n ih =>
      intro w
      rw [pow_succ T n, pow_succ μ n, pow_succ P n, LinearEquiv.mul_eq_trans,
        LinearEquiv.trans_apply, ih, hT w, map_smul, rho_mul, Module.End.mul_apply, smul_smul]
  have hw0 : pt0W σ ≠ 0 := by
    intro h
    exact pt0_ne_zero (K := F) (congrArg (fun x : Wform σ => (x : Cube F)) h)
  have hμ : μ ≠ 0 := by
    intro h0
    apply hw0
    apply T.map_eq_zero_iff.mp
    apply Subtype.ext
    simp [hT (pt0W σ), h0]
  obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
  have hodd : Odd (Fintype.card F - 1) := by
    rw [hcard]
    obtain ⟨t, ht⟩ : ∃ t, (n : ℕ) = t + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
    rw [ht, pow_succ]
    have h1 : 0 < 2 ^ t := pow_pos (by norm_num) t
    exact ⟨2 ^ t - 1, by omega⟩
  have hcop : Nat.Coprime (Fintype.card F - 1) (2 ^ (k + 1)) :=
    Nat.Coprime.pow_right (k + 1) (Nat.coprime_two_right.mpr hodd)
  have hμN : μ ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one μ hμ
  have hdet0 : (P : Matrix (Fin 6) (Fin 6) F).det ≠ 0 :=
    right_ne_zero_of_mul_eq_one (det_norm_one hP)
  have hdetN : (P : Matrix (Fin 6) (Fin 6) F).det ^ (Fintype.card F - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ hdet0
  have hPN : conjTr σ ((P ^ (Fintype.card F - 1) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((P ^ (Fintype.card F - 1) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
    simp only [Units.val_pow_eq_pow_val]
    exact h60_pow_unitary hP _
  have hdetPN : ((P ^ (Fintype.card F - 1) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
    simp only [Units.val_pow_eq_pow_val]
    rw [Matrix.det_pow, hdetN]
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : SUid σ 6, (g₀ : GL (Fin 6) F) = P ^ (Fintype.card F - 1) :=
    ⟨⟨P ^ (Fintype.card F - 1), mem_SUid.mpr ⟨hdetPN, hPN⟩⟩, rfl⟩
  have hTN : T ^ (Fintype.card F - 1) = Wact σ g₀ := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [hpow, hμN, one_smul, Wact_apply, hg₀]
  have hT2 : T ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ (2 : ℕ) k, pow_mul, hk, one_pow]
  have hφ : 0 < Nat.totient (2 ^ (k + 1)) := Nat.totient_pos.mpr (pow_pos (by norm_num) _)
  have h1φ : 1 ≤ Nat.totient (2 ^ (k + 1)) := hφ
  have hmod : (Fintype.card F - 1) ^ Nat.totient (2 ^ (k + 1)) % 2 ^ (k + 1) = 1 % 2 ^ (k + 1) :=
    Nat.ModEq.pow_totient hcop
  have h2 : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
  rw [Nat.mod_eq_of_lt h2] at hmod
  have hNm : (Fintype.card F - 1) * (Fintype.card F - 1) ^ (Nat.totient (2 ^ (k + 1)) - 1) =
      (Fintype.card F - 1) ^ Nat.totient (2 ^ (k + 1)) := by
    rw [← pow_succ', Nat.sub_add_cancel h1φ]
  have hTM : T ^ ((Fintype.card F - 1) * (Fintype.card F - 1) ^ (Nat.totient (2 ^ (k + 1)) - 1))
      = T := by
    rw [hNm]
    generalize (Fintype.card F - 1) ^ Nat.totient (2 ^ (k + 1)) = M at hmod ⊢
    have hdec := Nat.div_add_mod M (2 ^ (k + 1))
    rw [hmod] at hdec
    rw [← hdec, pow_add, pow_mul, hT2, one_pow, one_mul, pow_one]
  refine ⟨g₀ ^ ((Fintype.card F - 1) ^ (Nat.totient (2 ^ (k + 1)) - 1)), ?_⟩
  rw [map_pow, ← hTN, ← pow_mul, hTM]

private theorem h60_unitary_mul {A B : Matrix (Fin 6) (Fin 6) F} (hA : conjTr σ A * A = 1)
    (hB : conjTr σ B * B = 1) : conjTr σ (A * B) * (A * B) = 1 := by
  rw [conjTr_mul]
  calc conjTr σ B * conjTr σ A * (A * B)
      = conjTr σ B * (conjTr σ A * A) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

theorem innerType_mul_of_fieldType (hσ : IsUnitaryInvolution σ)
    {T₁ T₂ : Wform σ ≃ₗ[Fσ σ] Wform σ} {P₁ P₂ : GL (Fin 6) F} {μ₁ μ₂ : F}
    (hP₁ : conjTr σ (P₁ : Matrix (Fin 6) (Fin 6) F) * (P₁ : Matrix (Fin 6) (Fin 6) F) = 1)
    (hP₂ : conjTr σ (P₂ : Matrix (Fin 6) (Fin 6) F) * (P₂ : Matrix (Fin 6) (Fin 6) F) = 1)
    (h₁ : ∀ w : Wform σ, ((T₁ w : Wform σ) : Cube F) = μ₁ • rho F P₁ (sigmaC σ (w : Cube F)))
    (h₂ : ∀ w : Wform σ, ((T₂ w : Wform σ) : Cube F) = μ₂ • rho F P₂ (sigmaC σ (w : Cube F))) :
    conjTr σ ((P₁ * glAut σ P₂ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
        ((P₁ * glAut σ P₂ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 ∧
      ∀ w : Wform σ, (((T₁ * T₂) w : Wform σ) : Cube F) =
        (μ₁ * σ μ₂) • rho F (P₁ * glAut σ P₂) (w : Cube F) := by
  have hQ : conjTr σ ((glAut σ P₂ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((glAut σ P₂ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 :=
    conjTr_glAut_unitary (τ := σ) (fun c => rfl) hP₂
  refine ⟨?_, fun w => ?_⟩
  · rw [Units.val_mul]
    exact h60_unitary_mul hP₁ hQ
  · rw [LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply, h₁, h₂, sigmaC_smul, sigmaC_rho,
      sigmaC_sigmaC hσ.invol, map_smul, rho_mul, Module.End.mul_apply, smul_smul]

end CFSG.RankThree.GF2n.Smith81.U6Cube
