module

public import CFSG.Timmesfeld.Transvection.ModelSUBlock
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
import CFSG.LocalAnalysis.StandardType.GGRootDetectSU
import CFSG.Timmesfeld.Transvection.ModelRankSU
import CFSG.Timmesfeld.Transvection.ModelSUGeometry
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate43

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem exists_smul_of_commute_uTrans {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    {v : Fin n → F} (hv : v ≠ 0) {c : F} (hc : c ≠ 0)
    (h : M * uTrans σ v c = uTrans σ v c * M) : ∃ μ : F, M *ᵥ v = μ • v := by
  obtain ⟨y, hy⟩ := exists_uForm_eq_one (σ := σ) hv
  refine ⟨uForm σ v (M *ᵥ y), ?_⟩
  have h' := congrArg (fun N : Matrix (Fin n) (Fin n) F => N *ᵥ y) h
  rw [← mulVec_mulVec, ← mulVec_mulVec, uTrans_mulVec, uTrans_mulVec, hy, mul_one,
    mulVec_add, mulVec_smul] at h'
  have hcancel := add_left_cancel h'
  rw [mul_smul] at hcancel
  exact smul_right_injective _ hc hcancel

private theorem exists_eigenvalue_of_commute [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {M : Matrix (Fin 4) (Fin 4) F} (hM : ∀ g : SU σ 4, M * suMat σ 4 g = suMat σ 4 g * M)
    {v : Fin 4 → F} (hv : v ≠ 0) (hvv : uForm σ v v = 0) :
    ∃ μ : F, M *ᵥ v = μ • v := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans (σ := σ) hσ hvv h1
  exact exists_smul_of_commute_uTrans hv one_ne_zero (by simpa [ht] using hM t)

private theorem eq_diagonal_of_mulVec_single {M : Matrix (Fin 4) (Fin 4) F} {d : Fin 4 → F}
    (hd : ∀ i : Fin 4, M *ᵥ Pi.single i 1 = d i • Pi.single i 1) : M = diagonal d := by
  ext a b
  have h := congrFun (hd b) a
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp [Pi.smul_apply]
  · simp [Pi.smul_apply, Pi.single_apply, hab]

private theorem diagonal_eq_smul_one_of_eq {d : Fin 4 → F} {c : F} (hd : ∀ i, d i = c) :
    diagonal d = c • 1 := by
  rw [funext hd, Matrix.smul_one_eq_diagonal]

theorem exists_smul_one_of_commute_SU_four [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {M : Matrix (Fin 4) (Fin 4) F} (hM : ∀ g : SU σ 4, M * suMat σ 4 g = suMat σ 4 g * M) :
    ∃ c : F, M = c • 1 := by
  obtain ⟨μ0, hμ0⟩ := exists_eigenvalue_of_commute hσ hM (single_one_ne_zero 0)
    (uForm_single_self (by decide))
  obtain ⟨μ1, hμ1⟩ := exists_eigenvalue_of_commute hσ hM (single_one_ne_zero 1)
    (uForm_single_self (by decide))
  obtain ⟨μ2, hμ2⟩ := exists_eigenvalue_of_commute hσ hM (single_one_ne_zero 2)
    (uForm_single_self (by decide))
  obtain ⟨μ3, hμ3⟩ := exists_eigenvalue_of_commute hσ hM (single_one_ne_zero 3)
    (uForm_single_self (by decide))
  have hne01 : (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hne02 : (Pi.single 0 1 + Pi.single 2 1 : Fin 4 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hne13 : (Pi.single 1 1 + Pi.single 3 1 : Fin 4 → F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  have hiso01 : uForm σ (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → F)
      (Pi.single 0 1 + Pi.single 1 1) = 0 := by
    simp [uForm_eq, Fin.sum_univ_four]
  have hiso02 : uForm σ (Pi.single 0 1 + Pi.single 2 1 : Fin 4 → F)
      (Pi.single 0 1 + Pi.single 2 1) = 0 := by
    simp [uForm_eq, Fin.sum_univ_four]
  have hiso13 : uForm σ (Pi.single 1 1 + Pi.single 3 1 : Fin 4 → F)
      (Pi.single 1 1 + Pi.single 3 1) = 0 := by
    simp [uForm_eq, Fin.sum_univ_four]
  obtain ⟨μ01, hμ01⟩ := exists_eigenvalue_of_commute hσ hM hne01 hiso01
  obtain ⟨μ02, hμ02⟩ := exists_eigenvalue_of_commute hσ hM hne02 hiso02
  obtain ⟨μ13, hμ13⟩ := exists_eigenvalue_of_commute hσ hM hne13 hiso13
  have h01 : μ0 = μ1 := by
    have h := hμ01
    rw [Matrix.mulVec_add, hμ0, hμ1] at h
    have h0 : μ0 = μ01 := by simpa using congrFun h 0
    have h1 : μ1 = μ01 := by simpa using congrFun h 1
    exact h0.trans h1.symm
  have h02 : μ0 = μ2 := by
    have h := hμ02
    rw [Matrix.mulVec_add, hμ0, hμ2] at h
    have h0 : μ0 = μ02 := by simpa using congrFun h 0
    have h2 : μ2 = μ02 := by simpa using congrFun h 2
    exact h0.trans h2.symm
  have h13 : μ1 = μ3 := by
    have h := hμ13
    rw [Matrix.mulVec_add, hμ1, hμ3] at h
    have h1 : μ1 = μ13 := by simpa using congrFun h 1
    have h3 : μ3 = μ13 := by simpa using congrFun h 3
    exact h1.trans h3.symm
  let d : Fin 4 → F := fun i => if i = 0 then μ0 else if i = 1 then μ1 else
    if i = 2 then μ2 else μ3
  have hd : ∀ i : Fin 4, d i = μ0 := by
    intro i
    fin_cases i
    · simp [d]
    · simpa [d] using h01.symm
    · simpa [d] using h02.symm
    · simpa [d] using (h01.trans h13).symm
  have hcol : ∀ i : Fin 4, M *ᵥ Pi.single i 1 = d i • Pi.single i 1 := by
    intro i
    fin_cases i <;> simp [d, hμ0, hμ1, hμ2, hμ3]
  refine ⟨μ0, ?_⟩
  rw [eq_diagonal_of_mulVec_single hcol, diagonal_eq_smul_one_of_eq hd]

theorem exists_swap_SU_four (σ : F ≃+* F) :
    ∃ w : SU σ 4, ∀ v : Fin 4 → F, suMat σ 4 w *ᵥ v = ![v 1, v 0, v 3, v 2] := by
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  let S : Matrix (Fin 4) (Fin 4) F := τ.permMatrix F
  have hττ : τ * τ = 1 := by decide
  have hττ' : ∀ i, τ (τ i) = i := by
    intro i
    have := congrArg (fun p : Equiv.Perm (Fin 4) => p i) hττ
    simpa [Equiv.Perm.mul_apply] using this
  have hτ : ∀ i, τ (Fin.rev i) = Fin.rev (τ i) := by decide
  have hdet : S.det = 1 := by
    rw [Matrix.det_permutation]
    have hsign : Equiv.Perm.sign τ = 1 := by decide
    rw [hsign]
    simp
  have hcol : ∀ j : Fin 4, (fun x => S x j) = (Pi.single (τ j) 1 : Fin 4 → F) := by
    intro j
    funext x
    change (τ.permMatrix F) x j = (Pi.single (τ j) 1 : Fin 4 → F) x
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    by_cases h : x = τ j
    · subst h
      simp [hττ']
    · have h' : τ x ≠ j := fun hh => h (by rw [← hττ' x, hh])
      simp [h, h']
  have hiso : conjTr σ S * antidiag 4 * S = antidiag 4 := by
    ext a b
    rw [conjTr_mul_antidiag_mul_apply, hcol a, hcol b, uForm_single_left, ← hτ a]
    simp [Pi.single_apply, antidiag, τ.injective.eq_iff, eq_comm]
  have hτ0 : τ 0 = 1 := by decide
  have hτ1 : τ 1 = 0 := by decide
  have hτ2 : τ 2 = 3 := by decide
  have hτ3 : τ 3 = 2 := by decide
  obtain ⟨w, hw⟩ := exists_suMat_eq_of_isometry (σ := σ) hdet hiso
  refine ⟨w, fun v => ?_⟩
  rw [hw, show S = τ.permMatrix F from rfl, Matrix.permMatrix_mulVec]
  funext i
  fin_cases i <;> simp [hτ0, hτ1, hτ2, hτ3]

theorem eq_smul_of_perp_four [CharP F 2] {u : Fin 4 → F}
    (hu : u ≠ 0) (h0 : u 0 = 0) (h3 : u 3 = 0) (huu : uForm σ u u = 0) :
    (∃ c : F, c ≠ 0 ∧ u = c • Pi.single 2 1) ∨
      ∃ c s : F, c ≠ 0 ∧ σ s = s ∧ u = c • (Pi.single 1 1 + s • Pi.single 2 1) := by
  by_cases h1 : u 1 = 0
  · refine Or.inl ⟨u 2, ?_, ?_⟩
    · intro h
      exact hu (by funext i; fin_cases i <;> simp [h0, h1, h3, h])
    · funext i
      fin_cases i <;> simp [h0, h1, h3]
  · refine Or.inr ⟨u 1, u 2 / u 1, h1, ?_, ?_⟩
    · have hrel : σ (u 1) * u 2 + σ (u 2) * u 1 = 0 := by
        simpa [uForm_eq, Fin.sum_univ_four, h0, h3] using huu
      have hσ1 : σ (u 1) ≠ 0 := (map_ne_zero σ).2 h1
      have hsum : u 2 / u 1 + σ (u 2 / u 1) = 0 := by
        rw [map_div₀]
        field_simp [h1, hσ1]
        linear_combination hrel
      have hneg : σ (u 2 / u 1) = -(u 2 / u 1) := by linear_combination hsum
      rwa [CharTwo.neg_eq] at hneg
    · funext i
      fin_cases i <;> simp [h0, h3, h1, mul_div_cancel₀]

theorem uTrans_mulVec_single_one_four (s : F) :
    uTrans σ (Pi.single (2 : Fin 4) 1) s *ᵥ Pi.single 1 1 =
      Pi.single 1 1 + s • Pi.single 2 1 := by
  rw [uTrans_mulVec, uForm_single_left, show Fin.rev (2 : Fin 4) = 1 from by decide,
    Pi.single_eq_same, mul_one]

private theorem eq_of_uTrans_single_eq {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) {a b : F}
    (h : uTrans σ (Pi.single i 1) a = uTrans σ (Pi.single i 1) b) : a = b := by
  have h' := congrFun (congrFun h i) (Fin.rev i)
  have hii : (vecMulVec (Pi.single i 1) (uRow σ (Pi.single i 1))) i (Fin.rev i) = 1 := by
    simp [vecMulVec_apply, uRow_apply]
  have h1i : (1 : Matrix (Fin n) (Fin n) F) i (Fin.rev i) = 0 := by
    simp [Matrix.one_apply, hi]
  simp only [uTrans, uNil, Matrix.add_apply, Matrix.smul_apply, h1i, hii, smul_eq_mul, mul_one,
    zero_add] at h'
  exact h'

theorem center_SU_four_eq_bot [CharP F 2] (hσ : ∀ c, σ (σ c) = c) :
    Subgroup.center (SU σ 4) = ⊥ := by
  have hcomm : ∀ z : SU σ 4, z ∈ Subgroup.center (SU σ 4) → suMat σ 4 z = (1 : F) • 1 := by
    intro z hz
    obtain ⟨c, hc⟩ := exists_smul_one_of_commute_SU_four hσ (M := suMat σ 4 z) fun g => by
      have h := congrArg (suMat σ 4) (Subgroup.mem_center_iff.1 hz g)
      rw [map_mul, map_mul] at h
      exact h.symm
    have hdet : c ^ 4 = 1 := by
      have h : (suMat σ 4 z).det = 1 := (mem_SU.1 z.2).1
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
      exact h
    have hc2 : c ^ 2 = 1 := by
      refine CharTwo.sq_inj.mp ?_
      rw [← pow_mul, hdet]
      norm_num
    have hc1 : c = 1 := CharTwo.sq_inj.mp (by simpa using hc2)
    rw [hc, hc1, one_smul]
  ext z
  rw [Subgroup.mem_bot]
  constructor
  · intro hz
    refine suMat_injective σ ?_
    rw [hcomm z hz, one_smul, map_one]
  · rintro rfl
    rw [Subgroup.mem_center_iff]
    intro g
    rw [one_mul, mul_one]

private theorem commute_coord_of_diagonal [CharP F 2] {d : Fin 4 → F} {g : SU σ 4}
    (hg : suMat σ 4 g = diagonal d) (hd : ∀ i, d i * σ (d i) = 1) {i : Fin 4}
    {T : Subgroup (SU σ 4)} (hT : IsUTransGroup σ (Pi.single i 1) T) :
    ∀ x ∈ T, Commute g x := by
  intro x hx
  obtain ⟨c, hc, hx'⟩ := (hT.1 x).1 hx
  have hge : suMat σ 4 g *ᵥ Pi.single i 1 = d i • Pi.single i 1 := by
    rw [hg, Matrix.diagonal_mulVec_single]
    funext x
    by_cases h : x = i
    · subst h
      simp
    · simp [Pi.smul_apply, Pi.single_apply, h]
  have h1 : g * x * g⁻¹ = x := by
    refine suMat_injective σ ?_
    rw [suMat_conj_of_eq σ hx' g, hge, uTrans_smul, hd i, one_mul, ← hx']
  show g * x = x * g
  calc g * x = (g * x * g⁻¹) * g := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = x * g := by rw [h1]

private theorem mul_sigma_eq_one_of_commute_coord [CharP F 2] {i : Fin 4}
    (hi : i ≠ Fin.rev i) {T : Subgroup (SU σ 4)}
    (hT : IsUTransGroup σ (Pi.single i 1) T) {C : Subgroup (SU σ 4)} (hle : T ≤ C)
    {g : SU σ 4} (hg : g ∈ Subgroup.centralizer (C : Set (SU σ 4))) {d : Fin 4 → F}
    (hdiag : suMat σ 4 g = diagonal d) : d i * σ (d i) = 1 := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  obtain ⟨t, ht⟩ := hT.2 1 h1
  have htmem : t ∈ T := (hT.1 t).2 ⟨1, h1, ht⟩
  have hcomm : t * g = g * t := hg t (hle htmem)
  have hgt : g * t * g⁻¹ = t := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hcol : suMat σ 4 g *ᵥ Pi.single i 1 = d i • Pi.single i 1 := by
    rw [hdiag, Matrix.diagonal_mulVec_single]
    funext x
    by_cases h : x = i
    · subst h
      simp
    · simp [Pi.smul_apply, Pi.single_apply, h]
  have h := suMat_conj_of_eq σ ht g
  rw [hgt, ht, hcol, uTrans_smul, mul_one] at h
  exact eq_of_uTrans_single_eq hi h.symm

private theorem sigma_mul_rev_of_diagonal [CharP F 2] {d : Fin 4 → F} {g : SU σ 4}
    (hg : suMat σ 4 g = diagonal d) (i : Fin 4) : σ (d i) * d (Fin.rev i) = 1 := by
  have h := congrFun (congrFun (suMat_isometry σ g) i) (Fin.rev i)
  rw [hg, conjTr_mul_antidiag_mul_apply] at h
  have hcol : ∀ j : Fin 4, (fun x => diagonal d x j) = d j • (Pi.single j 1 : Fin 4 → F) := by
    intro j
    funext x
    rw [Matrix.diagonal_apply, Pi.smul_apply, Pi.single_apply]
    by_cases h : x = j
    · subst h
      simp
    · simp [h]
  rw [hcol i, hcol (Fin.rev i), uForm_smul_left, uForm_smul_right, uForm_single_left,
    Pi.single_eq_same, mul_one] at h
  simpa [antidiag] using h

private theorem exists_diagonal_data [CharP F 2] {T₀ T₁ T₂ T₃ : Subgroup (SU σ 4)}
    (hT₀ : IsUTransGroup σ (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single 1 1) T₁)
    (hT₂ : IsUTransGroup σ (Pi.single 2 1) T₂)
    (hT₃ : IsUTransGroup σ (Pi.single 3 1) T₃) {g : SU σ 4}
    (hg : g ∈ Subgroup.centralizer (((T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂)) : Subgroup (SU σ 4)) :
      Set (SU σ 4))) :
    ∃ d : Fin 4 → F, suMat σ 4 g = diagonal d ∧ (∀ i, d i * σ (d i) = 1) ∧
      d 3 = d 0 ∧ d 2 = d 1 ∧ d 1 * d 0 = 1 := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  have hle0 : T₀ ≤ (T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂) : Subgroup (SU σ 4)) :=
    le_sup_left.trans le_sup_left
  have hle3 : T₃ ≤ (T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂) : Subgroup (SU σ 4)) :=
    le_sup_right.trans le_sup_left
  have hle1 : T₁ ≤ (T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂) : Subgroup (SU σ 4)) :=
    le_sup_left.trans le_sup_right
  have hle2 : T₂ ≤ (T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂) : Subgroup (SU σ 4)) :=
    le_sup_right.trans le_sup_right
  have heig : ∀ (i : Fin 4) (T : Subgroup (SU σ 4)),
      IsUTransGroup σ (Pi.single i 1) T → T ≤ (T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂) : Subgroup (SU σ 4)) →
      ∃ μ : F, suMat σ 4 g *ᵥ Pi.single i 1 = μ • Pi.single i 1 := by
    intro i T hT hle
    obtain ⟨t, ht⟩ := hT.2 1 h1
    have htmem : t ∈ T := (hT.1 t).2 ⟨1, h1, ht⟩
    have hcomm : t * g = g * t := hg t (hle htmem)
    have hmat : suMat σ 4 g * uTrans σ (Pi.single i 1) 1 =
        uTrans σ (Pi.single i 1) 1 * suMat σ 4 g := by
      have h := congrArg (suMat σ 4) hcomm
      rw [map_mul, map_mul, ht] at h
      exact h.symm
    exact exists_smul_of_commute_uTrans (single_one_ne_zero i) one_ne_zero hmat
  have hμ : ∀ i : Fin 4, ∃ μ : F, suMat σ 4 g *ᵥ Pi.single i 1 = μ • Pi.single i 1 := by
    intro i
    fin_cases i
    · exact heig 0 T₀ hT₀ hle0
    · exact heig 1 T₁ hT₁ hle1
    · exact heig 2 T₂ hT₂ hle2
    · exact heig 3 T₃ hT₃ hle3
  choose d hd using hμ
  have hdiag : suMat σ 4 g = diagonal d := by
    ext a b
    have h := congrFun (hd b) a
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
    rw [h, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp [Pi.smul_apply]
    · simp [Pi.smul_apply, Pi.single_apply, hab]
  have hnorm : ∀ i, d i * σ (d i) = 1 := by
    intro i
    fin_cases i
    · exact mul_sigma_eq_one_of_commute_coord (by decide) hT₀ hle0 hg hdiag
    · exact mul_sigma_eq_one_of_commute_coord (by decide) hT₁ hle1 hg hdiag
    · exact mul_sigma_eq_one_of_commute_coord (by decide) hT₂ hle2 hg hdiag
    · exact mul_sigma_eq_one_of_commute_coord (by decide) hT₃ hle3 hg hdiag
  have hpair : ∀ i, σ (d i) * d (Fin.rev i) = 1 := fun i =>
    sigma_mul_rev_of_diagonal hdiag i
  have hd3 : d 3 = d 0 := by
    have h3 := hpair 0
    have h0 := hnorm 0
    exact (eq_inv_of_mul_eq_one_right h3).trans (eq_inv_of_mul_eq_one_left h0).symm
  have hd2 : d 2 = d 1 := by
    have h2 := hpair 1
    have h1' := hnorm 1
    exact (eq_inv_of_mul_eq_one_right h2).trans (eq_inv_of_mul_eq_one_left h1').symm
  have hdet : d 0 * d 1 * d 2 * d 3 = 1 := by
    have h : (suMat σ 4 g).det = 1 := (mem_SU.1 g.2).1
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_four] at h
    exact h
  have hsq : (d 0 * d 1) * (d 0 * d 1) = 1 := by
    rw [hd2, hd3] at hdet
    linear_combination hdet
  have h01 : d 0 * d 1 = 1 := by
    have h : (d 0 * d 1) ^ 2 = (1 : F) ^ 2 := by simpa [sq] using hsq
    exact CharTwo.sq_inj.mp h
  have hd10 : d 1 * d 0 = 1 := by rw [mul_comm]; exact h01
  exact ⟨d, hdiag, hnorm, hd3, hd2, hd10⟩

private theorem torusDiag_mul_sigma [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a l : Fˣ} (ha : σ (a : F) * (a : F) = 1) (hl : σ (l : F) * (l : F) = 1) :
    ∀ i : Fin 4, ((torusDiag (m := 2) σ a l) i : F) *
      σ ((torusDiag (m := 2) σ a l) i : F) = 1 := by
  intro i
  fin_cases i
  · change ((torusDiag (m := 2) σ a l) (0 : Fin 4) : F) *
      σ ((torusDiag (m := 2) σ a l) (0 : Fin 4) : F) = 1
    rw [torusDiag_zero, mul_comm]
    exact ha
  · change ((torusDiag (m := 2) σ a l) (mid (0 : Fin 2)) : F) *
      σ ((torusDiag (m := 2) σ a l) (mid (0 : Fin 2)) : F) = 1
    rw [torusDiag_mid, mul_comm]
    exact hl
  · change ((torusDiag (m := 2) σ a l) (mid (1 : Fin 2)) : F) *
      σ ((torusDiag (m := 2) σ a l) (mid (1 : Fin 2)) : F) = 1
    rw [torusDiag_mid, mul_comm]
    exact hl
  · change ((torusDiag (m := 2) σ a l) (Fin.last (2 + 1)) : F) *
      σ ((torusDiag (m := 2) σ a l) (Fin.last (2 + 1)) : F) = 1
    rw [torusDiag_last, map_inv₀, hσ]
    simpa [mul_comm, inv_one] using congrArg Inv.inv ha

private theorem torusElt_commute_coord [CharP F 2] {hσ : ∀ c, σ (σ c) = c}
    {a l : Fˣ} (ha : σ (a : F) * (a : F) = 1) (hl : σ (l : F) * (l : F) = 1)
    (hdet : (a : F) * (l : F) ^ 2 * (σ (a : F))⁻¹ = 1)
    {i : Fin 4} {T : Subgroup (SU σ 4)}
    (hT : IsUTransGroup σ (Pi.single i 1) T) :
    ∀ x ∈ T, Commute (torusElt (m := 2) hσ hl hdet) x := by
  have hdiag : suMat σ 4 (torusElt (m := 2) hσ hl hdet) =
      diagonal (fun s => ((torusDiag (m := 2) σ a l) s : F)) :=
    mat_torusElt
  exact commute_coord_of_diagonal hdiag (torusDiag_mul_sigma hσ ha hl) hT

private theorem torusElt_mem_centralizer_coord [CharP F 2] {hσ : ∀ c, σ (σ c) = c}
    {a l : Fˣ} (ha : σ (a : F) * (a : F) = 1) (hl : σ (l : F) * (l : F) = 1)
    (hdet : (a : F) * (l : F) ^ 2 * (σ (a : F))⁻¹ = 1)
    {T₀ T₁ T₂ T₃ : Subgroup (SU σ 4)}
    (hT₀ : IsUTransGroup σ (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single 1 1) T₁)
    (hT₂ : IsUTransGroup σ (Pi.single 2 1) T₂)
    (hT₃ : IsUTransGroup σ (Pi.single 3 1) T₃) :
    torusElt (m := 2) hσ hl hdet ∈
      Subgroup.centralizer (((T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂)) : Subgroup (SU σ 4)) : Set (SU σ 4)) := by
  have hc : ∀ {i : Fin 4} {T : Subgroup (SU σ 4)}, IsUTransGroup σ (Pi.single i 1) T →
      T ≤ Subgroup.centralizer ({torusElt (m := 2) hσ hl hdet} : Set (SU σ 4)) :=
    fun hT x hx => Subgroup.mem_centralizer_singleton_iff.2
      (torusElt_commute_coord ha hl hdet hT x hx).symm.eq
  have hle := sup_le (sup_le (hc hT₀) (hc hT₃)) (sup_le (hc hT₁) (hc hT₂))
  exact Subgroup.mem_centralizer_iff.2 fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

private theorem sigma_mul_self_of_norm_eq_one [Finite F] [CharP F 2] {f : ℕ}
    {h : UnitaryFieldData 2 f F} {a : Fˣ} (ha : h.norm (a : F) = 1) :
    unitaryInvolution F 2 f (a : F) * (a : F) = 1 := by
  rw [UnitaryFieldData.norm, RootDetectSU.bar_eq h] at ha
  rw [mul_comm]
  exact ha

private theorem sigma_mul_inv_self_of_norm_eq_one [Finite F] [CharP F 2] {f : ℕ}
    {h : UnitaryFieldData 2 f F} {a : Fˣ} (ha : h.norm (a : F) = 1) :
    unitaryInvolution F 2 f ((a⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F) = 1 := by
  rw [UnitaryFieldData.norm, RootDetectSU.bar_eq h] at ha
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  simpa [mul_comm, inv_one] using congrArg Inv.inv ha

private theorem mul_inv_sq_mul_inv_of_norm_eq_one [Finite F] [CharP F 2] {f : ℕ}
    {h : UnitaryFieldData 2 f F} {a : Fˣ} (ha : h.norm (a : F) = 1) :
    (a : F) * ((a⁻¹ : Fˣ) : F) ^ 2 * (unitaryInvolution F 2 f (a : F))⁻¹ = 1 := by
  rw [UnitaryFieldData.norm, RootDetectSU.bar_eq h] at ha
  rw [Units.val_inv_eq_inv_val, pow_two]
  calc (a : F) * ((a : F)⁻¹ * (a : F)⁻¹) * (unitaryInvolution F 2 f (a : F))⁻¹
      = ((a : F) * (a : F)⁻¹) * ((a : F)⁻¹ * (unitaryInvolution F 2 f (a : F))⁻¹) := by
        ring
    _ = 1 := by
        rw [mul_inv_cancel₀ a.ne_zero, one_mul, ← mul_inv]
        simpa [mul_comm, inv_one] using congrArg Inv.inv ha

private theorem exists_torusDiag_eq_of_diagonal [Finite F] [CharP F 2] {f : ℕ}
    {h : UnitaryFieldData 2 f F} {d : Fin 4 → F}
    (hnormd : ∀ i, d i * unitaryInvolution F 2 f (d i) = 1)
    (hd3 : d 3 = d 0) (hd2 : d 2 = d 1) (hd10 : d 1 * d 0 = 1) :
    ∃ a : Fˣ, h.norm (a : F) = 1 ∧
      d = fun s : Fin 4 =>
        ((torusDiag (m := 2) (unitaryInvolution F 2 f) a a⁻¹) s : F) := by
  have hd0 : d 0 ≠ 0 := by
    intro h0
    have h := hnormd 0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  let a : Fˣ := Units.mk0 (d 0) hd0
  have hnorma : (a : F) * unitaryInvolution F 2 f (a : F) = 1 := by
    change d 0 * unitaryInvolution F 2 f (d 0) = 1
    exact hnormd 0
  have hn : h.norm (a : F) = 1 := by
    rw [UnitaryFieldData.norm, RootDetectSU.bar_eq h, hnorma]
  refine ⟨a, hn, ?_⟩
  funext s
  fin_cases s
  · change d 0 = ((torusDiag (m := 2) (unitaryInvolution F 2 f) a a⁻¹) 0 : F)
    rw [torusDiag_zero]
    simp [a]
  · change d 1 = ((torusDiag (m := 2) (unitaryInvolution F 2 f) a a⁻¹)
      (mid (0 : Fin 2)) : F)
    rw [torusDiag_mid, eq_inv_of_mul_eq_one_left hd10]
    simp [a]
  · change d 2 = ((torusDiag (m := 2) (unitaryInvolution F 2 f) a a⁻¹)
      (mid (1 : Fin 2)) : F)
    rw [torusDiag_mid, hd2, eq_inv_of_mul_eq_one_left hd10]
    simp [a]
  · change d 3 = ((torusDiag (m := 2) (unitaryInvolution F 2 f) a a⁻¹)
      (Fin.last (2 + 1)) : F)
    rw [torusDiag_last, hd3]
    change d 0 = (unitaryInvolution F 2 f (d 0))⁻¹
    exact eq_inv_of_mul_eq_one_left (hnormd 0)

theorem natCard_centralizer_coord_SU_four [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    {T₀ T₁ T₂ T₃ : Subgroup (SU (unitaryInvolution F 2 f) 4)}
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 1 1) T₁)
    (hT₂ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 2 1) T₂)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 3 1) T₃) :
    Nat.card ↥(Subgroup.centralizer ((T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂) :
      Subgroup (SU (unitaryInvolution F 2 f) 4)) : Set (SU (unitaryInvolution F 2 f) 4))) =
      2 ^ f + 1 := by
  let σ : F ≃+* F := unitaryInvolution F 2 f
  let h : UnitaryFieldData 2 f F := RootDetectSU.unitaryFieldData_two hF hf
  have hσ : ∀ c, σ (σ c) = c := fun c => unitaryInvolution_involutive hF c
  let Z := (Units.map h.normHom).ker
  have hq : Nat.card ↥Z = 2 ^ f + 1 :=
    (UnitaryFieldData.card_ker_normUnits_and_surjective h).1
  have hnorm_of : ∀ u : ↥Z, h.norm ((u : Fˣ) : F) = 1 := fun u =>
    (UnitaryFieldData.mem_ker_normUnits h).1 u.2
  have ha_of : ∀ u : ↥Z, σ ((u : Fˣ) : F) * ((u : Fˣ) : F) = 1 := fun u =>
    sigma_mul_self_of_norm_eq_one (hnorm_of u)
  have hl_of : ∀ u : ↥Z, σ (((u : Fˣ)⁻¹ : Fˣ) : F) * (((u : Fˣ)⁻¹ : Fˣ) : F) = 1 :=
    fun u => sigma_mul_inv_self_of_norm_eq_one (hnorm_of u)
  have hdet_of : ∀ u : ↥Z,
      ((u : Fˣ) : F) * (((u : Fˣ)⁻¹ : Fˣ) : F) ^ 2 * (σ ((u : Fˣ) : F))⁻¹ = 1 :=
    fun u => mul_inv_sq_mul_inv_of_norm_eq_one (hnorm_of u)
  let torusOf : ↥Z → SU σ 4 := fun u => torusElt (m := 2) hσ (hl_of u) (hdet_of u)
  have hTorusMem : ∀ u : ↥Z, torusOf u ∈
      Subgroup.centralizer (((T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂)) : Subgroup (SU σ 4)) : Set (SU σ 4)) :=
    fun u => torusElt_mem_centralizer_coord (ha_of u) (hl_of u) (hdet_of u) hT₀ hT₁ hT₂ hT₃
  let θ : ↥Z → ↥(Subgroup.centralizer (((T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂)) : Subgroup (SU σ 4)) :
      Set (SU σ 4))) := fun u => ⟨torusOf u, hTorusMem u⟩
  have hmatOf : ∀ u : ↥Z, suMat σ 4 (torusOf u) =
      diagonal (fun s => ((torusDiag (m := 2) σ (u : Fˣ) ((u : Fˣ)⁻¹)) s : F)) :=
    fun u => mat_torusElt
  have hinj : Function.Injective θ := by
    intro u v huv
    apply Subtype.ext
    apply Units.ext
    have hmat : suMat σ 4 (torusOf u) = suMat σ 4 (torusOf v) := by
      have := congrArg (fun w : ↥(Subgroup.centralizer
        (((T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂)) : Subgroup (SU σ 4)) : Set (SU σ 4))) =>
          suMat σ 4 (w : SU σ 4)) huv
      simpa [θ] using this
    rw [hmatOf u, hmatOf v] at hmat
    have h0 := congrFun (congrFun hmat 0) 0
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, torusDiag_zero, torusDiag_zero] at h0
    simpa using h0
  have hsurj : Function.Surjective θ := by
    intro g
    obtain ⟨d, hdiag, hnormd, hd3, hd2, hd10⟩ :=
      exists_diagonal_data hT₀ hT₁ hT₂ hT₃ g.2
    obtain ⟨a, hna, hdeq⟩ := exists_torusDiag_eq_of_diagonal hnormd hd3 hd2 hd10
    let u : ↥Z := ⟨a, (UnitaryFieldData.mem_ker_normUnits h).2 hna⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply suMat_injective σ
    show suMat σ 4 (torusOf u) = suMat σ 4 (g : SU σ 4)
    rw [hmatOf u, hdiag, hdeq]
  have hbij : Function.Bijective θ := ⟨hinj, hsurj⟩
  have hcard : Nat.card ↥(Subgroup.centralizer
      (((T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂)) : Subgroup (SU σ 4)) : Set (SU σ 4))) = 2 ^ f + 1 := by
    rw [← Nat.card_eq_of_bijective θ hbij, hq]
  exact hcard

end CFSG.Timmesfeld.Transvection.ModelRank
