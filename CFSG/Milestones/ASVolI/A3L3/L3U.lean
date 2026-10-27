module

public import CFSG.Milestones.ASVolI.A3L3.L3Facts

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.ASVolI.ChA
open scoped MatrixGroups

section L3U

variable {F : Type} [Field F]

@[expose] def burnsideA315y_IsUT (g : Matrix (Fin 3) (Fin 3) F) : Prop :=
  g 0 0 = 1 ∧ g 1 1 = 1 ∧ g 2 2 = 1 ∧ g 1 0 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0

@[expose] def burnsideA315y_utMat (a b c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a, b; 0, 1, c; 0, 0, 1]

theorem burnsideA315y_eq_utMat {g : Matrix (Fin 3) (Fin 3) F} (hg : burnsideA315y_IsUT g) :
    g = burnsideA315y_utMat (g 0 1) (g 0 2) (g 1 2) := by
  obtain ⟨h00, h11, h22, h10, h20, h21⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideA315y_utMat, h00, h11, h22, h10, h20, h21]

theorem burnsideA315y_utMat_isUT (a b c : F) : burnsideA315y_IsUT (burnsideA315y_utMat a b c) := by
  simp [burnsideA315y_IsUT, burnsideA315y_utMat]

theorem burnsideA315y_det_utMat (a b c : F) : (burnsideA315y_utMat a b c).det = 1 := by
  simp [burnsideA315y_utMat, Matrix.det_fin_three]

theorem burnsideA315y_utMat_mul (a b c a' b' c' : F) :
    burnsideA315y_utMat a b c * burnsideA315y_utMat a' b' c' =
      burnsideA315y_utMat (a + a') (b' + a * c' + b) (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideA315y_utMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem burnsideA315y_utMat_mul_inv (a b c : F) :
    burnsideA315y_utMat a b c * burnsideA315y_utMat (-a) (a * c - b) (-c) = 1 := by
  rw [burnsideA315y_utMat_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideA315y_utMat] <;> ring

variable (Γ : Subgroup (GL (Fin 3) F))

@[expose] def burnsideA315y_U1 : Subgroup ↥Γ where
  carrier := {g | burnsideA315y_IsUT ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Units.val_mul] at ha hb ⊢
    rw [burnsideA315y_eq_utMat ha, burnsideA315y_eq_utMat hb, burnsideA315y_utMat_mul]
    exact burnsideA315y_utMat_isUT _ _ _
  one_mem' := by
    simp [burnsideA315y_IsUT]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 := burnsideA315y_eq_utMat ha
    have hinv : (((a⁻¹ : ↥Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        burnsideA315y_utMat (-((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1)
          (((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 *
            ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 -
            ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2)
          (-((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2) := by
      rw [Subgroup.coe_inv]
      apply Units.inv_eq_of_mul_eq_one_right
      conv_lhs => rw [h1]
      exact burnsideA315y_utMat_mul_inv _ _ _
    rw [hinv]
    exact burnsideA315y_utMat_isUT _ _ _

end L3U

section Model

variable {F : Type} [Field F] [Finite F] {x y : F} {hxy : x ^ 2 + y ^ 2 = -1}
  {two_ne : (2 : F) ≠ 0}

theorem burnsideA315y_l3_card_U1 :
    Nat.card ↥(burnsideA315y_U1 (burnsideA315y_l3Model x y hxy two_ne).Γ) = Nat.card F ^ 3 := by
  set M := burnsideA315y_l3Model x y hxy two_ne with hM
  let f : F × F × F → ↥(burnsideA315y_U1 M.Γ) := fun t =>
    ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (burnsideA315y_utMat t.1 t.2.1 t.2.2)
      (by rw [burnsideA315y_det_utMat]; exact one_ne_zero), trivial⟩,
      burnsideA315y_utMat_isUT _ _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      have h1 := congrArg (fun u : ↥(burnsideA315y_U1 M.Γ) =>
        (((u : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
      simp only [f] at h1
      have e1 := congrFun (congrFun h1 0) 1
      have e2 := congrFun (congrFun h1 0) 2
      have e3 := congrFun (congrFun h1 1) 2
      simp [burnsideA315y_utMat, Matrix.GeneralLinearGroup.mkOfDetNeZero] at e1 e2 e3
      simp [e1, e2, e3]
    · rintro ⟨g, hg⟩
      refine ⟨(((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1,
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2,
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      exact (burnsideA315y_eq_utMat hg).symm
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod]
  ring

theorem burnsideA315y_l3_U1_le :
    burnsideA315y_U1 (burnsideA315y_l3Model x y hxy two_ne).Γ ≤
      (burnsideA315y_l3Model x y hxy two_ne).Γ₁ := by
  intro g hg
  show ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1
  rw [burnsideA315y_eq_utMat hg, burnsideA315y_det_utMat]

theorem burnsideA315y_l3_U1_ker {g : ↥(burnsideA315y_l3Model x y hxy two_ne).Γ}
    (hg : g ∈ burnsideA315y_U1 (burnsideA315y_l3Model x y hxy two_ne).Γ)
    (h1 : (burnsideA315y_l3Model x y hxy two_ne).c g = 1) : g = 1 := by
  obtain ⟨μ, hμ⟩ := (burnsideA315y_l3Model x y hxy two_ne).exists_scalar_of_c_eq_one h1
  have h00 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := hg.1
  rw [hμ] at h00
  have hμ1 : μ = 1 := Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar] using h00)
  apply Subtype.ext
  rw [hμ, hμ1, map_one, Subgroup.coe_one]

theorem burnsideA315y_l3_card_Γ₁ {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    Nat.card ↥(burnsideA315y_l3Model x y hxy two_ne).Γ₁ * (p - 1) =
      (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2) := by
  haveI := Fintype.ofFinite F
  have hFc : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card, hF]
  have := Subgroup.card_mul_index (burnsideA315y_l3Model x y hxy two_ne).Γ₁
  rw [burnsideA315y_l3_index_Γ₁, Nat.card_units, hF] at this
  rw [this]
  show Nat.card ↥(⊤ : Subgroup (GL (Fin 3) F)) = _
  rw [Subgroup.card_top, Matrix.card_GL_field, hFc, Fin.prod_univ_three]
  simp

theorem burnsideA315y_l3_arithU {p R : ℕ} (hp : 2 ≤ p)
    (h : R * p ^ 3 * (p - 1) = (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2)) :
    R = (p ^ 3 - 1) * (p ^ 2 - 1) := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ p := by omega
  have h4 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h5 : p ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
  have h6 : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  zify [h1, h3, h4, h5, h6] at h ⊢
  have hP : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hne : ((p : ℤ) ^ 3 * ((p : ℤ) - 1)) ≠ 0 := by
    have ha : (0 : ℤ) < (p : ℤ) ^ 3 := by positivity
    have hb : (0 : ℤ) < (p : ℤ) - 1 := by linarith
    exact mul_ne_zero ha.ne' hb.ne'
  have h7 : ((R : ℤ) - ((p : ℤ) ^ 3 - 1) * ((p : ℤ) ^ 2 - 1)) * ((p : ℤ) ^ 3 * ((p : ℤ) - 1)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h7 with h8 | h8
  · exact sub_eq_zero.mp h8
  · exact absurd h8 hne

theorem burnsideA315y_not_dvd_pow_sub_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ¬ p ∣ p ^ k - 1 := by
  intro h
  have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
  have h2 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have h3 : p ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one h3)

theorem burnsideA315y_l3_cartanU {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    ∃ U : Subgroup (MulAut PSL(3, F)),
      CFSG.Quasithin.A315.IsSylowOf p U (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)).range ∧
      (burnsideA315y_l3Model x y hxy two_ne).D₀.map (burnsideA315y_l3Model x y hxy two_ne).c ≤
        Subgroup.normalizer (U : Set (MulAut PSL(3, F))) := by
  set M := burnsideA315y_l3Model x y hxy two_ne with hM
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  set U₁ := burnsideA315y_U1 M.Γ with hU₁
  have hcardU : Nat.card ↥(U₁.map M.c) = p ^ 3 := by
    rw [burnsideA315y_card_map_of_ker M.c U₁ (fun g hg h1 => burnsideA315y_l3_U1_ker hg h1),
      burnsideA315y_l3_card_U1, hF]
  refine ⟨U₁.map M.c, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← burnsideA315y_l3Model_L (x := x) (y := y) (hxy := hxy) (two_ne := two_ne)]
    exact Subgroup.map_mono burnsideA315y_l3_U1_le
  · exact IsPGroup.of_card hcardU
  · rw [← burnsideA315y_l3Model_L (x := x) (y := y) (hxy := hxy) (two_ne := two_ne)]
    intro hdvd
    have h1 : (U₁.map M.c).relIndex (M.Γ₁.map M.c) ∣ U₁.relIndex M.Γ₁ :=
      burnsideA315y_relIndex_map_dvd M.c burnsideA315y_l3_U1_le
    have h2 : U₁.relIndex M.Γ₁ * Nat.card ↥U₁ = Nat.card ↥M.Γ₁ := by
      have := Subgroup.relIndex_mul_card U₁ M.Γ₁
      rwa [inf_eq_left.mpr burnsideA315y_l3_U1_le] at this
    have h3 := burnsideA315y_l3_card_Γ₁ (x := x) (hxy := hxy) (two_ne := two_ne) hF
    rw [← h2, burnsideA315y_l3_card_U1, hF] at h3
    have h4 := burnsideA315y_l3_arithU hp2 h3
    have h5 : p ∣ (p ^ 3 - 1) * (p ^ 2 - 1) := by
      rw [← h4]
      exact hdvd.trans h1
    rcases (Nat.Prime.dvd_mul hp).mp h5 with h6 | h6
    · exact burnsideA315y_not_dvd_pow_sub_one hp (by norm_num) h6
    · exact burnsideA315y_not_dvd_pow_sub_one hp (by norm_num) h6
  ·
    have key : ∀ d ∈ M.D₀, ∀ u ∈ U₁, d * u * d⁻¹ ∈ U₁ := by
      intro d hd u hu
      obtain ⟨h01, h10, h11, h02, h12, h20, h21⟩ := M.D₀_form hd
      set D := ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hD
      have hdet : D.det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det D).mp (d : GL (Fin 3) F).isUnit).ne_zero
      rw [Matrix.det_fin_three, h01, h10, h11, h02, h12, h20, h21] at hdet
      have ha : D 0 0 ≠ 0 := by
        intro h0
        apply hdet
        rw [h0]
        ring
      have hw : D 2 2 ≠ 0 := by
        intro h0
        apply hdet
        rw [h0]
        ring
      have hDdiag : D = diagonal ![D 0 0, D 0 0, D 2 2] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h10, h11, h02, h12, h20, h21]
      have hinv : (((d⁻¹ : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal ![(D 0 0)⁻¹, (D 0 0)⁻¹, (D 2 2)⁻¹] := by
        rw [Subgroup.coe_inv]
        apply Units.inv_eq_of_mul_eq_one_right
        rw [← hD, hDdiag, diagonal_mul_diagonal]
        convert diagonal_one (n := Fin 3) (α := F) using 2
        funext i
        fin_cases i <;> simp [ha, hw]
      show burnsideA315y_IsUT (((d * u * d⁻¹ : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [hinv, ← hD, hDdiag, burnsideA315y_eq_utMat hu]
      simp [burnsideA315y_IsUT, burnsideA315y_utMat, Matrix.mul_apply, Fin.sum_univ_three,
        diagonal, ha, hw]
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨d * u * d⁻¹, key d hd u hu, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨u, hu, hzu⟩
      refine ⟨d⁻¹ * u * d, ?_, ?_⟩
      · have := key d⁻¹ (M.D₀.inv_mem hd) u hu
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv, hzu]
        group

end Model

end CFSG.ASVolI
