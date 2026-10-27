module

public import CFSG.RankThree.GF2n.Smith81.S81UFrame
public import CFSG.RankThree.GF2n.Smith81.S81A5Vt1

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

section UCard

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K] [Finite K]
  {e : K ≃+* Fσ σ}

@[expose] def u6cardA (σ : F ≃+* F) (d u : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  !![d 0, u 0, u 1; σ (u 0), d 1, u 2; σ (u 1), σ (u 2), d 2]

@[expose] def u6cardN (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  !![0, A 0 0, 0, A 0 1, 0, A 0 2;
    0, 0, 0, 0, 0, 0;
    0, A 1 0, 0, A 1 1, 0, A 1 2;
    0, 0, 0, 0, 0, 0;
    0, A 2 0, 0, A 2 1, 0, A 2 2;
    0, 0, 0, 0, 0, 0]

@[expose] def u6cardG (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  1 + u6cardN A

theorem u6cardN_mul_self (A : Matrix (Fin 3) (Fin 3) F) : u6cardN A * u6cardN A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, u6cardN]

theorem u6cardN_add_self (A : Matrix (Fin 3) (Fin 3) F) : u6cardN A + u6cardN A = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem u6cardG_mul_self (A : Matrix (Fin 3) (Fin 3) F) : u6cardG A * u6cardG A = 1 := by
  have h : (1 + u6cardN A) * (1 + u6cardN A) =
      1 + (u6cardN A + u6cardN A) + u6cardN A * u6cardN A := by
    noncomm_ring
  unfold u6cardG
  rw [h, u6cardN_add_self, u6cardN_mul_self, add_zero, add_zero]

theorem u6cardG_det (A : Matrix (Fin 3) (Fin 3) F) : (u6cardG A).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : (u6cardG A).det * (u6cardG A).det = 1 := by
    rw [← Matrix.det_mul, u6cardG_mul_self, Matrix.det_one]
  have h0 : ((u6cardG A).det - 1) * ((u6cardG A).det - 1) = 0 := by
    linear_combination hsq + (1 - (u6cardG A).det) * h2
  linear_combination mul_self_eq_zero.mp h0

@[expose] def u6cardUnit (A : Matrix (Fin 3) (Fin 3) F) : GL (Fin 6) F where
  val := u6cardG A
  inv := u6cardG A
  val_inv := u6cardG_mul_self A
  inv_val := u6cardG_mul_self A

theorem u6card_gram (hinv : ∀ c, σ (σ c) = c) {d u : Fin 3 → F} (hd : ∀ i, σ (d i) = d i) :
    conjTr σ (u6cardG (u6cardA σ d u)) * hypGram F * u6cardG (u6cardA σ d u) = hypGram F := by
  have hexp : conjTr σ (u6cardG (u6cardA σ d u)) * hypGram F * u6cardG (u6cardA σ d u) =
      hypGram F + ((conjTr σ (u6cardN (u6cardA σ d u)) * hypGram F +
        hypGram F * u6cardN (u6cardA σ d u)) +
        conjTr σ (u6cardN (u6cardA σ d u)) * hypGram F * u6cardN (u6cardA σ d u)) := by
    unfold u6cardG
    rw [conjTr_add, conjTr_one]
    noncomm_ring
  have hA1 : conjTr σ (u6cardN (u6cardA σ d u)) * hypGram F +
      hypGram F * u6cardN (u6cardA σ d u) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_six, conjTr_apply, u6cardN, u6cardA, hypGram, hinv, hd,
        CharTwo.add_self_eq_zero]
  have hA2 : conjTr σ (u6cardN (u6cardA σ d u)) * hypGram F * u6cardN (u6cardA σ d u) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_six, conjTr_apply, u6cardN, u6cardA, hypGram]
  rw [hexp, hA1, hA2, add_zero, add_zero]

theorem u6card_conj_mem (hinv : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1)
    {d u : Fin 3 → F} (hd : ∀ i, σ (d i) = d i) :
    frameGL σ ω hω * u6cardUnit (u6cardA σ d u) * (frameGL σ ω hω)⁻¹ ∈ SUid σ 6 :=
  frame_conj_mem_SUid hinv hω (u6cardG_det _) (u6card_gram hinv hd)

@[expose] noncomputable def u6cardElt (hinv : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1)
    (d u : Fin 3 → F) (hd : ∀ i, σ (d i) = d i) : SUid σ 6 :=
  ⟨frameGL σ ω hω * u6cardUnit (u6cardA σ d u) * (frameGL σ ω hω)⁻¹, u6card_conj_mem hinv hω hd⟩

theorem u6cardElt_val (hinv : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1)
    (d u : Fin 3 → F) (hd : ∀ i, σ (d i) = d i) :
    ((u6cardElt hinv hω d u hd : SUid σ 6) : GL (Fin 6) F) =
      frameGL σ ω hω * u6cardUnit (u6cardA σ d u) * (frameGL σ ω hω)⁻¹ := rfl

theorem u6card_col (A : Matrix (Fin 3) (Fin 3) F) (j : Fin 3) :
    (u6cardG A).mulVec (Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F)) =
      Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F) := by
  fin_cases j <;> funext r <;> fin_cases r <;>
    simp [u6cardG, u6cardN, Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.single_apply]

theorem u6card_fix (ω : F) (hω : ω + σ ω = 1) (A : Matrix (Fin 3) (Fin 3) F) :
    ∀ i : Fin 3, ((frameGL σ ω hω * u6cardUnit A * (frameGL σ ω hω)⁻¹ : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) = e3uT0Vec i := by
  intro i
  have hM : frameMat σ ω * u6cardG A * frameInv σ ω * frameMat σ ω =
      frameMat σ ω * u6cardG A := by
    rw [Matrix.mul_assoc (frameMat σ ω * u6cardG A), frameInv_mul_frameMat hω, Matrix.mul_one]
  have hval : ((frameGL σ ω hω * u6cardUnit A * (frameGL σ ω hω)⁻¹ : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) = frameMat σ ω * u6cardG A * frameInv σ ω := by
    rw [Units.val_mul, Units.val_mul]
    rfl
  rw [hval, ← frameMat_mulVec_even (σ := σ) ω i, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec,
    u6card_col]

theorem u6cardElt_fix (hinv : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1)
    (d u : Fin 3 → F) (hd : ∀ i, σ (d i) = d i) :
    ∀ i : Fin 3, (((u6cardElt hinv hω d u hd : SUid σ 6) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) = e3uT0Vec i := by
  rw [u6cardElt_val]
  exact u6card_fix ω hω (u6cardA σ d u)

theorem u6cardElt_mem (hinv : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1)
    (d u : Fin 3 → F) (hd : ∀ i, σ (d i) = d i) :
    u6cardElt hinv hω d u hd ∈ e3uU0Sub σ := by
  intro i
  exact u6cardElt_fix hinv hω d u hd i

theorem u6card_smul_mulVec (c : F) (M : Matrix (Fin 6) (Fin 6) F) (v : Fin 6 → F) :
    (c • M).mulVec v = c • M.mulVec v := by
  funext r
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem u6card_units_eq (hσ : IsUnitaryInvolution σ) {g h : SUid σ 6}
    (hg : ∀ i : Fin 3,
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) = e3uT0Vec i)
    (hh : ∀ i : Fin 3,
      ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) = e3uT0Vec i)
    (hgh : e3uWact σ e g = e3uWact σ e h) : (g : GL (Fin 6) F) = (h : GL (Fin 6) F) := by
  have h1 : e3uWact σ e (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  obtain ⟨l, -, hl⟩ := (e3uWact_eq_one_iff hσ (g * h⁻¹)).mp h1
  have hgx : (g : GL (Fin 6) F) = ((g * h⁻¹ : SUid σ 6) : GL (Fin 6) F) * (h : GL (Fin 6) F) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  have hmat : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      l • ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    rw [hgx, Units.val_mul, hl, Matrix.smul_mul, one_mul]
  have hv : l • e3uT0Vec (F := F) (0 : Fin 3) = e3uT0Vec (F := F) 0 := by
    calc l • e3uT0Vec (F := F) (0 : Fin 3)
        = (l • ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)).mulVec (e3uT0Vec 0) := by
          rw [u6card_smul_mulVec, hh 0]
      _ = ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 0) := by rw [hmat]
      _ = e3uT0Vec 0 := hg 0
  have hl1 : l = 1 := by
    have h0 := congrFun hv 0
    simpa [e3uT0Vec] using h0
  rw [hl1, one_smul] at hmat
  exact Units.ext hmat

@[expose] def u6cardDd (d : Fin 3 → Fσ σ) : Fin 3 → F := fun i => ((d i : Fσ σ) : F)

theorem u6cardDd_fix (d : Fin 3 → Fσ σ) : ∀ i, σ (u6cardDd d i) = u6cardDd d i :=
  fun i => mem_Fσ_iff.mp (d i).2

theorem u6card_domain_card (e : K ≃+* Fσ σ) (hF : Nat.card F = Nat.card K ^ 2) :
    Nat.card ((Fin 3 → Fσ σ) × (Fin 3 → F)) = Nat.card K ^ 9 := by
  have hFσ : Nat.card (Fσ σ) = Nat.card K := (Nat.card_congr e.toEquiv).symm
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, hFσ, hF, Nat.card_eq_fintype_card (α := Fin 3),
    Fintype.card_fin]
  ring

theorem u6_U_card (hσ : IsUnitaryInvolution σ) (hF : Nat.card F = Nat.card K ^ 2) :
    Nat.card K ^ 9 ≤ Nat.card (e3uU0 σ e) := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  haveI : Finite (Cube F) := Module.finite_of_finite F
  haveI : Finite (E3UWspace σ e) := (Subtype.finite : Finite (Wform σ))
  haveI : Finite (E3UWspace σ e ≃ₗ[K] E3UWspace σ e) :=
    Finite.of_injective (fun f : E3UWspace σ e ≃ₗ[K] E3UWspace σ e =>
      (f : E3UWspace σ e → E3UWspace σ e)) (fun f g h => LinearEquiv.ext fun x => congrFun h x)
  let Ψ : (Fin 3 → Fσ σ) × (Fin 3 → F) → e3uU0 σ e := fun p =>
    ⟨e3uWact σ e (u6cardElt hσ.invol hω (u6cardDd p.1) p.2 (u6cardDd_fix p.1)),
      Subgroup.mem_map_of_mem (e3uWact σ e) (u6cardElt_mem hσ.invol hω (u6cardDd p.1) p.2
        (u6cardDd_fix p.1))⟩
  have hΨ : Function.Injective Ψ := by
    rintro ⟨d₁, u₁⟩ ⟨d₂, u₂⟩ h
    have hw : e3uWact σ e (u6cardElt hσ.invol hω (u6cardDd d₁) u₁ (u6cardDd_fix d₁)) =
        e3uWact σ e (u6cardElt hσ.invol hω (u6cardDd d₂) u₂ (u6cardDd_fix d₂)) :=
      congrArg Subtype.val h
    have hGL := u6card_units_eq hσ (u6cardElt_fix hσ.invol hω (u6cardDd d₁) u₁ (u6cardDd_fix d₁))
      (u6cardElt_fix hσ.invol hω (u6cardDd d₂) u₂ (u6cardDd_fix d₂)) hw
    have h1 : u6cardUnit (u6cardA σ (u6cardDd d₁) u₁) =
        (frameGL σ ω hω)⁻¹ * ((u6cardElt hσ.invol hω (u6cardDd d₁) u₁ (u6cardDd_fix d₁) :
          SUid σ 6) : GL (Fin 6) F) * frameGL σ ω hω := by
      rw [u6cardElt_val]
      group
    have h2 : u6cardUnit (u6cardA σ (u6cardDd d₂) u₂) =
        (frameGL σ ω hω)⁻¹ * ((u6cardElt hσ.invol hω (u6cardDd d₂) u₂ (u6cardDd_fix d₂) :
          SUid σ 6) : GL (Fin 6) F) * frameGL σ ω hω := by
      rw [u6cardElt_val]
      group
    have hU : u6cardUnit (u6cardA σ (u6cardDd d₁) u₁) = u6cardUnit (u6cardA σ (u6cardDd d₂) u₂) := by
      rw [h1, h2, hGL]
    have hG : u6cardG (u6cardA σ (u6cardDd d₁) u₁) = u6cardG (u6cardA σ (u6cardDd d₂) u₂) :=
      congrArg Units.val hU
    have e01 := congrFun (congrFun hG 0) 1
    have e23 := congrFun (congrFun hG 2) 3
    have e45 := congrFun (congrFun hG 4) 5
    have e03 := congrFun (congrFun hG 0) 3
    have e05 := congrFun (congrFun hG 0) 5
    have e25 := congrFun (congrFun hG 2) 5
    simp [u6cardG, u6cardN, u6cardA, u6cardDd] at e01 e23 e45 e03 e05 e25
    have hd : d₁ = d₂ := by
      funext i
      fin_cases i
      · exact e01
      · exact e23
      · exact e45
    have hu : u₁ = u₂ := by
      funext i
      fin_cases i
      · exact e03
      · exact e05
      · exact e25
    rw [hd, hu]
  have hcard := u6card_domain_card e hF
  rw [← hcard]
  exact Nat.card_le_card_of_injective Ψ hΨ

end UCard

end CFSG.RankThree.GF2n.Smith81
