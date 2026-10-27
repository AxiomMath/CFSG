module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrameAux2
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvection

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open InndiagSU
open scoped Pointwise

variable {G : Type} [Group G] {K : Type} [Field K]

theorem e6QTwoSixIsSemilin_conj_frameMk (h : UnitaryFieldData 2 1 K) {Q : GL (Fin 6) K}
    (hQ : Q ∈ primeFormUnitary h (idGram K 6))
    (P : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
    IsSemilin (frameMk h Q hQ) (MulAut.conj (frameMk h Q hQ P)) (P : GL (Fin 6) K) 1 := by
  intro u v huv
  have hu : P * u * P⁻¹ = v := by
    refine Subtype.ext ?_
    simpa using huv.symm
  have hmul : frameMk h Q hQ P * frameMk h Q hQ u * (frameMk h Q hQ P)⁻¹ =
      frameMk h Q hQ (P * u * P⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [MulAut.conj_apply, hmul, hu]

@[expose] noncomputable def e6QTwoSixFramePerm (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6))
    (τ : Equiv.Perm (Fin 6)) : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
  MulAut.conj (frameMk (USixTwo.fieldDataFour hK) Q hQ (USixTwo.permGLSU hK τ))

theorem e6QTwoSixPowThreeVal (hK : Nat.card K = 4) {σ : Fin 6 → Kˣ}
    (hσ : ∀ k, σ k ^ 3 = 1) (k : Fin 6) :
    ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
  rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val, hσ k, Units.val_one]

theorem e6QTwoSixFrameAct_perm (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6)}
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))} {σ : Fin 6 → Kˣ}
    (he : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ) (τ : Equiv.Perm (Fin 6)) :
    TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoSixFramePerm hK hQ τ * e * (e6QTwoSixFramePerm hK hQ τ)⁻¹)
      (σ ∘ ⇑τ.symm) := by
  haveI : Finite K := USixTwo.finite_of_card_eq_four hK
  have hσn : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := fun k => by
    rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
      USixTwo.cube_unit_eq_one hK (σ k), Units.val_one]
  have hmatGL : (USixTwo.permGLSU hK τ : GL (Fin 6) K) * (diagHom 6 σ : GL (Fin 6) K) *
      ((USixTwo.permGLSU hK τ : GL (Fin 6) K))⁻¹ = (diagHom 6 (σ ∘ ⇑τ.symm) : GL (Fin 6) K) := by
    have hcoe : (USixTwo.permGLSU hK τ : GL (Fin 6) K) = TauCeti.permutationGL (k := K) τ :=
      USixTwo.coe_permGLSU hK τ
    have hdiag : (diagHom 6 σ : GL (Fin 6) K) = TauCeti.diagGL σ := Units.ext (by
      rw [coe_diagHom, TauCeti.diagGL_coe])
    have hdiag' : (diagHom 6 (σ ∘ ⇑τ.symm) : GL (Fin 6) K) = TauCeti.diagGL (σ ∘ ⇑τ.symm) :=
      Units.ext (by rw [coe_diagHom, TauCeti.diagGL_coe])
    rw [hcoe, hdiag, hdiag']
    rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix (TauCeti.permutationGL (k := K) τ) τ.symm
      (TauCeti.permutationGL_coe τ) σ]
    group
  have hmat : (USixTwo.permGLSU hK τ : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) *
      diagHom 6 σ * (USixTwo.permGLSU hK τ)⁻¹ = diagHom 6 (σ ∘ ⇑τ.symm) := by
    simpa using hmatGL
  have hP : (USixTwo.permGLSU hK τ : GL (Fin 6) K) ∈
      primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6) :=
    TableBUE.unitarySU_le_primeFormUnitary (USixTwo.fieldDataFour hK) (USixTwo.permGLSU hK τ).2
  have hconj := e6QTwoSixIsSemilin_conj_frameMk (USixTwo.fieldDataFour hK) (Q := Q) hQ
    (USixTwo.permGLSU hK τ)
  have hinv := TableBUD.IsSemilin.inv hconj
  have h1 := hconj.mul (USixTwo.fieldDataFour hK) he
    (TableBUD.diagHom_mem_primeFormUnitary (USixTwo.fieldDataFour hK) hσn)
  have h2 := h1.mul (USixTwo.fieldDataFour hK) hinv (Subgroup.inv_mem _ hP)
  rw [show (1 : K ≃+* K) * 1 * 1⁻¹ = 1 from by group] at h2
  simp only [map_one, MulAut.one_apply, inv_one, one_mul, mul_one] at h2
  rw [hmatGL] at h2
  exact h2

theorem e6QTwoSixFrameAct_exists (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6)}
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ)
    {σ : Fin 6 → Kˣ} (hσ : ∀ k, σ k ^ 3 = 1) :
    ∃ e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
      TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ := by
  have hσ0 : ∀ k, ((σ (0 : Fin 6))⁻¹ * σ k) ^ 3 = 1 := by
    intro k
    rw [mul_pow, inv_pow, hσ k, hσ (0 : Fin 6), inv_one, one_mul]
  obtain ⟨e, he⟩ := hfull (fun k => (σ (0 : Fin 6))⁻¹ * σ k) (by simp) hσ0
  refine ⟨e, ?_⟩
  have h := TableBUD.FrameAct.smul he (σ (0 : Fin 6))
  have hfun : (fun k => σ (0 : Fin 6) * ((σ (0 : Fin 6))⁻¹ * σ k)) = σ := by
    funext k
    rw [mul_inv_cancel_left]
  rwa [hfun] at h

theorem e6QTwoSixFrameAct_inj (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6)}
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))} {σ σ' : Fin 6 → Kˣ}
    (hσ0 : σ (0 : Fin 6) = 1) (hσ'0 : σ' (0 : Fin 6) = 1)
    (hσ : ∀ k, σ k ^ 3 = 1) (hσ' : ∀ k, σ' k ^ 3 = 1)
    (h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ)
    (h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ') : σ = σ' := by
  haveI : Finite K := USixTwo.finite_of_card_eq_four hK
  obtain ⟨c, hc⟩ := TableBUD.FrameAct.eq_smul (n := 1) (h := USixTwo.fieldDataFour hK)
    (by rw [hK]; norm_num) (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2))
    (p := 3) (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1)
    (fun k => e6QTwoSixPowThreeVal hK hσ k) (fun k => e6QTwoSixPowThreeVal hK hσ' k) h1 h2
  have hc1 : c = 1 := by
    have h0 := hc (0 : Fin 6)
    rw [hσ'0, hσ0, mul_one] at h0
    exact h0.symm
  funext k
  rw [hc k, hc1, one_mul]

theorem e6QTwoSixFrameAct_apply_eq_of_swap (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6)}
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))} {σ : Fin 6 → Kˣ}
    (hσ : ∀ k, σ k ^ 3 = 1)
    (he : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ) {i j : Fin 6} (hij : i ≠ j)
    (hfix : e6QTwoSixFramePerm hK hQ (Equiv.swap i j) * e *
      (e6QTwoSixFramePerm hK hQ (Equiv.swap i j))⁻¹ = e) :
    σ i = σ j := by
  haveI : Finite K := USixTwo.finite_of_card_eq_four hK
  have hσ3 : ∀ k, ((σ ∘ ⇑(Equiv.swap i j).symm) k) ^ 3 = 1 := fun k => hσ _
  have h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e
      (σ ∘ ⇑(Equiv.swap i j).symm) := by
    rw [← hfix]
    exact e6QTwoSixFrameAct_perm hK he (Equiv.swap i j)
  obtain ⟨c, hc⟩ := TableBUD.FrameAct.eq_smul (n := 1) (h := USixTwo.fieldDataFour hK)
    (by rw [hK]; norm_num) (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2))
    (p := 3) (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1)
    (fun k => e6QTwoSixPowThreeVal hK hσ3 k) (fun k => e6QTwoSixPowThreeVal hK hσ k) h2 he
  have h1 : σ i = c * σ j := by
    have h := hc i
    simpa [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] using h
  have h2' : σ j = c * σ i := by
    have h := hc j
    simpa [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right] using h
  have hc2 : c ^ 2 = 1 := by
    have h : c ^ 2 * σ i = 1 * σ i := by
      rw [one_mul]
      calc c ^ 2 * σ i = c * (c * σ i) := by rw [sq, mul_assoc]
        _ = c * σ j := by rw [h2']
        _ = σ i := h1.symm
    exact mul_right_cancel h
  have hc3 : c ^ 3 = 1 := USixTwo.cube_unit_eq_one hK c
  have hc1 : c = 1 := by
    have h := (pow_gcd_eq_one (a := c)).mpr ⟨hc2, hc3⟩
    rwa [show Nat.gcd 2 3 = 1 from by norm_num, pow_one] at h
  rw [h1, hc1, one_mul]

theorem e6QTwoSixFramePerm_injective_of_forall (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6)}
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ)
    {τ τ' : Equiv.Perm (Fin 6)}
    (h : ∀ σ : Fin 6 → Kˣ, (∀ k, σ k ^ 3 = 1) →
      ∀ e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ →
        e6QTwoSixFramePerm hK hQ τ * e * (e6QTwoSixFramePerm hK hQ τ)⁻¹ =
          e6QTwoSixFramePerm hK hQ τ' * e * (e6QTwoSixFramePerm hK hQ τ')⁻¹) :
    τ = τ' := by
  haveI : Finite K := USixTwo.finite_of_card_eq_four hK
  obtain ⟨ω, hωne⟩ := USixTwo.exists_unit_ne_one hK
  apply Equiv.Perm.ext
  intro p
  by_contra hne
  let f : Fin 6 → Kˣ := fun k => if k = p then ω else 1
  have hfp : f p = ω := by simp [f]
  have hf_ne : ∀ x : Fin 6, x ≠ p → f x = 1 := by
    intro x hx
    simp [f, hx]
  have hf3 : ∀ k, f k ^ 3 = 1 := by
    intro k
    by_cases hk : k = p
    · rw [show f k = ω from by simp [f, hk]]
      exact USixTwo.cube_unit_eq_one hK ω
    · rw [hf_ne k hk]
      exact one_pow 3
  obtain ⟨e, he⟩ := e6QTwoSixFrameAct_exists hK hfull hf3
  have hconj := h f hf3 e he
  have h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoSixFramePerm hK hQ τ * e * (e6QTwoSixFramePerm hK hQ τ)⁻¹) (f ∘ ⇑τ.symm) :=
    e6QTwoSixFrameAct_perm hK he τ
  have h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoSixFramePerm hK hQ τ * e * (e6QTwoSixFramePerm hK hQ τ)⁻¹) (f ∘ ⇑τ'.symm) := by
    rw [hconj]
    exact e6QTwoSixFrameAct_perm hK he τ'
  have hf3' : ∀ k, ((f ∘ ⇑τ.symm) k) ^ 3 = 1 := fun k => hf3 _
  have hf3'' : ∀ k, ((f ∘ ⇑τ'.symm) k) ^ 3 = 1 := fun k => hf3 _
  obtain ⟨c, hc⟩ := TableBUD.FrameAct.eq_smul (n := 1) (h := USixTwo.fieldDataFour hK)
    (by rw [hK]; norm_num) (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2))
    (p := 3) (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1)
    (fun k => e6QTwoSixPowThreeVal hK hf3'' k) (fun k => e6QTwoSixPowThreeVal hK hf3' k) h2 h1
  have hA : τ'.symm (τ p) ≠ p := by
    intro hh
    apply hne
    simpa using congrArg (⇑τ') hh
  have hB : τ.symm (τ' p) ≠ p := by
    intro hh
    apply hne
    simpa using (congrArg (⇑τ) hh).symm
  have h1' : (1 : Kˣ) = c * ω := by
    have hk := hc (τ' p)
    simp only [Function.comp_apply] at hk
    rw [hf_ne _ hB, τ'.symm_apply_apply, hfp] at hk
    exact hk
  have h2' : ω = c := by
    have hk := hc (τ p)
    simp only [Function.comp_apply] at hk
    rw [τ.symm_apply_apply, hf_ne _ hA, hfp, mul_one] at hk
    exact hk
  have hsq : ω ^ 2 = 1 := by
    have h1'' : (1 : Kˣ) = ω * ω := by
      rw [← h2'] at h1'
      exact h1'
    calc ω ^ 2 = ω * ω := by rw [pow_two]
      _ = 1 := h1''.symm
  have hω1 : ω = 1 := by
    have h := (pow_gcd_eq_one (a := ω)).mpr ⟨hsq, USixTwo.cube_unit_eq_one hK ω⟩
    rwa [show Nat.gcd 2 3 = 1 from by norm_num, pow_one] at h
  exact hωne hω1

end CFSG.StandardType.E6QTwo

end
