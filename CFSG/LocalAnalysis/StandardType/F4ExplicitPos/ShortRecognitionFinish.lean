module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SingleRootRecognition
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ShortPairDescentPart2

@[expose] public section

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal

open CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem Matrix

open CFSG.SeitzReduction.F4Pilot

open CFSG.Timmesfeld.ARS.CaseM

open CFSG.Timmesfeld.Transvection.ModelRank

open CFSG.StandardType.F4ExplicitPos.ShortPairDescent

open CFSG.StandardType.F4ExplicitPos.SingleRootRecognition

namespace CFSG.StandardType.F4ExplicitPos.ShortRecognitionFinish

theorem altNil_self_eq_zero {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : Fin n ⊕ Fin n → F) : altNil u u = 0 := by
  unfold altNil
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem altNil_smul_right {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (c : F) (u v : Fin n ⊕ Fin n → F) : altNil u (c • v) = c • altNil u v := by
  unfold altNil
  simp only [Matrix.mulVec_smul, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_add]

theorem altNil_mulVec {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (a b x : Fin n ⊕ Fin n → F) :
    altNil a b *ᵥ x = spForm b x • a + spForm a x • b := by
  unfold altNil
  rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
    dotProduct_mulVec_spGram, dotProduct_mulVec_spGram, op_smul_eq_smul, op_smul_eq_smul]
  rw [spForm_comm b x, CharTwo.neg_eq, spForm_comm a x, CharTwo.neg_eq]

theorem singleRootRecognition_unconditional {k Ω : Type} [Field k] [Finite k] [CharP k 2]
    [Field Ω] [Algebra k Ω] [CharP Ω 2]
    {P : Subgroup (StatedSp 3 k)} (hP : Nat.card P = Nat.card k)
    {β : Fin 3 → ℤ} (hβ : β ∈ (Symplectic.rootDatum 3 Ω).roots)
    (vΩ : StatedSp 3 Ω)
    (hplus : P.map (statedSpMap (algebraMap k Ω) 3) ≤
      ((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom) :
    ∃ β' ∈ (Symplectic.rootDatum 3 k).roots, ∃ u : StatedSp 3 k,
      P = ((Symplectic.rootDatum 3 k).rootGroup β').map (MulAut.conj u).toMonoidHom := by
  refine singleRootRecognition hP hβ vΩ hplus ?_
  intro hs
  obtain ⟨a₁, a₂, b₁, b₂, h₁, h₂, h₀, hXβ, -⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_altSiegelGroup_eq_conj_rootGroup_Sp 3 Ω hβ hs vΩ
  obtain ⟨h0a, -, h0ab, -⟩ := h₀
  have hab : spForm a₁ a₂ = 0 := h0a
  have h2 : spForm a₂ b₂ = 1 := h₂
  have h0ab' : spForm a₁ b₂ = 0 := h0ab
  let X : Subgroup (StatedSp 3 Ω) :=
    ((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom
  have hX : X.map (StatedSp 3 Ω).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) Ω) a₁ a₂ := by
    simpa only [X] using hXβ
  have hPX : P.map (statedSpMap (algebraMap k Ω) 3) ≤ X := hplus
  obtain ⟨u, v, hu0, hv0, hPalt, _huu, _hvv, huv, hμ⟩ :=
    short_case_recognition_of_altSiegelGroup hP (spForm_self a₁) (spForm_self a₂) hab hX hPX
  have hE : altNil u v ≠ 0 := by
    intro h0
    have hab_ne : altNil a₁ a₂ ≠ 0 := by
      intro hz
      have hbs : altNil a₁ a₂ *ᵥ b₂ = 0 := by rw [hz, Matrix.zero_mulVec]
      rw [altNil_mulVec, h2, h0ab'] at hbs
      simp only [one_smul, zero_smul, add_zero] at hbs
      have h1 : spForm a₁ b₁ = 1 := h₁
      rw [hbs] at h1
      exact (zero_ne_one : (0 : k) ≠ 1) (by simp [spForm] at h1)
    obtain ⟨μ, _hμ0, hμeq⟩ := hμ
    have hmap : altNil (fun i => algebraMap k Ω (u i)) (fun i => algebraMap k Ω (v i)) = 0 := by
      rw [← map_altNil, h0]
      simp
    rw [hmap, smul_zero] at hμeq
    exact hab_ne hμeq
  have hli : LinearIndependent k ![u, v] := by
    rw [LinearIndependent.pair_iff' hu0]
    intro c hc
    exact hE (by rw [← hc, altNil_smul_right, altNil_self_eq_zero, smul_zero])
  exact ⟨u, v, hli, huv,
    map_subtype_eq_altSiegelGroup_of_isAltSiegelGroup huv hPalt⟩

end CFSG.StandardType.F4ExplicitPos.ShortRecognitionFinish

end

end
