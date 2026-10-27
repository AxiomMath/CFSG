module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Gen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Transitive
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3P1
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.GL2Max
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3P1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open Matrix CFSG.LargeExtraspecial.A2Mod CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsLThreeTwo)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2Odd Bar2)
open CFSG.Blueprint (LieModel)

variable {F : Type} [Field F]

theorem false_of_transitive_of_sl2_le {W : Subgroup (SL3 F)} {μ : F} (hμ0 : μ ≠ 0)
    (hμ3 : μ ^ 3 ≠ 1) (hμW : lev (scalGL μ hμ0) ∈ W)
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v) (hb : W ⊓ P1 ⊓ Q1 = ⊥)
    (hSL : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range ≤
      ((W ⊓ P1).subgroupOf P1).map rho1) : False := by
  let τ : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  obtain ⟨y, hyW, hy⟩ := hSL ⟨τ, rfl⟩
  replace hyW : (y : SL3 F) ∈ W ⊓ P1 := hyW
  have hyM : ((rho1 y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := by
    rw [hy]
    rfl
  let s : ↥(P1 : Subgroup (SL3 F)) := ⟨lev (scalGL μ hμ0), lev_mem_P1 _⟩
  have hsy : s * y = y * s := by
    have hc : scalGL μ hμ0 * rho1 y = rho1 y * scalGL μ hμ0 :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, coe_scalGL, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
    have hk : rho1 (s * y * s⁻¹ * y⁻¹) = 1 := by
      have hs : rho1 s = scalGL μ hμ0 := rho1_lev _
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hs, hc, mul_inv_cancel_right,
        mul_inv_cancel]
    have hmem : ((s * y * s⁻¹ * y⁻¹ : ↥(P1 : Subgroup (SL3 F))) : SL3 F) ∈ W ⊓ P1 ⊓ Q1 :=
      ⟨⟨W.mul_mem (W.mul_mem (W.mul_mem hμW hyW.1) (W.inv_mem hμW)) (W.inv_mem hyW.1),
        (s * y * s⁻¹ * y⁻¹).2⟩, mem_ker_rho1.mp hk⟩
    rw [hb, Subgroup.mem_bot] at hmem
    have h1 : s * y * s⁻¹ * y⁻¹ = 1 := Subtype.ext hmem
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hsyM := congrArg (fun g : ↥(P1 : Subgroup (SL3 F)) =>
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) hsy
  simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul] at hsyM
  have hrow : ∀ j : Fin 3, j ≠ 0 → ((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 j = 0 := by
    intro j hj
    have h := congrFun (congrFun hsyM 0) j
    have key : ∀ a : F, (μ ^ 2)⁻¹ * a = a * μ → a = 0 := by
      intro a ha
      have h1 : a * (μ ^ 3 - 1) = 0 := by
        have h2 : a = a * μ ^ 3 := by
          calc a = μ ^ 2 * ((μ ^ 2)⁻¹ * a) := by field_simp
            _ = μ ^ 2 * (a * μ) := by rw [ha]
            _ = a * μ ^ 3 := by ring
        linear_combination -h2
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.mp h3) hμ3
    fin_cases j
    · exact absurd rfl hj
    all_goals
      simp [s, coe_lev, levMat, coe_scalGL, Matrix.mul_apply, Fin.sum_univ_three] at h
      first | exact key _ h | exact key _ h.symm
  have hblock : ((y : SL3 F) : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ =
      !![1, 1; 0, 1] := (coe_rho1 y).symm.trans hyM
  have hdet := P1_det_eq y.2
  rw [hblock, Matrix.det_fin_two_of] at hdet
  obtain ⟨h10, h20⟩ := hyW.2
  have h01 := hrow 1 (by decide)
  have h02 := hrow 2 (by decide)
  have h11 := congrFun (congrFun hblock 0) 0
  have h12 := congrFun (congrFun hblock 0) 1
  have h21 := congrFun (congrFun hblock 1) 0
  have h22 := congrFun (congrFun hblock 1) 1
  simp only [Matrix.submatrix_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h11 h12 h21 h22
  have he : (e2 : Fin 3 → F) ⬝ᵥ e1 = 0 := by simp [dotProduct, Fin.sum_univ_three]
  have hytv : (y : SL3 F) = tv e1 e2 := by
    refine Subtype.ext ?_
    rw [coe_tv he]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply]
  have he1 : (e1 : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  obtain ⟨g, hg, c, hc, hgc⟩ := htr e1 he1
  have hgv : ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e1 = c⁻¹ • e0 := by
    have : (e1 : Fin 3 → F) = c⁻¹ • ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0) := by
      rw [hgc, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this, Matrix.mulVec_smul, sl_inv_mulVec_mulVec]
  have hQ : g⁻¹ * (y : SL3 F) * g⁻¹⁻¹ ∈ (Q1 : Subgroup (SL3 F)) := by
    rw [hytv, conj_tv, hgv, tv_smul_left]
    exact tv_mem_pointGroup _ _
  have hmem : g⁻¹ * (y : SL3 F) * g⁻¹⁻¹ ∈ W ⊓ P1 ⊓ Q1 :=
    ⟨⟨W.mul_mem (W.mul_mem (W.inv_mem hg) hyW.1) (W.inv_mem (W.inv_mem hg)), Q1_le_P1 hQ⟩, hQ⟩
  rw [hb, Subgroup.mem_bot, conj_eq_one_iff] at hmem
  have h1 : y = 1 := Subtype.ext hmem
  rw [h1, map_one] at hyM
  have := congrFun (congrFun hyM 0) 1
  simp at this

theorem eq_top_of_isLThreeTwo_SL3 [Finite F]
    (hq : Nat.card F % 3 = 2) {W Y : Subgroup (SL3 F)}
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W) (hYW : Y ≤ W)
    (hAY : (A0 : Subgroup (SL3 F)) ≤ Y) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) : W = ⊤ := by
  have hroot := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.sq_add_self_add_one_ne_zero hq
  have hcube := exists_cube hq
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  obtain ⟨y, hy⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.F1Proof.exists_orderOf_three hAY
  rcases le_P1_or_le_P2_or_transitive hroot hcube hlev with h | h | htr
  ·
    exfalso
    by_cases hF : 2 ∣ Nat.card F
    · exact CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.false_of_le_P1_of_isLThreeTwo hF
        (hYW.trans h) hY
    · exact CFSG.LocalAnalysis.RankThreeUC.S15.F1Proof.false_of_le_P1_odd hq hF (hYW.trans h)
        hY hy
  ·
    exfalso
    by_cases hF : 2 ∣ Nat.card F
    · exact CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.false_of_le_P2_of_isLThreeTwo hF
        (hYW.trans h) hY
    · exact CFSG.LocalAnalysis.RankThreeUC.S15.F1Proof.false_of_le_P2_odd hq hF (hYW.trans h)
        hY hy
  ·
    rcases inf_Q1_eq_bot_or_le hroot hcube (Y := W ⊓ P1)
        (fun X hX => ⟨hlev X hX, lev_mem_P1 X⟩) with hb | hle
    · exfalso
      by_cases hF : 2 ∣ Nat.card F
      · exact CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.false_of_transitive_of_isLThreeTwo hF hYW
          htr hb hY
      · have h5 : 5 ≤ Nat.card F := by
          have h1 : 1 < Nat.card F := Finite.one_lt_card
          omega
        obtain ⟨μ, hμ0, hμ6⟩ := exists_pow_six_ne_one hq h5
        have hμ3 : μ ^ 3 ≠ 1 := fun h3 =>
          hμ6 (by rw [show 6 = 3 * 2 by norm_num, pow_mul, h3, one_pow])
        have hNtY : (Nt : Subgroup (GL (Fin 2) F)) ≤ ((W ⊓ P1).subgroupOf P1).map rho1 :=
          fun X hX => ⟨⟨lev X, lev_mem_P1 X⟩,
            Subgroup.mem_subgroupOf.mpr ⟨hNW (lev_mem_normalizer_A0 hX), lev_mem_P1 X⟩, rho1_lev X⟩
        rcases gl2NonsplitMax hq h5 _ hNtY with h | h
        · exact false_of_map_rho1_le_Nt hroot hμ0 hμ6 hlev htr h.le
        · exact false_of_transitive_of_sl2_le hμ0 hμ3 (hlev _ (scalGL_comm μ hμ0)) htr hb h
    · exact eq_top_of_Q1_le_of_transitive htr (hle.trans inf_le_left)

theorem genSeven_of_psl3 {Q : Type} [Group Q] [Finite Q]
    {p f : ℕ} (hq : p ^ f % 3 = 2) (hQ : LieModel Q .PSL 3 p f) {X : Subgroup Q}
    (hX : IsL2Odd (Bar2 X) 7) (hcyc : ∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P) :
    GenSeven Q X := by
  intro W hXW hD _
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hQ.statedClassicalModel (by decide)
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  let e : Q ≃* SL3 K := (eK.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
    (pslEquivSL3 hqK)
  have hcycS : ∀ P : Subgroup (SL3 K), IsPGroup 3 P → IsCyclic P := by
    intro P hP
    have := hcyc _ (hP.map e.symm.toMonoidHom)
    exact isCyclic_of_surjective
      (P.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨D, hDX, hD3⟩ := exists_le_card_eq_three_of_isL2Odd_seven hX
  have hD3' : Nat.card (D.map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hD3]
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.exists_conj_eq_of_card_eq_three hcycS
      hD3' card_A0
  let φ : Q ≃* SL3 K := e.trans (MulAut.conj g)
  have hmap : ∀ R : Subgroup Q,
      R.map φ.toMonoidHom = (R.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := fun R => by
    rw [Subgroup.map_map]
    rfl
  have hA : (A0 : Subgroup (SL3 K)) = D.map φ.toMonoidHom := by rw [hmap]; exact hg
  have hY : IsLThreeTwo (↥(X.map φ.toMonoidHom) ⧸ CFSG.pCore 2 ↥(X.map φ.toMonoidHom)) := by
    obtain ⟨d, hd, ⟨i⟩⟩ := isLThreeTwo_of_isL2Odd_seven hX
    let eX : ↥X ≃* ↥(X.map φ.toMonoidHom) := X.equivMapOfInjective φ.toMonoidHom φ.injective
    have : (CFSG.pCore 2 ↥(X.map φ.toMonoidHom)).Normal := by
      unfold CFSG.pCore
      exact Subgroup.sSup_normal _ fun _ hN => hN.1
    exact ⟨d, hd, ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥(X.map φ.toMonoidHom))
      eX (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eX)).symm.trans i⟩⟩
  have hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 K)) : Set (SL3 K)) ≤ W.map φ.toMonoidHom := by
    rw [hA, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (hD D hDX hD3)
  have htop := eq_top_of_isLThreeTwo_SL3 hqK hNW (Subgroup.map_mono hXW)
    (hA ▸ Subgroup.map_mono hDX) hY
  rw [eq_top_iff]
  intro x _
  obtain ⟨w, hw, hwx⟩ : φ x ∈ W.map φ.toMonoidHom := htop ▸ Subgroup.mem_top _
  rwa [φ.injective hwx] at hw

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
