module

public import CFSG.LocalAnalysis.StandardType.PhanEResS2cA2A1Model
public import CFSG.LocalAnalysis.StandardType.PhanEFlagNormalX
public import CFSG.LocalAnalysis.StandardType.PhanEResOrbit

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.Phan.PhanE.Flag

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

private theorem pls2a_isCut_013 : IsCut 3 [0, 1, 3] where
  head := by decide
  last := by decide
  strict := by
    intro i hi
    have hi3 : i + 1 < 3 := by simpa using hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl <;> decide

private theorem pls2a_isCut_02 : IsCut 2 [0, 2] where
  head := by decide
  last := by decide
  strict := by
    intro i hi
    have hi2 : i + 1 < 2 := by simpa using hi
    have hi' : i = 0 := by omega
    subst hi'
    decide

private theorem pls2a_cutTypes_013 : cutTypes 2 [0, 1, 3] = {1} := by
  ext j
  fin_cases j <;> simp [cutTypes] <;> decide

private theorem pls2a_blockSL_le_range
    (β : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K)
    (hβ : ∀ B : SpecialLinearGroup (Fin 2) K,
      ((β B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        emb21 (B : Matrix (Fin 2) (Fin 2) K)) :
    blockSL K 2 [0, 1, 3] ≤ β.range := by
  rw [blockSL]
  apply (Subgroup.closure_le _).mpr
  rintro A ⟨k, hk, c, hA⟩
  rw [pls2a_cutTypes_013] at hk
  simp only [Set.mem_singleton_iff] at hk
  subst hk
  rcases hA with rfl | rfl
  · refine ⟨CFSG.LieType.Steinberg.CentralExt.SLClosed.tv K 0 1 c, ?_⟩
    apply Subtype.ext
    rw [hβ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [emb21, SpecialLinearGroup.transvection_coe, Matrix.transvection,
        CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (by decide : (0:Fin 2) ≠ 1) c,
        CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (by decide : (1:Fin 3) ≠ 2) c]
  · refine ⟨CFSG.LieType.Steinberg.CentralExt.SLClosed.tv K 1 0 c, ?_⟩
    apply Subtype.ext
    rw [hβ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [emb21, SpecialLinearGroup.transvection_coe, Matrix.transvection,
        CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (by decide : (1:Fin 2) ≠ 0) c,
        CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (by decide : (2:Fin 3) ≠ 1) c]

private theorem pls2a_flagAct_mem_refSet_iff {n : ℕ} {d : List ℕ} {g : GL (Fin n) K}
    (hg : StabV n d g) (x : FlagK K n) :
    flagAct g x ∈ refSet K n d ↔ x ∈ refSet K n d := by
  constructor
  · intro hx
    have h := StabV.flagAct_mem_refSet (StabV.inv hg) hx
    rwa [flagAct_inv_flagAct] at h
  · exact StabV.flagAct_mem_refSet hg

private theorem pls2a_kapMat_false_one {m : ℕ} (B : SpecialLinearGroup (Fin (m + 1)) K) :
    kapMat (sg K f : K →+* K) false (1 : SpecialLinearGroup (Fin (m + 1)) K) B =
      SpecialLinearGroup.map (sg K f) B := by
  simp [kapMat]

private theorem pls2a_key_identity {I C : Type} (X : ChamberSystem I C)
    (hK : Nat.card K = (2 ^ f) ^ 2) (S : Set C) (ψ : C → C)
    (Θ₀ : ChamberIso X ((flagSys K 2).prod (flagSys K 1))) (N₁ : GL (Fin 3) K)
    (N₂ : GL (Fin 2) K)
    (hS : ∀ c, c ∈ S ↔ (Θ₀.Φ c).1 ∈ refSet K 3 [0, 1, 3])
    (β : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K)
    (hβ : ∀ B : SpecialLinearGroup (Fin 2) K,
      ((β B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        emb21 (B : Matrix (Fin 2) (Fin 2) K))
    (P₁ P₂ : SpecialLinearGroup (Fin 2) K) (hP₁ : P₁ = 1) (hP₂ : P₂ = 1)
    (hψ : ∀ B₁ B₂ : SpecialLinearGroup (Fin 2) K, ∀ c ∈ S,
      Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL (β B₁)) (stdFlag K 3),
        flagAct (SpecialLinearGroup.toGL B₂) (stdFlag K 2)) →
        Θ₀.Φ (ψ c) =
          (flagAct N₁ (flagAct
              (SpecialLinearGroup.toGL (β (kapMat (sg K f : K →+* K) false P₂ B₂)))
              (stdFlag K 3)),
            flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false P₁ B₁))
              (stdFlag K 2)))) :
    ∀ c ∈ S, Θ₀.Φ (ψ c) = (flagAct N₁ (psiA2A1 hK (Θ₀.Φ c)).1,
      flagAct N₂ (psiA2A1 hK (Θ₀.Φ c)).2) := by
  intro c hc
  obtain ⟨A₁, hA₁, hA₁x⟩ := exists_blockSL_of_mem_refSet (K := K) (m := 2) (d := [0, 1, 3])
    pls2a_isCut_013 ((hS c).mp hc)
  obtain ⟨B₁, hB₁⟩ := pls2a_blockSL_le_range β hβ hA₁
  have hA₂x : (Θ₀.Φ c).2 ∈ refSet K 2 [0, 2] := by
    intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i
    · change (Θ₀.Φ c).2.E 0 = Vsub 2 0
      rw [FlagK.E_zero, Vsub_zero]
    · change (Θ₀.Φ c).2.E 2 = Vsub 2 2
      rw [(Θ₀.Φ c).2.top 2 (by norm_num), Vsub_self]
  obtain ⟨A₂, hA₂, hA₂x⟩ := exists_blockSL_of_mem_refSet (K := K) (m := 1) (d := [0, 2])
    pls2a_isCut_02 hA₂x
  have hc_form : Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL (β B₁)) (stdFlag K 3),
      flagAct (SpecialLinearGroup.toGL A₂) (stdFlag K 2)) := by
    apply Prod.ext
    · rw [hA₁x, ← hB₁]
    · rw [hA₂x]
  have hψc := hψ B₁ A₂ c hc hc_form
  have hpsi : psiA2A1 hK (flagAct (SpecialLinearGroup.toGL (β B₁)) (stdFlag K 3),
      flagAct (SpecialLinearGroup.toGL A₂) (stdFlag K 2)) =
      (flagAct (SpecialLinearGroup.toGL (β (SpecialLinearGroup.map (sg K f) A₂))) (stdFlag K 3),
       flagAct (SpecialLinearGroup.toGL (SpecialLinearGroup.map (sg K f) B₁)) (stdFlag K 2)) := by
    have h := psiA2A1_flagAct hK
      (SpecialLinearGroup.toGL B₁) (SpecialLinearGroup.toGL A₂)
      (SpecialLinearGroup.toGL (β B₁))
      (SpecialLinearGroup.toGL (β (SpecialLinearGroup.map (sg K f) A₂)))
      (SpecialLinearGroup.toGL (SpecialLinearGroup.map (sg K f) B₁))
      ?_ ?_ ?_ pls2a_stdFlag_3_mem (c := (stdFlag K 3, stdFlag K 2))
    · simpa [psiA2A1_stdFlag hK] using h
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hβ,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hβ,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hpsi' : psiA2A1 hK (Θ₀.Φ c) =
      (flagAct (SpecialLinearGroup.toGL (β (SpecialLinearGroup.map (sg K f) A₂))) (stdFlag K 3),
       flagAct (SpecialLinearGroup.toGL (SpecialLinearGroup.map (sg K f) B₁)) (stdFlag K 2)) := by
    rw [hc_form]
    exact hpsi
  rw [hP₂] at hψc
  rw [hP₁] at hψc
  rw [pls2a_kapMat_false_one (m := 1) (B := A₂)] at hψc
  rw [pls2a_kapMat_false_one (m := 1) (B := B₁)] at hψc
  rw [hψc, hpsi']

theorem exists_chart_exchA2A1 {I C : Type} (X : ChamberSystem I C)
    (hK : Nat.card K = (2 ^ f) ^ 2) (S : Set C) (ψ : C → C)
    (Θ₀ : ChamberIso X ((flagSys K 2).prod (flagSys K 1))) (N₁ : GL (Fin 3) K)
    (N₂ : GL (Fin 2) K) (hN₁ : StabV 3 [0, 1, 3] N₁)
    (hS : ∀ c, c ∈ S ↔ (Θ₀.Φ c).1 ∈ refSet K 3 [0, 1, 3])
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c)
    (β : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K)
    (hβ : ∀ B : SpecialLinearGroup (Fin 2) K,
      ((β B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        emb21 (B : Matrix (Fin 2) (Fin 2) K))
    (P₁ P₂ : SpecialLinearGroup (Fin 2) K) (hP₁ : P₁ = 1) (hP₂ : P₂ = 1)
    (hψ : ∀ B₁ B₂ : SpecialLinearGroup (Fin 2) K, ∀ c ∈ S,
      Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL (β B₁)) (stdFlag K 3),
        flagAct (SpecialLinearGroup.toGL B₂) (stdFlag K 2)) →
        Θ₀.Φ (ψ c) =
          (flagAct N₁ (flagAct
              (SpecialLinearGroup.toGL (β (kapMat (sg K f : K →+* K) false P₂ B₂)))
              (stdFlag K 3)),
            flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false P₁ B₁))
              (stdFlag K 2)))) :
    ∃ Θ : ChamberIso X ((flagSys K 2).prod (flagSys K 1)),
      (∀ c, c ∈ S ↔ Θ.Φ c ∈ {c : FlagK K 3 × FlagK K 2 | c.1 ∈ refSet K 3 [0, 1, 3]}) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) = psiA2A1 hK (Θ.Φ c) := by
  have hinv : ∀ c : FlagK K 3 × FlagK K 2, c.1 ∈ refSet K 3 [0, 1, 3] →
      (flagAct N₁ (psiA2A1 hK (flagAct N₁ (psiA2A1 hK c).1, flagAct N₂ (psiA2A1 hK c).2)).1,
        flagAct N₂ (psiA2A1 hK (flagAct N₁ (psiA2A1 hK c).1,
          flagAct N₂ (psiA2A1 hK c).2)).2) = c := by
    intro c hc
    let c' := Θ₀.Φ.symm c
    have hΦc' : Θ₀.Φ c' = c := Θ₀.Φ.apply_symm_apply c
    have hc'S : c' ∈ S := (hS c').mpr (by rw [hΦc']; exact hc)
    have hkey1 := pls2a_key_identity X hK S ψ Θ₀ N₁ N₂ hS β hβ P₁ P₂ hP₁ hP₂ hψ c' hc'S
    rw [hΦc'] at hkey1
    have hψc'S : ψ c' ∈ S := hψS c' hc'S
    have hkey2 := pls2a_key_identity X hK S ψ Θ₀ N₁ N₂ hS β hβ P₁ P₂ hP₁ hP₂ hψ (ψ c') hψc'S
    rw [hψψ c' hc'S, hkey1] at hkey2
    rw [hΦc'] at hkey2
    exact hkey2.symm
  obtain ⟨e₁, e₂, he₁, heq⟩ := exists_normalForm_psiA2A1 hK hN₁ N₂ hinv
  let Θ : ChamberIso X ((flagSys K 2).prod (flagSys K 1)) :=
    Θ₀.trans (ChamberIso.prodCongr (flagMapIso (glLin e₁)) (flagMapIso (glLin e₂)))
  refine ⟨Θ, ?_, ?_⟩
  · intro c
    have hΘ : Θ.Φ c = (flagAct e₁ (Θ₀.Φ c).1, flagAct e₂ (Θ₀.Φ c).2) := by
      change (Θ₀.trans (ChamberIso.prodCongr (flagMapIso (glLin e₁))
        (flagMapIso (glLin e₂)))).Φ c = _
      rw [ChamberIso.trans_Φ_apply, ChamberIso.prodCongr_Φ_apply]
      rfl
    rw [hS c, hΘ]
    change (Θ₀.Φ c).1 ∈ refSet K 3 [0, 1, 3] ↔
      flagAct e₁ (Θ₀.Φ c).1 ∈ refSet K 3 [0, 1, 3]
    exact (pls2a_flagAct_mem_refSet_iff he₁ (Θ₀.Φ c).1).symm
  · intro c hc
    have hcS : c ∈ S := hc
    have hkey := pls2a_key_identity X hK S ψ Θ₀ N₁ N₂ hS β hβ P₁ P₂ hP₁ hP₂ hψ c hcS
    have hΘc : Θ.Φ c = (flagAct e₁ (Θ₀.Φ c).1, flagAct e₂ (Θ₀.Φ c).2) := by
      change (Θ₀.trans (ChamberIso.prodCongr (flagMapIso (glLin e₁))
        (flagMapIso (glLin e₂)))).Φ c = _
      rw [ChamberIso.trans_Φ_apply, ChamberIso.prodCongr_Φ_apply]
      rfl
    have hΘψc : Θ.Φ (ψ c) = (flagAct e₁ (Θ₀.Φ (ψ c)).1, flagAct e₂ (Θ₀.Φ (ψ c)).2) := by
      change (Θ₀.trans (ChamberIso.prodCongr (flagMapIso (glLin e₁))
        (flagMapIso (glLin e₂)))).Φ (ψ c) = _
      rw [ChamberIso.trans_Φ_apply, ChamberIso.prodCongr_Φ_apply]
      rfl
    have hmem : flagAct e₁ (Θ₀.Φ c).1 ∈ refSet K 3 [0, 1, 3] :=
      StabV.flagAct_mem_refSet he₁ ((hS c).mp hc)
    have heqc := heq (flagAct e₁ (Θ₀.Φ c).1, flagAct e₂ (Θ₀.Φ c).2) hmem
    simp only [flagAct_inv_flagAct] at heqc
    rw [hΘψc, hkey, hΘc]
    simpa using heqc

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
