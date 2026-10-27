module

import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelConj
import CFSG.Quasithin.Background.SmithB45Sp4Herm
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelTransport

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) SL(2, F) W}

theorem smul_mem_hermA {l : ℕ} {μ : F} (hμ : μ ^ 2 ^ l = μ)
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA l F) :
    μ • X ∈ hermA l F := by
  rw [mem_hermA] at hX ⊢
  rw [CFSG.Quasithin.B45Sp4.frobPow_smul', hμ, Matrix.transpose_smul, hX]

@[expose] def smulA (μ : ↥(frobFixField l F)) :
    ↥(hermA l F) →+ ↥(hermA l F) where
  toFun X :=
    ⟨(μ : F) • (X : Matrix (Fin 2) (Fin 2) F),
      smul_mem_hermA (l := l) μ.2 X.2⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' X Y := by
    apply Subtype.ext
    simp [add_smul]

@[simp] theorem smulA_coe (μ : ↥(frobFixField l F)) (X : ↥(hermA l F)) :
    ((smulA (l := l) μ X : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) =
      (μ : F) • (X : Matrix (Fin 2) (Fin 2) F) := rfl

theorem hermAct_smulA (μ : ↥(frobFixField l F)) (g : SL(2, F)) (X : ↥(hermA l F)) :
    hermAct l (sig_sig hF) g (smulA (l := l) μ X) =
      smulA (l := l) μ (hermAct l (sig_sig hF) g X) := by
  apply Subtype.ext
  calc ((hermAct l (sig_sig hF) g (smulA (l := l) μ X) : ↥(hermA l F)) :
        Matrix (Fin 2) (Fin 2) F)
      = CFSG.Quasithin.B45Sp4.tw l (g : Matrix (Fin 2) (Fin 2) F)
          ((μ : F) • (X : Matrix (Fin 2) (Fin 2) F)) := by
        rw [hermAct_coe, smulA_coe, CFSG.Quasithin.B45Sp4.tw_apply]
    _ = (μ : F) • CFSG.Quasithin.B45Sp4.tw l (g : Matrix (Fin 2) (Fin 2) F)
          (X : Matrix (Fin 2) (Fin 2) F) :=
        CFSG.Quasithin.B45Sp4.tw_smul l (g : Matrix (Fin 2) (Fin 2) F)
          (X : Matrix (Fin 2) (Fin 2) F) (μ : F)
    _ = ((smulA (l := l) μ (hermAct l (sig_sig hF) g X) : ↥(hermA l F)) :
          Matrix (Fin 2) (Fin 2) F) := by
        rw [smulA_coe, hermAct_coe, CFSG.Quasithin.B45Sp4.tw_apply]

theorem IsOrthModule.exists_scalars (hρ : IsOrthModule hF ρ) :
    ∃ 𝔰 : Set (W →+ W), (∀ s ∈ 𝔰, ∀ g w, s (ρ g w) = ρ g (s w)) ∧
      ∀ A : Subgroup SL(2, F), (∀ a ∈ A, a * a = 1) → Nat.card A = 2 ^ (2 * l) →
        ∀ w ∈ fixedSub ρ A, ∀ w' ∈ fixedSub ρ A, w ≠ 0 → w' ≠ 0 → ∃ s ∈ 𝔰, s w = w' := by
  obtain ⟨j, β, hβ⟩ := hρ
  refine ⟨Set.range fun μ : ↥(frobFixField l F) =>
    β.symm.toAddMonoidHom.comp ((smulA (l := l) μ).comp β.toAddMonoidHom), ?_, ?_⟩
  · rintro s ⟨μ, rfl⟩ g w
    apply β.injective
    change β (β.symm (smulA (l := l) μ (β (ρ g w)))) =
      β ((ρ g) (β.symm (smulA (l := l) μ (β w))))
    rw [AddEquiv.apply_symm_apply, hβ, hβ, AddEquiv.apply_symm_apply]
    exact (hermAct_smulA (hF := hF) μ (fieldAut F j g) (β w)).symm
  · intro A hA2 hA w hw w' hw' hw0 hw'0
    have hs := fieldAut_image_sylow A hA2 hA j
    have hAeq : Nat.card (A.map (fieldAut F j)) = Nat.card F := by
      rw [hs.2, Nat.card_eq_fintype_card, hF]
    obtain ⟨x, hx⟩ := eq_conj_rootGroup (A.map (fieldAut F j)) hs.1 hAeq
    have hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom :=
      eq_map_conj_upperSylow_of_forall_mem_iff hx
    have hβw : β w ∈ fixedSub (hermRep l hF) (A.map (fieldAut F j)) :=
      (fixedSub_fieldAut_mem (hF := hF) (j := j) hβ A w).mp hw
    have hβw' : β w' ∈ fixedSub (hermRep l hF) (A.map (fieldAut F j)) :=
      (fixedSub_fieldAut_mem (hF := hF) (j := j) hβ A w').mp hw'
    rw [hEq, fixedSub_map_conj] at hβw hβw'
    obtain ⟨v, hv, hvx⟩ := hβw
    obtain ⟨v', hv', hv'x⟩ := hβw'
    rw [fixedSub_upperSylow] at hv hv'
    obtain ⟨hv11, hv01⟩ := hv
    obtain ⟨hv'11, hv'01⟩ := hv'
    have hv10 : (v : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [hermA_10 (a := l) v, hv01]
      simp
    have hv'10 : (v' : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [hermA_10 (a := l) v', hv'01]
      simp
    have hv0 : v ≠ 0 := by
      intro h
      exact hw0 (β.injective (by rw [← hvx, h, map_zero, map_zero]))
    have hv'0 : v' ≠ 0 := by
      intro h
      exact hw'0 (β.injective (by rw [← hv'x, h, map_zero, map_zero]))
    have ha0 : (v : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h
      exact hv0 (Subtype.ext (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h, hv11, hv01, hv10]))
    have hb0 : (v' : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h
      exact hv'0 (Subtype.ext (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h, hv'11, hv'01, hv'10]))
    have ha : ((v : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 ^ l =
        (v : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      simpa [sig_apply] using hermA_00 (a := l) v
    have hb : ((v' : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 ^ l =
        (v' : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      simpa [sig_apply] using hermA_00 (a := l) v'
    let μ : ↥(frobFixField l F) :=
      ⟨(v' : Matrix (Fin 2) (Fin 2) F) 0 0 / (v : Matrix (Fin 2) (Fin 2) F) 0 0,
        by rw [mem_frobFixField, div_pow, hb, ha]⟩
    have hμv : smulA (l := l) μ v = v' := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [smulA_coe, Matrix.smul_apply, hv11, hv01, hv'11, hv'01, hv10, hv'10,
          μ, div_mul_cancel₀ _ ha0]
    refine ⟨β.symm.toAddMonoidHom.comp ((smulA (l := l) μ).comp β.toAddMonoidHom),
      ?_, ?_⟩
    · exact ⟨μ, rfl⟩
    calc β.symm (smulA (l := l) μ (β w))
        = β.symm (smulA (l := l) μ (hermRep l hF x v)) := by rw [hvx]
      _ = β.symm (hermRep l hF x (smulA (l := l) μ v)) := by
          rw [hermRep_apply, ← hermAct_smulA (hF := hF), hermRep_apply]
      _ = β.symm (hermRep l hF x v') := by rw [hμv]
      _ = β.symm (β w') := by rw [hv'x]
      _ = w' := β.symm_apply_apply w'

end CFSG.RankThree.GF2n.Tim81.Sec2
