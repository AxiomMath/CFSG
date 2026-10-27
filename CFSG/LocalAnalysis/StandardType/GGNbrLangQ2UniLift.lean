module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClUni
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniTypeDet
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

@[expose] def Q2UnitaryLift {P : Type} [Group P] (M : Subgroup (MulAut P)) : Prop :=
  ∃ (a m : ℕ) (D : Type) (_ : Field D) (hD : UnitaryFieldData 2 m D)
    (ψ : P ≃* LargeEvenProj (LargeEvenSUGroup (Fin a) D (2 ^ m)))
    (G : Subgroup ↥(TableB.unitGroup (ι := Fin a) hD.bar)), IsMulCommutative G ∧
    ∀ α ∈ M, ∃ g ∈ G, MulAut.congr ψ α = CFSG.HardMathSupport.C14Cl.uniConj hD a g

theorem q2_commutative_of_unitaryLift {P : Type} [Group P] {M : Subgroup (MulAut P)}
    (h : Q2UnitaryLift M) {d m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E)
    (hd : 3 ≤ d) (hdm : ¬ (d = 3 ∧ m = 1))
    (θ : P ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :
    IsMulCommutative ((M.map (MulAut.congr θ).toMonoidHom).comap
      (CFSG.HardMathSupport.C14Cl.uniConj hE d)) := by
  obtain ⟨a, mD, D, hDf, hD, ψL, G, hG, hlift⟩ := h
  letI : Field D := hDf
  haveI : Finite E := hE.finite
  haveI : Finite D := hD.finite
  have hcardE : Nat.card E = (2 ^ m) ^ 2 := by rw [hE.card, ← pow_mul, mul_comm]
  have hdq : ¬ (d = 3 ∧ 2 ^ m = 2) := fun ⟨h3, h2⟩ =>
    hdm ⟨h3, Nat.pow_right_injective (le_refl 2) (h2.trans (by norm_num : (2 : ℕ) = 2 ^ 1))⟩
  obtain ⟨ha, hmD⟩ := kgLangS1A_psu_typeDet (d := d) (d₁ := a) (m₀ := m) (m := mD)
    (F₀ := E) (E := D) hd hE.one_le hcardE hdq hD (θ.symm.trans ψL)
  subst a
  subst mD
  have hcardD : Nat.card D = (2 ^ m) ^ 2 := by rw [hD.card, ← pow_mul, mul_comm]
  let Ψ : LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) D (2 ^ m)) := θ.symm.trans ψL
  have hΨconj : ∀ (x : ↥(TableB.unitGroup (ι := Fin d) hE.bar))
      (x' : ↥(TableB.unitGroup (ι := Fin d) hD.bar)) (α : MulAut P),
      MulAut.congr θ α = CFSG.HardMathSupport.C14Cl.uniConj hE d x →
      MulAut.congr ψL α = CFSG.HardMathSupport.C14Cl.uniConj hD d x' →
      ∀ w, Ψ (TableB.projConj (LargeEvenSUGroup (Fin d) E (2 ^ m))
          (Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hE) x) w) =
        TableB.projConj (LargeEvenSUGroup (Fin d) D (2 ^ m))
          (Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hD) x') (Ψ w) := by
    intro x x' α hx hx' w
    have h1 : (CFSG.HardMathSupport.C14Cl.uniConj hE d x) w = θ (α (θ.symm w)) := by
      rw [← hx]
      rfl
    have h2 : (CFSG.HardMathSupport.C14Cl.uniConj hD d x') (ψL (θ.symm w)) =
        ψL (α (θ.symm w)) := by
      rw [← hx']
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change Ψ ((CFSG.HardMathSupport.C14Cl.uniConj hE d x) w) =
      (CFSG.HardMathSupport.C14Cl.uniConj hD d x') (Ψ w)
    rw [h1]
    simp only [Ψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact h2.symm
  rw [isMulCommutative_iff]
  intro x y
  obtain ⟨α, hαM, hαeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp x.2)
  obtain ⟨β, hβM, hβeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp y.2)
  obtain ⟨x', hx'G, hx'eq⟩ := hlift α hαM
  obtain ⟨y', hy'G, hy'eq⟩ := hlift β hβM
  have hαeq' : MulAut.congr θ α = CFSG.HardMathSupport.C14Cl.uniConj hE d x.1 := hαeq
  have hβeq' : MulAut.congr θ β = CFSG.HardMathSupport.C14Cl.uniConj hE d y.1 := hβeq
  have hgh : (x' : GL (Fin d) D) * y' = y' * x' := by
    have hcomm := (isMulCommutative_iff.mp hG) ⟨x', hx'G⟩ ⟨y', hy'G⟩
    simpa using congrArg (fun t : G => ((t : ↥(TableB.unitGroup (ι := Fin d) hD.bar)) :
      GL (Fin d) D)) hcomm
  have htransfer := kgLangS1A_uni_commute_transfer (d := d) (m := m) (F₀ := E) (E := D) hd
    hE.one_le hcardE hcardD hdq Ψ
    (hΨconj x.1 x' α hαeq' hx'eq) (hΨconj y.1 y' β hβeq' hy'eq) hgh
  exact Subtype.ext (Subtype.ext htransfer)

end CFSG.StandardType
