module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FA
public import CFSG.Quasithin.Vol2.Ch3Sec3WLn2C
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318E

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace FData

variable {T M L D : Subgroup G} {α : ↥L →* SL4}

theorem msPair_caseW (hD : FData G T M L D α) (hC34 : CFSG.Quasithin.C134L32CorrM)
    {Y : Subgroup G} (hY : Y ∈ lFamilyOf L T) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    {ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)} (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = CFSG.pCore 2 ↥Y) (hbot : pCoreOf 2 (Y ⊔ T ⊔ D) = ⊥) :
    IsMSPair (Y ⊔ T) T ∧ ∃ j : ℕ, CFSG.Quasithin.IsC134CaseM j (Y ⊔ T) T Y := by
  set α₂ := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom.comp ψ with hα₂
  have hα₂s : Function.Surjective α₂ := by
    rw [hα₂, MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hψs
  have hα₂k : α₂.ker = CFSG.pCore 2 ↥Y := by
    rw [hα₂, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hψk]
  have hMS : IsMSPair (Y ⊔ T) T :=
    (Ln2.isMSPair_or hD.hyp hY hTY hα₂s hα₂k).resolve_right fun h => h hbot
  exact ⟨hMS, Ln2.exists_isC134CaseW hC34 hMS (cComp_of_isLocal hY.2) hTY hα₂s hα₂k⟩

theorem exists_caseW (hD : FData G T M L D α) (h15 : Step3_3_15R)
    (hC34 : CFSG.Quasithin.C134L32CorrM) :
    ∃ i : ℕ, (i = 1 ∨ i = 3) ∧ pCoreOf 2 (liftCore α (FLc.QI 4 {i}) ⊔ T ⊔ D) = ⊥ ∧
      IsMSPair (liftCore α (FLc.QI 4 {i}) ⊔ T) T ∧
      ∃ j : ℕ, CFSG.Quasithin.IsC134CaseM j (liftCore α (FLc.QI 4 {i}) ⊔ T) T
        (liftCore α (FLc.QI 4 {i})) := by
  obtain ⟨ψ₁, hψ₁s, hψ₁k, -⟩ := hD.exists_levi_one
  obtain ⟨ψ₃, hψ₃s, hψ₃k, -⟩ := hD.exists_levi_three
  have ht₁ : L3312.Type3312R (↥(liftCore α (FLc.QI 4 {1})) ⧸
      CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {1}))) :=
    Or.inr (Or.inl (L3318.isPSL_of_hom le_rfl hψ₁s hψ₁k))
  have ht₃ : L3312.Type3312R (↥(liftCore α (FLc.QI 4 {3})) ⧸
      CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {3}))) :=
    Or.inr (Or.inl (L3318.isPSL_of_hom le_rfl hψ₃s hψ₃k))
  by_cases h₁ : pCoreOf 2 (liftCore α (FLc.QI 4 {1}) ⊔ T ⊔ D) = ⊥
  · exact ⟨1, Or.inl rfl, h₁, hD.msPair_caseW hC34 hD.mem_lFamilyOf_one (hD.le_normalizer_Y {1})
      hψ₁s hψ₁k h₁⟩
  by_cases h₃ : pCoreOf 2 (liftCore α (FLc.QI 4 {3}) ⊔ T ⊔ D) = ⊥
  · exact ⟨3, Or.inr rfl, h₃, hD.msPair_caseW hC34 hD.mem_lFamilyOf_three
      (hD.le_normalizer_Y {3}) hψ₃s hψ₃k h₃⟩
  exfalso
  obtain ⟨Y, hY, -, hpsl, -⟩ := h15 G T M L D _ _ hD.hyp hD.mem_lFamilyOf_one
    hD.mem_lFamilyOf_three hD.sup_eq h₁ h₃ ht₁ ht₃
  rcases hY with rfl | rfl
  · exact L3318.not_isPSL_two_two le_rfl (by norm_num) hψ₁s hψ₁k hpsl
  · exact L3318.not_isPSL_two_two le_rfl (by norm_num) hψ₃s hψ₃k hpsl


end FData

end CFSG.Quasithin.H13.L3321
