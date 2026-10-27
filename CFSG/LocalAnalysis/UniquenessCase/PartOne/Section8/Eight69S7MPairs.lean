module

public import CFSG.RankThree.Native.HSMcLSmallData
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairsAct
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairsJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open McLPairs in
theorem exists_mcl_five_pair_joins :
    ∃ (R : Subgroup (Equiv.Perm (Fin 275))) (B : Fin 3 → Subgroup (Equiv.Perm (Fin 275))),
      R ≤ CFSG.RankThree.Native.mcl275P ∧ Nat.card R = 125 ∧
      Nat.card ↥(Subgroup.normalizer (R : Set (Equiv.Perm (Fin 275))) ⊓
        CFSG.RankThree.Native.mcl275P) = 3000 ∧
      (∀ k, Nat.card (B k) = 126000) ∧
      (∀ k l, k ≠ l → B k ⊔ B l = CFSG.RankThree.Native.mcl275P) ∧
      ∀ g ∈ CFSG.RankThree.Native.mcl275P, R ⊔ R.map (MulAut.conj g).toMonoidHom = R ∨
        (∃ k, R ⊔ R.map (MulAut.conj g).toMonoidHom = B k) ∨
        R ⊔ R.map (MulAut.conj g).toMonoidHom = CFSG.RankThree.Native.mcl275P := by
  have hR : ∀ c ∈ mclN5, mclR5.map (MulAut.conj c).toMonoidHom = mclR5 := fun c hc =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (mclN5_le_normalizer hc)
  have hmul : ∀ (K : Subgroup (Equiv.Perm (Fin 275))) (x c : Equiv.Perm (Fin 275)),
      K.map (MulAut.conj (x * c)).toMonoidHom =
        (K.map (MulAut.conj c).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro K x c
    ext y
    simp [Subgroup.mem_map, mul_assoc]
  refine ⟨mclR5, mclB5, mclR5_le, card_mclR5, ?_, card_mclB5, fun k l hkl => mclB5_sup hkl, ?_⟩
  · rw [normalizer_inf_mcl275P]
    exact card_mclN5
  intro g hg
  obtain ⟨i, hi, a, ha, b, hb, hab⟩ := mcl_exists_dcoset g⁻¹ (inv_mem hg)
  have hg' : g = b⁻¹ * ((mclRep5 i)⁻¹ * a⁻¹) := by
    rw [← inv_inv g, hab]
    group
  have hjoin : mclR5 ⊔ mclR5.map (MulAut.conj g).toMonoidHom =
      (mclR5 ⊔ mclR5.map (MulAut.conj (mclRep5 i)⁻¹).toMonoidHom).map
        (MulAut.conj b⁻¹).toMonoidHom := by
    rw [Subgroup.map_sup, hR b⁻¹ (inv_mem hb), hg', hmul, hmul, hR a⁻¹ (inv_mem ha)]
  rw [hjoin]
  by_cases h0 : i = 0
  · subst h0
    left
    rw [hR (mclRep5 0)⁻¹ (by rw [mclRep5_zero, inv_one]; exact one_mem _), sup_idem,
      hR b⁻¹ (inv_mem hb)]
  by_cases h95 : i = 95
  · subst h95
    right
    left
    rw [← mclB5_zero]
    exact mclB5_map_conj (inv_mem hb) 0
  right
  right
  rw [mcl_pair_join hi h0 h95]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer (mclN5_le (inv_mem hb)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
