module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionTwF4Comp

private theorem tf_pow_two_odd_ne {a c : ℕ} (ha : 1 ≤ a) (h : 2 ^ (2 * a + 1) = c)
    (hc : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 9) : False := by
  have hx : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by
    have h2 : 2 ^ (2 * a) = 4 ^ a := by
      rw [pow_mul]
      norm_num
    rw [pow_add, pow_one, h2, mul_comm]
  have h4 : 4 ≤ 4 ^ a := by
    calc (4 : ℕ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem tf_fieldSize_ne {a : ℕ} (ha : 1 ≤ a) {c : ℕ}
    (h : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize
      (TauCeti.LieTypeIndex.reeF4 a) = c)
    (hc : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 9) : False :=
  tf_pow_two_odd_ne ha (show 2 ^ (2 * a + 1) = c from h) hc

theorem ggTorsion_twF4_compField
    {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {δ : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))} (hδ1 : δ ≠ 1) (hδp : δ ^ p = 1)
    (hδ : δ ∈ (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H a K) →*
      MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))).range)
    {J : Subgroup (LargeEvenCenterQuot (LargeEvenTwF4H a K))}
    (hJ : IsComponentOf J (ggAutFixedSubgroup δ)) :
    ∃ (m : ℕ) (lab : LargeEvenLabel), 1 ≤ m ∧ LargeEvenInLambda2 lab ∧ markChar lab = 2 ∧
      markDeg lab = (2 * a + 1) * m ∧ GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
  classical
  haveI : CharP K 2 := CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow hK
  have hv : (TauCeti.LieTypeIndex.reeF4 a).Valid :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_valid ha
  have hcomp : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CompIdxAt p (.reeF4 a)
      (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
    obtain ⟨e₁⟩ := centerQuot_twF4H_equiv (K := K) a
    have hhalf : (TauCeti.ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent = a :=
      TauCeti.SuzukiReeIndex.halfExponent_reeF4 a hv
    have hcard : Nat.card K =
        2 ^ (2 * (TauCeti.ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent + 1) := by
      rw [hhalf, hK]
    obtain ⟨e₂⟩ := CFSG.TauCetiBridge.reeF4_candidate_equiv_of_card
      (TauCeti.ReeF4LieIndex.of a hv) hcard
    rw [hhalf] at e₂
    have eR : LargeEvenCenterQuot (LargeEvenTwF4H a K) ≃*
        (TauCeti.CFSGIndex.lie ⟨.reeF4 a, hv⟩).Group :=
      e₁.trans ((CFSG.TauCetiBridge.ReeF4.nativeModelEquiv a).trans e₂.symm)
    exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compIdxAt_of_mulEquiv eR.symm
      (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compIdxAt_cat_reeF4 a hv hp hp2)
  have hδmem : δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (LargeEvenCenterQuot (LargeEvenTwF4H a K)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ hδ
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ = ggAutFixedSubgroup δ :=
    Subgroup.ext fun _ => Iff.rfl
  have hJopen : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ) := by
    rw [hfix]
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hJ
  obtain ⟨i, ⟨φ⟩, hrel⟩ := hcomp δ hδmem hδp hδ1 J hJopen
  cases i with
  | lie e =>
    dsimp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRelC] at hrel
    rcases hrel with ⟨hch, ⟨j, hj, hfj⟩, _⟩ | ⟨h2, _⟩ | ⟨h3, _⟩
    ·
      have he2 : e.1.characteristic = 2 :=
        hch.trans (TauCeti.LieTypeIndex.characteristic_reeF4 a)
      obtain ⟨t, n, f, hm, hf, _⟩ :=
        exists_lieModel_two_fieldSize_not_suzRee (S := ↥J ⧸ Subgroup.center ↥J) e he2 φ
      have hq : CFSG.Open.IsQuasisimple ↥J := hJopen.2.2
      have hZ : Subgroup.center (↥J ⧸ Subgroup.center ↥J) = ⊥ :=
        CFSG.HardMathSupport.Timmesfeld.SporadicRank.center_quotient_center_eq_bot hq
      obtain ⟨lab, hlab, _, _, hchar, hdeg, hraw⟩ :=
        exists_label_rawDatum_of_lieModel hZ hm
      have hf_eq : f = (2 * a + 1) * j := by
        apply Nat.pow_right_injective (le_refl 2)
        change 2 ^ f = 2 ^ ((2 * a + 1) * j)
        rw [← hf, hfj,
          show CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize
            (TauCeti.LieTypeIndex.reeF4 a) = 2 ^ (2 * a + 1) from rfl]
        rw [pow_mul]
      exact ⟨j, lab, hj, hlab, hchar, hdeg.trans hf_eq, hraw⟩
    · exact (tf_fieldSize_ne ha h2 (Or.inl rfl)).elim
    · exact (tf_fieldSize_ne ha h3 (Or.inr (Or.inl rfl))).elim
  | alternating n _ =>
    dsimp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRelC] at hrel
    rcases hrel with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · rcases h with h | h | h
      · exact (tf_fieldSize_ne ha h (Or.inl rfl)).elim
      · exact (tf_fieldSize_ne ha h (Or.inr (Or.inr (Or.inl rfl)))).elim
      · exact (tf_fieldSize_ne ha h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).elim
    · rcases h with h | h | h
      · exact (tf_fieldSize_ne ha h (Or.inl rfl)).elim
      · exact (tf_fieldSize_ne ha h (Or.inr (Or.inl rfl))).elim
      · exact (tf_fieldSize_ne ha h (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).elim
    · exact (tf_fieldSize_ne ha h (Or.inl rfl)).elim
  | _ => exact hrel.elim

end TorsionTwF4Comp

end CFSG.StandardType
