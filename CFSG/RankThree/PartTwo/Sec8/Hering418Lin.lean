module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Engine
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

theorem exists_bound_of_hom {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : MulAut X →* MulAut Y) (hφ : Function.Injective φ) (N : Subgroup (MulAut Y))
    (hinn : ∀ x : X, φ (MulAut.conj x) ∈ N) (h3 : ∀ σ : MulAut X, σ ^ 3 = 1 → φ σ ∈ N)
    (hN : ∀ F : Subgroup (MulAut Y), IsElemAbelian 3 F → F ≤ N → Nat.card F ≤ 9) :
    ∃ N' : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ N' ∧
      (∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ N') ∧
      ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F → F ≤ N' → Nat.card F ≤ 9 := by
  refine ⟨N.comap φ, ?_, fun σ hσ => h3 σ hσ, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hinn x
  · intro F hF hFN
    have hle : F.map φ ≤ N := by
      rw [Subgroup.map_le_iff_le_comap]
      exact hFN
    have := hN _ (hF.map φ) hle
    rwa [Subgroup.card_map_of_injective hφ] at this

theorem pow_three_mem_linearAutGroup {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h3f : ¬ 3 ∣ f)
    {α : MulAut (projectiveSL 3 K)} (hα : α ^ 3 = 1) : α ∈ linearAutGroup 3 K := by
  by_contra hD
  obtain ⟨σ, hσ, -⟩ := KFacts.linear_order_three_field_descent (n := 3) (le_refl 3) α hα hD
  exact h3f (KFacts.eq_frobenius_pow_of_orderOf_eq_three hp hf hK hσ).1

theorem pow_three_mem_psuConj_range {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : 2 < p ^ f) (h3f : ¬ 3 ∣ 2 * f)
    {α : MulAut (unitaryPSU h 3)} (hα : α ^ 3 = 1) : α ∈ (KFacts.psuConj h).range := by
  have := h.finite
  by_contra hD
  obtain ⟨σ, hσ, -⟩ := KFacts.unitary_order_three_field_descent hq α hα hD
  exact h3f (KFacts.eq_frobenius_pow_of_orderOf_eq_three h.prime (by have := h.one_le; omega)
    h.card hσ).1

section Two


theorem kF418ModelOn_two : KF418ModelOn (fun X _ => Sec4.IsList46Two X) := by
  refine kF418ModelOn_of_bound ?_
  intro X _ _ hX
  obtain ⟨p, e, hpf, hp3, he1, he2, hSL | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ := hX
  · obtain ⟨F, _, _, ⟨hF, ⟨φ⟩⟩ | ⟨hF, ⟨φ⟩⟩⟩ := hSL
    ·
      have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out (by omega) hF
      let e' : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
        φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
      let φ' : MulAut X →* MulAut (projectiveSL 3 F) :=
        (descendAut 3 F).comp (MulAut.congr e').toMonoidHom
      have hφ' : Function.Injective φ' :=
        Sec4.descendAut_three_injective.comp (MulAut.congr e').injective
      refine exists_bound_of_hom φ' hφ' (linearAutGroup 3 F) ?_ ?_ ?_
      · intro x
        simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [KFacts.congr_mulAutConj, KFacts.descendAut_conj]
        exact KFacts.innAut_le_linearAutGroup 3 F ⟨_, rfl⟩
      · intro σ hσ
        exact pow_three_mem_linearAutGroup Fact.out (by omega) hF (by omega)
          (α := φ' σ) (by rw [← map_pow, hσ, map_one])
      · intro F' hF' hFN
        have := Sec4.card_inf_linearAutGroup_three_le h3 hF'
        rwa [inf_eq_left.mpr hFN] at this
    ·
      have hU : UnitaryFieldData p e F := ⟨Fact.out, he1, by rw [hF, ← pow_mul, mul_comm]⟩
      have hq : 2 < p ^ e := by
        calc 2 < p := by omega
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he1
      have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card (p := p) (f := 2 * e) Fact.out
        (by omega) (by rw [hF, ← pow_mul, mul_comm])
      have := hU.finite
      let φ' : MulAut X →* MulAut (unitaryPSU hU 3) :=
        (MulAut.congr (KFacts.suCenterEquiv hU hq)).toMonoidHom.comp
          ((KFacts.centerDescend (unitarySU p e F 3)).comp (MulAut.congr φ).toMonoidHom)
      have hφ' : Function.Injective φ' :=
        (MulAut.congr (KFacts.suCenterEquiv hU hq)).injective.comp
          ((Sec21.Item223CensusProof.centerDescend_injective_unitarySU hU hq).comp
            (MulAut.congr φ).injective)
      refine exists_bound_of_hom φ' hφ' (KFacts.psuConj hU).range ?_ ?_ ?_
      · intro x
        simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [KFacts.congr_mulAutConj, KFacts.centerDescend_conj, KFacts.congr_mulAutConj]
        exact (KFacts.stdPinnedPSU3 hU).inn_le ⟨_, rfl⟩
      · intro σ hσ
        exact pow_three_mem_psuConj_range hq (by omega) (α := φ' σ)
          (by rw [← map_pow, hσ, map_one])
      · intro F' hF' hFN
        exact Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 F' hF' hFN
  ·
    set F := GaloisField p e with hFdef
    have hFcard : Nat.card F = p ^ e := GaloisField.card p e (by omega)
    have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out (by omega) hFcard
    let e' : X ≃* projectiveSL 3 F := φ.trans (Sec4.projSLEquivProjectiveSL 3 F)
    refine exists_bound_of_hom (MulAut.congr e').toMonoidHom (MulAut.congr e').injective
      (linearAutGroup 3 F) ?_ ?_ ?_
    · intro x
      rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
      exact KFacts.innAut_le_linearAutGroup 3 F ⟨e' x, rfl⟩
    · intro σ hσ
      exact pow_three_mem_linearAutGroup Fact.out (by omega) hFcard (by omega)
        (α := MulAut.congr e' σ) (by rw [← map_pow, hσ, map_one])
    · intro F' hF' hFN
      have := Sec4.card_inf_linearAutGroup_three_le h3 hF'
      rwa [inf_eq_left.mpr hFN] at this
  ·
    have hU := Sec4.unitaryFieldData_galoisField p e he1
    have hq : 2 < p ^ e := by
      calc 2 < p := by omega
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he1
    have h3 : (3 : GaloisField p (2 * e)) ≠ 0 :=
      Sec4.three_ne_zero_of_card Fact.out (by omega) (GaloisField.card p (2 * e) (by omega))
    have := hU.finite
    let e' : X ≃* unitaryPSU hU 3 := φ.trans (Sec4.projSUEquivUnitaryPSU p e hU)
    refine exists_bound_of_hom (MulAut.congr e').toMonoidHom (MulAut.congr e').injective
      (KFacts.psuConj hU).range ?_ ?_ ?_
    · intro x
      rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
      exact (KFacts.stdPinnedPSU3 hU).inn_le ⟨e' x, rfl⟩
    · intro σ hσ
      exact pow_three_mem_psuConj_range hq (by omega) (α := MulAut.congr e' σ)
        (by rw [← map_pow, hσ, map_one])
    · intro F' hF' hFN
      exact Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 F' hF' hFN

end Two

end CFSG.RankThree.PartTwo.Sec8.Hering418
