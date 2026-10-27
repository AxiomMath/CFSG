module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNst
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGThm
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGTrans

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem holds5 : Holds (hypPSU h 2 1) 2 := by
  have := h.finite
  have := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  have hKc : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have e := hypPSUEquivStatedProj h hR (by norm_num)
  have : Finite (StatedProj (StatedSU (2 * 2 + 1) (2 ^ f) K)) := Finite.of_equiv _ e.toEquiv
  exact Holds.of_mulEquiv e.symm (holds_statedProj_statedSU hKc (2 * 2 + 1))

include h in
theorem agY5 {D : Subgroup (hypPSU h 2 1)} (hD : IsAGMember (hypProjUnitriangular h 2 1) D) :
    Subgroup.normalizer (D : Set (hypPSU h 2 1)) ≤ u5PtP h ∨
      Subgroup.normalizer (D : Set (hypPSU h 2 1)) ≤ u5LnP h := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have := isSimpleGroup_hypPSU_five h
  have hY := u5_yamStd (h := h)
  have hBT : AG.BorelTitsIn (⊤ : Subgroup (hypPSU h 2 1)) := by
    have := AG.borelTitsIn_of_holds (MonoidHom.id (hypPSU h 2 1)) Function.injective_id
      (holds5 h)
    rwa [MonoidHom.range_eq_top.2 Function.surjective_id] at this
  have hfix₀ : Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) ≤
      Subgroup.normalizer (u5PtP h : Set (hypPSU h 2 1)) :=
    hY.le₀.trans Subgroup.le_normalizer
  have hfix₁ : Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) ≤
      Subgroup.normalizer (u5LnP h : Set (hypPSU h 2 1)) :=
    hY.le₁.trans Subgroup.le_normalizer
  rcases AG.normalizer_le_of_isAGMember hBT (u5_sylow h)
    (fun A _ hA hAtop => hY.above A (by simpa using hA) hAtop) hfix₀ hfix₁ hD with h1 | h1
  · exact Or.inl (u5PtP_normalizer h ▸ h1)
  · exact Or.inr (u5LnP_normalizer h ▸ h1)

end CFSG.Quasithin.H13.F431.Un.OL5
