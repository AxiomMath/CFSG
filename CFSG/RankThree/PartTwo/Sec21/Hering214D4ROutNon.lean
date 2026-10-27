module

public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RLine
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RSL3
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RPGL
public import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Sec19
open scoped commutatorElement

section OutNon


variable {n : ℕ} {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem outer_nonstd_four (P : D4Par n F σ) (hev : Even n) {β : MulAut (C0 σ)}
    (hβ3 : β ^ 3 = 1) (hβout : ¬ KFacts.IsInnerAut β) (hstd : ¬ Sec4.IsStdGraphFieldConj σ β)
    {x g : C0 σ} (hβg : β g = g) (hβx : β x = x) (hxg : x * g * x⁻¹ = g⁻¹) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) : FourFixedMoved β (MulAut.conj g) := by
  have hn1 := P.one_le
  haveI := P.charP
  have hPGL := Sec8.kF89D4SecondCentEven_of_y0 Sec8.kF89D4SecondCentY0Even_holds n hev hn1 F σ
    P.card P.frob β hβ3 hβout hstd
  obtain ⟨K', _, _, hK'c, ⟨ι⟩⟩ := hPGL
  haveI : CharP K' 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'c
  have h3 : 3 ∣ Nat.card K' - 1 := by
    rw [hK'c]
    exact three_dvd_two_pow_sub_one hev
  obtain ⟨ω, hω, hω1⟩ := exists_primitive_cube_root h3
  have hgS : g ∈ Sec4.autFix β := hβg
  have hxS : x ∈ Sec4.autFix β := hβx
  refine fourFixedMoved_of_subgroup (S := Sec4.autFix β) (fun s hs => hs) hgS ?_
  apply NormMoveFour.of_mulEquiv ι
  have hc : ⁅(⟨x, hxS⟩ : ↥(Sec4.autFix β)), (⟨g, hgS⟩ : ↥(Sec4.autFix β))⁆ =
      (⟨g, hgS⟩ : ↥(Sec4.autFix β)) :=
    Subtype.ext (commutator_eq_of_inverts hxg hg3)
  have hz : ι ⟨g, hgS⟩ ∈ ⁅(⊤ : Subgroup ↥(CFSG.PGLModel.projImage (Sec4.glPi true 3 (2 ^ n) K'))),
      (⊤ : Subgroup ↥(CFSG.PGLModel.projImage (Sec4.glPi true 3 (2 ^ n) K')))⁆ := by
    rw [← hc, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hz3 : (ι ⟨g, hgS⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨g, hgS⟩ : ↥(Sec4.autFix β)) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  have hz1 : ι ⟨g, hgS⟩ ≠ 1 := by
    intro h
    apply hg1
    have : (⟨g, hgS⟩ : ↥(Sec4.autFix β)) = 1 := ι.injective (h.trans (map_one ι).symm)
    exact congrArg Subtype.val this
  exact pgl3_four_of_commutator (2 ^ n)
    (fun h c hc hns => sl3_four_of_pow_three hω h c hc hns) _ hz hz3 hz1

end OutNon

end CFSG.RankThree.PartTwo.Sec21.Hering214
