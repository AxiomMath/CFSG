module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_card_LomGLMinus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {b c : K}
    (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} (hu : quadMinus m K b c u = 0) (hu0 : u ≠ 0) :
    Nat.card (LomGLMinus hm hirr u) = Nat.card K ^ (2 * m - 2) := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  have hfin : Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hLe := CFSG.ClassicalGroups.Orthogonal.rootGroup_le_elementaryGroup (quadMinus m K b c) u
  have hLom : Nat.card ↥(CFSG.ClassicalGroups.Orthogonal.Lom (quadMinus m K b c) u) =
      Nat.card ↥(CFSG.ClassicalGroups.Orthogonal.rootGroup (quadMinus m K b c) u) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLe).toEquiv
  rw [LomGLMinus,
    Subgroup.card_map_of_injective (f := (StatedOmega (StatedQuadMinus m K b c)).subtype)
      (Subgroup.subtype_injective _),
    Subgroup.card_map_of_injective (f := (statedOmegaMinusEquiv hm hirr).symm.toMonoidHom)
      (statedOmegaMinusEquiv hm hirr).symm.injective,
    hLom, CFSG.ClassicalGroups.Orthogonal.card_rootGroup hQ hu hu0, hfin]

theorem sec7ctr_card_LomGLPlus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) {u : Fin m ⊕ Fin m → K} (hu : quadPlus m K u = 0) (hu0 : u ≠ 0) :
    Nat.card (LomGLPlus hm u) = Nat.card K ^ (2 * m - 2) := by
  have hQ := nondegenerate_polarBilin_quadPlus m K
  have hfin : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hLe := CFSG.ClassicalGroups.Orthogonal.rootGroup_le_elementaryGroup (quadPlus m K) u
  have hLom : Nat.card ↥(CFSG.ClassicalGroups.Orthogonal.Lom (quadPlus m K) u) =
      Nat.card ↥(CFSG.ClassicalGroups.Orthogonal.rootGroup (quadPlus m K) u) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLe).toEquiv
  rw [LomGLPlus,
    Subgroup.card_map_of_injective (f := (StatedOmega (StatedQuadPlus m K)).subtype)
      (Subgroup.subtype_injective _),
    Subgroup.card_map_of_injective (f := (statedOmegaPlusEquiv (K := K) hm).symm.toMonoidHom)
      (statedOmegaPlusEquiv (K := K) hm).symm.injective,
    hLom, CFSG.ClassicalGroups.Orthogonal.card_rootGroup hQ hu hu0, hfin]

theorem sec7ctr_card_LB (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {r : G} (hr : Sec7A hc t r) :
    ∃ d : ℕ, 4 ≤ d ∧ Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ d ∧
      Nat.card (LB M Q B) = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (d - 2) := by
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.toSec5.mem
  rcases hcases with
    ⟨m, hm, φ, u, u', hu, -, hu0, -, -, hrange, hker, hsec, hLu, -⟩ |
    ⟨m, b, c, hm, hirr, φ, u, u', hu, -, hu0, -, -, hrange, hker, hsec, hLu, -⟩
  · have hnat : NaturalRep (ι := Fin m ⊕ Fin m) K (StatedOmega (StatedQuadPlus m K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) :=
      ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hcardι : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hsplit := card_inf_mul_card_map hLR φ hker
    rw [hLu, sec7ctr_card_LomGLPlus hm hu hu0] at hsplit
    refine ⟨2 * m, by omega, ?_, ?_⟩
    · rw [hcard, hcardι]
    · rw [← hsplit, hKZ]
  · have hnat : NaturalRep (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m K b c)) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
        (hc.CN t) :=
      ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hcardι : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hsplit := card_inf_mul_card_map hLR φ hker
    rw [hLu, sec7ctr_card_LomGLMinus hm hirr hu hu0] at hsplit
    refine ⟨2 * m, by omega, ?_, ?_⟩
    · rw [hcard, hcardι]
    · rw [← hsplit, hKZ]

end CFSG.RankThree.GF2n.Stroth80
