module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

theorem largeEvenMarking_of_rawDatum {X : Type} [Group X] (hX : commutator X = ⊤)
    [IsSimpleGroup (X ⧸ Subgroup.center X)] {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hraw : LargeEvenRawDatum lab fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R))
    {S : LargeEvenLabel → Prop} (hS : S lab) :
    LargeEvenMarking X fun lab' _ _ _ _ _ => S lab' :=
  ⟨hX, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨θ⟩ => ⟨θ.symm.isSimpleGroup,
    nonabelian_of_mulEquiv θ (exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance), θ, hS⟩)
    hraw⟩

theorem largeEvenMarking_A1_of_mulEquiv {X : Type} [Group X] (hX : commutator X = ⊤)
    {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) k) :
    LargeEvenMarking X fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1 := by
  have h4 : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hn)
  have := (LocalCores.isQuasisimple_of_mulEquiv e.symm
    (SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
      (Or.inr (hk ▸ h4)))).2.1
  have hM : Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 n :=
    ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => by rw [Prod.mk.injEq] at h; omega,
      fun h => by rw [Prod.mk.injEq] at h; omega⟩, k, inferInstance, inferInstance, hk,
      ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
        (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k)⟩⟩
  exact largeEvenMarking_of_rawDatum hX (lab := ⟨.A, 1, n⟩)
    ⟨(by omega : 1 ≤ n), le_rfl, fun _ => hn⟩ (recipeLinear_of_statedClassicalModel hM) ⟨rfl, rfl⟩

theorem largeEvenMarking_twA2_of_mulEquiv {X : Type} [Group X] {L : Type} [Field L] [Finite L]
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hL : Nat.card L = (2 ^ n) ^ 2)
    (e : X ≃* ↥(CFSG.Open.StatedSU 3 (2 ^ n) L)) :
    LargeEvenMarking X fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA ∧ lab.n = n := by
  have hn2 : 2 ≤ n := by omega
  have h4 : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hn2)
  have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := fun h => by rw [Prod.mk.injEq] at h; omega
  obtain ⟨hSU, hZ⟩ := LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hL le_rfl hnq
  have hXq := LocalCores.isQuasisimple_of_mulEquiv e.symm hSU
  have := hXq.2.1
  have hM : Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 n :=
    ⟨⟨Nat.prime_two, by omega, le_rfl, hnq⟩, L, inferInstance, inferInstance, hL,
      ⟨QuotientGroup.congr _ _ e ((Subgroup.map_center_eq e).trans hZ)⟩⟩
  have h3 : 3 ∣ 2 ^ n + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hodd
  exact largeEvenMarking_of_rawDatum hXq.1.commutator_eq_top (lab := ⟨.twA, 2, n⟩)
    ⟨(by omega : 1 ≤ n), le_rfl, fun _ => hn2⟩ (recipeUnitary_of_statedClassicalModel hM)
    ⟨⟨rfl, hn2, .inr ⟨rfl, h3⟩⟩, rfl, rfl⟩

end D4Inner

end CFSG.StandardType

end
