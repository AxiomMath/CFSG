module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2LU4Weyl
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSCRows

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.Open TableB

section U4

variable {n p : ℕ} {K : Type} [Field K]

theorem ggSCWeylIrredTwoU4_hypSU (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) : GGSCWeylIrredTwoLU4 p (hypSU h 2 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E hE h2 _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbar : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := 2) h hp hζ hbar
  obtain ⟨g, hg⟩ := exists_conj_hypEntries h hp hp2 hpq hζ (by norm_num) E hE h2
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := hg x hx
    refine ⟨Multiplicative.ofAdd t, Subtype.ext (Units.ext ?_)⟩
    rw [hι t]
    exact ht.symm
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : E.map (MulAut.conj g).toMonoidHom = ι.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_range_hypTorusHom h hp hζ ι hι]; exact h2)
  have hirr := ggWeylIrred_map (MulAut.conj g⁻¹) (ggWeylIrred_hypTorusRange h hp hp2 hζ hbar ι hι)
  have hback : ι.range.map (MulAut.conj g⁻¹).toMonoidHom = E := by
    rw [← heq, Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (hypSU h 2 0) := MonoidHom.ext fun x => by
      show g⁻¹ * (g * x * g⁻¹) * g = x
      group
    rw [hcomp, Subgroup.map_id]
  rwa [hback] at hirr

variable [Finite K]

theorem ggSCWeylIrredTwoU4_statedProj (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    GGSCWeylIrredTwoLU4 p (StatedProj (StatedSU (2 * 2) (2 ^ n) K)) := by
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  have hSU : GGSCWeylIrredTwoLU4 p (StatedSU (2 * 2) (2 ^ n) K) :=
    ggSCWeylIrredTwoLU4_of_mulEquiv (hypTransport h hR).symm
      (ggSCWeylIrredTwoU4_hypSU h hp hp2 hpq)
  refine ggSCWeylIrredTwoLU4_of_centralQuotient hp
    (QuotientGroup.mk' ((StatedScalars (Fin (2 * 2)) K).subgroupOf (StatedSU (2 * 2) (2 ^ n) K)))
    (QuotientGroup.mk'_surjective _) ?_ ?_ hSU
  · rw [QuotientGroup.ker_mk']
    exact scalars_le_center_statedSU
  · exact fun hdvd => hpq' (hdvd.trans (card_center_statedSU_dvd h.card_eq_sq (by omega)))


theorem ggTorusNoLineTwoU4_unitaryHyp (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    GGTorusNoLineTwo p (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenGUSet (Fin 4) K (2 ^ n))) := by
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hq4 : 4 ≤ 2 ^ n := four_le_two_pow_of_dvd_sub_one hp hp2 hn hpq
  exact ggTorusNoLineTwo_of_scWeylIrredTwoLU4 hp (center_statedProj_statedSU_eq_bot hK le_rfl)
    (fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega)
      hp hpq' φ hφ hφp)
    (ggCenterPrime_psu_even hK (by decide) le_rfl hq4 hpq')
    (ggSCWeylIrredTwoU4_statedProj hK hn hp hp2 hpq)

theorem recipeUnitary_rowPlainTwoU4 (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeUnitary 4 (2 ^ n) Q) :
    LargeEvenRecipeUnitary 4 (2 ^ n) fun R _ I F => Q R I F ∧ (GGTorusLift p 0 R ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLineTwo p R I)) := by
  obtain ⟨K', _, _, hK, hQ'⟩ := hQ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K' 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hK
  exact ⟨K', inferInstance, inferInstance, hK, hQ',
    TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (d := 4) (f := n) (K := K')
      (by norm_num)),
    fun _ _ => ggTorusNoLineTwoU4_unitaryHyp hK hn hp hp2 hpq⟩

end U4

theorem largeEvenLabelAll_rowPlainTwo_u4
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) := by
  obtain ⟨hT, hl, hpq⟩ := h
  have hrest : LargeEvenLabelAll lab fun R _ I _ => GGTorusLift p 0 R ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLineTwo p R I) := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at hT hl hpq
    subst hl
    have hn : 1 ≤ n := hlab.1
    intro Q hQ
    rcases hT with rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
    · exact recipeUnitary_rowPlainTwoU4 hn hp hp2 hpq hQ
    · simp only [show ¬ ((3 : ℕ) = 2) from by norm_num, ↓reduceIte] at hQ ⊢
      exact recipeUnitary_rowPlainTwoU4 hn hp hp2 hpq hQ
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_unitFour hlab hT hl) hrest).mono
    fun _ _ _ _ ⟨hi, hlift, hline⟩ => ⟨hi, hlift, hline⟩

end CFSG.StandardType

end
