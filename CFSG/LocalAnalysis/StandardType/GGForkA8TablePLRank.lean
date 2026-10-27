module

public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePClauses
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSL9_card_le_seven_cube {E : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    (hE : IsElemAbelian 7 E) : Nat.card E ≤ 7 ^ 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
    Finite.of_equiv (GL (Fin 9) (ZMod 2)) ggSL9GLEquiv.toEquiv
  have hEp : IsPGroup 7 ↥E := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hx : x ^ 7 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 (x : GGSL9V ≃ₗ[ZMod 2] GGSL9V) x.2
    exact orderOf_dvd_of_pow_eq_one hx
  obtain ⟨n, hEn⟩ := (IsPGroup.iff_card (p := 7) (G := ↥E)).mp hEp
  have hn_le : n ≤ 3 := by
    by_contra h
    push Not at h
    exact not_seven_pow_four_dvd_card_ggSL9
      (dvd_trans (Nat.pow_dvd_pow 7 (Nat.succ_le_of_lt h))
        (by rw [← hEn]; exact Subgroup.card_subgroup_dvd_card E))
  rw [hEn]
  exact Nat.pow_le_pow_right (by norm_num) hn_le

theorem largeEvenLabelAll_card_le_a8Two :
    LargeEvenLabelAll ⟨.A, 8, 1⟩ fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian 7 E → Nat.card E ≤ 7 ^ 3 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', ?_⟩
  intro E hEI hE
  haveI : Finite (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
    Finite.of_equiv (GL (Fin 9) (ZMod 2)) ggSL9GLEquiv.toEquiv
  let e := ggSL9RecipeEquiv hK
  have hEmap : IsElemAbelian 7 (E.map (MulAut.congr e).toMonoidHom) :=
    TableB.isElemAbelian_map hE _
  have hsub : ((E.map (MulAut.congr e).toMonoidHom :
      Subgroup (MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) :
      Set (MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) ⊆
      Set.range (MulAut.conj : (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →*
        MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rintro φ ⟨x, hx, rfl⟩
    exact congr_ggSL9RecipeEquiv_mem hK (hEI hx)
  obtain ⟨A, hA, hAc⟩ :=
    TableBSymp.exists_of_subset_inn (R := GGSL9V ≃ₗ[ZMod 2] GGSL9V) center_ggSL9_eq_bot hsub hEmap
  have h1 : Nat.card A ≤ 7 ^ 3 := ggSL9_card_le_seven_cube hA
  rw [hAc, Subgroup.card_map_of_injective (MulAut.congr e).injective] at h1
  exact h1

private def ta1_a8TwoBound (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I _ => lab = ⟨.A, 8, 1⟩ →
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian 7 E →
      Nat.card E ≤ 7 ^ 3

private theorem ta1_a8TwoBound_labelAll (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab (ta1_a8TwoBound lab) := by
  by_cases h : lab = ⟨.A, 8, 1⟩
  · subst h
    refine LargeEvenLabelAll.mono (P := fun R _ I _ => ∀ E : Subgroup (MulAut R),
        (E : Set (MulAut R)) ⊆ I → IsElemAbelian 7 E → Nat.card E ≤ 7 ^ 3)
      (P' := ta1_a8TwoBound ⟨.A, 8, 1⟩) ?_ largeEvenLabelAll_card_le_a8Two
    intro R _ I F hE hA8
    exact hE
  · refine LargeEvenLabelAll.mono (P := fun _ _ _ _ => True) ?_
      (largeEvenLabelAll_true lab)
    intro R _ I F _
    exact fun hA8 => absurd hA8 h

theorem ggA8Nbr_card_B {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig 7 B Bs x L D J) {y : G}
    {K : Subgroup G} (hK : GGNbr 7 B x D J y K) (hKd : GGInnerDiagOn Bs K)
    (hKlab : GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K)) :
    Nat.card B = 7 ^ 4 := by
  have hp : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hp⟩
  have hB : IsElemAbelian 7 B := hC.1.2.2.2.2.2.2.1.1.1
  have hBc : Nat.card B = 7 ^ LargeEvenTwoLocalRank 7 G := hC.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank 7 G := hC.1.2.2.2.2.2.1.2.2.2
  have hperf : commutator K = ⊤ := hKd.1
  have hMarking := ggMarking_and_labelAll_dep (P' := ta1_a8TwoBound) ta1_a8TwoBound_labelAll hKd
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨⟨hN, hinduces⟩, hP'⟩⟩ :=
    largeEvenMarking_exists_hasLabel hMarking
  have hlabA8 : lab = ⟨.A, 8, 1⟩ := by
    rcases ggLabelIso_typeA_cases hRig (r := 8) (f := 1) (by norm_num) hlab
        largeEvenInLambda2_a8 hhas hKlab with h | ⟨h83, -⟩
    · exact h
    · omega
  have hbound : ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsElemAbelian 7 E → Nat.card E ≤ 7 ^ 3 := hP' hlabA8
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hC.2.1.1.trans hN
  have hS : LargeEvenSHat 7 B y K := hK.1
  set α : ↥B →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hBN) with hα
  have hE : IsElemAbelian 7 α.range :=
    isElemAbelian_range (fun a b => hB.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hB.2 a a.2)) α
  have himgI : (α.range : Set (MulAut R)) ⊆ I := by
    rintro φ ⟨b, rfl⟩
    exact ggBeta_mem K θ hBN (fun b hb => hinduces b (hC.2.1.1 hb)) b
  have hrange : Nat.card α.range ≤ 7 ^ 3 := hbound α.range himgI hE
  have hker : α.ker ≤ (Subgroup.zpowers y).subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf, ← inf_centralizer_eq_zpowers_of_sHat hS]
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one K θ hperf (g := ⟨b, hBN b.2⟩) hb⟩
  have hyB : y ∈ B := hS.2.1
  have hy : Nat.card ((Subgroup.zpowers y).subgroupOf B) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hB.2 y hyB) hS.2.2.1]
  have hk : Nat.card α.ker ≤ 7 := hy ▸ Subgroup.card_le_of_le hker
  have h1 := Subgroup.card_ker_mul_card_range α
  have hBle : Nat.card B ≤ 7 * 7 ^ 3 := by
    rw [← h1]
    exact Nat.mul_le_mul hk hrange
  refine le_antisymm ?_ ?_
  · calc Nat.card B ≤ 7 * 7 ^ 3 := hBle
      _ = 7 ^ 4 := by norm_num
  · rw [hBc]
    exact Nat.pow_le_pow_right (by norm_num) h4

end CFSG.StandardType

end
