module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGB36LemmaRT
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecLinSmall
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4A5Close

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial

private noncomputable def ftab_statedProjEquiv (d : ℕ) (K : Type) [Field K] :
    LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* StatedProj (StatedSL d K) :=
  (TypeA.recipeEquiv d K).trans
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL d K).symm.trans
      (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d K))

private theorem ftab_lieModel_l24 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) :
    LieModel (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) .PSL 2 2 2 := by
  have hadm : StatedLieAdmissible .PSL 2 2 2 := by
    refine ⟨Nat.prime_two, by norm_num, by norm_num, ?_, ?_⟩
    · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.2 (by norm_num)
    · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.2 (by norm_num)
  exact Or.inl ⟨by decide,
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨ftab_statedProjEquiv 2 K⟩⟩⟩

private theorem ftab_aut_rank_l24 {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    (hlab : GGHasLabel ⟨.A, 1, 2⟩ (J ⧸ Subgroup.center J)) :
    ∀ E : Subgroup (MulAut J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 1 := by
  intro E hE
  unfold GGHasLabel at hlab
  dsimp only [LargeEvenRawDatum] at hlab
  unfold LargeEvenRecipeLinear at hlab
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hlab
  have hK4 : Nat.card K = 2 ^ 2 := hKcard
  have hmod : LieModel (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) .PSL 2 2 2 :=
    ftab_lieModel_l24 hK4
  have hinj : Function.Injective (ggInducedAut e) := ggInducedAut_injective_of_perfect hperf e
  have hcard : Nat.card (E.map (ggInducedAut e)) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  have hE' : IsElemAbelian 3 (E.map (ggInducedAut e)) := hE.map (ggInducedAut e)
  have hAutcard : Nat.card (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))) = 120 := by
    rw [CFSG.Quasithin.H13.card_mulAut_of_lieModel_L2 (n := 2) (by norm_num) hmod]
    norm_num
  have hdvd : Nat.card (E.map (ggInducedAut e)) ∣ 120 := by
    rw [← hAutcard]
    exact Subgroup.card_subgroup_dvd_card (E.map (ggInducedAut e))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hE')
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h9 : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
    have := h9.trans (hk ▸ hdvd)
    norm_num at this
  calc Nat.card E = Nat.card (E.map (ggInducedAut e)) := hcard.symm
    _ = 3 ^ k := hk
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1

theorem ggFieldTwoL24_false {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X} {n : ℕ} {S : ℕ → LargeEvenLabel → Prop}
    (hd : GGTPNBasicB 3 n S A Ab σ J)
    (hhJ : GGHasLabel ⟨.A, 1, 2⟩ (↥J ⧸ Subgroup.center ↥J)) : False := by
  obtain ⟨hlocCore, hflat, hcard3, -, -, -, -, -⟩ := hd
  obtain ⟨hAbA, hσAb, -, hkerAb⟩ := hflat
  have hperfJ : commutator ↥J = ⊤ := hlocCore.2.2.2.1.2.2.1
  have hAbab : IsElemAbelian 3 Ab := by
    obtain ⟨hc, hp⟩ := hlocCore.1
    haveI : IsMulCommutative A := hc
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      exact Subgroup.mul_comm_of_mem_isMulCommutative A (hAbA u.2) (hAbA v.2)
    · exact hp z (hAbA hz)
  have hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J :=
    fun a ha j hj => hlocCore.2.2.2.2 a (hAbA ha) j hj
  have hAut : ∀ E : Subgroup (MulAut ↥J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 1 :=
    ftab_aut_rank_l24 hperfJ hhJ
  have hle := B36.card_le_of_kernel_le_zpowers (p := 3) (by norm_num) hAbab hσAb hnorm hkerAb
    (k := 1) hAut
  exact absurd (le_trans hcard3 hle) (by norm_num)

end CFSG.StandardType

end
