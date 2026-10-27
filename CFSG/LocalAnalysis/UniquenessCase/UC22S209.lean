module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
import CFSG.LocalAnalysis.UniquenessCase.UC22P20m
import CFSG.LocalAnalysis.RankThreeUC.SmallNH
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.RankThree.PartTwo.Sec18 Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem uc22s209_le_of_isSubnormal {H K : Subgroup G} (h : CFSG.Open.IsSubnormal H K) :
    H ≤ K := by
  induction h with
  | refl H => exact le_rfl
  | step hHM _ _ ih => exact hHM.trans ih

omit [Finite G] in
private theorem uc22s209_hinf_le (H : Subgroup G) : Hinf H ≤ H :=
  Subgroup.map_subtype_le _

theorem uc22s209_parabolic_inf (D : Data G) {L Q P : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hQ : ParabolicOf L Q) (hTQ : D.T ≤ normalizer (Q : Set G)) (hP : ParabolicOf L P)
    (hTP : D.T ≤ normalizer (P : Set G)) : ParabolicOf L (Q ⊓ P) := by
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hTL : D.T ≤ normalizer (L : Set G) := hL.1
  have hB : ∀ {R : Subgroup G}, ParabolicOf L R → D.T ≤ normalizer (R : Set G) →
      L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G) ≤ R := fun hR hTR =>
    uc22p22m_le_of_parabolic D.sylowG hTL hR hTR inf_le_left inf_le_right
  refine ⟨le_inf hQ.1 hP.1, inf_le_left.trans hQ.2.1,
    (uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL), ?_⟩
  intro y hy
  obtain ⟨l, rfl⟩ := hπs y
  have hl : (l : G) ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    (uc22p20m_mem_normalizer_bar_iff D hL l).1 hy
  exact ⟨l, Subgroup.mem_subgroupOf.2 ⟨hB hQ hTQ ⟨l.2, hl⟩, hB hP hTP ⟨l.2, hl⟩⟩, rfl⟩

theorem uc22s209_hinf_mem_calLLow (D : Data G) (h204 : S20_4 D) (hL0 : L0Parabolic D)
    (h1930 : H1930 D) {L P : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hP : MinTInvParabolic D.T D.M L P) : Hinf P ∈ calLLow D.T D.M := by
  obtain ⟨⟨hPpar, hTP, hPM⟩, hmin⟩ := hP
  have hPL : P ≤ L := hPpar.2.1
  have hT2 : IsPGroup 2 D.T := D.sylowG.isPGroup
  have hH : P ⊔ D.T ∈ hSet D.T D.M :=
    mem_hSet_of_le D.sylowG hL.2.2.1 le_sup_right (sup_le_sup_right hPL _)
      fun h => hPM (le_sup_left.trans h)
  obtain ⟨K, hK, hKH⟩ : ∃ K ∈ calL D.T D.M, K ≤ P ⊔ D.T := by
    by_contra hno
    have hbot : (⨆ L' ∈ calLOf D.T D.M (P ⊔ D.T), L' : Subgroup G) = ⊥ :=
      iSup₂_eq_bot.2 fun L' hL' => absurd ⟨L', hL'.1, uc22s209_le_of_isSubnormal hL'.2⟩ hno
    apply hPM
    intro x hx
    have hxH : x ∈ ((P ⊔ D.T : Subgroup G) : Set G) := mem_sup_left hx
    rw [← h204 h1930 _ hH, hbot] at hxH
    obtain ⟨a, ha, m, hm, rfl⟩ := hxH
    rw [SetLike.mem_coe, Subgroup.mem_bot] at ha
    subst ha
    simpa using hm.2
  have hKP : K ≤ P := uc22p20m_le_of_perfect_sup hK.2.1 hKH hTP hT2
  obtain ⟨K₀, hK₀K, hK₀⟩ := Set.Finite.exists_le_minimal (Set.toFinite (calL D.T D.M)) hK
  obtain ⟨Q, hQ, hTQ, hK₀Q⟩ := hL0 h1930 L hL K₀ hK₀ (hK₀K.trans (hKP.trans hPL))
  have hK₀le : K₀ ≤ Q ⊓ P := le_inf (hK₀Q.le.trans (uc22s209_hinf_le Q)) (hK₀K.trans hKP)
  have hPQ : P ≤ Q ⊓ P :=
    hmin ⟨uc22s209_parabolic_inf D hL hQ hTQ hPpar hTP,
      fun t ht => inf_normalizer_le_normalizer_inf ⟨hTQ ht, hTP ht⟩,
      fun h => uc22p20i_not_le_M D hK₀.prop (hK₀le.trans h)⟩ inf_le_right
  have hEq : Hinf P = K₀ :=
    le_antisymm ((inSubgroup_perfectResidual_mono (hPQ.trans inf_le_left)).trans hK₀Q.ge)
      (le_inSubgroup_perfectResidual hK₀.prop.2.1 (hK₀K.trans hKP))
  rw [hEq]
  exact hK₀

theorem s20_9_of_l0Parabolic (D : Data G) (h204 : S20_4 D) (hL0 : L0Parabolic D) : S20_9 D := by
  intro h1930 L hL K
  constructor
  · rintro ⟨hK, hKL⟩
    obtain ⟨Q, hQ, hTQ, hKQ⟩ := hL0 h1930 L hL K hK hKL
    have hQM : ¬ Q ≤ D.M := fun h =>
      uc22p20i_not_le_M D hK.prop (hKQ.le.trans ((uc22s209_hinf_le Q).trans h))
    obtain ⟨P, hPQ, hP⟩ := Set.Finite.exists_le_minimal
      (s := {X : Subgroup G | ParabolicOf L X ∧ D.T ≤ normalizer (X : Set G) ∧ ¬ X ≤ D.M})
      (Set.toFinite _) ⟨hQ, hTQ, hQM⟩
    have hPK := uc22s209_hinf_mem_calLLow D h204 hL0 h1930 hL hP
    have h1 : Hinf P ≤ K := (inSubgroup_perfectResidual_mono hPQ).trans hKQ.ge
    exact ⟨P, hP, le_antisymm (hK.2 hPK.prop h1) h1⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨uc22s209_hinf_mem_calLLow D h204 hL0 h1930 hL hP,
      (uc22s209_hinf_le P).trans hP.prop.1.2.1⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
