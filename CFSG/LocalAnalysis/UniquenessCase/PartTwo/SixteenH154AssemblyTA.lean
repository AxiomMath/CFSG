module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CoverMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.GroupTheory.IsCyclicOfPRankLeOne
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_isComponentOf_map_mulEquiv_apply {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {L H : Subgroup A} (h : CFSG.Open.IsComponentOf L H) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (H.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map e.toMonoidHom h.2.1,
    CFSG.Open.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective).symm
      h.2.2⟩

private theorem s16h_cyclic_sylow_three_of_lie_shape {X : Type} [Group X] [Finite X]
    (h : IsL3 X 1 ∨ UC22.IsL2 X 2 ∨ UC22.IsL2 X 3) :
    ∀ Q : Sylow 3 X, IsCyclic ↥(Q : Subgroup X) := by
  intro Q
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with h3 | h2 | h2
  · exact isCyclic_of_prime_card (p := 3) (card_sylow_three_of_isL3 h3 Q)
  · have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 :=
      UC22.pRank_le_one_of_isL2_or_isSz (Or.inl h2) Nat.prime_three (by norm_num)
    have hQrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Q : Subgroup X)) ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (Q : Subgroup X)]
      exact (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt
        (le_top : (Q : Subgroup X) ≤ ⊤)).trans hrank
    exact CFSG.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) Q.isPGroup' hQrank
  · have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 :=
      UC22.pRank_le_one_of_isL2_or_isSz (Or.inl h2) Nat.prime_three (by norm_num)
    have hQrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Q : Subgroup X)) ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (Q : Subgroup X)]
      exact (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt
        (le_top : (Q : Subgroup X) ≤ ⊤)).trans hrank
    exact CFSG.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) Q.isPGroup' hQrank

theorem s16h_pRank_three_eq_one_of_lie_cover (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {K : Subgroup G} (hK : K ∈ calC D.M)
    {B : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hB : barSub V₀ V h.isElemAbelian K = B)
    (hshape : IsL3 ↥B 1 ∨ UC22.IsL2 ↥B 2 ∨ UC22.IsL2 ↥B 3) :
    CFSG.Open.pRank 3 K = 1 := by
  subst B
  haveI : Finite (MulAut (Vtil V₀ V h.isElemAbelian)) :=
    Finite.of_injective
      (fun e : MulAut (Vtil V₀ V h.isElemAbelian) =>
        (e : Vtil V₀ V h.isElemAbelian → Vtil V₀ V h.isElemAbelian))
      (fun _ _ hh => MulEquiv.ext (congrFun hh))
  have hcyc := s16h_cyclic_sylow_three_of_lie_shape hshape
  have h3B : 3 ∣ Nat.card ↥(barSub V₀ V h.isElemAbelian K) :=
    s16h_three_dvd_of_lieFactor hshape
  have hne : barSub V₀ V h.isElemAbelian K ≠ ⊥ := by
    intro hbot
    rw [hbot] at h3B
    have h1 : Nat.card ↥(⊥ : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))) = 1 :=
      Subgroup.card_bot
    rw [h1] at h3B
    exact absurd h3B (by norm_num)
  have hKle : K ≤ stabTil V₀ V :=
    (A3.subnormal_le hK.1).trans
      (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀)
  have h3K : 3 ∣ Nat.card K :=
    h3B.trans (s16h_card_barSub_dvd V₀ V h.isElemAbelian hKle)
  refine le_antisymm ?_ ?_
  · exact s16h_pRank_cover_le_one_of_cyclic_sylow D h hK hne Nat.prime_three (by norm_num) hcyc
  · rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) K]
    exact CFSG.one_le_pRank_of_dvd_card Nat.prime_three h3K

theorem s16h_four_or_strong_of_tensor (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)}
    (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t
      (lBar V₀ V h.hyp151.isElemAbelian L))
    {K : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))}
    (hK : IsComponentOf K (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    {g : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)}
    (hg : g ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : (lBar V₀ V h.hyp151.isElemAbelian L) = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hT : (IsL3 ↥K 1 ∧
        NatTensor (lBar V₀ V h.hyp151.isElemAbelian L)
          (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 3 1) ∨
      (UC22.IsL2 ↥K 2 ∧
        NatTensor (lBar V₀ V h.hyp151.isElemAbelian L)
          (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 2 2) ∨
      (UC22.IsL2 ↥K 3 ∧
        NatTensor (lBar V₀ V h.hyp151.isElemAbelian L)
          (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 2 3)) :
    4 ≤ CFSG.Open.pRank 3 D.M ∨ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hV := h.hyp151.isElemAbelian
  let Kb : Subgroup (MulAut (Vtil V₀ V hV)) := K.map (MulAut.conj g).toMonoidHom
  have hMbar : (Mbar D.M V₀ V hV).map (MulAut.conj g).toMonoidHom = Mbar D.M V₀ V hV :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (H := Mbar D.M V₀ V hV) hg)
  have hKb : IsComponentOf Kb (Mbar D.M V₀ V hV) := by
    have h1 : IsComponentOf (K.map (MulAut.conj g).toMonoidHom)
        ((Mbar D.M V₀ V hV).map (MulAut.conj g).toMonoidHom) :=
      s16h_isComponentOf_map_mulEquiv_apply (MulAut.conj g) hK
    rw [hMbar] at h1
    exact h1
  obtain ⟨K₁, hK₁mem, hK₁bar⟩ := s16h_exists_cover D S.h127 S.h119 h.hyp151.hyp125 hK
  obtain ⟨K₂, hK₂mem, hK₂bar⟩ := s16h_exists_cover D S.h127 S.h119 h.hyp151.hyp125 hKb
  have hshapeK : IsL3 ↥K 1 ∨ UC22.IsL2 ↥K 2 ∨ UC22.IsL2 ↥K 3 := by
    rcases hT with ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
  have hshapeKb : IsL3 ↥Kb 1 ∨ UC22.IsL2 ↥Kb 2 ∨ UC22.IsL2 ↥Kb 3 := by
    have e : ↥K ≃* ↥Kb :=
      K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    rcases hshapeK with h1 | h2 | h3
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h1)
    · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h2))
    · exact Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h3))
  have hKne : K ≠ ⊥ := by
    haveI := hK.2.2.2
    have hnt : Nontrivial ↥K :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K).mp hnt
  have hKbne : Kb ≠ ⊥ := by
    intro hbot
    apply hKne
    exact (Subgroup.map_eq_bot_iff_of_injective (H := K)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).1 hbot
  have e₁ : CFSG.Open.pRank 3 K₁ = 1 :=
    s16h_pRank_three_eq_one_of_lie_cover D h.hyp151.hyp125 hK₁mem hK₁bar hshapeK
  have e₂ : CFSG.Open.pRank 3 K₂ = 1 :=
    s16h_pRank_three_eq_one_of_lie_cover D h.hyp151.hyp125 hK₂mem hK₂bar hshapeKb
  have hne12 : K₁ ≠ K₂ := fun heq =>
    hne (hK₁bar.symm.trans ((congrArg (barSub V₀ V hV) heq).trans hK₂bar))
  refine Or.inr (s16h_stronglyEmbedded_of_two_pRank_one_covers D S.h82 h hs
    hK₁mem hK₂mem hne12 ?_ ?_ ?_ ?_ e₁ e₂)
  · rw [hK₁bar, show barSub V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom from hL]
    exact le_sup_left
  · rw [hK₂bar, show barSub V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom from hL]
    exact le_sup_right
  · rw [hK₁bar]; exact hKne
  · rw [hK₂bar]; exact hKbne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
