module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthALRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSpinor
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

private theorem ct_nb1_refl_class
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι)
    {a : MulAut ↥Bs} (ha : a ∈ ggAInf 3 B Bs x L D J) (hr : GGIsReflection 3 a) :
    ∃ c : ZMod 3, c ≠ 0 ∧ OrthReflOfNorm Q c (ggLin (p := 3) ι a) := by
  have hd : 0 < Module.finrank (ZMod 3) V := by
    rcases S.dim with h | h <;> omega
  have hFD : FiniteDimensional (ZMod 3) V := FiniteDimensional.of_finrank_pos hd
  have hFBs : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  have hFin : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hO : ggLin (p := 3) ι a ∈ QuadraticMap.orthogonalGroup Q :=
    QuadraticMap.mem_orthogonalGroup_iff.mpr ((S.orth (ggLin (p := 3) ι a)).mp ⟨a, ha, rfl⟩)
  have hrefl : GGLinRefl (ggLin (p := 3) ι a) :=
    (@ggIsReflection_iff_ggLinRefl G _ 3 ⟨by decide⟩ Bs V _ _ hFin (by decide) ι a).mp hr
  exact (@linRefl_iff_orthRefl V _ _ hFD Q S.nondeg (ggLin (p := 3) ι a) hO).mp hrefl

private lemma ct_nb1_eq_or_neg {c c₁ : ZMod 3} (hc : c ≠ 0) (hc₁ : c₁ ≠ 0) :
    c = c₁ ∨ c = -c₁ := by
  revert c c₁
  decide

private lemma ct_nb1_ne_neg {c₁ : ZMod 3} (hc₁ : c₁ ≠ 0) : c₁ ≠ -c₁ := by
  revert c₁
  decide

theorem ggOrthNbr_classL
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) :
    ∃ c₁ : ZMod 3, c₁ ≠ 0 ∧ (∀ a ∈ ggAutomizer L Bs, GGIsReflection 3 a → OrthReflOfNorm Q c₁ (ggLin (p := 3) ι a)) ∧
      ∃ a ∈ ggAutomizer L Bs, GGIsReflection 3 a := by
  obtain ⟨t, n, f, ψ, hloc, -, htab⟩ := s2jn_exists_tableBFrame G 3 B Bs x L D J 𝒦 S.cfg S.split
  obtain ⟨ε, hε, -, -⟩ := htab
  obtain ⟨⟨hp, hp2, hadm, h3⟩, -⟩ := hloc
  have hrank : 0 < (ggU t n f).D.rank := by
    rw [lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm h3]
    omega
  let i : Fin (ggU t n f).D.rank := ⟨0, hrank⟩
  let a0 : MulAut ↥Bs :=
    ((ε ((CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer L Bs)) :
      MulAut ↥Bs)
  have ha0 : a0 ∈ ggAutomizer L Bs :=
    (ε ((CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType).simple i)).2
  have hr0 : GGIsReflection 3 a0 := by
    simpa [a0] using hε i
  have ha0Inf : a0 ∈ ggAInf 3 B Bs x L D J := by
    unfold ggAInf
    exact Subgroup.mem_sup_left ha0
  obtain ⟨c₁, hc₁, hrefl0⟩ := ct_nb1_refl_class S ha0Inf hr0
  refine ⟨c₁, hc₁, ?_, a0, ha0, hr0⟩
  intro a ha har
  obtain ⟨g, hg, hga⟩ := (S.refl_conj).2 a0 ha0 a ha hr0 har
  have hgO : ggLin (p := 3) ι g ∈ QuadraticMap.orthogonalGroup Q :=
    QuadraticMap.mem_orthogonalGroup_iff.mpr
      ((S.orth (ggLin (p := 3) ι g)).mp ⟨g, Subgroup.mem_sup_left hg, rfl⟩)
  have hconj := OrthReflOfNorm.conj hrefl0 (ggLin (p := 3) ι g) hgO
  simpa [← map_mul, ← map_inv, ← hga] using hconj

theorem ggOrthNbr_exists_other
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) {c₁ : ZMod 3} (hc₁ : c₁ ≠ 0)
    (hL : ∀ a ∈ ggAutomizer L Bs, GGIsReflection 3 a → OrthReflOfNorm Q c₁ (ggLin (p := 3) ι a)) :
    ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
      ∃ s ∈ ggAutomizer K Bs, GGIsReflection 3 s ∧ OrthReflOfNorm Q (-c₁) (ggLin (p := 3) ι s) := by
  classical
  have hd : 0 < Module.finrank (ZMod 3) V := by
    rcases S.dim with h | h <;> omega
  have hFD : FiniteDimensional (ZMod 3) V := FiniteDimensional.of_finrank_pos hd
  have hd2 : 2 ≤ Module.finrank (ZMod 3) V := by
    rcases S.dim with h | h <;> omega
  by_contra h
  push Not at h
  let C₁ : Set (V ≃ₗ[ZMod 3] V) := {g | OrthReflOfNorm Q c₁ g}
  have hne : c₁ ≠ -c₁ := ct_nb1_ne_neg hc₁
  have hAL : ggAutomizer L Bs ≤ (Subgroup.closure C₁).comap (ggLin (p := 3) ι) := by
    rw [(S.refl_conj).1]
    refine (Subgroup.closure_le _).mpr ?_
    rintro a ⟨haL, har⟩
    exact Subgroup.subset_closure (hL a haL har)
  have hAKall : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ (Subgroup.closure C₁).comap (ggLin (p := 3) ι) := by
    intro y K hnb
    rw [S.cfg.2.1 y K hnb]
    refine (Subgroup.closure_le _).mpr ?_
    rintro a ⟨haK, har⟩
    have haInf : a ∈ ggAInf 3 B Bs x L D J := by
      unfold ggAInf
      exact Subgroup.mem_sup_right <| Subgroup.mem_iSup_of_mem y <|
        Subgroup.mem_iSup_of_mem K <| Subgroup.mem_iSup_of_mem hnb haK
    obtain ⟨c, hc0, hrefl⟩ := ct_nb1_refl_class S haInf har
    rcases ct_nb1_eq_or_neg hc0 hc₁ with hc | hc
    · rw [hc] at hrefl
      exact Subgroup.mem_comap.mpr (Subgroup.subset_closure hrefl)
    · rw [hc] at hrefl
      exact (h y K hnb a haK har hrefl).elim
  have hInf : ggAInf 3 B Bs x L D J ≤ (Subgroup.closure C₁).comap (ggLin (p := 3) ι) := by
    unfold ggAInf
    refine sup_le hAL ?_
    refine iSup_le fun y => ?_
    refine iSup_le fun K => ?_
    refine iSup_le fun hnb => hAKall y K hnb
  obtain ⟨g₀, hg₀⟩ :=
    @exists_orthReflOfNorm V _ _ hFD Q S.nondeg hd2 (-c₁) (neg_ne_zero.mpr hc₁)
  obtain ⟨a, haInf, hga⟩ := (S.orth g₀).mpr
    (QuadraticMap.mem_orthogonalGroup_iff.mp
      ((OrthReflOfNorm.mem_orthogonalGroup_and_ne_zero hg₀).1))
  have hmem : g₀ ∈ Subgroup.closure C₁ := by
    have := hInf haInf
    rw [Subgroup.mem_comap] at this
    rwa [hga] at this
  exact (@orthRefl_not_mem_closure V _ _ hFD Q S.nondeg c₁ (-c₁) hc₁ (neg_ne_zero.mpr hc₁)
    hne g₀ hg₀) hmem

end CFSG.StandardType.OrthF3

end
