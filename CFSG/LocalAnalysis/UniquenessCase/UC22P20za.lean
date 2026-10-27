module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20yd
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20z
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22pw_rank_of_cyclic_squarefree {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hcyc : IsCyclic E) (hsq : Squarefree (Nat.card E)) :
    ∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2 := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative E := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow p E) := inferInstance
  have hcard : Nat.card Q = p ^ (Nat.card E).factorization p := Sylow.card_eq_multiplicity Q
  have hle : (Nat.card E).factorization p ≤ 1 := Squarefree.natFactorization_le_one p hsq
  have hQ : Nat.card Q = 1 ∨ Nat.card Q = p := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
    · left; rw [hcard, h]; simp
    · right; rw [hcard, h]; simp
  refine ⟨Q, ⟨inferInstance, ?_⟩, ?_⟩
  · intro x hx
    have h1 : (⟨x, hx⟩ : ↥(Q : Subgroup E)) ^ Nat.card Q = 1 := pow_card_eq_one'
    rcases hQ with h | h
    · have : Subsingleton ↥(Q : Subgroup E) := Nat.card_eq_one_iff_unique.1 h |>.1
      have h2 : (⟨x, hx⟩ : ↥(Q : Subgroup E)) = 1 := Subsingleton.elim _ _
      have h3 : x = 1 := congrArg Subtype.val h2
      rw [h3]
      exact one_pow p
    · rw [h] at h1
      have := congrArg Subtype.val h1
      simpa using this
  · rcases hQ with h | h
    · rw [h]; exact Nat.one_le_pow _ _ hp.pos
    · rw [h]; exact Nat.le_self_pow (by norm_num) p

theorem uc22pw_good_rankOne (hR1 : uc22pwCartanRankOne) (D : Data G) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) :
    ∃ E : Subgroup (Bar2 L), uc22pwGood D L n E := by
  obtain ⟨e, m', hm', hnem⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hTL := hL.1
  obtain ⟨E, hEU, hcyc, hsq, hodd, hpi, hinv, hα, w, hw2, hwinv, hwtop⟩ :=
    hR1 (Bar2 L) hq n hn hsh ((uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL))
      ↥D.T D.sylowM.isPGroup (uc22pwIndHom L D.T hTL)
      (fun g x => uc22p20u_ind_sylowBar D hL (hTL g.2) g.2 x) e m' hm' hnem
  exact ⟨E, uc22pw_good_of_induced D hL hm' hnem hEU inferInstance hodd
    (uc22pw_rank_of_cyclic_squarefree hcyc hsq) hpi hinv hα ⟨w, hw2, hwinv, hwtop⟩⟩

theorem uc22pw_good_graph (hR2 : uc22pwCartanGraph) (D : Data G) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {n : ℕ} (hn : 2 < n)
    (hsh : IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n) :
    ∃ E : Subgroup (Bar2 L), uc22pwGood D L n E := by
  obtain ⟨e, m', hm', hnem⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hTL := hL.1
  obtain ⟨E, hEU, hab, hodd, hrank, hpi, hinv, hα, w, hw2, hwinv, hwtop⟩ :=
    hR2 (Bar2 L) hq n hn hsh ((uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL))
      ↥D.T D.sylowM.isPGroup (uc22pwIndHom L D.T hTL)
      (fun g x => uc22p20u_ind_sylowBar D hL (hTL g.2) g.2 x) e m' hm' hnem
  exact ⟨E, uc22pw_good_of_induced D hL hm' hnem hEU hab hodd hrank hpi hinv hα
    ⟨w, hw2, hwinv, hwtop⟩⟩

theorem uc22pw_exists_noncomm_of_quasisimple {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y) :
    ∃ a b : Y, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Y = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun z => Subgroup.mem_center_iff.2 fun g => h g z
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  haveI : Subsingleton (Y ⧸ Subgroup.center Y) := by
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ ‹Subsingleton (Y ⧸ Subgroup.center Y)›

theorem uc22pw_bar2_nonabelian (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    ∃ a b : Bar2 L, a * b ≠ b * a := by
  obtain ⟨K, hK, -⟩ := hL.2.2.2
  have hKL : K ≤ L := uc22p22a_le_of_isSubnormal hK.1
  obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hKL hK.1
  obtain ⟨a, b, hab⟩ := uc22pw_exists_noncomm_of_quasisimple hK.2.2
  refine ⟨(e a : Bar2 L), (e b : Bar2 L), fun h => hab ?_⟩
  apply e.injective
  apply Subtype.ext
  simpa using h

theorem uc22pw_isQuasisimple_of_single (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {n : ℕ}
    (h : NParamSingle (Bar2 L) n) : CFSG.Open.IsQuasisimple (Bar2 L) := by
  rcases h with hSz | hL2 | hSU | hSL | hSp
  · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (uc22pw_bar2_nonabelian D hL)).1
  · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (uc22pw_bar2_nonabelian D hL)).1
  · exact hSU.1
  · exact hSL.1
  · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (uc22pw_bar2_nonabelian D hL)).1

theorem uc22pw_swap (D : Data G) {L L₁ L₂ : Subgroup G} (hL : L ∈ calL D.T D.M) (h₁ : L₁ ∈ calC L)
    (h₂ : L₂ ∈ calC L) : ∃ t ∈ D.T, L₂ = uc22p20bCj t L₁ := by
  obtain ⟨K₀, hK₀, hLK₀⟩ := hL.2.2.2
  have hrange := uc22p20p_cComp_eq_range D hL hK₀ hLK₀
  have h₁c : L₁ ∈ Set.range (fun t : D.T => uc22p20bCj (t : G) K₀) := by
    rw [← hrange]; exact uc22p20e_cComp_of_calC h₁
  have h₂c : L₂ ∈ Set.range (fun t : D.T => uc22p20bCj (t : G) K₀) := by
    rw [← hrange]; exact uc22p20e_cComp_of_calC h₂
  obtain ⟨⟨s₁, hs₁⟩, rfl⟩ := h₁c
  obtain ⟨⟨s₂, hs₂⟩, rfl⟩ := h₂c
  refine ⟨s₂ * s₁⁻¹, D.T.mul_mem hs₂ (D.T.inv_mem hs₁), ?_⟩
  rw [uc22p20b_cj_cj]
  simp

theorem uc22pw_cases (hE : UC22P20gExcFacts) (D : Data G) (h1930 : H1930 D) (h20_7 : S20_7 D)
    {L : Subgroup G} (hL : L ∈ calLLow D.T D.M) {n : ℕ} (hn : NParam L n) :
    2 < n ∧
    ((CFSG.Open.IsQuasisimple (Bar2 L) ∧ (IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n)) ∨
      (CFSG.Open.IsQuasisimple (Bar2 L) ∧ (IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n)) ∨
      (∃ K K₂ : Subgroup G, ∃ t ∈ D.T, K ∈ calC L ∧ K₂ ∈ calC L ∧ K₂ ≠ K ∧ L = K ⊔ K₂ ∧
        K₂ = uc22p20bCj t K ∧ (IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n ∨ (n = 3 ∧ IsSU3 (Bar2 K) 3)))) := by
  have hLc : L ∈ calL D.T D.M := hL.prop
  have h3 : 3 ≤ n := uc22p20g_three_le_of_nparam hE h20_7 h1930 hL hn
  refine ⟨by omega, ?_⟩
  rcases hn with hsingle | ⟨L₁, L₂, hL₁, hL₂, hsup, hne, hall⟩
  · have hq := uc22pw_isQuasisimple_of_single D hLc hsingle
    rcases hsingle with h | h | h | h | h
    · exact Or.inl ⟨hq, Or.inl h⟩
    · exact Or.inl ⟨hq, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨hq, Or.inr (Or.inr h)⟩
    · exact Or.inr (Or.inl ⟨hq, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨hq, Or.inr h⟩)
  · obtain ⟨t, htT, ht⟩ := uc22pw_swap D hLc hL₁ hL₂
    exact Or.inr (Or.inr ⟨L₁, L₂, t, htT, hL₁, hL₂, hne.symm, hsup, ht, hall L₁ (by simp)⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22
