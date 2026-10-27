module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosure
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open Subgroup CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)
open CFSG.LocalAnalysis.RankThreeUC (twoLocalClosure)

variable {G : Type} [Group G] [Finite G]

theorem groupPRank_eq_pRank (p : ℕ) (E : Subgroup G) :
    CFSG.pRank p E = CFSG.Open.pRank p E := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]

theorem exists_maxLocal_mem_sigma {p : ℕ} (hp : p ∈ uniqueFourBeta G) :
    ∃ M : Subgroup G, uniqueFourIsMaxTwoLocal M ∧ p ∈ uniqueFourSigma M := by
  obtain ⟨B, hB⟩ := CFSG.PreuniquenessRankFour.Helpers.betaFour_has_bmax (G := G) hp
  obtain ⟨U, hU1, hU2, hBU⟩ := hB.2.2
  obtain ⟨M, hNM, hM⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal (G := G)
    (H := Subgroup.normalizer (U : Set G)) ⟨U, hU1, hU2, rfl⟩
  refine ⟨M, hM, ?_⟩
  exact ⟨hp, B, hB, hBU.trans hNM⟩

theorem ne_top_of_uniqueFourIsMaxTwoLocal (hS : Standing4 G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) : M ≠ ⊤ := by
  have := hS.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1

theorem twoLocalClosure_le_of_uniqueFour (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ uniqueFourSigma M) {E : Subgroup G}
    (hEM : E ≤ M) (hE2 : 2 ≤ pRank p E) : twoLocalClosure E ≤ M := by
  have hpp : p.Prime := hp.1.1
  rw [groupPRank_eq_pRank] at hE2
  refine iSup₂_le fun H hH => ?_
  refine (hU M hM ⟨p, hp⟩).2 H hH.1 ⟨p, hp, ?_⟩
  exact hE2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hpp (le_inf hH.2 hEM))

theorem not_uniqueFour_of_closure (hS : Standing4 G)
    (hcl : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ E S₀ : Subgroup G, IsElemAbelian p E →
      S₀ ≠ ⊥ → IsPGroup 2 S₀ → E ≤ normalizer (S₀ : Set G) → twoLocalClosure E = ⊤) :
    ¬ uniqueFourUnique G := by
  intro hU
  obtain ⟨p, hp⟩ := CFSG.PreuniquenessRankFour.Helpers.betaFour_nonempty (G := G) hS.rank
  have hpb : p ∈ uniqueFourBeta G := hp
  have hpp : p.Prime := hpb.1
  have hp2 : p ≠ 2 := hpb.2.1
  obtain ⟨M, hM, hpM⟩ := exists_maxLocal_mem_sigma hpb
  obtain ⟨B, hB, hBM⟩ := hpM.2
  obtain ⟨hBel, hBcard, U, hU0, hU2, hBU⟩ := hB
  have hrank : 2 ≤ pRank p B := by
    rw [groupPRank_eq_pRank]
    have h4 : 4 ≤ uniqueFourTwoLocalRank p G := hpb.2.2.2
    have hle : uniqueFourTwoLocalRank p G ≤ CFSG.Open.pRank p B :=
      CFSG.SectionRank.le_pRank hpp.one_lt le_rfl hBel hBcard
    omega
  have hBtop : twoLocalClosure B = ⊤ := hcl p hpp hp2 B U hBel hU0 hU2 hBU
  have hle := twoLocalClosure_le_of_uniqueFour hU hM hpM hBM hrank
  rw [hBtop] at hle
  exact ne_top_of_uniqueFourIsMaxTwoLocal hS hM (top_le_iff.mp hle)

theorem exists_sylow_le_of_uniqueFour (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ uniqueFourSigma M) :
    ∃ P : Sylow p G, (P : Subgroup G) ≤ M ∧ uniqueFourGamma p (P : Subgroup G) ≤ M := by
  obtain ⟨_, _, _, P, hPM, hG, _⟩ := (hU M hM ⟨p, hp⟩).1 p hp
  exact ⟨P, hPM, hG⟩

theorem openPRank_map_aut (p : ℕ) (H : Subgroup G) (e : G ≃* G) :
    CFSG.Open.pRank p (H.map e.toMonoidHom) = CFSG.Open.pRank p H := by
  have step : ∀ (K : Subgroup G) (f : G ≃* G) (k : ℕ),
      (∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k) →
        ∃ E : Subgroup G, E ≤ K.map f.toMonoidHom ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
    rintro K f k ⟨E, hEK, hE, hc⟩
    exact ⟨E.map f.toMonoidHom, Subgroup.map_mono hEK,
      CFSG.SectionRank.isElemAbelian_map hE f.toMonoidHom,
      by rw [Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective, hc]⟩
  have hback : (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
    ext x
    simp
  unfold CFSG.Open.pRank
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hk
    obtain ⟨E, hEK, hE, hc⟩ := step _ e.symm k hk
    rw [hback] at hEK
    exact ⟨E, hEK, hE, hc⟩
  · intro hk
    exact step H e k hk

theorem glbCore_le_of {p k : ℕ} {P X : Subgroup G}
    (h : ∀ Q : Subgroup G, Q ≤ P → k ≤ CFSG.Open.pRank p Q →
      Subgroup.normalizer (Q : Set G) ≤ X) :
    GLBCore p k P ≤ X := by
  unfold GLBCore
  apply sSup_le
  rintro N ⟨Q, hQ, hk, rfl⟩
  exact h Q hQ hk

theorem normalizer_le_glbCore {p k : ℕ} {P Q : Subgroup G} (hQ : Q ≤ P)
    (hk : k ≤ CFSG.Open.pRank p Q) :
    Subgroup.normalizer (Q : Set G) ≤ GLBCore p k P := by
  unfold GLBCore
  exact le_sSup ⟨Q, hQ, hk, rfl⟩

theorem glbCore_map_aut (p k : ℕ) (P : Subgroup G) (e : G ≃* G) :
    GLBCore p k (P.map e.toMonoidHom) = (GLBCore p k P).map e.toMonoidHom := by
  apply le_antisymm
  · apply glbCore_le_of
    intro Q hQ hk
    have hQe : (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
      ext x
      simp
    have hPe : (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
      ext x
      simp
    have hQ0 : Q.map e.symm.toMonoidHom ≤ P := by
      have h : Q.map e.symm.toMonoidHom ≤ (P.map e.toMonoidHom).map e.symm.toMonoidHom :=
        Subgroup.map_mono hQ
      rwa [hPe] at h
    have hk0 : k ≤ CFSG.Open.pRank p (Q.map e.symm.toMonoidHom) := by
      rw [← openPRank_map_aut p (Q.map e.symm.toMonoidHom) e, hQe]
      exact hk
    have hN : Subgroup.normalizer (Q : Set G) =
        (Subgroup.normalizer ((Q.map e.symm.toMonoidHom : Subgroup G) : Set G)).map
          e.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq, hQe]
    rw [hN]
    exact Subgroup.map_mono (normalizer_le_glbCore hQ0 hk0)
  · rw [Subgroup.map_le_iff_le_comap]
    apply glbCore_le_of
    intro Q hQ hk
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
    have hQ' : Q.map e.toMonoidHom ≤ P.map e.toMonoidHom := Subgroup.map_mono hQ
    exact normalizer_le_glbCore hQ' (by rw [openPRank_map_aut]; exact hk)

theorem uniqueFourGamma_map_conj (p : ℕ) (P : Subgroup G) (g : G) :
    uniqueFourGamma p (P.map (MulAut.conj g).toMonoidHom) =
      (uniqueFourGamma p P).map (MulAut.conj g).toMonoidHom := by
  unfold uniqueFourGamma
  exact glbCore_map_aut p 2 P (MulAut.conj g : G ≃* G)

theorem not_uniqueFour_of_gamma_eq_top (hS : Standing4 G) {p : ℕ} (hp : p ∈ uniqueFourBeta G)
    (P : Sylow p G) (hP : uniqueFourGamma p (P : Subgroup G) = ⊤) : ¬ uniqueFourUnique G := by
  intro hU
  have hpp : p.Prime := hp.1
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨M, hM, hpM⟩ := exists_maxLocal_mem_sigma hp
  obtain ⟨P', -, hΓP'⟩ := exists_sylow_le_of_uniqueFour hU hM hpM
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have hP'eq : (P' : Subgroup G) = (P : Subgroup G).map (MulAut.conj g : G ≃* G).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hΓ : uniqueFourGamma p (P' : Subgroup G) = ⊤ := by
    rw [hP'eq, uniqueFourGamma_map_conj, hP]
    ext x
    refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
    exact Subgroup.mem_map.mpr ⟨(MulAut.conj g⁻¹ : G ≃* G) x, Subgroup.mem_top _, by
      (simp [MulAut.conj_apply]; group)⟩
  rw [hΓ] at hΓP'
  exact ne_top_of_uniqueFourIsMaxTwoLocal hS hM (top_le_iff.mp hΓP')

theorem closure_hyp_of_mulEquiv {H : Type} [Group H] [Finite H] (e : G ≃* H)
    (hcl : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ E S₀ : Subgroup H, IsElemAbelian p E →
      S₀ ≠ ⊥ → IsPGroup 2 S₀ → E ≤ normalizer (S₀ : Set H) → twoLocalClosure E = ⊤) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ E S₀ : Subgroup G, IsElemAbelian p E →
      S₀ ≠ ⊥ → IsPGroup 2 S₀ → E ≤ normalizer (S₀ : Set G) → twoLocalClosure E = ⊤ := by
  intro p hp hp2 E S₀ hE hS₀ hS₀2 hEN
  have hT : twoLocalClosure (E.map e.toMonoidHom) = ⊤ :=
    hcl p hp hp2 (E.map e.toMonoidHom) (S₀.map e.toMonoidHom)
      (CFSG.SectionRank.isElemAbelian_map hE e.toMonoidHom)
      (fun h => hS₀ (by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [h, Subgroup.map_bot]))
      (IsPGroup.map hS₀2 e.toMonoidHom)
      ((Subgroup.map_mono hEN).trans (Subgroup.map_equiv_normalizer_eq S₀ e).le)
  have hle := CFSG.LocalAnalysis.RankThreeUC.map_twoLocalClosure_le e.symm (E.map e.toMonoidHom)
  have hEE : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    ext x
    simp
  rw [hEE] at hle
  rw [eq_top_iff]
  intro x _
  exact hle (by
    rw [hT]
    exact Subgroup.mem_map.mpr ⟨e x, Subgroup.mem_top _, by simp⟩)

end CFSG.LocalAnalysis.UniqueFourCatalog
