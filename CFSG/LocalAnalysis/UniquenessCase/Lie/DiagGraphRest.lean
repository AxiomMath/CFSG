module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagGraphL3
public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagGraphSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagAssembly
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.ASVolI.ChA

theorem uc22pdiag_false_of_bender {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hB : fusionIsBenderGroup S) (hT : ∀ V : Sylow 2 S, uc22pdiag_TwoCoatoms S (V : Subgroup S)) : False := by
  obtain ⟨V⟩ := (Sylow.nonempty : Nonempty (Sylow 2 S))
  obtain ⟨Q₁, Q₂, hne, h1, h2, hN1, hN2, -⟩ := hT V
  have key : ∀ Q : Subgroup S, IsCoatom Q → normalizer (V : Set S) ≤ Q → Q = normalizer (V : Set S) :=
    fun Q hQ hN => le_antisymm
      (CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB V (le_normalizer.trans hN) hQ.1) hN
  exact hne ((key Q₁ h1 hN1).trans (key Q₂ h2 hN2).symm)

theorem uc22pdiag_false_of_U3 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hT : ∀ V : Sylow 2 S, uc22pdiag_TwoCoatoms S (V : Subgroup S)) (h7 : 2 ^ 7 ∣ Nat.card S) {n : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (e : S ≃* StatedProj (StatedSU 3 (2 ^ n) K)) : False := by
  have hn1 : 1 ≤ n := by
    by_contra h0
    obtain rfl : n = 0 := by omega
    have := Finite.one_lt_card (α := K)
    simp [hK] at this
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl : n = 1 := by omega
    have hdvd : Nat.card S ∣ Nat.card (GL (Fin 3) K) := by
      rw [Nat.card_congr e.toEquiv]
      exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq, hK] at hdvd
    have := h7.trans hdvd
    revert this
    decide
  · have hcard : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
    let e' : S ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ n)) := e
    exact uc22pdiag_false_of_bender (Or.inr (Or.inl ⟨n, hn,
      ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hcard)⟩⟩)) hT

theorem uc22pdiag_false_of_Sz {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hT : ∀ V : Sylow 2 S, uc22pdiag_TwoCoatoms S (V : Subgroup S)) (h7 : 2 ^ 7 ∣ Nat.card S) {a : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : S ≃* ↥(CFSG.Blueprint.suzukiGroup a K)) : False := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hdvd : Nat.card S ∣ Nat.card (GL (Fin 4) K) := by
      rw [Nat.card_congr e.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq, hK] at hdvd
    have := h7.trans hdvd
    revert this
    decide
  · exact uc22pdiag_false_of_bender (CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isSz (n := 2 * a + 1)
      ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨e⟩⟩) hT

theorem uc22pdiag_ClassPres_of_id {S M : Type} [Group S] [Finite S] [Group M] (e : S ≃* M) (θ : MulAut S)
    (h : ∀ x : M, MulAut.congr e θ x = x) : uc22pdiag_ClassPres S θ :=
  uc22pdiag_ClassPres_of_congr e θ (by
    rw [show MulAut.congr e θ = 1 from MulEquiv.ext h]
    exact uc22pdiag_ClassPres_one)

section Unpack

open CFSG.Blueprint (LieModel)

theorem uc22pdiag_classPres_of_innDiagField {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hT : ∀ V : Sylow 2 S, uc22pdiag_TwoCoatoms S (V : Subgroup S)) (h7 : 2 ^ 7 ∣ Nat.card S)
    {θ : MulAut S} (h : IsInnDiagFieldAut S θ) : uc22pdiag_ClassPres S θ := by
  obtain ⟨ψ₁, ψ₂, h₁, h₂, rfl⟩ := h
  refine uc22pdiag_ClassPres_mul ?_ ?_
  · rcases h₁ with ⟨x, rfl⟩ | ⟨n, K, _, _, e, c, hK, hc⟩ | ⟨n, K, _, _, e, c, hK, hc⟩
    · exact uc22pdiag_ClassPres_conj x
    · haveI : CharP K 2 := uc22pwlie_charP_two hK
      exact uc22pdiag_ClassPres_of_congr e ψ₁ (uc22pdiag_classPres_L_conj (by norm_num) c _ hc)
    · exact (uc22pdiag_false_of_U3 hT h7 hK e).elim
  · rcases h₂ with ⟨n, K, _, _, e, σ, hK, hσ⟩ | ⟨n, K, _, _, e, σ, hK, hσ⟩ | ⟨n, K, _, _, e, σ, hK, -, -⟩ |
      ⟨n, K, _, _, e, σ, hK, hσ⟩ | ⟨a, K, _, _, e, σ, hK, -⟩ | ⟨n, K, _, _, e, σ, hK, hσ⟩ |
      ⟨n, K, _, _, σq, e, σ, hK, hσq, -, -⟩ | ⟨a, K, _, _, e, σ, hK, hσ⟩ | ⟨rfl, -⟩
    · haveI : CharP K 2 := uc22pwlie_charP_two hK
      exact uc22pdiag_ClassPres_of_congr e ψ₂ (uc22pdiag_classPres_L_field (by norm_num) σ _ hσ)
    · haveI : CharP K 2 := uc22pwlie_charP_two hK
      exact uc22pdiag_ClassPres_of_congr e ψ₂ (uc22pdiag_classPres_L_field (by norm_num) σ _ hσ)
    · exact (uc22pdiag_false_of_U3 hT h7 hK e).elim
    · haveI : CharP K 2 := uc22pwlie_charP_two hK
      exact uc22pdiag_ClassPres_of_congr e ψ₂ (uc22pdiag_classPres_Sp4_field σ _ hσ)
    · exact (uc22pdiag_false_of_Sz hT h7 hK e).elim
    ·
      rcases Nat.lt_or_ge n 2 with hn | hn
      · obtain rfl : n = 1 := by
          have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          interval_cases n <;> simp_all
        obtain rfl := CFSG.ComponentClassification.UnbalancedCatalog.ringEquiv_eq_refl_of_card_two
          (by simpa using hK) σ
        refine uc22pdiag_ClassPres_of_id e ψ₂ fun x => ?_
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨g', hg', hφ⟩ := hσ g
        rw [hφ, show g' = g from Subtype.ext
          (hg'.trans (CFSG.ComponentClassification.UnbalancedCatalog.units_map_entrywise_refl_k _))]
      · have hL : LieModel S .G2 0 2 n := Or.inr (Or.inl ⟨rfl, by decide,
          ⟨Nat.prime_two, by omega, rfl, by calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩)
        exact uc22pdiag_ClassPres_of_all (uc22pdiag_all_g2 hL) hT ψ₂
    ·
      have hn1 : 1 ≤ n := by
        by_contra h0
        obtain rfl : n = 0 := by omega
        have := Finite.one_lt_card (α := K)
        simp [hK] at this
      have hL : LieModel S .trialityD4 0 2 n := Or.inr (Or.inl ⟨rfl, by decide,
        ⟨Nat.prime_two, hn1, rfl⟩, K, inferInstance, inferInstance, hK, σq, hσq, ⟨e⟩⟩)
      exact uc22pdiag_ClassPres_of_all (uc22pdiag_all_triD4 hL) hT ψ₂
    ·
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · obtain rfl := CFSG.ComponentClassification.UnbalancedCatalog.ringEquiv_eq_refl_of_card_two
          (by simpa using hK) σ
        refine uc22pdiag_ClassPres_of_id e ψ₂ fun x => ?_
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨g', hg', hφ⟩ := hσ g
        rw [hφ, show g' = g from Subtype.ext
          (hg'.trans (CFSG.LieType.Chevalley.units_map_entrywiseHom_one_ringEquiv _))]
      · have hL : LieModel S .twistedF4 0 2 (2 * a + 1) := Or.inr (Or.inr (Or.inl ⟨rfl, by decide,
          ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl, K, inferInstance, inferInstance,
          hK, ⟨e⟩⟩))
        exact uc22pdiag_ClassPres_of_all (uc22pdiag_all_twF4 hL) hT ψ₂
    · exact uc22pdiag_ClassPres_one

end Unpack

section Dvd

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem uc22pdiag_dvd_L3 {M : Type} [Group M] [Finite M] {n : ℕ} (h : LieModel M .PSL 3 2 n) (hn : 2 < n) :
    2 ^ 7 ∣ Nat.card M := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  rw [Nat.card_congr e.toEquiv]
  refine Dvd.dvd.trans ?_ (Subgroup.card_subgroup_dvd_card (projUnitriangular 3 K))
  rw [card_projUnitriangular, hK, ← pow_mul]
  exact pow_dvd_pow 2 (by omega)

theorem uc22pdiag_dvd_Sp4 {M : Type} [Group M] [Finite M] {n : ℕ} (h : LieModel M .PSp 2 2 n) (hn : 2 < n) :
    2 ^ 7 ∣ Nat.card M := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  rw [Nat.card_congr e.toEquiv]
  refine Dvd.dvd.trans ?_ (Subgroup.card_subgroup_dvd_card (SymplecticFlag.projUnipotent 2 K))
  rw [SymplecticFlag.card_projUnipotent (by norm_num), hK, ← pow_mul]
  exact pow_dvd_pow 2 (by omega)

end Dvd


section Final

open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem uc22pdiag_graph_join {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {t : StatedLieTag} {m n : ℕ}
    (hM : LieModel S t m 2 n) (hg : uc22p20sGraphShape t m n) (V : Sylow 2 S) (B : Set (MulAut S))
    (hB : ∀ β ∈ B, ∀ x, x ∈ (V : Subgroup S) ↔ β x ∈ (V : Subgroup S))
    (hinn : ∀ β ∈ B, IsInnDiagFieldAut S β) : uc22pdiag_join (V : Subgroup S) B = ⊤ := by
  obtain ⟨hn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hg
  · exact uc22pdiag_join_eq_top_of_twoClasses V (uc22pdiag_twoClasses_L3 hM V) B hB fun β hβ =>
      uc22pdiag_classPres_of_innDiagField (fun V' => (uc22pdiag_twoClasses_L3 hM V').twoCoatoms)
        (uc22pdiag_dvd_L3 hM hn) (hinn β hβ)
  · exact uc22pdiag_join_eq_top_of_twoClasses V (uc22pdiag_twoClasses_Sp4 hM V) B hB fun β hβ =>
      uc22pdiag_classPres_of_innDiagField (fun V' => (uc22pdiag_twoClasses_Sp4 hM V').twoCoatoms)
        (uc22pdiag_dvd_Sp4 hM hn) (hinn β hβ)

theorem uc22p20uGraphInput_holds : uc22p20uGraphInput := by
  intro X _ _ hqs t m n hmodel U A hA ⟨hshape, hinn⟩
  haveI : IsSimpleGroup (X ⧸ center X) := hqs.2
  let π : X →* X ⧸ center X := QuotientGroup.mk' (center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let UB : Sylow 2 (X ⧸ center X) := Sylow.mapSurjective (f := π) hπ U
  let AB : Set (MulAut (X ⧸ center X)) :=
    {θ | ∃ α ∈ A, ∀ x, θ (QuotientGroup.mk x) = QuotientGroup.mk (α x)}
  have hUB : (UB : Subgroup (X ⧸ center X)) = (U : Subgroup X).map π := rfl
  have hAB : ∀ β ∈ AB, ∀ y, y ∈ (UB : Subgroup (X ⧸ center X)) ↔ β y ∈ (UB : Subgroup _) := by
    rintro β ⟨α, hα, hβ⟩ y
    have hβ' : β = uc22pdiag_inducedAut α := by
      ext z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
      rw [hβ, uc22pdiag_inducedAut_mk]
    rw [hUB, hβ']
    exact uc22pdiag_induced_preserves α U (hA α hα) y
  have hjoin : uc22pdiag_join (UB : Subgroup (X ⧸ center X)) AB = ⊤ :=
    uc22pdiag_graph_join hmodel hshape UB AB hAB fun θ ⟨α, hα, hθ⟩ => hinn α hα θ hθ
  exact uc22pdiag_join_pullback π hπ (U : Subgroup X) AB A
    (fun α hα x => ⟨uc22pdiag_inducedAut α, ⟨α, hα, fun z => uc22pdiag_inducedAut_mk α z⟩,
      (uc22pdiag_inducedAut_mk α x).symm⟩) (hUB ▸ hjoin)

theorem uc22p20uDiagramInput_holds : uc22p20uDiagramInput :=
  uc22p20uDiagramInput_of_graph uc22p20uGraphInput_holds

end Final

end CFSG.LocalAnalysis.UniquenessCase.UC22
