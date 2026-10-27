module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmMark

public section

namespace CFSG.StandardType

namespace OmNonsplit

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Module
  QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne CFSG.LieType.Universal.Spin CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff centerQuotientEquivSelf)
open scoped MatrixGroups

theorem nonempty_commutator_equiv_SL4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K W = 6)
    (hts : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nonempty (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≃* StatedSL 4 K) := by
  obtain ⟨e⟩ := K159.Klein.exists_isometry_quadPlus_three Q hQ hd hts
  obtain ⟨hs, hp⟩ := K159.Klein.sl4_isSimpleGroup_and_perfect (K := K)
  have hρinj := transportHom_injective e
    (K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _) K159.Klein.rho_injective
  have hρmem := transportHom_mem e
    (K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _) K159.Klein.rho_mem
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set ρ := transportHom e (K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _) with hρ
  have hle : ρ.range ≤ O := by
    rintro _ ⟨g, rfl⟩
    exact hρmem g
  have hcard : Nat.card O = 2 * Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e,
      K159.Klein.card_orthogonalGroup_quadPlus_three]
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ := derived_of_index_two_model O ρ hρinj hle hcard
  have h1 : (commutator ↥O).map O.subtype = ρ.range := by
    rw [Subgroup.map_subtype_commutator, hcomm]
  let e1 : commutator ↥O ≃* ρ.range :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)
  let e2 : ρ.range ≃* Matrix.SpecialLinearGroup (Fin 4) K := (MonoidHom.ofInjective hρinj).symm
  exact ⟨e1.trans (e2.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K))⟩

theorem center_eq_bot_of_mulEquiv {F : Type} [Field F] [Finite F] [CharP F 2] {W : Type}
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    {R : QuadraticForm F W} (hR : (polarBilin R).Nondegenerate)
    (hT : ∃ U : Submodule F W, finrank F U = 3 ∧ ∀ u ∈ U, R u = 0) {G : Type} [Group G]
    (e : G ≃* ↥(orthDerived R)) : Subgroup.center G = ⊥ := by
  have h1 := Subgroup.map_center_eq e
  rw [center_orthDerived_eq_bot hR hT] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

theorem exists_lieModel_omega {F : Type} [Field F] [Finite F] [CharP F 2] {W : Type}
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] {R : QuadraticForm F W}
    (hR : (polarBilin R).Nondegenerate) (h4 : 4 ≤ finrank F W) (hns : ¬ SplitFour R) {f : ℕ}
    (hF : Nat.card F = 2 ^ f) {G : Type} [Group G]
    (e : G ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆) :
    ∃ (t : StatedLieTag) (n g : ℕ), LieModel (G ⧸ Subgroup.center G) t n 2 g ∧
      (((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ n ∧ g = f) ∨
        ((t = .PSL ∨ t = .PSU) ∧ n = 4 ∧ g = f) ∨ (t = .PSL ∧ n = 2 ∧ g = 2 * f)) := by
  classical
  have hf : 1 ≤ f := by
    have h1 := Finite.one_lt_card (α := F)
    rw [hF] at h1
    by_contra h
    have : f = 0 := by omega
    subst this
    simp at h1
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨m, hm⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo R hR
  by_cases h8 : 8 ≤ finrank F W
  · have hm4 : 4 ≤ m := by omega
    have hdim : finrank F W = 2 * m := by omega
    have hZG := center_eq_bot_of_mulEquiv hR (exists_threeSingular_of_dim R hR hm4 hdim) e
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (by omega)
      hdim with he | ⟨b, c, hirr, he⟩
    · obtain ⟨e'⟩ := he
      exact ⟨.POmegaPlus, m, f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        (centerQuotientEquivSelf hZG).symm (lieModel_of_orthDerived_plus hm4 hf hF e' e),
        Or.inl ⟨Or.inl rfl, hm4, rfl⟩⟩
    · obtain ⟨e'⟩ := he
      exact ⟨.POmegaMinus, m, f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        (centerQuotientEquivSelf hZG).symm (lieModel_of_orthDerived_minus hm4 hf hF hirr e' e),
        Or.inl ⟨Or.inr rfl, hm4, rfl⟩⟩
  · by_cases hT : ∃ U : Submodule F W, finrank F U = 3 ∧ ∀ u ∈ U, R u = 0
    ·
      have hd6 : finrank F W = 6 := by
        obtain ⟨U, hU, hUs⟩ := hT
        have := CFSG.ComponentClassification.UnbalancedCatalog.two_mul_finrank_le_of_singular hR
          hUs
        omega
      obtain ⟨κ⟩ := nonempty_commutator_equiv_SL4 R hR hd6 hT
      have hZG := center_eq_bot_of_mulEquiv hR hT e
      let φ : G ≃* ↥(StatedSL 4 F) := e.trans ((orthDerivedEquivCommutator R).symm.trans κ)
      exact ⟨.PSL, 4, f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        (centerQuotientEquivSelf hZG).symm ((lieModel_classical_iff (by decide)).mpr
          ⟨⟨Nat.prime_two, hf, by norm_num, fun hc => absurd (Prod.mk.inj hc).1 (by norm_num),
            fun hc => absurd (Prod.mk.inj hc).1 (by norm_num)⟩, F, inferInstance, inferInstance,
            hF, ⟨φ.trans statedSL4EquivStatedProj⟩⟩), Or.inr (Or.inl ⟨Or.inl rfl, rfl, rfl⟩)⟩
    ·
      have hd : finrank F W = 4 ∨ finrank F W = 6 := by omega
      have hts : ∀ U : Submodule F W, finrank F U = finrank F W / 2 → ∃ u ∈ U, R u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        rcases hd with hd | hd
        · exact hns ⟨hd, U, by omega, hcon⟩
        · exact hT ⟨U, by omega, hcon⟩
      obtain ⟨-, -, -, -, -, h4', h6'⟩ := even_minus_four_six_actual_derived_extraction R hR hd hts
      rcases hd with hd4 | hd6
      · obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, hrange, -⟩ := h4' hd4
        have : CharP E 2 := charP_two_of_algebra (K := F)
        have hEfin : Finite E := by
          have : Nat.card E = Nat.card F ^ 2 := D.card_E
          exact Nat.finite_of_card_ne_zero (by rw [this]; exact pow_ne_zero 2 Nat.card_pos.ne')
        have hE : Nat.card E = 2 ^ (2 * f) := by rw [D.card_E, hF, ← pow_mul, mul_comm]
        let φ : G ≃* Matrix.SpecialLinearGroup (Fin 2) E :=
          e.trans ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm)
        exact ⟨.PSL, 2, 2 * f, lieModel_quotient_of_SL2 hE (by omega) φ,
          Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
      · obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, hrange, -⟩ := h6' hd6
        have : CharP E 2 := charP_two_of_algebra (K := F)
        obtain ⟨f₁, h, hK, hbar⟩ := D.exists_unitaryFieldData
        have hff : f₁ = f := Nat.pow_right_injective (le_refl 2) (hK.symm.trans hF)
        subst hff
        obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv h hbar
        let φ : G ≃* StatedSU 4 (2 ^ f₁) E :=
          (e.trans ((MulEquiv.subgroupCongr hrange.symm).trans
            (MonoidHom.ofInjective hinj).symm)).trans θ
        exact ⟨.PSU, 4, f₁, lieModel_quotient_of_statedSU4 h φ,
          Or.inr (Or.inl ⟨Or.inr rfl, rfl, rfl⟩)⟩

section Marking

theorem not_ggNbrClauseFiveMarking_of_omModel {G : Type} [Group G] {K' : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hM : OmModel F K') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1)
    (hq2 : ¬ p ∣ 2 ^ f + 1) {x : G}
    (hinn : ∃ k ∈ K', ∀ l ∈ K', x⁻¹ * l * x = k⁻¹ * l * k) :
    ¬ GGNbrClauseFiveMarking p x K' := by
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  rcases hM with ⟨W, _, _, _, R, hR, h4, hns, ⟨e⟩⟩ | ⟨h4, ⟨e⟩⟩
  · obtain ⟨t, n, g, hX, hcase⟩ := exists_lieModel_omega hR h4 hns hF e
    have hdet : ∀ lab : LargeEvenLabel, markChar lab = 2 →
        MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') →
          markTag lab = t ∧ markRank lab = n ∧ markDeg lab = g := by
      intro lab hc hlab
      have hX' : LieModel (↥K' ⧸ Subgroup.center ↥K') (markTag lab) (markRank lab) 2
          (markDeg lab) := by
        have h := hlab
        unfold MarkedModel at h
        rwa [hc] at h
      rcases hcase with ⟨hs, -, -⟩ | ⟨hs | hs, rfl, -⟩ | ⟨rfl, rfl, -⟩
      · exact CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique hs hX hX'
      · subst hs
        exact CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) hX hX'
      · subst hs
        exact CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq le_rfl hX hX'
          rfl
      · exact CFSG.SeitzReduction.RankOne.sl2EvenTypeDet _ _ _ _ _ hX
          (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hX') hX'
    have hlabel : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markChar lab = 2 →
        MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') →
          (∀ c, ¬ LargeEvenHalfSplit p lab c) ∧ LargeEvenLabelAll lab (GGRawInnField p) := by
      intro lab hlab hc hX
      obtain ⟨hT, hRk, hD⟩ := hdet lab hc hX
      refine markOm_label hlab hc hp hp2 hp3 hq1 hq2 ?_
      rw [hT, hRk, hD]
      exact hcase
    exact ClNonsplit.not_ggNbrClauseFiveMarking_of_inner hp hp3 hinn
      (fun lab hlab hc hX => (hlabel lab hlab hc hX).1 _)
      (fun lab hlab hc hX => (hlabel lab hlab hc hX).2)
  ·
    have hf2 : 2 ≤ f := by
      by_contra h
      have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    set ψ' : Matrix.SpecialLinearGroup (Fin (1 + 1)) F →* G :=
      K'.subtype.comp e.symm.toMonoidHom with hψ'
    have hinj : Function.Injective ψ' := K'.subtype_injective.comp e.symm.injective
    have hrange : ψ'.range = K' := by
      ext k
      constructor
      · rintro ⟨g, rfl⟩
        exact (e.symm g).2
      · intro hk
        exact ⟨e ⟨k, hk⟩, by simp [hψ']⟩
    have hker : ψ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (1 + 1)) F) := by
      rw [(MonoidHom.ker_eq_bot_iff ψ').mpr hinj]
      exact bot_le
    have h := ClNonsplit.not_ggNbrClauseFiveMarking_sl_two hF hf2 ψ' hker hp hp2 hq1 hq2
      (hrange ▸ hinn)
    rwa [hrange] at h

end Marking

end OmNonsplit

end CFSG.StandardType
