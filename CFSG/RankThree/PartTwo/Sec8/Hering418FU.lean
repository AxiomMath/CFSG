module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FCore
public import CFSG.RankThree.PartTwo.Sec8.Hering418FUFix
public import CFSG.RankThree.PartTwo.Sec8.Hering418FSL
public import CFSG.RankThree.PartTwo.Sec8.Hering418FSU
public import CFSG.RankThree.PartTwo.Sec8.Hering418FUOT

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian ordTwistedA)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField)

section U


theorem exists_fixed_order_four_psu {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    (hq : 2 < 2 ^ m) (hmo : Odd m) {α : MulAut (unitaryPSU h 3)}
    (hα : (KFacts.stdPinnedPSU3 h).HasKind α .field) (hα3 : α ^ 3 = 1) :
    ∃ u : unitaryPSU h 3, α u = u ∧ u ^ 4 = 1 ∧ u ^ 2 ≠ 1 := by
  have hD : α ∉ (KFacts.psuConj h).range :=
    (KFacts.stdPinnedPSU3_separated h).not_mem_inndiag_of_isField hα
  obtain ⟨σ, hσ, H, hαH⟩ := KFacts.unitary_order_three_field_descent hq α hα3 hD
  obtain ⟨f₀, hf, hf₀, hcard⟩ := KFacts.exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData 2 f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := KFacts.bar_coe_fixedField h hf h₀
  have hf₀o : Odd f₀ := by
    rw [hf] at hmo
    exact (Nat.odd_mul.mp hmo).2
  obtain ⟨u0, hu04, hu02⟩ := Item8KFacts2Proof.exists_unitarySU_pow_four h₀ hf₀o
  set v : unitaryPSU h 3 := fixedCoreHomU h h₀ hbar u0 with hv
  have hvfix : KFacts.psuField h σ v = v := fixedCoreU_fixed ⟨u0, rfl⟩
  refine ⟨KFacts.psuConj h H v, ?_, ?_, ?_⟩
  · rw [hαH]
    change (KFacts.psuConj h H) ((KFacts.psuField h σ) ((KFacts.psuConj h H)⁻¹
      (KFacts.psuConj h H v))) = KFacts.psuConj h H v
    rw [MulAut.inv_apply_self, hvfix]
  · rw [← map_pow, hv, ← map_pow, hu04, map_one, map_one]
  · intro h2
    rw [← map_pow] at h2
    have h3 : v ^ 2 = 1 := (KFacts.psuConj h H).injective (h2.trans (map_one _).symm)
    rw [hv, ← map_pow] at h3
    have h4 : KFacts.suIncl h h₀ hbar (u0 ^ 2) ∈ unitaryScalars h 3 := by
      rw [← ker_unitaryProj, MonoidHom.mem_ker]
      exact h3
    have h5 := pow_three_eq_one_of_mem_unitaryScalars h h4
    have h6 : KFacts.suIncl h h₀ hbar (u0 ^ 2) ^ 2 = 1 := by
      rw [← map_pow, ← pow_mul, show 2 * 2 = 4 from rfl, hu04, map_one]
    have h7 : KFacts.suIncl h h₀ hbar (u0 ^ 2) = 1 := by
      calc KFacts.suIncl h h₀ hbar (u0 ^ 2) =
          KFacts.suIncl h h₀ hbar (u0 ^ 2) ^ 3 * (KFacts.suIncl h h₀ hbar (u0 ^ 2) ^ 2)⁻¹ := by
            group
        _ = 1 := by rw [h5, h6]; simp
    exact hu02 (KFacts.suIncl_injective h h₀ hbar (h7.trans (map_one _).symm))

theorem dichotomy_uThreeSixOdd {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hX : IsUThreeSixOdd (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), innBar L ≤ N ∧
      (∀ F : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), IsElemAbelian 3 F → F ≤ N →
        Nat.card F ≤ 9) ∧
      ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)), x ^ 3 = 1 →
        (rho L ⟨x, hx⟩ ∈ N ∧ ¬ (KFacts.InducesStdKind L x .field ∨
            KFacts.InducesStdKind L x .graphField)) ∨
          (rho L ⟨x, hx⟩ ∉ N ∧ (KFacts.InducesStdKind L x .field ∨
            KFacts.InducesStdKind L x .graphField)) := by
  obtain ⟨k, hk, ⟨m, rfl⟩, ho, ⟨e₁⟩⟩ := hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3m : 1 ≤ 3 * m := by omega
  have hU := Sec4.unitaryFieldData_galoisField 2 (3 * m) h3m
  have hq2 : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  set E : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU hU 3 :=
    e₁.trans (Sec4.projSUEquivUnitaryPSU 2 (3 * m) hU) with hE
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd E.symm (KFacts.center_unitaryPSU_three_eq_bot hU hq2)
  have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = ordTwistedA 2 (2 ^ (3 * m)) :=
    (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two h3m)
  have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ 3 * m) e₁
  have := hU.finite
  have h3 : (3 : GaloisField 2 (2 * (3 * m))) ≠ 0 :=
    Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) (GaloisField.card 2 _ (by omega))
  refine ⟨(KFacts.psuConj hU).range.comap (MulAut.congr E).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    change MulAut.congr E (MulAut.conj y) ∈ (KFacts.psuConj hU).range
    rw [KFacts.congr_mulAutConj]
    exact (KFacts.stdPinnedPSU3 hU).inn_le ⟨E y, rfl⟩
  · intro F' hF' hFN
    have hle : F'.map (MulAut.congr E).toMonoidHom ≤ (KFacts.psuConj hU).range := by
      rintro _ ⟨σ, hσ, rfl⟩
      exact hFN hσ
    have := Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3
      (F'.map (MulAut.congr E).toMonoidHom) (hF'.map (MulAut.congr E).toMonoidHom) hle
    rwa [Subgroup.card_map_of_injective (MulAut.congr E).injective] at this
  · intro x hx hx3
    have hα3 : KFacts.inducedAutHom L E ⟨x, hx⟩ ^ 3 = 1 :=
      KFacts.inducedAutHom_pow_eq_one L E hx hx3
    by_cases hD : KFacts.inducedAutHom L E ⟨x, hx⟩ ∈ (KFacts.psuConj hU).range
    · left
      refine ⟨hD, ?_⟩
      have key : ∀ k' : KFacts.AutKind, k' ≠ .inner → k' ≠ .diagonal →
          ¬ KFacts.InducesStdKind L x k' := by
        intro k' h1 h2 hstd
        rcases KFacts.inducesKindPSU3_or_oddCharStdModel (m := 3 * m) ho hcard hZ hstd with
          ⟨K', _, hK', hq', e_L, hx', hkind⟩ | hO
        · have h1' : KFacts.inducedAutHom L e_L ⟨x, hx'⟩ =
              MulAut.congr (E.symm.trans e_L) (KFacts.inducedAutHom L E ⟨x, hx⟩) := by
            ext y
            simp [KFacts.inducedAutHom_apply, MulAut.congr_apply]
          have hD' : KFacts.inducedAutHom L e_L ⟨x, hx'⟩ ∈ (KFacts.psuConj hK').range := by
            rw [h1']
            exact Sec21.Item223CensusResProof.congr_mem_psuConj_range_of_eq hK' hU hq'
              (E.symm.trans e_L) hD
          exact (KFacts.stdPinnedPSU3_separated hK').not_mem_inndiag_of_hasKind hkind h1 h2 hD'
        · exact hodd hO
      rintro (h | h)
      · exact key .field (by decide) (by decide) h
      · exact key .graphField (by decide) (by decide) h
    · right
      exact ⟨hD, Or.inl (KFacts.InducesStdKind.psu3 hU hq2
        ⟨E, hx, KFacts.isField_psu3_of_pow_three_eq_one hq2 hα3 hD⟩)⟩

theorem kF418OuterOn_uThreeSixOdd : KF418OuterOn (fun X _ => IsUThreeSixOdd X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk
  obtain ⟨k, hk, ⟨m, rfl⟩, ho, ⟨e₁⟩⟩ := hl
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hβ : Sec4.InducesOuterTheta b L := by
    rcases hbk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .field) L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .graphField) L h (by decide)
  have h3m : 1 ≤ 3 * m := by omega
  have hmo : Odd m := (Nat.odd_mul.mp ho).2
  have hm1 : 1 ≤ m := by omega
  have hU := Sec4.unitaryFieldData_galoisField 2 (3 * m) h3m
  have hq2 : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd
      (e₁.trans (Sec4.projSUEquivUnitaryPSU 2 (3 * m) hU)).symm
      (KFacts.center_unitaryPSU_three_eq_bot hU hq2)
  have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = ordTwistedA 2 (2 ^ (3 * m)) :=
    (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two h3m)
  have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ 3 * m) e₁
  obtain ⟨K', _, hK', hq', e_L, hbN', hbkind⟩ : ∃ (K' : Type) (_ : Field K')
      (hK' : UnitaryFieldData 2 (3 * m) K') (_ : 2 < 2 ^ (3 * m))
      (e_L : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU hK' 3)
      (hbN' : b ∈ Subgroup.normalizer (L : Set G)),
      (KFacts.stdPinnedPSU3 hK').HasKind (KFacts.inducedAutHom L e_L ⟨b, hbN'⟩) .field := by
    rcases hbk with h | h
    · rcases KFacts.inducesKindPSU3_or_oddCharStdModel (m := 3 * m) ho hcard hZ h with
        ⟨K', _, hK', hq', e_L, hx', hkind⟩ | hO
      · exact ⟨K', inferInstance, hK', hq', e_L, hx', hkind⟩
      · exact (hodd hO).elim
    · rcases KFacts.inducesKindPSU3_or_oddCharStdModel (m := 3 * m) ho hcard hZ h with
        ⟨K', _, hK', -, hkK⟩ | hO
      · exact (KFacts.not_inducesKindPSU3_graphField hK' hkK).elim
      · exact (hodd hO).elim
  have hDb : KFacts.inducedAutHom L e_L ⟨b, hbN'⟩ ∉ (KFacts.psuConj hK').range :=
    (KFacts.stdPinnedPSU3_separated hK').not_mem_inndiag_of_isField hbkind
  have hb3' : KFacts.inducedAutHom L e_L ⟨b, hbN'⟩ ^ 3 = 1 :=
    KFacts.inducedAutHom_pow_eq_one L e_L hbN' hb3
  obtain ⟨σ, hσ, H, hβH⟩ := KFacts.unitary_order_three_field_descent hq' _ hb3' hDb
  let e'' : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU hK' 3 :=
    e_L.trans (KFacts.psuConj hK' H)⁻¹
  have hβ'' : MulAut.congr e'' c.beta = KFacts.psuField hK' σ := by
    have h1 : MulAut.congr e'' c.beta =
        MulAut.congr (KFacts.psuConj hK' H)⁻¹ (KFacts.inducedAutHom L e_L ⟨b, hbN'⟩) :=
      KFacts.congr_trans e_L _ _
    rw [h1, hβH, congr_eq_mul_mul_inv]
    group
  obtain ⟨f₀, hf, hf₀, hcardσ⟩ := KFacts.exists_card_fixedField_of_orderOf_eq_three hK' hσ
  have hf₀m : f₀ = m := by omega
  have h₀ : UnitaryFieldData 2 m (fixedField σ) := ⟨hK'.prime, hm1, by rw [hcardσ, hf₀m]⟩
  haveI : Finite (fixedField σ) := h₀.finite
  have hbar := KFacts.bar_coe_fixedField hK' (σ := σ) (f₀ := m) rfl h₀
  obtain ⟨Q, hQfix, hQcomm, ⟨εQ⟩⟩ :=
    exists_core_of_fieldAutU (h := hK') (h₀ := h₀) (hbar := hbar) e'' c.beta hβ''
  have hQC : Q ≤ Sec8.barCentralizer (Subgroup.zpowers b) L := fun x hx =>
    (KFacts.mem_barCentralizer_zpowers_iff c.hbL x).mpr (hQfix x hx)
  have hQcomm' : ⁅Sec8.barCentralizer (Subgroup.zpowers b) L,
      Sec8.barCentralizer (Subgroup.zpowers b) L⁆ ≤ Q :=
    Subgroup.commutator_le.mpr fun y hy z hz => hQcomm y z
      ((KFacts.mem_barCentralizer_zpowers_iff c.hbL y).mp hy)
      ((KFacts.mem_barCentralizer_zpowers_iff c.hbL z).mp hz)
  by_cases hm1' : m = 1
  ·
    exfalso
    subst hm1'
    have hcardF0 : Nat.card (fixedField σ) = (2 ^ 1) ^ 2 := by
      rw [hcardσ, hf₀m]
      norm_num
    have hsolv : Group.IsSolvable (unitarySU 2 1 (fixedField σ) 3) :=
      CFSG.Quasithin.isSolvable_statedSU_one hcardF0
    haveI hfs : Group.IsSolvable ↥(fixedCoreU hK' h₀ hbar) :=
      isSolvable_fixedCoreU (h := hK') (h₀ := h₀) (hbar := hbar) hsolv
    haveI hQsolv : Group.IsSolvable ↥Q :=
      Group.isSolvable_of_isSolvable_injective (f := εQ.symm.toMonoidHom) εQ.symm.injective
    have hle := imageModTheta_le_barCentralizer_of_le c.hbL c.hb3 c.hKL c.hKb
    haveI hP := isPerfect_imageModTheta hK
    have hcomm : ⁅Sec8.imageModTheta L K, Sec8.imageModTheta L K⁆ = Sec8.imageModTheta L K :=
      Subgroup.commutator_eq_self
    have hleQ : Sec8.imageModTheta L K ≤ Q := by
      rw [← hcomm]
      exact (Subgroup.commutator_mono hle hle).trans hQcomm'
    haveI : Group.IsSolvable ↥(Sec8.imageModTheta L K) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hleQ)
        (Subgroup.inclusion_injective hleQ)
    haveI : Nontrivial ↥(Sec8.imageModTheta L K) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr (imageModTheta_ne_bot c.hKL hKq)
    have := IsSolvable.commutator_lt_top_of_nontrivial (Sec8.imageModTheta L K)
    rw [Group.IsPerfect.commutator_eq_top] at this
    exact lt_irrefl _ this
  have hm3 : 3 ≤ m := by
    obtain ⟨j, hj⟩ := hmo
    omega
  have hq₀ : 2 < 2 ^ m :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ m))
  haveI hQs : IsSimpleGroup ↥Q := by
    haveI := fixedCoreU_isSimpleGroup (h := hK') (h₀ := h₀) (hbar := hbar) hq' hq₀
    exact εQ.symm.isSimpleGroup
  have hQns : ¬ Group.IsSolvable ↥Q := fun hs =>
    not_isSolvable_fixedCoreU (h := hK') (h₀ := h₀) (hbar := hbar) hq' hq₀
      (Group.isSolvable_of_isSolvable_injective (f := εQ.toMonoidHom) εQ.injective)
  obtain ⟨Ψ, hΨ⟩ := c.exists_mulEquiv_of_simple_core hK hQC hQcomm' hQs hQns
  let eKU : K ⧸ aschbacherSolvableCore 3 K ≃* unitaryPSU h₀ 3 :=
    Ψ.trans (εQ.symm.trans (fixedCoreUEquivPSU (h := hK') (h₀ := h₀) (hbar := hbar) hq' hq₀))
  have hGF := Sec4.unitaryFieldData_galoisField 2 m hm1
  obtain ⟨ψ⟩ : Nonempty (fixedField σ ≃+* GaloisField 2 (2 * m)) :=
    nonempty_ringEquiv_of_card_eq (by rw [hcardσ, hf₀m, GaloisField.card 2 (2 * m) (by omega)])
  let eKP : K ⧸ aschbacherSolvableCore 3 K ≃* projSU 3 2 m :=
    eKU.trans ((Sec21.Item223CensusResProof.psuEquiv ψ hGF h₀ hq₀).trans
      (Sec4.projSUEquivUnitaryPSU 2 m hGF).symm)
  have hcardK : Nat.card (K ⧸ aschbacherSolvableCore 3 K) = ordTwistedA 2 (2 ^ m) :=
    (Nat.card_congr eKP.toEquiv).trans (KFacts.card_projSU_three_two hm1)
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd eKU.symm (KFacts.center_unitaryPSU_three_eq_bot h₀ hq₀)
  have hoddK := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ m) eKP
  obtain ⟨K'', _, hK'', hq'', eK, haK', hkindK⟩ :
      ∃ (K'' : Type) (_ : Field K'') (hK'' : UnitaryFieldData 2 m K'') (_ : 2 < 2 ^ m)
        (eK : K ⧸ aschbacherSolvableCore 3 K ≃* unitaryPSU hK'' 3)
        (haK' : a ∈ Subgroup.normalizer (K : Set G)),
        (KFacts.stdPinnedPSU3 hK'').HasKind (KFacts.inducedAutHom K eK ⟨a, haK'⟩) .field := by
    rcases KFacts.inducesKindPSU3_or_oddCharStdModel (m := m) hmo hcardK hZK hKa with
      ⟨K'', _, hK'', hq'', eK, hx', hkind⟩ | hO
    · exact ⟨K'', inferInstance, hK'', hq'', eK, hx', hkind⟩
    · exact (hoddK hO).elim
  obtain ⟨uK, huKfix, huK4, huK2⟩ := exists_fixed_order_four_psu hK'' hq'' hmo hkindK
    (KFacts.inducedAutHom_pow_eq_one K eK haK' ha3)
  set y : K ⧸ aschbacherSolvableCore 3 K := eK.symm uK with hy
  have hey : eK y = uK := by rw [hy]; simp
  have hyfix : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) y = y := by
    apply eK.injective
    have h1 : KFacts.inducedAutHom K eK ⟨a, c.haK⟩ (eK y) =
        eK (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) y) := by
      change MulAut.congr eK _ (eK y) = _
      simp [MulAut.congr_apply]
    rw [← h1, hey]
    exact huKfix
  have hy4 : y ^ 4 = 1 := by
    apply eK.injective
    rw [map_pow, map_one, hey]
    exact huK4
  have hy2 : y ^ 2 ≠ 1 := by
    intro h
    apply huK2
    rw [← hey, ← map_pow, h, map_one]
  let ι : K ⧸ aschbacherSolvableCore 3 K →* L ⧸ aschbacherSolvableCore 3 L :=
    Q.subtype.comp Ψ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp Ψ.injective
  set u : L ⧸ aschbacherSolvableCore 3 L := ι y with hu
  have hu4 : u ^ 4 = 1 := by rw [hu, ← map_pow, hy4, map_one]
  have hu2 : u ^ 2 ≠ 1 := by
    rw [hu, ← map_pow]
    intro h
    exact hy2 (hι (h.trans (map_one ι).symm))
  have hαu : c.alpha u = u := by
    have h1 := hΨ y
    rw [hyfix] at h1
    exact h1.symm
  have hβu : c.beta u = u := hQfix _ (Ψ y).2
  have hOTC : KFacts.OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L) :=
    (KFacts.outThreeCyclic_psu3 (h := hK') hq').of_mulEquiv e_L
  have hcomm : Commute c.beta c.alpha := c.alpha_mul_beta.symm
  obtain ⟨i, -, x, hx⟩ := hOTC c.beta c.alpha hcomm c.beta_pow_three c.alpha_pow_three hβ.2
  have hτu : (c.beta ^ i * c.alpha) u = u := by
    rw [MulAut.mul_apply, hαu]
    exact pow_apply_eq_of_apply_eq hβu i
  have hτ3 : (c.beta ^ i * c.alpha) ^ 3 = 1 := by
    rw [(hcomm.pow_left i).mul_pow, c.alpha_pow_three, mul_one, ← pow_mul, mul_comm, pow_mul,
      c.beta_pow_three, one_pow]
  have hconj : MulAut.congr e'' (c.beta ^ i * c.alpha) = MulAut.conj (e'' x) := by
    rw [← hx, KFacts.congr_mulAutConj]
  have hyy3 : (MulAut.conj (e'' x) : MulAut (unitaryPSU hK' 3)) ^ 3 = 1 := by
    rw [← hconj, ← map_pow, hτ3, map_one]
  have hyyu : e'' x * e'' u * (e'' x)⁻¹ = e'' u := by
    have h1 : MulAut.congr e'' (c.beta ^ i * c.alpha) (e'' u) = e'' u := by
      change e'' ((c.beta ^ i * c.alpha) (e''.symm (e'' u))) = e'' u
      rw [MulEquiv.symm_apply_apply, hτu]
    rw [hconj] at h1
    exact h1
  have huu4 : e'' u ^ 4 = 1 := by rw [← map_pow, hu4, map_one]
  have huu2 : e'' u ^ 2 ≠ 1 := fun h => hu2 (e''.injective (by rw [map_pow, h, map_one]))
  have hx1 : e'' x = 1 := eq_one_of_conj_fixed_psu3 hK' hq' hyy3 hyyu huu4 huu2
  have hx0 : x = 1 := e''.injective (by rw [hx1, map_one])
  have hτ1 : c.beta ^ i * c.alpha = 1 := by rw [← hx, hx0, map_one]
  apply c.hαβ (i : ℤ)
  rw [zpow_natCast, (hcomm.pow_left i).symm.eq]
  exact hτ1

theorem kF418ModelOn_uThreeSixOdd : KF418ModelOn (fun X _ => IsUThreeSixOdd X) :=
  kF418ModelOn_of_dichotomy (fun _ _ _ _ _ hl => dichotomy_uThreeSixOdd hl)
    kF418OuterOn_uThreeSixOdd

end U

end CFSG.RankThree.PartTwo.Sec8.Hering418
