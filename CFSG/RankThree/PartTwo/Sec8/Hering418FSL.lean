module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FDich
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofTransport
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofSL34
public import CFSG.RankThree.PartTwo.Sec8.Hering418FSplit

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section SL


theorem inducesKindSL_of_ringEquiv {K K' : Type} [Field K] [Field K'] [Finite K] [Finite K']
    (ψ : K' ≃+* K) {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {k : KFacts.AutKind}
    (h : KFacts.InducesKindSL 3 K' L x k) : KFacts.InducesKindSL 3 K L x k := by
  obtain ⟨e, hx, hk⟩ := h
  refine ⟨e.trans (Sec21.Item223CensusResProof.slEquiv ψ 3), hx, ?_⟩
  rw [show KFacts.inducedAutHom L (e.trans (Sec21.Item223CensusResProof.slEquiv ψ 3)) ⟨x, hx⟩ =
    MulAut.congr (Sec21.Item223CensusResProof.slEquiv ψ 3)
      (KFacts.inducedAutHom L e ⟨x, hx⟩) from KFacts.congr_trans _ _ _,
    Sec21.Item223CensusResProof.descendAut_congr]
  exact Item8ModelProof.hasKind_congr_slEquiv ψ 3 hk

theorem nonempty_ringEquiv_of_card_eq {K K' : Type} [Field K] [Field K'] [Finite K] [Finite K']
    (h : Nat.card K' = Nat.card K) : Nonempty (K' ≃+* K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype K' := Fintype.ofFinite K'
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, h])⟩

theorem dichotomy_slThreeSixEven {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hX : IsSLThreeSixEven (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), innBar L ≤ N ∧
      (∀ F : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), IsElemAbelian 3 F → F ≤ N →
        Nat.card F ≤ 9) ∧
      ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)), x ^ 3 = 1 →
        (rho L ⟨x, hx⟩ ∈ N ∧ ¬ (KFacts.InducesStdKind L x .field ∨
            KFacts.InducesStdKind L x .graphField)) ∨
          (rho L ⟨x, hx⟩ ∉ N ∧ (KFacts.InducesStdKind L x .field ∨
            KFacts.InducesStdKind L x .graphField)) := by
  obtain ⟨k, hk, ⟨m, rfl⟩, he, K, hKf, hKfin, hK, ⟨φ⟩⟩ := hX
  have hq1 : 2 ^ (3 * m) % 3 = 1 := two_pow_mod_three_of_even' he
  have hIso : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (3 * m) ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* StatedSL 3 K) := ⟨K, hKf, hKfin, hK, ⟨φ⟩⟩
  have hm3 : 3 ≤ 3 * m := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : (3 : K) ≠ 0 := Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hK
  let e' : L ⧸ aschbacherSolvableCore 3 L ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
  let φ' : MulAut (L ⧸ aschbacherSolvableCore 3 L) →* MulAut (projectiveSL 3 K) :=
    (descendAut 3 K).comp (MulAut.congr e').toMonoidHom
  have hφ' : Function.Injective φ' :=
    Sec4.descendAut_three_injective.comp (MulAut.congr e').injective
  refine ⟨(linearAutGroup 3 K).comap φ', ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    change φ' (MulAut.conj y) ∈ linearAutGroup 3 K
    simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [KFacts.congr_mulAutConj, KFacts.descendAut_conj]
    exact KFacts.innAut_le_linearAutGroup 3 K ⟨_, rfl⟩
  · intro F hF hFN
    have hle : F.map φ' ≤ linearAutGroup 3 K := by
      rintro _ ⟨σ, hσ, rfl⟩
      exact hFN hσ
    have := Sec4.card_inf_linearAutGroup_three_le h3 (hF.map φ')
    rw [inf_eq_left.mpr hle, Subgroup.card_map_of_injective hφ'] at this
    exact this
  · intro x hx hx3
    have hτ3 : descendAut 3 K (KFacts.inducedAutHom L e' ⟨x, hx⟩) ^ 3 = 1 := by
      rw [← map_pow, KFacts.inducedAutHom_pow_eq_one L e' hx hx3, map_one]
    by_cases hD : descendAut 3 K (KFacts.inducedAutHom L e' ⟨x, hx⟩) ∈ linearAutGroup 3 K
    · left
      refine ⟨hD, ?_⟩
      rintro (h | h)
      · obtain ⟨K', _, _, hK', hk'⟩ :=
          KFacts.inducesKindSL_of_inducesStdKind hm3 hq1 hIso h
        obtain ⟨ψ⟩ := nonempty_ringEquiv_of_card_eq (K := K) (K' := K') (by rw [hK', hK])
        obtain ⟨hx', hkind⟩ := (KFacts.inducesKindSL_iff L le_rfl e' x .field).mp
          (inducesKindSL_of_ringEquiv ψ hk')
        have hsep := KFacts.stdPinnedPSL_separated (K := K) (n := 3) le_rfl
        exact hsep.not_mem_inndiag_of_hasKind hkind (by decide) (by decide) hD
      · exact KFacts.not_inducesStdKind_graphField_of_isoSLThree hm3 hq1 hIso hx3 h
    · right
      exact ⟨hD, Or.inl (KFacts.InducesStdKind.sl 3 K le_rfl
        ⟨e', hx, KFacts.isField_of_pow_three_eq_one le_rfl hτ3 hD⟩)⟩

theorem kF418OuterOn_slThreeSixEven : KF418OuterOn (fun X _ => IsSLThreeSixEven X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk
  obtain ⟨k, hk, ⟨m, rfl⟩, he, F, hFf, hFfin, hF, ⟨φ⟩⟩ := hl
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hm1 : 1 ≤ m := by omega
  have hme : Even m := (Nat.even_mul.mp he).resolve_left (by decide)
  have hm2 : 2 ≤ m := by
    obtain ⟨j, hj⟩ := hme
    omega
  have hq1 : 2 ^ (3 * m) % 3 = 1 := two_pow_mod_three_of_even' he
  have hIso : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (3 * m) ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* StatedSL 3 K) := ⟨F, hFf, hFfin, hF, ⟨φ⟩⟩
  have hbF : KFacts.InducesStdKind L b .field :=
    hbk.resolve_right (KFacts.not_inducesStdKind_graphField_of_isoSLThree (by omega) hq1 hIso hb3)
  have hSL : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * m)) :=
    ⟨F, hFf, hFfin, Or.inl ⟨hF, hq1, ⟨φ⟩⟩⟩
  have hC := KFacts.isSLThreePiAt_barCentralizer_of_field hm1 hSL hb3 (Or.inl hbF)
  have hqC := KFacts.isQuasisimple_of_isSLThreePiAt_two_pow hm2 hC
  have hcardC := KFacts.card_center_of_isSLThreePiAt_two_pow hm1 hC
  have hZ : IsPGroup 3 (Subgroup.center ↥(Sec8.barCentralizer (Subgroup.zpowers b) L)) :=
    IsPGroup.of_card (n := 1) (by rw [hcardC, pow_one])
  obtain ⟨Ψ, -⟩ := c.exists_mulEquiv_barCentralizer_of_isQuasisimple hK hqC hZ
  have hcardK : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = 3 := by
    rw [card_center_congr Ψ]
    exact hcardC
  obtain ⟨K'', hK''f, hK''fin, hC''⟩ := hC
  rcases hC'' with ⟨hK'', -, ⟨ι⟩⟩ | ⟨-, hmod, -⟩
  · rcases htype with hSU | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
    · obtain ⟨F', hF'f, hF'fin, hF', ⟨ψ⟩⟩ := hSU
      have hU : UnitaryFieldData 2 (3 * n) F' :=
        ⟨Nat.prime_two, by omega, by rw [hF', ← pow_mul, mul_comm]⟩
      have hcSU := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three hU
      have hcSU' : Nat.card (StatedSU 3 (2 ^ (3 * n)) F') =
          (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1)) := by
        rw [show StatedSU 3 (2 ^ (3 * n)) F' =
          CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (3 * n) F' 3 from rfl, hcSU, mul_assoc]
      have hcSL : Nat.card (StatedSL 3 K'') =
          (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) := by
        rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
          K'').toEquiv, Sec21.Item223CensusResProof.card_SL_three, hK'']
      have h1 : Nat.card (StatedSU 3 (2 ^ (3 * n)) F') = Nat.card (StatedSL 3 K'') := by
        rw [← Nat.card_congr ψ.toEquiv, Nat.card_congr Ψ.toEquiv, Nat.card_congr ι.toEquiv]
      rw [hcSU', hcSL] at h1
      refine Item82OneProof.su3Order_ne_sl3Order_of_four_le (p := 2) (f := 3 * n) (Q := 2 ^ m)
        (m := m) Nat.prime_two (by norm_num) (by omega) rfl ?_ (by rw [← mul_assoc] at h1; exact h1)
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    · rw [Sec13.Res5Proof.center_eq_bot_of_projSL (admissible_psl (Or.inl rfl) hn) hKq ψ,
        Subgroup.card_bot] at hcardK
      omega
    · rw [Sec13.Res5Proof.center_eq_bot_of_projSL (admissible_psl (Or.inr rfl) hn) hKq ψ,
        Subgroup.card_bot] at hcardK
      omega
  · have := two_pow_mod_three_of_even' hme
    omega

theorem kF418ModelOn_slThreeSixEven : KF418ModelOn (fun X _ => IsSLThreeSixEven X) :=
  kF418ModelOn_of_dichotomy (fun _ _ _ _ _ hl => dichotomy_slThreeSixEven hl)
    kF418OuterOn_slThreeSixEven

end SL

end CFSG.RankThree.PartTwo.Sec8.Hering418
