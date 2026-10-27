module

public import CFSG.Quasithin.Background.C35Claim
public import CFSG.Quasithin.Background.C31SporL

public section

namespace CFSG.Quasithin.C35

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

omit [Finite G] in
theorem isPGroup_center (hZ : IsPGroup 2 ↥(centerOf K)) : IsPGroup 2 ↥(Subgroup.center ↥K) :=
  hZ.of_equiv ((MulEquiv.subgroupCongr (map_center_eq_centerOf K)).symm.trans
    (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).symm)

theorem Y_le_M (hC129 : ASC129Statement G) (hC111 : ASC111Statement G)
    (hC19 : ASC19Statement G) (hA3 : A3Orbits G) (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) {Y : Subgroup G} (hYK : Y ≤ K)
    (hM0 : conjClosure L M = perfectCore Y) : Y ≤ M := by
  obtain ⟨T, hT, hRT⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge h.le_M h.pgroup
  rw [← c2_12 hC129 hC111 hC19 hA3 h hT hRT]
  refine le_inf (hYK.trans hK.1) ?_
  rw [hM0]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le Y)).mp (perfectCore_normal Y)

omit [Finite G] in
theorem isParabolic2_inf {Y : Subgroup G} (hYM : Y ≤ M) (hpar : IsParabolic2 K Y) :
    IsParabolic2 K (M ⊓ K) := by
  obtain ⟨hYK, S, hS, hN⟩ := hpar
  exact ⟨inf_le_right, S, hS, hN.trans (le_inf hYM hYK)⟩

omit [Finite G] in
theorem inf_eq_of_isMaxParabolic2 {Y : Subgroup G} (hYM : Y ≤ M) (hKM : ¬ K ≤ M)
    (hmax : IsMaxParabolic2 K Y) : M ⊓ K = Y :=
  hmax.2.2 (M ⊓ K) (isParabolic2_inf hYM hmax.1)
    (fun he => hKM (by rw [← he]; exact inf_le_left)) (le_inf hYM hmax.1.1)

theorem c31Case1_of (hSp4 : SchurMult2Sp4) (hK : CFSG.Open.IsComponentOf K H)
    (hZ : IsPGroup 2 ↥(centerOf K)) {Y : Subgroup G} (hYM : Y ≤ M) (hKM : ¬ K ≤ M)
    (hM0 : conjClosure L M = perfectCore Y) (h1 : C35Concl1 K Y (conjClosure L M) V) :
    C31Case1 H R M L V K := by
  obtain ⟨n, hrank, hmax, hpsl, hnat⟩ := h1
  have hMK := inf_eq_of_isMaxParabolic2 hYM hKM hmax
  refine ⟨n, hrank, by rw [hMK]; exact hmax, by rw [hMK]; exact hM0, hpsl, ?_⟩
  rcases hnat with hnat | ⟨hsp, hnat⟩
  · exact Or.inl hnat
  · refine Or.inr ⟨?_, hnat⟩
    have hc := hSp4 n ↥K hK.2.2 (isPGroup_center hZ) hsp
    exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot) hsp

omit [Finite G] in
theorem c31Case2_of_concl2a {n : ℕ} (hn : n = 4 ∨ n = 5) {Y : Subgroup G} (hYM : Y ≤ M)
    (hKM : ¬ K ≤ M) (hM0 : conjClosure L M = perfectCore Y)
    (h2 : C35Concl2a n K Y (conjClosure L M) V) : C31Case2 H R M L V K := by
  obtain ⟨hpsl, hmax, hpsl', hV, hnat⟩ := h2
  have hMK := inf_eq_of_isMaxParabolic2 hYM hKM hmax
  exact ⟨n, hn, hpsl, by rw [hMK]; exact hmax.1, by rw [hMK]; exact hM0,
    Or.inl ⟨hpsl', hV, hnat⟩⟩

omit [Finite G] in
theorem c31Case2_of_concl2b {Y : Subgroup G} (hYM : Y ≤ M) (hpar : IsParabolic2 K Y)
    (hKM : ¬ K ≤ M) (h2 : C35Concl2b K Y (conjClosure L M) V) : C31Case2 H R M L V K := by
  obtain ⟨hpsl, hext, hnat, hQ⟩ := h2
  have hpar' := isParabolic2_inf hYM hpar
  have heq := hQ (M ⊓ K) hpar' (le_inf hYM hpar.1)
    (fun he => hKM (by rw [← he]; exact inf_le_left))
    (inf_le_left.trans (le_normalizer_conjClosure L M))
  exact ⟨5, Or.inr rfl, hpsl, hpar', heq.symm, Or.inr ⟨rfl, hext, hnat⟩⟩

theorem eq_conjClosure_of_modO2 (hA3 : A3Orbits G) (h : HypC28 H R M L V)
    (hq : C31Spor.QuasiNoTwo (ModO2 (conjClosure L M))) : L = conjClosure L M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine C31Spor.eq_conjClosure_of_quotient hA3 h (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_ hq
  rw [QuotientGroup.ker_mk']
  exact CFSG.pCore_isPGroup

omit [Finite G] in
theorem not_prime_card_psl22 {n : ℕ} {Y : Type} [Group Y] (h : IsPSL 2 2 n Y) :
    ¬ (Nat.card Y).Prime := by
  have hn : 2 ≤ n := by
    obtain ⟨⟨-, hn1, -, h22, -⟩, -⟩ := h
    by_contra hlt
    exact h22 (by rw [show n = 1 by omega]; rfl)
  rw [C48.card_psl_two_two h]
  intro hp
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have h16 : 16 ≤ 4 ^ n := (Nat.pow_le_pow_right (by norm_num) hn : 4 ^ 2 ≤ 4 ^ n)
  rcases hp.eq_one_or_self_of_dvd 2 (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _) with
    h2 | h2
  · omega
  · have : 4 * 15 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h4 (by omega)
    omega

theorem eq_conjClosure_of_isB48TwoModule (hA3 : A3Orbits G) (h : HypC28 H R M L V)
    (hB : IsB48TwoModule (conjClosure L M) V) : L = conjClosure L M := by
  obtain ⟨hVM, hVe, -, -, -, -, α, hαs, hαk, -⟩ := hB
  refine C31Spor.eq_conjClosure_of_quotient hA3 h α hαs ?_
    (C31Spor.quasiNoTwo_L32 (C48.isPSL_of_mulEquiv_statedSL (n := 3) le_rfl (MulEquiv.refl _)))
  rw [hαk]
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  exact hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVM).symm

theorem isPSL_four_two_of_isAlt_eight {X : Type} [Group X] (h : IsAlt 8 X) : IsPSL 4 2 1 X := by
  rcases (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff X).2 h with
    ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact hm
  all_goals exact absurd h0 (by decide)

theorem c31LieStep_of (hInsp : InspC35) (hC41 : ASC41Statement G)
    (h22one : ASC22One G) (h22two : ASC22Two G) (h22four : ASC22Four G) (hA3 : A3Orbits G)
    (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hInsp33 : InspC33) (hSp4 : SchurMult2Sp4) (hL42 : SchurMult2L42) (hL52 : SchurMult2L52) :
    C31LieStep G := by
  intro H R M L V K h hK hb ht
  have hHN := C31B.le_normalizer h36 h38 hA3 hSch hInsp33 h hK
  have hM0 := eq_perfectCore_Y hC41 h22one h22two h22four hA3 hInsp h hK hHN hb ht
  have hD := c35Data_of h22two h22four h hK hHN hb ht hM0
  have hYM := Y_le_M hC129 hC111 hC19 hA3 h hK inf_le_left hM0
  have hKM : ¬ K ≤ M := c2_10_two h K hK
  have hZ := isPGroup_center hb.2.2
  have hsmall := hInsp.small G _ _ _ _ hD
  have hc1 : C35Concl1 K (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G))
      (conjClosure L M) V → L = conjClosure L M ∧
      (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case10 H R M L V K) := fun h1 => by
    obtain ⟨n, -, -, hpsl, -⟩ := id h1
    exact ⟨eq_conjClosure_of_modO2 hA3 h
        (C31Spor.quasiNoTwo_of_isPSL hpsl (not_prime_card_psl22 hpsl)),
      Or.inl (c31Case1_of hSp4 hK hb.2.2 hYM hKM hM0 h1)⟩
  have hc45 : (IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
      IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K)) → L = conjClosure L M ∧
      (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case10 H R M L V K) := by
    intro h45
    by_cases hZb : Subgroup.center ↥K = ⊥
    · rcases hInsp.l45 G _ _ _ _ hD hZb h45 with ⟨n, hn, h2a⟩ | h2b
      · refine ⟨eq_conjClosure_of_modO2 hA3 h ?_,
          Or.inr (Or.inl (c31Case2_of_concl2a hn hYM hKM hM0 h2a))⟩
        rcases hn with rfl | rfl
        · exact C31Spor.quasiNoTwo_L32 h2a.2.2.1
        · exact C31Spor.quasiNoTwo_L42 h2a.2.2.1
      · exact ⟨C31Spor.eq_conjClosure_of_isExt hA3 h (fun h => C48Spor.isPGroup_of_isE2 h)
          (fun h => C31Spor.quasiNoTwo_L32 h) h2b.2.1,
          Or.inr (Or.inl (c31Case2_of_concl2b hYM hD.parabolic hKM h2b))⟩
    · have h4 : IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) := by
        rcases h45 with h4 | h8 | h5
        · exact h4
        · exact isPSL_four_two_of_isAlt_eight h8
        · exact absurd (hL52 ↥K hK.2.2 hZ h5) hZb
      have hc2 : Nat.card ↥(Subgroup.center ↥K) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp (hL42 ↥K hK.2.2 hZ h4) with h1 | h2
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZb
        · exact h2
      have h10 := hInsp.a8cover G _ _ _ _ hD hc2 (Or.inl h4)
      exact ⟨eq_conjClosure_of_isB48TwoModule hA3 h h10.2.2,
        Or.inr (Or.inr ⟨h10.1, h10.2.1, h10.2.2⟩)⟩
  unfold C31Lie2Types at ht
  rcases ht with h5 | h6 | h8 | (⟨f, ⟨hf, h2⟩ | ⟨hf, h3⟩ | ⟨hf, hu⟩ | ⟨hf, hsp⟩ | ⟨hf, hg⟩ |
      ⟨hf, hd⟩ | ⟨hfo, hf3, hf4⟩ | ⟨hfo, hf3, hsz⟩⟩ | htits) | ⟨n, hn, hpsl⟩
  · exact (hsmall (Or.inr (Or.inl h5))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inl h6)))).elim
  · exact hc45 (Or.inr (Or.inl h8))
  · exact (hsmall (Or.inl ⟨f, Or.inl ⟨hf, h2⟩⟩)).elim
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inl h3))))).elim
    · exact hc1 (hInsp.l3 G _ _ _ _ hD f hf2 h3)
  · exact (hsmall (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hu⟩)⟩)).elim
  · exact hc1 (hInsp.sp4 G _ _ _ _ hD f hf hsp)
  · exact hc1 (hInsp.g2 G _ _ _ _ hD f hf hg)
  · exact hc1 (hInsp.d4 G _ _ _ _ hD f hf hd)
  · exact hc1 (hInsp.f4 G _ _ _ _ hD f hfo hf3 hf4)
  · exact (hsmall (Or.inl ⟨f, Or.inr (Or.inr ⟨hfo, hf3, hsz⟩)⟩)).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr htits))))).elim
  · rcases hn with rfl | rfl
    · exact hc45 (Or.inl hpsl)
    · exact hc45 (Or.inr (Or.inr hpsl))

end CFSG.Quasithin.C35
