module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommon
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonAltRk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonAltSixNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonOmRk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfOrdLn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfOrdSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfOrdOmM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Spin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord
import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L52
import CFSG.LieType.ChevTwo.Orthogonal
public import CFSG.Quasithin.Background.F918V2GDA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section Generic

private theorem s16e_two_perfect_of_commutator_top {Γ : Type*} [Group Γ] {S : Subgroup Γ}
    (h : _root_.commutator ↥S = ⊤) : ⁅S, S⁆ = S :=
  Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 h)

private theorem s16e_two_perfect_of_simple {Γ : Type*} [Group Γ] {S : Subgroup Γ}
    (hS : IsSimpleGroup ↥S) (hnp : ¬ (Nat.card ↥S).Prime) : ⁅S, S⁆ = S := by
  apply s16e_two_perfect_of_commutator_top
  haveI := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator ↥S) with h | h
  · exfalso
    haveI : IsMulCommutative ↥S := ⟨⟨fun a b => by
      have hc : ⁅a, b⁆ ∈ _root_.commutator ↥S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc⟩⟩
    exact hnp (Group.is_simple_iff_prime_card.mp hS)
  · exact h

private theorem s16e_two_not_prime_of_two_pow_dvd {N : ℕ} (h : 2 ^ 7 ∣ N) : ¬ N.Prime := by
  intro hp
  have h2 : 2 ∣ N := (dvd_pow_self 2 (by norm_num)).trans h
  have hN : N = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  subst hN
  exact absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)

private theorem s16e_two_card_inner {S : Type} [Group S] (hz : Subgroup.center S = ⊥) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) = Nat.card S := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have hxc : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut S => φ g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * x = (x * g * x⁻¹) * x := by rw [h1]
        _ = x * g := by group
    rw [hz, Subgroup.mem_bot] at hxc
    exact hxc
  unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem s16e_two_card_mulAut_dvd {S : Type} [Group S] {k : ℕ} (hz : Subgroup.center S = ⊥)
    (hk : Nat.card (Outer S) ∣ k) : Nat.card (MulAut S) ∣ k * Nat.card S := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  rw [h, s16e_two_card_inner hz]
  exact Nat.mul_dvd_mul_right hk _

theorem s16e_two_card_aut_dvd_of_le {S : Type} [Group S] [Finite S]
    (hz : Subgroup.center S = ⊥) (h : Nat.card (MulAut S) ≤ 2 * Nat.card S) :
    Nat.card (MulAut S) ∣ 2 * Nat.card S := by
  haveI : Finite (MulAut S) := Finite.of_injective (fun f : MulAut S => (f : S → S))
    DFunLike.coe_injective
  obtain ⟨d, hd⟩ := Subgroup.card_subgroup_dvd_card
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  rw [s16e_two_card_inner hz] at hd
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hApos : 0 < Nat.card (MulAut S) := Nat.card_pos
  have hd2 : d ≤ 2 := by
    rw [hd] at h
    exact Nat.le_of_mul_le_mul_left (by linarith) hSpos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    omega
  rw [hd]
  rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
  · exact ⟨2, by ring⟩
  · exact ⟨1, by ring⟩

private theorem s16e_two_center_bot_of_simple {X : Type} [Group X] (hS : IsSimpleGroup X)
    (hnp : ¬ (Nat.card X).Prime) : Subgroup.center X = ⊥ := by
  haveI := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative X := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center X := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm⟩⟩
    exact hnp (Group.is_simple_iff_prime_card.mp hS)

private theorem s16e_two_no_cube {N : ℕ} (S : Finset ℕ) (hN : N ≠ 0) (hS : N.primeFactors = S)
    (hS' : ∀ p ∈ S, p = 2 ∨ p = 3 ∨ ¬ p ^ 3 ∣ N) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 3 ∣ N := by
  intro p hp hp2 hp3 h
  have hmem : p ∈ N.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, hN⟩
  rw [hS] at hmem
  rcases hS' p hmem with h2 | h3 | h'
  · exact hp2 h2
  · exact hp3 h3
  · exact h' h

private theorem s16e_two_isOMinus_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsOMinus Y n a) : IsOMinus X n a := by
  obtain ⟨hn, K, hK, hKf, b, c, hcard, hirr, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, b, c, hcard, hirr, ⟨e.trans e'⟩⟩

private theorem s16e_two_ln_not_prime {X : Type} [Group X] {m : ℕ} (hm3 : 3 ≤ m)
    (hLm : IsLn X m 1) : ¬ (Nat.card X).Prime := by
  obtain ⟨h3, h4, h5⟩ := s15k_pord_ln hm3 hLm
  rcases Nat.lt_or_ge m 5 with hm | hm
  · rcases (by omega : m = 3 ∨ m = 4) with rfl | rfl
    · rw [h3 rfl]
      norm_num
    · rw [h4 rfl]
      norm_num
  · exact s16e_two_not_prime_of_two_pow_dvd (h5 hm)

end Generic

section Bundles

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_fam_alt (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) {n : ℕ}
    (hn5 : 5 ≤ n) (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    s16e_two_Fam D V₀ V L hV (fun H U Z => AlternatingNatural H U Z n) where
  natFacts := ⟨fun J hJ => s16c167_mem_irrSet_alt hn5 hJ,
    fun J hJ => s16c167_cfg2_fix_alt hn5 hJ, fun J hJ => s16c167_endUnits_alt hn5 hJ⟩
  simple := s16c167_cfg2_simple_alt hn5 hA
  perfect := s16e_two_perfect_of_commutator_top (s16c1610_commutator_of_isAlt hn5 hA)
  sum := hsum

theorem s16e_two_fam_ln (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) {m : ℕ}
    (hm3 : 3 ≤ m) (hLm : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    s16e_two_Fam D V₀ V L hV (fun H U Z => BinaryNaturalSL H U Z m 1) where
  natFacts := ⟨fun J hJ => s16c167_mem_irrSet_ln (by omega) hJ,
    fun J hJ => s16c167_inf_fixV_eq_bot_of_binaryNaturalSL (by omega) hJ,
    fun J hJ => s16c167_endUnits_ln hm3 hJ⟩
  simple := s16c167_cfg2_simple_ln hLm
  perfect := s16e_two_perfect_of_simple (s16c167_cfg2_simple_ln hLm)
    (s16e_two_ln_not_prime hm3 hLm)
  sum := hsum

theorem s16e_two_fam_sp (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    s16e_two_Fam D V₀ V L hV (fun H U Z => NatSpn H U Z 6 1) where
  natFacts := ⟨fun J hJ => s16c167_mem_irrSet_sp (by norm_num) hJ,
    fun J hJ => s16c167_cfg2_fix_sp (by norm_num) hJ,
    fun J hJ => s15k_abs_endUnits_sp (by norm_num) hJ⟩
  simple := s16c167_cfg2_simple_sp hSp
  perfect := s16e_two_perfect_of_simple (s16c167_cfg2_simple_sp hSp)
    (s16e_two_not_prime_of_two_pow_dvd (s15k_pord_sp (by norm_num) hSp))
  sum := hsum

theorem s16e_two_fam_om (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) {n : ℕ}
    (hn : n = 6 ∨ n = 8) (hO : IsOmegaMinus ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    s16e_two_Fam D V₀ V L hV (fun H U Z => NatOmegaMinus H U Z n 1) where
  natFacts := ⟨fun J hJ => s16c167_mem_irrSet_omegaMinus hn hJ,
    fun J hJ => s16c167_cfg2_fix_omegaMinus hn hJ,
    fun J hJ => s15k_abs_endUnits_omegaMinus (by omega) hJ⟩
  simple := by
    rcases hn with rfl | rfl
    · exact s16c1_isSimpleGroup_of_isOmegaMinus_six hO
    · exact s16c167_cfg2_simple_omegaMinus_eight hO
  perfect := by
    rcases hn with rfl | rfl
    · refine s16e_two_perfect_of_simple (s16c1_isSimpleGroup_of_isOmegaMinus_six hO) ?_
      rw [(s15k_six_om6 hO).1]
      norm_num
    · exact s16e_two_perfect_of_simple (s16c167_cfg2_simple_omegaMinus_eight hO)
        (s16e_two_not_prime_of_two_pow_dvd (s15k_pord_omega_minus (by norm_num) hO))
  sum := hsum

end Bundles

section Alt

theorem s16e_two_alt_aut_equiv {X : Type} [Group X] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (hA : UC22.IsAlt X n) : Nonempty (MulAut X ≃* Equiv.Perm (Fin n)) := by
  obtain ⟨e⟩ := hA
  exact ⟨(MulAut.congr e).trans (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6)).symm⟩

theorem s16e_two_alt_rk_ge {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    {n : ℕ} (hn5 : 5 ≤ n) (h : AlternatingNatural H J ⊥ n) : 4 ≤ rk ↥J := by
  rcases Nat.even_or_odd n with he | ho
  · have h1 := s16c1610_le_rk_alternatingNatural (by omega : 2 ≤ n) h
    obtain ⟨k, hk⟩ := he
    omega
  · have h1 := s16c1610_rk_alternatingNatural_odd ho h
    omega

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_fam_alt_card_mbar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1) {n : ℕ}
    (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * Nat.factorial n := by
  obtain ⟨e⟩ := s16e_two_alt_aut_equiv hn5 hn6 hA
  refine s16e_two_card_mbar D hx h61 h127 h1214 hV hset hL hs (s16e_two_fam_alt D hV hn5 hA hsum)
    (a := Nat.factorial n) (dvd_of_eq ?_)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem s16e_two_fam_alt_route (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig) {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ IsSym ↥L₀ n := by
  obtain ⟨hK, L₀, hdir, ⟨e⟩⟩ := s16e_two_route_outer D hx h61 h127 h1214 h638 hV hset hL hconc hs h3
    (s16e_two_fam_alt D hV hn5 hA hsum) (fun J hJ => s16e_two_alt_rk_ge hn5 hJ)
    (fun J hJ h hh h1 h2 => s16e_two_alt_comm_rk_ge hn5 hJ hh h1 h2)
    (s15k_six_alt hA (by omega)).2
  obtain ⟨e'⟩ := s16e_two_alt_aut_equiv hn5 hn6 hA
  exact ⟨hK, L₀, hdir, ⟨e.trans e'⟩⟩

end Alt

section AltSix

theorem s16e_two_alt6_card_aut_dvd {X : Type} [Group X] (hA : UC22.IsAlt X 6) :
    Nat.card (MulAut X) ∣ 4 * 360 := by
  have hcard : Nat.card X = 360 := by
    rw [s15k_six_alt_card hA (by norm_num)]
    norm_num [Nat.factorial]
  have hz : Subgroup.center X = ⊥ :=
    s16e_two_center_bot_of_simple (s16c167_cfg2_simple_alt (by norm_num) hA)
      (by rw [hcard]; norm_num)
  obtain ⟨e⟩ := hA
  have hout : Nat.card (Outer X) ∣ 4 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    rcases s15k_six_alt6_outer with h2 | h4
    · rw [h2]
      norm_num
    · rw [h4]
  have h := s16e_two_card_mulAut_dvd hz hout
  rwa [hcard] at h

theorem s16e_two_alt6_not_cube_aut {X : Type} [Group X] (hA : UC22.IsAlt X 6) :
    ¬ 3 ^ 3 ∣ Nat.card (MulAut X) := by
  intro h
  have h1 := h.trans (s16e_two_alt6_card_aut_dvd hA)
  norm_num at h1

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_fam_alt6_route (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L) (hs : s15 D.M V₀ V hV L = 1)
    (h3 : 3 ∈ D.sig) (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ IsSym ↥L₀ 6 := by
  refine s16e_two_route_outer_six D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs h3
    (s16e_two_fam_alt D hV (by norm_num) hA hsum) (fun J hJ => s16e_two_alt_rk_ge (by norm_num) hJ)
    (fun J hJ h hh h1 h2 => s16e_two_alt_comm_rk_ge (by norm_num) hJ hh h1 h2)
    (s16e_two_alt6_not_cube_aut hA) ?_ (fun J hJ => s16e_two_alt6_normalizer_isSym hJ)
  rw [s15k_six_alt_card hA (by norm_num)]
  norm_num [Nat.factorial]

end AltSix

section Sp

theorem s16e_two_sp_card_aut_dvd {X : Type} [Group X] (h : IsSpn X 6 1) :
    Nat.card (MulAut X) ∣ Nat.card X := by
  have hsurj : Function.Surjective (MulAut.conj : X →* MulAut X) := fun α => by
    obtain ⟨x, hx⟩ := isSpn_six_one_exists_eq_conj h α
    exact ⟨x, hx.symm⟩
  have h1 : Nat.card (MulAut.conj : X →* MulAut X).range = Nat.card (MulAut X) := by
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
  rw [← h1]
  exact Subgroup.card_range_dvd _

theorem s16e_two_sp_inner {X : Type} [Group X] (h : IsSpn X 6 1) (φ : MulAut X) :
    ∃ h₀ : X, ∀ x : X, φ x = h₀ * x * h₀⁻¹ := by
  obtain ⟨y, hy⟩ := isSpn_six_one_exists_eq_conj h φ
  exact ⟨y, fun x => by rw [hy, MulAut.conj_apply]⟩

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_fam_sp_card_mbar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * 1451520 := by
  refine s16e_two_card_mbar D hx h61 h127 h1214 hV hset hL hs (s16e_two_fam_sp D hV hSp hsum)
    (a := 1451520) ?_
  rw [← s16c1610_card_of_isSpn_six hSp]
  exact s16e_two_sp_card_aut_dvd hSp

theorem s16e_two_fam_sp_sig (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 1) (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    D.sig = {3} := by
  refine s16e_two_sig D hx h4 h61 h127 h1214 hV hset
    (s16e_two_fam_sp_card_mbar D hx h61 h127 h1214 hV hset hL hs hSp hsum) ?_
  refine s16e_two_no_cube (N := 6 * 1451520) {2, 3, 5, 7} (by norm_num) ?_ ?_
  · simp [Nat.primeFactors]
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (by norm_num))
    · exact Or.inr (Or.inr (by norm_num))

theorem s16e_two_fam_sp_main (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig) (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      IsInternalDirect (kBar D.M V₀ V hV L) (lBar V₀ V hV L) (Mbar D.M V₀ V hV) :=
  s16e_two_route_inner D hx h61 h127 h1214 h638 hV hset hL hconc hs h3
    (s16e_two_fam_sp D hV hSp hsum) (s16e_two_sp_inner hSp)

end Sp

section Ln

open scoped Matrix
open CFSG.Quasithin.B5.Ln (mat)

theorem s16e_two_ln_autFromGroup {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {J : Subgroup W} {m : ℕ} (h : BinaryNaturalSL H J ⊥ m 1) : Z391.AutFromGroup H J := by
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  let β : ↥J ≃* Multiplicative (Fin m → ZMod 2) := MulEquiv.ofBijective f ⟨hfi, hfs⟩
  intro hh
  let F : Multiplicative (Fin m → ZMod 2) ≃* Multiplicative (Fin m → ZMod 2) :=
    β.symm.trans (hh.trans β)
  obtain ⟨g, hg⟩ := Z391.v2gd_model_aut (n := m) (M₀ := mat) (Or.inl rfl) F
  refine ⟨((π g : ↥H) : MulAut W), (π g).2, fun x => ?_⟩
  have hu : ((π g : ↥H) : MulAut W) (x : W) ∈ J := hπ.2.2.2.1 (π g) x x.2
  have h1 := hfe g x hu
  have h2 : β ⟨((π g : ↥H) : MulAut W) (x : W), hu⟩ = β (hh x) := by
    have e1 : β ⟨((π g : ↥H) : MulAut W) (x : W), hu⟩ = f ⟨((π g : ↥H) : MulAut W) (x : W), hu⟩ :=
      rfl
    have e2 : β (hh x) = F (β x) := by simp [F]
    rw [e1, h1, e2, hg]
    rfl
  have h3 := β.injective h2
  rw [MulAut.smul_def]
  exact (congrArg Subtype.val h3).symm

theorem s16e_two_ln_card_cases {X : Type} [Group X] {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5)
    (h : IsLn X m 1) : Nat.card X = 168 ∨ Nat.card X = 20160 ∨ Nat.card X = 9999360 := by
  rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5) with rfl | rfl | rfl
  · exact Or.inl ((s15k_pord_ln hm3 h).1 rfl)
  · exact Or.inr (Or.inl ((s15k_pord_ln hm3 h).2.1 rfl))
  · exact Or.inr (Or.inr (CFSG.ComponentClassification.GSThmB.CF23I.card_of_lieModel_L52 h))

theorem s16e_two_ln_card_outer_five {X : Type} [Group X] (h : IsLn X 5 1) :
    Nat.card (Outer X) ∣ 2 := by
  obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h
  letI : Field K := hF
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨hfin, hle⟩ := CFSG.SeitzReduction.SeitzQ2.card_outer_le_two_of_mulEquiv_PSL_two
    (by norm_num) hK2 e
  haveI := hfin
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  rcases (by omega : Nat.card (Outer X) = 1 ∨ Nat.card (Outer X) = 2) with h1 | h1 <;> rw [h1]
  exact one_dvd _

theorem s16e_two_ln_card_aut_dvd {X : Type} [Group X] {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5)
    (h : IsLn X m 1) : Nat.card (MulAut X) ∣ 2 * Nat.card X := by
  have hz : Subgroup.center X = ⊥ :=
    s16e_two_center_bot_of_simple (s16c167_cfg2_simple_ln h) (s16e_two_ln_not_prime hm3 h)
  haveI : Finite X := Nat.finite_of_card_ne_zero (by
    rcases s16e_two_ln_card_cases hm3 hm5 h with h | h | h <;> rw [h] <;> norm_num)
  rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5) with rfl | rfl | rfl
  · exact s16e_two_card_aut_dvd_of_le hz (s15k_six_l3 h).2
  · exact s16e_two_card_aut_dvd_of_le hz (s15k_six_l4 h).2
  · exact s16e_two_card_mulAut_dvd hz (s16e_two_ln_card_outer_five h)

theorem s16e_two_ln_not_cube {X : Type} [Group X] {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5)
    (h : IsLn X m 1) : ¬ 3 ^ 3 ∣ Nat.card (MulAut X) := by
  intro h27
  have h1 := h27.trans (s16e_two_ln_card_aut_dvd hm3 hm5 h)
  rcases s16e_two_ln_card_cases hm3 hm5 h with hc | hc | hc <;> rw [hc] at h1 <;> norm_num at h1

private theorem s16e_two_ln_arith {N : ℕ} (h : N = 168 ∨ N = 20160 ∨ N = 9999360) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 3 ∣ 6 * (2 * N) := by
  rcases h with rfl | rfl | rfl
  · refine s16e_two_no_cube {2, 3, 7} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  · refine s16e_two_no_cube {2, 3, 5, 7} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · refine s16e_two_no_cube {2, 3, 5, 7, 31} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_fam_ln_card_mbar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1) {m : ℕ}
    (hm3 : 3 ≤ m) (hm5 : m ≤ 5) (hLm : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * (2 * Nat.card ↥(lBar V₀ V hV L)) :=
  s16e_two_card_mbar D hx h61 h127 h1214 hV hset hL hs (s16e_two_fam_ln D hV hm3 hLm hsum)
    (a := 2 * Nat.card ↥(lBar V₀ V hV L)) (s16e_two_ln_card_aut_dvd hm3 hm5 hLm)

theorem s16e_two_fam_ln_sig (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 1) {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5)
    (hLm : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    D.sig = {3} :=
  s16e_two_sig D hx h4 h61 h127 h1214 hV hset
    (s16e_two_fam_ln_card_mbar D hx h61 h127 h1214 hV hset hL hs hm3 hm5 hLm hsum)
    (s16e_two_ln_arith (s16e_two_ln_card_cases hm3 hm5 hLm))

theorem s16e_two_fam_ln_main (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig) {m : ℕ}
    (hm3 : 3 ≤ m) (hm5 : m ≤ 5) (hLm : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      IsInternalDirect (kBar D.M V₀ V hV L) (lBar V₀ V hV L) (Mbar D.M V₀ V hV) :=
  s16e_two_route_autFrom D hx h4 h61 h127 h1214 h638 hV hset hL hs h3
    (s16e_two_fam_ln D hV hm3 hLm hsum) (fun J hJ => s16e_two_ln_autFromGroup hJ)
    (s16e_two_ln_not_cube hm3 hm5 hLm)

end Ln

section Om

theorem s16e_two_om_card_cases {X : Type} [Group X] {n : ℕ} (hn : n = 6 ∨ n = 8)
    (h : IsOmegaMinus X n 1) : Nat.card X = 25920 ∨ Nat.card X = 197406720 := by
  rcases hn with rfl | rfl
  · exact Or.inl (s15k_six_om6 h).1
  · exact Or.inr (s16c1610_card_of_isOmegaMinus_eight h)

theorem s16e_two_om_card_outer_eight {X : Type} [Group X] (h : IsOmegaMinus X 8 1) :
    Nat.card (Outer X) ∣ 2 := by
  have hmodel : StatedClassicalModel X .POmegaMinus 4 2 1 := by
    obtain ⟨-, K, hF, hFin, b, c, hK, hirr, ⟨e⟩⟩ := h
    exact ⟨⟨Nat.prime_two, le_refl _, le_refl _⟩, K, hF, hFin, by simpa using hK, b, c, hirr,
      ⟨e⟩⟩
  obtain ⟨hpos, hle⟩ := CFSG.AGLEmbedding.card_outer_le_two_of_omegaMinus_two hmodel
  rcases (by omega : Nat.card (Outer X) = 1 ∨ Nat.card (Outer X) = 2) with h1 | h1 <;>
    rw [h1]
  exact one_dvd _

private theorem s16e_two_om_center_bot {X : Type} [Group X] {n : ℕ} (hn : n = 6 ∨ n = 8)
    (h : IsOmegaMinus X n 1) : Subgroup.center X = ⊥ := by
  rcases hn with rfl | rfl
  · refine s16e_two_center_bot_of_simple (s16c1_isSimpleGroup_of_isOmegaMinus_six h) ?_
    rw [(s15k_six_om6 h).1]
    norm_num
  · exact s16e_two_center_bot_of_simple (s16c167_cfg2_simple_omegaMinus_eight h)
      (s16e_two_not_prime_of_two_pow_dvd (s15k_pord_omega_minus (by norm_num) h))

theorem s16e_two_om_card_aut_dvd {X : Type} [Group X] {n : ℕ} (hn : n = 6 ∨ n = 8)
    (h : IsOmegaMinus X n 1) : Nat.card (MulAut X) ∣ 2 * Nat.card X := by
  have hz := s16e_two_om_center_bot hn h
  rcases hn with rfl | rfl
  · haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [(s15k_six_om6 h).1]; norm_num)
    exact s16e_two_card_aut_dvd_of_le hz (s15k_six_om6 h).2
  · exact s16e_two_card_mulAut_dvd hz (s16e_two_om_card_outer_eight h)

theorem s16e_two_om_card_aut_le {X : Type} [Group X] {n : ℕ} (hn : n = 6 ∨ n = 8)
    (h : IsOmegaMinus X n 1) : Nat.card (MulAut X) ≤ 2 * Nat.card X := by
  haveI : Finite X := Nat.finite_of_card_ne_zero (by
    rcases s16e_two_om_card_cases hn h with hc | hc <;> rw [hc] <;> norm_num)
  exact Nat.le_of_dvd (Nat.mul_pos two_pos Nat.card_pos) (s16e_two_om_card_aut_dvd hn h)

open CFSG.LieType.ChevTwo CFSG.HardMathSupport.Foote.E27 in
theorem s16e_two_om_isOMinus_mulAut {X : Type} [Group X] {n : ℕ} (hn : n = 6 ∨ n = 8)
    (h : IsOmegaMinus X n 1) : IsOMinus (MulAut X) n 1 := by
  obtain ⟨hev, K', hK'field, hK'finite, b', c', hK'card, hpoly', ⟨eY⟩⟩ := h
  letI : Field K' := hK'field
  letI : Finite K' := hK'finite
  rw [pow_one] at hK'card
  have e1 : X ≃* ↥(StatedOmega (StatedQuadMinus (n / 2) (ZMod 2) 1 1)) := by
    refine eY.trans (Q2.statedProjOmegaEquiv (StatedQuadMinus (n / 2) K' b' c') hK'card
      (StatedQuadMinus (n / 2) (ZMod 2) 1 1) ?_)
    intro v σ
    exact Q2.quadMinus_comp (n / 2) σ hpoly' v
  have hind : OmegaTwoAutInduced (StatedQuadMinus (n / 2) (ZMod 2) 1 1) := by
    rcases hn with rfl | rfl
    · exact omegaTwoAutInduced.1 2 (by norm_num)
    · exact omegaTwoAutInduced.1 3 (by norm_num)
  have hG : GoodQ (StatedQuadMinus (n / 2) (ZMod 2) 1 1) := by
    rcases hn with rfl | rfl
    · exact goodQ_minus (n := 2) (by norm_num)
    · exact goodQ_minus (n := 3) (by norm_num)
  have hbij : Function.Bijective (kappa (StatedQuadMinus (n / 2) (ZMod 2) 1 1)) :=
    ⟨hG.kappa_injective, fun α => (inducedByIso_iff_mem_range _ α).1 (hind α)⟩
  refine ⟨hev, ZMod 2, inferInstance, inferInstance, 1, 1, by simp, by decide, ⟨?_⟩⟩
  exact ((MulAut.congr e1).trans (MulEquiv.ofBijective (kappa _) hbij).symm).trans
    (MulEquiv.subgroupCongr (isoGrp_eq_isometryCore _))

private theorem s16e_two_om_arith {N : ℕ} (h : N = 25920 ∨ N = 197406720) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 3 ∣ 6 * (2 * N) := by
  rcases h with rfl | rfl
  · refine s16e_two_no_cube {2, 3, 5} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  · refine s16e_two_no_cube {2, 3, 5, 7, 17} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_fam_om_card_mbar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1) {n : ℕ}
    (hn : n = 6 ∨ n = 8) (hO : IsOmegaMinus ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * (2 * Nat.card ↥(lBar V₀ V hV L)) :=
  s16e_two_card_mbar D hx h61 h127 h1214 hV hset hL hs (s16e_two_fam_om D hV hn hO hsum)
    (a := 2 * Nat.card ↥(lBar V₀ V hV L)) (s16e_two_om_card_aut_dvd hn hO)

theorem s16e_two_fam_om_sig (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn : n = 6 ∨ n = 8)
    (hO : IsOmegaMinus ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    D.sig = {3} :=
  s16e_two_sig D hx h4 h61 h127 h1214 hV hset
    (s16e_two_fam_om_card_mbar D hx h61 h127 h1214 hV hset hL hs hn hO hsum)
    (s16e_two_om_arith (s16e_two_om_card_cases hn hO))

theorem s16e_two_fam_om_main (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig) {n : ℕ} (hn : n = 6 ∨ n = 8)
    (hO : IsOmegaMinus ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ IsOMinus ↥L₀ n 1 := by
  obtain ⟨hK, L₀, hdir, ⟨e⟩⟩ := s16e_two_route_outer D hx h61 h127 h1214 h638 hV hset hL hconc hs
    h3 (s16e_two_fam_om D hV hn hO hsum)
    (fun J hJ => by
      have h1 := s16c1610_rk_natOmegaMinus (n := n) (a := 1) (by omega) hJ
      omega)
    (fun J hJ h hh h1 h2 => s16e_two_om_comm_rk_ge hn hJ hh h1 h2)
    (s16e_two_om_card_aut_le hn hO)
  exact ⟨hK, L₀, hdir, s16e_two_isOMinus_of_equiv e (s16e_two_om_isOMinus_mulAut hn hO)⟩

end Om

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
