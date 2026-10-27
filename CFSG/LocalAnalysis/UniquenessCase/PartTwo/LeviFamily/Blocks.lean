module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
import CFSG.LocalAnalysis.AGLEmbedding.ComponentCentralizer
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma44
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4Quot
import CFSG.RankThree.PartTwo.Sec21.FF84S49AGen
import CFSG.Quasithin.EmptyFaithful.SzF53BasFin
import CFSG.GroupTheory.TwoElementGeneration
import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutAlt8Perm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
import CFSG.Fischer.Classification.Symmetric.LocalData
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem center_eq_bot_of_mulEquiv_perm {n : ℕ} (hn : 3 ≤ n)
    (e : X ≃* Equiv.Perm (Fin n)) : center X = ⊥ := by
  rw [← Subgroup.map_center_eq e.symm,
    CFSG.Fischer.Classification.SymPair.center_perm_eq_bot (by simpa using hn), Subgroup.map_bot]

omit [Finite X] in
private theorem opp_top_of_mulEquiv_perm {n : ℕ} (e : X ≃* Equiv.Perm (Fin n)) :
    Opp 2 (⊤ : Subgroup X) = ⊤ := by
  have hgen : Subgroup.closure {x : X | x * x = 1} = ⊤ := by
    have hmap : Subgroup.map e.toMonoidHom (Subgroup.closure {x : X | x * x = 1}) = ⊤ := by
      rw [MonoidHom.map_closure]
      have hset : e.toMonoidHom '' {x : X | x * x = 1} =
          {σ : Equiv.Perm (Fin n) | σ * σ = 1} := by
        ext σ
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using congrArg e hx
        · intro hσ
          exact ⟨e.symm σ, by simpa using congrArg e.symm hσ, e.apply_symm_apply σ⟩
      rw [hset, CFSG.GroupTheory.closure_involutions_perm_eq_top]
    exact Subgroup.map_injective e.injective (by
      rw [hmap, Subgroup.map_top_of_surjective _ e.surjective])
  have hle : Subgroup.closure {x : X | x * x = 1} ≤ Opp 2 (⊤ : Subgroup X) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    refine Subgroup.subset_closure ⟨Subgroup.mem_top x, ?_⟩
    have hpow : x ^ 2 = 1 := by simpa [pow_two] using hx
    have hdvd : orderOf x ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  rw [hgen] at hle
  exact top_le_iff.mp hle

private theorem le_card_isL2_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    504 ≤ 2 ^ n * (2 ^ (2 * n) - 1) := by
  have h1 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 63 ≤ 2 ^ (2 * n) - 1 := by
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 504 = 8 * 63 := by norm_num
    _ ≤ 2 ^ n * (2 ^ (2 * n) - 1) := Nat.mul_le_mul h1 h2

private theorem le_card_isL2_of_four_le (n : ℕ) (hn : 4 ≤ n) :
    4080 ≤ 2 ^ n * (2 ^ (2 * n) - 1) := by
  have h1 : 16 ≤ 2 ^ n := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 255 ≤ 2 ^ (2 * n) - 1 := by
    have h256 : 256 ≤ 2 ^ (2 * n) := by
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 4080 = 16 * 255 := by norm_num
    _ ≤ 2 ^ n * (2 ^ (2 * n) - 1) := Nat.mul_le_mul h1 h2

private theorem not_isL2_of_card_dvd_720 {Y : Type} [Group Y] [Finite Y]
    (h : Nat.card Y ∣ 720) {n : ℕ} (hn : 3 ≤ n) : ¬ IsL2 Y n := by
  intro hL
  have hcard := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.card_of_isL2 hL
  have hge : 504 ≤ Nat.card Y := by
    rw [hcard]
    exact le_card_isL2_of_three_le n hn
  have hle : Nat.card Y ≤ 720 := Nat.le_of_dvd (by norm_num) h
  have hn3 : n = 3 := by
    by_contra hne
    have h4 : 4 ≤ n := by omega
    have hge4 : 4080 ≤ Nat.card Y := by
      rw [hcard]
      exact le_card_isL2_of_four_le n h4
    omega
  have hYcard : Nat.card Y = 504 := by
    rw [hcard, hn3]
    norm_num
  rw [hYcard] at h
  norm_num at h

omit [Finite X] in
theorem IsLeviBlock.center_eq_bot_of_not_isQuasisimple (hX : IsLeviBlock X)
    (hq : ¬ CFSG.Open.IsQuasisimple X) : center X = ⊥ := by
  rcases hX with h3 | h6 | ⟨hqs, -, -⟩
  · obtain ⟨e⟩ := h3
    exact center_eq_bot_of_mulEquiv_perm (by simp) e
  · obtain ⟨e⟩ := h6
    exact center_eq_bot_of_mulEquiv_perm (by simp) e
  · exact absurd hqs hq

omit [Finite X] in
theorem nonempty_quotient_center_quotient_mulEquiv (hX : CFSG.Open.IsQuasisimple X)
    {Z : Subgroup X} [Z.Normal] (hZ : Z ≤ center X) :
    Nonempty ((X ⧸ Z) ⧸ center (X ⧸ Z) ≃* X ⧸ center X) := by
  have hperfect : Group.IsPerfect X := ⟨hX.1⟩
  have hcenter : (center X).map (QuotientGroup.mk' Z) = center (X ⧸ Z) :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
      (by simpa only [QuotientGroup.ker_mk'] using hZ)
  let equivalence := QuotientGroup.quotientQuotientEquivQuotient Z (center X) hZ
  let centerEquivalence := QuotientGroup.congr
    ((center X).map (QuotientGroup.mk' Z)) (center (X ⧸ Z)) (MulEquiv.refl _)
    (by simpa using hcenter)
  exact ⟨centerEquivalence.symm.trans equivalence⟩

omit [Finite X] in
theorem IsLeviBlock.quotient (hX : IsLeviBlock X) {Z : Subgroup X} [Z.Normal]
    (hZ : Z ≤ center X) : IsLeviBlock (X ⧸ Z) := by
  rcases hX with h3 | h6 | ⟨hq, ho, h2⟩
  · obtain ⟨e3⟩ := h3
    have hc : center X = ⊥ := center_eq_bot_of_mulEquiv_perm (by simp) e3
    have hZbot : Z = ⊥ := le_bot_iff.mp (hZ.trans hc.le)
    exact Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hZbot).trans
      QuotientGroup.quotientBot).trans e3⟩
  · obtain ⟨e6⟩ := h6
    have hc : center X = ⊥ := center_eq_bot_of_mulEquiv_perm (by simp) e6
    have hZbot : Z = ⊥ := le_bot_iff.mp (hZ.trans hc.le)
    exact Or.inr (Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hZbot).trans
      QuotientGroup.quotientBot).trans e6⟩)
  · have hperfect : Group.IsPerfect X := ⟨hq.1⟩
    have hqZ : CFSG.Open.IsQuasisimple (X ⧸ Z) :=
      CFSG.ComponentClassification.Quasisimple.central_quotient hq Z hZ
    have hcenter : (center X).map (QuotientGroup.mk' Z) = center (X ⧸ Z) :=
      CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
        (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
        (by simpa only [QuotientGroup.ker_mk'] using hZ)
    have hoddQ : Odd (Nat.card (center (X ⧸ Z))) := by
      rw [← hcenter]
      exact ho.of_dvd_nat (Subgroup.card_map_dvd (center X) (QuotientGroup.mk' Z))
    have h2Q : 2 ∣ Nat.card (X ⧸ Z) := by
      have hZodd : Odd (Nat.card Z) := ho.of_dvd_nat (Subgroup.card_dvd_of_le hZ)
      have hdvd : 2 ∣ Nat.card (X ⧸ Z) * Nat.card Z := by
        rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup Z]
        exact h2
      rcases (Nat.prime_two.dvd_mul).mp hdvd with h | h
      · exact h
      · exact absurd h hZodd.not_two_dvd_nat
    exact Or.inr (Or.inr ⟨hqZ, hoddQ, h2Q⟩)

theorem IsLeviBlock.eq_bot_of_normal_isPGroup_two (hX : IsLeviBlock X) {N : Subgroup X}
    (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  rcases hX with h3 | h6 | ⟨hq, ho, h2X⟩
  · obtain ⟨e⟩ := h3
    have hNmap : (Subgroup.map e.toMonoidHom N).Normal :=
      hN.map e.toMonoidHom e.surjective
    have hmap : Subgroup.map e.toMonoidHom N = ⊥ :=
      @CFSG.Quasithin.F53Push.perm3_normal_two_group (Subgroup.map e.toMonoidHom N)
        hNmap (h2.map e.toMonoidHom)
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp hmap
  · obtain ⟨e⟩ := h6
    have hmap : Subgroup.map e.toMonoidHom N = ⊥ :=
      CFSG.RankThree.PartTwo.Sec21.FF84.S4.perm6_normal_two_group
        (hN.map e.toMonoidHom e.surjective) (h2.map e.toMonoidHom)
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp hmap
  · have hcen : N ≤ center X :=
      CFSG.AGLEmbedding.le_center_of_normal_of_isPGroup_two hq hN h2
    exact CFSG.HardMathSupport.Solomon.LocalBalance.eq_bot_of_isPGroup_two_of_odd h2 hcen ho

theorem IsLeviBlock.opp_top (hX : IsLeviBlock X) : Opp 2 (⊤ : Subgroup X) = ⊤ := by
  rcases hX with h3 | h6 | ⟨hq, ho, h2⟩
  · obtain ⟨e⟩ := h3
    exact opp_top_of_mulEquiv_perm e
  · obtain ⟨e⟩ := h6
    exact opp_top_of_mulEquiv_perm e
  · obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
    have hxL : x ∈ Opp 2 (⊤ : Subgroup X) :=
      Subgroup.subset_closure ⟨Subgroup.mem_top x, 1, by rw [hx2, pow_one]⟩
    have hxc : x ∉ center X := by
      intro hxc
      have hdvd : 2 ∣ Nat.card (center X) := by
        rw [← hx2]
        exact Subgroup.orderOf_dvd_natCard (center X) hxc
      exact ho.not_two_dvd_nat hdvd
    have hLnorm : (Opp 2 (⊤ : Subgroup X)).Normal := by
      have hnorm : ((Opp 2 (⊤ : Subgroup X)).subgroupOf ⊤).Normal := close16_opp_normal 2 ⊤
      have hmap := hnorm.map (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).toMonoidHom
        (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).surjective
      rw [show (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).toMonoidHom =
        (⊤ : Subgroup X).subtype from rfl, Subgroup.map_subgroupOf_eq_of_le le_top] at hmap
      exact hmap
    have hLnorm' : (Opp 2 (⊤ : Subgroup X)).Normal := hLnorm
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (Opp 2 (⊤ : Subgroup X)) with hle | htop
    · exact absurd (hle hxL) hxc
    · exact htop

omit [Finite X] in
theorem IsLeviBlock.exists_pow_two_mem (hX : IsLeviBlock X) {N : Subgroup X} (hN : N.Normal)
    (hc : ¬ N ≤ center X) (x : X) : ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
  rcases hX with h3 | h6 | ⟨hq, ho, h2X⟩
  · obtain ⟨e⟩ := h3
    have hne : N ≠ ⊥ := fun hbot => hc (by rw [hbot]; exact bot_le)
    have hNmap : (Subgroup.map e.toMonoidHom N).Normal :=
      hN.map e.toMonoidHom e.surjective
    have hnemap : Subgroup.map e.toMonoidHom N ≠ ⊥ := by
      intro hbot
      exact hne ((Subgroup.map_eq_bot_iff_of_injective N e.injective).mp hbot)
    have hAlt : alternatingGroup (Fin 3) ≤ Subgroup.map e.toMonoidHom N :=
      @CFSG.Quasithin.F53.normal_ge_alt3 (Subgroup.map e.toMonoidHom N) hNmap hnemap
    have hsq : e x ^ 2 ∈ Subgroup.map e.toMonoidHom N := by
      apply hAlt
      rw [Equiv.Perm.mem_alternatingGroup, map_pow, pow_two, Int.units_mul_self]
    have hsq' : e (x ^ 2) ∈ Subgroup.map e.toMonoidHom N := by
      simpa [map_pow] using hsq
    exact ⟨1, (Subgroup.mem_map_iff_mem e.injective).mp hsq'⟩
  · obtain ⟨e⟩ := h6
    have hne : N ≠ ⊥ := fun hbot => hc (by rw [hbot]; exact bot_le)
    have hNmap : (Subgroup.map e.toMonoidHom N).Normal :=
      hN.map e.toMonoidHom e.surjective
    have hnemap : Subgroup.map e.toMonoidHom N ≠ ⊥ := by
      intro hbot
      exact hne ((Subgroup.map_eq_bot_iff_of_injective N e.injective).mp hbot)
    have hAlt : alternatingGroup (Fin 6) ≤ Subgroup.map e.toMonoidHom N := by
      rcases CFSG.EvenSporadicStandard.M22Std.perm_six_eq_bot_or_alt_le hNmap with h | h
      · exact absurd h hnemap
      · exact h
    have hsq : e x ^ 2 ∈ Subgroup.map e.toMonoidHom N := by
      apply hAlt
      rw [Equiv.Perm.mem_alternatingGroup, map_pow, pow_two, Int.units_mul_self]
    have hsq' : e (x ^ 2) ∈ Subgroup.map e.toMonoidHom N := by
      simpa [map_pow] using hsq
    exact ⟨1, (Subgroup.mem_map_iff_mem e.injective).mp hsq'⟩
  · have hNtop : N = ⊤ := by
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq N with
        hle | htop
      · exact absurd hle hc
      · exact htop
    exact ⟨0, by rw [hNtop]; exact Subgroup.mem_top x⟩

theorem not_isL2_of_card_lt {Y : Type} [Group Y] [Finite Y] (h : Nat.card Y < 504) {n : ℕ}
    (hn : 3 ≤ n) : ¬ IsL2 Y n := by
  intro hL
  have hge : 504 ≤ Nat.card Y := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.card_of_isL2 hL]
    exact le_card_isL2_of_three_le n hn
  omega

theorem IsLeviBlock.not_isL2_of_normal (hX : IsLeviBlock X)
    (hL : CFSG.Open.IsQuasisimple X → ∀ n, 3 ≤ n → ¬ IsL2 (X ⧸ center X) n) {N : Subgroup X}
    (hN : N.Normal) {n : ℕ} (hn : 3 ≤ n) : ¬ IsL2 ↥N n := by
  rcases hX with h3 | h6 | ⟨hq, ho, h2X⟩
  · obtain ⟨e⟩ := h3
    have hXcard : Nat.card X = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm]
      norm_num
    exact not_isL2_of_card_dvd_720
      ((hXcard ▸ Subgroup.card_subgroup_dvd_card N).trans (by norm_num)) hn
  · obtain ⟨e⟩ := h6
    have hXcard : Nat.card X = 720 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm]
      norm_num
    exact not_isL2_of_card_dvd_720 (hXcard ▸ Subgroup.card_subgroup_dvd_card N) hn
  · have hNtop : N = ⊤ ∨ N ≤ center X := by
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq N with
        hle | htop
      · exact Or.inr hle
      · exact Or.inl htop
    rcases hNtop with htop | hle
    · intro hL2N
      have hL2X : IsL2 X n :=
        CFSG.Blueprint.LieModel.of_mulEquiv Subgroup.topEquiv (htop ▸ hL2N)
      have hsimple : IsSimpleGroup X := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2X
      have hperfect : Group.IsPerfect X := ⟨hq.1⟩
      have hZ : center X = ⊥ :=
        TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
          (Group.IsPerfect.not_isMulCommutative X)
      have hL2Q : IsL2 (X ⧸ center X) n :=
        CFSG.Blueprint.LieModel.of_mulEquiv
          ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hL2X
      exact hL hq n hn hL2Q
    · intro hL2N
      have hoddN : Odd (Nat.card N) := ho.of_dvd_nat (Subgroup.card_dvd_of_le hle)
      have hcard := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.card_of_isL2 hL2N
      have heven : 2 ∣ Nat.card N := by
        rw [hcard]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
      exact hoddN.not_two_dvd_nat heven

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
