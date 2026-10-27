module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddJ1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddFix
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93k
import CFSG.GroupTheory.PCentralElement
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddBorel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddInv
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920ShapeJ1
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem isJ1_bar2_opp (S : SliceCore D L D₃ Y H) (hJ : IsJ1 (Bar2 Y)) : IsJ1 (Bar2 (Opp 3 Y)) := by
  obtain ⟨e⟩ := S.nonempty_bar2_opp_equiv
  obtain ⟨f⟩ := hJ
  exact ⟨e.symm.trans f⟩

theorem exists_conj_pow_opp_of_isJ1 (S : SliceCore D L D₃ Y H) (hJ : IsJ1 (Bar2 Y)) :
    (∃ u d : ↥(Opp 3 Y), orderOf u = 19 ∧ d * u * d⁻¹ = u ^ 8) ∧
      ∃ u d : ↥(Opp 3 Y), orderOf u = 11 ∧ d * u * d⁻¹ = u ^ 2 := by
  have hO : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (CFSG.pCore 2 ↥(Opp 3 Y)) := by
    intro q hq hq2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(Opp 3 Y)))
    rw [hn]
    exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  obtain ⟨⟨a, b, ha, hab⟩, a', b', ha', hab'⟩ := exists_conj_pow_of_isJ1 (S.isJ1_bar2_opp hJ)
  exact ⟨exists_conj_pow_of_quotient (by norm_num) (CFSG.pCore 2 ↥(Opp 3 Y))
      (hO 19 (by norm_num) (by norm_num)) ha hab,
    exists_conj_pow_of_quotient (by norm_num) (CFSG.pCore 2 ↥(Opp 3 Y))
      (hO 11 (by norm_num) (by norm_num)) ha' hab'⟩

theorem I9_le_M_of_isJ1 (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (S : SliceCore D L D₃ Y H)
    (hJ : IsJ1 (Bar2 Y)) {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) : F09.I9 H ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨⟨u, d, hu, hdu⟩, u', d', hu', hdu'⟩ := S.exists_conj_pow_opp_of_isJ1 hJ
  have hle : CFSG.pPrimeCore 3 ↥(Opp 3 Y) ≤ CFSG.pCore 2 ↥(Opp 3 Y) :=
    le_pCore_two_of_normal S.isSimpleGroup_bar2_opp S.three_dvd_card_bar2_opp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card)
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Opp 3 Y))).ker := by
    rw [QuotientGroup.ker_mk']
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(Opp 3 Y))).to_le hle
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Opp 3 Y)) with hπ
  have ha := CFSG.orderOf_map_eq_of_isPGroup_ker (by norm_num) π hker hu
  have ha' := CFSG.orderOf_map_eq_of_isPGroup_ker (by norm_num) π hker hu'
  have hab : π d * π u * (π d)⁻¹ = π u ^ 8 := by
    rw [← map_inv, ← map_mul, ← map_mul, hdu, map_pow]
  have hab' : π d' * π u' * (π d')⁻¹ = π u' ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, hdu', map_pow]
  refine F09.I9_le_M_of_not_isL2 hK461 hK462 hSch hyp S.H_ne_top S.not_isPGroup_barO3_opp ?_
  rintro ⟨p, f, hL⟩
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
  exact false_of_conj_pow_of_mulEquiv le_rfl e hp hcard (by norm_num) (by norm_num) ha hab ha'
    hab'

theorem exists_conj_pow_lbar9_of_isJ1 (S : SliceCore D L D₃ Y H) (hJ : IsJ1 (Bar2 Y)) :
    (∃ a b : F09.Lbar9 Y H, orderOf a = 19 ∧ b * a * b⁻¹ = a ^ 8) ∧
      ∃ a b : F09.Lbar9 Y H, orderOf a = 11 ∧ b * a * b⁻¹ = a ^ 2 := by
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (F09.L9 Y H) :=
    Subgroup.map_mono fun y hy => F09.opp_le_L9 Y H hy
  let ι : ↥(Opp 3 Y) →* F09.Lbar9 Y H := (Subgroup.inclusion hle).comp (toImg9 hXH)
  have key : ∀ {q : ℕ}, q.Prime → q ≠ 2 → ∀ {u : ↥(Opp 3 Y)}, orderOf u = q →
      orderOf (ι u) = q := by
    intro q hq hq2 u hu
    haveI : Fact q.Prime := ⟨hq⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
    · intro h1
      have hk : u ∈ (toImg9 hXH).ker :=
        (Subgroup.inclusion_injective hle) (by rw [map_one]; exact h1)
      obtain ⟨n, hn⟩ := S.isPGroup_ker_toImg9 hXH ⟨u, hk⟩
      have hu2 : u ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have h2 : q ∣ 2 ^ n := hu ▸ orderOf_dvd_of_pow_eq_one hu2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
  obtain ⟨⟨u, d, hu, hdu⟩, u', d', hu', hdu'⟩ := S.exists_conj_pow_opp_of_isJ1 hJ
  exact ⟨⟨ι u, ι d, key (by norm_num) (by norm_num) hu,
      by rw [← map_inv, ← map_mul, ← map_mul, hdu, map_pow]⟩,
    ι u', ι d', key (by norm_num) (by norm_num) hu',
      by rw [← map_inv, ← map_mul, ← map_mul, hdu', map_pow]⟩

theorem false_of_isSpor_lbar9 (S : SliceCore D L D₃ Y H) (hJ : IsJ1 (Bar2 Y)) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M) (hJL : IsSpor (F09.Lbar9 Y H) .J1) :
    False := by
  have hcard : Nat.card (F09.Lbar9 Y H) = 175560 := (kJ1_holds (F09.Lbar9 Y H) hJL).1
  have hX : 175560 ∣ Nat.card (xbar9 Y H) := by
    rw [← (kJ1_holds _ (S.isJ1_bar2_opp hJ)).1]
    exact S.card_bar2_opp_dvd_card_xbar9
  have htop : xbar9 Y H = ⊤ := by
    refine (xbar9 Y H).eq_top_of_card_eq (le_antisymm (xbar9 Y H).card_le_card_group ?_)
    rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos hX
  refine S.false_of_wbar9_eq_top hyp hI ((Subgroup.eq_top_iff' _).mpr fun z => ?_)
  exact S.xbar9_le_wbar9 ((Subgroup.eq_top_iff' _).mp htop z)

theorem false_of_isJ1 (hK32 : UCK.K32) (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (S : SliceCore D L D₃ Y H)
    (hJ : IsJ1 (Bar2 Y)) {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) : False := by
  obtain ⟨⟨a, b, ha, hab⟩, a', b', ha', hab'⟩ := S.exists_conj_pow_lbar9_of_isJ1 hJ
  rcases F09.shape92_of_hyp91 hK32 hSch hyp S.H_ne_top with
    ⟨-, h3⟩ | hJL | ⟨p, f, hL⟩ | ⟨p, f, -, hL⟩ | ⟨p, f, -, hU⟩
  · obtain ⟨n, hn⟩ := h3 a
    have h19 : 19 ∣ 3 ^ n := by
      rw [← ha]
      exact orderOf_dvd_of_pow_eq_one hn
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_three).mp
      ((by norm_num : Nat.Prime 19).dvd_of_dvd_pow h19)
    omega
  · exact S.false_of_isSpor_lbar9 hJ hyp (S.I9_le_M_of_isJ1 hK461 hK462 hSch hJ hyp) hJL
  · obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
    exact false_of_conj_pow_of_mulEquiv le_rfl e hp hcard (by norm_num) (by norm_num) ha hab ha'
      hab'
  · obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
    exact false_of_conj_pow_of_mulEquiv le_rfl e hp hcard (by norm_num) (by norm_num) ha hab ha'
      hab'
  · obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hU (by decide)
    rw [← pow_mul] at hcard
    exact false_of_conj_pow_of_mulEquiv (CFSG.Open.StatedAPI.statedSU_le_statedSL 3 _ K) e hp
      hcard (by norm_num) (by norm_num) ha hab ha' hab'

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
