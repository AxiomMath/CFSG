module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.PCoreSurjective
import CFSG.Quasithin.Recognition.GoldschmidtF112F20Orb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {S : Type} [Group S]

theorem card_eq_sixty_mul_of_isAlt_five {K : Subgroup S} (hA5 : IsAlt (Bar2 K) 5) :
    Nat.card K = 60 * Nat.card (CFSG.pCore 2 K) := by
  obtain ⟨e⟩ : Nonempty (Bar2 K ≃* alternatingGroup (Fin 5)) := hA5
  have h60 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 K), h60]

theorem sixty_dvd_card_of_isAlt_five {K : Subgroup S} (hA5 : IsAlt (Bar2 K) 5) :
    60 ∣ Nat.card K :=
  ⟨_, card_eq_sixty_mul_of_isAlt_five hA5⟩

theorem not_isSolvable_of_isAlt_five {K : Subgroup S} (hA5 : IsAlt (Bar2 K) 5) :
    ¬ Group.IsSolvable K := by
  obtain ⟨e⟩ : Nonempty (Bar2 K ≃* alternatingGroup (Fin 5)) := hA5
  intro hK
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have h1 : Group.IsSolvable (Bar2 K) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem exists_perfect_core_of_isAlt_five [Finite S] {K : Subgroup S} (hA5 : IsAlt (Bar2 K) 5) :
    ∃ P : Subgroup S, P ≤ K ∧ ⁅P, P⁆ = P ∧ P ⊔ pCoreOf 2 K = K ∧
      normalizer (K : Set S) ≤ normalizer (P : Set S) ∧ IsAlt (Bar2 P) 5 ∧
      ∀ D : Subgroup S, D ≤ K → Odd (Nat.card D) → D ≤ P := by
  obtain ⟨e⟩ : Nonempty (Bar2 K ≃* alternatingGroup (Fin 5)) := hA5
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  haveI : Group.IsPerfect (Bar2 K) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hres : CFSG.perfectResidual (Bar2 K) = ⊤ := by
    simp [CFSG.perfectResidual]
  have hmap : (CFSG.perfectResidual K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) = ⊤ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq _
      (QuotientGroup.mk'_surjective _)).trans hres
  have hsup : CFSG.perfectResidual K ⊔ CFSG.pCore 2 K = ⊤ := by
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 K)) (CFSG.perfectResidual K)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hPK : (CFSG.perfectResidual K).map K.subtype ≤ K := map_subtype_le _
  refine ⟨(CFSG.perfectResidual K).map K.subtype, hPK,
    (Subgroup.isPerfect_iff).mp
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map K), ?_,
    CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map K,
    ?_, ?_⟩
  · show _ ⊔ (CFSG.pCore 2 K).map K.subtype = K
    rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  ·
    have hφ : Function.Surjective
        ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hPK)) := by
      intro y
      have hy : y ∈ (CFSG.perfectResidual K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
        rw [hmap]
        exact mem_top y
      obtain ⟨r, hr, rfl⟩ := mem_map.mp hy
      exact ⟨⟨r, mem_map_of_mem _ hr⟩, rfl⟩
    have hker : IsPGroup 2
        ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hPK)).ker := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hPK)
    obtain ⟨e₁⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker _ hφ hker
    have hbot : CFSG.pCore 2 (Bar2 K) = ⊥ := by
      rw [← CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (QuotientGroup.mk' (CFSG.pCore 2 K))
        (QuotientGroup.mk'_surjective _)
        (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)]
      exact (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge
    exact ⟨e₁.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      (QuotientGroup.quotientBot.trans e))⟩
  ·
    intro D hDK hD d hd
    haveI : (CFSG.perfectResidual K).Characteristic :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic (G := K)
    have hmapO :
        (CFSG.pCore 2 K).map (QuotientGroup.mk' (CFSG.perfectResidual K)) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← hsup,
        Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge,
        bot_sup_eq]
    have hx : QuotientGroup.mk' (CFSG.perfectResidual K) ⟨d, hDK hd⟩ ∈
        (CFSG.pCore 2 K).map (QuotientGroup.mk' (CFSG.perfectResidual K)) := by
      rw [hmapO]
      exact mem_top _
    obtain ⟨o, ho, hdo⟩ := mem_map.mp hx
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := K) ⟨o, ho⟩
    have h1 : QuotientGroup.mk' (CFSG.perfectResidual K) ⟨d, hDK hd⟩ ^ 2 ^ n = 1 := by
      have ho1 : o ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      rw [← hdo, ← map_pow, ho1, map_one]
    have h2 : QuotientGroup.mk' (CFSG.perfectResidual K) ⟨d, hDK hd⟩ ^ Nat.card D = 1 := by
      have hd1 : (⟨d, hDK hd⟩ : K) ^ Nat.card D = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_mk]
        exact D.orderOf_dvd_natCard hd
      rw [← map_pow, hd1, map_one]
    have hcop : Nat.Coprime (Nat.card D) (2 ^ n) := (Nat.coprime_two_right.mpr hD).pow_right n
    have h3 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
    rw [hcop.gcd_eq_one, pow_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact mem_map.mpr ⟨_, h3, rfl⟩

theorem sixteen_le_card_of_isAlt_five [Finite S] {Q K : Subgroup S} (hQ : IsPGroup 2 Q)
    (hKQ : K ≤ normalizer (Q : Set S)) (hA5 : IsAlt (Bar2 K) 5)
    (hC : K ⊓ centralizer (Q : Set S) ≤ pCoreOf 2 K) : 16 ≤ Nat.card Q := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 5
    ((show (5 : ℕ) ∣ 60 by norm_num).trans (sixty_dvd_card_of_isAlt_five hA5))
  have hk5 : (k : S) ^ 5 = 1 := by
    rw [← hk, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have hkO : (k : S) ∉ pCoreOf 2 K := by
    intro hmem
    obtain ⟨y, hy, hyk⟩ := mem_map.mp hmem
    obtain rfl : y = k := Subtype.ext hyk
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := K) ⟨y, hy⟩
    have h5 : orderOf y ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
    rw [hk] at h5
    exact absurd (Nat.le_of_dvd two_pos (Nat.prime_five.dvd_of_dvd_pow h5)) (by norm_num)
  have hne : ¬ Q ≤ centralizer {(k : S)} := by
    intro hle
    refine hkO (hC (mem_inf.mpr ⟨k.2, mem_centralizer_iff.mpr fun q hq => ?_⟩))
    exact ((mem_centralizer_iff.mp (hle hq)) k rfl).symm
  have h16 := CFSG.Quasithin.F112B3.sixteen_mul_card_le hQ hk5 (hKQ k.2) hne
  have hpos : 0 < Nat.card ↥(Q ⊓ centralizer {(k : S)}) := Nat.card_pos
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
