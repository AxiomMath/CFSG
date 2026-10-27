module

public import CFSG.Quasithin.H13.U3S1347Z
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.H13.KGFactL2
public import CFSG.Quasithin.H13.U3S1347X

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem two_pow_eq_four {a r m : ℕ} (h : 2 ^ a * r = 4 * m) (hr : ¬ 2 ∣ r) (hm : ¬ 2 ∣ m) :
    2 ^ a = 4 := by
  have hr' : Nat.Coprime 2 r := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hr
  have hm' : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm
  apply Nat.dvd_antisymm
  · have h1 : 2 ^ a ∣ 4 * m := ⟨r, h.symm⟩
    exact (Nat.Coprime.pow_left a hm').dvd_of_dvd_mul_right h1
  · have h1 : 4 ∣ 2 ^ a * r := ⟨m, h⟩
    have h4 : Nat.Coprime 4 r := Nat.Coprime.pow_left 2 hr'
    exact h4.dvd_of_dvd_mul_right h1

theorem s1347_solv_f618 (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hH₀ : InH T (H₁ ⊔ H₂)) (hsolv : Group.IsSolvable ↥(H₁ ⊔ H₂))
    (hne : pCoreOf 2 H₁ ≠ pCoreOf 2 H₂) :
    F6.IsF618CaseTwo (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) ∧
      Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 (H₁ ⊔ H₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT := s1347_triple S h
  have hT' := hT.subgroupOf
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hTinf : H₁.subgroupOf (H₁ ⊔ H₂) ⊓ H₂.subgroupOf (H₁ ⊔ H₂) = T.subgroupOf (H₁ ⊔ H₂) := by
    rw [← s1347_inf_eq S h]
    ext x
    simp only [mem_inf, mem_subgroupOf]
  have hcardT : Nat.card ↥T = Nat.card ↥((T.subgroupOf (H₁ ⊔ H₂)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)))) *
        Nat.card ↥(pCoreOf 2 (H₁ ⊔ H₂)) := by
    have h1 := relIndex_mul_card (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) (T.subgroupOf (H₁ ⊔ H₂))
    rw [← F6.card_map_mk] at h1
    have h2 : CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂) ⊓ T.subgroupOf (H₁ ⊔ H₂) =
        Open.pCore 2 ↥(H₁ ⊔ H₂) := by
      rw [inf_comm, ← hTinf]
      exact F6.inf_inf_pPrimeCore_eq_pCore hT'
    rw [h2] at h1
    have h3 : Nat.card ↥(T.subgroupOf (H₁ ⊔ H₂)) = Nat.card ↥T :=
      Nat.card_congr (subgroupOfEquivOfLe hH₀.1).toEquiv
    have h4 : Nat.card ↥(Open.pCore 2 ↥(H₁ ⊔ H₂)) = Nat.card ↥(pCoreOf 2 (H₁ ⊔ H₂)) :=
      (card_map_of_injective (H₁ ⊔ H₂).subtype_injective).symm
    rw [← h3, ← h1, h4]
  have hO₀T : pCoreOf 2 (H₁ ⊔ H₂) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have hQ₀i : ∀ {Hi : Subgroup G}, Hi ≤ H₁ ⊔ H₂ → T ≤ Hi →
      pCoreOf 2 (H₁ ⊔ H₂) ≤ pCoreOf 2 Hi := fun hHi hTHi =>
    le_pCoreOf_of_le_normalizer 2 (hO₀T.trans hTHi)
      (hHi.trans (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂))) (pCoreOf_isPGroup 2 (H₁ ⊔ H₂))
  have hcardQ : ∀ {Hi : Subgroup G}, quasithinO2QuotientIso Hi (Perm (Fin 3)) → T ≤ Hi →
      Nat.card ↥T = 2 * Nat.card ↥(pCoreOf 2 Hi) := fun {Hi} hq hTHi => by
    have hsyl := A5.isSylowTwoOf_of_le S.h13.sylow hTHi
    have hOT := pCoreOf_two_le_of_isSylowTwoOf hsyl
    have h2 := relIndex_pCoreOf_T hq hTHi (s1347_relIndex_three S hTHi hq) hOT
    have h1 := relIndex_mul_card (pCoreOf 2 Hi) T
    rw [inf_eq_left.2 hOT, h2] at h1
    exact h1.symm
  rcases hT.f6_18Cat hF (stronglyQuasithin_of_pCoreOf_ne_bot S.h13.qtke hH₀.2)
    (kGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH₀.2) with
    ⟨hinf, hAm, -, hconc⟩ | ⟨hQ1, hQ2, -, -, -⟩
  swap
  · exfalso
    apply hne
    rw [← map_pCoreOf_subgroupOf (le_sup_left : H₁ ≤ H₁ ⊔ H₂),
      ← map_pCoreOf_subgroupOf (le_sup_right : H₂ ≤ H₁ ⊔ H₂), hQ1, hQ2]
  have hTplus : (H₁.subgroupOf (H₁ ⊔ H₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) ⊓
      (H₂.subgroupOf (H₁ ⊔ H₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) =
      (T.subgroupOf (H₁ ⊔ H₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) := by
    rw [hinf, hTinf]
  have hone : ∀ {A B : Subgroup (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))},
      A ⊓ B = (H₁.subgroupOf (H₁ ⊔ H₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) ⊓
        (H₂.subgroupOf (H₁ ⊔ H₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) →
      F6.IsF618CaseOne A B → False := by
    intro A B hAB hc
    obtain ⟨⟨e⟩, -⟩ := hc
    have h2 : Nat.card ↥(A ⊓ B) = 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      rfl
    rw [hAB, hTplus] at h2
    rw [h2] at hcardT
    have e₁ : pCoreOf 2 (H₁ ⊔ H₂) = pCoreOf 2 H₁ := by
      refine eq_of_le_of_card_ge (hQ₀i le_sup_left h.inH₁.1) ?_
      have := hcardQ h.s3₁ h.inH₁.1
      omega
    have e₂ : pCoreOf 2 (H₁ ⊔ H₂) = pCoreOf 2 H₂ := by
      refine eq_of_le_of_card_ge (hQ₀i le_sup_right h.inH₂.1) ?_
      have := hcardQ h.s3₂ h.inH₂.1
      omega
    exact hne (e₁.symm.trans e₂)
  have hquasi : ∀ {K : Subgroup (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))},
      CFSG.IsQuasisimple ↥K → False := fun hK =>
    CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hK inferInstance
  have key : ∀ {A B : Subgroup (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))},
      IsGoldschmidtAmalgam A B →
      A ⊓ B = (H₁.subgroupOf (H₁ ⊔ H₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) ⊓
        (H₂.subgroupOf (H₁ ⊔ H₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) →
      F6.IsF618CaseOrientedCat A B →
        F6.IsF618CaseTwo (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) := by
    intro A B hAB hinfAB hc
    rcases hc with h1 | h2 | h3 | h4
    · exact (hone hinfAB h1).elim
    · exact h2
    · obtain ⟨p, K, Z, hp, hp24, hK, -⟩ := h3
      exact (hquasi (A5.factL2Three_holds p ↥K hp hp24 hK).1).elim
    · exact (hquasi (hBig _ A B hAB h4).1).elim
  have hcase2 : F6.IsF618CaseTwo (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) := by
    rcases hconc with hc | hc
    · exact key hAm rfl hc
    · exact key ⟨hAm.toIsGoldschmidtTriple.symm, hAm.pCore_eq_bot⟩ (inf_comm _ _) hc
  refine ⟨hcase2, ?_⟩
  have hD : Nat.card (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) = 4 * 9 ∨
      Nat.card (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) = 4 * 27 := by
    rcases hcase2 with he | ⟨φ, hφ, hker⟩
    · left
      obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    · right
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
        hker.2.1, Nat.card_prod] at h1
      have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      rw [h1, h2]
      norm_num
  have h4 : Nat.card ↥((T.subgroupOf (H₁ ⊔ H₂)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)))) = 4 := by
    obtain ⟨P, hP⟩ := hAm.sylow
    rw [← hTplus, ← hP]
    obtain ⟨a, ha⟩ := P.2.exists_card_eq
    have hmul := card_mul_index (P : Subgroup (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)))
    rw [ha] at hmul ⊢
    rcases hD with hD | hD <;> rw [hD] at hmul
    · exact two_pow_eq_four hmul P.not_dvd_index (by decide)
    · exact two_pow_eq_four hmul P.not_dvd_index (by decide)
  rw [hcardT, h4]

theorem s1347_pPrimeCore_eq (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) (hsolv : Group.IsSolvable ↥(H₁ ⊔ H₂))
    (hne : pCoreOf 2 H₁ ≠ pCoreOf 2 H₂)
    (hT4 : Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 (H₁ ⊔ H₂))) :
    CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂) = Open.pCore 2 ↥(H₁ ⊔ H₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT' := (s1347_triple S h).subgroupOf
  have hsq := stronglyQuasithin_of_pCoreOf_ne_bot S.h13.qtke hH₀.2
  have hTinf : H₁.subgroupOf (H₁ ⊔ H₂) ⊓ H₂.subgroupOf (H₁ ⊔ H₂) = T.subgroupOf (H₁ ⊔ H₂) := by
    rw [← s1347_inf_eq S h]
    ext x
    simp only [mem_inf, mem_subgroupOf]
  have hcT : Nat.card ↥(H₁.subgroupOf (H₁ ⊔ H₂) ⊓ H₂.subgroupOf (H₁ ⊔ H₂)) ≤
      4 * Nat.card ↥(Open.pCore 2 ↥(H₁ ⊔ H₂)) := by
    have h4 : Nat.card ↥(Open.pCore 2 ↥(H₁ ⊔ H₂)) = Nat.card ↥(pCoreOf 2 (H₁ ⊔ H₂)) :=
      (card_map_of_injective (H₁ ⊔ H₂).subtype_injective).symm
    rw [hTinf, Nat.card_congr (subgroupOfEquivOfLe hH₀.1).toEquiv, hT4, h4]
  have hQ' : pCoreOf 2 (H₁.subgroupOf (H₁ ⊔ H₂)) ≠ pCoreOf 2 (H₂.subgroupOf (H₁ ⊔ H₂)) := by
    intro he
    apply hne
    rw [← map_pCoreOf_subgroupOf (le_sup_left : H₁ ≤ H₁ ⊔ H₂),
      ← map_pCoreOf_subgroupOf (le_sup_right : H₂ ≤ H₁ ⊔ H₂), he]
  refine le_antisymm ?_ F6.pCore_le_pPrimeCore
  have hN2 : IsPGroup 2 ↥(CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      fun {q} hq hqd => ?_)
    by_contra hq2
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card hqd
    have hqD : q ∣ Nat.card ↥(H₁ ⊔ H₂) := hqd.trans (card_subgroup_dvd_card _)
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(H₁ ⊔ H₂)) 2).exists_card_eq
    have hDc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥(H₁ ⊔ H₂))
    rw [hk] at hDc
    rw [hDc] at hqD
    have hq' : q ∣ Nat.card (↥(H₁ ⊔ H₂) ⧸ Open.pCore 2 ↥(H₁ ⊔ H₂)) :=
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).2 hq2)).dvd_of_dvd_mul_right
        hqD
    rcases prime_dvd_quot_pCore hT' hsolv hsq hcT hQ' hq hq' with e | e
    · exact hq2 e
    · exact hq3 e
  exact le_pCore 2 CFSG.pPrimeCore_normal hN2

end CFSG.Quasithin.H13.U3
