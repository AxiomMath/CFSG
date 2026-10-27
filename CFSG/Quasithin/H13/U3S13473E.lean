module

public import CFSG.Quasithin.H13.U3S1347Z1
public import CFSG.Quasithin.H13.U3S1347Z2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem solv_f618_of_triple (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (S : A6.Setting134 G T L V) {P₁ P₂ : Subgroup G}
    (htr : F6.IsGoldschmidtTripleIn (P₁ ⊔ P₂) P₁ P₂) (hinf : P₁ ⊓ P₂ = T)
    (hq₁ : quasithinO2QuotientIso P₁ (Perm (Fin 3)))
    (hq₂ : quasithinO2QuotientIso P₂ (Perm (Fin 3))) (hY : InH T (P₁ ⊔ P₂))
    (hsolv : Group.IsSolvable ↥(P₁ ⊔ P₂)) (hne : pCoreOf 2 P₁ ≠ pCoreOf 2 P₂) :
    F6.IsF618CaseTwo (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) ∧
      Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 (P₁ ⊔ P₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT' := htr.subgroupOf
  have hTP₁ : T ≤ P₁ := hinf ▸ inf_le_left
  have hTP₂ : T ≤ P₂ := hinf ▸ inf_le_right
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hY.1
  have hTinf : P₁.subgroupOf (P₁ ⊔ P₂) ⊓ P₂.subgroupOf (P₁ ⊔ P₂) = T.subgroupOf (P₁ ⊔ P₂) := by
    rw [← hinf]
    ext x
    simp only [mem_inf, mem_subgroupOf]
  have hcardT : Nat.card ↥T = Nat.card ↥((T.subgroupOf (P₁ ⊔ P₂)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)))) *
        Nat.card ↥(pCoreOf 2 (P₁ ⊔ P₂)) := by
    have h1 := relIndex_mul_card (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) (T.subgroupOf (P₁ ⊔ P₂))
    rw [← F6.card_map_mk] at h1
    have h2 : CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂) ⊓ T.subgroupOf (P₁ ⊔ P₂) =
        Open.pCore 2 ↥(P₁ ⊔ P₂) := by
      rw [inf_comm, ← hTinf]
      exact F6.inf_inf_pPrimeCore_eq_pCore hT'
    rw [h2] at h1
    have h3 : Nat.card ↥(T.subgroupOf (P₁ ⊔ P₂)) = Nat.card ↥T :=
      Nat.card_congr (subgroupOfEquivOfLe hY.1).toEquiv
    have h4 : Nat.card ↥(Open.pCore 2 ↥(P₁ ⊔ P₂)) = Nat.card ↥(pCoreOf 2 (P₁ ⊔ P₂)) :=
      (card_map_of_injective (P₁ ⊔ P₂).subtype_injective).symm
    rw [← h3, ← h1, h4]
  have hO₀T : pCoreOf 2 (P₁ ⊔ P₂) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have hQ₀i : ∀ {Hi : Subgroup G}, Hi ≤ P₁ ⊔ P₂ → T ≤ Hi →
      pCoreOf 2 (P₁ ⊔ P₂) ≤ pCoreOf 2 Hi := fun hHi hTHi =>
    le_pCoreOf_of_le_normalizer 2 (hO₀T.trans hTHi)
      (hHi.trans (le_normalizer_pCoreOf 2 (P₁ ⊔ P₂))) (pCoreOf_isPGroup 2 (P₁ ⊔ P₂))
  have hcardQ : ∀ {Hi : Subgroup G}, quasithinO2QuotientIso Hi (Perm (Fin 3)) → T ≤ Hi →
      Nat.card ↥T = 2 * Nat.card ↥(pCoreOf 2 Hi) := fun {Hi} hq hTHi => by
    have hsyl := A5.isSylowTwoOf_of_le S.h13.sylow hTHi
    have hOT := pCoreOf_two_le_of_isSylowTwoOf hsyl
    have h2 := relIndex_pCoreOf_T hq hTHi (s1347_relIndex_three S hTHi hq) hOT
    have h1 := relIndex_mul_card (pCoreOf 2 Hi) T
    rw [inf_eq_left.2 hOT, h2] at h1
    exact h1.symm
  rcases htr.f6_18Cat hF (stronglyQuasithin_of_pCoreOf_ne_bot S.h13.qtke hY.2)
    (kGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hY.2) with
    ⟨hinf', hAm, -, hconc⟩ | ⟨hQ1, hQ2, -, -, -⟩
  swap
  · exfalso
    apply hne
    rw [← map_pCoreOf_subgroupOf (le_sup_left : P₁ ≤ P₁ ⊔ P₂),
      ← map_pCoreOf_subgroupOf (le_sup_right : P₂ ≤ P₁ ⊔ P₂), hQ1, hQ2]
  have hTplus : (P₁.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))) ⊓
      (P₂.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))) =
      (T.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))) := by
    rw [hinf', hTinf]
  have hone : ∀ {A B : Subgroup (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))},
      A ⊓ B = (P₁.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))) ⊓
        (P₂.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))) →
      F6.IsF618CaseOne A B → False := by
    intro A B hAB hc
    obtain ⟨⟨e⟩, -⟩ := hc
    have h2 : Nat.card ↥(A ⊓ B) = 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      rfl
    rw [hAB, hTplus] at h2
    rw [h2] at hcardT
    have e₁ : pCoreOf 2 (P₁ ⊔ P₂) = pCoreOf 2 P₁ := by
      refine eq_of_le_of_card_ge (hQ₀i le_sup_left hTP₁) ?_
      have := hcardQ hq₁ hTP₁
      omega
    have e₂ : pCoreOf 2 (P₁ ⊔ P₂) = pCoreOf 2 P₂ := by
      refine eq_of_le_of_card_ge (hQ₀i le_sup_right hTP₂) ?_
      have := hcardQ hq₂ hTP₂
      omega
    exact hne (e₁.symm.trans e₂)
  have hquasi : ∀ {K : Subgroup (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))},
      CFSG.IsQuasisimple ↥K → False := fun hK =>
    CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hK inferInstance
  have key : ∀ {A B : Subgroup (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))},
      IsGoldschmidtAmalgam A B →
      A ⊓ B = (P₁.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))) ⊓
        (P₂.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂))) →
      F6.IsF618CaseOrientedCat A B →
        F6.IsF618CaseTwo (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) := by
    intro A B hAB hinfAB hc
    rcases hc with h1 | h2 | h3 | h4
    · exact (hone hinfAB h1).elim
    · exact h2
    · obtain ⟨p, K, Z, hp, hp24, hK, -⟩ := h3
      exact (hquasi (A5.factL2Three_holds p ↥K hp hp24 hK).1).elim
    · exact (hquasi (hBig _ A B hAB h4).1).elim
  have hcase2 : F6.IsF618CaseTwo (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) := by
    rcases hconc with hc | hc
    · exact key hAm rfl hc
    · exact key ⟨hAm.toIsGoldschmidtTriple.symm, hAm.pCore_eq_bot⟩ (inf_comm _ _) hc
  refine ⟨hcase2, ?_⟩
  have hD : Nat.card (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) = 4 * 9 ∨
      Nat.card (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) = 4 * 27 := by
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
  have h4 : Nat.card ↥((T.subgroupOf (P₁ ⊔ P₂)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)))) = 4 := by
    obtain ⟨P, hP⟩ := hAm.sylow
    rw [← hTplus, ← hP]
    obtain ⟨a, ha⟩ := P.2.exists_card_eq
    have hmul := card_mul_index (P : Subgroup (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)))
    rw [ha] at hmul ⊢
    rcases hD with hD | hD <;> rw [hD] at hmul
    · exact two_pow_eq_four hmul P.not_dvd_index (by decide)
    · exact two_pow_eq_four hmul P.not_dvd_index (by decide)
  rw [hcardT, h4]

theorem pPrimeCore_eq_of_triple (S : A6.Setting134 G T L V) {P₁ P₂ : Subgroup G}
    (htr : F6.IsGoldschmidtTripleIn (P₁ ⊔ P₂) P₁ P₂) (hinf : P₁ ⊓ P₂ = T)
    (hY : InH T (P₁ ⊔ P₂)) (hsolv : Group.IsSolvable ↥(P₁ ⊔ P₂))
    (hne : pCoreOf 2 P₁ ≠ pCoreOf 2 P₂)
    (hT4 : Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 (P₁ ⊔ P₂))) :
    CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂) = Open.pCore 2 ↥(P₁ ⊔ P₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT' := htr.subgroupOf
  have hsq := stronglyQuasithin_of_pCoreOf_ne_bot S.h13.qtke hY.2
  have hTinf : P₁.subgroupOf (P₁ ⊔ P₂) ⊓ P₂.subgroupOf (P₁ ⊔ P₂) = T.subgroupOf (P₁ ⊔ P₂) := by
    rw [← hinf]
    ext x
    simp only [mem_inf, mem_subgroupOf]
  have hcT : Nat.card ↥(P₁.subgroupOf (P₁ ⊔ P₂) ⊓ P₂.subgroupOf (P₁ ⊔ P₂)) ≤
      4 * Nat.card ↥(Open.pCore 2 ↥(P₁ ⊔ P₂)) := by
    have h4 : Nat.card ↥(Open.pCore 2 ↥(P₁ ⊔ P₂)) = Nat.card ↥(pCoreOf 2 (P₁ ⊔ P₂)) :=
      (card_map_of_injective (P₁ ⊔ P₂).subtype_injective).symm
    rw [hTinf, Nat.card_congr (subgroupOfEquivOfLe hY.1).toEquiv, hT4, h4]
  have hQ' : pCoreOf 2 (P₁.subgroupOf (P₁ ⊔ P₂)) ≠ pCoreOf 2 (P₂.subgroupOf (P₁ ⊔ P₂)) := by
    intro he
    apply hne
    rw [← map_pCoreOf_subgroupOf (le_sup_left : P₁ ≤ P₁ ⊔ P₂),
      ← map_pCoreOf_subgroupOf (le_sup_right : P₂ ≤ P₁ ⊔ P₂), he]
  refine le_antisymm ?_ F6.pCore_le_pPrimeCore
  have hN2 : IsPGroup 2 ↥(CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      fun {q} hq hqd => ?_)
    by_contra hq2
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card hqd
    have hqD : q ∣ Nat.card ↥(P₁ ⊔ P₂) := hqd.trans (card_subgroup_dvd_card _)
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(P₁ ⊔ P₂)) 2).exists_card_eq
    have hDc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥(P₁ ⊔ P₂))
    rw [hk] at hDc
    rw [hDc] at hqD
    have hq' : q ∣ Nat.card (↥(P₁ ⊔ P₂) ⧸ Open.pCore 2 ↥(P₁ ⊔ P₂)) :=
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).2 hq2)).dvd_of_dvd_mul_right
        hqD
    rcases prime_dvd_quot_pCore hT' hsolv hsq hcT hQ' hq hq' with e | e
    · exact hq2 e
    · exact hq3 e
  exact le_pCore 2 CFSG.pPrimeCore_normal hN2

omit [Finite G] in
theorem comm_le_of_s3s3 {P₁ P₂ : Subgroup G}
    (hN : CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂) = Open.pCore 2 ↥(P₁ ⊔ P₂))
    (e : ↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂) ≃* Perm (Fin 3) × Perm (Fin 3)) :
    ⁅oTwoRes P₁, oTwoRes P₂⁆ ≤ pCoreOf 2 (P₁ ⊔ P₂) := by
  set f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) with hf
  let E : Subgroup (↥(P₁ ⊔ P₂) ⧸ CFSG.pPrimeCore 3 ↥(P₁ ⊔ P₂)) :=
    { carrier := {d | e d ^ 3 = 1}
      mul_mem' := fun {a b} ha hb => by
        show e (a * b) ^ 3 = 1
        rw [map_mul]
        exact s3s3_mul_pow_three ha hb
      one_mem' := by
        show e 1 ^ 3 = 1
        rw [map_one, one_pow]
      inv_mem' := fun {a} ha => by
        show e a⁻¹ ^ 3 = 1
        rw [map_inv, inv_pow, show e a ^ 3 = 1 from ha, inv_one] }
  have hE : ∀ d, d ∈ E ↔ e d ^ 3 = 1 := fun _ => Iff.rfl
  have hK : ∀ {Hi : Subgroup G}, Hi ≤ P₁ ⊔ P₂ →
      oTwoRes Hi ≤ (E.comap f).map (P₁ ⊔ P₂).subtype := by
    intro Hi hHi
    rw [oTwoRes, closure_le]
    rintro y ⟨hyH, m, hm, hym⟩
    have h1 : orderOf (⟨y, hHi hyH⟩ : ↥(P₁ ⊔ P₂)) ∣ m :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hym))
    have h2 : orderOf (e (f ⟨y, hHi hyH⟩)) ∣ m :=
      (orderOf_map_dvd (e.toMonoidHom.comp f) _).trans h1
    exact ⟨⟨y, hHi hyH⟩, (hE _).2 (s3s3_pow_three (Odd.of_dvd_nat hm h2)), rfl⟩
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := hK le_sup_left ha
  obtain ⟨b', hb', rfl⟩ := hK le_sup_right hb
  have h1 : f ⁅a', b'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply e.injective
    rw [map_mul, map_mul]
    exact s3s3_comm ((hE _).1 ha') ((hE _).1 hb')
  have h2 : ⁅a', b'⁆ ∈ Open.pCore 2 ↥(P₁ ⊔ P₂) := by
    rw [← hN]
    exact (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h2, rfl⟩

end CFSG.Quasithin.H13.U3
