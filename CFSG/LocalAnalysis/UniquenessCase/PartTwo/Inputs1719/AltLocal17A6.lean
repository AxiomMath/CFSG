module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def K_A6Exp4SThreePair : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) →
    (∀ s ∈ S, s ^ 4 = 1) →
    ∃ P₁ P₂ : Subgroup Y, S ≤ P₁ ∧ S ≤ P₂ ∧ P₁ ⊔ P₂ = ⊤ ∧
      Nonempty (Bar2 P₁ ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty (Bar2 P₂ ≃* Equiv.Perm (Fin 3))

@[expose] def K_A6Exp4Noncentral : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) →
    (∀ s ∈ S, s ^ 4 = 1) →
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S

@[expose] def K_A6AutOrder8 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L₀ : Subgroup A), L₀.Normal →
    Nonempty (↥L₀ ≃* alternatingGroup (Fin 6)) → Subgroup.centralizer (L₀ : Set A) = ⊥ →
    (∃ a : A, a ^ 4 ≠ 1 ∧ ∃ n : ℕ, a ^ 2 ^ n = 1) →
    IsAutOf A (alternatingGroup (Fin 6)) ∨ IsM10 A ∨ CFSG.Quasithin.F6.IsPGL2 9 A


theorem k_A6Exp4Noncentral_of_sThreePair (h : K_A6Exp4SThreePair) :
    K_A6Exp4Noncentral := by
  intro Y instY finY K S hKY hA hexp
  obtain ⟨P₁, P₂, hSP₁, hSP₂, hsup, hbar₁, hbar₂⟩ := h Y K S hKY hA hexp
  have hKN : K.Normal := hKY.1
  obtain ⟨a, hKindex⟩ := hKY.2.2.2.2.1
  have hSylY : IsSylowIn 2 S ⊤ := hKY.2.2.2.2.2
  have hSylYcard : Nat.card S = 2 ^ (Nat.card Y).factorization 2 := by
    simpa using hSylY.card_eq
  have hbasic : ∀ E : Subgroup Y, Nat.card E = 3 →
      E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) := by
    intro E hE
    refine ⟨?_, ?_, ?_⟩
    · intro hbot
      rw [hbot, Subgroup.card_bot] at hE
      norm_num at hE
    · exact IsPGroup.of_card (n := 1) (p := 3) (G := ↥E) (by rw [hE]; norm_num)
    · intro x hx
      have hdvd : orderOf x ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard E hx
        simpa [hE] using this
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have key : ∀ P : Subgroup Y, S ≤ P →
      Nonempty (Bar2 P ≃* Equiv.Perm (Fin 3)) →
      ∃ E : Subgroup Y, E ≤ P ∧ E ≤ K ∧ Nat.card E = 3 ∧ E ⊓ S = ⊥ ∧
        E ⊔ S = P ∧ Permutes E S := by
    intro P hSP hbar
    obtain ⟨e⟩ := hbar
    have hbarcard : Nat.card (Bar2 P) = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm]
      norm_num
    have hOcard : (CFSG.pCore 2 ↥P).index = 6 := by
      rw [Subgroup.index_eq_card]
      exact hbarcard
    have hPcard : Nat.card P = 6 * Nat.card (CFSG.pCore 2 ↥P) := by
      have h := Subgroup.card_mul_index (H := CFSG.pCore 2 ↥P)
      rw [hOcard] at h
      simpa [mul_comm] using h.symm
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).exists_card_eq
    have hSylP : IsSylowIn 2 S P := by
      refine ⟨hSP, hSylY.isPGroup, ?_⟩
      intro h2
      apply hSylY.not_dvd_relIndex
      rw [← Subgroup.relIndex_mul_relIndex S P ⊤ hSP le_top]
      exact dvd_mul_of_dvd_left h2 _
    have hScardY : Nat.card S = 2 ^ (Nat.card P).factorization 2 := hSylP.card_eq
    have hv : (Nat.card P).factorization 2 = k + 1 := by
      rw [hPcard, hk, Nat.factorization_mul (by norm_num) (pow_ne_zero k (by norm_num))]
      rw [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two]
      have h6 : (6 : ℕ).factorization 2 = 1 := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.Prime.factorization_self Nat.prime_two,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
      rw [h6]
      omega
    have hScard2 : Nat.card S = 2 * Nat.card (CFSG.pCore 2 ↥P) := by
      rw [hScardY, hv, hk]
      ring
    have hP3 : Nat.card P = 3 * Nat.card S := by
      rw [hPcard, hScard2]
      ring
    have h3dvd : 3 ∣ Nat.card P := ⟨Nat.card S, hP3⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3dvd
    let E : Subgroup Y := Subgroup.zpowers (x : Y)
    have hEP : E ≤ P := Subgroup.zpowers_le_of_mem x.2
    have hEcard : Nat.card E = 3 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
    have hcop : Nat.Coprime (Nat.card E) (Nat.card S) := by
      rw [hEcard, hScardY]
      exact Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)
    have hdisj : Disjoint E S := Subgroup.disjoint_of_coprime_natCard hcop
    have hinf : E ⊓ S = ⊥ := hdisj.eq_bot
    have hleES : E ⊔ S ≤ P := sup_le hEP hSP
    have hge : Nat.card P ≤ Nat.card ↥(E ⊔ S) := by
      rw [hP3]
      have hfuninj : Function.Injective (fun p : ↥E × ↥S =>
          (⟨(p.1 : Y) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(E ⊔ S))) := by
        intro p q hpq
        exact Subgroup.mul_injective_of_disjoint hdisj (congrArg Subtype.val hpq)
      have := Nat.card_le_card_of_injective
        (fun p : ↥E × ↥S =>
          (⟨(p.1 : Y) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(E ⊔ S))) hfuninj
      simpa [Nat.card_prod, hEcard] using this
    have hsupES : E ⊔ S = P := Subgroup.eq_of_le_of_card_ge hleES hge
    have hperm : Permutes E S := by
      refine CFSG.Quasithin.H.L3Wr.permute_of_card hinf ?_
      rw [hsupES, hP3, hEcard]
    have hEK : E ≤ K := by
      have himgbot : E.map (QuotientGroup.mk' K) = ⊥ := by
        apply Subgroup.eq_bot_of_card_eq
        have hdvd3 : Nat.card (E.map (QuotientGroup.mk' K)) ∣ 3 := by
          simpa [hEcard] using Subgroup.card_map_dvd (H := E) (f := QuotientGroup.mk' K)
        have hdvd2 : Nat.card (E.map (QuotientGroup.mk' K)) ∣ 2 ^ a := by
          have h := Subgroup.card_subgroup_dvd_card (E.map (QuotientGroup.mk' K))
          rwa [show Nat.card (Y ⧸ K) = 2 ^ a by
            rw [← Subgroup.index_eq_card K, hKindex]] at h
        have hcopg : Nat.Coprime 3 (2 ^ a) :=
          Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)
        exact Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hcopg ▸ Nat.dvd_gcd hdvd3 hdvd2)
      have hker : E ≤ (QuotientGroup.mk' K).ker :=
        (Subgroup.map_eq_bot_iff (H := E) (f := QuotientGroup.mk' K)).mp himgbot
      simpa [QuotientGroup.ker_mk'] using hker
    exact ⟨E, hEP, hEK, hEcard, hinf, hsupES, hperm⟩
  obtain ⟨E₁, hE₁P, hE₁K, hE₁card, hE₁inf, hE₁sup, hE₁perm⟩ := key P₁ hSP₁ hbar₁
  obtain ⟨E₂, hE₂P, hE₂K, hE₂card, hE₂inf, hE₂sup, hE₂perm⟩ := key P₂ hSP₂ hbar₂
  by_cases hc₁ : E₁ ≤ (Subgroup.center ↥K).map K.subtype
  · by_cases hc₂ : E₂ ≤ (Subgroup.center ↥K).map K.subtype
    · exfalso
      let Z : Subgroup Y := (Subgroup.center ↥K).map K.subtype
      have hZnorm : Z.Normal := by
        have : (Subgroup.center ↥K).Characteristic := Subgroup.centerCharacteristic
        exact ConjAct.normal_of_characteristic_of_normal (H := K)
          (K := Subgroup.center ↥K)
      have : Z.Normal := hZnorm
      have hZcard : Nat.card Z = Nat.card (Subgroup.center ↥K) :=
        Subgroup.card_subtype K (Subgroup.center ↥K)
      have hZodd : Odd (Nat.card Z) := by
        rw [hZcard]
        exact hKY.2.2.1
      have hKcenter : Nat.card K = Nat.card (Subgroup.center ↥K) * 360 := by
        obtain ⟨e⟩ := hA
        have hquot : Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
          norm_num
        have hidx : (Subgroup.center ↥K).index = 360 := by
          rw [Subgroup.index_eq_card]
          exact hquot
        have h := Subgroup.card_mul_index (H := Subgroup.center ↥K)
        rw [hidx] at h
        exact h.symm
      have hKZ : Nat.card K = Nat.card Z * 360 := by
        rw [hKcenter, hZcard]
      have hZinfS : Z ⊓ S = ⊥ := by
        refine Subgroup.inf_eq_bot_of_coprime ?_
        rw [hSylYcard]
        exact Nat.Coprime.pow_right _ hZodd.coprime_two_right
      have hcardjoin : Nat.card ↥(Z ⊔ S) = Nat.card Z * Nat.card S := by
        have h :=
          CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
            (H := S) (K := Z) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
        rw [sup_comm, inf_comm, hZinfS, Subgroup.card_bot, mul_one, mul_comm] at h
        exact h
      have htop : Z ⊔ S = ⊤ := by
        refine eq_top_iff.mpr ?_
        rw [← hsup]
        refine sup_le ?_ ?_
        · rw [← hE₁sup]
          exact sup_le (hc₁.trans le_sup_left) le_sup_right
        · rw [← hE₂sup]
          exact sup_le (hc₂.trans le_sup_left) le_sup_right
      have hcardY : Nat.card Y = Nat.card ↥(Z ⊔ S) := by
        rw [htop, Subgroup.card_top]
      have hdiv : Nat.card K ∣ Nat.card ↥(Z ⊔ S) := by
        rw [← hcardY]
        exact Subgroup.card_subgroup_dvd_card K
      rw [hKZ, hcardjoin] at hdiv
      have h360 : 360 ∣ Nat.card S :=
        Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdiv
      have h3dvd : 3 ∣ Nat.card S :=
        dvd_trans (by norm_num : 3 ∣ 360) h360
      rw [hSylYcard] at h3dvd
      have h32 : (3 : ℕ) ∣ 2 :=
        Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3dvd
      norm_num at h32
    · have hb := hbasic E₂ hE₂card
      exact ⟨E₂, hE₂K, hb.1, hb.2.1, hb.2.2, hc₂, hE₂perm⟩
  · have hb := hbasic E₁ hE₁card
    exact ⟨E₁, hE₁K, hb.1, hb.2.1, hb.2.2, hc₁, hE₁perm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
