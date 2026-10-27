module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A5S1327h
public import CFSG.Quasithin.H13.A6HatPlusA

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

theorem eq_bot_of_isPerfect_of_isPGroup {D : Type*} [Group D] [Finite D] {p : ℕ} [Fact p.Prime]
    {N : Subgroup D} (hperf : ⁅N, N⁆ = N) (hp : IsPGroup p N) : N = ⊥ := by
  have : Group.IsPerfect ↥N := Subgroup.isPerfect_iff.2 hperf
  have : Group.IsNilpotent ↥N := hp.isNilpotent
  by_contra hne
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
  exact Group.IsPerfect.not_isNilpotent ↥N ‹_›

theorem le_oTwoUpper_of_isPerfect {D : Type*} [Group D] [Finite D] {N : Subgroup D}
    (hperf : ⁅N, N⁆ = N) : N ≤ oTwoUpper (⊤ : Subgroup D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (oTwoUpper (⊤ : Subgroup D)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_oTwoUpper ⊤))
  have h2 : IsPGroup 2 ↥(N.map (QuotientGroup.mk' (oTwoUpper (⊤ : Subgroup D)))) := by
    rintro ⟨_, x, -, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup D) (mem_top x)
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← map_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hk
  have hperf' : ⁅N.map (QuotientGroup.mk' (oTwoUpper (⊤ : Subgroup D))),
      N.map (QuotientGroup.mk' (oTwoUpper (⊤ : Subgroup D)))⁆ =
      N.map (QuotientGroup.mk' (oTwoUpper (⊤ : Subgroup D))) := by
    rw [← Subgroup.map_commutator, hperf]
  have hbot := eq_bot_of_isPerfect_of_isPGroup hperf' h2
  intro x hx
  have hx' : QuotientGroup.mk' (oTwoUpper (⊤ : Subgroup D)) x ∈
      N.map (QuotientGroup.mk' (oTwoUpper (⊤ : Subgroup D))) := mem_map_of_mem _ hx
  rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  exact hx'

theorem eq_of_isQuasisimple {D : Type*} [Group D] {Q N : Subgroup D}
    (hQ : CFSG.IsQuasisimple ↥Q) (hNQ : N ≤ Q) (hn : Q ≤ normalizer (N : Set D))
    (hperf : ⁅N, N⁆ = N) (hne : N ≠ ⊥) : N = Q := by
  have : (N.subgroupOf Q).Normal := (normal_subgroupOf_iff_le_normalizer hNQ).2 hn
  have hQ' : CFSG.Open.IsQuasisimple ↥Q := ⟨Group.isPerfect_def.mp hQ.1, hQ.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ'
    (N.subgroupOf Q) with h | h
  · exfalso
    apply hne
    rw [← hperf, commutator_eq_bot_iff_le_centralizer]
    intro a ha
    refine mem_centralizer_iff.2 fun b hb => ?_
    have hc := mem_center_iff.1 (h (mem_subgroupOf.2 ha : (⟨a, hNQ ha⟩ : ↥Q) ∈ _))
      ⟨b, hNQ hb⟩
    exact congrArg Subtype.val hc
  · exact le_antisymm hNQ fun x hx => by
      have : (⟨x, hx⟩ : ↥Q) ∈ N.subgroupOf Q := by
        rw [h]
        exact mem_top _
      exact mem_subgroupOf.1 this

theorem card_le_of_isPGroup_of_sylow {D : Type*} [Group D] [Finite D] {S P : Subgroup D}
    (hS : ∃ T : Sylow 2 D, (T : Subgroup D) = S) (hP : IsPGroup 2 P) :
    Nat.card P ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, rfl⟩ := hS
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  calc Nat.card P ≤ Nat.card Q := card_le_of_le hPQ
    _ = Nat.card T := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]

theorem commutatorElement_mul_eq {D : Type*} [Group D] {k k' z z' : D} (h1 : k' * z = z * k')
    (h2 : k * z' = z' * k) (hzz : z * z' = z' * z) : ⁅k * z, k' * z'⁆ = ⁅k, k'⁆ := by
  have hc : z * (k' * z') = k' * z' * z := by
    rw [← mul_assoc, ← h1, mul_assoc, hzz, ← mul_assoc]
  have hc' : z' * k⁻¹ = k⁻¹ * z' := by
    calc z' * k⁻¹ = k⁻¹ * (k * z') * k⁻¹ := by group
      _ = k⁻¹ * (z' * k) * k⁻¹ := by rw [h2]
      _ = k⁻¹ * z' := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc k * z * (k' * z') * (k * z)⁻¹ * (k' * z')⁻¹ =
        k * (z * (k' * z')) * z⁻¹ * k⁻¹ * (k' * z')⁻¹ := by group
    _ = k * k' * (z' * k⁻¹) * z'⁻¹ * k'⁻¹ := by rw [hc]; group
    _ = k * k' * k⁻¹ * k'⁻¹ := by rw [hc']; group

theorem eq_oTwoUpper_of_f618 {D : Type} [Group D] [Finite D] {G₁ G₂ N P : Subgroup D}
    (hBig : A5.FactF618Big) (hL2 : A5.FactL2Three) (hA : IsGoldschmidtAmalgam G₁ G₂)
    (hc : F6.F618ConclusionCat G₁ G₂) (hNn : N.Normal) (hperf : ⁅N, N⁆ = N) (hPN : P ≤ N)
    (hP2 : IsPGroup 2 P) (hP4 : 4 ≤ Nat.card P)
    (hcard : (∃ b : ℕ, Nat.card N = 60 * 2 ^ b) ∨ 8 ≤ Nat.card P) :
    N = oTwoUpper (⊤ : Subgroup D) ∧ ∀ b : ℕ, Nat.card N ≠ 60 * 2 ^ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNO := le_oTwoUpper_of_isPerfect hperf
  have hNbot : N ≠ ⊥ := by
    rintro rfl
    have := card_le_of_le hPN
    rw [card_bot] at this
    omega
  have hNt : ∀ X : Subgroup D, X ≤ normalizer (N : Set D) := fun X =>
    le_top.trans (normalizer_eq_top_iff.mpr hNn).ge
  have hone : ∀ {A B : Subgroup D}, (∃ T : Sylow 2 D, (T : Subgroup D) = A ⊓ B) →
      F6.IsF618CaseOne A B → False := by
    intro A B hS h
    obtain ⟨⟨e⟩, -⟩ := h
    have h2 : Nat.card ↥(A ⊓ B) = 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      rfl
    have := card_le_of_isPGroup_of_sylow hS hP2
    omega
  have htwo : F6.IsF618CaseTwo D → False := by
    intro h
    have hP3 : IsPGroup 3 ↥P := (A5.isPGroup_oTwoUpper_of_caseTwo h).to_le (hPN.trans hNO)
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    obtain ⟨m, hm⟩ := hP3.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    have h2 : 2 ∣ 3 ^ m := by
      rw [← hm, hk]
      exact dvd_pow_self 2 hk0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).1
      (Nat.prime_two.dvd_of_dvd_pow h2)
    omega
  have hthree : ∀ {A B : Subgroup D}, F6.IsF618CaseThree A B → False := by
    intro A B h
    obtain ⟨p, K, Z, hp, hp24, hK, hZ, hKZ, -, hcomm, -⟩ := h
    obtain ⟨hKq, hKc, hK4⟩ := hL2 p ↥K hp hp24 hK
    have hNKZ : N ≤ K ⊔ Z := by
      rw [hKZ, F6.twoResidual_eq_oTwoUpper]
      exact hNO
    have hNK : N ≤ K := by
      rw [← hperf, commutator_le]
      intro a ha b hb
      obtain ⟨k, hk, z, hz, rfl⟩ := A5.exists_mul_of_mem_sup_comm hcomm (hNKZ ha)
      obtain ⟨k', hk', z', hz', rfl⟩ := A5.exists_mul_of_mem_sup_comm hcomm (hNKZ hb)
      rw [commutatorElement_mul_eq (hcomm k' hk' z hz) (hcomm k hk z' hz')
        (A5.comm_of_card_three hZ hz hz'), commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hk hk') (inv_mem hk)) (inv_mem hk')
    have hNeq : N = K := eq_of_isQuasisimple hKq hNK (hNt K) hperf hNbot
    rcases hcard with ⟨b, hb⟩ | h8
    · exact hKc b (hNeq ▸ hb)
    · have hPK : P ≤ K := hNeq ▸ hPN
      have h1 := hK4 (P.subgroupOf K) (hP2.of_equiv (subgroupOfEquivOfLe hPK).symm)
      rw [Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv] at h1
      omega
  have hbig : ∀ {A B : Subgroup D}, IsGoldschmidtAmalgam A B →
      (F6.IsF618CaseFour A B ∨ F6.IsF618CaseFive A B ∨ F6.IsF618CaseSix A B ∨
        F6.IsF618CaseSeven A B ∨ F6.IsF618CaseEightCat A B ∨ F6.IsF618CaseNineCat A B ∨
        F6.IsF618CaseTen A B ∨ F6.IsF618CaseEleven A B ∨ F6.IsF618CaseTwelve A B ∨
        F6.IsF618CaseThirteen A B) →
      N = oTwoUpper (⊤ : Subgroup D) ∧ ∀ b : ℕ, Nat.card N ≠ 60 * 2 ^ b := by
    intro A B hAB h
    obtain ⟨hq, hc⟩ := hBig D A B hAB h
    have e := eq_of_isQuasisimple hq hNO (hNt _) hperf hNbot
    exact ⟨e, fun b hb => hc b (e ▸ hb)⟩
  have hA' : IsGoldschmidtAmalgam G₂ G₁ := ⟨hA.toIsGoldschmidtTriple.symm, hA.pCore_eq_bot⟩
  have hS₂ : ∃ T : Sylow 2 D, (T : Subgroup D) = G₂ ⊓ G₁ := by
    rw [inf_comm]
    exact hA.sylow
  rcases hc with h | h
  · rcases h with h | h | h | h
    · exact (hone hA.sylow h).elim
    · exact (htwo h).elim
    · exact (hthree h).elim
    · exact hbig hA h
  · rcases h with h | h | h | h
    · exact (hone hS₂ h).elim
    · exact (htwo h).elim
    · exact (hthree h).elim
    · exact hbig hA' h

end CFSG.Quasithin.H13.U3
