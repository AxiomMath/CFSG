module

public import CFSG.Quasithin.H13.L32AC47a
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement

section Generic

theorem eq_alt5_of_normal_perfect {A : Subgroup (Equiv.Perm (Fin 5))} (hn : A.Normal)
    (hperf : ⁅A, A⁆ = A) (hbot : A ≠ ⊥) : A = alternatingGroup (Fin 5) := by
  have hle : A ≤ alternatingGroup (Fin 5) := by
    rw [← hperf]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hAn : (A.subgroupOf (alternatingGroup (Fin 5))).Normal := hn.subgroupOf _
  rcases hAn.eq_bot_or_eq_top with h | h
  · exfalso
    apply hbot
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hle hx⟩ : ↥(alternatingGroup (Fin 5))) ∈
        A.subgroupOf (alternatingGroup (Fin 5)) := hx
    rw [h, Subgroup.mem_bot] at hx'
    have := congrArg Subtype.val hx'
    simpa using this
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

theorem eq_one_of_odd_of_isPGroup_two {X : Type*} [Group X] {P : Subgroup X}
    (hP : IsPGroup 2 P) {x : X} (hx : x ∈ P) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h1 : orderOf x = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) hd
  exact orderOf_eq_one_iff.mp h1

end Generic

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_le_oPrimeResidualOf_three {X H : Subgroup G}
    (h3 : (pCoreOf 2 (oTwoUpper X)).relIndex (oTwoUpper X) = 3) (hXH : oTwoUpper X ≤ H) :
    oTwoUpper X ≤ CFSG.Quasithin.oPrimeResidualOf 3 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := oTwoUpper X with hN
  have hn : ((pCoreOf 2 N).subgroupOf N).Normal := by
    rw [subgroupOf_pCoreOf_eq_pCore]
    exact CFSG.pCore_normal
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  have hxN : x ∈ N := Subgroup.subset_closure hx
  have hx3 : x ^ 3 ∈ pCoreOf 2 N := by
    have h := Subgroup.pow_index_mem ((pCoreOf 2 N).subgroupOf N) (⟨x, hxN⟩ : ↥N)
    rw [← Subgroup.relIndex, h3, Subgroup.mem_subgroupOf] at h
    simpa using h
  have hodd3 : Odd (orderOf (x ^ 3)) := Odd.of_dvd_nat hx.2 (orderOf_pow_dvd 3)
  have h1 : x ^ 3 = 1 :=
    eq_one_of_odd_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) hx3 hodd3
  refine Subgroup.subset_closure ⟨hXH hxN, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

theorem alt5_of_s5 {H K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hne : Nontrivial (cStar K))
    (hS5 : quasithinO2QuotientIso H (Equiv.Perm (Fin 5))) :
    IsAlt 5 (cStar K) ∧ ∀ x ∈ H, Odd (orderOf x) → x ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := hS5
  have hKH : K ≤ H := le_of_mem_cComp hK
  set N := CFSG.pCore 2 ↥H with hN
  have hk : φ.ker = N := by rw [hφk, hN]
  let φb : (↥H ⧸ N) ≃* Equiv.Perm (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hφb : ∀ h : ↥H, φb (QuotientGroup.mk h) = φ h := fun h => rfl
  set K' := K.subgroupOf H with hK'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hK'p : ⁅K', K'⁆ = K' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hK', Subgroup.map_subgroupOf_eq_of_le hKH,
      perfect_of_mem_cComp hK]
  set A := K'.map φ with hA
  have hAn : A.Normal := hK'n.map φ hφs
  have hAp : ⁅A, A⁆ = A := by rw [hA, ← Subgroup.map_commutator, hK'p]
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  have hKbA : (modO2Image H K).map φb.toMonoidHom = A := by
    rw [modO2Image, Subgroup.map_map, hA]
    rfl
  let eA : cStar K ≃* ↥A :=
    ((cStarEquiv K).trans e).trans
      ((φb.subgroupMap (modO2Image H K)).trans (MulEquiv.subgroupCongr hKbA))
  have hAbot : A ≠ ⊥ := by
    intro hbot
    have : Subsingleton ↥A := by
      rw [hbot]
      infer_instance
    obtain ⟨a, b, hab⟩ := hne.exists_pair_ne
    exact hab (eA.injective (Subsingleton.elim _ _))
  have hA5 := eq_alt5_of_normal_perfect hAn hAp hAbot
  refine ⟨⟨eA.trans (MulEquiv.subgroupCongr hA5)⟩, ?_⟩
  have hcardH : Nat.card ↥H = 120 * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr φb.toEquiv,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcardK : Nat.card ↥K = 60 * Nat.card (CFSG.pCore 2 ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K),
      ← Nat.card_congr (cStarEquiv K).toEquiv, Nat.card_congr eA.toEquiv,
      Nat.card_congr (MulEquiv.subgroupCongr hA5).toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
  obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  have hcardK' : Nat.card ↥K' = Nat.card ↥K := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH)
  have hQ : IsPGroup 2 (↥H ⧸ K') := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
    rw [hcardK', hcardK, hcardH, hN, ha, hb] at hmul
    have hdvd : Nat.card (↥H ⧸ K') ∣ 2 ^ (a + 1) := by
      refine ⟨2 ^ b, ?_⟩
      have h60 : 0 < 60 := by norm_num
      have : 2 ^ (a + 1) * 60 = Nat.card (↥H ⧸ K') * 2 ^ b * 60 := by
        rw [pow_succ]
        linarith
      have := Nat.eq_of_mul_eq_mul_right h60 this
      rw [this]
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card hc
  intro x hx hodd
  have hmk : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ K') = 1 := by
    obtain ⟨k, hk⟩ := hQ (QuotientGroup.mk (⟨x, hx⟩ : ↥H))
    have hd : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ K') ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have hd' : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ K') ∣ orderOf x := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_map_dvd (QuotientGroup.mk' K') _
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd' hcop) hd)
  rw [QuotientGroup.eq_one_iff, hK', Subgroup.mem_subgroupOf] at hmk
  exact hmk

end Ambient

end CFSG.Quasithin.H13.L32A.C
