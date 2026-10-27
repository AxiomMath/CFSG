module

public import CFSG.Holt.General.Aschbacher73
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26BenderAux
public import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration

public section

namespace CFSG.OddTranspositions.PartFour

open MulAction Subgroup


variable {P : Type} [Group P] [Finite P] {Ω : Type*} [MulAction P Ω] {α : Ω} {A : Subgroup P}

theorem card_eq_two_pow_add_one_of_semiregular [FaithfulSMul P Ω] [IsPretransitive P Ω]
    (hAα : A ≤ stabilizer P α) (hAN : stabilizer P α ≤ normalizer (A : Set P))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA4 : 4 ≤ Nat.card A)
    (hsemi : ∀ a ∈ A, ∀ β : Ω, a • β = β → β ≠ α → a = 1) :
    ∃ e : ℕ, Nat.card Ω = 2 ^ e + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQα : ∀ q ∈ A, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α := by
    intro q hq hq2 ω
    refine ⟨fun hω => by_contra fun hne => ?_, fun h => h ▸ hAα hq⟩
    rw [hsemi q hq ω hω hne, orderOf_one] at hq2
    exact absurd hq2 (by decide)
  obtain ⟨z, hzA, hz1⟩ : ∃ z ∈ A, z ≠ 1 := by
    by_contra h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr fun x hx =>
      by_contra fun hx1 => h ⟨x, hx, hx1⟩
    rw [hbot, Subgroup.card_bot] at hA4
    omega
  have hz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hA2 z hzA) hz1
  rcases CFSG.Holt.General.aschbacher73_theorem2 hQα hAN hzA hz with ⟨-, hO⟩ | ⟨hB, hL, hBor⟩
  · exfalso
    have hLn : (Subgroup.normalClosure ({z} : Set P)).Normal := Subgroup.normalClosure_normal
    have hVn : (CFSG.Holt.General.oddCoreOf (Subgroup.normalClosure ({z} : Set P))).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hVodd : ¬ 2 ∣ Nat.card (CFSG.Holt.General.oddCoreOf
        (Subgroup.normalClosure ({z} : Set P))) := by
      unfold CFSG.Holt.General.oddCoreOf
      rw [Subgroup.card_map_of_injective (Subgroup.normalClosure ({z} : Set P)).subtype_injective]
      have hc : Nat.Coprime 2
          (Nat.card (CFSG.pPrimeCore 2 (Subgroup.normalClosure ({z} : Set P)))) :=
        CFSG.pPrimeCore_coprime_card
      obtain ⟨k, hk⟩ := Nat.coprime_two_left.mp hc
      omega
    have hsq : ∀ g : A, g ^ 2 = 1 := fun g =>
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]; exact hA2 g g.2)
    have hVα := CFSG.RankThree.GroupTheory.SteinbergBM.le_of_forall_inf_centralizer_le
      { toIsMulCommutative := ⟨⟨fun a b =>
          (Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_of_pow_eq_one (hsq g)) a b).eq⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }
      (by simpa using hA4) hVodd (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (W := stabilizer P α) fun b hb hb1 k hk => by
        obtain ⟨-, hkc⟩ := Subgroup.mem_inf.mp hk
        rw [Subgroup.mem_centralizer_singleton_iff] at hkc
        rw [mem_stabilizer_iff]
        by_contra hne
        refine hb1 (hsemi b hb (k • α) ?_ hne)
        rw [smul_smul, ← hkc, mul_smul, mem_stabilizer_iff.mp (hAα hb)]
    have hall : ∀ ω : Ω, ω = α := fun ω => by
      obtain ⟨⟨k, hk⟩, hkω⟩ := hO.exists_smul_eq α ω
      rw [← hkω]
      exact mem_stabilizer_iff.mp (hVα hk)
    exact hz1 (FaithfulSMul.eq_of_smul_eq_smul fun ω => (hall _).trans (hall _).symm)
  · obtain ⟨S, hS⟩ := hBor.2
    have hstab : stabilizer (Subgroup.normalClosure ({z} : Set P)) α =
        (stabilizer P α).subgroupOf (Subgroup.normalClosure ({z} : Set P)) := by
      ext x
      rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_stabilizer_iff]
      rfl
    have hsyl : (normalizer (((S : Subgroup (Subgroup.normalClosure ({z} : Set P)))) :
        Set (Subgroup.normalClosure ({z} : Set P)))).index =
        Nat.card (Sylow 2 (Subgroup.normalClosure ({z} : Set P))) :=
      (Sylow.card_eq_index_normalizer S).symm
    obtain ⟨e, he⟩ := S.isPGroup'.exists_card_eq
    refine ⟨e, ?_⟩
    rw [← @index_stabilizer_of_transitive _ _ _ _ α hL, hstab, hS, hsyl,
      CFSG.ComponentClassification.Asc76.L26.card_sylow_of_isBender hB S, he]

end CFSG.OddTranspositions.PartFour
