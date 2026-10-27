module

public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.GroupTheory.SteinbergBKCoprimeHallContainment

public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG
open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_sup_dvd_mul [Finite G] {U E : Subgroup G} (hE : E ≤ normalizer (U : Set G)) :
    Nat.card (U ⊔ E : Subgroup G) ∣ Nat.card U * Nat.card E := by
  have hsup : E ⊔ U = U ⊔ E := sup_comm _ _
  have h1 := Subgroup.normal_subgroupOf_of_le_normalizer hE
  have h2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer hE
  let equivalence := QuotientGroup.quotientInfEquivProdNormalizerQuotient E U hE
  have hquotientCard : Nat.card ((E ⊔ U : Subgroup G) ⧸ U.subgroupOf (E ⊔ U)) ∣ Nat.card E := by
    rw [← Nat.card_congr equivalence.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hsectionCard : Nat.card (U.subgroupOf (E ⊔ U)) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show U ≤ E ⊔ U from le_sup_right)).toEquiv
  rw [← hsup, Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf (E ⊔ U)),
    hsectionCard, mul_comm]
  exact mul_dvd_mul_left _ hquotientCard

theorem exists_invariant_hall [Finite G] {N V X : Subgroup G} {c : G} {q : ℕ} (hq : q.Prime)
    (hNsolv : Group.IsSolvable N) (hcop : Nat.Coprime (Nat.card (zpowers c)) (Nat.card N))
    (hcN : c ∈ normalizer (N : Set G)) (hVN : V ≤ N)
    (hVπ : ∀ p : ℕ, p.Prime → p ∣ Nat.card V → p = 2 ∨ p = q)
    (hcV : c ∈ normalizer (V : Set G)) (hXN : X ≤ N) (hXq : IsPGroup q X) :
    ∃ W : Subgroup G, V ≤ W ∧ W ≤ N ∧ c ∈ normalizer (W : Set G) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = q) ∧
      ∃ g ∈ N, ∀ x ∈ X, g * x * g⁻¹ ∈ W := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hzN : zpowers c ≤ normalizer (N : Set G) := Subgroup.zpowers_le.mpr hcN
  have hzV : zpowers c ≤ normalizer (V : Set G) := Subgroup.zpowers_le.mpr hcV
  let _inst : MulDistribMulAction (zpowers c) N :=
    MulDistribMulAction.compHom N (Subgroup.inclusion hzN : zpowers c →* normalizer (N : Set G))
  have hsmul : ∀ (a : zpowers c) (x : N), ((a • x : N) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun a x => rfl
  let π : Set Nat.Primes := {p | (p : ℕ) = 2 ∨ (p : ℕ) = q}
  have hcardV : Nat.card (V.subgroupOf N) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
  have hVπ' : IsPiSubgroup π (V.subgroupOf N) := fun p hp => by
    rw [hcardV] at hp
    exact hVπ p p.2 hp
  have hinv : ∀ a : zpowers c, ∀ x ∈ V.subgroupOf N, a • x ∈ V.subgroupOf N := by
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hzV a.2) x).mp hx
  obtain ⟨K, hK, hKinv, hVK⟩ :=
    CFSG.GroupTheory.SteinbergBK.solvable_coprime_invariant_hall_containment hNsolv hcop π
      (V.subgroupOf N) hVπ' hinv
  have hKact : ∀ a ∈ zpowers c, ∀ w ∈ K.map N.subtype, a * w * a⁻¹ ∈ K.map N.subtype := by
    intro a ha w hw
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hw
    exact Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : zpowers c) • k, hKinv ⟨a, ha⟩ k hk, hsmul ⟨a, ha⟩ k⟩
  have hqπ : (⟨q, hq⟩ : Nat.Primes) ∈ π := Or.inr rfl
  have hqK : ¬ q ∣ K.index := fun h => hK.p_in_pi_of_p_dvd_index ⟨q, hq⟩ h hqπ
  have hfac : (Nat.card N).factorization q = (Nat.card K).factorization q := by
    have h := Subgroup.card_mul_index K
    rw [← h, Nat.factorization_mul Nat.card_pos.ne' (Subgroup.index_ne_zero_of_finite),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqK, add_zero]
  obtain ⟨S₀⟩ : Nonempty (Sylow q K) := inferInstance
  have hS₁card : Nat.card ((S₀ : Subgroup K).map K.subtype) =
      q ^ (Nat.card N).factorization q := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  let S₁ : Sylow q N := Sylow.ofCard _ hS₁card
  have hXq' : IsPGroup q (X.subgroupOf N) := hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXN).symm
  obtain ⟨S, hS⟩ := hXq'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N S S₁
  refine ⟨K.map N.subtype, ?_, Subgroup.map_subtype_le K, ?_, ?_, g, g.2, ?_⟩
  · intro v hv
    exact Subgroup.mem_map.mpr ⟨⟨v, hVN hv⟩, hVK hv, rfl⟩
  · exact mem_normalizer_of_forward (hKact c (Subgroup.mem_zpowers c)) (fun x hx => by
      simpa using hKact c⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) x hx)
  · intro p hp hdvd
    have hcardW : Nat.card (K.map N.subtype) = Nat.card K :=
      Subgroup.card_map_of_injective N.subtype_injective
    rw [hcardW] at hdvd
    exact hK.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hdvd
  · intro x hx
    have hxS : (⟨x, hXN hx⟩ : N) ∈ S := hS (Subgroup.mem_subgroupOf.mpr hx)
    have h1 : (MulAut.conj g) • (⟨x, hXN hx⟩ : N) ∈ (MulAut.conj g) • (S : Subgroup N) :=
      (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨_, hxS, rfl⟩
    have h2 : (MulAut.conj g) • (S : Subgroup N) = ((g • S : Sylow q N) : Subgroup N) :=
      Sylow.coe_subgroup_smul.symm
    rw [h2, hg] at h1
    have h3 : (MulAut.conj g) • (⟨x, hXN hx⟩ : N) ∈ (S₀ : Subgroup K).map K.subtype := h1
    obtain ⟨k, -, hkx⟩ := Subgroup.mem_map.mp h3
    refine Subgroup.mem_map.mpr ⟨(k : N), k.2, ?_⟩
    have := congrArg Subtype.val hkx
    simpa using this

end CFSG.RankThree.PartOne.Sec9Excl
