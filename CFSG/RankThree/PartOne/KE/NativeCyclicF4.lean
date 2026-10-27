module

public import CFSG.RankThree.PartOne.KE.NativeCyclicAbstract
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter
public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4Noninner
public import CFSG.RankThree.Chevalley.SteinbergCFOddF4NoninnerLocalCore
public import CFSG.RankThree.PartOne.KE.Endpoint
public import CFSG.RankThree.PartOne.KE.EndpointStatements

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.Chevalley
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

theorem outer_commutator_odd_of_hom {C : Type*} [Group C] {A : Type*} [Group A]
    (hA : ∀ a b : A, a * b = b * a) (Θ : MulAut C →* A)
    (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range) :
    ¬ 2 ∣ Nat.card (commutator (Outer C)) := by
  have hle : inner C ≤ Θ.ker := by rw [hker]; exact le_rfl
  let Θ' : Outer C →* A := QuotientGroup.lift (inner C) Θ hle
  have hker' : Θ'.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : Θ a = 1 := hx
    have h2 : a ∈ (MulAut.conj : C →* MulAut C).range := hker ▸ h1
    exact (QuotientGroup.eq_one_iff (N := inner C) a).2 h2
  have hc : commutator (Outer C) = ⊥ :=
    eq_bot_iff.2 (hker' ▸ commutator_le_ker_of_comm Θ' hA)
  rw [hc, Subgroup.card_bot]
  omega

theorem F4_outer_commutator_odd (K : Type) [Field K] [Finite K] :
    ¬ 2 ∣ Nat.card (commutator (Outer (adjointGroup .F4 K))) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  by_cases h2 : ringChar K = 2
  · have hK2 : Nat.card K = 2 ^ (n : ℕ) := by rw [hK, h2]
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime :=
      finite_field_prime_power_characteristic Nat.prime_two n.pos hK2
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form n.pos K hK2
    exact outer_commutator_odd_of_hom (fun a b => mul_comm a b) Θ hker
  · obtain ⟨-, hΘ⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp h2 n.pos K hK .F4
      (Or.inl rfl)
    obtain ⟨Θ, -, -, hker, -⟩ := hΘ
    obtain ⟨-, hcyc⟩ := card_ringAut_and_isCyclic hp K hK
    have hcomm : ∀ a b : K ≃+* K, a * b = b * a := fun a b => by
      have := hcyc
      exact (IsCyclic.commGroup : CommGroup (K ≃+* K)).mul_comm a b
    exact outer_commutator_odd_of_hom hcomm Θ hker

theorem localCoreTrivialOn_noninner_F4 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) :
    LocalCoreTrivialOn p fun α : MulAut (adjointGroup .F4 K) =>
      α ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  by_cases h2 : ringChar K = 2
  · have hK2 : Nat.card K = 2 ^ (n : ℕ) := by rw [hK, h2]
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime :=
      finite_field_prime_power_characteristic Nat.prime_two n.pos hK2
    obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form n.pos K hK2
    exact localCoreTrivialOn_of_forall hp fun B hB α hα hαp => by
      obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α.1
      exact (even_F4_noninner_odd_prime_field_descent_and_local_core_trivial n.pos hK2 hp
        (by omega) B hB α hα hαp x a a.2 hxa).2.2.2.2
  · exact localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (odd_F4_noninner_prime_local_core_trivial hℓ h2 n.pos K hK hp B hB).1 α hα hαp

theorem planeLocalCoreOdd_F4_of_cyclic (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hcyc : ∀ Q : Subgroup (adjointGroup .F4 K), IsPGroup p Q → IsCyclic Q)
    (hcent : ∀ x : adjointGroup .F4 K, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    PlaneLocalCoreOdd p (adjointGroup .F4 K) :=
  planeLocalCoreOdd_of_cyclic_centralizers_abstract hp hp3 center_adjointGroup_eq_bot hcyc hcent
    (F4_outer_commutator_odd K) (localCoreTrivialOn_noninner_F4 K hp hp3)

theorem oddEndpoint_F4_of_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f →
      (∀ Q : Subgroup (adjointGroup Tag.F4 K), IsPGroup p Q → IsCyclic Q) ∧
        ∀ x : adjointGroup Tag.F4 K, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    OddEndpoint .F4 Cond := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  obtain ⟨hcyc, hcent⟩ := h K p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_F4_of_cyclic K hp hp3 hcyc hcent)).1

end CFSG.RankThree.PartOne.KE
