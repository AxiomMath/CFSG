module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
import CFSG.RankThree.Automorphisms.LinearCoprime
import CFSG.RankThree.Automorphisms.UnitaryCoprime
import CFSG.RankThree.Automorphisms.SymplecticCoprime
import CFSG.RankThree.Automorphisms.SuzukiCoprime
import CFSG.RankThree.Automorphisms.SmallReeCoprime
import CFSG.RankThree.Automorphisms.LargeReeCoprime
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.RankThree.SteinbergR3EOrdinaryCoprimeCyclic
import CFSG.RankThree.SteinbergR3EDiagramFixedCoprimeCyclic
import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
import CFSG.RankThree.Classical.OrthogonalOrderThree
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LieType.Ree.Duality

public section

open CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.Automorphisms CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem pSubgroupsCyclic_classical {T : Type} [Group T] [Finite T] {t : StatedLieTag}
    {n ℓ f p : ℕ} (hm : StatedClassicalModel T t n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) : PSubgroupsCyclic p T := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3_of_dvd : (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → 3 < p := fun ht => by
    have h3 := (CFSG.RankThree.Classical.orthogonal_model_exists_orderOf_eq_three ht hm).2
    have hp3 : p ≠ 3 := fun h => hpT (h ▸ h3)
    have := hp.two_le
    omega
  cases t with
  | PSL =>
    obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    let e' : T ≃* LinearFlag.projectiveSL n K :=
      eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
    have hpT' : ¬ p ∣ Nat.card (LinearFlag.projectiveSL n K) := by
      rwa [← Nat.card_congr e'.toEquiv]
    exact PSubgroupsCyclic.of_mulEquiv e'
      (linear_coprime_odd_prime_automorphism_subgroups_cyclic.{0} hn hp hodd hpT').1
  | PSU =>
    obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq' : ¬ (n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
    let e' : T ≃* ClassicalGroups.UnitaryFlag.unitaryPSU h n :=
      eT.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm
    have hpT' : ¬ p ∣ Nat.card (ClassicalGroups.UnitaryFlag.unitaryPSU h n) := by
      rwa [← Nat.card_congr e'.toEquiv]
    exact PSubgroupsCyclic.of_mulEquiv e'
      (unitary_coprime_odd_prime_automorphism_subgroups_cyclic.{0} h hn hq' hp hodd hpT').1
  | PSp =>
    obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    have hpT' : ¬ p ∣ Nat.card (StatedProj (StatedSp n K)) := by
      rwa [← Nat.card_congr eT.toEquiv]
    exact PSubgroupsCyclic.of_mulEquiv eT
      (symplectic_coprime_odd_prime_automorphism_subgroups_cyclic.{0} hn hp hodd hpT').1
  | POmegaOdd =>
    exact (orthogonal_coprime_large_prime_automorphism_subgroups_cyclic.{0} T .POmegaOdd
      (.inl rfl) n ℓ f hm hp (hp3_of_dvd (.inl rfl)) hpT).1
  | POmegaPlus =>
    exact (orthogonal_coprime_large_prime_automorphism_subgroups_cyclic.{0} T .POmegaPlus
      (.inr (.inl rfl)) n ℓ f hm hp (hp3_of_dvd (.inr (.inl rfl))) hpT).1
  | POmegaMinus =>
    exact (orthogonal_coprime_large_prime_automorphism_subgroups_cyclic.{0} T .POmegaMinus
      (.inr (.inr rfl)) n ℓ f hm hp (hp3_of_dvd (.inr (.inr rfl))) hpT).1
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact hm.2.elim

theorem pSubgroupsCyclic_untwisted
    {T : Type} [Group T] {τ : Tag} {q p : ℕ}
    (h : UntwistedChevalleyModel T τ q) (hp : p.Prime) (hp3 : 3 < p) (hpT : ¬ p ∣ Nat.card T) :
    PSubgroupsCyclic p T := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted h
  have hpC : ¬ p ∣ Nat.card (adjointGroup τ K) := by
    rwa [Nat.card_congr e.toEquiv]
  exact PSubgroupsCyclic.of_mulEquiv e.symm
    (ordinary_Chevalley_coprime_large_prime_automorphism_subgroups_cyclic.{0} τ K hp hp3 hpC).1

theorem pSubgroupsCyclic_twisted
    {T : Type} {t : TwistTag} {ℓ f p : ℕ} [Group T] (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (h : TwistedChevalleyModel T t (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p)
    (hpT : ¬ p ∣ Nat.card T) : PSubgroupsCyclic p T := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hℓ hf h
  have hpC : ¬ p ∣ Nat.card (CFSG.LieType.Chevalley.graphFixedRootGroup t K σ) := by
    rwa [Nat.card_congr e.toEquiv]
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : ∀ c, (RingEquiv.ofBijective σ hbij) c = c ^ (ℓ ^ f) := hσ
  have hpC' : ¬ p ∣ Nat.card (CFSG.LieType.Chevalley.graphFixedRootGroup t K
      (RingEquiv.ofBijective σ hbij).toRingHom) := hpC
  exact PSubgroupsCyclic.of_mulEquiv e.symm
    (diagram_fixed_coprime_large_prime_automorphism_subgroups_cyclic.{0} t hℓ hf K hK
      (RingEquiv.ofBijective σ hbij) hσ' hp hp3 hpC').1

theorem pSubgroupsCyclic_exceptional
    {T : Type} [Group T] [Finite T] {p : ℕ}
    (h : ExceptionalRep T) (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) :
    PSubgroupsCyclic p T := by
  rcases h with ⟨t, ℓ, f, ht, hm⟩ | ⟨t, ℓ, f, ht, hm⟩ | ⟨ℓ, f, hm⟩
  · have hp3 : 3 < p := by
      have h3 := CFSG.RankThree.Chevalley.Chevalley_exceptional_models_order_divisible_by_three
        T t ℓ f hm
      have hp3 : p ≠ 3 := fun h => hpT (h ▸ h3)
      have := hp.two_le
      omega
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    obtain ⟨⟨hℓ, hf, -⟩, hmod⟩ := hm
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pSubgroupsCyclic_untwisted hmod hp hp3 hpT
    · exact pSubgroupsCyclic_untwisted hmod hp hp3 hpT
    · exact pSubgroupsCyclic_untwisted hmod hp hp3 hpT
    · exact pSubgroupsCyclic_untwisted hmod hp hp3 hpT
    · exact pSubgroupsCyclic_untwisted hmod hp hp3 hpT
    · exact pSubgroupsCyclic_twisted hℓ hf hmod hp hp3 hpT
    · exact pSubgroupsCyclic_twisted hℓ hf hmod hp hp3 hpT
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact (small_Ree_coprime_automorphism_subgroups_cyclic.{0} T ℓ f hm hp hpT).1
    · obtain ⟨-, -, -, hℓ2, -, hiso⟩ := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier T ℓ f hm
      obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hm
      subst hℓ2
      have ha : 1 ≤ a := by
        have := hadm.2.2.2.2.2
        omega
      have : Fintype K := Fintype.ofFinite K
      have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
        rw [← Nat.card_eq_fintype_card, hK]
        rfl)
      obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
      have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
      have hpΓ : ¬ p ∣ Nat.card (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := by
        rwa [← Nat.card_congr E.toEquiv]
      exact PSubgroupsCyclic.of_mulEquiv E
        (large_Ree_coprime_odd_prime_automorphism_subgroups_cyclic.{0} a ha K hK' hp
          (hp.odd_of_ne_two hp2) hpΓ).1
    · have h2 := (Sporadic.Schreier.Tits.AT_Tits_model_Schreier T ℓ f hm).1
      exact PSubgroupsCyclic.of_not_dvd_card_mulAut hp
        (not_dvd_card_mulAut_of_not_dvd_outer hp hpT
          ((NoOddOuter.of_isPGroup_two h2) p hp hp2 hpT))
  · exact PSubgroupsCyclic.of_mulEquiv (MulEquiv.refl T)
      (Suzuki_coprime_odd_prime_automorphism_subgroups_cyclic.{0} T ℓ f hm hp
        (hp.odd_of_ne_two hp2) hpT).1

end CFSG.SignalizerFunctorTheorem.CatalogBridge
