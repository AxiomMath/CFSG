module

public import CFSG.RankThree.PartOne.KP.Assembly
public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.RankThree.Automorphisms.LinearCoprime
public import CFSG.RankThree.Automorphisms.UnitaryCoprime
public import CFSG.RankThree.Automorphisms.SymplecticCoprime
public import CFSG.RankThree.Automorphisms.SuzukiCoprime
public import CFSG.RankThree.Automorphisms.SmallReeCoprime
public import CFSG.RankThree.Automorphisms.LargeReeCoprime
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.RankThree.SteinbergR3EDiagramFixedCoprimeCyclic
public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.Automorphisms CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem elementaryRankAtMostOne_of_cyclic_equiv {T G : Type*} [Group T] [Group G] {p : ℕ}
    (hp : p.Prime) (e : T ≃* G) (hG : ∀ P : Subgroup (MulAut G), IsPGroup p P → IsCyclic P) :
    ElementaryRankAtMostOne p (MulAut T) :=
  ElementaryRankAtMostOne.of_isCyclic hp fun _ hP => isCyclic_of_isPGroup_of_mulEquiv e hG hP

theorem elementaryRankAtMostOne_of_alternating {T : Type} [Group T] [Finite T] {n p : ℕ}
    (hn : 5 ≤ n) (e : T ≃* alternatingGroup (Fin n)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpT : ¬ p ∣ Nat.card T) : ElementaryRankAtMostOne p (MulAut T) := by
  have hpA : ¬ p ∣ Nat.card (alternatingGroup (Fin n)) := by
    rwa [← Nat.card_congr e.toEquiv]
  refine ElementaryRankAtMostOne.of_mulEquiv e
    (ElementaryRankAtMostOne.of_outer_card_lt hp hpA ?_)
  have h4 := card_outer_alternating_le_four hn
  have : 25 ≤ p ^ 2 := by nlinarith
  omega

theorem elementaryRankAtMostOne_of_untwisted {T : Type} [Group T] {τ : Tag} {q p : ℕ}
    (h : UntwistedChevalleyModel T τ q) (hp : p.Prime) (hp3 : 3 < p) (hpT : ¬ p ∣ Nat.card T) :
    ElementaryRankAtMostOne p (MulAut T) := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted h
  have hpC : ¬ p ∣ Nat.card (adjointGroup τ K) := by
    rwa [Nat.card_congr e.toEquiv]
  exact elementaryRankAtMostOne_of_cyclic_equiv hp e.symm
    (ordinary_Chevalley_coprime_large_prime_automorphism_subgroups_cyclic.{0} τ K hp hp3 hpC).1

theorem elementaryRankAtMostOne_of_twisted {T : Type} [Group T] {t : TwistTag} {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h : TwistedChevalleyModel T t (ℓ ^ f)) (hp : p.Prime)
    (hp3 : 3 < p) (hpT : ¬ p ∣ Nat.card T) : ElementaryRankAtMostOne p (MulAut T) := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hℓ hf h
  have hpC : ¬ p ∣ Nat.card (CFSG.LieType.Chevalley.graphFixedRootGroup t K σ) := by
    rwa [Nat.card_congr e.toEquiv]
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : ∀ c, (RingEquiv.ofBijective σ hbij) c = c ^ (ℓ ^ f) := hσ
  have hpC' : ¬ p ∣ Nat.card (CFSG.LieType.Chevalley.graphFixedRootGroup t K
      (RingEquiv.ofBijective σ hbij).toRingHom) := hpC
  exact elementaryRankAtMostOne_of_cyclic_equiv hp e.symm
    (diagram_fixed_coprime_large_prime_automorphism_subgroups_cyclic.{0} t hℓ hf K hK
      (RingEquiv.ofBijective σ hbij) hσ' hp hp3 hpC').1

theorem elementaryRankAtMostOne_of_classical {T : Type} [Group T] {t : StatedLieTag}
    {n ℓ f p : ℕ} (hm : StatedClassicalModel T t n ℓ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpT : ¬ p ∣ Nat.card T) : ElementaryRankAtMostOne p (MulAut T) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  cases t with
  | PSL =>
    obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    let e' : T ≃* LinearFlag.projectiveSL n K :=
      eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
    have hpT' : ¬ p ∣ Nat.card (LinearFlag.projectiveSL n K) := by
      rwa [← Nat.card_congr e'.toEquiv]
    exact elementaryRankAtMostOne_of_cyclic_equiv hp e'
      (linear_coprime_odd_prime_automorphism_subgroups_cyclic.{0} hn hp hodd hpT').1
  | PSU =>
    obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    have h : UnitaryFieldData ℓ f K :=
      ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq' : ¬ (n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
    let e' : T ≃* ClassicalGroups.UnitaryFlag.unitaryPSU h n :=
      eT.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm
    have hpT' : ¬ p ∣ Nat.card (ClassicalGroups.UnitaryFlag.unitaryPSU h n) := by
      rwa [← Nat.card_congr e'.toEquiv]
    exact elementaryRankAtMostOne_of_cyclic_equiv hp e'
      (unitary_coprime_odd_prime_automorphism_subgroups_cyclic.{0} h hn hq' hp hodd hpT').1
  | PSp =>
    obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    have hpT' : ¬ p ∣ Nat.card (StatedProj (StatedSp n K)) := by
      rwa [← Nat.card_congr eT.toEquiv]
    exact elementaryRankAtMostOne_of_cyclic_equiv hp eT
      (symplectic_coprime_odd_prime_automorphism_subgroups_cyclic.{0} hn hp hodd hpT').1
  | POmegaOdd =>
    exact ElementaryRankAtMostOne.of_isCyclic hp
      (orthogonal_coprime_large_prime_automorphism_subgroups_cyclic.{0} T .POmegaOdd (.inl rfl) n ℓ
        f hm hp (by omega) hpT).1
  | POmegaPlus =>
    exact ElementaryRankAtMostOne.of_isCyclic hp
      (orthogonal_coprime_large_prime_automorphism_subgroups_cyclic.{0} T .POmegaPlus
        (.inr (.inl rfl)) n ℓ f hm hp (by omega) hpT).1
  | POmegaMinus =>
    exact ElementaryRankAtMostOne.of_isCyclic hp
      (orthogonal_coprime_large_prime_automorphism_subgroups_cyclic.{0} T .POmegaMinus
        (.inr (.inr rfl)) n ℓ f hm hp (by omega) hpT).1
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact hm.2.elim

theorem elementaryRankAtMostOne_of_smallRee {T : Type} [Group T] {ℓ f p : ℕ}
    (hm : ReeTitsModel T .twistedG2 ℓ f) (hp : p.Prime) (hpT : ¬ p ∣ Nat.card T) :
    ElementaryRankAtMostOne p (MulAut T) :=
  ElementaryRankAtMostOne.of_isCyclic hp
    (small_Ree_coprime_automorphism_subgroups_cyclic.{0} T ℓ f hm hp hpT).1

theorem elementaryRankAtMostOne_of_largeRee {T : Type} [Group T] {ℓ f p : ℕ}
    (hm : ReeTitsModel T .twistedF4 ℓ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpT : ¬ p ∣ Nat.card T) : ElementaryRankAtMostOne p (MulAut T) := by
  obtain ⟨-, -, -, hℓ2, -, hiso⟩ := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier T ℓ f hm
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
  exact elementaryRankAtMostOne_of_cyclic_equiv hp E
    (large_Ree_coprime_odd_prime_automorphism_subgroups_cyclic.{0} a ha K hK' hp
      (hp.odd_of_ne_two (by omega)) hpΓ).1

theorem elementaryRankAtMostOne_of_tits {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : ReeTitsModel T .Tits ℓ f) (hp : p.Prime) (hp5 : 5 ≤ p) (hpT : ¬ p ∣ Nat.card T) :
    ElementaryRankAtMostOne p (MulAut T) := by
  refine ElementaryRankAtMostOne.of_not_dvd_outer hp hpT fun hdvd => ?_
  obtain ⟨k, hk⟩ := (Sporadic.Schreier.Tits.AT_Tits_model_Schreier T ℓ f hm).1.exists_card_eq
  rw [hk] at hdvd
  have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
  omega

theorem elementaryRankAtMostOne_of_exceptional {T : Type} [Group T] [Finite T] {p : ℕ}
    (h : ExceptionalRep T) (hp : p.Prime) (hp5 : 5 ≤ p) (hpT : ¬ p ∣ Nat.card T) :
    ElementaryRankAtMostOne p (MulAut T) := by
  rcases h with ⟨t, ℓ, f, ht, hm⟩ | ⟨t, ℓ, f, ht, hm⟩ | ⟨ℓ, f, hm⟩
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    obtain ⟨⟨hℓ, hf, -⟩, hmod⟩ := hm
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact elementaryRankAtMostOne_of_untwisted hmod hp (by omega) hpT
    · exact elementaryRankAtMostOne_of_untwisted hmod hp (by omega) hpT
    · exact elementaryRankAtMostOne_of_untwisted hmod hp (by omega) hpT
    · exact elementaryRankAtMostOne_of_untwisted hmod hp (by omega) hpT
    · exact elementaryRankAtMostOne_of_untwisted hmod hp (by omega) hpT
    · exact elementaryRankAtMostOne_of_twisted hℓ hf hmod hp (by omega) hpT
    · exact elementaryRankAtMostOne_of_twisted hℓ hf hmod hp (by omega) hpT
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact elementaryRankAtMostOne_of_smallRee hm hp hpT
    · exact elementaryRankAtMostOne_of_largeRee hm hp hp5 hpT
    · exact elementaryRankAtMostOne_of_tits hm hp hp5 hpT
  · exact ElementaryRankAtMostOne.of_isCyclic hp
      (Suzuki_coprime_odd_prime_automorphism_subgroups_cyclic.{0} T ℓ f hm hp
        (hp.odd_of_ne_two (by omega)) hpT).1

theorem catalogCoprimeAutomorphismRankOneOrJ4BM_of_sporadic
    (hsp : ∀ s : TauCeti.SporadicName, s ≠ .J4 → s ≠ .B → s ≠ .M → SporadicCoprimeRank s) :
    CatalogCoprimeAutomorphismRankOneOrJ4BM := by
  intro T _ _ _ hnab hcat p hp hp5 hpT
  rcases hcat with ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hm⟩ | hexc | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact Or.inr (Or.inr (Or.inr (elementaryRankAtMostOne_of_alternating hn e hp hp5 hpT)))
  · exact Or.inr (Or.inr (Or.inr (elementaryRankAtMostOne_of_classical hm hp hp5 hpT)))
  · exact Or.inr (Or.inr (Or.inr (elementaryRankAtMostOne_of_exceptional hexc hp hp5 hpT)))
  · by_cases h4 : s = .J4
    · subst h4
      exact Or.inl ⟨e⟩
    by_cases hB : s = .B
    · subst hB
      exact Or.inr (Or.inl ⟨e⟩)
    by_cases hM : s = .M
    · subst hM
      exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    exact Or.inr (Or.inr (Or.inr (hsp s h4 hB hM T ⟨e⟩ p hp hp5 hpT)))

end CFSG.RankThree.PartOne
