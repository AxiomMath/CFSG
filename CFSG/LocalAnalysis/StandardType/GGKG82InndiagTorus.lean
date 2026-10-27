module

public import CFSG.LocalAnalysis.StandardType.GGKG82InndiagRoots

public section

namespace CFSG.StandardType.KG82

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix

theorem card_mul_le_of_lt {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {H H' : Subgroup G} (hle : H ≤ H') (hne : H ≠ H') (hH' : IsPGroup p H') :
    p * Nat.card H ≤ Nat.card H' := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hH'
  have hd : Nat.card H ∣ p ^ k := hk ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).1 hd
  have hjk : j ≠ k := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hk, hj']))
  rw [hj', hk, ← pow_succ']
  exact Nat.pow_le_pow_right hp.out.pos (by omega)

theorem card_closure_insert_ge {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : IsPGroup p A) {s : Set G} {g x : G} (hs : insert g s ⊆ A)
    (hsx : ∀ a ∈ s, Commute a x) (hgx : ¬ Commute g x) :
    p * Nat.card (Subgroup.closure s) ≤ Nat.card (Subgroup.closure (insert g s)) := by
  refine card_mul_le_of_lt (Subgroup.closure_mono (Set.subset_insert g s)) ?_
    (hA.to_le ((Subgroup.closure_le A).2 hs))
  intro h
  have hle : Subgroup.closure s ≤ Subgroup.centralizer {x} :=
    (Subgroup.closure_le _).2 fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hsx a ha).eq
  have hg : g ∈ Subgroup.closure s := h ▸ Subgroup.subset_closure (Set.mem_insert g s)
  exact hgx (Subgroup.mem_centralizer_singleton_iff.1 (hle hg))

section Gens

variable {K : Type} [Field K]

@[expose] noncomputable def diagGen (ζ : Kˣ) (k : Fin 2) : ModGL TwistTag.E6.tag K :=
  rootDiagUnit TwistTag.E6.tag (diagParam ζ (diagExp k))

@[expose] noncomputable def rankFiveGen
    (ζ : Kˣ) : Fin 2 ⊕ Fin 3 → ModGL TwistTag.E6.tag K
  | .inl k => diagGen ζ k
  | .inr i => leviY K (leviRoot i)

@[expose] noncomputable def rankFiveGroup
    (ζ : Kˣ) : Subgroup (ModGL TwistTag.E6.tag K) :=
  Subgroup.closure (Set.range (rankFiveGen ζ))

theorem rankFiveGen_mem (ζ : Kˣ)
    (a : Fin 2 ⊕ Fin 3) : rankFiveGen ζ a ∈ rankFiveGroup (K := K) ζ :=
  Subgroup.subset_closure ⟨a, rfl⟩

end Gens

section Comm

variable {K : Type} [Field K]

theorem rootChar_diagGen_eq_one (ζ : Kˣ) (k : Fin 2) :
    rootChar (diagParam ζ (diagExp k)) e6HighestRoot = 1 ∧
      ∀ i, rootChar (diagParam ζ (diagExp k)) (leviRoot i) = 1 := by
  refine ⟨?_, fun i => ?_⟩
  · rw [rootChar_diagParam, diagExp_facts.2.1 k, zpow_zero]
  · rw [rootChar_diagParam, diagExp_facts.2.2.1 k i, zpow_zero]

theorem commute_diagGen_pinnedX
    (ζ : Kˣ) (k : Fin 2) (i : Fin 3) (c : K) :
    Commute (diagGen ζ k) (pinnedX TwistTag.E6.tag K (leviRoot i) c) :=
  commute_rootDiagUnit_pinnedX (isRoot_leviRoot i) ((rootChar_diagGen_eq_one ζ k).2 i) c

theorem commute_diagGen_highRoot
    (ζ : Kˣ) (k : Fin 2) (c : K) :
    Commute (diagGen ζ k) (pinnedX TwistTag.E6.tag K e6HighestRoot c) :=
  commute_rootDiagUnit_pinnedX isRoot_e6HighestRoot (rootChar_diagGen_eq_one ζ k).1 c

theorem commute_diagGen_leviY
    (ζ : Kˣ) (k : Fin 2) (i : Fin 3) :
    Commute (diagGen ζ k) (leviY K (leviRoot i)) :=
  commute_rootDiagUnit_leviY (isRoot_leviRoot i) ((rootChar_diagGen_eq_one ζ k).2 i)

theorem commute_diagGen (ζ : Kˣ) (k l : Fin 2) :
    Commute (diagGen (K := K) ζ k) (diagGen ζ l) :=
  commute_rootDiagUnit _ _

theorem rankFiveGen_commute
    (ζ : Kˣ) (a b : Fin 2 ⊕ Fin 3) :
    Commute (rankFiveGen (K := K) ζ a) (rankFiveGen ζ b) := by
  rcases a with k | i <;> rcases b with l | j
  · exact commute_diagGen ζ k l
  · exact commute_diagGen_leviY ζ k j
  · exact (commute_diagGen_leviY ζ l i).symm
  · exact commute_leviY_leviY i j

theorem rankFiveGroup_le_centralizer
    (ζ : Kˣ) :
    rankFiveGroup (K := K) ζ ≤
      Subgroup.centralizer {pinnedX TwistTag.E6.tag K e6HighestRoot 1} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases a with k | i
  · exact (commute_diagGen_highRoot ζ k 1).eq
  · exact (commute_leviY_highRoot i 1).eq

theorem isElemAbelian_rankFiveGroup
    [CharP K 2] {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (rankFiveGroup (K := K) ζ) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact (rankFiveGen_commute ζ a b).eq
  · rintro _ ⟨a, rfl⟩
    rcases a with k | i
    · exact rootDiagUnit_pow_three (diagParam_pow_three hζ _)
    · exact leviY_pow_three (isRoot_leviRoot i)

theorem diagGen_test
    (ζ : Kˣ) (hζ1 : ζ ≠ 1) :
    ¬ Commute (diagGen ζ 0) (pinnedX TwistTag.E6.tag K (Pi.single 0 1) 1) ∧
      Commute (diagGen ζ 0) (pinnedX TwistTag.E6.tag K (Pi.single 2 1) 1) ∧
      ¬ Commute (diagGen ζ 1) (pinnedX TwistTag.E6.tag K (Pi.single 2 1) 1) := by
  refine ⟨not_commute_rootDiagUnit_pinnedX (isRoot_single _ 0) ?_,
    commute_rootDiagUnit_pinnedX (isRoot_single _ 2) ?_ 1,
    not_commute_rootDiagUnit_pinnedX (isRoot_single _ 2) ?_⟩
  · rw [rootChar_diagParam, diagExp_facts.2.2.2.1, zpow_one]
    exact hζ1
  · rw [rootChar_diagParam, diagExp_facts.2.2.2.2.1, zpow_zero]
  · rw [rootChar_diagParam, diagExp_facts.2.2.2.2.2, zpow_one]
    exact hζ1

theorem card_rankFiveGroup
    [CharP K 2] [Finite K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    3 ^ 5 ≤ Nat.card (rankFiveGroup (K := K) ζ) := by
  classical
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hA : IsPGroup 3 (rankFiveGroup (K := K) ζ) := (isElemAbelian_rankFiveGroup hζ).isPGroup
  obtain ⟨t1, t2, t3⟩ := diagGen_test (K := K) ζ hζ1
  set g : Fin 2 ⊕ Fin 3 → ModGL TwistTag.E6.tag K := rankFiveGen ζ with hg
  have hgA : ∀ a, g a ∈ (rankFiveGroup (K := K) ζ : Set (ModGL TwistTag.E6.tag K)) :=
    rankFiveGen_mem ζ
  have s1 : insert (g (.inl 0)) ∅ ⊆ (rankFiveGroup (K := K) ζ : Set (ModGL TwistTag.E6.tag K)) :=
    Set.insert_subset_iff.2 ⟨hgA _, Set.empty_subset _⟩
  have s2 : insert (g (.inl 1)) (insert (g (.inl 0)) ∅) ⊆
      (rankFiveGroup (K := K) ζ : Set (ModGL TwistTag.E6.tag K)) :=
    Set.insert_subset_iff.2 ⟨hgA _, s1⟩
  have s3 : insert (g (.inr 0)) (insert (g (.inl 1)) (insert (g (.inl 0)) ∅)) ⊆
      (rankFiveGroup (K := K) ζ : Set (ModGL TwistTag.E6.tag K)) :=
    Set.insert_subset_iff.2 ⟨hgA _, s2⟩
  have s4 : insert (g (.inr 1)) (insert (g (.inr 0)) (insert (g (.inl 1))
      (insert (g (.inl 0)) ∅))) ⊆ (rankFiveGroup (K := K) ζ : Set (ModGL TwistTag.E6.tag K)) :=
    Set.insert_subset_iff.2 ⟨hgA _, s3⟩
  have s5 : insert (g (.inr 2)) (insert (g (.inr 1)) (insert (g (.inr 0)) (insert (g (.inl 1))
      (insert (g (.inl 0)) ∅)))) ⊆ (rankFiveGroup (K := K) ζ : Set (ModGL TwistTag.E6.tag K)) :=
    Set.insert_subset_iff.2 ⟨hgA _, s4⟩
  have h1 := card_closure_insert_ge hA s1 (fun a ha => absurd ha (Set.notMem_empty a)) t1
  have h2 := card_closure_insert_ge hA s2 (fun a ha => by
    rw [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at ha
    rw [ha]
    exact t2) t3
  have h3 := card_closure_insert_ge hA s3 (x := pinnedX TwistTag.E6.tag K (leviRoot 0) 1)
    (fun a ha => by
      simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at ha
      rcases ha with ha | ha <;> rw [ha]
      · exact commute_diagGen_pinnedX ζ 1 0 1
      · exact commute_diagGen_pinnedX ζ 0 0 1)
    (not_commute_leviY (isRoot_leviRoot 0) (leviRoot_facts.2.2.2.1 0)
      (leviRoot_facts.2.2.2.2.1 0))
  have h4 := card_closure_insert_ge hA s4 (x := pinnedX TwistTag.E6.tag K (leviRoot 1) 1)
    (fun a ha => by
      simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at ha
      rcases ha with ha | ha | ha <;> rw [ha]
      · exact (commute_leviY_pinnedX h01 1).1
      · exact commute_diagGen_pinnedX ζ 1 1 1
      · exact commute_diagGen_pinnedX ζ 0 1 1)
    (not_commute_leviY (isRoot_leviRoot 1) (leviRoot_facts.2.2.2.1 1)
      (leviRoot_facts.2.2.2.2.1 1))
  have h5 := card_closure_insert_ge hA s5 (x := pinnedX TwistTag.E6.tag K (leviRoot 2) 1)
    (fun a ha => by
      simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at ha
      rcases ha with ha | ha | ha | ha <;> rw [ha]
      · exact (commute_leviY_pinnedX h12 1).1
      · exact (commute_leviY_pinnedX h02 1).1
      · exact commute_diagGen_pinnedX ζ 1 2 1
      · exact commute_diagGen_pinnedX ζ 0 2 1)
    (not_commute_leviY (isRoot_leviRoot 2) (leviRoot_facts.2.2.2.1 2)
      (leviRoot_facts.2.2.2.2.1 2))
  have h6 := Subgroup.card_le_of_le ((Subgroup.closure_le _).2 s5)
  rw [Subgroup.closure_empty, Subgroup.card_bot] at h1
  omega

theorem rankFiveGroup_le_twInndiagGroup
    [CharP K 2] [Finite K] (σ : K ≃+* K) {ζ : Kˣ}
    (hσζ : Units.map σ.toRingHom.toMonoidHom ζ = ζ⁻¹) :
    rankFiveGroup (K := K) ζ ≤ RecipeExcLang.twInndiagGroup K σ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, rfl⟩
  rcases a with k | i
  · exact RecipeExcLang.rootDiagUnit_mem_twInndiag
      (isCompatE6_diagParam hσζ (diagExp_facts.1 k))
  · exact RecipeExcLang.graphFixedRootGroup_le_twInndiag σ
      (leviY_mem_graphFixedRootGroup σ.toRingHom i)

end Comm

end CFSG.StandardType.KG82
