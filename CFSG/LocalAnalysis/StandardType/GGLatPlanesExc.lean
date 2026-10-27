module

public import CFSG.LocalAnalysis.StandardType.GGLatPlanes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Exceptional

private def reachNbrs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun d => A c d ≠ 0

private def reachSet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℕ → Fin n → Finset (Fin n)
  | 0, a => {a}
  | k + 1, a => reachSet A k a ∪ (reachSet A k a).biUnion (reachNbrs A)

private def reachProfile {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (a : Fin n) : Fin n → ℕ :=
  fun k => (reachSet A k.val a).card

private lemma reachSet_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (π : Equiv.Perm (Fin n))
    (hπ : ∀ i j, A (π i) (π j) = A i j) (k : ℕ) (a : Fin n) :
    reachSet A k (π a) = (reachSet A k a).image π := by
  induction k generalizing a with
  | zero => simp [reachSet]
  | succ k ih =>
      have hnbr : ∀ c, reachNbrs A (π c) = (reachNbrs A c).image π := by
        intro c
        ext d
        simp only [reachNbrs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hd
          refine ⟨π.symm d, ?_, by simp⟩
          have hcd : A (π c) (π (π.symm d)) = A c (π.symm d) := hπ c (π.symm d)
          rw [Equiv.apply_symm_apply] at hcd
          rwa [hcd] at hd
        · rintro ⟨e, he, rfl⟩
          have hce : A (π c) (π e) = A c e := hπ c e
          rwa [hce]
      simp only [reachSet]
      rw [ih a, Finset.image_union]
      congr 1
      rw [Finset.image_biUnion]
      simp_rw [hnbr]
      rw [Finset.biUnion_image]

private lemma reachProfile_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (π : Equiv.Perm (Fin n))
    (hπ : ∀ i j, A (π i) (π j) = A i j) (a : Fin n) :
    reachProfile A (π a) = reachProfile A a := by
  funext k
  rw [reachProfile, reachProfile, reachSet_perm A π hπ k.val a,
    Finset.card_image_of_injective _ π.injective]

private lemma nodesConnected_of_parent {N : ℕ} (G : SimpleGraph (Fin N)) (T : Set (Fin N))
    (base : Fin N) (b : ℕ) (hbase : base ∈ T) (hbaseval : base.val = b)
    (hparent : ∀ m : Fin N, m ∈ T → m.val ≠ b →
      ∃ p : Fin N, p ∈ T ∧ p.val < m.val ∧ G.Adj p m) :
    (G.induce T).Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable (G.induce T)).mpr ⟨⟨base, hbase⟩, ?_⟩
  intro w
  obtain ⟨wv, hwT⟩ := w
  have key : ∀ n, ∀ m : Fin N, m.val = n → (hmT : m ∈ T) →
      (G.induce T).Reachable ⟨base, hbase⟩ ⟨m, hmT⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hmval hmT
      by_cases h2 : m.val = b
      · have hm : m = base := Fin.ext (by rw [h2, hbaseval])
        subst hm
        exact SimpleGraph.Reachable.rfl
      · obtain ⟨p, hpT, hplt, hadj⟩ := hparent m hmT h2
        have ihp : (G.induce T).Reachable ⟨base, hbase⟩ ⟨p, hpT⟩ :=
          ih p.val (by rw [← hmval]; exact hplt) p rfl hpT
        have hadj' : (G.induce T).Adj ⟨p, hpT⟩ ⟨m, hmT⟩ := by
          rwa [SimpleGraph.induce_adj]
        exact ihp.trans hadj'.reachable
  exact key wv.val wv rfl hwT

private def F4M : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]

private def E6M : Matrix (Fin 6) (Fin 6) ℤ := Tag.cartanE 6

private def E7M : Matrix (Fin 7) (Fin 7) ℤ := Tag.cartanE 7

private def E8M : Matrix (Fin 8) (Fin 8) ℤ := Tag.cartanE 8

private lemma cartan_F4_eq : Tag.cartan .F4 = F4M := rfl

private lemma cartan_E6_eq : Tag.cartan .E6 = E6M := rfl

private lemma cartan_E7_eq : Tag.cartan .E7 = E7M := rfl

private lemma cartan_E8_eq : Tag.cartan .E8 = E8M := rfl

private lemma diagAut_F4_eq_one (π : Equiv.Perm (Fin 4))
    (hπ : ∀ i j, F4M (π i) (π j) = F4M i j) : π = 1 := by
  have h21 : F4M (π 2) (π 1) = -2 := by
    have h := hπ 2 1
    rwa [show F4M 2 1 = -2 by decide] at h
  have hkey : ∀ a b : Fin 4, F4M a b = -2 → a = 2 ∧ b = 1 := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      first
        | exact ⟨rfl, rfl⟩
        | exact absurd h (by decide)
  obtain ⟨h2, h1⟩ : π 2 = 2 ∧ π 1 = 1 := hkey (π 2) (π 1) h21
  have h10 : F4M 1 (π 0) = -1 := by
    have h := hπ 1 0
    rw [h1] at h
    rwa [show F4M 1 0 = -1 by decide] at h
  have h0 : π 0 = 0 := by
    have hkey1 : ∀ a : Fin 4, F4M 1 a = -1 → a = 0 ∨ a = 2 := by
      intro a h
      fin_cases a <;>
        first
          | exact Or.inl rfl
          | exact Or.inr rfl
          | exact absurd h (by decide)
    rcases hkey1 (π 0) h10 with h | h
    · exact h
    · exact absurd (π.injective (h.trans h2.symm)) (by decide)
  have h23 : F4M 2 (π 3) = -1 := by
    have h := hπ 2 3
    rw [h2] at h
    rwa [show F4M 2 3 = -1 by decide] at h
  have h3 : π 3 = 3 := by
    have hkey2 : ∀ a : Fin 4, F4M 2 a = -1 → a = 3 := by
      intro a h
      fin_cases a <;>
        first
          | rfl
          | exact absurd h (by decide)
    exact hkey2 (π 3) h23
  apply Equiv.ext
  intro a
  fin_cases a <;> simp [h0, h1, h2, h3]

private lemma diagAut_E7_eq_one (π : Equiv.Perm (Fin 7))
    (hπ : ∀ i j, E7M (π i) (π j) = E7M i j) : π = 1 := by
  have huniq : ∀ a b : Fin 7,
      reachProfile E7M a = reachProfile E7M b → a = b := by decide
  apply Equiv.ext
  intro a
  simpa using huniq (π a) a (reachProfile_perm E7M π hπ a)

private lemma diagAut_E8_eq_one (π : Equiv.Perm (Fin 8))
    (hπ : ∀ i j, E8M (π i) (π j) = E8M i j) : π = 1 := by
  have huniq : ∀ a b : Fin 8,
      reachProfile E8M a = reachProfile E8M b → a = b := by decide
  apply Equiv.ext
  intro a
  simpa using huniq (π a) a (reachProfile_perm E8M π hπ a)

private def gamma : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 2 4

private lemma gamma_apply_0 : gamma 0 = 5 := by decide
private lemma gamma_apply_5 : gamma 5 = 0 := by decide
private lemma gamma_apply_2 : gamma 2 = 4 := by decide
private lemma gamma_apply_4 : gamma 4 = 2 := by decide
private lemma gamma_apply_1 : gamma 1 = 1 := by decide

private lemma sameCycle_gamma_0 (m : Fin 6) : gamma.SameCycle 0 m ↔ m = 0 ∨ m = 5 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    have hpair : ∀ i : ℕ,
        ((gamma ^ i) 0 = 0 ∨ (gamma ^ i) 0 = 5) ∧
        ((gamma ^ i) 5 = 0 ∨ (gamma ^ i) 5 = 5) := by
      intro i
      induction i with
      | zero => exact ⟨Or.inl rfl, Or.inr rfl⟩
      | succ i ih =>
          obtain ⟨ih0, ih5⟩ := ih
          refine ⟨?_, ?_⟩
          · rw [pow_succ, Equiv.Perm.mul_apply, gamma_apply_0]; exact ih5
          · rw [pow_succ, Equiv.Perm.mul_apply, gamma_apply_5]; exact ih0
    rw [← hi]; exact (hpair i).1
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl gamma 0
    · exact ⟨(1 : ℤ), by decide⟩

private lemma sameCycle_gamma_1 (m : Fin 6) : gamma.SameCycle 1 m ↔ m = 1 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    have hfix : ∀ i : ℕ, (gamma ^ i) 1 = 1 := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ, Equiv.Perm.mul_apply, gamma_apply_1, ih]
    rw [← hi]; exact hfix i
  · rintro rfl
    exact Equiv.Perm.SameCycle.refl gamma 1

private lemma diagAut_E6_eq_one_or_gamma (π : Equiv.Perm (Fin 6))
    (hπ : ∀ i j, E6M (π i) (π j) = E6M i j) :
    π = 1 ∨ π = gamma := by
  have hp : ∀ a, reachProfile E6M (π a) = reachProfile E6M a :=
    fun a => reachProfile_perm E6M π hπ a
  have hcl0 : ∀ b : Fin 6, reachProfile E6M b = reachProfile E6M 0 → b = 0 ∨ b = 5 := by
    decide
  have hcl1 : ∀ b : Fin 6, reachProfile E6M b = reachProfile E6M 1 → b = 1 := by decide
  have hcl2 : ∀ b : Fin 6, reachProfile E6M b = reachProfile E6M 2 → b = 2 ∨ b = 4 := by
    decide
  have hcl3 : ∀ b : Fin 6, reachProfile E6M b = reachProfile E6M 3 → b = 3 := by decide
  have hcl4 : ∀ b : Fin 6, reachProfile E6M b = reachProfile E6M 4 → b = 2 ∨ b = 4 := by
    decide
  have hcl5 : ∀ b : Fin 6, reachProfile E6M b = reachProfile E6M 5 → b = 0 ∨ b = 5 := by
    decide
  have h0 := hcl0 (π 0) (hp 0)
  have h1 : π 1 = 1 := hcl1 (π 1) (hp 1)
  have h2 := hcl2 (π 2) (hp 2)
  have h3 : π 3 = 3 := hcl3 (π 3) (hp 3)
  have h4 := hcl4 (π 4) (hp 4)
  have h5 := hcl5 (π 5) (hp 5)
  have hcouple : (π 0 = 0 ∧ π 2 = 2) ∨ (π 0 = 5 ∧ π 2 = 4) := by
    rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2
    · exact Or.inl ⟨h0, h2⟩
    · exfalso
      have h := hπ 0 2
      rw [h0, h2] at h
      exact (by decide : E6M 0 4 ≠ E6M 0 2) h
    · exfalso
      have h := hπ 0 2
      rw [h0, h2] at h
      exact (by decide : E6M 5 2 ≠ E6M 0 2) h
    · exact Or.inr ⟨h0, h2⟩
  rcases hcouple with ⟨h00, h22⟩ | ⟨h05, h24⟩
  · left
    have h44 : π 4 = 4 := by
      rcases h4 with h | h
      · exact absurd (π.injective (h.trans h22.symm)) (by decide)
      · exact h
    have h55 : π 5 = 5 := by
      rcases h5 with h | h
      · exact absurd (π.injective (h.trans h00.symm)) (by decide)
      · exact h
    apply Equiv.ext
    intro a
    rcases (by decide : ∀ a : Fin 6, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5) a with
      rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [h00]
    · simpa [h1]
    · simpa [h22]
    · simpa [h3]
    · simpa [h44]
    · simpa [h55]
  · right
    have h42 : π 4 = 2 := by
      rcases h4 with h | h
      · exact h
      · exact absurd (π.injective (h.trans h24.symm)) (by decide)
    have h50 : π 5 = 0 := by
      rcases h5 with h | h
      · exact h
      · exact absurd (π.injective (h.trans h05.symm)) (by decide)
    apply Equiv.ext
    intro a
    rcases (by decide : ∀ a : Fin 6, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5) a with
      rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h05]; decide
    · rw [h1]; decide
    · rw [h24]; decide
    · rw [h3]; decide
    · rw [h42]; decide
    · rw [h50]; decide

private def latPlaneCore {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N)) : Prop :=
  ∃ i j k : Fin N, ¬ π.SameCycle i j ∧ π k = k ∧ ¬ π.SameCycle i k ∧ ¬ π.SameCycle j k ∧
    ((SimpleGraph.fromRel fun a b : Fin N => A a b ≠ 0).induce
        {m : Fin N | ¬ π.SameCycle i m ∧ ¬ π.SameCycle j m}).Connected ∧
    (3 ≤ Set.ncard {m : Fin N | ¬ π.SameCycle i m ∧ ¬ π.SameCycle j m} ∨
      ∃ m m' : Fin N, m ≠ m' ∧ (¬ π.SameCycle i m ∧ ¬ π.SameCycle j m) ∧
        (¬ π.SameCycle i m' ∧ ¬ π.SameCycle j m') ∧ 2 ≤ A m m' * A m' m)

private lemma latPlane_F4 (f : ℕ) (π : Equiv.Perm (Fin (ggU .F4 6 f).D.rank))
    (hπ : IsDiagAut (ggU .F4 6 f).D π) : LatPlane (ggU .F4 6 f).D π := by
  have hπ' : ∀ i j, F4M (π i) (π j) = F4M i j := by
    intro i j
    have h := hπ i j
    rwa [ggU_cartan_F4, cartan_F4_eq] at h
  have hpi : π = 1 := diagAut_F4_eq_one π hπ'
  rw [hpi]
  show latPlaneCore F4M (1 : Equiv.Perm (Fin 4))
  have hset : {m : Fin 4 | ¬ (1 : Equiv.Perm (Fin 4)).SameCycle 0 m ∧
      ¬ (1 : Equiv.Perm (Fin 4)).SameCycle 3 m} = {m : Fin 4 | m ≠ 0 ∧ m ≠ 3} := by
    ext m
    simp only [Equiv.Perm.sameCycle_one, ne_eq]
    constructor <;> intro h <;> exact ⟨fun h0 => h.1 h0.symm, fun h1 => h.2 h1.symm⟩
  refine ⟨0, 3, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · rfl
  · decide
  · decide
  · rw [hset]
    exact nodesConnected_of_parent
      (G := SimpleGraph.fromRel fun i j : Fin 4 => F4M i j ≠ 0)
      (T := {m : Fin 4 | m ≠ 0 ∧ m ≠ 3}) (base := 1) (b := 1) (by decide) rfl
      (by intro m hm h2; fin_cases m <;> simp_all <;> decide)
  · right
    exact ⟨1, 2, by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

private lemma latPlane_E7 (f : ℕ) (π : Equiv.Perm (Fin (ggU .E7 6 f).D.rank))
    (hπ : IsDiagAut (ggU .E7 6 f).D π) : LatPlane (ggU .E7 6 f).D π := by
  have hπ' : ∀ i j, E7M (π i) (π j) = E7M i j := by
    intro i j
    have h := hπ i j
    rwa [ggU_cartan_E7, cartan_E7_eq] at h
  have hpi : π = 1 := diagAut_E7_eq_one π hπ'
  rw [hpi]
  show latPlaneCore E7M (1 : Equiv.Perm (Fin 7))
  have hset : {m : Fin 7 | ¬ (1 : Equiv.Perm (Fin 7)).SameCycle 0 m ∧
      ¬ (1 : Equiv.Perm (Fin 7)).SameCycle 1 m} = {m : Fin 7 | m ≠ 0 ∧ m ≠ 1} := by
    ext m
    simp only [Equiv.Perm.sameCycle_one, ne_eq]
    constructor <;> intro h <;> exact ⟨fun h0 => h.1 h0.symm, fun h1 => h.2 h1.symm⟩
  refine ⟨0, 1, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · rfl
  · decide
  · decide
  · rw [hset]
    exact nodesConnected_of_parent
      (G := SimpleGraph.fromRel fun i j : Fin 7 => E7M i j ≠ 0)
      (T := {m : Fin 7 | m ≠ 0 ∧ m ≠ 1}) (base := 2) (b := 2) (by decide) rfl
      (by intro m hm h2; fin_cases m <;> simp_all <;> decide)
  · left
    rw [hset]
    have hsub : (↑({2, 3, 4} : Finset (Fin 7)) : Set (Fin 7)) ⊆
        {m : Fin 7 | m ≠ 0 ∧ m ≠ 1} := by
      intro m hm
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
        Set.mem_setOf_eq] at hm ⊢
      rcases hm with rfl | rfl | rfl <;> decide
    calc 3 = (↑({2, 3, 4} : Finset (Fin 7)) : Set (Fin 7)).ncard := by
          rw [Set.ncard_coe_finset]; decide
      _ ≤ ({m : Fin 7 | m ≠ 0 ∧ m ≠ 1} : Set (Fin 7)).ncard :=
          Set.ncard_le_ncard hsub

private lemma latPlane_E8 (f : ℕ) (π : Equiv.Perm (Fin (ggU .E8 6 f).D.rank))
    (hπ : IsDiagAut (ggU .E8 6 f).D π) : LatPlane (ggU .E8 6 f).D π := by
  have hπ' : ∀ i j, E8M (π i) (π j) = E8M i j := by
    intro i j
    have h := hπ i j
    rwa [ggU_cartan_E8, cartan_E8_eq] at h
  have hpi : π = 1 := diagAut_E8_eq_one π hπ'
  rw [hpi]
  show latPlaneCore E8M (1 : Equiv.Perm (Fin 8))
  have hset : {m : Fin 8 | ¬ (1 : Equiv.Perm (Fin 8)).SameCycle 0 m ∧
      ¬ (1 : Equiv.Perm (Fin 8)).SameCycle 1 m} = {m : Fin 8 | m ≠ 0 ∧ m ≠ 1} := by
    ext m
    simp only [Equiv.Perm.sameCycle_one, ne_eq]
    constructor <;> intro h <;> exact ⟨fun h0 => h.1 h0.symm, fun h1 => h.2 h1.symm⟩
  refine ⟨0, 1, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · rfl
  · decide
  · decide
  · rw [hset]
    exact nodesConnected_of_parent
      (G := SimpleGraph.fromRel fun i j : Fin 8 => E8M i j ≠ 0)
      (T := {m : Fin 8 | m ≠ 0 ∧ m ≠ 1}) (base := 2) (b := 2) (by decide) rfl
      (by intro m hm h2; fin_cases m <;> simp_all <;> decide)
  · left
    rw [hset]
    have hsub : (↑({2, 3, 4} : Finset (Fin 8)) : Set (Fin 8)) ⊆
        {m : Fin 8 | m ≠ 0 ∧ m ≠ 1} := by
      intro m hm
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
        Set.mem_setOf_eq] at hm ⊢
      rcases hm with rfl | rfl | rfl <;> decide
    calc 3 = (↑({2, 3, 4} : Finset (Fin 8)) : Set (Fin 8)).ncard := by
          rw [Set.ncard_coe_finset]; decide
      _ ≤ ({m : Fin 8 | m ≠ 0 ∧ m ≠ 1} : Set (Fin 8)).ncard :=
          Set.ncard_le_ncard hsub

private lemma latPlane_E6 (f : ℕ) (π : Equiv.Perm (Fin (ggU .E6 6 f).D.rank))
    (hπ : IsDiagAut (ggU .E6 6 f).D π) : LatPlane (ggU .E6 6 f).D π := by
  have hπ' : ∀ i j, E6M (π i) (π j) = E6M i j := by
    intro i j
    have h := hπ i j
    rwa [ggU_cartan_E6, cartan_E6_eq] at h
  rcases diagAut_E6_eq_one_or_gamma π hπ' with hpi | hpi
  · rw [hpi]
    show latPlaneCore E6M (1 : Equiv.Perm (Fin 6))
    have hset : {m : Fin 6 | ¬ (1 : Equiv.Perm (Fin 6)).SameCycle 0 m ∧
        ¬ (1 : Equiv.Perm (Fin 6)).SameCycle 1 m} = {m : Fin 6 | m ≠ 0 ∧ m ≠ 1} := by
      ext m
      simp only [Equiv.Perm.sameCycle_one, ne_eq]
      constructor <;> intro h <;> exact ⟨fun h0 => h.1 h0.symm, fun h1 => h.2 h1.symm⟩
    refine ⟨0, 1, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide
    · rfl
    · decide
    · decide
    · rw [hset]
      exact nodesConnected_of_parent
        (G := SimpleGraph.fromRel fun i j : Fin 6 => E6M i j ≠ 0)
        (T := {m : Fin 6 | m ≠ 0 ∧ m ≠ 1}) (base := 2) (b := 2) (by decide) rfl
        (by intro m hm h2; fin_cases m <;> simp_all <;> decide)
    · left
      rw [hset]
      have hsub : (↑({2, 3, 4} : Finset (Fin 6)) : Set (Fin 6)) ⊆
          {m : Fin 6 | m ≠ 0 ∧ m ≠ 1} := by
        intro m hm
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
          Set.mem_setOf_eq] at hm ⊢
        rcases hm with rfl | rfl | rfl <;> decide
      calc 3 = (↑({2, 3, 4} : Finset (Fin 6)) : Set (Fin 6)).ncard := by
            rw [Set.ncard_coe_finset]; decide
        _ ≤ ({m : Fin 6 | m ≠ 0 ∧ m ≠ 1} : Set (Fin 6)).ncard :=
            Set.ncard_le_ncard hsub
  · rw [hpi]
    show latPlaneCore E6M gamma
    have hset : {m : Fin 6 | ¬ gamma.SameCycle 0 m ∧ ¬ gamma.SameCycle 1 m} =
        {m : Fin 6 | m = 2 ∨ m = 3 ∨ m = 4} := by
      ext m
      simp only [Set.mem_setOf_eq]
      rw [sameCycle_gamma_0 m, sameCycle_gamma_1 m]
      fin_cases m <;> decide
    refine ⟨0, 1, 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sameCycle_gamma_0]; decide
    · decide
    · rw [sameCycle_gamma_0]; decide
    · rw [sameCycle_gamma_1]; decide
    · rw [hset]
      exact nodesConnected_of_parent
        (G := SimpleGraph.fromRel fun i j : Fin 6 => E6M i j ≠ 0)
        (T := {m : Fin 6 | m = 2 ∨ m = 3 ∨ m = 4}) (base := 2) (b := 2) (by decide) rfl
        (by intro m hm h2; fin_cases m <;> simp_all <;> decide)
    · left
      rw [hset]
      have hsub : (↑({2, 3, 4} : Finset (Fin 6)) : Set (Fin 6)) ⊆
          {m : Fin 6 | m = 2 ∨ m = 3 ∨ m = 4} := by
        intro m hm
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
          Set.mem_setOf_eq] at hm ⊢
        rcases hm with rfl | rfl | rfl <;> decide
      calc 3 = (↑({2, 3, 4} : Finset (Fin 6)) : Set (Fin 6)).ncard := by
            rw [Set.ncard_coe_finset]; decide
        _ ≤ ({m : Fin 6 | m = 2 ∨ m = 3 ∨ m = 4} : Set (Fin 6)).ncard :=
            Set.ncard_le_ncard hsub

theorem latPlane_exc (τ : StatedLieTag) (f : ℕ) (hτ : GGExcFive τ)
    (π : Equiv.Perm (Fin (ggU (absTag τ) 6 f).D.rank))
    (hπ : IsDiagAut (ggU (absTag τ) 6 f).D π) : LatPlane (ggU (absTag τ) 6 f).D π := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact latPlane_F4 f π hπ
  · exact latPlane_E6 f π hπ
  · exact latPlane_E7 f π hπ
  · exact latPlane_E8 f π hπ
  · exact latPlane_E6 f π hπ

private lemma gamma_apply_3 : gamma 3 = 3 := by decide

private lemma sameCycle_gamma_2 (m : Fin 6) : gamma.SameCycle 2 m ↔ m = 2 ∨ m = 4 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    have hpair : ∀ i : ℕ,
        ((gamma ^ i) 2 = 2 ∨ (gamma ^ i) 2 = 4) ∧
        ((gamma ^ i) 4 = 2 ∨ (gamma ^ i) 4 = 4) := by
      intro i
      induction i with
      | zero => exact ⟨Or.inl rfl, Or.inr rfl⟩
      | succ i ih =>
          obtain ⟨ih2, ih4⟩ := ih
          refine ⟨?_, ?_⟩
          · rw [pow_succ, Equiv.Perm.mul_apply, gamma_apply_2]; exact ih4
          · rw [pow_succ, Equiv.Perm.mul_apply, gamma_apply_4]; exact ih2
    rw [← hi]; exact (hpair i).1
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl gamma 2
    · exact ⟨(1 : ℤ), by decide⟩

private lemma sameCycle_gamma_3 (m : Fin 6) : gamma.SameCycle 3 m ↔ m = 3 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    have hfix : ∀ i : ℕ, (gamma ^ i) 3 = 3 := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ, Equiv.Perm.mul_apply, gamma_apply_3, ih]
    rw [← hi]; exact hfix i
  · rintro rfl
    exact Equiv.Perm.SameCycle.refl gamma 3

private lemma sameCycle_gamma_5 (m : Fin 6) : gamma.SameCycle 5 m ↔ m = 0 ∨ m = 5 := by
  rw [← gamma_apply_0, Equiv.Perm.sameCycle_apply_left]
  exact sameCycle_gamma_0 m

private lemma sameCycle_gamma_4 (m : Fin 6) : gamma.SameCycle 4 m ↔ m = 2 ∨ m = 4 := by
  rw [← gamma_apply_2, Equiv.Perm.sameCycle_apply_left]
  exact sameCycle_gamma_2 m

private def gamInd0 : Fin 6 → ZMod 3 := ![1, 0, 0, 0, 0, 1]
private def gamInd1 : Fin 6 → ZMod 3 := ![0, 1, 0, 0, 0, 0]
private def gamInd2 : Fin 6 → ZMod 3 := ![0, 0, 1, 0, 1, 0]
private def gamInd3 : Fin 6 → ZMod 3 := ![0, 0, 0, 1, 0, 0]

private lemma gam_indicator_0 :
    (fun m : Fin 6 => if gamma.SameCycle 0 m then (1 : ZMod 3) else 0) = gamInd0 := by
  funext m
  fin_cases m <;>
    (first
      | rw [if_pos (by rw [sameCycle_gamma_0]; decide)]
      | rw [if_neg (by rw [sameCycle_gamma_0]; decide)]) <;> decide

private lemma gam_indicator_1 :
    (fun m : Fin 6 => if gamma.SameCycle 1 m then (1 : ZMod 3) else 0) = gamInd1 := by
  funext m
  fin_cases m <;>
    (first
      | rw [if_pos (by rw [sameCycle_gamma_1]; decide)]
      | rw [if_neg (by rw [sameCycle_gamma_1]; decide)]) <;> decide

private lemma gam_indicator_2 :
    (fun m : Fin 6 => if gamma.SameCycle 2 m then (1 : ZMod 3) else 0) = gamInd2 := by
  funext m
  fin_cases m <;>
    (first
      | rw [if_pos (by rw [sameCycle_gamma_2]; decide)]
      | rw [if_neg (by rw [sameCycle_gamma_2]; decide)]) <;> decide

private lemma gam_indicator_3 :
    (fun m : Fin 6 => if gamma.SameCycle 3 m then (1 : ZMod 3) else 0) = gamInd3 := by
  funext m
  fin_cases m <;>
    (first
      | rw [if_pos (by rw [sameCycle_gamma_3]; decide)]
      | rw [if_neg (by rw [sameCycle_gamma_3]; decide)]) <;> decide

private lemma gam_indicator_4 :
    (fun m : Fin 6 => if gamma.SameCycle 4 m then (1 : ZMod 3) else 0) = gamInd2 := by
  funext m
  fin_cases m <;>
    (first
      | rw [if_pos (by rw [sameCycle_gamma_4]; decide)]
      | rw [if_neg (by rw [sameCycle_gamma_4]; decide)]) <;> decide

private lemma gam_indicator_5 :
    (fun m : Fin 6 => if gamma.SameCycle 5 m then (1 : ZMod 3) else 0) = gamInd0 := by
  funext m
  fin_cases m <;>
    (first
      | rw [if_pos (by rw [sameCycle_gamma_5]; decide)]
      | rw [if_neg (by rw [sameCycle_gamma_5]; decide)]) <;> decide

private def corootSpanE6 : Set (Fin 6 → ZMod 3) :=
  {g | ∃ c : Fin 6 → ℤ, ∀ i, g i = ∑ j, (c j : ZMod 3) * (E6M j i : ZMod 3)}

private lemma gamInd_mem_corootSpan (g : Fin 6 → ZMod 3) (c : Fin 6 → ℤ)
    (h : ∀ i, g i = ∑ j, (c j : ZMod 3) * (E6M j i : ZMod 3)) :
    g ∈ corootSpanE6 :=
  ⟨c, h⟩

private lemma gamInd0_mem : gamInd0 ∈ corootSpanE6 :=
  gamInd_mem_corootSpan gamInd0 ![0, 2, 2, 1, 1, 1]
    (by intro i; fin_cases i <;> decide)

private lemma gamInd1_mem : gamInd1 ∈ corootSpanE6 :=
  gamInd_mem_corootSpan gamInd1 ![0, 2, 0, 0, 1, 2]
    (by intro i; fin_cases i <;> decide)

private lemma gamInd2_mem : gamInd2 ∈ corootSpanE6 :=
  gamInd_mem_corootSpan gamInd2 ![0, 1, 0, 2, 0, 0]
    (by intro i; fin_cases i <;> decide)

private lemma gamInd3_mem : gamInd3 ∈ corootSpanE6 :=
  gamInd_mem_corootSpan gamInd3 ![0, 0, 0, 0, 2, 1]
    (by intro i; fin_cases i <;> decide)

private lemma not_prime_dvd_one (p : ℕ) (hp : p.Prime) : ¬ (p : ℤ) ∣ 1 := by
  intro h
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using h))

private lemma not_prime_dvd_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have h' : p ∣ 2 := Int.natCast_dvd_natCast.mp (by simpa using h)
  rcases (Nat.dvd_prime Nat.prime_two).mp h' with h1 | h1
  · exact hp.ne_one h1
  · exact hp2 h1

private lemma not_prime_dvd_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) : ¬ (p : ℤ) ∣ 3 := by
  intro h
  have h' : p ∣ 3 := Int.natCast_dvd_natCast.mp (by simpa using h)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h' with h1 | h1
  · exact hp.ne_one h1
  · exact hp3 h1

private lemma det_ggU_F4 (f : ℕ) : (ggU .F4 6 f).D.cartan.det = 1 := by
  change (Tag.cartan .F4).det = 1
  exact det_cartan_F4

private lemma det_ggU_E6 (f : ℕ) : (ggU .E6 6 f).D.cartan.det = 3 := by
  change (Tag.cartan .E6).det = 3
  exact det_cartan_E6

private lemma det_ggU_E7 (f : ℕ) : (ggU .E7 6 f).D.cartan.det = 2 := by
  change (Tag.cartan .E7).det = 2
  exact det_cartan_E7

private lemma det_ggU_E8 (f : ℕ) : (ggU .E8 6 f).D.cartan.det = 1 := by
  change (Tag.cartan .E8).det = 1
  exact det_cartan_E8

private lemma latGram_smul_nat {n : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (α β : Fin n → ℤ) :
    latGram ((k : ℤ) • A) α β = (k : ℤ) * latGram A α β := by
  simp only [latGram, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma latLinked_smul_nat {n : ℕ} (k : ℕ) (hk : (k : ℤ) ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℤ) (Φ : Set (Fin n → ℤ)) (α β : Fin n → ℤ) :
    latLinked ((k : ℤ) • A) Φ α β ↔ latLinked A Φ α β := by
  have hgen : ∀ a b, (a ∈ Φ ∧ b ∈ Φ ∧ latGram ((k : ℤ) • A) a b ≠ 0) ↔
      (a ∈ Φ ∧ b ∈ Φ ∧ latGram A a b ≠ 0) := by
    intro a b
    rw [latGram_smul_nat]
    constructor
    · rintro ⟨ha, hb, h⟩
      exact ⟨ha, hb, fun h0 => h (by rw [h0, mul_zero])⟩
    · rintro ⟨ha, hb, h⟩
      exact ⟨ha, hb, fun h0 => h ((mul_eq_zero.mp h0).resolve_left hk)⟩
  constructor
  · intro h
    exact (Relation.EqvGen.mono (fun a b hh => (hgen a b).mp hh)) α β h
  · intro h
    exact (Relation.EqvGen.mono (fun a b hh => (hgen a b).mpr hh)) α β h

private lemma latAdmPlane_congr {U' : Type} [Group U'] (Δ : UniversalRootDatum U')
    (S A : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ) (p : ℕ) (q2 : Prop)
    (π : Equiv.Perm (Fin Δ.rank))
    (h : ∀ (Φ : Set (Fin Δ.rank → ℤ)) (α β : Fin Δ.rank → ℤ),
      latLinked S Φ α β ↔ latLinked A Φ α β) :
    LatAdmPlane Δ S p q2 π ↔ LatAdmPlane Δ A p q2 π := by
  unfold LatAdmPlane
  constructor
  · rintro ⟨f₁, f₂, h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨f₁, f₂, h1, h2, h3, h4, h5, h6, ?_⟩
    intro a b hab
    obtain ⟨O, hO, hs, hc⟩ := h7 a b hab
    have hO' : IsCompOrbit A π (latPhi Δ.roots p (a • f₁ + b • f₂)) O := by
      unfold IsCompOrbit at hO ⊢
      obtain ⟨α, hα, hOeq⟩ := hO
      refine ⟨α, hα, ?_⟩
      rw [hOeq]
      apply Set.ext
      intro β
      constructor
      · rintro ⟨n, hn⟩; exact ⟨n, (h _ _ _).mp hn⟩
      · rintro ⟨n, hn⟩; exact ⟨n, (h _ _ _).mpr hn⟩
    exact ⟨O, hO', hs, hc⟩
  · rintro ⟨f₁, f₂, h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨f₁, f₂, h1, h2, h3, h4, h5, h6, ?_⟩
    intro a b hab
    obtain ⟨O, hO, hs, hc⟩ := h7 a b hab
    have hO' : IsCompOrbit S π (latPhi Δ.roots p (a • f₁ + b • f₂)) O := by
      unfold IsCompOrbit at hO ⊢
      obtain ⟨α, hα, hOeq⟩ := hO
      refine ⟨α, hα, ?_⟩
      rw [hOeq]
      apply Set.ext
      intro β
      constructor
      · rintro ⟨n, hn⟩; exact ⟨n, (h _ _ _).mpr hn⟩
      · rintro ⟨n, hn⟩; exact ⟨n, (h _ _ _).mp hn⟩
    exact ⟨O, hO', hs, hc⟩

private def e6f1 : Fin 6 → ZMod 3 := Pi.single 1 1

private def e6f2 : Fin 6 → ZMod 3 := Pi.single 4 1 + Pi.single 5 1

private def e6alpha : Fin 6 → ℤ := Pi.single 0 1

private lemma e6f1_mem : e6f1 ∈ corootSpanE6 :=
  gamInd_mem_corootSpan e6f1 ![0, 2, 0, 0, 1, 2] (by intro i; fin_cases i <;> decide)

private lemma e6f2_mem : e6f2 ∈ corootSpanE6 :=
  gamInd_mem_corootSpan e6f2 ![0, 0, 0, 0, 0, 2] (by intro i; fin_cases i <;> decide)

private lemma e6_independent :
    ∀ a b : ZMod 3, a • e6f1 + b • e6f2 = 0 → a = 0 ∧ b = 0 := by
  intro a b h
  have h1 := congrFun h 1
  have h4 := congrFun h 4
  simp [e6f1, e6f2, smul_eq_mul] at h1 h4
  exact ⟨h1, h4⟩

private lemma e6alpha_mem : e6alpha ∈ (rootFinset Tag.E6 : Set (Fin Tag.E6.rank → ℤ)) := by
  haveI : NeZero Tag.E6.rank := ⟨by decide⟩
  exact mem_rootFinset.mpr (IsRoot.basis (0 : Fin Tag.E6.rank))

private lemma e6f1_latChar_alpha : latChar 3 e6f1 e6alpha = 0 := by decide

private lemma e6f2_latChar_alpha : latChar 3 e6f2 e6alpha = 0 := by decide

private lemma latPerm_one_apply (α : Fin 6 → ℤ) :
    latPerm (1 : Equiv.Perm (Fin 6)) α = α := rfl

private lemma iterate_latPerm_one (m : ℕ) (α : Fin 6 → ℤ) :
    (latPerm (1 : Equiv.Perm (Fin 6)))^[m] α = α := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, latPerm_one_apply]

private def e6Adj (β γ : Fin 6 → ℤ) : Bool := latGram E6M β γ != 0

private def e6Step (L X : List (Fin 6 → ℤ)) : List (Fin 6 → ℤ) :=
  X ++ L.filter (fun γ => X.any (fun β => e6Adj β γ))

private def e6Closure (L : List (Fin 6 → ℤ)) (α : Fin 6 → ℤ) (n : ℕ) : List (Fin 6 → ℤ) :=
  (e6Step L)^[n] [α]

private def e6RootList : List (Fin 6 → ℤ) :=
  (List.range (Tag.rootCertificate .E6).roots.length).map (Tag.rootCertificate .E6).root

private def e6PhiList (w : Fin 6 → ZMod 3) : List (Fin 6 → ℤ) :=
  e6RootList.filter (fun β => latChar 3 w β == 0)

set_option backward.isDefEq.respectTransparency false in
private lemma e6PhiList_set (f : ℕ) (w : Fin 6 → ZMod 3) :
    {γ : Fin 6 → ℤ | γ ∈ e6PhiList w} = latPhi (ggU .E6 6 f).D.roots 3 w := by
  ext γ
  change γ ∈ e6PhiList w ↔ γ ∈ (ggU .E6 6 f).D.roots ∧ latChar 3 w γ = 0
  rw [mem_roots_E6]
  simp only [rootFinset, e6PhiList, e6RootList, List.mem_filter, List.mem_toFinset, beq_iff_eq]

private lemma e6Step_linked (L X : List (Fin 6 → ℤ)) (α : Fin 6 → ℤ)
    (hXL : ∀ β ∈ X, β ∈ L)
    (hX : ∀ β ∈ X, latLinked E6M {γ | γ ∈ L} α β) :
    ∀ β ∈ e6Step L X, latLinked E6M {γ | γ ∈ L} α β := by
  intro β hβ
  simp only [e6Step, List.mem_append, List.mem_filter, List.any_eq_true] at hβ
  rcases hβ with hβ | ⟨hβL, δ, hδ, hadj⟩
  · exact hX β hβ
  · have hδL : δ ∈ L := hXL δ hδ
    have hadj' : latGram E6M δ β ≠ 0 := by simpa [e6Adj, bne_iff_ne] using hadj
    have hrel : (fun a b : Fin 6 → ℤ => a ∈ {γ | γ ∈ L} ∧ b ∈ {γ | γ ∈ L} ∧
        latGram E6M a b ≠ 0) δ β := ⟨hδL, hβL, hadj'⟩
    exact Relation.EqvGen.trans α δ β (hX δ hδ) (Relation.EqvGen.rel δ β hrel)

private lemma e6Closure_sub_linked (L : List (Fin 6 → ℤ)) (α : Fin 6 → ℤ) (hαL : α ∈ L) :
    ∀ n, (∀ β ∈ e6Closure L α n, β ∈ L) ∧
      (∀ β ∈ e6Closure L α n, latLinked E6M {γ | γ ∈ L} α β) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro β hβ
        have hβ' : β = α := by simpa [e6Closure] using hβ
        rw [hβ']; exact hαL
      · intro β hβ
        have hβ' : β = α := by simpa [e6Closure] using hβ
        rw [hβ']
        exact Relation.EqvGen.refl α
  | succ n ih =>
      obtain ⟨hsub, hlink⟩ := ih
      refine ⟨?_, ?_⟩
      · intro β hβ
        simp only [e6Closure, Function.iterate_succ_apply', e6Step, List.mem_append,
          List.mem_filter, List.any_eq_true] at hβ
        rcases hβ with hβ | ⟨hβL, _⟩
        · exact hsub β hβ
        · exact hβL
      · intro β hβ
        have hβ' : β ∈ e6Step L (e6Closure L α n) := by
          simpa only [e6Closure, Function.iterate_succ_apply'] using hβ
        exact e6Step_linked L (e6Closure L α n) α hsub hlink β hβ'

private def e6ClosedCheck (L : List (Fin 6 → ℤ)) (α : Fin 6 → ℤ) : Bool :=
  decide (∀ β ∈ L, β ∈ e6Closure L α (L.length + 1))

private lemma e6ClosedCheck_sound (L : List (Fin 6 → ℤ)) (α : Fin 6 → ℤ) (hαL : α ∈ L)
    (h : e6ClosedCheck L α = true) :
    ∀ β ∈ L, latLinked E6M {γ | γ ∈ L} α β := by
  have hcov : ∀ β ∈ L, β ∈ e6Closure L α (L.length + 1) := by
    simpa [e6ClosedCheck] using h
  intro β hβ
  exact (e6Closure_sub_linked L α hαL (L.length + 1)).2 β (hcov β hβ)

private lemma latLinked_mem_right {S : Matrix (Fin 6) (Fin 6) ℤ} {Φ : Set (Fin 6 → ℤ)}
    {α β : Fin 6 → ℤ} (hα : α ∈ Φ) (h : latLinked S Φ α β) : β ∈ Φ := by
  haveI : IsEquiv (Fin 6 → ℤ) (fun a b => (a ∈ Φ → b ∈ Φ) ∧ (b ∈ Φ → a ∈ Φ)) :=
    { refl := fun a => ⟨fun h => h, fun h => h⟩
      trans := fun a b c hab hbc =>
        ⟨fun ha => hbc.1 (hab.1 ha), fun hc => hab.2 (hbc.2 hc)⟩
      symm := fun a b h => ⟨h.2, h.1⟩ }
  have hle : (fun a b : Fin 6 → ℤ => a ∈ Φ ∧ b ∈ Φ ∧ latGram S a b ≠ 0) ≤
      (fun a b => (a ∈ Φ → b ∈ Φ) ∧ (b ∈ Φ → a ∈ Φ)) :=
    fun a b ⟨ha, hb, _⟩ => ⟨fun _ => hb, fun _ => ha⟩
  exact ((Relation.EqvGen.eqvGen_le hle) α β h).1 hα

private lemma not_latSolv_of_ncard (q2 : Prop) (O : Set (Fin 6 → ℤ)) (h : 7 ≤ O.ncard) :
    ¬ LatSolv q2 (1 : Equiv.Perm (Fin 6)) O := by
  rintro ⟨-, h | ⟨h6, -⟩⟩
  · obtain ⟨α, hO⟩ := h
    have hle : O.ncard ≤ 2 := by
      rw [hO]
      simpa using Set.ncard_insert_le α ({-α} : Set (Fin 6 → ℤ))
    omega
  · omega

private lemma ncard_list_set (L : List (Fin 6 → ℤ)) (hL : L.Nodup) :
    ({γ : Fin 6 → ℤ | γ ∈ L} : Set (Fin 6 → ℤ)).ncard = L.length := by
  have hset : {γ : Fin 6 → ℤ | γ ∈ L} = (↑L.toFinset : Set (Fin 6 → ℤ)) := by
    ext γ; simp
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

private lemma e6RootList_nodup : e6RootList.Nodup := by
  have h := Tag.rootCertificate_checkNodup .E6
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
  refine List.Nodup.of_map (fun v => List.ofFn v) ?_
  change (List.map (fun v => List.ofFn v) (List.map Tag.E6.rootCertificate.root
    (List.range Tag.E6.rootCertificate.roots.length))).Nodup
  rw [← List.comp_map]
  exact h

private lemma e6PhiList_nodup (w : Fin 6 → ZMod 3) : (e6PhiList w).Nodup :=
  e6RootList_nodup.filter (fun β => latChar 3 w β == 0)

private def e6AllVecs : List (Fin 6 → ZMod 3) :=
  (List.finRange 729).map fun n => fun i => (((n.val / 3 ^ i.val % 3 : ℕ) : ZMod 3))

private theorem mem_e6AllVecs : ∀ f : Fin 6 → ZMod 3, f ∈ e6AllVecs := by
  intro f
  have h0 := ZMod.val_lt (f 0)
  have h1 := ZMod.val_lt (f 1)
  have h2 := ZMod.val_lt (f 2)
  have h3 := ZMod.val_lt (f 3)
  have h4 := ZMod.val_lt (f 4)
  have h5 := ZMod.val_lt (f 5)
  have hN : (f 0).val + 3 * (f 1).val + 9 * (f 2).val + 27 * (f 3).val + 81 * (f 4).val
      + 243 * (f 5).val < 729 := by omega
  refine List.mem_map.2 ⟨⟨_, hN⟩, List.mem_finRange _, ?_⟩
  have key : ∀ (k : ℕ) (i : Fin 6), 3 ^ i.val = k → ((f 0).val + 3 * (f 1).val + 9 * (f 2).val
      + 27 * (f 3).val + 81 * (f 4).val + 243 * (f 5).val) / k % 3 = (f i).val →
      (((((f 0).val + 3 * (f 1).val + 9 * (f 2).val + 27 * (f 3).val + 81 * (f 4).val
        + 243 * (f 5).val) / 3 ^ i.val % 3 : ℕ)) : ZMod 3) = f i := by
    intro k i hk h
    rw [hk, h, ZMod.natCast_zmod_val]
  funext i
  fin_cases i
  · exact key 1 0 rfl (by omega)
  · exact key 3 1 rfl (by omega)
  · exact key 9 2 rfl (by omega)
  · exact key 27 3 rfl (by omega)
  · exact key 81 4 rfl (by omega)
  · exact key 243 5 rfl (by omega)

private def e6Decode (f : Fin 6 → ZMod 3) : ℕ :=
  (f 0).val + 3 * (f 1).val + 9 * (f 2).val + 27 * (f 3).val + 81 * (f 4).val + 243 * (f 5).val

private theorem e6Decode_digits : ∀ n : Fin 729,
    e6Decode (fun i => (((n.val / 3 ^ i.val % 3 : ℕ) : ZMod 3))) = n.val := by
  decide +kernel

private theorem nodup_e6AllVecs : e6AllVecs.Nodup := by
  refine (List.nodup_finRange 729).map fun n m h => Fin.ext ?_
  rw [← e6Decode_digits n, ← e6Decode_digits m]
  exact congrArg e6Decode h

private lemma card_e6AllVecs (P : (Fin 6 → ZMod 3) → Prop) [DecidablePred P] :
    Nat.card {f : Fin 6 → ZMod 3 // P f} = (e6AllVecs.filter fun f => decide (P f)).length := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : Finset.univ.filter P = (e6AllVecs.filter fun f => decide (P f)).toFinset := by
    ext f
    simp [mem_e6AllVecs f]
  rw [hset]
  exact List.toFinset_card_of_nodup (nodup_e6AllVecs.filter _)

private def annCheck (L : List (Fin 6 → ℤ)) : Bool :=
  decide ((e6AllVecs.filter (fun g => decide (∀ β ∈ L, latChar 3 g β = 0))).length ≤ 9)

private lemma annCheck_sound (L : List (Fin 6 → ℤ)) (h : annCheck L = true) :
    Nat.card {g : Fin 6 → ZMod 3 // ∀ β ∈ L, latChar 3 g β = 0} ≤ 9 := by
  have hcard : (e6AllVecs.filter (fun g => decide (∀ β ∈ L, latChar 3 g β = 0))).length ≤ 9 := by
    simpa [annCheck] using h
  rw [card_e6AllVecs (fun g => ∀ β ∈ L, latChar 3 g β = 0)]
  exact hcard

set_option backward.isDefEq.respectTransparency false in
private lemma isCompOrbit_e6PhiList (f : ℕ) (w : Fin 6 → ZMod 3)
    (hα : e6alpha ∈ e6PhiList w)
    (hcheck : e6ClosedCheck (e6PhiList w) e6alpha = true) :
    IsCompOrbit (ggU .E6 6 f).D.cartan (1 : Equiv.Perm (Fin (ggU .E6 6 f).D.rank))
      (latPhi (ggU .E6 6 f).D.roots 3 w) (latPhi (ggU .E6 6 f).D.roots 3 w) := by
  show @IsCompOrbit (ggU .E6 6 f).D.rank (ggU .E6 6 f).D.cartan (1 : Equiv.Perm (Fin (ggU .E6 6 f).D.rank))
    (latPhi (ggU .E6 6 f).D.roots 3 w) (latPhi (ggU .E6 6 f).D.roots 3 w)
  refine ⟨e6alpha, ?_, ?_⟩
  · rw [← e6PhiList_set f w]; exact hα
  · apply Set.ext
    intro β
    constructor
    · intro hβ
      have hβL : β ∈ e6PhiList w := by
        rw [← e6PhiList_set f w] at hβ; exact hβ
      refine ⟨0, ?_⟩
      rw [← e6PhiList_set f w]
      show latLinked E6M {γ : Fin 6 → ℤ | γ ∈ e6PhiList w} e6alpha β
      exact e6ClosedCheck_sound (e6PhiList w) e6alpha hα hcheck β hβL
    · rintro ⟨m, hm⟩
      have hm' : latLinked E6M {γ : Fin 6 → ℤ | γ ∈ e6PhiList w} e6alpha β := by
        rw [← e6PhiList_set f w] at hm
        rw [iterate_latPerm_one m e6alpha] at hm
        show latLinked E6M {γ : Fin 6 → ℤ | γ ∈ e6PhiList w} e6alpha β
        exact hm
      have hb : β ∈ {γ : Fin 6 → ℤ | γ ∈ e6PhiList w} :=
        latLinked_mem_right (S := E6M) (Φ := {γ : Fin 6 → ℤ | γ ∈ e6PhiList w}) hα hm'
      rwa [e6PhiList_set f w] at hb

set_option backward.isDefEq.respectTransparency false in
private lemma adm_clause_e6 (f : ℕ) (q2 : Prop) (w : Fin 6 → ZMod 3)
    (hα : e6alpha ∈ e6PhiList w)
    (hcheck : e6ClosedCheck (e6PhiList w) e6alpha = true)
    (hncard : 7 ≤ ({γ : Fin 6 → ℤ | γ ∈ e6PhiList w} : Set (Fin 6 → ℤ)).ncard)
    (hann : annCheck (e6PhiList w) = true) :
    ∃ O, IsCompOrbit (ggU .E6 6 f).D.cartan (1 : Equiv.Perm (Fin (ggU .E6 6 f).D.rank))
        (latPhi (ggU .E6 6 f).D.roots 3 w) O ∧
      ¬ LatSolv q2 (1 : Equiv.Perm (Fin (ggU .E6 6 f).D.rank)) O ∧
      Nat.card {g : Fin (ggU .E6 6 f).D.rank → ZMod 3 //
        (∀ i, g i = g i) ∧ ∀ β ∈ O, latChar 3 g β = 0} ≤ 3 ^ 2 := by
  refine ⟨latPhi (ggU .E6 6 f).D.roots 3 w, ?_, ?_, ?_⟩
  · simpa using isCompOrbit_e6PhiList f w hα hcheck
  · apply not_latSolv_of_ncard q2
    rwa [← e6PhiList_set f w]
  · have h9 : Nat.card {g : Fin 6 → ZMod 3 // ∀ β ∈ e6PhiList w, latChar 3 g β = 0} ≤ 9 :=
      annCheck_sound (e6PhiList w) hann
    refine le_trans ?_ h9
    refine Nat.card_le_card_of_injective
      (fun g => ⟨g.1, fun β hβ => g.2.2 β (by rw [← e6PhiList_set f w]; exact hβ)⟩) ?_
    intro a b hab
    apply Subtype.ext
    have h := congrArg (fun g : {g : Fin 6 → ZMod 3 // ∀ β ∈ e6PhiList w, latChar 3 g β = 0} =>
      g.1) hab
    exact h

private def e6Cond (w : Fin 6 → ZMod 3) : Prop :=
  e6alpha ∈ e6PhiList w ∧
  e6ClosedCheck (e6PhiList w) e6alpha = true ∧
  7 ≤ (e6PhiList w).length ∧
  annCheck (e6PhiList w) = true

private lemma e6Cond_01 : e6Cond (0 • e6f1 + 1 • e6f2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private lemma e6Cond_02 : e6Cond (0 • e6f1 + 2 • e6f2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private lemma e6Cond_10 : e6Cond (1 • e6f1 + 0 • e6f2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private lemma e6Cond_11 : e6Cond (1 • e6f1 + 1 • e6f2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private lemma e6Cond_12 : e6Cond (1 • e6f1 + 2 • e6f2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private lemma e6Cond_20 : e6Cond (2 • e6f1 + 0 • e6f2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private lemma e6Cond_21 : e6Cond (2 • e6f1 + 1 • e6f2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private lemma e6Cond_22 : e6Cond (2 • e6f1 + 2 • e6f2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option backward.isDefEq.respectTransparency false in
private lemma latAdmPlane_E6_p3_cartan (f : ℕ) (q2 : Prop) :
    LatAdmPlane (ggU .E6 6 f).D (ggU .E6 6 f).D.cartan 3 q2 1 := by
  refine ⟨e6f1, e6f2, ?_, ?_, ?_, ?_, e6_independent, ?_, ?_⟩
  · intro i; rfl
  · intro i; rfl
  · show e6f1 ∈ corootSpanE6
    exact e6f1_mem
  · show e6f2 ∈ corootSpanE6
    exact e6f2_mem
  · refine ⟨e6alpha, ?_, ?_, ?_, ?_⟩
    · exact (mem_roots_E6 6 f e6alpha).mpr e6alpha_mem
    · exact latPerm_one_apply e6alpha
    · exact e6f1_latChar_alpha
    · exact e6f2_latChar_alpha
  · intro a b hab
    have ha : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
    have hb : ∀ b : ZMod 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
    rcases ha a with rfl | rfl | rfl <;> rcases hb b with rfl | rfl | rfl
    · exfalso
      rcases hab with h | h <;> exact h rfl
    · obtain ⟨h1, h2, h3, h4⟩ := e6Cond_01
      exact adm_clause_e6 f q2 (0 • e6f1 + 1 • e6f2 : Fin 6 → ZMod 3) h1 h2
        (by rw [ncard_list_set (e6PhiList _) (e6PhiList_nodup _)]; exact h3) h4
    · obtain ⟨h1, h2, h3, h4⟩ := e6Cond_02
      exact adm_clause_e6 f q2 (0 • e6f1 + 2 • e6f2 : Fin 6 → ZMod 3) h1 h2
        (by rw [ncard_list_set (e6PhiList _) (e6PhiList_nodup _)]; exact h3) h4
    · obtain ⟨h1, h2, h3, h4⟩ := e6Cond_10
      exact adm_clause_e6 f q2 (1 • e6f1 + 0 • e6f2 : Fin 6 → ZMod 3) h1 h2
        (by rw [ncard_list_set (e6PhiList _) (e6PhiList_nodup _)]; exact h3) h4
    · obtain ⟨h1, h2, h3, h4⟩ := e6Cond_11
      exact adm_clause_e6 f q2 (1 • e6f1 + 1 • e6f2 : Fin 6 → ZMod 3) h1 h2
        (by rw [ncard_list_set (e6PhiList _) (e6PhiList_nodup _)]; exact h3) h4
    · obtain ⟨h1, h2, h3, h4⟩ := e6Cond_12
      exact adm_clause_e6 f q2 (1 • e6f1 + 2 • e6f2 : Fin 6 → ZMod 3) h1 h2
        (by rw [ncard_list_set (e6PhiList _) (e6PhiList_nodup _)]; exact h3) h4
    · obtain ⟨h1, h2, h3, h4⟩ := e6Cond_20
      exact adm_clause_e6 f q2 (2 • e6f1 + 0 • e6f2 : Fin 6 → ZMod 3) h1 h2
        (by rw [ncard_list_set (e6PhiList _) (e6PhiList_nodup _)]; exact h3) h4
    · obtain ⟨h1, h2, h3, h4⟩ := e6Cond_21
      exact adm_clause_e6 f q2 (2 • e6f1 + 1 • e6f2 : Fin 6 → ZMod 3) h1 h2
        (by rw [ncard_list_set (e6PhiList _) (e6PhiList_nodup _)]; exact h3) h4
    · obtain ⟨h1, h2, h3, h4⟩ := e6Cond_22
      exact adm_clause_e6 f q2 (2 • e6f1 + 2 • e6f2 : Fin 6 → ZMod 3) h1 h2
        (by rw [ncard_list_set (e6PhiList _) (e6PhiList_nodup _)]; exact h3) h4

set_option backward.isDefEq.respectTransparency false in
theorem latAdmPlane_E6_p3 (f : ℕ)
    (S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E6 6 f).D S) (q2 : Prop) : LatAdmPlane (ggU .E6 6 f).D S 3 q2 1 := by
  obtain ⟨k, hkpos, hkS⟩ := isRootGram_E6 6 f S hS
  have hk : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hsymm : Tag.symmetrizedCartan .E6 = (ggU .E6 6 f).D.cartan := by
    show Tag.symmetrizer .E6 * Tag.cartan .E6 = (ggU .E6 6 f).D.cartan
    rw [show Tag.symmetrizer .E6 = 1 from rfl, Matrix.one_mul, ← ggU_cartan_E6]
  exact (latAdmPlane_congr _ S (ggU .E6 6 f).D.cartan 3 q2 1 (fun Φ α β => by
    rw [hkS, hsymm]
    exact latLinked_smul_nat k hk (ggU .E6 6 f).D.cartan Φ α β)).mpr
    (latAdmPlane_E6_p3_cartan f q2)

private lemma latAdmPlane_E6_datum (f : ℕ)
    (S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E6 6 f).D S)
    (π : Equiv.Perm (Fin (ggU .E6 6 f).D.rank))
    (hπ : IsDiagAut (ggU .E6 6 f).D π)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (q2 : Prop) :
    LatAdmPlane (ggU .E6 6 f).D S p q2 π := by
  have hdiv : (ggU .E6 6 f).D.divisible = ∅ := ggU_divisible_E6 6 f
  have hπ' : ∀ i j, E6M (π i) (π j) = E6M i j := by
    intro i j
    have h := hπ i j
    rwa [ggU_cartan_E6, cartan_E6_eq] at h
  by_cases hp3 : p = 3
  · subst hp3
    rcases diagAut_E6_eq_one_or_gamma π hπ' with hpi | hpi
    · subst hpi
      exact latAdmPlane_E6_p3 f S hS q2
    · subst hpi
      have hplane : LatPlane (ggU .E6 6 f).D gamma :=
        latPlane_exc .E6 f (Or.inr (Or.inl rfl)) gamma hπ
      refine latAdmPlane_of_latPlane _ hdiv S hS gamma hπ hplane 3 hp hp2 q2 ?_
      have key : ∀ i : Fin 6,
          (fun m : Fin 6 => if gamma.SameCycle i m then (1 : ZMod 3) else 0) ∈ corootSpanE6 := by
        intro i
        fin_cases i
        · change (fun m : Fin 6 => if gamma.SameCycle 0 m then (1 : ZMod 3) else 0) ∈ corootSpanE6
          rw [gam_indicator_0]; exact gamInd0_mem
        · change (fun m : Fin 6 => if gamma.SameCycle 1 m then (1 : ZMod 3) else 0) ∈ corootSpanE6
          rw [gam_indicator_1]; exact gamInd1_mem
        · change (fun m : Fin 6 => if gamma.SameCycle 2 m then (1 : ZMod 3) else 0) ∈ corootSpanE6
          rw [gam_indicator_2]; exact gamInd2_mem
        · change (fun m : Fin 6 => if gamma.SameCycle 3 m then (1 : ZMod 3) else 0) ∈ corootSpanE6
          rw [gam_indicator_3]; exact gamInd3_mem
        · change (fun m : Fin 6 => if gamma.SameCycle 4 m then (1 : ZMod 3) else 0) ∈ corootSpanE6
          rw [gam_indicator_4]; exact gamInd2_mem
        · change (fun m : Fin 6 => if gamma.SameCycle 5 m then (1 : ZMod 3) else 0) ∈ corootSpanE6
          rw [gam_indicator_5]; exact gamInd0_mem
      exact key
  · have hplane : LatPlane (ggU .E6 6 f).D π :=
      latPlane_exc .E6 f (Or.inr (Or.inl rfl)) π hπ
    refine latAdmPlane_of_latPlane _ hdiv S hS π hπ hplane p hp hp2 q2 ?_
    intro i
    apply latCorootSpan_eq_top _ p hp
    rw [det_ggU_E6 f]
    exact not_prime_dvd_three p hp hp3

theorem ggLatAdmPlaneExc_holds : GGLatAdmPlaneExc := by
  intro τ f hτ S π hS hπ p hp hp2 q2
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · have hdiv : (ggU .F4 6 f).D.divisible = ∅ := ggU_divisible_F4 6 f
    have hplane : LatPlane (ggU .F4 6 f).D π := latPlane_exc .F4 f (Or.inl rfl) π hπ
    refine latAdmPlane_of_latPlane _ hdiv S hS π hπ hplane p hp hp2 q2 ?_
    intro i
    apply latCorootSpan_eq_top _ p hp
    rw [det_ggU_F4 f]
    exact not_prime_dvd_one p hp
  · exact latAdmPlane_E6_datum f S hS π hπ p hp hp2 q2
  · have hdiv : (ggU .E7 6 f).D.divisible = ∅ := ggU_divisible_E7 6 f
    have hplane : LatPlane (ggU .E7 6 f).D π :=
      latPlane_exc .E7 f (Or.inr (Or.inr (Or.inl rfl))) π hπ
    refine latAdmPlane_of_latPlane _ hdiv S hS π hπ hplane p hp hp2 q2 ?_
    intro i
    apply latCorootSpan_eq_top _ p hp
    rw [det_ggU_E7 f]
    exact not_prime_dvd_two p hp hp2
  · have hdiv : (ggU .E8 6 f).D.divisible = ∅ := ggU_divisible_E8 6 f
    have hplane : LatPlane (ggU .E8 6 f).D π :=
      latPlane_exc .E8 f (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) π hπ
    refine latAdmPlane_of_latPlane _ hdiv S hS π hπ hplane p hp hp2 q2 ?_
    intro i
    apply latCorootSpan_eq_top _ p hp
    rw [det_ggU_E8 f]
    exact not_prime_dvd_one p hp
  · exact latAdmPlane_E6_datum f S hS π hπ p hp hp2 q2

end Exceptional

end CFSG.StandardType
