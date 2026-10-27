module

public import CFSG.SignalizerFunctorTheorem.RankReduction
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

@[expose] def SolvableRankOneTheoremAt (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsElemAbelian p A →
    p ^ 3 ≤ Nat.card A → ∀ Θ : Subgroup G → Subgroup G, IsSignalizerFunctor p 1 A Θ →
    (∀ S ∈ signalizerFunctorEk p 1 A, Group.IsSolvable (Θ S)) →
    IsComplete p 1 A Θ ∧ Group.IsSolvable (completion p 1 A Θ)

@[expose] def SolvableRankOneTheorem : Prop :=
  ∀ p : ℕ, p.Prime → SolvableRankOneTheoremAt p

@[expose] def McBrideRankOneTheoremAt (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsElemAbelian p A →
    p ^ 3 ≤ Nat.card A → ∀ Θ : Subgroup G → Subgroup G, IsSignalizerFunctor p 1 A Θ →
    (∀ S ∈ signalizerFunctorEk p 1 A, signalizerMcBrideHypothesisB p (Θ S)) →
    IsComplete p 1 A Θ ∧ signalizerMcBrideHypothesisB p (completion p 1 A Θ)

@[expose] def McBrideRankOneTheorem : Prop :=
  ∀ p : ℕ, p.Prime → McBrideRankOneTheoremAt p

variable {G : Type} [Group G] [Finite G]

theorem solvable_oracle {p : ℕ} (h : SolvableRankOneTheoremAt p) {A : Subgroup G}
    (hA : IsElemAbelian p A) : RankOneOracle p A (fun H => Group.IsSolvable H) :=
  fun F hF hlarge Φ hΦ hP =>
    h G F (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hF) hlarge Φ hΦ hP

theorem mcBride_oracle {p : ℕ} (h : McBrideRankOneTheoremAt p) {A : Subgroup G}
    (hA : IsElemAbelian p A) : RankOneOracle p A (fun H => signalizerMcBrideHypothesisB p H) :=
  fun F hF hlarge Φ hΦ hP =>
    h G F (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hF) hlarge Φ hΦ hP

theorem signalizer_functor_theorem_of_rankOneAt
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hSol : SolvableRankOneTheoremAt p) (hMcB : McBrideRankOneTheoremAt p)
    (k : ℕ) (hk : 1 ≤ k)
    (A : Subgroup G) (hA : IsElemAbelian p A) (hrank : p ^ (k + 2) ≤ Nat.card A)
    (Θ : Subgroup G → Subgroup G)
    (hcent : ∀ S ∈ signalizerFunctorEk p k A, Θ S ≤ Subgroup.centralizer (S : Set G))
    (hcop : ∀ S ∈ signalizerFunctorEk p k A, Nat.Coprime p (Nat.card (Θ S)))
    (hinv : ∀ S ∈ signalizerFunctorEk p k A, A ≤ Subgroup.normalizer (Θ S : Set G))
    (hbal : ∀ S ∈ signalizerFunctorEk p k A, ∀ S' ∈ signalizerFunctorEk p k A,
      Θ S ⊓ Subgroup.centralizer (S' : Set G) ≤ Θ S')
    (hK : ∀ S ∈ signalizerFunctorEk p k A, signalizerMcBrideHypothesisB p (Θ S)) :
    let W : Subgroup G := ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk p k A), Θ S
    (Nat.Coprime p (Nat.card W) ∧ A ≤ Subgroup.normalizer (W : Set G)) ∧
    (∀ S ∈ signalizerFunctorEk p k A, W ⊓ Subgroup.centralizer (S : Set G) = Θ S) ∧
    (∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
      (∀ S ∈ signalizerFunctorEk p k A, Y ⊓ Subgroup.centralizer (S : Set G) ≤ Θ S) →
      Y ≤ W) ∧
    ((∀ S ∈ signalizerFunctorEk p k A, Group.IsSolvable (Θ S)) → Group.IsSolvable W) := by
  intro W
  have hΘ : IsSignalizerFunctor p k A Θ := ⟨hcent, hcop, hinv, hbal⟩
  obtain ⟨⟨hWcop, hWcent⟩, -⟩ :=
    isComplete_of_rankOneOracle hp hA (mcBride_oracle hMcB hA) k hk hrank Θ hΘ hK
  refine ⟨⟨hWcop, le_normalizer_completion hinv⟩, hWcent, fun Y hY hYC => ?_, fun hsol => ?_⟩
  · exact CFSG.SignalizerFunctor.Helpers.signalizer_maximality p k hp A hA
      ((Nat.pow_le_pow_right hp.pos (by omega)).trans hrank) Θ hcop Y hY hYC
  · exact (isComplete_of_rankOneOracle hp hA (solvable_oracle hSol hA) k hk hrank Θ hΘ hsol).2

theorem signalizer_functor_theorem_of_rankOne (hSol : SolvableRankOneTheorem)
    (hMcB : McBrideRankOneTheorem)
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k)
    (A : Subgroup G) (hA : IsElemAbelian p A) (hrank : p ^ (k + 2) ≤ Nat.card A)
    (Θ : Subgroup G → Subgroup G)
    (hcent : ∀ S ∈ signalizerFunctorEk p k A, Θ S ≤ Subgroup.centralizer (S : Set G))
    (hcop : ∀ S ∈ signalizerFunctorEk p k A, Nat.Coprime p (Nat.card (Θ S)))
    (hinv : ∀ S ∈ signalizerFunctorEk p k A, A ≤ Subgroup.normalizer (Θ S : Set G))
    (hbal : ∀ S ∈ signalizerFunctorEk p k A, ∀ S' ∈ signalizerFunctorEk p k A,
      Θ S ⊓ Subgroup.centralizer (S' : Set G) ≤ Θ S')
    (hK : ∀ S ∈ signalizerFunctorEk p k A, signalizerMcBrideHypothesisB p (Θ S)) :
    let W : Subgroup G := ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk p k A), Θ S
    (Nat.Coprime p (Nat.card W) ∧ A ≤ Subgroup.normalizer (W : Set G)) ∧
    (∀ S ∈ signalizerFunctorEk p k A, W ⊓ Subgroup.centralizer (S : Set G) = Θ S) ∧
    (∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
      (∀ S ∈ signalizerFunctorEk p k A, Y ⊓ Subgroup.centralizer (S : Set G) ≤ Θ S) →
      Y ≤ W) ∧
    ((∀ S ∈ signalizerFunctorEk p k A, Group.IsSolvable (Θ S)) → Group.IsSolvable W) :=
  signalizer_functor_theorem_of_rankOneAt G p hp (hSol p hp) (hMcB p hp) k hk A hA hrank Θ hcent
    hcop hinv hbal hK

@[expose] def elementValues {X : Type*} [Group X] (θ : X → Subgroup X) (S : Subgroup X) :
    Subgroup X :=
  ⨆ (a : X) (_ : a ∈ S) (_ : a ≠ 1), θ a

omit [Finite G] in
theorem zpowers_mem_E1 {p : ℕ} (hp : p.Prime) {A : Subgroup G} (hA : IsElemAbelian p A)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : Subgroup.zpowers a ∈ signalizerFunctorEk p 1 A := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨Subgroup.zpowers_le.mpr ha, ?_⟩
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_prime (hA.2 a ha) ha1

theorem eq_zpowers_of_card_eq_prime {p : ℕ} (hp : p.Prime) {S : Subgroup G}
    (hS : Nat.card S = p) {a : G} (ha : a ∈ S) (ha1 : a ≠ 1) : Subgroup.zpowers a = S := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha) ?_
  rw [hS, Nat.card_zpowers]
  have hdvd : orderOf a ∣ p := hS ▸ Subgroup.orderOf_dvd_natCard S ha
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) ha1
  · exact h.ge

omit [Finite G] in
theorem centralizer_zpowers (a : G) :
    Subgroup.centralizer (Subgroup.zpowers a : Set G) = Subgroup.centralizer {a} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite G] in
theorem theta_le_of_mem_zpowers {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
    (hθ : IsSolvableSignalizerFunctor p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A)
    (hb1 : b ≠ 1) (hab : a ∈ Subgroup.zpowers b) : θ b ≤ θ a := by
  intro x hx
  refine hθ.balance b hb hb1 a ha ha1 ⟨hx, ?_⟩
  have hxb : x ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [centralizer_zpowers]
    exact hθ.le_centralizer b hb hb1 hx
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hab) hxb

theorem elementValues_eq {p : ℕ} (hp : p.Prime) {A : Subgroup G} {θ : G → Subgroup G}
    (hθ : IsSolvableSignalizerFunctor p A θ) {S : Subgroup G}
    (hS : S ∈ signalizerFunctorEk p 1 A) {a : G} (ha : a ∈ S) (ha1 : a ≠ 1) :
    elementValues θ S = θ a := by
  have hScard : Nat.card S = p := by rw [hS.2, pow_one]
  apply le_antisymm
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    have hzb := eq_zpowers_of_card_eq_prime hp hScard hb hb1
    exact theta_le_of_mem_zpowers hθ (hS.1 ha) ha1 (hS.1 hb) hb1 (hzb ▸ ha)
  · exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))

omit [Finite G] in
theorem exists_ne_one_of_mem_E1 {p : ℕ} (hp : p.Prime) {A S : Subgroup G}
    (hS : S ∈ signalizerFunctorEk p 1 A) : ∃ a ∈ S, a ≠ 1 := by
  have hScard : Nat.card S = p := by rw [hS.2, pow_one]
  by_contra! h
  have hbot : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr h
  rw [hbot, Subgroup.card_bot] at hScard
  exact hp.one_lt.ne hScard

omit [Finite G] in
theorem le_normalizer_of_map_conj {A H : Subgroup G}
    (h : ∀ x ∈ A, H.map (MulAut.conj x).toMonoidHom = H) :
    A ≤ Subgroup.normalizer (H : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h x hx]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h x hx] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      simpa [MulAut.conj_apply] using hzy
    exact this ▸ hz

theorem isSignalizerFunctor_elementValues {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    {θ : G → Subgroup G} (hθ : IsSolvableSignalizerFunctor p A θ) :
    IsSignalizerFunctor p 1 A (elementValues θ) ∧
      ∀ S ∈ signalizerFunctorEk p 1 A, Group.IsSolvable (elementValues θ S) := by
  have key : ∀ S ∈ signalizerFunctorEk p 1 A, ∃ a ∈ A, a ≠ 1 ∧
      Subgroup.zpowers a = S ∧ elementValues θ S = θ a := by
    intro S hS
    obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_mem_E1 hp hS
    exact ⟨a, hS.1 ha, ha1, eq_zpowers_of_card_eq_prime hp (by rw [hS.2, pow_one]) ha ha1,
      elementValues_eq hp hθ hS ha ha1⟩
  refine ⟨⟨fun S hS => ?_, fun S hS => ?_, fun S hS => ?_, fun S hS S' hS' => ?_⟩,
    fun S hS => ?_⟩
  · obtain ⟨a, ha, ha1, rfl, heq⟩ := key S hS
    rw [heq, centralizer_zpowers]
    exact hθ.le_centralizer a ha ha1
  · obtain ⟨a, ha, ha1, -, heq⟩ := key S hS
    rw [heq]
    exact hθ.coprime a ha ha1
  · obtain ⟨a, ha, ha1, -, heq⟩ := key S hS
    rw [heq]
    exact le_normalizer_of_map_conj (hθ.invariant a ha ha1)
  · obtain ⟨a, ha, ha1, -, heq⟩ := key S hS
    obtain ⟨b, hb, hb1, rfl, heq'⟩ := key S' hS'
    rw [heq, heq', centralizer_zpowers]
    exact hθ.balance a ha ha1 b hb hb1
  · obtain ⟨a, ha, ha1, -, heq⟩ := key S hS
    rw [heq]
    exact hθ.solvable a ha ha1

theorem completion_elementValues {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) {θ : G → Subgroup G} (hθ : IsSolvableSignalizerFunctor p A θ) :
    completion p 1 A (elementValues θ) = ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a := by
  apply le_antisymm
  · refine completion_le fun S hS => ?_
    obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_mem_E1 hp hS
    rw [elementValues_eq hp hθ hS ha ha1]
    exact le_iSup_of_le a (le_iSup_of_le (hS.1 ha) (le_iSup_of_le ha1 le_rfl))
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    have hz := zpowers_mem_E1 hp hA ha ha1
    rw [← elementValues_eq hp hθ hz (Subgroup.mem_zpowers a) ha1]
    exact le_completion hz

theorem glauberman_of_solvableRankOneAt
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hSol : SolvableRankOneTheoremAt p)
    (A : Subgroup G) (hA : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hrank : p ^ 3 ∣ Nat.card A)
    (θ : G → Subgroup G) (hθ : IsSolvableSignalizerFunctor p A θ) :
    let W : Subgroup G := ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a
    Nat.Coprime p (Nat.card W) ∧ Group.IsSolvable W ∧
      ∀ a ∈ A, a ≠ 1 → θ a = W ⊓ Subgroup.centralizer {a} := by
  intro W
  have hElem : IsElemAbelian p A := ⟨hA, hexp⟩
  obtain ⟨hΘ, hsol⟩ := isSignalizerFunctor_elementValues hp hθ
  obtain ⟨⟨hcop, hcent⟩, hWsol⟩ := hSol G A hElem (Nat.le_of_dvd Nat.card_pos hrank) _ hΘ hsol
  have hW : completion p 1 A (elementValues θ) = W := completion_elementValues hp hElem hθ
  rw [hW] at hcop hWsol hcent
  refine ⟨hcop, hWsol, fun a ha ha1 => ?_⟩
  have hz := zpowers_mem_E1 hp hElem ha ha1
  rw [← centralizer_zpowers, hcent _ hz, elementValues_eq hp hθ hz (Subgroup.mem_zpowers a) ha1]

theorem glauberman_of_solvableRankOne (hSol : SolvableRankOneTheorem)
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime)
    (A : Subgroup G) (hA : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hrank : p ^ 3 ∣ Nat.card A)
    (θ : G → Subgroup G) (hθ : IsSolvableSignalizerFunctor p A θ) :
    let W : Subgroup G := ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a
    Nat.Coprime p (Nat.card W) ∧ Group.IsSolvable W ∧
      ∀ a ∈ A, a ≠ 1 → θ a = W ⊓ Subgroup.centralizer {a} :=
  glauberman_of_solvableRankOneAt G p hp (hSol p hp) A hA hexp hrank θ hθ

end CFSG.SignalizerFunctorTheorem
