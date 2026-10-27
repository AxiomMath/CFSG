module

public import CFSG.Quasithin.Recognition.St84.Sec7Setup


public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable (X : Setup Γ G)

theorem Ki_transitive_gen (i : ℤ) {a b : V}
    (ha : Γ.Adj (X.vert i) a) (hb : Γ.Adj (X.vert i) b)
    (ha1 : a ≠ X.vert (i - 1)) (ha2 : a ≠ X.vert (i + 1))
    (hb1 : b ≠ X.vert (i - 1)) (hb2 : b ≠ X.vert (i + 1)) :
    ∃ k ∈ X.Ki i, k • a = b := by
  classical
  let D : Set V := Γ.neighborSet (X.vert i) \ {X.vert (i - 1), X.vert (i + 1)}
  have hleft_adj : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro h
    have := X.vert_injective h
    omega
  have hDcard : D.ncard = 2 ^ X.n i - 1 := by
    have h := ncard_neighborSet_diff_two X.hyp (β := X.vert (i - 1)) (γ := X.vert (i + 1))
      hleft_adj (X.adj i) hne
    rw [show D.ncard =
      (Γ.neighborSet (X.vert i) \ {X.vert (i - 1), X.vert (i + 1)}).ncard from rfl, h]
  have hDfin : D.Finite := (X.hyp.finite_neighborSet (X.vert i)).sdiff
  have haD : a ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborSet]
      exact ha
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1, ha2⟩
  have hbD : b ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborSet]
      exact hb
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hb1, hb2⟩
  by_cases hn : X.n i = 1
  ·
    have hD1 : D.ncard ≤ 1 := by
      rw [hDcard, hn]
      norm_num
    refine ⟨1, (X.Ki i).one_mem, ?_⟩
    rw [one_smul]
    exact (Set.ncard_le_one hDfin).mp hD1 a haD b hbD
  ·
    have hn2 : 2 ≤ X.n i := by
      have h1 : 1 ≤ X.n i := (X.hyp.valency (X.vert i)).1
      omega
    have hKi3 : Nat.card ↥(X.Ki i) = 2 ^ X.n i - 1 := X.card_Ki i
    have hact : ∀ k : X.Ki i, ∀ x ∈ D, (k : G) • x ∈ D := by
      intro k x hx
      have hkK : (k : G) ∈ X.K := k.2.1
      have hxadj : Γ.Adj (X.vert i) x := by
        have h := hx.1
        rwa [SimpleGraph.mem_neighborSet] at h
      have hx1 : x ≠ X.vert (i - 1) := fun h => hx.2 (by simp [h])
      have hx2 : x ≠ X.vert (i + 1) := fun h => hx.2 (by simp [h])
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_neighborSet]
        have hfixi : (k : G) • X.vert i = X.vert i := X.K_fix (k : G) hkK i
        rw [← hfixi]
        exact (X.hyp.adj_smul (k : G) (X.vert i) x).2 hxadj
      · intro h
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        rcases h with h | h
        · apply hx1
          have hfix : (k : G) • X.vert (i - 1) = X.vert (i - 1) := X.K_fix (k : G) hkK (i - 1)
          have heq : (k : G) • x = (k : G) • X.vert (i - 1) := by rw [h, hfix]
          exact MulAction.injective (k : G) heq
        · apply hx2
          have hfix : (k : G) • X.vert (i + 1) = X.vert (i + 1) := X.K_fix (k : G) hkK (i + 1)
          have heq : (k : G) • x = (k : G) • X.vert (i + 1) := by rw [h, hfix]
          exact MulAction.injective (k : G) heq
    have horbD : MulAction.orbit (X.Ki i) a ⊆ D := by
      rintro _ ⟨k, rfl⟩
      exact hact k a haD
    have hstab : MulAction.stabilizer (X.Ki i) a = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      rw [MulAction.mem_stabilizer_iff] at hk
      by_contra hk1
      have hkG : (k : G) ∈ X.Ki i := k.2
      have hk1G : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
      have hfix := (X.torus_fixed i hn2 hkG hk1G a ha).mp hk
      rcases hfix with h | h
      · exact ha1 h
      · exact ha2 h
    have hcard_le : D.ncard ≤ (MulAction.orbit (X.Ki i) a).ncard := by
      rw [← MulAction.index_stabilizer, hstab, Subgroup.index_bot, hKi3, hDcard]
    have horb_eq : MulAction.orbit (X.Ki i) a = D :=
      Set.eq_of_subset_of_ncard_le horbD hcard_le hDfin
    have hb_orbit : b ∈ MulAction.orbit (X.Ki i) a := by
      rw [horb_eq]
      exact hbD
    obtain ⟨k, hk⟩ := hb_orbit
    exact ⟨k, k.2, hk⟩

private theorem fixes_of_odd_centralizer_aux (Y : Setup Γ G) {v u₀ : V} {S Q : Subgroup G}
    {k : G}
    (hS : S ≤ MulAction.stabilizer G v) (hS2 : IsPGroup 2 S)
    (hQfix : ∀ a : V, Γ.Adj v a → ∀ q ∈ Q, q • a = a)
    (htrans : ∀ a b : V, Γ.Adj v a → a ≠ u₀ → Γ.Adj v b → b ≠ u₀ →
      ∃ x ∈ S, x • a = b)
    (hkfixv : k • v = v) (hkfixu : k • u₀ = u₀) (hodd : Odd (orderOf k))
    (hcomm : ∀ x ∈ S, ⁅k, x⁆ ∈ Q) :
    ∀ w : V, Γ.Adj v w → k • w = w := by
  classical
  have hkinvu : k⁻¹ • u₀ = u₀ := by
    have h := congrArg (fun z => k⁻¹ • z) hkfixu
    simpa using h.symm
  have hstep : ∀ (s : G), s ∈ S → ∀ u : V, Γ.Adj v u → k • (s • u) = s • (k • u) := by
    intro s hs u hu
    have hku : Γ.Adj v (k • u) := by
      rw [← hkfixv]
      exact (Y.hyp.adj_smul k v u).2 hu
    have hsku : Γ.Adj v (s • (k • u)) := by
      have hsv : s • v = v := MulAction.mem_stabilizer_iff.mp (hS hs)
      rw [← hsv]
      exact (Y.hyp.adj_smul s v (k • u)).2 hku
    have hks : k * s = ⁅k, s⁆ * s * k := by
      rw [commutatorElement_def]
      group
    calc k • (s • u) = (k * s) • u := (mul_smul k s u).symm
      _ = (⁅k, s⁆ * s * k) • u := by rw [hks]
      _ = ⁅k, s⁆ • (s • (k • u)) := by simp only [mul_smul]
      _ = s • (k • u) := hQfix _ hsku ⁅k, s⁆ (hcomm s hs)
  intro w hw
  by_cases hwu : w = u₀
  · rw [hwu, hkfixu]
  have hkw : Γ.Adj v (k • w) := by
    rw [← hkfixv]
    exact (Y.hyp.adj_smul k v w).2 hw
  have hkwu : k • w ≠ u₀ := by
    intro h
    have h1 : k⁻¹ • (k • w) = k⁻¹ • u₀ := by rw [h]
    rw [inv_smul_smul, hkinvu] at h1
    exact hwu h1
  obtain ⟨x, hxS, hxw⟩ := htrans w (k • w) hw hwu hkw hkwu
  have hpow : ∀ m : ℕ, k ^ m • w = x ^ m • w := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc k ^ (m + 1) • w = k • (k ^ m • w) := by rw [pow_succ', mul_smul]
        _ = k • (x ^ m • w) := by rw [ih]
        _ = x ^ m • (k • w) := hstep (x ^ m) (S.pow_mem hxS m) w hw
        _ = x ^ m • (x • w) := by rw [hxw]
        _ = x ^ (m + 1) • w := by rw [pow_succ, mul_smul]
  have hfixm : x ^ orderOf k • w = w := by
    rw [← hpow (orderOf k), pow_orderOf_eq_one, one_smul]
  obtain ⟨c, hc⟩ := hS2.exists_orderOf_eq_pow (⟨x, hxS⟩ : S)
  have hxord : orderOf x = 2 ^ c :=
    (Subgroup.orderOf_coe (⟨x, hxS⟩ : S)).trans hc
  have hcop : (orderOf k).Coprime (orderOf x) := by
    rw [hxord]
    exact hodd.coprime_two_right.pow_right c
  obtain ⟨d, hd⟩ := exists_pow_eq_self_of_coprime (x := x) (n := orderOf k) hcop
  have hfixpow : ∀ d : ℕ, ((x ^ orderOf k) ^ d) • w = w := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => rw [pow_succ', mul_smul, ih, hfixm]
  have hxw' : x • w = w := by
    rw [← hd]
    exact hfixpow d
  rw [← hxw, hxw']

theorem sup_Q_eq_edgeSylow_of_gen (i : ℤ) {A : Subgroup G}
    (hK : X.K ⊓ X.L (i + 1) ≤ Subgroup.normalizer (A : Set G))
    (hA : A ≤ X.edgeSylow i) (hnot : ¬ A ≤ X.Q (i + 1)) :
    A ⊔ X.Q (i + 1) = X.edgeSylow i := by
  classical
  refine le_antisymm (sup_le hA (X.Q_le_edgeSylow i)) ?_
  intro s hs
  by_cases hsQ : s ∈ X.Q (i + 1)
  · exact Subgroup.mem_sup_right hsQ
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hnot
  obtain ⟨t, ht, htq⟩ :=
    X.exists_conj_mem_pCoreOf i (x := a) (y := s) (hA haA) hs haQ hsQ
  have htaA : t * a * t⁻¹ ∈ A :=
    (Subgroup.mem_set_normalizer_iff.mp (hK ht) a).mp haA
  have hs_eq : s = (t * a * t⁻¹ * s⁻¹)⁻¹ * (t * a * t⁻¹) := by group
  rw [hs_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((X.Q (i + 1)).inv_mem htq))
    (Subgroup.mem_sup_left htaA)

theorem sup_Q_eq_edgeSylow_of_left_gen (i : ℤ) {A : Subgroup G}
    (hK : X.K ⊓ X.L i ≤ Subgroup.normalizer (A : Set G))
    (hA : A ≤ X.edgeSylow i) (hnot : ¬ A ≤ X.Q i) :
    A ⊔ X.Q i = X.edgeSylow i := by
  classical
  refine le_antisymm (sup_le hA (X.Q_le_edgeSylow_left i)) ?_
  intro s hs
  by_cases hsQ : s ∈ X.Q i
  · exact Subgroup.mem_sup_right hsQ
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hnot
  obtain ⟨t, ht, htq⟩ := X.exists_conj_mem_Q_left i (hA haA) hs haQ hsQ
  have htaA : t * a * t⁻¹ ∈ A :=
    (Subgroup.mem_set_normalizer_iff.mp (hK ht) a).mp haA
  have hs_eq : s = (t * a * t⁻¹ * s⁻¹)⁻¹ * (t * a * t⁻¹) := by group
  rw [hs_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((X.Q i).inv_mem htq))
    (Subgroup.mem_sup_left htaA)

theorem fixes_neighbors_of_centralizes_edgeSylow_gen (j : ℤ) {k : G}
    (hk1 : k ∈ X.Gi (j - 1)) (hk2 : k ∈ X.Gi j) (hodd : Odd (orderOf k))
    (hcomm : ∀ x ∈ X.edgeSylow (j - 1), ⁅k, x⁆ ∈ X.Q j) :
    ∀ w : V, Γ.Adj (X.vert j) w → k • w = w := by
  refine fixes_of_odd_centralizer_aux X (v := X.vert j) (u₀ := X.vert (j - 1))
    (S := X.edgeSylow (j - 1)) (Q := X.Q j) ?_ ?_ ?_ ?_ ?_ ?_ hodd hcomm
  · intro s hs
    have h := (X.isSylowTwoOf_edgeSylow (j - 1)).1 hs
    have h2 : s ∈ X.Gi ((j - 1) + 1) := (Subgroup.mem_inf.mp h).2
    simpa only [show (j - 1) + 1 = j by omega] using h2
  · exact X.isPGroup_edgeSylow (j - 1)
  · exact X.Q_fixes_neighbors_vert j
  · intro a b ha ha1 hb hb1
    obtain ⟨s, hs, hsb⟩ := X.edgeSylow_transitive_right j a b ha ha1 hb hb1
    exact ⟨s, by rwa [X.edgeSylow_right_eq j], hsb⟩
  · exact MulAction.mem_stabilizer_iff.mp hk2
  · exact MulAction.mem_stabilizer_iff.mp hk1

theorem fixes_neighbors_of_centralizes_edgeSylow_left_gen (j : ℤ) {k : G}
    (hk1 : k ∈ X.Gi (j + 1)) (hk2 : k ∈ X.Gi j) (hodd : Odd (orderOf k))
    (hcomm : ∀ x ∈ X.edgeSylow j, ⁅k, x⁆ ∈ X.Q j) :
    ∀ w : V, Γ.Adj (X.vert j) w → k • w = w := by
  refine fixes_of_odd_centralizer_aux X (v := X.vert j) (u₀ := X.vert (j + 1))
    (S := X.edgeSylow j) (Q := X.Q j) ?_ ?_ ?_ ?_ ?_ ?_ hodd hcomm
  · intro s hs
    exact (Subgroup.mem_inf.mp ((X.isSylowTwoOf_edgeSylow j).1 hs)).1
  · exact X.isPGroup_edgeSylow j
  · exact X.Q_fixes_neighbors_vert j
  · exact X.edgeSylow_transitive_left j
  · exact MulAction.mem_stabilizer_iff.mp hk2
  · exact MulAction.mem_stabilizer_iff.mp hk1

end Setup

end CFSG.Quasithin.St84
