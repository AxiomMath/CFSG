module

public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.SBd18Out

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.Open CFSG.Quasithin

theorem sq_dvd_card_of_noncyclic {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    {Q : Sylow p S} (h : ¬ IsCyclic ↥(Q : Subgroup S)) : p ^ 2 ∣ Nat.card S := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp Q.isPGroup'
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    apply h
    interval_cases k
    · have : Subsingleton ↥(Q : Subgroup S) := by
        have : Nat.card ↥(Q : Subgroup S) ≤ 1 := by rw [hk]; simp
        exact (Finite.card_le_one_iff_subsingleton).mp this
      infer_instance
    · exact isCyclic_of_prime_card (p := p) (by simpa using hk)
  calc p ^ 2 ∣ p ^ k := pow_dvd_pow p hk2
    _ = Nat.card ↥(Q : Subgroup S) := hk.symm
    _ ∣ Nat.card S := Subgroup.card_subgroup_dvd_card _

theorem pCore_eq_bot_of_isSimpleGroup {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) (p : ℕ) [Fact p.Prime] : CFSG.pCore p Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore p Q) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup p Q := by
      have := CFSG.pCore_isPGroup (p := p) (G := Q)
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnab
    have hnt : Nontrivial Q := ⟨a, b, fun h => hab (by rw [h])⟩
    have hc : Subgroup.center Q = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h1 | h1
      · exfalso
        have := hp.center_nontrivial
        exact ((Subgroup.nontrivial_iff_ne_bot _).mp this) h1
      · exact h1
    have hbc : b ∈ Subgroup.center Q := hc ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hbc a)

theorem isSubnormal_eq_bot_or_top {S : Type*} [Group S] [IsSimpleGroup S] {H K : Subgroup S}
    (h : IsSubnormal H K) (hK : K = ⊥ ∨ K = ⊤) : H = ⊥ ∨ H = ⊤ :=
  by
    rcases hK with rfl | rfl
    · exact Or.inl (le_bot_iff.1 h.le)
    · exact h.eq_bot_or_top

theorem false_of_fixedSub_one {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hQ : ∃ Q : Sylow 3 S, ¬ IsCyclic ↥(Q : Subgroup S)) {K : Subgroup S}
    (hK : IsSubnormal K (SBd18.fixedSub (1 : MulAut S))) (hL32 : IsPSL 3 2 1 ↥K) : False := by
  have hfix : SBd18.fixedSub (1 : MulAut S) = ⊤ := by
    ext x
    simp [SBd18.mem_fixedSub]
  rw [hfix] at hK
  have hcard : Nat.card ↥K = 168 := SBc11.card_of_isPSL_three_two hL32
  rcases isSubnormal_eq_bot_or_top hK (Or.inr rfl) with h | h
  · rw [h, Subgroup.card_bot] at hcard
    omega
  · rw [h, Subgroup.card_top] at hcard
    obtain ⟨Q, hQ⟩ := hQ
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h9 := sq_dvd_card_of_noncyclic hQ
    rw [hcard] at h9
    omega

end CFSG.Quasithin.SBd19F
