module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
public import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem center_eq_of_simple_central_quot {S : Type} [Group S] (hq : IsQuasisimple S)
    (Z : Subgroup S) [Z.Normal] (hZ : Z ≤ Subgroup.center S) (hs : IsSimpleGroup (S ⧸ Z)) :
    Z = Subgroup.center S := by
  have hnt : Nontrivial (S ⧸ Subgroup.center S) := hq.2.1.toNontrivial
  have hN : ((Subgroup.center S).map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  rcases hs.eq_bot_or_eq_top_of_normal ((Subgroup.center S).map (QuotientGroup.mk' Z)) with
    hbot | htop
  · apply le_antisymm hZ
    intro x hx
    have hmem : QuotientGroup.mk' Z x ∈ (Subgroup.center S).map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · exfalso
    have hc : Subgroup.center S = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hx : QuotientGroup.mk' Z x ∈ (Subgroup.center S).map (QuotientGroup.mk' Z) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨c, hcc, hcx⟩ := Subgroup.mem_map.mp hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hcx
      have hrel : c⁻¹ * x ∈ Z := QuotientGroup.eq.mp hcx
      have key : c * (c⁻¹ * x) ∈ Subgroup.center S := mul_mem hcc (hZ hrel)
      rwa [mul_inv_cancel_left] at key
    have hsub : Subsingleton (S ⧸ Subgroup.center S) := by
      rw [hc]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact hab (hsub.elim a b)

theorem card_central_quot_eq_of_simple {S : Type} [Group S] (hq : IsQuasisimple S)
    (Z₁ Z₂ : Subgroup S) [Z₁.Normal] [Z₂.Normal] (h₁ : Z₁ ≤ Subgroup.center S)
    (h₂ : Z₂ ≤ Subgroup.center S) (s₁ : IsSimpleGroup (S ⧸ Z₁)) (s₂ : IsSimpleGroup (S ⧸ Z₂)) :
    Nat.card (S ⧸ Z₁) = Nat.card (S ⧸ Z₂) := by
  rw [center_eq_of_simple_central_quot hq Z₁ h₁ s₁, center_eq_of_simple_central_quot hq Z₂ h₂ s₂]

theorem flag_arith_finset {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (h : (6 + ∑ i ∈ s, m i) ^ 2 = 18 + ∑ i ∈ s, m i ^ 2 + 18) : ∑ i ∈ s, m i = 0 := by
  have hsq : ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Nat.zero_le (m i))
  have h12 : 12 * ∑ i ∈ s, m i ≤ 0 := by nlinarith [hsq, h]
  omega

theorem flag_core_arith {k r : ℕ} (m : Fin k → ℕ) (a b i : Fin k) (hab : a ≠ b) (hai : a ≠ i)
    (hbi : b ≠ i) (ha1 : m a = 1) (hb1 : m b = 1) (hi4 : m i = 4)
    (hsum : ∑ j, m j = r) (hsq : r ^ 2 = 18 + ∑ j, m j ^ 2) : r = 6 := by
  have hsub : ({a, i, b} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
  have hs1 : ∑ j ∈ Finset.univ \ {a, i, b}, m j + ∑ j ∈ ({a, i, b} : Finset (Fin k)), m j =
      ∑ j, m j := Finset.sum_sdiff hsub
  have hs2 : ∑ j ∈ Finset.univ \ {a, i, b}, m j ^ 2 +
      ∑ j ∈ ({a, i, b} : Finset (Fin k)), m j ^ 2 = ∑ j, m j ^ 2 := Finset.sum_sdiff hsub
  have hnot : a ∉ ({i, b} : Finset (Fin k)) := by simp [hai, hab]
  have hT1 : ∑ j ∈ ({a, i, b} : Finset (Fin k)), m j = 6 := by
    rw [Finset.sum_insert hnot, Finset.sum_pair (Ne.symm hbi)]
    omega
  have hT2 : ∑ j ∈ ({a, i, b} : Finset (Fin k)), m j ^ 2 = 18 := by
    rw [Finset.sum_insert hnot, Finset.sum_pair (Ne.symm hbi)]
    simp [ha1, hi4, hb1]
  have e1 : r = 6 + ∑ j ∈ Finset.univ \ {a, i, b}, m j := by omega
  have e2 : ∑ j, m j ^ 2 = 18 + ∑ j ∈ Finset.univ \ {a, i, b}, m j ^ 2 := by omega
  have hz := flag_arith_finset (Finset.univ \ {a, i, b}) m (by rw [← e1]; omega)
  omega

theorem flag_type_of_radical
    (hRad : RadicalTwoSubgroupLinearStatement) (hArtin : ArtinLinearOrdersStatement)
    (r : ℕ) (K : Type) [Field K] [Finite K] (hr : 3 ≤ r)
    (hK : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f) (q : ℕ) (hq4 : 4 ≤ q)
    (K' : Type) [Field K'] [Finite K'] (hK' : Nat.card K' = q) (hq2 : ∃ g : ℕ, q = 2 ^ g)
    (U : Subgroup (StatedProj (StatedSL r K))) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hrad : inSubgroup (pCore 2) (Subgroup.normalizer (U : Set (StatedProj (StatedSL r K)))) = U)
    (hZ : Nat.card ↥(Subgroup.center ↥U) = q) (hcard : Nat.card U = q ^ 9)
    (S : Subgroup (↥(Subgroup.normalizer (U : Set (StatedProj (StatedSL r K)))) ⧸
        U.subgroupOf (Subgroup.normalizer (U : Set (StatedProj (StatedSL r K))))))
    (hSn : S.Normal) (hSq : IsQuasisimple S)
    (hS4 : ∃ Z' : Subgroup S, Z' ≤ Subgroup.center S ∧ ∃ _ : Z'.Normal,
      Nonempty ((S ⧸ Z') ≃* StatedProj (StatedSL 4 K'))) :
    r = 6 ∧ Nat.card K = q := by
  obtain ⟨k, m, hk, hm1, hsum, hcen, hord, hS⟩ := hRad r K hr hK U hU1 hU2 hrad
  obtain ⟨i, hi2, hbad, Z₂, hZ₂c, hZ₂n, hiso⟩ := hS S hSn hSq
  obtain ⟨Z₁, hZ₁c, hZ₁n, hiso4⟩ := hS4
  obtain ⟨e2⟩ := hiso
  obtain ⟨e4⟩ := hiso4
  have hKne3 : Nat.card K ≠ 3 := by
    obtain ⟨f, hf1, hf⟩ := hK
    rw [hf]
    intro h
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hK4 : IsSimpleGroup (StatedProj (StatedSL 4 K')) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 4) K' (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hKi : IsSimpleGroup (StatedProj (StatedSL (m i) K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := m i) K hi2
      (not_and_or.mp hbad) (Or.inr hKne3)
  have hS2 : IsSimpleGroup (S ⧸ Z₂) := e2.isSimpleGroup
  have hS1 : IsSimpleGroup (S ⧸ Z₁) := e4.isSimpleGroup
  have hcardSQ : Nat.card (S ⧸ Z₂) = Nat.card (S ⧸ Z₁) :=
    card_central_quot_eq_of_simple hSq Z₂ Z₁ hZ₂c hZ₁c hS2 hS1
  have hcardeq : Nat.card (StatedProj (StatedSL (m i) K)) =
      Nat.card (StatedProj (StatedSL 4 K')) :=
    (Nat.card_congr e2.toEquiv).symm.trans (hcardSQ.trans (Nat.card_congr e4.toEquiv))
  have hK'pow : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K' = 2 ^ f := by
    obtain ⟨g, hg⟩ := hq2
    have hg1 : 1 ≤ g := by
      rcases Nat.eq_zero_or_pos g with h0 | h0
      · subst h0
        simp at hg
        omega
      · omega
    exact ⟨g, hg1, by rw [hK', hg]⟩
  have hbad4 : ¬ (4 = 2 ∧ Nat.card K' = 2) := fun h => absurd h.1 (by norm_num)
  have hArt := hArtin (m i) 4 K K' hi2 (by norm_num) hK hK'pow hbad hbad4 hcardeq
  have hmi : m i = 4 ∧ Nat.card K = q := by
    rcases hArt with ⟨h1, h2⟩ | ⟨h1, h2, _, h4⟩ | ⟨h1, _, h3, _⟩
    · exact ⟨h1, by rw [h2, hK']⟩
    · exfalso
      omega
    · exfalso
      omega
  obtain ⟨hmi4, hKq⟩ := hmi
  have hqE := hcen
  rw [hZ, hKq] at hqE
  have hexp : m ⟨0, by omega⟩ * m ⟨k - 1, by omega⟩ = 1 := by
    have h2 : q ^ (m ⟨0, by omega⟩ * m ⟨k - 1, by omega⟩) = q ^ 1 := by
      rw [pow_one]
      exact hqE.symm
    exact Nat.pow_right_injective (show 2 ≤ q by omega) h2
  have hm0 : m ⟨0, by omega⟩ = 1 := Nat.eq_one_of_mul_eq_one_right hexp
  have hmk : m ⟨k - 1, by omega⟩ = 1 := Nat.eq_one_of_mul_eq_one_left hexp
  have hE9 : (r ^ 2 - ∑ j, m j ^ 2) / 2 = 9 := by
    have h9 : q ^ ((r ^ 2 - ∑ j, m j ^ 2) / 2) = q ^ 9 := by
      rw [← hcard, hord, hKq]
    exact Nat.pow_right_injective (show 2 ≤ q by omega) h9
  have hsq_mod : ∀ x : ℕ, x ^ 2 % 2 = x % 2 := by
    intro x
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have hsum_mod : ∀ s : Finset (Fin k), (∑ j ∈ s, m j ^ 2) % 2 = (∑ j ∈ s, m j) % 2 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have := hsq_mod (m a)
      omega
  have hr_mod : r ^ 2 % 2 = (∑ j, m j ^ 2) % 2 := by
    rw [← hsum, hsq_mod, hsum_mod Finset.univ]
  have hle : ∑ j, m j ^ 2 ≤ r ^ 2 := by
    rw [← hsum]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => Nat.zero_le (m j))
  have hsq18 : r ^ 2 = 18 + ∑ j, m j ^ 2 := by omega
  have hab : (⟨0, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩ := by
    intro h
    have h' := Fin.mk.inj h
    omega
  have hai : (⟨0, by omega⟩ : Fin k) ≠ i := by
    intro h
    rw [h] at hm0
    omega
  have hbi : (⟨k - 1, by omega⟩ : Fin k) ≠ i := by
    intro h
    rw [h] at hmk
    omega
  exact ⟨flag_core_arith m _ _ i hab hai hbi hm0 hmk hmi4 hsum hsq18, hKq⟩

end CFSG.RankThree.GF2n.Stroth80
