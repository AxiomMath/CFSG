module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitWeylEquiv
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private def l05nK3c_SignedPerm (k : ℕ) (g : ggWeylD k) (π : Equiv.Perm (Fin k))
    (ε : Fin k → ℤ) : Prop :=
  (∀ c, ε c = 1 ∨ ε c = -1) ∧
    ∀ v : Fin k → ℤ,
      toStdD k (weylAction (isFiniteType_cartanD k) g v) = fun c => ε c * toStdD k v (π c)

private def l05nK3c_zero (k : ℕ) (hk : 3 ≤ k) : Fin k := ⟨0, by omega⟩

private def l05nK3c_one (k : ℕ) (hk : 3 ≤ k) : Fin k := ⟨1, by omega⟩

private def l05nK3c_two (k : ℕ) (hk : 3 ≤ k) : Fin k := ⟨2, by omega⟩

private def l05nK3c_next (k : ℕ) (a : Fin k) (ha : a.val + 1 < k) : Fin k := ⟨a.val + 1, ha⟩

private lemma l05nK3c_zero_val (k : ℕ) (hk : 3 ≤ k) : (l05nK3c_zero k hk).val = 0 := rfl

private lemma l05nK3c_one_val (k : ℕ) (hk : 3 ≤ k) : (l05nK3c_one k hk).val = 1 := rfl

private lemma l05nK3c_two_val (k : ℕ) (hk : 3 ≤ k) : (l05nK3c_two k hk).val = 2 := rfl

private lemma l05nK3c_next_val (k : ℕ) (a : Fin k) (ha : a.val + 1 < k) :
    (l05nK3c_next k a ha).val = a.val + 1 := rfl

private lemma l05nK3c_one_ne_two (k : ℕ) (hk : 3 ≤ k) :
    l05nK3c_one k hk ≠ l05nK3c_two k hk := by
  intro h
  have hv := congrArg Fin.val h
  simp only [l05nK3c_one_val, l05nK3c_two_val] at hv
  omega

private lemma l05nK3c_zero_ne_next (k : ℕ) (hk : 3 ≤ k)
    (h : (l05nK3c_zero k hk).val + 1 < k) :
    l05nK3c_zero k hk ≠ l05nK3c_next k (l05nK3c_zero k hk) h := by
  intro heq
  have hv := congrArg Fin.val heq
  rw [l05nK3c_zero_val, l05nK3c_next_val, l05nK3c_zero_val] at hv
  omega

private lemma l05nK3c_zero_ne_next_next (k : ℕ) (hk : 3 ≤ k)
    (h : (l05nK3c_zero k hk).val + 1 < k)
    (h' : (l05nK3c_next k (l05nK3c_zero k hk) h).val + 1 < k) :
    l05nK3c_zero k hk ≠ l05nK3c_next k (l05nK3c_next k (l05nK3c_zero k hk) h) h' := by
  intro heq
  have hv := congrArg Fin.val heq
  rw [l05nK3c_zero_val, l05nK3c_next_val, l05nK3c_next_val, l05nK3c_zero_val] at hv
  omega

private lemma l05nK3c_next_ne_next_next (k : ℕ) (hk : 3 ≤ k)
    (h : (l05nK3c_zero k hk).val + 1 < k)
    (h' : (l05nK3c_next k (l05nK3c_zero k hk) h).val + 1 < k) :
    l05nK3c_next k (l05nK3c_zero k hk) h ≠
      l05nK3c_next k (l05nK3c_next k (l05nK3c_zero k hk) h) h' := by
  intro heq
  have hv := congrArg Fin.val heq
  rw [l05nK3c_next_val, l05nK3c_next_val, l05nK3c_next_val, l05nK3c_zero_val] at hv
  omega

private def l05nK3c_signSet (k : ℕ) (hk : 3 ≤ k) : Fin k ⊕ Unit → Finset (Fin k)
  | Sum.inl i => if i = l05nK3c_zero k hk then ∅ else {l05nK3c_zero k hk, i}
  | Sum.inr _ => {l05nK3c_one k hk, l05nK3c_two k hk}

private def l05nK3c_eps (k : ℕ) (hk : 3 ≤ k) (j : Fin k ⊕ Unit) : Fin k → ℤ :=
  fun c => if c ∈ l05nK3c_signSet k hk j then -1 else 1

private lemma l05nK3c_toStdD_single_self (k : ℕ) (hk2 : 2 ≤ k) (x : Fin k) :
    toStdD k (Pi.single x (1 : ℤ)) x = 1 := by
  by_cases hx : x.val + 1 < k
  · rw [toStdD_single_of_lt k hx]
    have hne : (⟨x.val + 1, hx⟩ : Fin k) ≠ x := by
      intro h
      simp only [Fin.ext_iff] at h
      omega
    rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne), sub_zero]
  · rw [toStdD_single_of_not_lt k hx hk2]
    have hne : (⟨k - 2, by omega⟩ : Fin k) ≠ x := by
      intro h
      simp only [Fin.ext_iff] at h
      have := x.isLt
      omega
    rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hne), Pi.single_eq_same, zero_add]

private lemma l05nK3c_ifsub_eq_zero_iff {k : ℕ} (a b x : Fin k) (hab : a ≠ b) :
    ((if x = a then (1 : ℤ) else 0) - (if x = b then (1 : ℤ) else 0)) = 0 ↔
      ¬(x = a ∨ x = b) := by
  by_cases ha : x = a
  · rw [if_pos ha, if_neg (fun h : x = b => hab (ha.symm.trans h)), sub_zero]
    simp [ha]
  · by_cases hb : x = b
    · rw [if_neg ha, if_pos hb, zero_sub]
      simp [hb]
    · rw [if_neg ha, if_neg hb, sub_zero]
      simp [ha, hb]

private theorem l05nK3c_signedPerm_unique {k : ℕ} (hk : 3 ≤ k) {g : ggWeylD k}
    {π π' : Equiv.Perm (Fin k)} {ε ε' : Fin k → ℤ}
    (h : l05nK3c_SignedPerm k g π ε) (h' : l05nK3c_SignedPerm k g π' ε') :
    π = π' ∧ ε = ε' := by
  obtain ⟨hε, hact⟩ := h
  obtain ⟨hε', hact'⟩ := h'
  have hfun : ∀ v : Fin k → ℤ,
      (fun c => ε c * toStdD k v (π c)) = fun c => ε' c * toStdD k v (π' c) := by
    intro v
    rw [← hact v, hact' v]
  have key : ∀ (a : Fin k) (ha : a.val + 1 < k) (c : Fin k),
      (π c = a ∨ π c = (⟨a.val + 1, ha⟩ : Fin k)) ↔
        (π' c = a ∨ π' c = (⟨a.val + 1, ha⟩ : Fin k)) := by
    intro a ha c
    have hc := congrFun (hfun (Pi.single a (1 : ℤ))) c
    rw [toStdD_single_of_lt k ha] at hc
    simp only [Pi.sub_apply, Pi.single_apply] at hc
    have hab : a ≠ (⟨a.val + 1, ha⟩ : Fin k) := by
      intro hh
      simp only [Fin.ext_iff] at hh
      omega
    have hzero :
        ((if π c = a then (1 : ℤ) else 0) -
            (if π c = (⟨a.val + 1, ha⟩ : Fin k) then 1 else 0)) = 0 ↔
          ((if π' c = a then (1 : ℤ) else 0) -
            (if π' c = (⟨a.val + 1, ha⟩ : Fin k) then 1 else 0)) = 0 := by
      constructor
      · intro hx
        have h0 : ε c *
            ((if π c = a then (1 : ℤ) else 0) -
              (if π c = (⟨a.val + 1, ha⟩ : Fin k) then 1 else 0)) = 0 := by
          rw [hx, mul_zero]
        rw [hc] at h0
        have hne : ε' c ≠ 0 := by
          rcases hε' c with h1 | h1 <;> rw [h1] <;> norm_num
        exact (mul_eq_zero.mp h0).resolve_left hne
      · intro hx
        have h0 : ε' c *
            ((if π' c = a then (1 : ℤ) else 0) -
              (if π' c = (⟨a.val + 1, ha⟩ : Fin k) then 1 else 0)) = 0 := by
          rw [hx, mul_zero]
        rw [← hc] at h0
        have hne : ε c ≠ 0 := by
          rcases hε c with h1 | h1 <;> rw [h1] <;> norm_num
        exact (mul_eq_zero.mp h0).resolve_left hne
    rw [l05nK3c_ifsub_eq_zero_iff a (⟨a.val + 1, ha⟩ : Fin k) (π c) hab,
      l05nK3c_ifsub_eq_zero_iff a (⟨a.val + 1, ha⟩ : Fin k) (π' c) hab] at hzero
    exact not_iff_not.mp hzero
  let f : Equiv.Perm (Fin k) := π' * π.symm
  have hf_apply : ∀ c, f (π c) = π' c := by
    intro c
    simp [f]
  have hpair : ∀ (a : Fin k) (ha : a.val + 1 < k),
      f a = a ∨ f a = l05nK3c_next k a ha := by
    intro a ha
    have hfa : f a = π' (π.symm a) := by simpa using hf_apply (π.symm a)
    rcases (key a ha (π.symm a)).mp (Or.inl (by simp)) with hh | hh
    · exact Or.inl (by rw [hfa, hh])
    · refine Or.inr ?_
      rw [hfa, hh]
      exact Fin.ext (by simp [l05nK3c_next])
  have hpair' : ∀ (a : Fin k) (ha : a.val + 1 < k),
      f (l05nK3c_next k a ha) = a ∨ f (l05nK3c_next k a ha) = l05nK3c_next k a ha := by
    intro a ha
    have hfa : f (l05nK3c_next k a ha) = π' (π.symm (l05nK3c_next k a ha)) := by
      simpa using hf_apply (π.symm (l05nK3c_next k a ha))
    rcases (key a ha (π.symm (l05nK3c_next k a ha))).mp
        (Or.inr (by simp [l05nK3c_next])) with hh | hh
    · exact Or.inl (by rw [hfa, hh])
    · refine Or.inr ?_
      rw [hfa, hh]
      exact Fin.ext (by simp [l05nK3c_next])
  have hfix : ∀ m : ℕ, ∀ hm : m < k, f ⟨m, hm⟩ = ⟨m, hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        have h01 : (l05nK3c_zero k hk).val + 1 < k := by
          simp only [l05nK3c_zero, Fin.val_mk]
          omega
        rcases hpair (l05nK3c_zero k hk) h01 with h | h
        · exact h
        · exfalso
          have h12 : (l05nK3c_next k (l05nK3c_zero k hk) h01).val + 1 < k := by
            rw [l05nK3c_next_val, l05nK3c_zero_val]
            omega
          have h0 := hpair' (l05nK3c_zero k hk) h01
          have h1 := hpair (l05nK3c_next k (l05nK3c_zero k hk) h01) h12
          rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
          · rw [h0] at h1
            exact absurd h1 (l05nK3c_zero_ne_next k hk h01)
          · rw [h0] at h1
            exact absurd h1 (l05nK3c_zero_ne_next_next k hk h01 h12)
          · have h01eq : f (l05nK3c_zero k hk) =
                f (l05nK3c_next k (l05nK3c_zero k hk) h01) := by rw [h, h0]
            exact absurd (f.injective h01eq) (l05nK3c_zero_ne_next k hk h01)
          · rw [h0] at h1
            exact absurd h1 (l05nK3c_next_ne_next_next k hk h01 h12)
      · have hm1 : m - 1 < k := by omega
        have hprev : f (⟨m - 1, hm1⟩ : Fin k) = (⟨m - 1, hm1⟩ : Fin k) :=
          ih (m - 1) (by omega) hm1
        have hsucc : (⟨m - 1, hm1⟩ : Fin k).val + 1 < k := by
          simp only [Fin.val_mk]
          omega
        have hloc : l05nK3c_next k (⟨m - 1, hm1⟩ : Fin k) hsucc = ⟨m, hm⟩ := by
          simp only [l05nK3c_next, Fin.ext_iff, Fin.val_mk]
          omega
        have hmem := hpair' (⟨m - 1, hm1⟩ : Fin k) hsucc
        rw [hloc] at hmem
        rcases hmem with hmem | hmem
        · exfalso
          have hbad : f (⟨m - 1, hm1⟩ : Fin k) = f ⟨m, hm⟩ := by rw [hprev, hmem]
          have := f.injective hbad
          simp only [Fin.ext_iff] at this
          omega
        · exact hmem
  have hfid : f = 1 := by
    apply Equiv.ext
    intro c
    simpa using hfix c.val c.isLt
  have hfπ : f * π = π' := by
    ext c
    simp [f]
  have hπeq : π = π' := by
    rw [← hfπ, hfid, one_mul]
  have heps : ε = ε' := by
    funext c
    have hself : toStdD k (Pi.single (π c) (1 : ℤ)) (π c) = 1 :=
      l05nK3c_toStdD_single_self k (by omega) (π c)
    have hpc : π' c = π c := by rw [← hπeq]
    have hc := congrFun (hfun (Pi.single (π c) (1 : ℤ))) c
    rw [hself, hpc, hself] at hc
    simpa using hc
  exact ⟨hπeq, heps⟩

private theorem l05nK3c_exists_sgnReal (k : ℕ) (hk : 3 ≤ k) (j : Fin k ⊕ Unit) :
    ∃ g : ggWeylD k, ∀ v : Fin k → ℤ,
      toStdD k (weylAction (isFiniteType_cartanD k) g v) = l05nK3c_eps k hk j • toStdD k v := by
  have hk2 : 2 ≤ k := by omega
  rcases j with i | u
  · by_cases hi : i = l05nK3c_zero k hk
    · subst hi
      refine ⟨1, fun v => ?_⟩
      funext c
      simp [l05nK3c_eps, l05nK3c_signSet, Pi.smul_apply, smul_eq_mul]
    · obtain ⟨g, hg⟩ := ggD_exists_negPair (k := k) hk2 (x := l05nK3c_zero k hk) (y := i)
        (fun h => hi h.symm)
      refine ⟨g, fun v => ?_⟩
      rw [hg v]
      funext c
      by_cases hc : c = l05nK3c_zero k hk ∨ c = i
      · rw [if_pos hc]
        have hcm : c ∈ ({l05nK3c_zero k hk, i} : Finset (Fin k)) := by
          rcases hc with rfl | rfl <;> simp
        simp [l05nK3c_eps, l05nK3c_signSet, hi, hcm]
      · rw [if_neg hc]
        have hcm : c ∉ ({l05nK3c_zero k hk, i} : Finset (Fin k)) := by
          intro h
          exact hc (by simpa using h)
        simp [l05nK3c_eps, l05nK3c_signSet, hi, hcm]
  · obtain ⟨g, hg⟩ := ggD_exists_negPair (k := k) hk2 (x := l05nK3c_one k hk)
      (y := l05nK3c_two k hk) (l05nK3c_one_ne_two k hk)
    refine ⟨g, fun v => ?_⟩
    rw [hg v]
    funext c
    by_cases hc : c = l05nK3c_one k hk ∨ c = l05nK3c_two k hk
    · rw [if_pos hc]
      have hcm : c ∈ ({l05nK3c_one k hk, l05nK3c_two k hk} : Finset (Fin k)) := by
        rcases hc with rfl | rfl <;> simp
      simp [l05nK3c_eps, l05nK3c_signSet, hcm]
    · rw [if_neg hc]
      have hcm : c ∉ ({l05nK3c_one k hk, l05nK3c_two k hk} : Finset (Fin k)) := by
        intro h
        exact hc (by simpa using h)
      simp [l05nK3c_eps, l05nK3c_signSet, hcm]

private noncomputable def l05nK3c_sgnReal (k : ℕ) (hk : 3 ≤ k) (j : Fin k ⊕ Unit) :
    ggWeylD k :=
  Classical.choose (l05nK3c_exists_sgnReal k hk j)

private theorem l05nK3c_sgnReal_spec (k : ℕ) (hk : 3 ≤ k) (j : Fin k ⊕ Unit) :
    ∀ v : Fin k → ℤ,
      toStdD k (weylAction (isFiniteType_cartanD k) (l05nK3c_sgnReal k hk j) v) =
        l05nK3c_eps k hk j • toStdD k v :=
  Classical.choose_spec (l05nK3c_exists_sgnReal k hk j)

private noncomputable def l05nK3c_permReal (k : ℕ) (hk2 : 2 ≤ k)
    (π : Equiv.Perm (Fin k)) : ggWeylD k :=
  Classical.choose (ggD_exists_perm hk2 π)

private theorem l05nK3c_permReal_spec (k : ℕ) (hk2 : 2 ≤ k) (π : Equiv.Perm (Fin k)) :
    ∀ v : Fin k → ℤ,
      toStdD k (weylAction (isFiniteType_cartanD k) (l05nK3c_permReal k hk2 π) v) =
        toStdD k v ∘ π :=
  Classical.choose_spec (ggD_exists_perm hk2 π)

private theorem l05nK3c_eps_injective (k : ℕ) (hk : 3 ≤ k) :
    Function.Injective (l05nK3c_eps k hk) := by
  have hmem_inl : ∀ {i c : Fin k}, i ≠ l05nK3c_zero k hk →
      (c ∈ l05nK3c_signSet k hk (Sum.inl i) ↔ c = l05nK3c_zero k hk ∨ c = i) := by
    intro i c hi
    simp [l05nK3c_signSet, hi]
  have hmem_inr : ∀ (u : Unit) {c : Fin k},
      (c ∈ l05nK3c_signSet k hk (Sum.inr u) ↔
        c = l05nK3c_one k hk ∨ c = l05nK3c_two k hk) := by
    intro u c
    simp [l05nK3c_signSet]
  have hzero_inr : ∀ u : Unit, l05nK3c_zero k hk ∉ l05nK3c_signSet k hk (Sum.inr u) := by
    intro u
    rw [hmem_inr u]
    rintro (h | h)
    · have hv := congrArg Fin.val h
      simp only [l05nK3c_zero_val, l05nK3c_one_val] at hv
      omega
    · have hv := congrArg Fin.val h
      simp only [l05nK3c_zero_val, l05nK3c_two_val] at hv
      omega
  intro j j' h
  have hset : l05nK3c_signSet k hk j = l05nK3c_signSet k hk j' := by
    ext c
    have hc := congrFun h c
    simp only [l05nK3c_eps] at hc
    by_cases h1 : c ∈ l05nK3c_signSet k hk j
    · by_cases h2 : c ∈ l05nK3c_signSet k hk j'
      · simp [h1, h2]
      · exfalso
        rw [if_pos h1, if_neg h2] at hc
        norm_num at hc
    · by_cases h2 : c ∈ l05nK3c_signSet k hk j'
      · exfalso
        rw [if_neg h1, if_pos h2] at hc
        norm_num at hc
      · simp [h1, h2]
  rcases j with i | u
  · rcases j' with i' | u'
    · by_cases hi : i = l05nK3c_zero k hk
      · subst hi
        have hz : l05nK3c_signSet k hk (Sum.inl i') = ∅ := by
          rw [← hset]
          simp [l05nK3c_signSet]
        have hzi : i' = l05nK3c_zero k hk := by
          by_contra hne
          have hmem : l05nK3c_zero k hk ∈ l05nK3c_signSet k hk (Sum.inl i') :=
            (hmem_inl hne).mpr (Or.inl rfl)
          rw [hz] at hmem
          simp at hmem
        subst hzi
        rfl
      · by_cases hi' : i' = l05nK3c_zero k hk
        · subst hi'
          have hz : l05nK3c_signSet k hk (Sum.inl i) = ∅ := by
            rw [hset]
            simp [l05nK3c_signSet]
          have hmem : l05nK3c_zero k hk ∈ l05nK3c_signSet k hk (Sum.inl i) :=
            (hmem_inl hi).mpr (Or.inl rfl)
          rw [hz] at hmem
          simp at hmem
        · have hmem : i ∈ l05nK3c_signSet k hk (Sum.inl i') := by
            rw [← hset]
            exact (hmem_inl hi).mpr (Or.inr rfl)
          rcases (hmem_inl hi').mp hmem with h | h
          · exact absurd h hi
          · exact congrArg Sum.inl h
    · exfalso
      by_cases hi : i = l05nK3c_zero k hk
      · rw [hi] at hset
        have hz : l05nK3c_signSet k hk (Sum.inl (l05nK3c_zero k hk)) = ∅ := by
          simp [l05nK3c_signSet]
        rw [hz] at hset
        have hmem : l05nK3c_one k hk ∈ l05nK3c_signSet k hk (Sum.inr u') :=
          (hmem_inr u').mpr (Or.inl rfl)
        rw [← hset] at hmem
        exact absurd hmem (by simp)
      · have hmem : l05nK3c_zero k hk ∈ l05nK3c_signSet k hk (Sum.inr u') := by
          rw [← hset]
          exact (hmem_inl hi).mpr (Or.inl rfl)
        exact hzero_inr u' hmem
  · rcases j' with i' | u'
    · exfalso
      by_cases hi' : i' = l05nK3c_zero k hk
      · rw [hi'] at hset
        have hz : l05nK3c_signSet k hk (Sum.inl (l05nK3c_zero k hk)) = ∅ := by
          simp [l05nK3c_signSet]
        rw [hz] at hset
        have hmem : l05nK3c_one k hk ∈ l05nK3c_signSet k hk (Sum.inr u) :=
          (hmem_inr u).mpr (Or.inl rfl)
        rw [hset] at hmem
        exact absurd hmem (by simp)
      · have hmem : l05nK3c_zero k hk ∈ l05nK3c_signSet k hk (Sum.inr u) := by
          rw [hset]
          exact (hmem_inl hi').mpr (Or.inl rfl)
        exact hzero_inr u hmem
    · rfl

private theorem l05nK3c_card_wD_ge (k : ℕ) (hk : 3 ≤ k) :
    (k + 1).factorial ≤ Nat.card (ggWeylD k) := by
  have hk2 : 2 ≤ k := by omega
  haveI : Finite (ggWeylD k) := finite_group (isFiniteType_cartanD k)
  let F : Equiv.Perm (Fin k) × (Fin k ⊕ Unit) → ggWeylD k :=
    fun q => l05nK3c_permReal k hk2 q.1 * l05nK3c_sgnReal k hk q.2
  have hF_rep : ∀ (π : Equiv.Perm (Fin k)) (j : Fin k ⊕ Unit),
      l05nK3c_SignedPerm k (l05nK3c_permReal k hk2 π * l05nK3c_sgnReal k hk j) π
        (fun c => l05nK3c_eps k hk j (π c)) := by
    intro π j
    refine ⟨?_, ?_⟩
    · intro c
      simp only [l05nK3c_eps]
      split_ifs <;> norm_num
    · intro v
      calc toStdD k (weylAction (isFiniteType_cartanD k)
            (l05nK3c_permReal k hk2 π * l05nK3c_sgnReal k hk j) v)
          = toStdD k (weylAction (isFiniteType_cartanD k) (l05nK3c_permReal k hk2 π)
              (weylAction (isFiniteType_cartanD k) (l05nK3c_sgnReal k hk j) v)) := by
            rw [weylAction_mul_apply]
        _ = toStdD k (weylAction (isFiniteType_cartanD k) (l05nK3c_sgnReal k hk j) v) ∘ π :=
            l05nK3c_permReal_spec k hk2 π _
        _ = (l05nK3c_eps k hk j • toStdD k v) ∘ π := by
            rw [l05nK3c_sgnReal_spec k hk j v]
        _ = fun c => l05nK3c_eps k hk j (π c) * toStdD k v (π c) := by
            funext c
            simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  have hF : Function.Injective F := by
    intro q q' hEq
    obtain ⟨π, j⟩ := q
    obtain ⟨π', j'⟩ := q'
    have h1 := hF_rep π j
    have h2 := hF_rep π' j'
    have hEq' : l05nK3c_permReal k hk2 π * l05nK3c_sgnReal k hk j =
        l05nK3c_permReal k hk2 π' * l05nK3c_sgnReal k hk j' := hEq
    rw [hEq'] at h1
    obtain ⟨hπ, heps⟩ := l05nK3c_signedPerm_unique hk h1 h2
    have heps' : l05nK3c_eps k hk j = l05nK3c_eps k hk j' := by
      funext c
      have := congrFun heps (π.symm c)
      simpa [hπ] using this
    exact Prod.ext hπ (l05nK3c_eps_injective k hk heps')
  have hcard := Nat.card_le_card_of_injective F hF
  have hcard2 : Nat.card (Equiv.Perm (Fin k) × (Fin k ⊕ Unit)) = (k + 1).factorial := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit,
      Nat.factorial_succ, mul_comm]
  rwa [hcard2] at hcard

private theorem l05nK3c_card_coxeterA (n : ℕ) :
    Nat.card (CoxeterMatrix.A n).Group = (n + 1).factorial := by
  rw [← coxeterMatrix_isFiniteType_A_eq n]
  rw [← Nat.card_congr (typeAWeylEquiv n).toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem ggRC_card_weyl_ge {ι : Type} [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    (hM : GGIsWeylMatrix M) (hr : 9 ≤ Fintype.card ι) :
    (Fintype.card ι + 1).factorial ≤ Nat.card M.Group := by
  rcases hM with ⟨n, e, hn, hAD⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · rcases hAD with hA | hBD
    ·
      have hcardI : Fintype.card ι = n := by
        rw [← Fintype.card_congr e, Fintype.card_fin]
      rw [hcardI]
      rw [hA]
      rw [Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv]
      rw [l05nK3c_card_coxeterA n]
    · rcases hBD with ⟨hn2, hB⟩ | ⟨hn4, hD⟩
      ·
        have hcardI : Fintype.card ι = n := by
          rw [← Fintype.card_congr e, Fintype.card_fin]
        rw [hcardI]
        rw [hB]
        rw [Nat.card_congr ((CoxeterMatrix.B n).reindexGroupEquiv e).toEquiv]
        calc (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
          _ ≤ 2 ^ n * n.factorial :=
              Nat.mul_le_mul_right n.factorial
                (Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := n)))
          _ ≤ Nat.card (CoxeterMatrix.B n).Group := SpFrame.card_coxeterB_ge n hn2
      ·
        have hcardI : Fintype.card ι = n := by
          rw [← Fintype.card_congr e, Fintype.card_fin]
        rw [hcardI]
        obtain ⟨φ, -⟩ := ggDk_weylEquiv hD
        rw [Nat.card_congr φ.toEquiv]
        exact l05nK3c_card_wD_ge n (by omega)
  ·
    exfalso
    have h6 : Fintype.card ι = 6 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  ·
    exfalso
    have h7 : Fintype.card ι = 7 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  ·
    exfalso
    have h8 : Fintype.card ι = 8 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  ·
    exfalso
    have h4 : Fintype.card ι = 4 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  ·
    exfalso
    have h2 : Fintype.card ι = 2 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega

end CFSG.StandardType
