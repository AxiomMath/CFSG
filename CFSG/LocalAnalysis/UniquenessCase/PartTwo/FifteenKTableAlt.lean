module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.SectionRank

private lemma s15k_tal_zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val = 0 ∨ a.val = 1 := by
    have := ZMod.val_lt a
    omega
  have hcast : (a.val : ZMod 2) = a := ZMod.natCast_zmod_val a
  rcases h with h | h
  · left; rw [← hcast, h]; rfl
  · right; rw [← hcast, h]; rfl

private lemma s15k_tal_isThreeCycle {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Equiv.Perm.IsThreeCycle (Equiv.swap a b * Equiv.swap b c) := by
  have hsupp : (Equiv.swap a b * Equiv.swap b c).support = {a, b, c} :=
    Equiv.Perm.support_swap_mul_swap (by simp [hab, hac, hbc])
  rw [← _root_.card_support_eq_three_iff, hsupp]
  exact Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩

private lemma s15k_tal_mem_permStab {n : ℕ} (x : CFSG.Quasithin.G6.PermMod n)
    {T : Finset (Fin n)}
    (hT : ∀ i ∈ T, ∀ k ∈ T, Multiplicative.toAdd x i = Multiplicative.toAdd x k)
    {c : Equiv.Perm (Fin n)} (hc : c.support ⊆ T) : c ∈ s15kPermStab n x := by
  show CFSG.Quasithin.G6.permAct n c x = x
  apply Multiplicative.toAdd.injective
  funext i
  rw [CFSG.Quasithin.G6.permAct_apply]
  by_cases hi : i ∈ T
  · have hci : c⁻¹ i ∈ T := by
      by_cases hfix : c⁻¹ i = i
      · rwa [hfix]
      · have hmem : c⁻¹ i ∈ c.support := by
          rw [Equiv.Perm.mem_support]
          intro h
          refine hfix ?_
          calc c⁻¹ i = c (c⁻¹ i) := h.symm
            _ = i := Equiv.apply_symm_apply c i
        exact hc hmem
    exact hT (c⁻¹ i) hci i hi
  · have hfix : c⁻¹ i = i := by
      by_contra h
      have hmem : i ∈ (c⁻¹).support := by
        rw [Equiv.Perm.mem_support]
        exact h
      rw [Equiv.Perm.support_inv] at hmem
      exact hi (hc hmem)
    rw [hfix]

private lemma s15k_tal_threeCycle_mem {n : ℕ} (x : CFSG.Quasithin.G6.PermMod n)
    {T : Finset (Fin n)}
    (hT : ∀ i ∈ T, ∀ k ∈ T, Multiplicative.toAdd x i = Multiplicative.toAdd x k)
    {a b c : Fin n} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup (Fin n) ⊓ s15kPermStab n x := by
  have hsupp : (Equiv.swap a b * Equiv.swap b c).support = {a, b, c} :=
    Equiv.Perm.support_swap_mul_swap (by simp [hab, hac, hbc])
  refine Subgroup.mem_inf.mpr ⟨(s15k_tal_isThreeCycle hab hac hbc).mem_alternatingGroup, ?_⟩
  refine s15k_tal_mem_permStab x hT ?_
  intro i hi
  rw [hsupp] at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  exacts [ha, hb, hc]

private lemma s15k_tal_disjoint_swap {n : ℕ} {a b c d e g : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hde : d ≠ e) (hdg : d ≠ g) (heg : e ≠ g) (had : a ≠ d)
    (hae : a ≠ e) (hag : a ≠ g) (hbd : b ≠ d) (hbe : b ≠ e) (hbg : b ≠ g) (hcd : c ≠ d)
    (hce : c ≠ e) (hcg : c ≠ g) :
    Equiv.Perm.Disjoint (Equiv.swap a b * Equiv.swap b c)
      (Equiv.swap d e * Equiv.swap e g) := by
  have h1 : (Equiv.swap a b * Equiv.swap b c).support = {a, b, c} :=
    Equiv.Perm.support_swap_mul_swap (by simp [hab, hac, hbc])
  have h2 : (Equiv.swap d e * Equiv.swap e g).support = {d, e, g} :=
    Equiv.Perm.support_swap_mul_swap (by simp [hde, hdg, heg])
  rw [Equiv.Perm.disjoint_iff_disjoint_support, h1, h2]
  exact Finset.disjoint_iff_ne.mpr (by
    intro p hp q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · exact had
    · exact hae
    · exact hag
    · exact hbd
    · exact hbe
    · exact hbg
    · exact hcd
    · exact hce
    · exact hcg)

private lemma s15k_tal_pow_ne {n : ℕ} {γ₁ γ₂ : Equiv.Perm (Fin n)} {a b c d : Fin n}
    (h1 : γ₁.support = {a, b, c}) (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hγ₂d : γ₂ d ≠ d) : ∀ k : ℕ, γ₁ ^ k ≠ γ₂ := by
  intro k h
  have hfix : (γ₁ ^ k) d = d := by
    have hnot : d ∉ (γ₁ ^ k).support := by
      intro hmem
      have hsupp : d ∈ γ₁.support := Equiv.Perm.support_pow_le γ₁ k hmem
      rw [h1] at hsupp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsupp
      rcases hsupp with h' | h' | h'
      · exact hda h'
      · exact hdb h'
      · exact hdc h'
    rwa [Equiv.Perm.notMem_support] at hnot
  rw [h] at hfix
  exact hγ₂d hfix

private lemma s15k_tal_two_le_of_six {n : ℕ} (x : CFSG.Quasithin.G6.PermMod n)
    {S : Finset (Fin n)} (hS : 6 ≤ S.card)
    (hconst : ∀ i ∈ S, ∀ k ∈ S, Multiplicative.toAdd x i = Multiplicative.toAdd x k) :
    2 ≤ pRank 3 (alternatingGroup (Fin n) ⊓ s15kPermStab n x) := by
  classical
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (s := S) hS
  have hconstT : ∀ i ∈ T, ∀ k ∈ T,
      Multiplicative.toAdd x i = Multiplicative.toAdd x k :=
    fun i hi k hk => hconst i (hTS hi) k (hTS hk)
  obtain ⟨a, b, c, haT, hbT, hcT, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < T.card)
  have hsub : ({a, b, c} : Finset (Fin n)) ⊆ T := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    exacts [haT, hbT, hcT]
  have hcard3 : ({a, b, c} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hUcard : 2 < (T \ {a, b, c}).card := by
    rw [Finset.card_sdiff_of_subset hsub, hcard3, hTcard]
    norm_num
  obtain ⟨d, e, g, hdU, heU, hgU, hde, hdg, heg⟩ :=
    Finset.two_lt_card_iff.mp hUcard
  have hdT : d ∈ T := (Finset.mem_sdiff.mp hdU).1
  have heT : e ∈ T := (Finset.mem_sdiff.mp heU).1
  have hgT : g ∈ T := (Finset.mem_sdiff.mp hgU).1
  have hdnot : d ∉ ({a, b, c} : Finset (Fin n)) := (Finset.mem_sdiff.mp hdU).2
  have henot : e ∉ ({a, b, c} : Finset (Fin n)) := (Finset.mem_sdiff.mp heU).2
  have hgnot : g ∉ ({a, b, c} : Finset (Fin n)) := (Finset.mem_sdiff.mp hgU).2
  have hda : d ≠ a := fun h => hdnot (by simp [h])
  have hdb : d ≠ b := fun h => hdnot (by simp [h])
  have hdc : d ≠ c := fun h => hdnot (by simp [h])
  have had : a ≠ d := fun h => hdnot (by simp [h.symm])
  have hae : a ≠ e := fun h => henot (by simp [h.symm])
  have hag : a ≠ g := fun h => hgnot (by simp [h.symm])
  have hbd : b ≠ d := fun h => hdnot (by simp [h.symm])
  have hbe : b ≠ e := fun h => henot (by simp [h.symm])
  have hbg : b ≠ g := fun h => hgnot (by simp [h.symm])
  have hcd : c ≠ d := fun h => hdnot (by simp [h.symm])
  have hce : c ≠ e := fun h => henot (by simp [h.symm])
  have hcg : c ≠ g := fun h => hgnot (by simp [h.symm])
  have h1supp : (Equiv.swap a b * Equiv.swap b c).support = {a, b, c} :=
    Equiv.Perm.support_swap_mul_swap (by simp [hab, hac, hbc])
  have h2supp : (Equiv.swap d e * Equiv.swap e g).support = {d, e, g} :=
    Equiv.Perm.support_swap_mul_swap (by simp [hde, hdg, heg])
  have hγ1three := s15k_tal_isThreeCycle hab hac hbc
  have hγ2three := s15k_tal_isThreeCycle hde hdg heg
  have hγ1mem := s15k_tal_threeCycle_mem x hconstT haT hbT hcT hab hac hbc
  have hγ2mem := s15k_tal_threeCycle_mem x hconstT hdT heT hgT hde hdg heg
  have hcomm : Commute (Equiv.swap a b * Equiv.swap b c)
      (Equiv.swap d e * Equiv.swap e g) :=
    (s15k_tal_disjoint_swap hab hac hbc hde hdg heg had hae hag hbd hbe hbg hcd hce hcg).commute
  have hγ2d : (Equiv.swap d e * Equiv.swap e g) d ≠ d :=
    Equiv.Perm.mem_support.mp (by rw [h2supp]; simp)
  have hne : ∀ k : ℕ, (Equiv.swap a b * Equiv.swap b c) ^ k ≠
      Equiv.swap d e * Equiv.swap e g :=
    s15k_tal_pow_ne h1supp hda hdb hdc hγ2d
  exact s15k_table_two_le_pRank hγ1mem hγ2mem
    (by rw [← hγ1three.orderOf]; exact pow_orderOf_eq_one _)
    (by rw [← hγ2three.orderOf]; exact pow_orderOf_eq_one _) hcomm hγ1three.ne_one hne

private lemma s15k_tal_two_le_of_two_sets {n : ℕ} (x : CFSG.Quasithin.G6.PermMod n)
    {S T : Finset (Fin n)} (hS : 3 ≤ S.card) (hT : 3 ≤ T.card)
    (hconstS : ∀ i ∈ S, ∀ k ∈ S, Multiplicative.toAdd x i = Multiplicative.toAdd x k)
    (hconstT : ∀ i ∈ T, ∀ k ∈ T, Multiplicative.toAdd x i = Multiplicative.toAdd x k)
    (hdisj : ∀ i ∈ S, i ∉ T) :
    2 ≤ pRank 3 (alternatingGroup (Fin n) ⊓ s15kPermStab n x) := by
  classical
  obtain ⟨a, b, c, haS, hbS, hcS, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < S.card)
  obtain ⟨d, e, g, hdT, heT, hgT, hde, hdg, heg⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < T.card)
  have had : a ≠ d := fun h => hdisj a haS (by rw [h]; exact hdT)
  have hae : a ≠ e := fun h => hdisj a haS (by rw [h]; exact heT)
  have hag : a ≠ g := fun h => hdisj a haS (by rw [h]; exact hgT)
  have hbd : b ≠ d := fun h => hdisj b hbS (by rw [h]; exact hdT)
  have hbe : b ≠ e := fun h => hdisj b hbS (by rw [h]; exact heT)
  have hbg : b ≠ g := fun h => hdisj b hbS (by rw [h]; exact hgT)
  have hcd : c ≠ d := fun h => hdisj c hcS (by rw [h]; exact hdT)
  have hce : c ≠ e := fun h => hdisj c hcS (by rw [h]; exact heT)
  have hcg : c ≠ g := fun h => hdisj c hcS (by rw [h]; exact hgT)
  have hda : d ≠ a := had.symm
  have hdb : d ≠ b := hbd.symm
  have hdc : d ≠ c := hcd.symm
  have h1supp : (Equiv.swap a b * Equiv.swap b c).support = {a, b, c} :=
    Equiv.Perm.support_swap_mul_swap (by simp [hab, hac, hbc])
  have h2supp : (Equiv.swap d e * Equiv.swap e g).support = {d, e, g} :=
    Equiv.Perm.support_swap_mul_swap (by simp [hde, hdg, heg])
  have hγ1three := s15k_tal_isThreeCycle hab hac hbc
  have hγ2three := s15k_tal_isThreeCycle hde hdg heg
  have hγ1mem := s15k_tal_threeCycle_mem x hconstS haS hbS hcS hab hac hbc
  have hγ2mem := s15k_tal_threeCycle_mem x hconstT hdT heT hgT hde hdg heg
  have hcomm : Commute (Equiv.swap a b * Equiv.swap b c)
      (Equiv.swap d e * Equiv.swap e g) :=
    (s15k_tal_disjoint_swap hab hac hbc hde hdg heg had hae hag hbd hbe hbg hcd hce hcg).commute
  have hγ2d : (Equiv.swap d e * Equiv.swap e g) d ≠ d :=
    Equiv.Perm.mem_support.mp (by rw [h2supp]; simp)
  have hne : ∀ k : ℕ, (Equiv.swap a b * Equiv.swap b c) ^ k ≠
      Equiv.swap d e * Equiv.swap e g :=
    s15k_tal_pow_ne h1supp hda hdb hdc hγ2d
  exact s15k_table_two_le_pRank hγ1mem hγ2mem
    (by rw [← hγ1three.orderOf]; exact pow_orderOf_eq_one _)
    (by rw [← hγ2three.orderOf]; exact pow_orderOf_eq_one _) hcomm hγ1three.ne_one hne

theorem s15k_table_alt_rank {n : ℕ} (hn : 5 ≤ n) (x : CFSG.Quasithin.G6.PermMod n) :
    1 ≤ pRank 3 (alternatingGroup (Fin n) ⊓ s15kPermStab n x) ∧
      (8 ≤ n → 2 ≤ pRank 3 (alternatingGroup (Fin n) ⊓ s15kPermStab n x)) := by
  classical
  set F0 : Finset (Fin n) :=
    Finset.univ.filter (fun i => Multiplicative.toAdd x i = 0) with hF0def
  set F1 : Finset (Fin n) :=
    Finset.univ.filter (fun i => ¬ Multiplicative.toAdd x i = 0) with hF1def
  have hF0 : ∀ i, i ∈ F0 ↔ Multiplicative.toAdd x i = 0 := by
    intro i; rw [hF0def]; simp
  have hF1 : ∀ i, i ∈ F1 ↔ Multiplicative.toAdd x i ≠ 0 := by
    intro i; rw [hF1def]; simp
  have hsum : F0.card + F1.card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i => Multiplicative.toAdd x i = 0)
    rw [hF0def, hF1def]
    simpa using h
  have hconst0 : ∀ i ∈ F0, ∀ k ∈ F0,
      Multiplicative.toAdd x i = Multiplicative.toAdd x k := by
    intro i hi k hk
    rw [(hF0 i).mp hi, (hF0 k).mp hk]
  have hconst1 : ∀ i ∈ F1, ∀ k ∈ F1,
      Multiplicative.toAdd x i = Multiplicative.toAdd x k := by
    intro i hi k hk
    have hi' : Multiplicative.toAdd x i ≠ 0 := (hF1 i).mp hi
    have hk' : Multiplicative.toAdd x k ≠ 0 := (hF1 k).mp hk
    rcases s15k_tal_zmod_two_cases (Multiplicative.toAdd x i) with h | h
    · exact absurd h hi'
    · rcases s15k_tal_zmod_two_cases (Multiplicative.toAdd x k) with h' | h'
      · exact absurd h' hk'
      · rw [h, h']
  have hone : 1 ≤ pRank 3 (alternatingGroup (Fin n) ⊓ s15kPermStab n x) := by
    have h3 : 3 ≤ F0.card ∨ 3 ≤ F1.card := by
      rcases lt_or_ge 2 F0.card with h | h
      · left; omega
      · right; omega
    rcases h3 with h3 | h3
    · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
        Finset.two_lt_card_iff.mp (by omega : 2 < F0.card)
      have h3c := s15k_tal_isThreeCycle hab hac hbc
      refine s15k_table_one_le_pRank (H := alternatingGroup (Fin n) ⊓ s15kPermStab n x)
        (s15k_tal_threeCycle_mem x hconst0 ha hb hc hab hac hbc) ?_ h3c.ne_one
      rw [← h3c.orderOf]
      exact pow_orderOf_eq_one _
    · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
        Finset.two_lt_card_iff.mp (by omega : 2 < F1.card)
      have h3c := s15k_tal_isThreeCycle hab hac hbc
      refine s15k_table_one_le_pRank (H := alternatingGroup (Fin n) ⊓ s15kPermStab n x)
        (s15k_tal_threeCycle_mem x hconst1 ha hb hc hab hac hbc) ?_ h3c.ne_one
      rw [← h3c.orderOf]
      exact pow_orderOf_eq_one _
  refine ⟨hone, ?_⟩
  intro hn8
  by_cases hbig : 6 ≤ F0.card ∨ 6 ≤ F1.card
  · rcases hbig with h6 | h6
    · exact s15k_tal_two_le_of_six x h6 hconst0
    · exact s15k_tal_two_le_of_six x h6 hconst1
  · have hlt0 : ¬ 6 ≤ F0.card := fun hh => hbig (Or.inl hh)
    have hlt1 : ¬ 6 ≤ F1.card := fun hh => hbig (Or.inr hh)
    have h0 : 3 ≤ F0.card := by omega
    have h1 : 3 ≤ F1.card := by omega
    exact s15k_tal_two_le_of_two_sets x h0 h1 hconst0 hconst1
      (fun i hi0 hi1 => (hF1 i).mp hi1 ((hF0 i).mp hi0))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
