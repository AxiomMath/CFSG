module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent.Defs
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofEightG2
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofExcSpor
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow
public import CFSG.CGT.PushingUpLit.Glue.BlockInX
public import CFSG.RankThree.PartTwo.KFacts.KP4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec11

theorem not_hasType424_of_isSolvable {H : Type} [Group H] [Finite H] (h : Group.IsSolvable H) :
    ¬ Sec11.KS11Lie2Proof.HasType424 H := by
  rintro ⟨L, hL, hT⟩
  rcases hL with ⟨hP, -, -⟩
  have hL0 : L = ⊥ := GroupTheory.eq_bot_of_isPerfect_of_isSolvable hP inferInstance
  subst hL0
  have h3 := KS11LieProof.three_dvd_card_of_isType424 hT
  have h1 : Nat.card ((⊥ : Subgroup H) ⧸ aschbacherSolvableCore 3 (⊥ : Subgroup H)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  omega

theorem noType424At3_of_isSolvable_centralizer {S : Type} [Group S] [Finite S]
    (h : ∀ s : S, orderOf s = 3 → Group.IsSolvable (Subgroup.centralizer ({s} : Set S))) :
    Coordinator.CoverCent.NoType424At3 S := by
  intro s hs
  rw [Item424Res2.fixSub_conj_eq_centralizer_singleton]
  exact not_hasType424_of_isSolvable (h s hs)

theorem aschbacherSolvableCore_eq_bot_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hns : ¬ Group.IsSolvable X) : aschbacherSolvableCore 3 X = ⊥ := by
  have hR : CFSG.solvableRadical X = ⊥ := by
    refine le_bot_iff.mp (sSup_le ?_)
    rintro N ⟨hN, hsol⟩
    have := hN
    rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
    · exact le_of_eq h
    · exfalso
      apply hns
      rw [h] at hsol
      exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup X).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  unfold aschbacherSolvableCore inSubgroup
  rw [hR]
  rw [eq_bot_iff]
  rintro _ ⟨y, -, rfl⟩
  have : y = 1 := Subsingleton.elim _ _
  simp [this]

theorem not_isType424_quot_of_subsingleton {X : Type} [Group X] [Subsingleton X] :
    ¬ IsType424 (X ⧸ aschbacherSolvableCore 3 X) := fun h => by
  have h3 := KS11LieProof.three_dvd_card_of_isType424 h
  have h1 : Nat.card (X ⧸ aschbacherSolvableCore 3 X) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  omega

theorem not_hasType424_of_normal_simple {C : Type} [Group C] [Finite C] (E : Subgroup C)
    [E.Normal] [IsSimpleGroup E] (hE : ¬ Group.IsSolvable E) (hq : Group.IsSolvable (C ⧸ E))
    (hT : ¬ IsType424 E) : ¬ Sec11.KS11Lie2Proof.HasType424 C := by
  rintro ⟨L, hL, hT'⟩
  rcases hL with ⟨hP, hsn, -⟩
  have := hP
  have := hq
  have hmapP : Group.IsPerfect (L.map (QuotientGroup.mk' E)) := Group.IsPerfect.map (QuotientGroup.mk' E)
  have hmapbot : L.map (QuotientGroup.mk' E) = ⊥ :=
    GroupTheory.eq_bot_of_isPerfect_of_isSolvable hmapP inferInstance
  have hLE : L ≤ E := by
    intro x hx
    have hmem : (QuotientGroup.mk' E x) ∈ L.map (QuotientGroup.mk' E) := Subgroup.mem_map_of_mem _ hx
    rw [hmapbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance
      (Subgroup.IsSubnormal.subgroupOf (K := E) hsn) with h | h
  · have hdisj : Disjoint L E := Subgroup.subgroupOf_eq_bot.mp h
    have hLbot : L = ⊥ := by
      have h1 := inf_eq_left.mpr hLE
      rw [disjoint_iff.mp hdisj] at h1
      exact h1.symm
    subst hLbot
    exact not_isType424_quot_of_subsingleton hT'
  · have hEL : E ≤ L := Subgroup.subgroupOf_eq_top.mp h
    have hLE' : L = E := le_antisymm hLE hEL
    subst hLE'
    have hcore := aschbacherSolvableCore_eq_bot_of_simple hE
    exact hT (isType424_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm) hT')

set_option maxRecDepth 100000 in
theorem perm_six_pow_nine_imp_pow_three :
    ∀ g : Equiv.Perm (Fin 6), g ^ 9 = 1 → g ^ 3 = 1 := by
  decide

theorem alt_six_orderOf_ne_nine (g : alternatingGroup (Fin 6)) : orderOf g ≠ 9 := by
  intro h
  have hg9 : g ^ 9 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one g
  have hperm9 : (g : Equiv.Perm (Fin 6)) ^ 9 = 1 := by
    rw [← Subgroup.coe_pow, hg9, Subgroup.coe_one]
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, perm_six_pow_nine_imp_pow_three _ hperm9, Subgroup.coe_one]
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [h] at hdvd
  omega

theorem nat_card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem alt_six_sylow_three_card (P : Sylow 3 (alternatingGroup (Fin 6))) : Nat.card P = 9 := by
  rw [Sylow.card_eq_multiplicity, nat_card_alt_six]
  have hf : Nat.factorization 360 3 = 2 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.factorization_def _ Nat.prime_three,
      show (360 : ℕ) = 3 ^ 2 * 40 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [hf]
  norm_num

theorem alt_six_sylow_three_not_cyclic (P : Sylow 3 (alternatingGroup (Fin 6))) :
    ¬ IsCyclic P := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  rw [alt_six_sylow_three_card P] at hg
  have hA : orderOf (g : alternatingGroup (Fin 6)) = 9 := by
    rw [Subgroup.orderOf_coe]
    exact hg
  exact alt_six_orderOf_ne_nine _ hA

theorem not_isType424_alt_six : ¬ IsType424 (alternatingGroup (Fin 6)) := by
  intro hT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : CFSG.IsQuasisimple (alternatingGroup (Fin 6)) :=
    CFSG.CGT.PushingUpLit.Glue.isQuasisimple_alternating (by norm_num)
  obtain P : Sylow 3 (alternatingGroup (Fin 6)) := Sylow.nonempty.some
  exact alt_six_sylow_three_not_cyclic P (KS11LieProof.isCyclic_sylow_three_of_isType424 hT hQ P)

theorem noType424At3_M22 :
    Coordinator.CoverCent.NoType424At3 (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  have hfin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
    unfold CFSG.Blueprint.NativeSporadic.Carrier
    infer_instance
  refine noType424At3_of_isSolvable_centralizer ?_
  intro s hs
  have hcard := (CFSG.RankThree.PartTwo.KFacts.KP4.m22_centralizer_facts_of_orderOf
    (L := CFSG.Blueprint.NativeSporadic.Carrier .M22) (a := s) ⟨MulEquiv.refl _⟩ hs).1
  have := Fintype.ofFinite (Subgroup.centralizer ({s} : Set (CFSG.Blueprint.NativeSporadic.Carrier .M22)))
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 2) (b := 2) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)

theorem two_le_sum_of_mem_two {m : Multiset ℕ} {a b : ℕ} (ha : a ∈ m) (hb : b ∈ m)
    (hab : a ≠ b) : a + b ≤ m.sum := by
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hb' : b ∈ s := (Multiset.mem_cons.1 hb).resolve_left (Ne.symm hab)
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hb'
  simp only [Multiset.sum_cons]
  omega

theorem perm_le_seven_orderOf_ne_three_mul {k : ℕ} (hk : k ≤ 7) (σ : Equiv.Perm (Fin k)) {p : ℕ}
    (hpr : p = 5 ∨ p = 7) (h : orderOf σ = 3 * p) : False := by
  have hl := Equiv.Perm.lcm_cycleType σ
  have hs := Equiv.Perm.sum_cycleType_le σ
  rw [Fintype.card_fin] at hs
  rw [h] at hl
  have hmem : ∀ x ∈ σ.cycleType, x = 3 ∨ x = p := by
    intro x hx
    have h1 : x ∣ 3 * p := hl ▸ Multiset.dvd_lcm hx
    have h2 : x ≤ 7 := (Multiset.le_sum_of_mem hx).trans (hs.trans hk)
    have h3 := σ.two_le_of_mem_cycleType hx
    rcases hpr with rfl | rfl <;> interval_cases x <;>
      first
      | (left; rfl)
      | (right; rfl)
      | (exfalso; norm_num at h1)
  have hp_in : p ∈ σ.cycleType := by
    by_contra hn
    have hdv : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.2 fun x hx => by
      rcases hmem x hx with rfl | rfl
      · exact dvd_rfl
      · exact absurd hx hn
    rw [hl] at hdv
    rcases hpr with rfl | rfl <;> norm_num at hdv
  have h3_in : 3 ∈ σ.cycleType := by
    by_contra hn
    have hdv : σ.cycleType.lcm ∣ p := Multiset.lcm_dvd.2 fun x hx => by
      rcases hmem x hx with rfl | rfl
      · exact absurd hx hn
      · exact dvd_rfl
    rw [hl] at hdv
    have hp0 : 0 < p := by rcases hpr with rfl | rfl <;> norm_num
    have := Nat.le_of_dvd hp0 hdv
    omega
  have hne : 3 ≠ p := by rcases hpr with rfl | rfl <;> norm_num
  have hsum := two_le_sum_of_mem_two h3_in hp_in hne
  omega

theorem alt_le_seven_orderOf_ne_three_mul {n : ℕ} (hn : n ≤ 7) (x : alternatingGroup (Fin n))
    {p : ℕ} (hpr : p = 5 ∨ p = 7) (h : orderOf x = 3 * p) : False :=
  perm_le_seven_orderOf_ne_three_mul hn (x : Equiv.Perm (Fin n)) hpr ((Subgroup.orderOf_coe x).trans h)

theorem isSolvable_centralizer_alt_of_orderOf_three {n : ℕ} (hn : n ≤ 7)
    (s : alternatingGroup (Fin n)) (hs : orderOf s = 3) :
    Group.IsSolvable (Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n)))) := by
  have hperm : Nat.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hdvd7 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial 7 := by
    refine (Subgroup.card_subgroup_dvd_card _).trans ?_
    rw [hperm]
    exact Nat.factorial_dvd_factorial hn
  have h7fac : Nat.factorial 7 = 2 ^ 4 * 3 ^ 2 * (5 * 7) := by norm_num [Nat.factorial]
  have hdvdC : Nat.card (Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n)))) ∣
      2 ^ 4 * 3 ^ 2 * (5 * 7) := by
    rw [← h7fac]
    exact (Subgroup.card_subgroup_dvd_card _).trans hdvd7
  have h5 : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n)))) := by
    intro hd5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n))))) 5 hd5
    have hot : orderOf (t : alternatingGroup (Fin n)) = 5 := by
      rw [Subgroup.orderOf_coe]
      exact ht
    have hcomm : Commute s (t : alternatingGroup (Fin n)) := by
      have ht' := t.2
      rw [Subgroup.mem_centralizer_iff] at ht'
      exact ht' s (Set.mem_singleton s)
    have hco : (orderOf s).Coprime (orderOf (t : alternatingGroup (Fin n))) := by
      rw [hs, hot]
      norm_num
    exact alt_le_seven_orderOf_ne_three_mul hn (s * (t : alternatingGroup (Fin n))) (p := 5)
      (Or.inl rfl) (by rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hs, hot])
  have h7 : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n)))) := by
    intro hd7
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n))))) 7 hd7
    have hot : orderOf (t : alternatingGroup (Fin n)) = 7 := by
      rw [Subgroup.orderOf_coe]
      exact ht
    have hcomm : Commute s (t : alternatingGroup (Fin n)) := by
      have ht' := t.2
      rw [Subgroup.mem_centralizer_iff] at ht'
      exact ht' s (Set.mem_singleton s)
    have hco : (orderOf s).Coprime (orderOf (t : alternatingGroup (Fin n))) := by
      rw [hs, hot]
      norm_num
    exact alt_le_seven_orderOf_ne_three_mul hn (s * (t : alternatingGroup (Fin n))) (p := 7)
      (Or.inr rfl) (by rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hs, hot])
  have hcop : Nat.Coprime (Nat.card (Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n)))))
      (5 * 7) :=
    Nat.Coprime.mul_right
      ((Nat.prime_five.coprime_iff_not_dvd.2 h5).symm)
      (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.2 h7).symm)
  have hdiv : Nat.card (Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n)))) ∣
      2 ^ 4 * 3 ^ 2 := hcop.dvd_of_dvd_mul_right hdvdC
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 hdiv
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype (Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n)))) :=
    Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := i) (b := j) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card]; exact hk.symm)

theorem noType424At3_alt {n : ℕ} (hn : n ≤ 7) :
    Coordinator.CoverCent.NoType424At3 (alternatingGroup (Fin n)) :=
  noType424At3_of_isSolvable_centralizer fun s hs =>
    isSolvable_centralizer_alt_of_orderOf_three hn s hs

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
