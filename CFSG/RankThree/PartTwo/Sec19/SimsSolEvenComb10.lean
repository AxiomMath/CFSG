module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenBar

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

namespace Comb

variable {n : ℕ}

@[expose] def indV (I : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ I then 1 else 0

theorem indV_eq_one_iff {I : Finset (Fin n)} {i : Fin n} : indV I i = 1 ↔ i ∈ I := by
  by_cases h : i ∈ I <;> simp [indV, h]

theorem vecWt_indV (I : Finset (Fin n)) : vecWt (indV I) = I.card := by
  unfold vecWt
  congr 1
  ext i
  simp [indV_eq_one_iff]

theorem indV_compl (I : Finset (Fin n)) : indV Iᶜ = indV I + allOnes n := by
  funext i
  by_cases h : i ∈ I
  · simp only [indV, allOnes, Pi.add_apply, Finset.mem_compl, h, not_true_eq_false, if_false,
      if_true]
    decide
  · simp [indV, allOnes, h]

theorem exists_indV (x : Fin n → ZMod 2) : ∃ I, indV I = x :=
  ⟨Finset.univ.filter fun i => x i = 1, funext fun i => by
    rcases zmod_two_cases' (x i) with h | h <;> simp [indV, h]⟩

theorem indV_add_of_disjoint {I J : Finset (Fin n)} (h : Disjoint I J) :
    indV I + indV J = indV (I ∪ J) := by
  funext i
  by_cases hi : i ∈ I
  · have hj : i ∉ J := Finset.disjoint_left.1 h hi
    simp [indV, hi, hj]
  · by_cases hj : i ∈ J <;> simp [indV, hi, hj]

@[expose] noncomputable def barVec (I : Finset (Fin n)) : permBar n :=
  ((indV I : Fin n → ZMod 2) : permBar n)

theorem barVec_surjective : Function.Surjective (barVec (n := n)) := by
  intro v
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨I, rfl⟩ := exists_indV x
  exact ⟨I, rfl⟩

theorem allOnes_mk : ((allOnes n : Fin n → ZMod 2) : permBar n) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)

theorem barVec_compl (I : Finset (Fin n)) : barVec Iᶜ = barVec I := by
  unfold barVec
  rw [indV_compl, QuotientAddGroup.mk_add, allOnes_mk, add_zero]

theorem barVec_add_of_disjoint {I J : Finset (Fin n)} (h : Disjoint I J) :
    barVec I + barVec J = barVec (I ∪ J) := by
  unfold barVec
  rw [← QuotientAddGroup.mk_add, indV_add_of_disjoint h]

theorem indV_sub_apply_eq_zero_iff (I J : Finset (Fin n)) (k : Fin n) :
    (indV I - indV J) k = 0 ↔ (k ∈ I ↔ k ∈ J) := by
  by_cases h1 : k ∈ I <;> by_cases h2 : k ∈ J <;> simp [indV, h1, h2] <;> decide

theorem barVec_eq_barVec_iff {I J : Finset (Fin n)} : barVec I = barVec J ↔ I = J ∨ I = Jᶜ := by
  unfold barVec
  rw [QuotientAddGroup.eq_iff_sub_mem, mem_zmultiples_allOnes_iff]
  constructor
  · rintro (h | h)
    · left
      ext k
      exact (indV_sub_apply_eq_zero_iff I J k).1 (congrFun h k)
    · right
      ext k
      have h1 := congrFun h k
      have h2 := indV_sub_apply_eq_zero_iff I J k
      simp only [Pi.sub_apply, allOnes] at h1 h2
      rw [Finset.mem_compl]
      by_cases hk : k ∈ I <;> by_cases hk' : k ∈ J <;> simp_all [indV]
  · rintro (rfl | rfl)
    · left
      exact sub_self _
    · right
      funext k
      by_cases hk : k ∈ J <;> simp [indV, allOnes, hk]

theorem vecPerm_indV (σ : Perm (Fin n)) (I : Finset (Fin n)) :
    vecPerm σ (indV I) = indV (I.map σ.toEmbedding) := by
  funext i
  simp [vecPerm_apply, indV, Finset.mem_map_equiv, Perm.inv_def]

theorem barAct_barVec (σ : Perm (Fin n)) (I : Finset (Fin n)) :
    barAct σ (barVec I) = barVec (I.map σ.toEmbedding) := by
  unfold barVec
  rw [barAct_mk, vecPerm_indV]

theorem barLen_barVec (I : Finset (Fin n)) : barLen (barVec I) = min I.card (n - I.card) := by
  unfold barVec
  rw [barLen_mk, vecWt_indV]

theorem vecWt_vecPerm (σ : Perm (Fin n)) (x : Fin n → ZMod 2) :
    vecWt (vecPerm σ x) = vecWt x := by
  unfold vecWt
  refine Finset.card_equiv σ⁻¹ (fun i => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

theorem barLen_eq_iff {l : ℕ} (hl : 2 * l < n) {v : permBar n} :
    barLen v = l ↔ ∃ I : Finset (Fin n), I.card = l ∧ barVec I = v := by
  constructor
  · intro h
    obtain ⟨I, rfl⟩ := barVec_surjective v
    rw [barLen_barVec] at h
    have hI : I.card ≤ n := by simpa using Finset.card_le_univ I
    by_cases hc : I.card ≤ n - I.card
    · exact ⟨I, by omega, rfl⟩
    · refine ⟨Iᶜ, ?_, barVec_compl I⟩
      rw [Finset.card_compl, Fintype.card_fin]
      omega
  · rintro ⟨I, hI, rfl⟩
    rw [barLen_barVec, hI]
    omega

theorem eq_of_barVec_eq {l : ℕ} (hl : 2 * l < n) {I J : Finset (Fin n)} (hI : I.card = l)
    (hJ : J.card = l) (h : barVec I = barVec J) : I = J := by
  rcases barVec_eq_barVec_iff.1 h with h | h
  · exact h
  · exfalso
    have := congrArg Finset.card h
    rw [Finset.card_compl, Fintype.card_fin, hI, hJ] at this
    omega

theorem card_barLen {l : ℕ} (hl : 2 * l < n) :
    Nat.card {v : permBar n // barLen v = l} = n.choose l := by
  have e : {I : Finset (Fin n) // I.card = l} ≃ {v : permBar n // barLen v = l} :=
    Equiv.ofBijective
      (fun I => ⟨barVec I.1, by rw [barLen_eq_iff hl]; exact ⟨I.1, I.2, rfl⟩⟩)
      ⟨fun I J h => Subtype.ext (eq_of_barVec_eq hl I.2 J.2 (congrArg Subtype.val h)),
        fun v => by
          obtain ⟨I, hI, hv⟩ := (barLen_eq_iff hl).1 v.2
          exact ⟨⟨I, hI⟩, Subtype.ext hv⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

open scoped Pointwise in
theorem exists_alt_map_eq (hn : 3 ≤ n) {I J : Finset (Fin n)} (h : I.card = J.card) :
    ∃ σ ∈ alternatingGroup (Fin n), I.map σ.toEmbedding = J := by
  haveI : MulAction.IsPretransitive (alternatingGroup (Fin n))
      (Set.powersetCard (Fin n) I.card) :=
    Set.powersetCard.isPretransitive_alternatingGroup (by simpa using hn)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n))
    (⟨I, rfl⟩ : Set.powersetCard (Fin n) I.card) ⟨J, h.symm⟩
  refine ⟨g, g.2, ?_⟩
  have h2 : (g • (⟨I, rfl⟩ : Set.powersetCard (Fin n) I.card)).1 = g • I :=
    Set.powersetCard.coe_smul
  have h3 : (g • (⟨I, rfl⟩ : Set.powersetCard (Fin n) I.card)).1 = J := Subtype.ext_iff.1 hg
  rw [h2] at h3
  rw [← h3]
  ext x
  simp only [Finset.mem_map_equiv, Finset.mem_smul_finset, Subgroup.smul_def, Perm.smul_def]
  constructor
  · intro hx
    exact ⟨_, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem exists_alt_barAct_eq (hn : 3 ≤ n) {l : ℕ} (hl : 2 * l < n) {u v : permBar n}
    (hu : barLen u = l) (hv : barLen v = l) :
    ∃ σ ∈ alternatingGroup (Fin n), barAct σ u = v := by
  obtain ⟨I, hI, rfl⟩ := (barLen_eq_iff hl).1 hu
  obtain ⟨J, hJ, rfl⟩ := (barLen_eq_iff hl).1 hv
  obtain ⟨σ, hσ, hσI⟩ := exists_alt_map_eq hn (hI.trans hJ.symm)
  exact ⟨σ, hσ, by rw [barAct_barVec, hσI]⟩

theorem barLen_zero : barLen (0 : permBar n) = 0 := by
  have : (0 : permBar n) = (((0 : Fin n → ZMod 2)) : permBar n) := rfl
  rw [this, barLen_mk]
  simp [vecWt]

theorem card_pairs_fixed_swap {i j : Fin n} (hij : i ≠ j) :
    Fintype.card {I : Finset (Fin n) // I.card = 2 ∧ I.map (swap i j).toEmbedding = I} =
      1 + (n - 2).choose 2 := by
  classical
  rw [Fintype.card_subtype]
  have hS : (Finset.univ.filter fun I : Finset (Fin n) =>
      I.card = 2 ∧ I.map (swap i j).toEmbedding = I) =
      insert {i, j} ((Finset.univ \ {i, j}).powersetCard 2) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hc, hm⟩
      have hstab : ∀ x ∈ I, swap i j x ∈ I := fun x hx => by
        have : swap i j x ∈ I.map (swap i j).toEmbedding := Finset.mem_map_of_mem _ hx
        rwa [hm] at this
      by_cases hmeet : i ∈ I ∨ j ∈ I
      · left
        have hi : i ∈ I ∧ j ∈ I := by
          rcases hmeet with h | h
          · exact ⟨h, by simpa using hstab i h⟩
          · exact ⟨by simpa using hstab j h, h⟩
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hi.1
          · exact hi.2
        · rw [hc, Finset.card_pair hij]
      · right
        push Not at hmeet
        refine ⟨fun x hx => ?_, hc⟩
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          true_and, not_or]
        exact ⟨fun h => hmeet.1 (h ▸ hx), fun h => hmeet.2 (h ▸ hx)⟩
    · rintro (rfl | ⟨hsub, hc⟩)
      · refine ⟨Finset.card_pair hij, ?_⟩
        rw [Finset.map_insert, Finset.map_singleton]
        simp only [Equiv.coe_toEmbedding, swap_apply_left, swap_apply_right]
        exact Finset.pair_comm _ _
      · refine ⟨hc, ?_⟩
        ext x
        rw [Finset.mem_map_equiv, Equiv.symm_swap]
        by_cases hx : x = i ∨ x = j
        · have h1 : x ∉ I := fun h => by
            have := hsub h
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
              Finset.mem_singleton, true_and, not_or] at this
            rcases hx with rfl | rfl
            · exact this.1 rfl
            · exact this.2 rfl
          have h2 : swap i j x ∉ I := fun h => by
            have := hsub h
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
              Finset.mem_singleton, true_and, not_or] at this
            rcases hx with rfl | rfl
            · rw [swap_apply_left] at this
              exact this.2 rfl
            · rw [swap_apply_right] at this
              exact this.1 rfl
          simp [h1, h2]
        · push Not at hx
          rw [swap_apply_of_ne_of_ne hx.1 hx.2]
  have hnot : ({i, j} : Finset (Fin n)) ∉ (Finset.univ \ {i, j}).powersetCard 2 := by
    intro h
    have := (Finset.mem_powersetCard.1 h).1 (show i ∈ ({i, j} : Finset (Fin n)) by simp)
    simp at this
  rw [hS, Finset.card_insert_of_notMem hnot, Finset.card_powersetCard, Finset.card_univ_diff,
    Finset.card_pair hij, Fintype.card_fin]
  exact add_comm _ _

theorem zmod_two_sub_self (x : ZMod 2) : x - x = 0 := by
  revert x
  decide

@[expose] def barDiff (a b : Fin n) : permBar n →+ ZMod 2 :=
  QuotientAddGroup.lift _
    (Pi.evalAddMonoidHom (fun _ : Fin n => ZMod 2) a +
      Pi.evalAddMonoidHom (fun _ : Fin n => ZMod 2) b) (by
    intro z hz
    rw [AddMonoidHom.mem_ker]
    rcases (mem_zmultiples_allOnes_iff z).1 hz with rfl | rfl
    · simp
    · simp only [AddMonoidHom.add_apply, Pi.evalAddMonoidHom_apply, allOnes]
      decide)

theorem barDiff_mk (a b : Fin n) (x : Fin n → ZMod 2) :
    barDiff a b (x : permBar n) = x a + x b := rfl

theorem barDiff_barVec (a b : Fin n) (I : Finset (Fin n)) :
    barDiff a b (barVec I) = indV I a + indV I b := rfl

theorem barLen_eq_two_iff (hn : 4 < n) {v : permBar n} :
    barLen v = 2 ↔ ∃ a b : Fin n, a ≠ b ∧ v = barVec {a, b} := by
  rw [barLen_eq_iff (l := 2) (by omega)]
  constructor
  · rintro ⟨I, hI, rfl⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hI
    exact ⟨a, b, hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨{a, b}, Finset.card_pair hab, rfl⟩

theorem card_len_two_fixed_swap (hn : 4 < n) {i j : Fin n} (hij : i ≠ j) :
    Nat.card {v : permBar n // barLen v = 2 ∧ barAct (swap i j) v = v} =
      1 + (n - 2).choose 2 := by
  have e : {I : Finset (Fin n) // I.card = 2 ∧ I.map (swap i j).toEmbedding = I} ≃
      {v : permBar n // barLen v = 2 ∧ barAct (swap i j) v = v} :=
    Equiv.ofBijective
      (fun I => ⟨barVec I.1, by
        rw [barLen_barVec, I.2.1]
        exact ⟨by omega, by rw [barAct_barVec, I.2.2]⟩⟩)
      ⟨fun I J h => Subtype.ext (eq_of_barVec_eq (l := 2) (by omega) I.2.1 J.2.1
          (congrArg Subtype.val h)),
        fun v => by
          obtain ⟨I, hI, hv⟩ := (barLen_eq_iff (l := 2) (by omega)).1 v.2.1
          refine ⟨⟨I, hI, ?_⟩, Subtype.ext hv⟩
          refine eq_of_barVec_eq (l := 2) (by omega) (by rw [Finset.card_map, hI]) hI ?_
          rw [← barAct_barVec, hv]
          exact v.2.2⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, card_pairs_fixed_swap hij]

theorem card_le_four_of_len_two (hn : 8 ≤ n) (V : AddSubgroup (permBar n))
    (h : ∀ v ∈ V, v ≠ 0 → barLen v = 2) : Nat.card V ≤ 4 := by
  by_cases hV : ∀ v ∈ V, v = 0
  · have : Subsingleton V := ⟨fun a b => Subtype.ext ((hV a a.2).trans (hV b b.2).symm)⟩
    have h1 : Nat.card V ≤ 1 := Finite.card_le_one_iff_subsingleton.2 this
    omega
  · push Not at hV
    obtain ⟨v, hvV, hv0⟩ := hV
    obtain ⟨a, b, hab, hvab⟩ := (barLen_eq_two_iff (by omega)).1 (h v hvV hv0)
    obtain ⟨c, hca, hcb⟩ : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b} := fun p _ => by
        by_cases hpa : p = a
        · simp [hpa]
        · simp [hcon p hpa]
      have h1 := Finset.card_le_card hsub
      have h2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    let φ : V → ZMod 2 × ZMod 2 := fun u => (barDiff a b u, barDiff a c u)
    have hφ : Function.Injective φ := by
      intro u u' huu'
      have h1 : barDiff a b (u : permBar n) = barDiff a b (u' : permBar n) :=
        congrArg Prod.fst huu'
      have h2 : barDiff a c (u : permBar n) = barDiff a c (u' : permBar n) :=
        congrArg Prod.snd huu'
      have hwV : (u : permBar n) - u' ∈ V := V.sub_mem u.2 u'.2
      have hw1 : barDiff a b ((u : permBar n) - u') = 0 := by
        rw [map_sub, h1]
        exact zmod_two_sub_self _
      have hw2 : barDiff a c ((u : permBar n) - u') = 0 := by
        rw [map_sub, h2]
        exact zmod_two_sub_self _
      have hw0 : (u : permBar n) - u' = 0 := by
        by_contra hw0
        obtain ⟨K, hK, hwK⟩ := (barLen_eq_iff (l := 2) (by omega)).1 (h _ hwV hw0)
        rw [← hwK, barDiff_barVec] at hw1 hw2
        have hab' : (a ∈ K ↔ b ∈ K) := by
          by_cases ha : a ∈ K <;> by_cases hb : b ∈ K <;>
            simp_all [indV]
        have hac' : (a ∈ K ↔ c ∈ K) := by
          by_cases ha : a ∈ K <;> by_cases hc : c ∈ K <;>
            simp_all [indV]
        by_cases ha : a ∈ K
        · have hb : b ∈ K := hab'.1 ha
          have hc : c ∈ K := hac'.1 ha
          have hsub : ({a, b, c} : Finset (Fin n)) ⊆ K := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
          have h3 : ({a, b, c} : Finset (Fin n)).card = 3 :=
            Finset.card_eq_three.2 ⟨a, b, c, hab, hca.symm, hcb.symm, rfl⟩
          have := Finset.card_le_card hsub
          omega
        · have hb : b ∉ K := fun hb => ha (hab'.2 hb)
          have hdisj : Disjoint ({a, b} : Finset (Fin n)) K := by
            rw [Finset.disjoint_left]
            intro x hx hxK
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact ha hxK
            · exact hb hxK
          have hsum : v + ((u : permBar n) - (u' : permBar n)) = barVec ({a, b} ∪ K) := by
            rw [← hwK, hvab, barVec_add_of_disjoint hdisj]
          have hcard : ({a, b} ∪ K).card = 4 := by
            rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hab, hK]
          have hlen : barLen (v + ((u : permBar n) - (u' : permBar n))) = 4 := by
            rw [hsum, barLen_barVec, hcard]
            omega
          have hne : v + ((u : permBar n) - (u' : permBar n)) ≠ 0 := by
            intro h0
            rw [h0, barLen_zero] at hlen
            omega
          have := h _ (V.add_mem hvV hwV) hne
          omega
      exact Subtype.ext (sub_eq_zero.1 hw0)
    have := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_prod, Nat.card_zmod] at this

end Comb

theorem card_barLen_two : Nat.card {v : permBar 10 // barLen v = 2} = 45 := by
  rw [Comb.card_barLen (by norm_num)]
  decide

theorem card_barLen_four : Nat.card {v : permBar 10 // barLen v = 4} = 210 := by
  rw [Comb.card_barLen (by norm_num)]
  decide

theorem exists_alt_barAct_eq_of_barLen_two {u v : permBar 10} (hu : barLen u = 2)
    (hv : barLen v = 2) : ∃ σ ∈ alternatingGroup (Fin 10), barAct σ u = v :=
  Comb.exists_alt_barAct_eq (by norm_num) (by norm_num) hu hv

theorem exists_alt_barAct_eq_of_barLen_four {u v : permBar 10} (hu : barLen u = 4)
    (hv : barLen v = 4) : ∃ σ ∈ alternatingGroup (Fin 10), barAct σ u = v :=
  Comb.exists_alt_barAct_eq (by norm_num) (by norm_num) hu hv

theorem card_len_two_fixed_swap (i j : Fin 10) (hij : i ≠ j) :
    Nat.card {v : permBar 10 // barLen v = 2 ∧ barAct (swap i j) v = v} = 29 := by
  rw [Comb.card_len_two_fixed_swap (by norm_num) hij]
  decide

theorem barLen_barAct {n : ℕ} (σ : Perm (Fin n)) (v : permBar n) :
    barLen (barAct σ v) = barLen v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [barAct_mk, barLen_mk, barLen_mk, Comb.vecWt_vecPerm]

theorem card_le_four_of_len_two (V : AddSubgroup (permBar 10))
    (h : ∀ v ∈ V, v ≠ 0 → barLen v = 2) : Nat.card V ≤ 4 :=
  Comb.card_le_four_of_len_two (by norm_num) V h

namespace Comb

variable {n : ℕ}

theorem vecPerm_single (σ : Perm (Fin n)) (a : Fin n) :
    vecPerm σ (Pi.single a (1 : ZMod 2)) = Pi.single (σ a) 1 := by
  funext i
  rw [vecPerm_apply, Pi.single_apply, Pi.single_apply]
  simp only [Perm.inv_eq_iff_eq]

theorem zmod_two_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  revert a b
  decide

theorem zmod_two_neg_add_self_ne_one (t : ZMod 2) : -t + t ≠ 1 := by
  revert t
  decide

@[expose] def barPar (hn : Even n) : permBar n →+ ZMod 2 :=
  QuotientAddGroup.lift _
    { toFun := fun x => ∑ i, x i
      map_zero' := by simp
      map_add' := fun x y => by simp [Finset.sum_add_distrib] } (by
    intro z hz
    rw [AddMonoidHom.mem_ker]
    rcases (mem_zmultiples_allOnes_iff z).1 hz with rfl | rfl
    · simp
    · show ∑ i : Fin n, allOnes n i = 0
      simp only [allOnes, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      exact (ZMod.natCast_eq_zero_iff_even).2 hn)

theorem barPar_mk (hn : Even n) (x : Fin n → ZMod 2) :
    barPar hn (x : permBar n) = ∑ i, x i := rfl

theorem mem_range_heartToBar_iff (hn : Even n) (v : permBar n) :
    v ∈ (heartToBar : altHeart n →+ permBar n).range ↔ barPar hn v = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [heartToBar_mk] at hu
    rw [← hu]
    exact y.2
  · intro h
    exact ⟨((⟨x, h⟩ : evenWeight n) : altHeart n), rfl⟩

theorem barPar_barVec (hn : Even n) (I : Finset (Fin n)) :
    barPar hn (barVec I) = (I.card : ZMod 2) := by
  show ∑ i, indV I i = _
  simp [indV, Finset.sum_boole]

theorem barVec_mem_range_heartToBar (hn : Even n) {I : Finset (Fin n)} (hI : Even I.card) :
    barVec I ∈ (heartToBar : altHeart n →+ permBar n).range := by
  rw [mem_range_heartToBar_iff hn, barPar_barVec]
  exact (ZMod.natCast_eq_zero_iff_even).2 hI

theorem card_permBar (hn : 0 < n) : Nat.card (permBar n) = 2 ^ (n - 1) := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (AddSubgroup.zmultiples (allOnes n))
  have h2 : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    simp [Nat.card_fun]
  have h3a : (2 : ℕ) • allOnes n = 0 := by
    funext i
    show (2 : ℕ) • (1 : ZMod 2) = 0
    decide
  have h3b : allOnes n ≠ 0 := by
    intro h
    have h' : (1 : ZMod 2) = 0 := congrFun h ⟨0, hn⟩
    exact absurd h' (by decide)
  have h3 : Nat.card (AddSubgroup.zmultiples (allOnes n)) = 2 := by
    rw [Nat.card_zmultiples]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact addOrderOf_eq_prime h3a h3b
  rw [h2, h3] at h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ] at h1
  simp only [Nat.add_sub_cancel]
  have : Nat.card (permBar (m + 1)) * 2 = 2 ^ m * 2 := h1.symm
  omega

theorem barAct_mk_eq_self_iff {σ : Perm (Fin n)} {e : Fin n} (he : σ e = e)
    (x : Fin n → ZMod 2) :
    barAct σ (x : permBar n) = (x : permBar n) ↔ ∀ m, x m = x (σ m) := by
  rw [barAct_mk, QuotientAddGroup.eq]
  constructor
  · intro h
    rcases (mem_zmultiples_allOnes_iff _).1 h with h0 | h1
    · intro m
      have h' : vecPerm σ x = x := neg_add_eq_zero.1 h0
      have := congrFun h' (σ m)
      have h3 : σ⁻¹ (σ m) = m := by simp
      rw [vecPerm_apply, h3] at this
      exact this
    · exfalso
      have h2 := congrFun h1 e
      have hσ : σ⁻¹ e = e := by rw [Perm.inv_eq_iff_eq]; exact he.symm
      simp only [Pi.add_apply, Pi.neg_apply, vecPerm_apply, hσ, allOnes] at h2
      exact zmod_two_neg_add_self_ne_one _ h2
  · intro h
    have h' : vecPerm σ x = x := funext fun i => by
      rw [vecPerm_apply]
      have := h (σ⁻¹ i)
      have h3 : σ (σ⁻¹ i) = i := by simp
      rw [h3] at this
      exact this
    rw [h', neg_add_cancel]
    exact zero_mem _

theorem fixed_swap_iff {i j e : Fin n} (hei : e ≠ i) (hej : e ≠ j) (x : Fin n → ZMod 2) :
    barAct (swap i j) (x : permBar n) = (x : permBar n) ↔ x i = x j := by
  rw [barAct_mk_eq_self_iff (e := e) (swap_apply_of_ne_of_ne hei hej)]
  constructor
  · intro h
    have := h i
    rwa [swap_apply_left] at this
  · intro h m
    by_cases hmi : m = i
    · rw [hmi, swap_apply_left]
      exact h
    · by_cases hmj : m = j
      · rw [hmj, swap_apply_right]
        exact h.symm
      · rw [swap_apply_of_ne_of_ne hmi hmj]

@[expose] def fixSub (F : Set (Perm (Fin n))) : AddSubgroup (permBar n) where
  carrier := {v | ∀ σ ∈ F, barAct σ v = v}
  zero_mem' := fun σ _ => map_zero _
  add_mem' := fun {a b} ha hb σ hσ => by rw [map_add, ha σ hσ, hb σ hσ]
  neg_mem' := fun {a} ha σ hσ => by rw [map_neg, ha σ hσ]

theorem mem_fixSub {F : Set (Perm (Fin n))} {v : permBar n} :
    v ∈ fixSub F ↔ ∀ σ ∈ F, barAct σ v = v := Iff.rfl

theorem card_ker_pow {B : Type*} [AddGroup B] {k : ℕ} (hn : 0 < n) (φ : permBar n →+ B)
    (hφ : Function.Surjective φ) (hB : Nat.card B = 2 ^ k) (hk : k ≤ n - 1) :
    Nat.card φ.ker = 2 ^ (n - 1 - k) := by
  have h1 := AddSubgroup.card_ker_mul_card_of_surjective hφ
  rw [hB, card_permBar hn] at h1
  have h2 : 2 ^ (n - 1) = 2 ^ (n - 1 - k) * 2 ^ k := by
    rw [← pow_add]
    congr 1
    omega
  have h3 : 0 < 2 ^ k := by positivity
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right h3 h1

theorem card_fixSub_swap (hn : 5 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    Nat.card ↥(fixSub {swap i j}) = 2 ^ (n - 2) := by
  have hker : fixSub {swap i j} = (barDiff i j).ker := by
    ext v
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
    obtain ⟨e, hei, hej, -, -⟩ := exists_ne_four hn i j i j
    rw [mem_fixSub, AddMonoidHom.mem_ker, barDiff_mk, zmod_two_add_eq_zero_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact fixed_swap_iff hei hej x
  have hsurj : Function.Surjective (barDiff i j) := fun t =>
    ⟨((Pi.single i t : Fin n → ZMod 2) : permBar n), by
      rw [barDiff_mk]
      simp [Pi.single_apply, hij.symm]⟩
  rw [hker]
  have h := card_ker_pow (k := 1) (by omega) (barDiff i j) hsurj (by simp [Nat.card_zmod])
    (by omega)
  rwa [show n - 1 - 1 = n - 2 by omega] at h

end Comb

namespace Comb

variable {n : ℕ}

@[expose] noncomputable def bp (x y : Fin n) : permBar n :=
  ((Pi.single x (1 : ZMod 2) + Pi.single y (1 : ZMod 2) : Fin n → ZMod 2) : permBar n)

theorem barAct_bp (σ : Perm (Fin n)) (x y : Fin n) : barAct σ (bp x y) = bp (σ x) (σ y) := by
  unfold bp
  rw [barAct_mk, map_add, vecPerm_single, vecPerm_single]

@[expose] def dv (p q r s : Fin n) : Fin n → ZMod 2 :=
  Pi.single p 1 + Pi.single q 1 - (Pi.single r 1 + Pi.single s 1)

theorem dv_apply (p q r s k : Fin n) :
    dv p q r s k = ((if k = p then 1 else 0) + (if k = q then 1 else 0)) -
      ((if k = r then 1 else 0) + (if k = s then 1 else 0)) := by
  simp [dv, Pi.single_apply]

theorem bp_sub_bp (p q r s : Fin n) : bp p q - bp r s = ((dv p q r s : Fin n → ZMod 2) : permBar n) := by
  unfold bp dv
  rw [QuotientAddGroup.mk_sub]

theorem mk_ne_zero_of_coords {w : Fin n → ZMod 2} {i j : Fin n} (hi : w i = 1) (hj : w j = 0) :
    (w : permBar n) ≠ 0 := by
  intro h
  rcases (mem_zmultiples_allOnes_iff w).1 ((QuotientAddGroup.eq_zero_iff w).1 h) with h0 | h1
  · rw [h0] at hi
    exact absurd hi (by show ¬ (0 : ZMod 2) = 1; decide)
  · rw [h1] at hj
    exact absurd hj (by show ¬ (1 : ZMod 2) = 0; decide)

theorem mk_ne_mk_of_coords {w w' : Fin n → ZMod 2} {i j : Fin n} (hi : w i ≠ w' i)
    (hj : w j = w' j) : (w : permBar n) ≠ (w' : permBar n) := by
  intro h
  rw [QuotientAddGroup.eq_iff_sub_mem, mem_zmultiples_allOnes_iff] at h
  rcases h with h0 | h1
  · exact hi (sub_eq_zero.1 (congrFun h0 i))
  · have h2 := congrFun h1 j
    rw [Pi.sub_apply, hj] at h2
    have h3 : w' j - w' j = 0 := zmod_two_sub_self _
    rw [h3] at h2
    exact absurd h2 (by show ¬ (0 : ZMod 2) = 1; decide)

theorem barAct_bp_sub (σ : Perm (Fin n)) (x y : Fin n) :
    barAct σ (bp x y) - bp x y = ((dv (σ x) (σ y) x y : Fin n → ZMod 2) : permBar n) := by
  rw [barAct_bp, bp_sub_bp]

theorem exists_two_values (hn : 5 ≤ n) {σ : Perm (Fin n)} (h1 : σ ≠ 1) (hs : ¬ σ.IsSwap) :
    ∃ x₁ y₁ x₂ y₂ : Fin n, barAct σ (bp x₁ y₁) - bp x₁ y₁ ≠ 0 ∧
      barAct σ (bp x₂ y₂) - bp x₂ y₂ ≠ 0 ∧
      barAct σ (bp x₁ y₁) - bp x₁ y₁ ≠ barAct σ (bp x₂ y₂) - bp x₂ y₂ := by
  by_cases hA : ∃ a, σ (σ a) ≠ a
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ : ∃ b, σ a = b := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, σ b = c := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, σ c = d := ⟨_, rfl⟩
    have hca : c ≠ a := by rw [← hc, ← hb]; exact ha
    have hab : a ≠ b := fun h => ha (by
      have : σ a = a := hb.trans h.symm
      rw [this, this])
    have hbc : b ≠ c := fun h => hab (σ.injective (by rw [hb, hc]; exact h))
    have hcd : c ≠ d := fun h => hbc (σ.injective (by rw [hc, hd]; exact h))
    have hbd : b ≠ d := fun h => hca (σ.injective (by rw [hd, hb]; exact h.symm))
    obtain ⟨e, hea, heb, hec, hed⟩ := exists_ne_four hn a b c d
    have hba := hab.symm
    have hcb := hbc.symm
    have hac := hca.symm
    have hdc := hcd.symm
    have hdb := hbd.symm
    refine ⟨a, b, b, c, ?_, ?_, ?_⟩
    · rw [barAct_bp_sub, hb, hc]
      refine mk_ne_zero_of_coords (i := a) (j := b) ?_ ?_
      · simp [dv_apply, hab, hba, hac, hca, hbc, hcb] <;> decide
      · simp [dv_apply, hab, hba, hac, hca, hbc, hcb] <;> decide
    · rw [barAct_bp_sub, hc, hd]
      refine mk_ne_zero_of_coords (i := b) (j := c) ?_ ?_
      · simp [dv_apply, hbc, hcb, hbd, hdb, hcd, hdc] <;> decide
      · simp [dv_apply, hbc, hcb, hbd, hdb, hcd, hdc] <;> decide
    · rw [barAct_bp_sub, barAct_bp_sub, hb, hc, hd]
      refine mk_ne_mk_of_coords (i := c) (j := e) ?_ ?_
      · simp [dv_apply, hab, hba, hac, hca, hbc, hcb, hcd, hdc, hbd, hdb] <;> decide
      · simp [dv_apply, hea, heb, hec, hed]
  · push Not at hA
    obtain ⟨a, haa⟩ : ∃ a, σ a ≠ a := by
      by_contra h
      push Not at h
      exact h1 (Equiv.ext h)
    obtain ⟨b, hb⟩ : ∃ b, σ a = b := ⟨_, rfl⟩
    have hba : σ b = a := by rw [← hb]; exact hA a
    have hab : a ≠ b := fun h => haa (hb.trans h.symm)
    obtain ⟨z, hza, hzb, hzz⟩ : ∃ z, z ≠ a ∧ z ≠ b ∧ σ z ≠ z := by
      by_contra h
      push Not at h
      apply hs
      refine ⟨a, b, hab, Equiv.ext fun x => ?_⟩
      by_cases hxa : x = a
      · rw [hxa, swap_apply_left, hb]
      by_cases hxb : x = b
      · rw [hxb, swap_apply_right, hba]
      · rw [swap_apply_of_ne_of_ne hxa hxb]
        exact h x hxa hxb
    obtain ⟨w, hw⟩ : ∃ w, σ z = w := ⟨_, rfl⟩
    have hwz : σ w = z := by rw [← hw]; exact hA z
    have hwa : w ≠ a := fun h => hzb (σ.injective (by rw [hw, hba]; exact h))
    have hwb : w ≠ b := fun h => hza (σ.injective (by rw [hw, hb]; exact h))
    have hzw : z ≠ w := fun h => hzz (hw.trans h.symm)
    obtain ⟨p, hpa, hpb, hpz, hpw⟩ := exists_ne_four hn a b z w
    obtain ⟨q, hq⟩ : ∃ q, σ p = q := ⟨_, rfl⟩
    have hqp : σ q = p := by rw [← hq]; exact hA p
    have hqa : q ≠ a := fun h => hpb (by rw [← hqp, h, hb])
    have hqb : q ≠ b := fun h => hpa (by rw [← hqp, h, hba])
    have hqz : q ≠ z := fun h => hpw (by rw [← hqp, h, hw])
    have hqw : q ≠ w := fun h => hpz (by rw [← hqp, h, hwz])
    have hba := hab.symm
    have haz := hza.symm
    have hbz := hzb.symm
    have hwz' := hzw.symm
    have haw := hwa.symm
    have hbw := hwb.symm
    have hap := hpa.symm
    have hbp := hpb.symm
    have hzp := hpz.symm
    have hwp := hpw.symm
    have haq := hqa.symm
    have hbq := hqb.symm
    have hzq := hqz.symm
    have hwq := hqw.symm
    refine ⟨a, z, a, p, ?_, ?_, ?_⟩
    · rw [barAct_bp_sub, hb, hw]
      refine mk_ne_zero_of_coords (i := a) (j := p) ?_ ?_
      · simp [dv_apply, hab, hba, haw, hwa, haz, hza] <;> decide
      · simp [dv_apply, hpa, hpb, hpz, hpw, hap, hbp, hzp, hwp] <;> decide
    · rw [barAct_bp_sub, hb, hq]
      refine mk_ne_zero_of_coords (i := a) (j := z) ?_ ?_
      · simp [dv_apply, hab, hba, haq, hqa, hap, hpa] <;> decide
      · simp [dv_apply, hza, haz, hzb, hbz, hzq, hqz, hzp, hpz] <;> decide
    · rw [barAct_bp_sub, barAct_bp_sub, hb, hw, hq]
      refine mk_ne_mk_of_coords (i := z) (j := a) ?_ ?_
      · simp [dv_apply, hza, haz, hzb, hbz, hzw, hwz', hzq, hqz, hzp, hpz] <;> decide
      · simp [dv_apply, hab, hba, haw, hwa, haz, hza, haq, hqa, hap, hpa]

@[expose] noncomputable def pc (x y : Fin n) : altHeart n :=
  ((pairEW x y : evenWeight n) : altHeart n)

theorem heartToBar_pc (x y : Fin n) : heartToBar (pc x y) = bp x y := by
  rw [pc, heartToBar_mk]
  unfold bp
  congr 1
  funext p
  rw [pairEW_apply, Pi.add_apply, Pi.single_apply, Pi.single_apply]

theorem heartToBar_commutator (σ : Perm (Fin n)) (x y : Fin n) :
    heartToBar (altAct σ (pc x y) - pc x y) = barAct σ (bp x y) - bp x y := by
  rw [map_sub, heartToBar_altAct, heartToBar_pc]

theorem exists_two_values_alt (hn : 5 ≤ n) {σ : Perm (Fin n)} (h1 : σ ≠ 1) (hs : ¬ σ.IsSwap) :
    ∃ u₁ u₂ : altHeart n, altAct σ u₁ - u₁ ≠ 0 ∧ altAct σ u₂ - u₂ ≠ 0 ∧
      altAct σ u₁ - u₁ ≠ altAct σ u₂ - u₂ := by
  obtain ⟨x₁, y₁, x₂, y₂, h1', h2', h12⟩ := exists_two_values hn h1 hs
  refine ⟨pc x₁ y₁, pc x₂ y₂, ?_, ?_, ?_⟩
  · intro h
    apply h1'
    have := congrArg (heartToBar : altHeart n →+ permBar n) h
    rwa [heartToBar_commutator, map_zero] at this
  · intro h
    apply h2'
    have := congrArg (heartToBar : altHeart n →+ permBar n) h
    rwa [heartToBar_commutator, map_zero] at this
  · intro h
    apply h12
    have := congrArg (heartToBar : altHeart n →+ permBar n) h
    rwa [heartToBar_commutator, heartToBar_commutator] at this

theorem eq_one_or_isSwap_of_commutator_eq (hn : 5 ≤ n) {σ : Perm (Fin n)}
    (h : ∀ u v : altHeart n, altAct σ u - u ≠ 0 → altAct σ v - v ≠ 0 →
      altAct σ u - u = altAct σ v - v) : σ = 1 ∨ σ.IsSwap := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₁, u₂, h1, h2, h12⟩ := exists_two_values_alt hn hcon.1 hcon.2
  exact h12 (h u₁ u₂ h1 h2)

end Comb

end CFSG.RankThree.PartTwo.Sec19.SolEven
