module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightBar
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4b

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Eight

section Pairs

variable {n : ℕ}

theorem uvec_moved (hn : 5 ≤ n) {σ : Perm (Fin n)} {x y : Fin n} (hxy : x ≠ y) (h1 : σ x ≠ x)
    (h2 : σ x ≠ y) : barAct σ (uvec x y) ≠ uvec x y := by
  rw [barAct_uvec]
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ := exists_ne_four hn (σ x) (σ y) x y
  have hσxy : σ x ≠ σ y := fun h => hxy (σ.injective h)
  unfold uvec
  refine bar_mk_ne_of_coords (i := σ x) (j := j) ?_ ?_
  · simp only [Pi.add_apply, Pi.single_apply, if_true, hσxy, h1, h2, if_false]
    decide
  · simp only [Pi.add_apply, Pi.single_apply, hj1, hj2, hj3, hj4, if_false]

theorem barAct_uvec_ne_of_fourGroup (hn : 5 ≤ n) {I : Finset (Fin n)}
    {N : Subgroup (Perm (Fin n))} (h : FourGroup I N) (hI : I.card = 4) {σ σ' : Perm (Fin n)}
    (hσ : σ ∈ N) (hσ1 : σ ≠ 1) (hσ' : σ' ∈ N) (hσ'1 : σ' ≠ 1) (hne : σ ≠ σ') {a : Fin n}
    (ha : a ∈ I) : barAct σ (uvec a (σ' a)) ≠ uvec a (σ' a) :=
  uvec_moved hn (fun h' => h.free hI hσ' hσ'1 a ha h'.symm) (h.free hI hσ hσ1 a ha)
    (h.apart hI hσ hσ' hne ha)

theorem uvec_self (a : Fin n) : uvec a a = 0 := by
  unfold uvec
  have : (Pi.single a (1 : ZMod 2) + Pi.single a 1 : Fin n → ZMod 2) = 0 := by
    funext m
    by_cases hm : m = a
    · subst hm
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply]
      decide
    · simp [Pi.single_apply, hm]
  rw [this]
  rfl

theorem uvec_comm (a b : Fin n) : uvec a b = uvec b a := by
  unfold uvec
  rw [add_comm]

theorem uvec_add_uvec (a b p : Fin n) : uvec a p + uvec b p = uvec a b := by
  have h := neg_uvec_add_uvec a b p
  rwa [permBar_neg_eq] at h

theorem uvec_mem_qbar0 {I : Finset (Fin n)} (hI : Even I.card) (hIc : Even Iᶜ.card)
    {J : Finset (Fin n)} (hJ : J = I ∨ J = Iᶜ) {a b : Fin n} (ha : a ∈ J) (hb : b ∈ J) :
    uvec a b ∈ qbar0 I := by
  unfold uvec
  rw [mem_qbar0_mk hI hIc]
  have key : ∀ S : Finset (Fin n), (a ∈ S ↔ b ∈ S) →
      ∑ i ∈ S, ((Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2) : Fin n → ZMod 2) i) = 0 := by
    intro S hS
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    by_cases haS : a ∈ S
    · rw [if_pos haS, if_pos (hS.1 haS)]
      decide
    · rw [if_neg haS, if_neg (fun h => haS (hS.2 h)), add_zero]
  have hab : ∀ S : Finset (Fin n), (S = I ∨ S = Iᶜ) → (a ∈ S ↔ b ∈ S) := by
    intro S hS
    rcases hJ with rfl | rfl <;> rcases hS with rfl | rfl
    · exact iff_of_true ha hb
    · simp only [Finset.mem_compl]
      exact iff_of_false (not_not.2 ha) (not_not.2 hb)
    · simp only [Finset.mem_compl] at ha hb
      exact iff_of_false ha hb
    · exact iff_of_true ha hb
  exact ⟨key I (hab I (Or.inl rfl)), key Iᶜ (hab Iᶜ (Or.inr rfl))⟩

theorem qbar0_le_of_pairs {I : Finset (Fin n)} (hI : Even I.card) (hIc : Even Iᶜ.card)
    (hIne : I.Nonempty) (hIcne : Iᶜ.Nonempty) {W : AddSubgroup (permBar n)}
    (hW : ∀ J : Finset (Fin n), (J = I ∨ J = Iᶜ) → ∀ a ∈ J, ∀ b ∈ J, uvec a b ∈ W) :
    qbar0 I ≤ W := by
  classical
  obtain ⟨a, ha⟩ := hIne
  obtain ⟨b, hb⟩ := hIcne
  intro v hv
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨h1, h2⟩ := (mem_qbar0_mk hI hIc x).1 hv
  set S₁ := I.filter (fun i => x i = 1) with hS₁
  set S₂ := Iᶜ.filter (fun i => x i = 1) with hS₂
  have hsumI : ∀ S : Finset (Fin n), ∑ i ∈ S, x i = (S.filter (fun i => x i = 1)).card := by
    intro S
    rw [← Finset.sum_filter_add_sum_filter_not S (fun i => x i = 1)]
    have h3 : ∑ i ∈ S.filter (fun i => ¬ x i = 1), x i = 0 :=
      Finset.sum_eq_zero fun i hi => (zmod_two_eq_zero_iff_ne_one _).2 (Finset.mem_filter.1 hi).2
    have h4 : ∑ i ∈ S.filter (fun i => x i = 1), x i =
        ∑ i ∈ S.filter (fun i => x i = 1), (1 : ZMod 2) :=
      Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2
    rw [h3, add_zero, h4, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc1 : ((S₁.card : ℕ) : ZMod 2) = 0 := by rw [← hsumI I, h1]
  have hc2 : ((S₂.card : ℕ) : ZMod 2) = 0 := by rw [← hsumI Iᶜ, h2]
  have hvec : x = ∑ i ∈ S₁, (Pi.single i (1 : ZMod 2) + Pi.single a 1) +
      ∑ k ∈ S₂, (Pi.single k (1 : ZMod 2) + Pi.single b 1) := by
    funext m
    simp only [Finset.sum_apply, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
      Finset.sum_const, nsmul_eq_mul]
    simp only [Pi.single_apply, Finset.sum_ite_eq', Finset.sum_const_zero]
    by_cases hmI : m ∈ I
    · have hmb : m ≠ b := fun h => (Finset.mem_compl.1 hb) (h ▸ hmI)
      have hmS₂ : m ∉ S₂ := fun h => (Finset.mem_compl.1 (Finset.mem_filter.1 h).1) hmI
      by_cases hma : m = a
      · subst hma
        by_cases hx : x m = 1
        · have hmS₁ : m ∈ S₁ := Finset.mem_filter.2 ⟨hmI, hx⟩
          simp [hmS₁, hmS₂, hmb, hc1, hx]
        · have hmS₁ : m ∉ S₁ := fun h => hx (Finset.mem_filter.1 h).2
          simp [hmS₁, hmS₂, hmb, hc1, (zmod_two_eq_zero_iff_ne_one _).2 hx]
      · by_cases hx : x m = 1
        · have hmS₁ : m ∈ S₁ := Finset.mem_filter.2 ⟨hmI, hx⟩
          simp [hmS₁, hmS₂, hmb, hma, hx]
        · have hmS₁ : m ∉ S₁ := fun h => hx (Finset.mem_filter.1 h).2
          simp [hmS₁, hmS₂, hmb, hma, (zmod_two_eq_zero_iff_ne_one _).2 hx]
    · have hmIc : m ∈ Iᶜ := Finset.mem_compl.2 hmI
      have hma : m ≠ a := fun h => hmI (h ▸ ha)
      have hmS₁ : m ∉ S₁ := fun h => hmI (Finset.mem_filter.1 h).1
      by_cases hmb : m = b
      · subst hmb
        by_cases hx : x m = 1
        · have hmS₂ : m ∈ S₂ := Finset.mem_filter.2 ⟨hmIc, hx⟩
          simp [hmS₁, hmS₂, hma, hc2, hx]
        · have hmS₂ : m ∉ S₂ := fun h => hx (Finset.mem_filter.1 h).2
          simp [hmS₁, hmS₂, hma, hc2, (zmod_two_eq_zero_iff_ne_one _).2 hx]
      · by_cases hx : x m = 1
        · have hmS₂ : m ∈ S₂ := Finset.mem_filter.2 ⟨hmIc, hx⟩
          simp [hmS₁, hmS₂, hma, hmb, hx]
        · have hmS₂ : m ∉ S₂ := fun h => hx (Finset.mem_filter.1 h).2
          simp [hmS₁, hmS₂, hma, hmb, (zmod_two_eq_zero_iff_ne_one _).2 hx]
  rw [hvec, QuotientAddGroup.mk_add]
  refine W.add_mem ?_ ?_
  · have e : ((∑ i ∈ S₁, (Pi.single i (1 : ZMod 2) + Pi.single a 1) : Fin n → ZMod 2) :
        permBar n) = ∑ i ∈ S₁, uvec i a :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (allOnes n))) _ _
    rw [e]
    refine W.sum_mem fun i hi => ?_
    exact hW I (Or.inl rfl) i (Finset.mem_filter.1 hi).1 a ha
  · have e : ((∑ k ∈ S₂, (Pi.single k (1 : ZMod 2) + Pi.single b 1) : Fin n → ZMod 2) :
        permBar n) = ∑ k ∈ S₂, uvec k b :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (allOnes n))) _ _
    rw [e]
    refine W.sum_mem fun k hk => ?_
    exact hW Iᶜ (Or.inr rfl) k (Finset.mem_filter.1 hk).1 b hb

theorem pairs_of_one {J : Finset (Fin n)} (hJ : J.card = 4) {W : AddSubgroup (permBar n)}
    (h3 : ∀ τ : Perm (Fin n), τ.IsThreeCycle → (∀ y, y ∉ J → τ y = y) → ∀ w ∈ W,
      barAct τ w ∈ W)
    {a p : Fin n} (ha : a ∈ J) (hp : p ∈ J) (hap : a ≠ p) (hw : uvec a p ∈ W) :
    ∀ u ∈ J, ∀ v ∈ J, uvec u v ∈ W := by
  obtain ⟨q, hq, hqs⟩ := exists_fourth hJ {a, p} (Finset.card_le_two.trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqs
  obtain ⟨hqa, hqp⟩ := hqs
  obtain ⟨r, hr, hrs⟩ := exists_fourth hJ {a, p, q} Finset.card_le_three
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrs
  obtain ⟨hra, hrp, hrq⟩ := hrs
  have hJeq : ∀ y ∈ J, y = a ∨ y = p ∨ y = q ∨ y = r := by
    intro y hy
    have hsub : ({a, p, q, r} : Finset (Fin n)) ⊆ J := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> assumption
    have hcard : ({a, p, q, r} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair (Ne.symm hrq)]
      · simp [Ne.symm hqp, Ne.symm hrp]
      · simp [hap, Ne.symm hqa, Ne.symm hra]
    have hJe : ({a, p, q, r} : Finset (Fin n)) = J :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hJ, hcard])
    rw [← hJe] at hy
    simpa using hy
  have hcyc : ∀ {i j k : Fin n}, i ∈ J → j ∈ J → k ∈ J → i ≠ j → i ≠ k → j ≠ k →
      ∀ w ∈ W, barAct (cyc i j k) w ∈ W := by
    intro i j k hi hj hk hij hik hjk w hw'
    refine h3 _ (cyc_isThreeCycle hij hik hjk) (fun y hy => ?_) w hw'
    exact cyc_apply_of_ne (fun h => hy (h ▸ hi)) (fun h => hy (h ▸ hj)) (fun h => hy (h ▸ hk))
  have hfa : ∀ {i j k : Fin n}, a ≠ i → a ≠ j → a ≠ k → cyc i j k a = a :=
    fun h1 h2 h3' => cyc_apply_of_ne h1 h2 h3'
  have hwq : uvec a q ∈ W := by
    have h := hcyc hp hr hq (Ne.symm hrp) (Ne.symm hqp) hrq _ hw
    rwa [barAct_uvec, hfa hap (Ne.symm hra) (Ne.symm hqa),
      cyc_apply_first (Ne.symm hqp) hrq] at h
  have hwr : uvec a r ∈ W := by
    have h := hcyc hp hq hr (Ne.symm hqp) (Ne.symm hrp) (Ne.symm hrq) _ hw
    rwa [barAct_uvec, hfa hap (Ne.symm hqa) (Ne.symm hra),
      cyc_apply_first (Ne.symm hrp) (Ne.symm hrq)] at h
  have hthrough : ∀ y ∈ J, uvec a y ∈ W := by
    intro y hy
    rcases hJeq y hy with rfl | rfl | rfl | rfl
    · rw [uvec_self]; exact W.zero_mem
    · exact hw
    · exact hwq
    · exact hwr
  intro u hu v hv
  have h := W.add_mem (hthrough u hu) (hthrough v hv)
  rwa [uvec_comm a u, uvec_comm a v, uvec_add_uvec] at h

theorem exists_pair_of_nonconst {J : Finset (Fin n)} (hJ : J.card = 4) {W : AddSubgroup (permBar n)}
    (h3 : ∀ τ : Perm (Fin n), τ.IsThreeCycle → (∀ y, y ∉ J → τ y = y) → ∀ w ∈ W,
      barAct τ w ∈ W)
    {z : Fin n → ZMod 2} (hz : (z : permBar n) ∈ W) {a b : Fin n} (ha : a ∈ J) (hb : b ∈ J)
    (hza : z a = 1) (hzb : z b = 0) : ∃ p ∈ J, a ≠ p ∧ uvec a p ∈ W := by
  have hab : a ≠ b := fun h => by rw [h, hzb] at hza; exact zero_ne_one hza
  obtain ⟨c, hc, hcs⟩ := exists_fourth hJ {a, b} (Finset.card_le_two.trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcs
  obtain ⟨hca, hcb⟩ := hcs
  have hτ : (cyc a b c).IsThreeCycle := cyc_isThreeCycle hab (Ne.symm hca) (Ne.symm hcb)
  have hsupp : ∀ y, y ∉ J → cyc a b c y = y := fun y hy =>
    cyc_apply_of_ne (fun h => hy (h ▸ ha)) (fun h => hy (h ▸ hb)) (fun h => hy (h ▸ hc))
  have hmem : barAct (cyc a b c) (z : permBar n) - (z : permBar n) ∈ W :=
    W.sub_mem (h3 _ hτ hsupp _ hz) hz
  have hinv : ∀ y, (cyc a b c)⁻¹ y = cyc a c b y := fun y => by rw [cyc_inv]
  have hd : barAct (cyc a b c) (z : permBar n) - (z : permBar n) =
      ((fun m => z ((cyc a c b) m) - z m : Fin n → ZMod 2) : permBar n) := by
    rw [barAct_mk, ← QuotientAddGroup.mk_sub]
    congr 1
  rw [hd] at hmem
  have hca' : cyc a c b a = b := cyc_apply_first hab hcb
  have hcb' : cyc a c b b = c := cyc_apply_third a c b
  have hcc' : cyc a c b c = a := cyc_apply_second (Ne.symm hca) hcb
  have hfix : ∀ m, m ≠ a → m ≠ b → m ≠ c → cyc a c b m = m := fun m h1 h2 h3' =>
    cyc_apply_of_ne h1 h3' h2
  rcases zmod_two_cases' (z c) with hzc | hzc
  ·
    refine ⟨c, hc, Ne.symm hca, ?_⟩
    have e : ((fun m => z ((cyc a c b) m) - z m : Fin n → ZMod 2) : permBar n) = uvec a c := by
      unfold uvec
      congr 1
      funext m
      by_cases hma : m = a
      · subst hma
        simp [hca', hza, hzb, Pi.single_apply, Ne.symm hca]
      by_cases hmb : m = b
      · subst hmb
        simp [hcb', hzb, hzc, Pi.single_apply, hma, Ne.symm hcb]
      by_cases hmc : m = c
      · subst hmc
        simp [hcc', hza, hzc, Pi.single_apply, hma]
      · simp [hfix m hma hmb hmc, Pi.single_apply, hma, hmc]
    rwa [e] at hmem
  ·
    refine ⟨b, hb, hab, ?_⟩
    have e : ((fun m => z ((cyc a c b) m) - z m : Fin n → ZMod 2) : permBar n) = uvec a b := by
      unfold uvec
      congr 1
      funext m
      by_cases hma : m = a
      · subst hma
        simp [hca', hza, hzb, Pi.single_apply, hab]
      by_cases hmb : m = b
      · subst hmb
        simp [hcb', hzb, hzc, Pi.single_apply, hma]
      by_cases hmc : m = c
      · subst hmc
        simp [hcc', hza, hzc, Pi.single_apply, hma, hcb]
      · simp [hfix m hma hmb hmc, Pi.single_apply, hma, hmb]
    rwa [e] at hmem

end Pairs

section Eight

variable {I : Finset (Fin 8)}

theorem qbar0_le_of_invariant (hI : I.card = 4) {W : AddSubgroup (permBar 8)}
    (h3 : ∀ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) → ∀ τ : Perm (Fin 8), τ.IsThreeCycle →
      (∀ y, y ∉ J → τ y = y) → ∀ w ∈ W, barAct τ w ∈ W)
    {s : Perm (Fin 8)} (hs : ∀ y, s y ∈ I ↔ y ∉ I) (hsW : ∀ w ∈ W, barAct s w ∈ W)
    {w₀ : permBar 8} (hw₀ : w₀ ∈ W) (h0 : w₀ ≠ 0) (h1 : w₀ ≠ barInd I) : qbar0 I ≤ W := by
  classical
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective w₀
  have hnc : ∃ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) ∧ ∃ a ∈ J, ∃ b ∈ J, z a = 1 ∧ z b = 0 := by
    by_contra hall
    push Not at hall
    have hconst : ∀ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) → ∀ a ∈ J, ∀ b ∈ J, z a = z b := by
      intro J hJ a ha b hb
      rcases zmod_two_cases' (z a) with h | h <;> rcases zmod_two_cases' (z b) with h' | h'
      · rw [h, h']
      · exact absurd h (hall J hJ b hb a ha h')
      · exact absurd h' (hall J hJ a ha b hb h)
      · rw [h, h']
    obtain ⟨i₀, hi₀⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨k₀, hk₀⟩ : Iᶜ.Nonempty := Finset.card_pos.1 (by omega)
    have hzI : ∀ m, z m = if m ∈ I then z i₀ else z k₀ := fun m => by
      by_cases hm : m ∈ I
      · rw [if_pos hm]; exact hconst I (Or.inl rfl) m hm i₀ hi₀
      · rw [if_neg hm]; exact hconst Iᶜ (Or.inr rfl) m (Finset.mem_compl.2 hm) k₀ hk₀
    rcases zmod_two_cases' (z i₀) with hi | hi <;> rcases zmod_two_cases' (z k₀) with hk | hk
    · apply h0
      have : z = 0 := funext fun m => by rw [hzI m]; split_ifs <;> simp [hi, hk]
      rw [this]
      rfl
    · apply h1
      rw [← barInd_compl, barInd]
      congr 1
      funext m
      rw [hzI m]
      by_cases hm : m ∈ I <;> simp [hm, hi, hk, indVec]
    · apply h1
      rw [barInd]
      congr 1
      funext m
      rw [hzI m]
      by_cases hm : m ∈ I <;> simp [hm, hi, hk, indVec]
    · apply h0
      have : z = allOnes 8 := funext fun m => by rw [hzI m]; split_ifs <;> simp [hi, hk, allOnes]
      rw [this]
      exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)
  obtain ⟨J, hJ, a, ha, b, hb, hza, hzb⟩ := hnc
  have hJc : J.card = 4 := by rcases hJ with rfl | rfl <;> assumption
  obtain ⟨p, hp, hap, hwp⟩ := exists_pair_of_nonconst hJc (h3 J hJ) hw₀ ha hb hza hzb
  have hallJ := pairs_of_one hJc (h3 J hJ) ha hp hap hwp
  have hsJ : ∀ y, y ∈ J → s y ∈ Jᶜ := by
    intro y hy
    rw [Finset.mem_compl]
    rcases hJ with rfl | rfl
    · exact fun h => ((hs y).1 h) hy
    · rw [Finset.mem_compl] at hy
      exact fun h => (Finset.mem_compl.1 h) ((hs y).2 hy)
  have hJcc : Jᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hJc]
  have hJ' : Jᶜ = I ∨ Jᶜ = Iᶜ := by
    rcases hJ with rfl | rfl
    · exact Or.inr rfl
    · rw [compl_compl]; exact Or.inl rfl
  have hsap : s a ≠ s p := fun h => hap (s.injective h)
  have hws : uvec (s a) (s p) ∈ W := by
    have := hsW _ (hallJ a ha p hp)
    rwa [barAct_uvec] at this
  have hallJc := pairs_of_one hJcc (h3 Jᶜ hJ') (hsJ a ha) (hsJ p hp) hsap hws
  refine qbar0_le_of_pairs hIe hIce (Finset.card_pos.1 (by omega)) (Finset.card_pos.1 (by omega))
    fun K hK u hu v hv => ?_
  rcases hJ with rfl | rfl <;> rcases hK with rfl | rfl
  · exact hallJ u hu v hv
  · exact hallJc u hu v hv
  · rw [compl_compl] at hallJc
    exact hallJc u hu v hv
  · exact hallJ u hu v hv

theorem eq_zero_or_barInd_of_fixed (hI : I.card = 4) {v : permBar 8}
    (h1 : ∀ σ ∈ klein4 I, barAct σ v = v) (h2 : ∀ σ ∈ klein4 Iᶜ, barAct σ v = v) :
    v = 0 ∨ v = barInd I := by
  classical
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  have hconst : ∀ J : Finset (Fin 8), J.card = 4 → Jᶜ.Nonempty →
      (∀ σ ∈ klein4 J, barAct σ (x : permBar 8) = x) → ∀ a ∈ J, ∀ b ∈ J, x a = x b := by
    intro J hJ hJne hfix a ha b hb
    have hF := klein4_fourGroup hJ
    have hN : klein4 J ≠ ⊥ := by
      intro h
      have := card_klein4 hJ
      rw [h, Subgroup.card_bot] at this
      omega
    obtain ⟨σ, hσ, hσa⟩ := hF.transitive hJ hN hb ha
    have h := hfix σ hσ
    rw [barAct_mk_eq_self_iff] at h
    obtain ⟨k, hk⟩ := hJne
    have hkJ : k ∉ J := Finset.mem_compl.1 hk
    have hσk : σ⁻¹ k = k := by
      rw [Perm.inv_eq_iff_eq]
      exact (hF.fix σ hσ k hkJ).symm
    rcases h with h | h
    · have := h (σ b)
      rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply, hσa] at this
      exact this.symm
    · exfalso
      have := h k
      rw [hσk] at this
      have h0 : ∀ t : ZMod 2, t ≠ t + 1 := by decide
      exact h0 _ this
  have hIne : Iᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have hIcne : Iᶜᶜ.Nonempty := by rw [compl_compl]; exact Finset.card_pos.1 (by omega)
  have hcI := hconst I hI hIne h1
  have hcIc := hconst Iᶜ hIc hIcne h2
  obtain ⟨i₀, hi₀⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨k₀, hk₀⟩ := hIne
  have hxI : ∀ m, x m = if m ∈ I then x i₀ else x k₀ := fun m => by
    by_cases hm : m ∈ I
    · rw [if_pos hm]; exact hcI m hm i₀ hi₀
    · rw [if_neg hm]; exact hcIc m (Finset.mem_compl.2 hm) k₀ hk₀
  rcases zmod_two_cases' (x i₀) with hi | hi <;> rcases zmod_two_cases' (x k₀) with hk | hk
  · left
    have : x = 0 := funext fun m => by rw [hxI m]; split_ifs <;> simp [hi, hk]
    rw [this]
    rfl
  · right
    rw [← barInd_compl, barInd]
    congr 1
    funext m
    rw [hxI m]
    by_cases hm : m ∈ I <;> simp [hm, hi, hk, indVec]
  · right
    rw [barInd]
    congr 1
    funext m
    rw [hxI m]
    by_cases hm : m ∈ I <;> simp [hm, hi, hk, indVec]
  · left
    have : x = allOnes 8 := funext fun m => by rw [hxI m]; split_ifs <;> simp [hi, hk, allOnes]
    rw [this]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)

theorem mem_of_uvec_eq {a b c e : Fin 8} (hab : a ≠ b) (hce : c ≠ e) (h : uvec a b = uvec c e) :
    a = c ∨ a = e := by
  rw [H4b.uvec_eq_barInd hab, H4b.uvec_eq_barInd hce, barInd_eq_barInd_iff] at h
  rcases h with h | h
  · have : a ∈ ({c, e} : Finset (Fin 8)) := h ▸ Finset.mem_insert_self a {b}
    simpa using this
  · exfalso
    have := congrArg Finset.card h
    rw [Finset.card_pair hab, Finset.card_compl, Fintype.card_fin, Finset.card_pair hce] at this
    omega

theorem eq_one_of_fix_pairs (hI : I.card = 4) {σ : Perm (Fin 8)}
    (h : ∀ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) → ∀ a ∈ J, ∀ b ∈ J,
      barAct σ (uvec a b) = uvec a b) : σ = 1 := by
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  refine Equiv.ext fun a => ?_
  show σ a = a
  have hside : ∃ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) ∧ a ∈ J := by
    by_cases ha : a ∈ I
    · exact ⟨I, Or.inl rfl, ha⟩
    · exact ⟨Iᶜ, Or.inr rfl, Finset.mem_compl.2 ha⟩
  obtain ⟨J, hJ, ha⟩ := hside
  have hJc : J.card = 4 := by rcases hJ with rfl | rfl <;> assumption
  obtain ⟨b, hb, hbs⟩ := exists_fourth hJc {a} (by simp)
  simp only [Finset.mem_singleton] at hbs
  obtain ⟨c, hc, hcs⟩ := exists_fourth hJc {a, b} (Finset.card_le_two.trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcs
  obtain ⟨hca, hcb⟩ := hcs
  have hab : a ≠ b := Ne.symm hbs
  have hac : a ≠ c := Ne.symm hca
  have h1 := h J hJ a ha b hb
  have h2 := h J hJ a ha c hc
  rw [barAct_uvec] at h1 h2
  have hσab : σ a ≠ σ b := fun e => hab (σ.injective e)
  have hσac : σ a ≠ σ c := fun e => hac (σ.injective e)
  rcases mem_of_uvec_eq hσab hab h1 with e1 | e1
  · exact e1
  · rcases mem_of_uvec_eq hσac hac h2 with e2 | e2
    · exact e2
    · exact absurd (e1.symm.trans e2) (fun h' => hcb h'.symm)

theorem card_qbar0 (hI : I.card = 4) : Nat.card ↥(qbar0 I) = 2 ^ 5 := by
  classical
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  let φ : permBar 8 →+ ZMod 2 × ZMod 2 := (barParOn I).prod (barParOn Iᶜ)
  have hker : φ.ker = qbar0 I := by
    ext v
    simp only [φ, AddMonoidHom.mem_ker, AddMonoidHom.prod_apply, Prod.mk_eq_zero, qbar0,
      AddSubgroup.mem_inf]
  obtain ⟨a, ha⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨b, hb⟩ : Iᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have haI : a ∉ Iᶜ := fun h => (Finset.mem_compl.1 h) ha
  have hbI : b ∉ I := Finset.mem_compl.1 hb
  have hφa : φ ((Pi.single a (1 : ZMod 2) : Fin 8 → ZMod 2) : permBar 8) = (1, 0) := by
    simp only [φ, AddMonoidHom.prod_apply, barParOn_mk hIe, barParOn_mk hIce,
      Finset.sum_pi_single', if_pos ha, if_neg haI]
  have hφb : φ ((Pi.single b (1 : ZMod 2) : Fin 8 → ZMod 2) : permBar 8) = (0, 1) := by
    simp only [φ, AddMonoidHom.prod_apply, barParOn_mk hIe, barParOn_mk hIce,
      Finset.sum_pi_single', if_neg hbI, if_pos hb]
  have hsurj : Function.Surjective φ := by
    rintro ⟨s, t⟩
    rcases zmod_two_cases' s with rfl | rfl <;> rcases zmod_two_cases' t with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨_, hφb⟩
    · exact ⟨_, hφa⟩
    · refine ⟨((Pi.single a (1 : ZMod 2) : Fin 8 → ZMod 2) : permBar 8) +
        ((Pi.single b (1 : ZMod 2) : Fin 8 → ZMod 2) : permBar 8), ?_⟩
      rw [map_add, hφa, hφb]
      rfl
  have hcard : Nat.card (ZMod 2 × ZMod 2) = 2 ^ 2 := by
    rw [Nat.card_prod, Nat.card_zmod]
    norm_num
  have h := Comb.card_ker_pow (by norm_num) φ hsurj hcard (by norm_num)
  rwa [hker] at h

end Eight

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
