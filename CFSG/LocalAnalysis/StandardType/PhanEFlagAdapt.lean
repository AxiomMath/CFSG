module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def rk (E F : FlagK K n) (i j : ℕ) : ℕ :=
  finrank K ↥(E.E i ⊓ F.E j)

@[expose] def permRk (σ : Equiv.Perm (Fin n)) (i j : ℕ) : ℕ :=
  (Finset.univ.filter fun k : Fin n => k.val < i ∧ (σ k).val < j).card

@[expose] def HasPos (E F : FlagK K n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, i ≤ n → j ≤ n → rk E F i j = permRk σ i j

@[expose] def IsAdapted (b : Fin n → (Fin n → K)) (σ : Equiv.Perm (Fin n)) (E F : FlagK K n) :
    Prop :=
  LinearIndependent K b ∧
    (∀ i, i ≤ n → E.E i = Submodule.span K (b '' {k : Fin n | k.val < i})) ∧
    ∀ j, j ≤ n → F.E j = Submodule.span K (b '' {k : Fin n | (σ k).val < j})

@[expose] noncomputable def stdFlag (K : Type) [Field K] (n : ℕ) : FlagK K n where
  E j := Vsub n j
  mono _ _ h := Vsub_mono h
  dim j hj := finrank_Vsub hj
  top j hj := by
    ext v
    simp only [Submodule.mem_top, iff_true]
    intro i _
    exact absurd hj (by omega)

private lemma q2cFP_finrank_span_image (b : Fin n → (Fin n → K))
    (hb : LinearIndependent K b) (S : Finset (Fin n)) :
    finrank K (Submodule.span K (b '' (S : Set (Fin n)))) = S.card := by
  have hrange : Set.range (fun x : S => b x.1) = b '' (S : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card]
  · exact Fintype.card_coe S
  · exact hb.comp _ Subtype.val_injective

lemma q2cFP_finrank_span_inter (b : Fin n → (Fin n → K))
    (hb : LinearIndependent K b) (S T : Finset (Fin n)) :
    finrank K ↥(Submodule.span K (b '' (S : Set (Fin n))) ⊓
      Submodule.span K (b '' (T : Set (Fin n)))) = (S ∩ T).card := by
  have hU : Submodule.span K (b '' ((S ∪ T : Finset (Fin n)) : Set (Fin n))) =
      Submodule.span K (b '' (S : Set (Fin n))) ⊔
        Submodule.span K (b '' (T : Set (Fin n))) := by
    rw [Finset.coe_union, Set.image_union, Submodule.span_union]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K (b '' (S : Set (Fin n))))
    (Submodule.span K (b '' (T : Set (Fin n))))
  rw [← hU, q2cFP_finrank_span_image b hb (S ∪ T),
    q2cFP_finrank_span_image b hb S, q2cFP_finrank_span_image b hb T] at hdim
  have hcard : (S ∪ T).card + (S ∩ T).card = S.card + T.card :=
    Finset.card_union_add_card_inter S T
  omega

private lemma q2cFP_exists_pos (E F : FlagK K n) (k : ℕ) (hk : k < n) :
    ∃ j : ℕ, ¬ (E.E (k + 1) ⊓ F.E (j + 1) ≤ E.E k) := by
  refine ⟨n - 1, ?_⟩
  rw [show n - 1 + 1 = n by omega, F.top n le_rfl, inf_top_eq]
  intro hle
  have h1 : finrank K (E.E (k + 1)) = k + 1 := E.dim (k + 1) (by omega)
  have h2 : finrank K (E.E k) = k := E.dim k (by omega)
  have := Submodule.finrank_mono hle
  omega

private noncomputable def q2cFP_pos (E F : FlagK K n) (k : ℕ) (hk : k < n) : ℕ := by
  classical
  exact Nat.find (q2cFP_exists_pos E F k hk)

private lemma q2cFP_pos_spec (E F : FlagK K n) (k : ℕ) (hk : k < n) :
    ¬ (E.E (k + 1) ⊓ F.E (q2cFP_pos E F k hk + 1) ≤ E.E k) := by
  classical
  exact Nat.find_spec (q2cFP_exists_pos E F k hk)

private lemma q2cFP_pos_min (E F : FlagK K n) (k : ℕ) (hk : k < n) {j : ℕ}
    (hj : j < q2cFP_pos E F k hk) :
    E.E (k + 1) ⊓ F.E (j + 1) ≤ E.E k := by
  classical
  by_contra hle
  exact Nat.find_min (q2cFP_exists_pos E F k hk) hj hle

private lemma q2cFP_exists_b (E F : FlagK K n) (k : ℕ) (hk : k < n) :
    ∃ v : Fin n → K,
      v ∈ E.E (k + 1) ∧ v ∈ F.E (q2cFP_pos E F k hk + 1) ∧ v ∉ E.E k := by
  have h := q2cFP_pos_spec E F k hk
  by_contra hc
  apply h
  intro x hx
  by_contra hxE
  exact hc ⟨x, (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2, hxE⟩

private noncomputable def q2cFP_b (E F : FlagK K n) (k : Fin n) : Fin n → K :=
  Classical.choose (q2cFP_exists_b E F k.val k.isLt)

private lemma q2cFP_b_mem_E (E F : FlagK K n) (k : Fin n) :
    q2cFP_b E F k ∈ E.E (k.val + 1) :=
  (Classical.choose_spec (q2cFP_exists_b E F k.val k.isLt)).1

private lemma q2cFP_b_mem_F (E F : FlagK K n) (k : Fin n) :
    q2cFP_b E F k ∈ F.E (q2cFP_pos E F k.val k.isLt + 1) :=
  (Classical.choose_spec (q2cFP_exists_b E F k.val k.isLt)).2.1

private lemma q2cFP_b_notMem_E (E F : FlagK K n) (k : Fin n) :
    q2cFP_b E F k ∉ E.E k.val :=
  (Classical.choose_spec (q2cFP_exists_b E F k.val k.isLt)).2.2

private noncomputable def q2cFP_sigmaFun (E F : FlagK K n) : Fin n → ℕ :=
  fun k => q2cFP_pos E F k.val k.isLt

private lemma q2cFP_E_succ (E F : FlagK K n) (k : Fin n) :
    E.E (k.val + 1) = E.E k.val ⊔ Submodule.span K {q2cFP_b E F k} := by
  have hbE := q2cFP_b_mem_E E F k
  have hbnot := q2cFP_b_notMem_E E F k
  have hle : E.E k.val ⊔ Submodule.span K {q2cFP_b E F k} ≤ E.E (k.val + 1) := by
    apply sup_le
    · exact E.mono (by omega)
    · rw [Submodule.span_le]
      rintro _ rfl
      exact hbE
  have hdim : finrank K ↥(E.E k.val ⊔ Submodule.span K {q2cFP_b E F k}) = k.val + 1 := by
    rw [Submodule.finrank_sup_span_singleton hbnot, E.dim k.val (by omega)]
  have hdim2 : finrank K (E.E (k.val + 1)) = k.val + 1 := E.dim (k.val + 1) (by omega)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, hdim2])).symm

private lemma q2cFP_inf_eq_of_le_pos (E F : FlagK K n) (k : Fin n) {j : ℕ}
    (hj : j ≤ q2cFP_pos E F k.val k.isLt) :
    E.E (k.val + 1) ⊓ F.E j = E.E k.val ⊓ F.E j := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxE, hxF⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨?_, hxF⟩
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hbot : F.E 0 = ⊥ := F.E_zero
      rw [hbot, Submodule.mem_bot] at hxF
      simpa [hxF] using Submodule.zero_mem (E.E k.val)
    · have hmin := q2cFP_pos_min E F k.val k.isLt (j := j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at hmin
      exact hmin hx
  · exact inf_le_inf_right (F.E j) (E.mono (by omega))

private lemma q2cFP_inf_eq_of_gt_pos (E F : FlagK K n) (k : Fin n) {j : ℕ}
    (hj : q2cFP_pos E F k.val k.isLt < j) :
    E.E (k.val + 1) ⊓ F.E j = (E.E k.val ⊓ F.E j) ⊔ Submodule.span K {q2cFP_b E F k} := by
  have hbF : q2cFP_b E F k ∈ F.E j :=
    F.mono (by omega) (q2cFP_b_mem_F E F k)
  rw [q2cFP_E_succ E F k]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxsup, hxF⟩ := Submodule.mem_inf.mp hx
    obtain ⟨a, ha, z, hz, hsum⟩ := Submodule.mem_sup.mp hxsup
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    have hzF : z ∈ F.E j := by
      rw [← hc]
      exact (F.E j).smul_mem c hbF
    have haF : a ∈ F.E j := by
      rw [← hsum] at hxF
      simpa using (F.E j).sub_mem hxF hzF
    exact Submodule.mem_sup.mpr
      ⟨a, Submodule.mem_inf.mpr ⟨ha, haF⟩, z, hz, hsum⟩
  · intro x hx
    obtain ⟨a, ha, z, hz, hsum⟩ := Submodule.mem_sup.mp hx
    obtain ⟨haE, haF⟩ := Submodule.mem_inf.mp ha
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    have hzF : z ∈ F.E j := by
      rw [← hc]
      exact (F.E j).smul_mem c hbF
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.mem_sup.mpr ⟨a, haE, z, hz, hsum⟩
    · rw [← hsum]
      exact (F.E j).add_mem haF hzF

private theorem q2cFP_rank_formula (E F : FlagK K n) :
    ∀ i j : ℕ, i ≤ n → j ≤ n →
      finrank K ↥(E.E i ⊓ F.E j) =
        (Finset.univ.filter fun k : Fin n => k.val < i ∧ q2cFP_sigmaFun E F k < j).card := by
  intro i
  induction i with
  | zero =>
      intro j _ _
      rw [E.E_zero, bot_inf_eq]
      have hemp : (Finset.univ.filter fun k : Fin n =>
          k.val < 0 ∧ q2cFP_sigmaFun E F k < j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro k _ hk
        omega
      rw [hemp]
      simp
  | succ i ih =>
      intro j hi hj
      have hik : i ≤ n := by omega
      have hin : i < n := by omega
      by_cases hjp : j ≤ q2cFP_pos E F i hin
      · rw [q2cFP_inf_eq_of_le_pos E F ⟨i, hin⟩ hjp, ih j hik hj]
        congr 1
        apply Finset.filter_congr
        intro k _
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          by_contra hki
          have hk : k = (⟨i, hin⟩ : Fin n) := by
            apply Fin.ext
            simp only [Fin.val_mk]
            omega
          subst hk
          have h2' : q2cFP_pos E F i hin < j := by
            simpa [q2cFP_sigmaFun] using h2
          omega
      · have hjp' : q2cFP_pos E F i hin < j := by omega
        rw [q2cFP_inf_eq_of_gt_pos E F ⟨i, hin⟩ hjp']
        rw [Submodule.finrank_sup_span_singleton (p := E.E i ⊓ F.E j)
          (fun h => q2cFP_b_notMem_E E F ⟨i, hin⟩ (Submodule.mem_inf.mp h).1)]
        rw [ih j hik hj]
        have hfilter : (Finset.univ.filter fun k : Fin n =>
              k.val < i + 1 ∧ q2cFP_sigmaFun E F k < j) =
            (Finset.univ.filter fun k : Fin n =>
              k.val < i ∧ q2cFP_sigmaFun E F k < j) ∪ {(⟨i, hin⟩ : Fin n)} := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases hki : k.val < i
            · exact Or.inl ⟨hki, h2⟩
            · exact Or.inr (by
                apply Fin.ext
                simp only [Fin.val_mk]
                omega)
          · rintro (⟨h1, h2⟩ | rfl)
            · exact ⟨by omega, h2⟩
            · refine ⟨by simp, ?_⟩
              exact hjp'
        have hdisj : Disjoint (Finset.univ.filter fun k : Fin n =>
            k.val < i ∧ q2cFP_sigmaFun E F k < j) {(⟨i, hin⟩ : Fin n)} := by
          rw [Finset.disjoint_singleton_right]
          simp
        rw [hfilter, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

private lemma q2cFP_sigma_card_lt (E F : FlagK K n) {j : ℕ} (hj : j ≤ n) :
    (Finset.univ.filter fun k : Fin n => q2cFP_sigmaFun E F k < j).card = j := by
  have h := q2cFP_rank_formula E F n j le_rfl hj
  rw [E.top n le_rfl, top_inf_eq, F.dim j hj] at h
  have hset : (Finset.univ.filter fun k : Fin n =>
        k.val < n ∧ q2cFP_sigmaFun E F k < j) =
      (Finset.univ.filter fun k : Fin n => q2cFP_sigmaFun E F k < j) := by
    apply Finset.filter_congr
    intro k _
    simp
  rw [hset] at h
  exact h.symm

private lemma q2cFP_sigmaFun_lt (E F : FlagK K n) (k : Fin n) :
    q2cFP_sigmaFun E F k < n := by
  have h := q2cFP_rank_formula E F n n le_rfl le_rfl
  rw [E.top n le_rfl, top_inf_eq, F.dim n le_rfl] at h
  have hset : (Finset.univ.filter fun k : Fin n =>
        k.val < n ∧ q2cFP_sigmaFun E F k < n) =
      (Finset.univ.filter fun k : Fin n => q2cFP_sigmaFun E F k < n) := by
    apply Finset.filter_congr
    intro k _
    simp
  rw [hset] at h
  have hcard : (Finset.univ.filter fun k : Fin n => q2cFP_sigmaFun E F k < n).card =
      (Finset.univ : Finset (Fin n)).card := by
    rw [← h, Finset.card_univ, Fintype.card_fin]
  exact Finset.filter_card_eq hcard k (Finset.mem_univ k)

private lemma q2cFP_sigma_fiber_card (E F : FlagK K n) (m : Fin n) :
    (Finset.univ.filter fun k : Fin n =>
      (⟨q2cFP_sigmaFun E F k, q2cFP_sigmaFun_lt E F k⟩ : Fin n) = m).card = 1 := by
  set A := Finset.univ.filter (fun k : Fin n => q2cFP_sigmaFun E F k < m.val + 1) with hA
  set B := Finset.univ.filter (fun k : Fin n => q2cFP_sigmaFun E F k < m.val) with hB
  have hBA : B ⊆ A := by
    intro k hk
    simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  have hdiff : A \ B = Finset.univ.filter fun k : Fin n =>
      (⟨q2cFP_sigmaFun E F k, q2cFP_sigmaFun_lt E F k⟩ : Fin n) = m := by
    ext k
    simp only [Finset.mem_sdiff, hA, hB, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      apply Fin.ext
      simp only
      omega
    · intro hk
      have hv : q2cFP_sigmaFun E F k = m.val := by
        simpa using congrArg Fin.val hk
      exact ⟨by omega, by omega⟩
  rw [← hdiff, Finset.card_sdiff_of_subset hBA,
    q2cFP_sigma_card_lt E F (by omega : m.val + 1 ≤ n),
    q2cFP_sigma_card_lt E F (by omega : m.val ≤ n)]
  omega

private noncomputable def q2cFP_sigma (E F : FlagK K n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective
    (fun k : Fin n => (⟨q2cFP_sigmaFun E F k, q2cFP_sigmaFun_lt E F k⟩ : Fin n)) (by
      have hinj : Function.Injective
          (fun k : Fin n => (⟨q2cFP_sigmaFun E F k, q2cFP_sigmaFun_lt E F k⟩ : Fin n)) := by
        intro a b hab
        have hcard := q2cFP_sigma_fiber_card E F
          (⟨q2cFP_sigmaFun E F a, q2cFP_sigmaFun_lt E F a⟩ : Fin n)
        have ha : a ∈ Finset.univ.filter (fun k : Fin n =>
            (⟨q2cFP_sigmaFun E F k, q2cFP_sigmaFun_lt E F k⟩ : Fin n) =
            (⟨q2cFP_sigmaFun E F a, q2cFP_sigmaFun_lt E F a⟩ : Fin n)) := by simp
        have hb : b ∈ Finset.univ.filter (fun k : Fin n =>
            (⟨q2cFP_sigmaFun E F k, q2cFP_sigmaFun_lt E F k⟩ : Fin n) =
            (⟨q2cFP_sigmaFun E F a, q2cFP_sigmaFun_lt E F a⟩ : Fin n)) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hab.symm
        exact Finset.card_le_one.mp (le_of_eq hcard) a ha b hb
      exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

private lemma q2cFP_sigma_apply (E F : FlagK K n) (k : Fin n) :
    (q2cFP_sigma E F k).val = q2cFP_sigmaFun E F k := rfl

private theorem q2cFP_E_span (E F : FlagK K n) :
    ∀ i, i ≤ n →
      E.E i = Submodule.span K (q2cFP_b E F '' {k : Fin n | k.val < i}) := by
  intro i
  induction i with
  | zero =>
      intro _
      symm
      rw [E.E_zero, Submodule.span_eq_bot]
      rintro _ ⟨k, hk, rfl⟩
      exact absurd hk (Nat.not_lt_zero k.val)
  | succ i ih =>
      intro hi
      have hik : i ≤ n := by omega
      have hin : i < n := by omega
      calc
        E.E (i + 1) = E.E i ⊔ Submodule.span K {q2cFP_b E F ⟨i, hin⟩} :=
          q2cFP_E_succ E F ⟨i, hin⟩
        _ = Submodule.span K (q2cFP_b E F '' {k : Fin n | k.val < i}) ⊔
              Submodule.span K {q2cFP_b E F ⟨i, hin⟩} := by rw [ih hik]
        _ = Submodule.span K (q2cFP_b E F ''
              ({k : Fin n | k.val < i} ∪ {⟨i, hin⟩})) := by
              rw [Set.image_union, Submodule.span_union]
              simp
        _ = Submodule.span K (q2cFP_b E F '' {k : Fin n | k.val < i + 1}) := by
              have hset : ({k : Fin n | k.val < i} ∪ {(⟨i, hin⟩ : Fin n)} : Set (Fin n)) =
                  {k : Fin n | k.val < i + 1} := by
                ext k
                change (k.val < i ∨ k = (⟨i, hin⟩ : Fin n)) ↔ k.val < i + 1
                constructor
                · rintro (h | h)
                  · omega
                  · subst h
                    simp
                · intro h
                  by_cases hki : k.val < i
                  · exact Or.inl hki
                  · exact Or.inr (by
                      apply Fin.ext
                      simp only [Fin.val_mk]
                      omega)
              rw [hset]

private noncomputable def q2cFP_bFin (E F : FlagK K n) (i : ℕ) (hi : i ≤ n) :
    Fin i → (Fin n → K) :=
  fun k => q2cFP_b E F ⟨k.val, lt_of_lt_of_le k.isLt hi⟩

private theorem q2cFP_linIndep_fin (E F : FlagK K n) :
    ∀ i (hi : i ≤ n), LinearIndependent K (q2cFP_bFin E F i hi) := by
  intro i
  induction i with
  | zero =>
      intro _
      exact linearIndependent_empty_type
  | succ i ih =>
      intro hi
      have hik : i ≤ n := by omega
      have hin : i < n := by omega
      have hsnoc : q2cFP_bFin E F (i + 1) hi =
          Fin.snoc (q2cFP_bFin E F i hik) (q2cFP_b E F ⟨i, hin⟩) := by
        funext k
        by_cases hk : k.val < i
        · have hkc : k = Fin.castSucc (⟨k.val, hk⟩ : Fin i) := Fin.ext rfl
          rw [hkc]
          simp only [q2cFP_bFin, Fin.snoc_castSucc]
          rfl
        · have hke : k.val = i := by omega
          have hkl : k = Fin.last i := Fin.ext hke
          rw [hkl]
          simp only [q2cFP_bFin, Fin.snoc_last]
          rfl
      rw [hsnoc]
      apply LinearIndependent.finSnoc (ih hik)
      have hspan : Submodule.span K (Set.range (q2cFP_bFin E F i hik)) =
          Submodule.span K (q2cFP_b E F '' {k : Fin n | k.val < i}) := by
        congr 1
        ext v
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨⟨k.val, lt_of_lt_of_le k.isLt hik⟩, by simp, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨⟨k.val, hk⟩, by simp [q2cFP_bFin]⟩
      rw [hspan, ← q2cFP_E_span E F i hik]
      exact q2cFP_b_notMem_E E F ⟨i, hin⟩

private theorem q2cFP_linIndep (E F : FlagK K n) :
    LinearIndependent K (q2cFP_b E F) := by
  have h := q2cFP_linIndep_fin E F n le_rfl
  convert h using 1
  funext k
  simp [q2cFP_bFin]

private theorem q2cFP_F_eq (E F : FlagK K n) {j : ℕ} (hj : j ≤ n) :
    F.E j = Submodule.span K (q2cFP_b E F '' {k : Fin n | (q2cFP_sigma E F k).val < j}) := by
  have hspan_le : Submodule.span K
      (q2cFP_b E F '' {k : Fin n | (q2cFP_sigma E F k).val < j}) ≤ F.E j := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    change (q2cFP_sigma E F k).val < j at hk
    rw [q2cFP_sigma_apply] at hk
    have hk' : q2cFP_pos E F k.val k.isLt < j := by
      simpa [q2cFP_sigmaFun] using hk
    exact F.mono (by omega) (q2cFP_b_mem_F E F k)
  have hdim : finrank K (Submodule.span K
      (q2cFP_b E F '' {k : Fin n | (q2cFP_sigma E F k).val < j})) = j := by
    rw [show {k : Fin n | (q2cFP_sigma E F k).val < j} =
        ↑(Finset.univ.filter fun k : Fin n => (q2cFP_sigma E F k).val < j) by
      ext k
      simp]
    rw [q2cFP_finrank_span_image (q2cFP_b E F) (q2cFP_linIndep E F)]
    rw [show (Finset.univ.filter fun k : Fin n => (q2cFP_sigma E F k).val < j) =
        (Finset.univ.filter fun k : Fin n => q2cFP_sigmaFun E F k < j) by
      apply Finset.filter_congr
      intro k _
      rw [q2cFP_sigma_apply]]
    exact q2cFP_sigma_card_lt E F hj
  exact (Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hdim, F.dim j hj])).symm

theorem exists_adapted (E F : FlagK K n) :
    ∃ (b : Fin n → (Fin n → K)) (σ : Equiv.Perm (Fin n)), IsAdapted b σ E F :=
  ⟨q2cFP_b E F, q2cFP_sigma E F, q2cFP_linIndep E F,
    fun i hi => q2cFP_E_span E F i hi, fun j hj => q2cFP_F_eq E F hj⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
