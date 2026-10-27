module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.Permutation.AlternatingAutomorphism.JohnsonGraph
import CFSG.Permutation.AlternatingAutomorphism.Conjugation
import CFSG.Permutation.AlternatingAutomorphism.JohnsonGraphIso

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

variable {n : ℕ}

theorem altAct_eq_iff (hn : 5 ≤ n) {σ τ : Perm (Fin n)} :
    (∀ v : altHeart n, altAct σ v = altAct τ v) ↔ σ = τ := by
  refine ⟨fun h => ?_, fun h v => by rw [h]⟩
  have h1 : τ⁻¹ * σ = 1 := by
    refine perm_eq_one_of_altHeart_fixed hn _ fun x => ?_
    have h2 : altAct (τ⁻¹ * σ) (x : altHeart n) = (x : altHeart n) := by
      rw [altAct_mul, h, altAct_inv_apply]
    rwa [altAct_mk] at h2
  exact (inv_mul_eq_one.1 h1).symm

theorem altHeart_exists_ne_zero (hn : 3 ≤ n) : ∃ v : altHeart n, v ≠ 0 := by
  have := altHeart_nontrivial hn
  exact exists_ne 0

@[expose] def NormalizerIsSym (n : ℕ) : Prop :=
  ∀ γ : altHeart n ≃+ altHeart n,
    (∀ σ ∈ alternatingGroup (Fin n), ∃ σ' ∈ alternatingGroup (Fin n),
      ∀ v, γ (altAct σ v) = altAct σ' (γ v)) →
    ∃ π : Perm (Fin n), ∀ v, γ v = altAct π v

theorem exists_aut_of_normalizing (hn : 5 ≤ n) (γ : altHeart n ≃+ altHeart n)
    (hγ : ∀ σ ∈ alternatingGroup (Fin n), ∃ σ' ∈ alternatingGroup (Fin n),
      ∀ v, γ (altAct σ v) = altAct σ' (γ v)) :
    ∃ φ : MulAut (alternatingGroup (Fin n)), ∀ (σ : alternatingGroup (Fin n)) (v : altHeart n),
      γ (altAct (σ : Perm (Fin n)) v) = altAct (φ σ : Perm (Fin n)) (γ v) := by
  choose! f hfA hf using hγ
  have huniq : ∀ σ ∈ alternatingGroup (Fin n), ∀ τ : Perm (Fin n),
      (∀ v, γ (altAct σ v) = altAct τ (γ v)) → τ = f σ := by
    intro σ hσ τ hτ
    refine ((altAct_eq_iff hn).1 fun w => ?_)
    obtain ⟨v, rfl⟩ := γ.surjective w
    rw [← hτ, hf σ hσ]
  have hmul : ∀ σ ∈ alternatingGroup (Fin n), ∀ ρ ∈ alternatingGroup (Fin n),
      f (σ * ρ) = f σ * f ρ := by
    intro σ hσ ρ hρ
    symm
    refine huniq (σ * ρ) (mul_mem hσ hρ) _ fun v => ?_
    rw [altAct_mul σ ρ v, hf σ hσ, hf ρ hρ, altAct_mul (f σ) (f ρ) (γ v)]
  have hinj : ∀ σ ∈ alternatingGroup (Fin n), ∀ ρ ∈ alternatingGroup (Fin n),
      f σ = f ρ → σ = ρ := by
    intro σ hσ ρ hρ hfσρ
    refine (altAct_eq_iff hn).1 fun v => γ.injective ?_
    rw [hf σ hσ, hf ρ hρ, hfσρ]
  let φ : alternatingGroup (Fin n) →* alternatingGroup (Fin n) :=
    MonoidHom.mk' (fun σ => ⟨f σ, hfA σ σ.2⟩) fun a b =>
      Subtype.ext (hmul a a.2 b b.2)
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab))
  exact ⟨MulEquiv.ofBijective φ (Finite.injective_iff_bijective.1 hφinj),
    fun σ v => hf σ σ.2 v⟩

theorem exists_perm_of_normalizing (hn : 7 ≤ n) (γ : altHeart n ≃+ altHeart n)
    (hγ : ∀ σ ∈ alternatingGroup (Fin n), ∃ σ' ∈ alternatingGroup (Fin n),
      ∀ v, γ (altAct σ v) = altAct σ' (γ v)) :
    ∃ π : Perm (Fin n), ∀ v, γ v = altAct π v := by
  have h5 : 5 ≤ n := by omega
  obtain ⟨φ, hφ⟩ := exists_aut_of_normalizing h5 γ hγ
  obtain ⟨π, hπ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inr hn) φ
  let δ : altHeart n →+ altHeart n := (altAct π⁻¹).comp γ.toAddMonoidHom
  have hδ : ∀ σ ∈ alternatingGroup (Fin n), ∀ v, δ (altAct σ v) = altAct σ (δ v) := by
    intro σ hσ v
    show altAct π⁻¹ (γ (altAct σ v)) = altAct σ (altAct π⁻¹ (γ v))
    rw [hφ ⟨σ, hσ⟩ v, ← altAct_mul, ← altAct_mul, hπ ⟨σ, hσ⟩]
    congr 1
    group
  have hγπ : ∀ v, γ v = altAct π (δ v) := fun v => (altAct_apply_inv π (γ v)).symm
  rcases altHeart_endo_eq_zero_or_id h5 δ hδ with h0 | h1
  · exfalso
    obtain ⟨v, hv⟩ := altHeart_exists_ne_zero (n := n) (by omega)
    refine hv (γ.injective ?_)
    rw [hγπ v, h0]
    simp
  · refine ⟨π, fun v => ?_⟩
    rw [hγπ v, h1]
    rfl

theorem normalizerIsSym_of_seven_le (hn : 7 ≤ n) : NormalizerIsSym n := fun γ hγ =>
  exists_perm_of_normalizing hn γ hγ

open CFSG.AlternatingAutomorphism

namespace Six

@[expose] def indVec {n : ℕ} (s : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun i => if i ∈ s then 1 else 0

theorem sum_indVec {n : ℕ} (s : Finset (Fin n)) : ∑ i, indVec s i = (s.card : ZMod 2) := by
  simp [indVec, Finset.sum_boole, Finset.filter_mem_eq_inter]

theorem indVec_mem_evenWeight {n : ℕ} {s : Finset (Fin n)} (hs : s.card = 2) :
    indVec s ∈ evenWeight n := by
  rw [evenWeight, AddMonoidHom.mem_ker]
  show ∑ i, indVec s i = 0
  rw [sum_indVec, hs]
  rfl

@[expose] noncomputable def pairVec {n : ℕ} (s : {s : Finset (Fin n) // s.card = 2}) :
    altHeart n :=
  ((⟨indVec s.1, indVec_mem_evenWeight s.2⟩ : evenWeight n) : altHeart n)

theorem altAct_pairVec {n : ℕ} (σ : Perm (Fin n)) (s : {s : Finset (Fin n) // s.card = 2}) :
    altAct σ (pairVec s) = pairVec ⟨s.1.map σ.toEmbedding, by rw [Finset.card_map, s.2]⟩ := by
  unfold pairVec
  rw [altAct_mk]
  congr 1
  refine Subtype.ext (funext fun i => ?_)
  show indVec s.1 (σ⁻¹ i) = indVec (s.1.map σ.toEmbedding) i
  simp [indVec, Finset.mem_map_equiv]

theorem exists_notMem_of_card_lt {n : ℕ} {s : Finset (Fin n)} (h : s.card < n) : ∃ b, b ∉ s := by
  by_contra hcon
  push Not at hcon
  have : s = Finset.univ := Finset.eq_univ_of_forall hcon
  rw [this, Finset.card_univ, Fintype.card_fin] at h
  exact lt_irrefl _ h

theorem zmod_two_neg_add (a b c : ZMod 2) : -a + b = c ↔ a + b = c := by
  revert a b c; decide

theorem mk_eq_mk_iff {n : ℕ} (x y : evenWeight n) :
    (x : altHeart n) = (y : altHeart n) ↔
      ∃ c : ZMod 2, ∀ i, (x : Fin n → ZMod 2) i + (y : Fin n → ZMod 2) i = c := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes h
    exact ⟨c, fun i => (zmod_two_neg_add _ _ _).1 (hc i)⟩
  · rintro ⟨c, hc⟩
    exact mem_evenWeightOnes_of_forall_eq (c := c) fun i => (zmod_two_neg_add _ _ _).2 (hc i)

theorem pairVec_ne_zero {n : ℕ} (hn : 3 ≤ n) (s : {s : Finset (Fin n) // s.card = 2}) :
    pairVec s ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes ((QuotientAddGroup.eq_zero_iff _).1 h)
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by rw [s.2]; norm_num : 0 < s.1.card)
  obtain ⟨b, hb⟩ := exists_notMem_of_card_lt (n := n) (s := s.1) (by rw [s.2]; omega)
  have h1 : (1 : ZMod 2) = c := hc a ▸ by simp [indVec, ha]
  have h2 : (0 : ZMod 2) = c := hc b ▸ by simp [indVec, hb]
  exact absurd (h2.trans h1.symm) (by decide)

theorem pairVec_injective {n : ℕ} (hn : 5 ≤ n) : Function.Injective (pairVec (n := n)) := by
  intro s t h
  obtain ⟨c, hc⟩ := (mk_eq_mk_iff _ _).1 h
  obtain ⟨i, hi⟩ : ∃ i, i ∉ s.1 ∪ t.1 :=
    exists_notMem_of_card_lt (lt_of_le_of_lt (Finset.card_union_le _ _) (by rw [s.2, t.2]; omega))
  have hc0 : c = 0 := by
    have h1 := hc i
    rw [Finset.mem_union, not_or] at hi
    have h2 : (0 : ZMod 2) = c := h1 ▸ by simp [indVec, hi.1, hi.2]
    exact h2.symm
  refine Subtype.ext (Finset.ext fun j => ?_)
  have hj : indVec s.1 j + indVec t.1 j = 0 := (hc j).trans hc0
  by_cases hjs : j ∈ s.1 <;> by_cases hjt : j ∈ t.1 <;> simp_all [indVec] <;> revert hj <;> decide

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem eq_indVec {n : ℕ} (x : Fin n → ZMod 2) :
    x = indVec (Finset.univ.filter fun i => x i = 1) := by
  funext i
  rcases zmod_two_eq_zero_or_one (x i) with h | h
  · simp [indVec, h]
  · simp [indVec, h]

theorem exists_pairVec_of_ne_zero (v : altHeart 6) (hv : v ≠ 0) : ∃ s, pairVec s = v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  set S : Finset (Fin 6) := Finset.univ.filter fun i => (x : Fin 6 → ZMod 2) i = 1 with hS
  have hx : (x : Fin 6 → ZMod 2) = indVec S := eq_indVec _
  have hsum : ∑ i, indVec S i = 0 := by rw [← hx]; exact x.2
  rw [sum_indVec] at hsum
  have heven : Even S.card := ZMod.natCast_eq_zero_iff_even.1 hsum
  have hle : S.card ≤ 6 := by simpa using Finset.card_le_univ S
  obtain ⟨k, hk⟩ := heven
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  ·
    exfalso
    have hS0 : S = ∅ := Finset.card_eq_zero.1 (by omega)
    refine hv ((QuotientAddGroup.eq_zero_iff _).2
      (mem_evenWeightOnes_of_forall_eq (c := 0) fun i => ?_))
    rw [show ((x : Fin 6 → ZMod 2) i) = indVec S i from congrFun hx i, hS0]
    simp [indVec]
  ·
    refine ⟨⟨S, by omega⟩, ?_⟩
    have h1 : (⟨indVec S, indVec_mem_evenWeight (by omega)⟩ : evenWeight 6) = x :=
      Subtype.ext hx.symm
    unfold pairVec
    rw [h1]
  ·
    have hc : (Sᶜ).card = 2 := by rw [Finset.card_compl, Fintype.card_fin]; omega
    refine ⟨⟨Sᶜ, hc⟩, ?_⟩
    refine (mk_eq_mk_iff _ _).2 ⟨1, fun i => ?_⟩
    show indVec Sᶜ i + (x : Fin 6 → ZMod 2) i = 1
    rw [show ((x : Fin 6 → ZMod 2) i) = indVec S i from congrFun hx i]
    by_cases h : i ∈ S <;> simp [indVec, h]
  ·
    exfalso
    have hS6 : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using (by omega : S.card = 6))
    refine hv ((QuotientAddGroup.eq_zero_iff _).2
      (mem_evenWeightOnes_of_forall_eq (c := 1) fun i => ?_))
    rw [show ((x : Fin 6 → ZMod 2) i) = indVec S i from congrFun hx i, hS6]
    simp [indVec]

theorem eq_one_of_card_support_le_two {n : ℕ} {σ : Perm (Fin n)} (hσ : sign σ = 1)
    (h : σ.support.card ≤ 2) : σ = 1 := by
  obtain hs | hs | hs : σ.support.card = 0 ∨ σ.support.card = 1 ∨ σ.support.card = 2 := by omega
  · exact Equiv.Perm.card_support_eq_zero.mp hs
  · exact absurd hs (Equiv.Perm.card_support_ne_one σ)
  · simp [(Equiv.Perm.card_support_eq_two.mp hs).sign_eq] at hσ

theorem map_eq_self_of_fix {n : ℕ} {σ : Perm (Fin n)} {s : Finset (Fin n)}
    (h : ∀ a ∈ s, σ a = a) : s.map σ.toEmbedding = s := by
  ext a
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [h b hb]
    exact hb
  · intro ha
    exact ⟨a, ha, h a ha⟩

theorem fix_of_map_eq {n : ℕ} {σ : Perm (Fin n)} (hσ3 : σ ^ 3 = 1) {s : Finset (Fin n)}
    (hs : s.card = 2) (hmap : s.map σ.toEmbedding = s) : ∀ a ∈ s, σ a = a := by
  intro a ha
  by_contra hne
  have hσs : ∀ b ∈ s, σ b ∈ s := fun b hb => by
    rw [← hmap]
    exact Finset.mem_map_of_mem _ hb
  have hsub : ({a, σ a} : Finset (Fin n)) ⊆ s := by
    intro c hc
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact ha
    · rw [Finset.mem_singleton.1 hc]
      exact hσs a ha
  have hcard : ({a, σ a} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hne)
  have heq : ({a, σ a} : Finset (Fin n)) = s :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hs, hcard])
  have h2 : σ (σ a) ∈ ({a, σ a} : Finset (Fin n)) := by
    rw [heq]
    exact hσs _ (hσs a ha)
  have h3 : σ (σ a) = a := by
    rcases Finset.mem_insert.1 h2 with h | h
    · exact h
    · exact absurd (σ.injective (Finset.mem_singleton.1 h)) hne
  have h4 : (σ ^ 3) a = a := by rw [hσ3]; rfl
  apply hne
  calc σ a = σ (σ (σ a)) := by rw [h3]
    _ = (σ ^ 3) a := by simp [pow_succ, Perm.mul_apply]
    _ = a := h4

def FixAdj (p q : altHeart 6) : Prop :=
  ∃ σ ∈ alternatingGroup (Fin 6), σ ≠ 1 ∧ σ ^ 3 = 1 ∧ altAct σ p = p ∧ altAct σ q = q

theorem adj_iff_fixAdj {s t : {s : Finset (Fin 6) // s.card = 2}} (hst : s ≠ t) :
    (johnsonGraph (Fin 6) 2).Adj s t ↔ FixAdj (pairVec s) (pairVec t) := by
  constructor
  · intro hadj
    have hinter : (s.1 ∩ t.1).card = 1 := by simpa using hadj
    have hunion : (s.1 ∪ t.1).card = 3 := by
      have := Finset.card_union_add_card_inter s.1 t.1
      rw [s.2, t.2, hinter] at this
      omega
    have hcompl : (s.1 ∪ t.1)ᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, hunion]
    obtain ⟨x, y, z, hxy, hxz, hyz, hxyz⟩ := Finset.card_eq_three.1 hcompl
    have hσ3 : (swap x y * swap x z).IsThreeCycle := isThreeCycle_swap_mul_swap_same hxy hxz hyz
    have hfix : ∀ a ∈ s.1 ∪ t.1, (swap x y * swap x z) a = a := by
      intro a ha
      have hax : a ≠ x := fun h => by
        have : x ∈ (s.1 ∪ t.1)ᶜ := by rw [hxyz]; simp
        exact (Finset.mem_compl.1 this) (h ▸ ha)
      have hay : a ≠ y := fun h => by
        have : y ∈ (s.1 ∪ t.1)ᶜ := by rw [hxyz]; simp
        exact (Finset.mem_compl.1 this) (h ▸ ha)
      have haz : a ≠ z := fun h => by
        have : z ∈ (s.1 ∪ t.1)ᶜ := by rw [hxyz]; simp
        exact (Finset.mem_compl.1 this) (h ▸ ha)
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hax haz, swap_apply_of_ne_of_ne hax hay]
    refine ⟨swap x y * swap x z, hσ3.mem_alternatingGroup, ?_, ?_, ?_, ?_⟩
    · intro h1
      have := hσ3.orderOf
      rw [h1, orderOf_one] at this
      omega
    · rw [← hσ3.orderOf]
      exact pow_orderOf_eq_one _
    · rw [altAct_pairVec]
      congr 1
      exact Subtype.ext (map_eq_self_of_fix fun a ha => hfix a (Finset.mem_union_left _ ha))
    · rw [altAct_pairVec]
      congr 1
      exact Subtype.ext (map_eq_self_of_fix fun a ha => hfix a (Finset.mem_union_right _ ha))
  · rintro ⟨σ, hσA, hσ1, hσ3, hs, ht⟩
    rw [altAct_pairVec] at hs ht
    have hs' := fix_of_map_eq hσ3 s.2 (congrArg Subtype.val (pairVec_injective (by omega) hs))
    have ht' := fix_of_map_eq hσ3 t.2 (congrArg Subtype.val (pairVec_injective (by omega) ht))
    have hlt := johnsonGraph.card_inter_lt hst
    have hfix : ∀ a ∈ s.1 ∪ t.1, σ a = a := fun a ha => by
      rcases Finset.mem_union.1 ha with h | h
      · exact hs' a h
      · exact ht' a h
    rw [johnsonGraph.adj_iff]
    by_contra hne
    have h0 : (s.1 ∩ t.1).card = 0 := by omega
    have hunion : (s.1 ∪ t.1).card = 4 := by
      have := Finset.card_union_add_card_inter s.1 t.1
      rw [s.2, t.2, h0] at this
      omega
    have hsupp : σ.support ⊆ (s.1 ∪ t.1)ᶜ := fun a ha => by
      rw [Finset.mem_compl]
      intro hmem
      exact (Equiv.Perm.mem_support.1 ha) (hfix a hmem)
    have hcard : σ.support.card ≤ 2 := by
      have := Finset.card_le_card hsupp
      rwa [Finset.card_compl, Fintype.card_fin, hunion] at this
    exact hσ1 (eq_one_of_card_support_le_two (Equiv.Perm.mem_alternatingGroup.1 hσA) hcard)

noncomputable def pairMap (γ : altHeart 6 ≃+ altHeart 6) (s : {s : Finset (Fin 6) // s.card = 2}) :
    {s : Finset (Fin 6) // s.card = 2} :=
  Classical.choose (exists_pairVec_of_ne_zero (γ (pairVec s))
    (fun h => pairVec_ne_zero (by omega) s (γ.injective (h.trans (map_zero γ).symm))))

theorem pairVec_pairMap (γ : altHeart 6 ≃+ altHeart 6) (s : {s : Finset (Fin 6) // s.card = 2}) :
    pairVec (pairMap γ s) = γ (pairVec s) :=
  Classical.choose_spec (exists_pairVec_of_ne_zero (γ (pairVec s))
    (fun h => pairVec_ne_zero (by omega) s (γ.injective (h.trans (map_zero γ).symm))))

theorem pairMap_injective (γ : altHeart 6 ≃+ altHeart 6) : Function.Injective (pairMap γ) :=
  fun s t h => pairVec_injective (by omega) (γ.injective (by
    rw [← pairVec_pairMap, ← pairVec_pairMap, h]))

theorem pairMap_symm_pairMap (γ : altHeart 6 ≃+ altHeart 6)
    (s : {s : Finset (Fin 6) // s.card = 2}) : pairMap γ.symm (pairMap γ s) = s :=
  pairVec_injective (by omega) (by
    rw [pairVec_pairMap, pairVec_pairMap, AddEquiv.symm_apply_apply])

theorem pairMap_pairMap_symm (γ : altHeart 6 ≃+ altHeart 6)
    (s : {s : Finset (Fin 6) // s.card = 2}) : pairMap γ (pairMap γ.symm s) = s :=
  pairVec_injective (by omega) (by
    rw [pairVec_pairMap, pairVec_pairMap, AddEquiv.apply_symm_apply])

theorem adj_pairMap (γ : altHeart 6 ≃+ altHeart 6) (φ : MulAut (alternatingGroup (Fin 6)))
    (hφ : ∀ (σ : alternatingGroup (Fin 6)) (v : altHeart 6),
      γ (altAct (σ : Perm (Fin 6)) v) = altAct (φ σ : Perm (Fin 6)) (γ v))
    {s t : {s : Finset (Fin 6) // s.card = 2}} (h : (johnsonGraph (Fin 6) 2).Adj s t) :
    (johnsonGraph (Fin 6) 2).Adj (pairMap γ s) (pairMap γ t) := by
  have hst : s ≠ t := (johnsonGraph (Fin 6) 2).ne_of_adj h
  have hst' : pairMap γ s ≠ pairMap γ t := fun h' => hst (pairMap_injective γ h')
  rw [adj_iff_fixAdj hst] at h
  rw [adj_iff_fixAdj hst', pairVec_pairMap, pairVec_pairMap]
  obtain ⟨σ, hσA, hσ1, hσ3, hs, ht⟩ := h
  refine ⟨(φ ⟨σ, hσA⟩ : Perm (Fin 6)), (φ ⟨σ, hσA⟩).2, ?_, ?_, ?_, ?_⟩
  · intro h1
    have h2 : φ ⟨σ, hσA⟩ = 1 := Subtype.ext h1
    have h3 := φ.injective (h2.trans (map_one φ).symm)
    exact hσ1 (congrArg Subtype.val h3)
  · have h1 : (⟨σ, hσA⟩ : alternatingGroup (Fin 6)) ^ 3 = 1 := Subtype.ext hσ3
    have h2 : (φ ⟨σ, hσA⟩) ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    exact congrArg Subtype.val h2
  · rw [← hφ ⟨σ, hσA⟩ (pairVec s), hs]
  · rw [← hφ ⟨σ, hσA⟩ (pairVec t), ht]

noncomputable def pairIso (γ : altHeart 6 ≃+ altHeart 6) (φ : MulAut (alternatingGroup (Fin 6)))
    (hφ : ∀ (σ : alternatingGroup (Fin 6)) (v : altHeart 6),
      γ (altAct (σ : Perm (Fin 6)) v) = altAct (φ σ : Perm (Fin 6)) (γ v)) :
    johnsonGraph (Fin 6) 2 ≃g johnsonGraph (Fin 6) 2 where
  toFun := pairMap γ
  invFun := pairMap γ.symm
  left_inv := pairMap_symm_pairMap γ
  right_inv := pairMap_pairMap_symm γ
  map_rel_iff' {s t} := by
    refine ⟨fun h => ?_, adj_pairMap γ φ hφ⟩
    have hφ' : ∀ (σ : alternatingGroup (Fin 6)) (v : altHeart 6),
        γ.symm (altAct (σ : Perm (Fin 6)) v) =
          altAct (φ.symm σ : Perm (Fin 6)) (γ.symm v) := by
      intro σ v
      have h1 := hφ (φ.symm σ) (γ.symm v)
      rw [MulEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h1
      rw [← h1, AddEquiv.symm_apply_apply]
    have h2 := adj_pairMap γ.symm φ.symm hφ' h
    simpa only [Equiv.coe_fn_mk, pairMap_symm_pairMap] using h2

theorem normalizerIsSym : NormalizerIsSym 6 := by
  intro γ hγ
  obtain ⟨φ, hφ⟩ := exists_aut_of_normalizing (by norm_num : 5 ≤ 6) γ hγ
  obtain ⟨π, hπ⟩ := johnsonGraph.exists_perm_of_iso (k := 2) (by rw [Fintype.card_fin]; omega)
    (pairIso γ φ hφ)
  refine ⟨π, fun v => ?_⟩
  by_cases hv : v = 0
  · rw [hv, map_zero, map_zero]
  · obtain ⟨s, rfl⟩ := exists_pairVec_of_ne_zero v hv
    rw [← pairVec_pairMap, altAct_pairVec]
    congr 1
    exact Subtype.ext (hπ s)

end Six

theorem normalizerIsSym_six : NormalizerIsSym 6 := Six.normalizerIsSym

theorem normalizerIsSym_of_six_or_seven_le (hn : n = 6 ∨ 7 ≤ n) : NormalizerIsSym n := by
  rcases hn with rfl | hn
  · exact normalizerIsSym_six
  · exact normalizerIsSym_of_seven_le hn

end CFSG.RankThree.PartTwo.Sec19.SolEven
