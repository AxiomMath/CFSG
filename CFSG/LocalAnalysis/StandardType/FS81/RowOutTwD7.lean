module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels
public import CFSG.LocalAnalysis.StandardType.FS81.RowCent

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

private def wtSupp {k : ℕ} (v : Coords k) : Finset (Fin k) :=
  Finset.univ.filter fun i => v i ≠ 0

private lemma wt_eq_wtSupp_card {k : ℕ} (v : Coords k) : wt v = (wtSupp v).card := rfl

private lemma zmod3_one_ne_zero : (1 : ZMod 3) ≠ 0 := by decide

private lemma zmod3_eq_one_or_neg_one : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide

private lemma zmod3_mul_self : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide

private lemma wtSupp_single_one {i : Fin 8} :
    wtSupp (Pi.single i (1 : ZMod 3) : Coords 8) = {i} := by
  ext x
  simp only [wtSupp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Pi.single_apply]
  by_cases hx : x = i <;> simp [hx]

private lemma wtSupp_single_zero_add {t : Coords 8} (ht : t 0 = 0) :
    wtSupp (Pi.single (0 : Fin 8) 1 + t) = insert 0 (wtSupp t) := by
  ext i
  simp only [wtSupp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hi : i = 0
  · subst hi
    simp [ht]
  · have hsi : (Pi.single (0 : Fin 8) (1 : ZMod 3) : Coords 8) i = 0 :=
      Pi.single_eq_of_ne hi 1
    rw [Pi.add_apply, hsi, zero_add]
    simp [hi]

private lemma wtSupp_single_zero_sub {t : Coords 8} (ht : t 0 = 0) :
    wtSupp (Pi.single (0 : Fin 8) 1 - t) = insert 0 (wtSupp t) := by
  ext i
  simp only [wtSupp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hi : i = 0
  · subst hi
    simp [ht]
  · have hsi : (Pi.single (0 : Fin 8) (1 : ZMod 3) : Coords 8) i = 0 :=
      Pi.single_eq_of_ne hi 1
    rw [Pi.sub_apply, hsi, zero_sub]
    simp [hi]

private lemma wt_single_zero_add {t : Coords 8} (ht : t 0 = 0) :
    wt (Pi.single (0 : Fin 8) 1 + t) = wt t + 1 := by
  have h0 : (0 : Fin 8) ∉ wtSupp t := by simp [wtSupp, ht]
  rw [wt_eq_wtSupp_card, wtSupp_single_zero_add ht, Finset.card_insert_of_notMem h0,
    wt_eq_wtSupp_card]

private lemma wt_single_zero_sub {t : Coords 8} (ht : t 0 = 0) :
    wt (Pi.single (0 : Fin 8) 1 - t) = wt t + 1 := by
  have h0 : (0 : Fin 8) ∉ wtSupp t := by simp [wtSupp, ht]
  rw [wt_eq_wtSupp_card, wtSupp_single_zero_sub ht, Finset.card_insert_of_notMem h0,
    wt_eq_wtSupp_card]

private lemma wt_add_single {j : Fin 8} (hj : j ≠ 0) :
    wt (Pi.single (0 : Fin 8) 1 + Pi.single j (1 : ZMod 3)) = 2 := by
  have ht : (Pi.single j (1 : ZMod 3) : Coords 8) 0 = 0 :=
    Pi.single_eq_of_ne (Ne.symm hj) 1
  rw [wt_single_zero_add ht, wt_eq_wtSupp_card, wtSupp_single_one, Finset.card_singleton]

private lemma wt_sub_single {j : Fin 8} (hj : j ≠ 0) :
    wt (Pi.single (0 : Fin 8) 1 - Pi.single j (1 : ZMod 3)) = 2 := by
  have ht : (Pi.single j (1 : ZMod 3) : Coords 8) 0 = 0 :=
    Pi.single_eq_of_ne (Ne.symm hj) 1
  rw [wt_single_zero_sub ht, wt_eq_wtSupp_card, wtSupp_single_one, Finset.card_singleton]

private lemma spMat_mulVec_single {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3)
    (j : Fin k) : spMat σ s *ᵥ Pi.single j 1 = s j • Pi.single (σ j) 1 := by
  rw [Matrix.mulVec_single_one]
  ext i
  rw [Matrix.col_apply, spMat_apply, Pi.smul_apply, Pi.single_apply]
  by_cases h : i = σ j <;> simp [h]

private lemma exists_smul_single_of_wt_eq_one {t : Coords 8} (h : wt t = 1) :
    ∃ i : Fin 8, ∃ s : ZMod 3, s ≠ 0 ∧ t = s • Pi.single i 1 := by
  rw [wt_eq_wtSupp_card] at h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  have hti : t i ≠ 0 := by
    have : i ∈ wtSupp t := by rw [hi]; simp
    simpa [wtSupp] using this
  have hzero : ∀ j, j ≠ i → t j = 0 := by
    intro j hj
    by_contra hne
    have hmem : j ∈ wtSupp t := by simpa [wtSupp] using hne
    rw [hi, Finset.mem_singleton] at hmem
    exact hj hmem
  refine ⟨i, t i, hti, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [hzero j hj]
    simp [Pi.smul_apply, Pi.single_eq_of_ne hj]

private lemma wt_mulVec_single_eq_one (M : Matrix (Fin 8) (Fin 8) (ZMod 3))
    (h0 : M.mulVec (Pi.single 0 1) = Pi.single 0 1)
    (hT : ∀ e : Coords 8, e 0 = 0 → M.mulVec e 0 = 0)
    (hS : ∀ e : Coords 8, e ≠ 0 → (wt e = 2 ∨ (wt e = 8 ∧ ∏ i, e i = -1)) →
      wt (M.mulVec e) = 2 ∨ (wt (M.mulVec e) = 8 ∧ ∏ i, M.mulVec e i = -1))
    (j : Fin 8) : wt (M.mulVec (Pi.single j 1)) = 1 := by
  by_cases hj : j = 0
  · subst hj
    rw [h0, wt_eq_wtSupp_card, wtSupp_single_one, Finset.card_singleton]
  · let t : Coords 8 := M.mulVec (Pi.single j 1)
    change wt t = 1
    by_contra hwt
    have ht0 : t 0 = 0 := hT (Pi.single j 1) (Pi.single_eq_of_ne (Ne.symm hj) 1)
    have hne_add : (Pi.single (0 : Fin 8) 1 + Pi.single j (1 : ZMod 3) : Coords 8) ≠ 0 := by
      intro h
      have := congrFun h 0
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj), add_zero] at this
      exact zmod3_one_ne_zero this
    have hgood_add : wt (Pi.single (0 : Fin 8) (1 : ZMod 3) + Pi.single j (1 : ZMod 3)) = 2 ∨
        (wt (Pi.single (0 : Fin 8) (1 : ZMod 3) + Pi.single j (1 : ZMod 3)) = 8 ∧
          ∏ i, (Pi.single (0 : Fin 8) (1 : ZMod 3) + Pi.single j (1 : ZMod 3) : Coords 8) i
            = -1) :=
      Or.inl (wt_add_single hj)
    have hA := hS (Pi.single (0 : Fin 8) 1 + Pi.single j 1) hne_add hgood_add
    have hAmv : M.mulVec (Pi.single (0 : Fin 8) 1 + Pi.single j 1) =
        Pi.single (0 : Fin 8) 1 + t := by
      rw [Matrix.mulVec_add, h0]
    have hA' : wt (Pi.single (0 : Fin 8) 1 + t) = 2 ∨
        (wt (Pi.single (0 : Fin 8) 1 + t) = 8 ∧
          ∏ i, (Pi.single (0 : Fin 8) 1 + t : Coords 8) i = -1) := by
      rw [← hAmv]; exact hA
    have hwt_add_ne2 : wt (Pi.single (0 : Fin 8) 1 + t) ≠ 2 := by
      rw [wt_single_zero_add ht0]; omega
    have hAprod : ∏ i, (Pi.single (0 : Fin 8) 1 + t : Coords 8) i = -1 := by
      rcases hA' with h2 | ⟨_, hp⟩
      · exact absurd h2 hwt_add_ne2
      · exact hp
    have hne_sub : (Pi.single (0 : Fin 8) 1 - Pi.single j (1 : ZMod 3) : Coords 8) ≠ 0 := by
      intro h
      have := congrFun h 0
      rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj), sub_zero] at this
      exact zmod3_one_ne_zero this
    have hgood_sub : wt (Pi.single (0 : Fin 8) (1 : ZMod 3) - Pi.single j (1 : ZMod 3)) = 2 ∨
        (wt (Pi.single (0 : Fin 8) (1 : ZMod 3) - Pi.single j (1 : ZMod 3)) = 8 ∧
          ∏ i, (Pi.single (0 : Fin 8) (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : Coords 8) i
            = -1) :=
      Or.inl (wt_sub_single hj)
    have hB := hS (Pi.single (0 : Fin 8) 1 - Pi.single j 1) hne_sub hgood_sub
    have hBmv : M.mulVec (Pi.single (0 : Fin 8) 1 - Pi.single j 1) =
        Pi.single (0 : Fin 8) 1 - t := by
      rw [Matrix.mulVec_sub, h0]
    have hB' : wt (Pi.single (0 : Fin 8) 1 - t) = 2 ∨
        (wt (Pi.single (0 : Fin 8) 1 - t) = 8 ∧
          ∏ i, (Pi.single (0 : Fin 8) 1 - t : Coords 8) i = -1) := by
      rw [← hBmv]; exact hB
    have hwt_sub_ne2 : wt (Pi.single (0 : Fin 8) 1 - t) ≠ 2 := by
      rw [wt_single_zero_sub ht0]; omega
    have hBprod : ∏ i, (Pi.single (0 : Fin 8) 1 - t : Coords 8) i = -1 := by
      rcases hB' with h2 | ⟨_, hp⟩
      · exact absurd h2 hwt_sub_ne2
      · exact hp
    have hprod_add : ∏ i : Fin 8, (Pi.single (0 : Fin 8) 1 + t : Coords 8) i =
        ∏ i : Fin 7, t i.succ := by
      rw [Fin.prod_univ_succ]
      have hz : (Pi.single (0 : Fin 8) 1 + t : Coords 8) 0 = 1 := by
        rw [Pi.add_apply, Pi.single_eq_same, ht0, add_zero]
      rw [hz, one_mul]
      apply Finset.prod_congr rfl
      intro i _
      rw [Pi.add_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i), zero_add]
    have hprod_sub : ∏ i : Fin 8, (Pi.single (0 : Fin 8) 1 - t : Coords 8) i =
        - ∏ i : Fin 7, t i.succ := by
      rw [Fin.prod_univ_succ]
      have hz : (Pi.single (0 : Fin 8) 1 - t : Coords 8) 0 = 1 := by
        rw [Pi.sub_apply, Pi.single_eq_same, ht0, sub_zero]
      rw [hz, one_mul]
      rw [show (∏ i : Fin 7, (Pi.single (0 : Fin 8) 1 - t : Coords 8) i.succ) =
          ∏ i : Fin 7, (- t i.succ) by
        apply Finset.prod_congr rfl
        intro i _
        rw [Pi.sub_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i), zero_sub]]
      rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin,
        show (-1 : ZMod 3) ^ 7 = -1 by decide, neg_one_mul]
    have hQm1 : ∏ i : Fin 7, t i.succ = -1 := by
      rw [hprod_add] at hAprod; exact hAprod
    have hQ1 : ∏ i : Fin 7, t i.succ = 1 := by
      rw [hprod_sub] at hBprod; exact neg_inj.mp hBprod
    rw [hQ1] at hQm1
    exact (show (1 : ZMod 3) ≠ -1 by decide) hQm1

theorem mem_evenFix0_of_mulVec_mapsTo_twD7 (M : Matrix (Fin 8) (Fin 8) (ZMod 3))
    (h0 : M.mulVec (Pi.single 0 1) = Pi.single 0 1)
    (hT : ∀ e : Coords 8, e 0 = 0 → M.mulVec e 0 = 0)
    (hinj : Function.Injective M.mulVec)
    (hS : ∀ e : Coords 8, e ≠ 0 → (wt e = 2 ∨ (wt e = 8 ∧ ∏ i, e i = -1)) →
      wt (M.mulVec e) = 2 ∨ (wt (M.mulVec e) = 8 ∧ ∏ i, M.mulVec e i = -1)) :
    M ∈ evenFix0 7 := by
  have hW : ∀ j : Fin 8, wt (M.mulVec (Pi.single j 1)) = 1 :=
    wt_mulVec_single_eq_one M h0 hT hS
  choose i s hs_ne hs_eq using fun j => exists_smul_single_of_wt_eq_one (hW j)
  have hi0 : i 0 = 0 := by
    by_contra hne
    have h := congrFun (hs_eq 0) 0
    simp only [h0, Pi.single_eq_same, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at h
    rw [if_neg (fun hh : (0 : Fin 8) = i 0 => hne hh.symm), mul_zero] at h
    exact zmod3_one_ne_zero h
  have hs0 : s 0 = 1 := by
    have h := congrFun (hs_eq 0) 0
    rw [hi0, h0, Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at h
    exact h.symm
  have hi_ne : ∀ j : Fin 8, j ≠ 0 → i j ≠ 0 := by
    intro j hj
    have h := congrFun (hs_eq j) 0
    rw [hT (Pi.single j 1) (Pi.single_eq_of_ne (Ne.symm hj) 1), Pi.smul_apply,
      Pi.single_apply, smul_eq_mul] at h
    intro hij
    rw [hij, if_pos rfl, mul_one] at h
    exact hs_ne j h.symm
  have hinj_i : Function.Injective i := by
    intro a b hab
    by_cases ha : a = 0
    · subst ha
      by_contra hb
      exact hi_ne b (fun hb' => hb hb'.symm) (by rw [← hab]; exact hi0)
    · by_cases hb : b = 0
      · subst hb
        exact absurd (by rw [hab]; exact hi0) (hi_ne a ha)
      · by_cases hab' : a = b
        · exact hab'
        · exfalso
          have hsq : s b * s b = 1 := zmod3_mul_self (s b) (hs_ne b)
          have hMv : M.mulVec (Pi.single a 1 - (s a * s b) • Pi.single b 1) = 0 := by
            rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hs_eq a, hs_eq b, hab, smul_smul,
              show s a * s b * s b = s a by rw [mul_assoc, hsq, mul_one]]
            exact sub_self _
          have hker : (Pi.single a 1 - (s a * s b) • Pi.single b 1 : Coords 8) = 0 := by
            apply hinj
            rw [hMv, Matrix.mulVec_zero]
          have h1 : (Pi.single a 1 - (s a * s b) • Pi.single b 1 : Coords 8) a = 1 := by
            rw [Pi.sub_apply, Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_of_ne hab' 1,
              smul_zero, sub_zero]
          have h0a : (Pi.single a 1 - (s a * s b) • Pi.single b 1 : Coords 8) a = 0 := by
            rw [hker]; rfl
          rw [h1] at h0a
          exact zmod3_one_ne_zero h0a
  let σ : Equiv.Perm (Fin 8) := Equiv.ofBijective i hinj_i.bijective_of_finite
  have hσ0 : σ 0 = 0 := by
    change i 0 = 0
    exact hi0
  have hsign : IsSign s := fun j => zmod3_eq_one_or_neg_one (s j) (hs_ne j)
  have hM : M = spMat σ s := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [hs_eq j]
    exact (spMat_mulVec_single σ s j).symm
  have hprod8 : ∏ j : Fin 8, s j = 1 := by
    let t0 : Coords 8 := fun i => if i = 1 then -1 else 1
    have ht0_ne : t0 ≠ 0 := by
      intro h
      have := congrFun h 1
      simp [t0] at this
    have ht0_wt : wt t0 = 8 := by decide
    have ht0_prod : ∏ i, t0 i = -1 := by decide
    have ht0_good : wt t0 = 2 ∨ (wt t0 = 8 ∧ ∏ i, t0 i = -1) := Or.inr ⟨ht0_wt, ht0_prod⟩
    have hA := hS t0 ht0_ne ht0_good
    have hwtMt0 : wt (M.mulVec t0) = 8 := by
      rw [hM, wt_eq_wtSupp_card]
      have hsupp : wtSupp (spMat σ s *ᵥ t0) = Finset.univ := by
        ext x
        simp only [wtSupp, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [spMat_mulVec]
        exact iff_true_intro (mul_ne_zero (hs_ne (σ.symm x)) (by
          by_cases hx : σ.symm x = 1 <;>
            simp [t0, hx]))
      rw [hsupp, Finset.card_univ, Fintype.card_fin]
    have hne2 : wt (M.mulVec t0) ≠ 2 := by omega
    have hprodA : ∏ i, M.mulVec t0 i = -1 := by
      rcases hA with h2 | ⟨_, hp⟩
      · exact absurd h2 hne2
      · exact hp
    have hcalc : ∏ i, M.mulVec t0 i = (∏ i : Fin 8, s i) * (-1) := by
      rw [hM]
      simp only [spMat_mulVec]
      rw [Equiv.prod_comp σ.symm (fun i => s i * t0 i), Finset.prod_mul_distrib, ht0_prod]
    rw [hcalc] at hprodA
    have hneg : -(∏ i : Fin 8, s i) = -1 := by
      rw [mul_neg, mul_one] at hprodA; exact hprodA
    exact neg_inj.mp hneg
  have hs_prod7 : ∏ i : Fin 7, s i.succ = 1 := by
    have h := Fin.prod_univ_succ (fun i : Fin 8 => s i)
    rw [hprod8, hs0, one_mul] at h
    exact h.symm
  rw [evenFix0, spSet]
  exact ⟨σ, s, hsign, ⟨hσ0, hs0, hs_prod7⟩, hM⟩

private theorem vec_nsmul_aux {G : Type} [Group G] {k : ℕ} (B : Basis3 G k) (m : ℕ)
    (e : Coords k) : B.vec (m • e) = B.vec e ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, B.vec_zero]
  | succ m ih => rw [succ_nsmul, B.vec_add, ih, pow_succ]

private theorem vec_smul_single_aux {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    (c : ZMod 3) (i : Fin k) : B.vec (c • Pi.single i 1) = B.b i ^ c.val := by
  rw [show c • (Pi.single i 1 : Coords k) = c.val • Pi.single i 1 by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val],
    vec_nsmul_aux, B.vec_single]

private theorem zpowers_conj_aux {G : Type} [Group G] {g x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers (g * y * g⁻¹) := by
  have hx : Subgroup.zpowers (g * x * g⁻¹) =
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom :=
    (MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom x).symm
  rw [hx, h, MonoidHom.map_zpowers]
  rfl

private theorem vec_mem_K_of_zero {G : Type} [Group G] {n : ℕ} (B : Basis3 G (n + 1))
    {K : Subgroup G} (hK : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ K) {e : Coords (n + 1)}
    (he : e 0 = 0) : B.vec e ∈ K := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  by_cases hi : i = 0
  · subst hi
    rw [he, ZMod.val_zero, pow_zero]
    exact K.one_mem
  · exact K.pow_mem (hK i hi) _

theorem realized_centralizer_subset_evenFix0_of_recOutTwD7 {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K)) (hrec : RecOutTwD7 B b₀) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ evenFix0 7 := by
  intro A hA
  obtain ⟨g, hgC, hActs⟩ := hA
  obtain ⟨hspan, hb0, hbK⟩ := hB
  have hgcomm : g * b₀ = b₀ * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hord : orderOf b₀ = 3 := by rw [← hb0]; exact B.ord 0
  have hdisj' : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := by
    rw [hspan]; exact hdisj
  have hgNB : g ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hActs
  have hgNK : g ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn hgC
  have hinj : Function.Injective A.mulVec := by
    intro e e' hee
    apply B.vec_injective
    have h1 : g * B.vec e * g⁻¹ = g * B.vec e' * g⁻¹ := by
      rw [B.acts_vec hActs e, B.acts_vec hActs e', hee]
    calc B.vec e = g⁻¹ * (g * B.vec e * g⁻¹) * g := by group
      _ = g⁻¹ * (g * B.vec e' * g⁻¹) * g := by rw [h1]
      _ = B.vec e' := by group
  have h0 : A.mulVec (Pi.single 0 1) = Pi.single 0 1 := by
    apply B.vec_injective
    have hb0conj : g * b₀ * g⁻¹ = b₀ := by rw [hgcomm]; group
    rw [← B.acts_vec hActs (Pi.single 0 1), B.vec_single, hb0, hb0conj]
  have hT : ∀ e : Coords 8, e 0 = 0 → A.mulVec e 0 = 0 := by
    intro e he
    have hveK : B.vec e ∈ K := vec_mem_K_of_zero B (fun i hi => hbK i hi) he
    have hconjK : g * B.vec e * g⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hgNK (B.vec e)).mp hveK
    set f := A.mulVec e with hfdef
    have hfK : B.vec f ∈ K := by
      rw [hfdef]
      rwa [B.acts_vec hActs e] at hconjK
    set e' : Coords 8 := f - f 0 • Pi.single 0 1 with he'def
    have he'0 : e' 0 = 0 := by simp [he'def]
    have he'K : B.vec e' ∈ K := vec_mem_K_of_zero B (fun i hi => hbK i hi) he'0
    have hsum : f 0 • Pi.single 0 1 + e' = f := by
      rw [he'def]; abel
    have hsplit : B.vec f = B.vec (f 0 • Pi.single 0 1) * B.vec e' := by
      rw [← B.vec_add, hsum]
    have hpow : b₀ ^ (f 0).val = B.vec f * (B.vec e')⁻¹ := by
      rw [← hb0, ← vec_smul_single_aux B (f 0) 0, hsplit]; group
    have hpowK : b₀ ^ (f 0).val ∈ K := by
      rw [hpow]; exact K.mul_mem hfK (K.inv_mem he'K)
    have hpowE : b₀ ^ (f 0).val ∈ B.span :=
      B.span.pow_mem (hb0 ▸ B.b_mem_span 0) _
    have hbot : b₀ ^ (f 0).val = 1 := by
      have hmem : b₀ ^ (f 0).val ∈ Subgroup.zpowers b₀ ⊓ (B.span ⊓ K) :=
        ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _, hpowE, hpowK⟩
      exact Subgroup.mem_bot.mp (disjoint_iff_inf_le.mp hdisj' hmem)
    have hdvd : 3 ∣ (f 0).val := by
      have := orderOf_dvd_of_pow_eq_one hbot
      rwa [hord] at this
    have hval0 : (f 0).val = 0 := by
      have hlt := ZMod.val_lt (f 0)
      omega
    exact (ZMod.val_eq_zero (f 0)).mp hval0
  have hS : ∀ e : Coords 8, e ≠ 0 → (wt e = 2 ∨ (wt e = 8 ∧ ∏ i, e i = -1)) →
      wt (A.mulVec e) = 2 ∨ (wt (A.mulVec e) = 8 ∧ ∏ i, A.mulVec e i = -1) := by
    intro e he hgood
    have hne : A.mulVec e ≠ 0 := by
      intro hzero
      exact he (hinj (by rw [hzero, Matrix.mulVec_zero]))
    refine (hrec.2.2 (A.mulVec e) hne).mp ?_
    have hline := (hrec.2.2 e he).mpr hgood
    obtain ⟨h, hhN, hhline⟩ := hline
    have hline' : Subgroup.zpowers (h * (b₀ * B.b 1) * h⁻¹) = Subgroup.zpowers (B.vec e) :=
      hhline
    refine ⟨g * h, Subgroup.mul_mem _ hgNB hhN, ?_⟩
    change Subgroup.zpowers ((g * h) * (b₀ * B.b 1) * (g * h)⁻¹)
      = Subgroup.zpowers (B.vec (A.mulVec e))
    have hgh : (g * h) * (b₀ * B.b 1) * (g * h)⁻¹
        = g * (h * (b₀ * B.b 1) * h⁻¹) * g⁻¹ := by group
    rw [hgh, ← B.acts_vec hActs e]
    exact zpowers_conj_aux hline'
  exact mem_evenFix0_of_mulVec_mapsTo_twD7 A h0 hT hinj hS

private theorem card_realized_eq_card_ggInduced {G : Type} [Group G] [Finite G] {k : ℕ}
    (B : Basis3 G k) (H : Subgroup G) :
    Nat.card ↥(B.realized H) = Nat.card ↥(ggInduced H B.span) := by
  have hset : B.realized H = B.matOf '' ggInduced H B.span := by
    ext A
    rw [B.mem_realized_iff H A, Set.mem_image]
  rw [hset, Nat.card_image_of_injective B.matOf_injective (ggInduced H B.span)]

theorem Basis3.card_realized_eq_of_span_eq {G : Type} [Group G] [Finite G] {k : ℕ}
    {B B' : Basis3 G k} (h : B.span = B'.span) (H : Subgroup G) :
    Nat.card ↥(B.realized H) = Nat.card ↥(B'.realized H) := by
  calc Nat.card ↥(B.realized H)
      = Nat.card ↥(ggInduced H B.span) := card_realized_eq_card_ggInduced B H
    _ = Nat.card ↥(ggInduced H B'.span) := by rw [h]
    _ = Nat.card ↥(B'.realized H) := (card_realized_eq_card_ggInduced B' H).symm

theorem disjoint_zpowers_of_center {G : Type} [Group G] {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) (hcenter : Subgroup.center K = ⊥) :
    Disjoint (Subgroup.zpowers b₀) K := by
  rw [Subgroup.disjoint_def]
  intro x hx hxK
  have hxcenter : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : Commute b₀ (y : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hKC y.2)).symm
    exact (hcomm.zpow_left m).eq.symm
  rw [hcenter] at hxcenter
  simpa using hxcenter

theorem centralizer_eq_sup_of_recOutTwD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) :
    Subgroup.centralizer ({b₀} : Set G) =
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) := by
  obtain ⟨_hsimple, hHyp, hCanon⟩ := hstd
  obtain ⟨hrow, hdisjEK, hsup, hmax, hcard, _⟩ := hCanon
  obtain ⟨hA, _, _, _, _, _⟩ := hHyp
  obtain ⟨hb₀, hKC, hKn, hcenter, _, _hcyc, _, _⟩ := hA
  change RecOutTwD7 B b₀ at hrec
  obtain ⟨_hKs, ⟨φ⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hrow hcenter
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hcenter
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin]
    decide
  refine le_antisymm ?_ (sup_le hKC inf_le_left)
  by_contra hout
  obtain ⟨B', hB', heven, M, hM, hMnot⟩ :=
    exists_basis_not_mem_evenFix0_of_not_le
      (V := Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)
      (Q := CFSG.LieType.Universal.Spin.quadMinus 7 (ZMod 2) 1 1)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 7 (ZMod 2)
        (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0))
      exists_totallySingular_three_quadMinus_seven h6
      omegaAutIsometric_quadMinus_seven (n := 7) (by norm_num)
      φ hb₀ hKC hKn hdisj hsup hmax hcard hout
  let C := Subgroup.centralizer ({b₀} : Set G)
  have hsub : B.realized C ⊆ evenFix0 7 :=
    realized_centralizer_subset_evenFix0_of_recOutTwD7 hB hKC hKn hdisjEK hrec
  have hcardeq : Nat.card ↥(B.realized C) = Nat.card ↥(B'.realized C) :=
    Basis3.card_realized_eq_of_span_eq (hB.1.trans hB'.1.symm) C
  have hcardeq' : (B.realized C).ncard = (B'.realized C).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hcardeq
  have hle : (B'.realized C).ncard ≤ (evenFix0 7).ncard := by
    rw [← hcardeq']
    exact Set.ncard_le_ncard hsub
  have heq : evenFix0 7 = B'.realized C := Set.eq_of_subset_of_ncard_le heven hle
  rw [← heq] at hM
  exact hMnot hM

theorem rowOutAt_twD7 : RowOutAt Row.twD7 := fun _ _ _ _ _ _ hstd _ hB hrec _ =>
  centralizer_eq_sup_of_recOutTwD7 hstd hB hrec

theorem rowCentAt_twD7 : RowCentAt Row.twD7 :=
  rowCentAt_of_rowOutAt rowOutAt_twD7

end CFSG.StandardType.FrameRoute.FS81
