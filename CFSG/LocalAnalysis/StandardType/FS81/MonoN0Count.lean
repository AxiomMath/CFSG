module

public import CFSG.LocalAnalysis.StandardType.FS81.MonoN0Orbit
public import CFSG.LocalAnalysis.StandardType.FS81.WtTwo

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {n : ℕ}

private theorem monoCount_fin_ne {a b : ℕ} (ha : a < n + 1) (hb : b < n + 1) (hab : a ≠ b) :
    (OfNat.ofNat a : Fin (n + 1)) ≠ (OfNat.ofNat b : Fin (n + 1)) := by
  apply Fin.ne_of_val_ne
  change (Fin.ofNat (n + 1) a).val ≠ (Fin.ofNat (n + 1) b).val
  rw [Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact hab

private theorem monoCount_wt_single (a : Fin (n + 1)) :
    wt (Pi.single a (1 : ZMod 3)) = 1 := by
  simpa using wt_smul_single (k := n + 1) (c := (1 : ZMod 3)) one_ne_zero a

private theorem monoCount_orbN_of_wt_one {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    {w : Coords (n + 1)} (hw : wt w = 1) : OrbN Xg w := by
  refine orbN_of_wt_eq_of_fk hFK orbN_e0 ?_
  rw [hw, monoCount_wt_single (0 : Fin (n + 1))]

private theorem monoCount_orbN_of_wt_two {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    {u : Coords (n + 1)} (hu : OrbN Xg u) (hu2 : wt u = 2) {w : Coords (n + 1)}
    (hw : wt w = 2) : OrbN Xg w := by
  refine orbN_of_wt_eq_of_fk hFK hu ?_
  rw [hw, hu2]

private theorem monoCount_orbN_of_wt_full {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    {u : Coords (n + 1)} (hu : OrbN Xg u) (hfull : wt u = n + 1) {w : Coords (n + 1)}
    (hw : wt w = n + 1) : OrbN Xg w := by
  refine orbN_of_wt_eq_of_fk hFK hu ?_
  rw [hw, hfull]

private theorem monoCount_mulVec_injective (A : GL (Fin (n + 1)) (ZMod 3)) :
    Function.Injective fun z : Coords (n + 1) =>
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z := by
  intro z z' h
  have h1 := congrArg (fun t => ((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ t) h
  rwa [gl_inv_mulVec_mulVec, gl_inv_mulVec_mulVec] at h1

private theorem monoCount_pigeonhole {m m' : ℕ} (hm : m' < m)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hM : ∀ z z' : Coords (n + 1), M *ᵥ z = M *ᵥ z' → z = z')
    {r : Fin m → Coords (n + 1)} {y : Fin m' → Coords (n + 1)}
    (hcover : ∀ i, ∃ j : Fin m', M *ᵥ r i = y j ∨ M *ᵥ r i = -(y j))
    (hne : ∀ i i', i ≠ i' → r i ≠ r i' ∧ r i ≠ -(r i')) : False := by
  classical
  have hcard : Fintype.card (Fin m') < Fintype.card (Fin m) := by simpa using hm
  let f : Fin m → Fin m' := fun i => (hcover i).choose
  have hf : ∀ i, M *ᵥ r i = y (f i) ∨ M *ᵥ r i = -(y (f i)) := fun i => (hcover i).choose_spec
  obtain ⟨i, i', hii, hff⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hi := hf i
  have hi' := hf i'
  rw [← hff] at hi'
  rcases hi with hi | hi <;> rcases hi' with hi' | hi'
  · exact (hne i i' hii).1 (hM _ _ (hi.trans hi'.symm))
  · refine (hne i i' hii).2 (hM _ _ ?_)
    rw [hi, Matrix.mulVec_neg, hi', neg_neg]
  · refine (hne i i' hii).2 (hM _ _ ?_)
    rw [hi, Matrix.mulVec_neg, hi']
  · exact (hne i i' hii).1 (hM _ _ (hi.trans hi'.symm))

private theorem monoCount_zmod3_trichotomy (c : ZMod 3) : c = 0 ∨ c = 1 ∨ c = -1 := by
  revert c
  decide

private theorem monoCount_pair_nz (c d : ZMod 3) :
    (c ≠ 0 ∧ d ≠ 0) ∨ (1 + c ≠ 0 ∧ 1 + d ≠ 0) ∨ (1 - c ≠ 0 ∧ 1 - d ≠ 0) := by
  revert c d
  decide

private theorem monoCount_zero_triple (c : ZMod 3) : c = 0 ∨ 1 + c = 0 ∨ 1 - c = 0 := by
  revert c
  decide

private theorem monoCount_wt_ge_three {u : Coords (n + 1)} {a b c : Fin (n + 1)}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : u a ≠ 0) (hb : u b ≠ 0) (hc : u c ≠ 0) : 3 ≤ wt u := by
  rw [wt]
  have hsub : ({a, b, c} : Finset (Fin (n + 1))) ⊆ Finset.univ.filter (fun j => u j ≠ 0) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have h3 : ({a, b, c} : Finset (Fin (n + 1))).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have := Finset.card_le_card hsub
  omega

private theorem monoCount_wt_ge_pred (h01 : (0 : Fin (n + 1)) ≠ 1) {u : Coords (n + 1)}
    (h : ∀ j, j ≠ 0 → j ≠ 1 → u j ≠ 0) : n + 1 - 2 ≤ wt u := by
  rw [wt]
  have hsub : (Finset.univ \ ({0, 1} : Finset (Fin (n + 1)))) ⊆
      Finset.univ.filter (fun j => u j ≠ 0) := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, h j ?_ ?_⟩
    · intro h0
      exact hj.2 (h0 ▸ Finset.mem_insert_self _ _)
    · intro h1
      exact hj.2 (h1 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff (s := ({0, 1} : Finset (Fin (n + 1)))) (t := Finset.univ),
    Finset.inter_univ, Finset.card_univ, Fintype.card_fin, Finset.card_pair h01] at hcard
  omega

private theorem monoCount_P_classify {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg)
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    (hn : 4 ≤ n) {w : Coords (n + 1)} (hw : OrbN Xg w)
    (hp : OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 + w))
    (hm : OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 - w)) :
    w = Pi.single (0 : Fin (n + 1)) 1 ∨ w = -Pi.single (0 : Fin (n + 1)) 1 ∨
      w = Pi.single (1 : Fin (n + 1)) 1 ∨ w = -Pi.single (1 : Fin (n + 1)) 1 ∨
      w = Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1 ∨
      w = -(Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1) := by
  classical
  let v : Coords (n + 1) := Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1
  have h01 : (0 : Fin (n + 1)) ≠ 1 :=
    monoCount_fin_ne (n := n) (a := 0) (b := 1) (by omega) (by omega) (by decide)
  have h10 : (1 : Fin (n + 1)) ≠ 0 := h01.symm
  have hv0 : v 0 = (1 : ZMod 3) := by
    simp [v, Pi.add_apply, Pi.single_apply, h01]
  have hv1 : v 1 = (1 : ZMod 3) := by
    simp [v, Pi.add_apply, Pi.single_apply, h10]
  have hvz : ∀ j : Fin (n + 1), j ≠ 0 → j ≠ 1 → v j = 0 := by
    intro j hj0 hj1
    simp [v, Pi.add_apply, Pi.single_apply, hj0, hj1]
  have hvwt : wt v = 2 := by
    change wt (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1) = 2
    simpa using wt_single_add_single (i := (0 : Fin (n + 1))) (j := (1 : Fin (n + 1))) h01
      one_ne_zero one_ne_zero
  have hw1 : wt w = 1 ∨ wt w = 2 ∨ wt w = n + 1 := MonoN0Hyp.wt_orbN h hFK hw
  have hw2 : wt (v + w) = 1 ∨ wt (v + w) = 2 ∨ wt (v + w) = n + 1 :=
    MonoN0Hyp.wt_orbN h hFK hp
  have hw3 : wt (v - w) = 1 ∨ wt (v - w) = 2 ∨ wt (v - w) = n + 1 :=
    MonoN0Hyp.wt_orbN h hFK hm
  have hsupp : ∀ j : Fin (n + 1), j ≠ 0 → j ≠ 1 → w j = 0 := by
    intro j hj0 hj1
    by_contra hj
    have hAll : ∀ j' : Fin (n + 1), j' ≠ 0 → j' ≠ 1 → w j' ≠ 0 := by
      intro j' hj0' hj1'
      rcases monoCount_pair_nz (w 0) (w 1) with hc | hc | hc
      · have hge : 3 ≤ wt w :=
          monoCount_wt_ge_three h01 (Ne.symm hj0) (Ne.symm hj1) hc.1 hc.2 hj
        have hf : wt w = n + 1 := by rcases hw1 with h1 | h1 | h1 <;> omega
        exact (wt_eq_iff_forall_ne_zero w).mp hf j'
      · have hge : 3 ≤ wt (v + w) := by
          refine monoCount_wt_ge_three h01 (Ne.symm hj0) (Ne.symm hj1) ?_ ?_ ?_
          · rw [Pi.add_apply, hv0]; exact hc.1
          · rw [Pi.add_apply, hv1]; exact hc.2
          · rw [Pi.add_apply, hvz j hj0 hj1, zero_add]; exact hj
        have hf : wt (v + w) = n + 1 := by rcases hw2 with h1 | h1 | h1 <;> omega
        have h' : (v + w) j' ≠ 0 := (wt_eq_iff_forall_ne_zero (v + w)).mp hf j'
        rwa [Pi.add_apply, hvz j' hj0' hj1', zero_add] at h'
      · have hge : 3 ≤ wt (v - w) := by
          refine monoCount_wt_ge_three h01 (Ne.symm hj0) (Ne.symm hj1) ?_ ?_ ?_
          · rw [Pi.sub_apply, hv0]; exact hc.1
          · rw [Pi.sub_apply, hv1]; exact hc.2
          · rw [Pi.sub_apply, hvz j hj0 hj1, zero_sub]; exact neg_ne_zero.mpr hj
        have hf : wt (v - w) = n + 1 := by rcases hw3 with h1 | h1 | h1 <;> omega
        have h' : (v - w) j' ≠ 0 := (wt_eq_iff_forall_ne_zero (v - w)).mp hf j'
        rw [Pi.sub_apply, hvz j' hj0' hj1', zero_sub] at h'
        exact neg_ne_zero.mp h'
    have hf1 : wt w = n + 1 := by
      have hge : n + 1 - 2 ≤ wt w := monoCount_wt_ge_pred h01 hAll
      rcases hw1 with h1 | h1 | h1 <;> omega
    have hf2 : wt (v + w) = n + 1 := by
      have hge : n + 1 - 2 ≤ wt (v + w) := monoCount_wt_ge_pred h01 (fun j' j0 j1 => by
        rw [Pi.add_apply, hvz j' j0 j1, zero_add]
        exact hAll j' j0 j1)
      rcases hw2 with h1 | h1 | h1 <;> omega
    have hf3 : wt (v - w) = n + 1 := by
      have hge : n + 1 - 2 ≤ wt (v - w) := monoCount_wt_ge_pred h01 (fun j' j0 j1 => by
        rw [Pi.sub_apply, hvz j' j0 j1, zero_sub]
        exact neg_ne_zero.mpr (hAll j' j0 j1))
      rcases hw3 with h1 | h1 | h1 <;> omega
    have hz1 : w 0 ≠ 0 := (wt_eq_iff_forall_ne_zero w).mp hf1 0
    have hz2 : (v + w) 0 ≠ 0 := (wt_eq_iff_forall_ne_zero (v + w)).mp hf2 0
    have hz3 : (v - w) 0 ≠ 0 := (wt_eq_iff_forall_ne_zero (v - w)).mp hf3 0
    rw [Pi.add_apply, hv0] at hz2
    rw [Pi.sub_apply, hv0] at hz3
    rcases monoCount_zero_triple (w 0) with h0 | h0 | h0
    · exact hz1 h0
    · exact hz2 h0
    · exact hz3 h0
  have hwdec : w = w 0 • Pi.single (0 : Fin (n + 1)) 1 +
      w 1 • Pi.single (1 : Fin (n + 1)) 1 := by
    funext k
    by_cases hk0 : k = 0
    · subst hk0
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, h01]
    · by_cases hk1 : k = 1
      · subst hk1
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, h10]
      · rw [hsupp k hk0 hk1]
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hk0, hk1]
  have hwne : w ≠ 0 := orbN_ne_zero hw
  rcases monoCount_zmod3_trichotomy (w 0) with hc | hc | hc <;>
    rcases monoCount_zmod3_trichotomy (w 1) with hd | hd | hd
  · exfalso
    apply hwne
    rw [hwdec, hc, hd]
    simp
  · exact Or.inr (Or.inr (Or.inl (by
      rw [hwdec, hc, hd]; simp only [zero_smul, one_smul, neg_smul]; abel)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by
      rw [hwdec, hc, hd]; simp only [zero_smul, one_smul, neg_smul]; abel))))
  · exact Or.inl (by rw [hwdec, hc, hd]; simp only [zero_smul, one_smul, neg_smul]; abel)
  · exfalso
    have hveq : w = Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 := by
      rw [hwdec, hc, hd]; simp
    have hzero : Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 - w = 0 := by
      rw [hveq]; abel
    exact orbN_ne_zero (by simpa [hzero] using hm) rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      rw [hwdec, hc, hd]; simp only [zero_smul, one_smul, neg_smul]; abel)))))
  · exact Or.inr (Or.inl (by
      rw [hwdec, hc, hd]; simp only [zero_smul, one_smul, neg_smul]; abel))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      rw [hwdec, hc, hd]; simp only [zero_smul, one_smul, neg_smul]; abel)))))
  · exfalso
    have hveq : w = -(Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1) := by
      rw [hwdec, hc, hd]; simp only [one_smul, neg_smul]; abel
    have hzero : Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 + w = 0 := by
      rw [hveq]; abel
    exact orbN_ne_zero (by simpa [hzero] using hp) rfl

private theorem monoCount_wt_flip (S : Finset (Fin (n + 1))) :
    wt (fun j : Fin (n + 1) => if j ∈ S then (-1 : ZMod 3) else 1) = n + 1 := by
  rw [wt_eq_iff_forall_ne_zero]
  intro j
  split_ifs <;> decide

private theorem monoCount_wt_add_flip (S : Finset (Fin (n + 1))) :
    wt (fun j : Fin (n + 1) => (1 : ZMod 3) + (if j ∈ S then -1 else 1)) = n + 1 - S.card := by
  rw [wt]
  have hset : (Finset.univ.filter fun j : Fin (n + 1) =>
      (1 : ZMod 3) + (if j ∈ S then -1 else 1) ≠ 0) = Finset.univ \ S := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    by_cases hj : j ∈ S
    · have h1 : (1 : ZMod 3) + (if j ∈ S then -1 else 1) = 0 := by simp [hj]
      simp [h1, hj]
    · have h1 : (1 : ZMod 3) + (if j ∈ S then -1 else 1) = 1 + 1 := by simp [hj]
      have h2 : (1 : ZMod 3) + 1 ≠ 0 := by decide
      simp [h1, h2, hj]
  rw [hset, Finset.card_sdiff (s := S) (t := Finset.univ), Finset.inter_univ,
    Finset.card_univ, Fintype.card_fin]

private theorem monoCount_wt_sub_flip (S : Finset (Fin (n + 1))) :
    wt (fun j : Fin (n + 1) => (1 : ZMod 3) - (if j ∈ S then -1 else 1)) = S.card := by
  rw [wt]
  have hset : (Finset.univ.filter fun j : Fin (n + 1) =>
      (1 : ZMod 3) - (if j ∈ S then -1 else 1) ≠ 0) = S := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j ∈ S
    · have h1 : (1 : ZMod 3) - (if j ∈ S then -1 else 1) = 1 + 1 := by
        rw [if_pos hj]; decide
      have h2 : (1 : ZMod 3) + 1 ≠ 0 := by decide
      simp [h1, h2, hj]
    · have h1 : (1 : ZMod 3) - (if j ∈ S then -1 else 1) = 0 := by simp [hj]
      simp [h1, hj]
  rw [hset]

private theorem monoCount_neg_flip (S : Finset (Fin (n + 1))) :
    -(fun j : Fin (n + 1) => if j ∈ S then (-1 : ZMod 3) else 1) =
      fun j => if j ∈ Sᶜ then -1 else 1 := by
  funext j
  simp only [Pi.neg_apply, Finset.mem_compl]
  by_cases hj : j ∈ S <;> simp [hj]

private theorem monoCount_flip_inj {S T : Finset (Fin (n + 1))}
    (h : (fun j : Fin (n + 1) => if j ∈ S then (-1 : ZMod 3) else 1) =
      fun j => if j ∈ T then -1 else 1) : S = T := by
  ext j
  have hj := congrFun h j
  change (if j ∈ S then (-1 : ZMod 3) else 1) = (if j ∈ T then -1 else 1) at hj
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
    simp_all [show (1 : ZMod 3) ≠ -1 from by decide, show (-1 : ZMod 3) ≠ 1 from by decide]

private theorem monoCount_eq_smul_single_of_wt_one {w : Coords (n + 1)} (hw : wt w = 1) :
    ∃ (i : Fin (n + 1)) (c : ZMod 3), c ≠ 0 ∧ w = c • Pi.single i 1 := by
  rw [wt] at hw
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hw
  have hwi : w i ≠ 0 := by
    have : i ∈ Finset.univ.filter (fun j => w j ≠ 0) := by
      rw [hi]; exact Finset.mem_singleton_self i
    exact (Finset.mem_filter.mp this).2
  refine ⟨i, w i, hwi, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Pi.smul_apply, smul_eq_mul]
  · have hwj : w j = 0 := by
      by_contra h
      have hmem : j ∈ Finset.univ.filter (fun j => w j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
      rw [hi] at hmem
      exact hj (Finset.mem_singleton.mp hmem)
    simp [Pi.smul_apply, smul_eq_mul, Pi.single_apply, hj, hwj]

private theorem monoCount_N_e0 {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg)
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    (h2 : ∀ v, OrbN Xg v → wt v ≠ 2) {u : Coords (n + 1)} (hu : OrbN Xg u)
    (hfull : wt u = n + 1) {w : Coords (n + 1)} (hw : OrbN Xg w)
    (hne1 : w ≠ Pi.single (0 : Fin (n + 1)) 1) (hne2 : w ≠ -Pi.single (0 : Fin (n + 1)) 1)
    (hp : ¬ OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 + w))
    (hm : ¬ OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 - w)) :
    ∃ k : Fin (n + 1), k ≠ 0 ∧ (w = Pi.single k 1 ∨ w = -Pi.single k 1) := by
  classical
  have h1 : wt w = 1 ∨ wt w = 2 ∨ wt w = n + 1 := MonoN0Hyp.wt_orbN h hFK hw
  have hwt : wt w = 1 := by
    rcases h1 with h1 | h1 | h1
    · exact h1
    · exact absurd h1 (h2 w hw)
    · exfalso
      have hall : ∀ i, w i ≠ 0 := (wt_eq_iff_forall_ne_zero w).mp h1
      have hw0 : w 0 = 1 ∨ w 0 = -1 := eq_one_or_of_ne_zero (hall 0)
      rcases hw0 with hw0 | hw0
      · apply hp
        apply monoCount_orbN_of_wt_full hFK hu hfull
        rw [wt_eq_iff_forall_ne_zero]
        intro i
        by_cases hi : i = 0
        · subst hi
          rw [Pi.add_apply, Pi.single_eq_same, hw0]
          decide
        · rw [Pi.add_apply, Pi.single_eq_of_ne hi 1, zero_add]
          exact hall i
      · apply hm
        apply monoCount_orbN_of_wt_full hFK hu hfull
        rw [wt_eq_iff_forall_ne_zero]
        intro i
        by_cases hi : i = 0
        · subst hi
          rw [Pi.sub_apply, Pi.single_eq_same, hw0]
          decide
        · rw [Pi.sub_apply, Pi.single_eq_of_ne hi 1, zero_sub]
          exact neg_ne_zero.mpr (hall i)
  obtain ⟨k, c, hc0, hwk⟩ := monoCount_eq_smul_single_of_wt_one hwt
  refine ⟨k, ?_, ?_⟩
  · intro hk
    subst hk
    rcases eq_one_or_of_ne_zero hc0 with hc | hc
    · exact hne1 (by rw [hwk, hc, one_smul])
    · apply hne2
      rw [hwk, hc, neg_smul, one_smul]
  · rcases eq_one_or_of_ne_zero hc0 with hc | hc
    · exact Or.inl (by rw [hwk, hc, one_smul])
    · exact Or.inr (by rw [hwk, hc, neg_smul, one_smul])

namespace MonoN0Hyp

variable {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))} (h : MonoN0Hyp Xg)
include h

theorem false_of_orbN_wt_two (hn : 4 ≤ n)
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    {u : Fin (n + 1) → ZMod 3} (hu : OrbN Xg u) (hu2 : wt u = 2) : False := by
  classical
  have h01 : (0 : Fin (n + 1)) ≠ 1 :=
    monoCount_fin_ne (n := n) (a := 0) (b := 1) (by omega) (by omega) (by decide)
  have h10 : (1 : Fin (n + 1)) ≠ 0 := h01.symm
  have h02 : (0 : Fin (n + 1)) ≠ 2 :=
    monoCount_fin_ne (n := n) (a := 0) (b := 2) (by omega) (by omega) (by decide)
  have h12 : (1 : Fin (n + 1)) ≠ 2 :=
    monoCount_fin_ne (n := n) (a := 1) (b := 2) (by omega) (by omega) (by decide)
  have hwt_e0e1 : wt (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1) = 2 := by
    simpa using wt_single_add_single (i := (0 : Fin (n + 1))) (j := (1 : Fin (n + 1))) h01
      one_ne_zero one_ne_zero
  have hwt_e0se1 : wt (Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1) = 2 := by
    simpa using wt_single_sub_single (i := (0 : Fin (n + 1))) (j := (1 : Fin (n + 1))) h01
      one_ne_zero one_ne_zero
  have hwt_e0e2 : wt (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (2 : Fin (n + 1)) 1) = 2 := by
    simpa using wt_single_add_single (i := (0 : Fin (n + 1))) (j := (2 : Fin (n + 1))) h02
      one_ne_zero one_ne_zero
  have hwt_e0se2 : wt (Pi.single (0 : Fin (n + 1)) 1 - Pi.single (2 : Fin (n + 1)) 1) = 2 := by
    simpa using wt_single_sub_single (i := (0 : Fin (n + 1))) (j := (2 : Fin (n + 1))) h02
      one_ne_zero one_ne_zero
  have hv : OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1) :=
    monoCount_orbN_of_wt_two hFK hu hu2 hwt_e0e1
  have he0e0 : (Pi.single (0 : Fin (n + 1)) (1 : ZMod 3) +
      Pi.single (0 : Fin (n + 1)) 1 : Coords (n + 1)) = -Pi.single (0 : Fin (n + 1)) 1 := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp only [Pi.add_apply, Pi.neg_apply, Pi.single_eq_same]
      decide
    · rw [Pi.add_apply, Pi.neg_apply, Pi.single_eq_of_ne hk 1]
      decide
  have hid1 : (Pi.single (0 : Fin (n + 1)) 1 +
      (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1) : Coords (n + 1)) =
      -(Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1) := by
    rw [← add_assoc, he0e0]
    abel
  have hid2 : (Pi.single (0 : Fin (n + 1)) 1 -
      (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1) : Coords (n + 1)) =
      -Pi.single (1 : Fin (n + 1)) 1 := by
    abel
  have hid3 : (Pi.single (0 : Fin (n + 1)) 1 +
      (Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1) : Coords (n + 1)) =
      -(Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1) := by
    rw [show (Pi.single (0 : Fin (n + 1)) 1 +
      (Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1) : Coords (n + 1)) =
      (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (0 : Fin (n + 1)) 1) -
        Pi.single (1 : Fin (n + 1)) 1 from by abel, he0e0]
    abel
  have hid4 : (Pi.single (0 : Fin (n + 1)) 1 -
      (Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1) : Coords (n + 1)) =
      Pi.single (1 : Fin (n + 1)) 1 := by
    abel
  let r : Fin 4 → Coords (n + 1) := fun i =>
    Fin.cases (motive := fun _ => Coords (n + 1))
      (Pi.single (1 : Fin (n + 1)) 1)
      (fun i1 => Fin.cases (motive := fun _ => Coords (n + 1))
        (Pi.single (2 : Fin (n + 1)) 1)
        (fun i2 => Fin.cases (motive := fun _ => Coords (n + 1))
          (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1)
          (fun _ => Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1)
          i2)
        i1)
      i
  let y : Fin 3 → Coords (n + 1) := fun k =>
    Fin.cases (motive := fun _ => Coords (n + 1))
      (Pi.single (0 : Fin (n + 1)) 1)
      (fun i1 => Fin.cases (motive := fun _ => Coords (n + 1))
        (Pi.single (1 : Fin (n + 1)) 1)
        (fun _ => Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1)
        i1)
      k
  have hmem : ∀ i : Fin 4, OrbN Xg (r i) ∧
      OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 + r i) ∧
      OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 - r i) := by
    intro i
    fin_cases i
    · exact ⟨monoCount_orbN_of_wt_one hFK (monoCount_wt_single (1 : Fin (n + 1))), hv,
        monoCount_orbN_of_wt_two hFK hu hu2 hwt_e0se1⟩
    · exact ⟨monoCount_orbN_of_wt_one hFK (monoCount_wt_single (2 : Fin (n + 1))),
        monoCount_orbN_of_wt_two hFK hu hu2 hwt_e0e2,
        monoCount_orbN_of_wt_two hFK hu hu2 hwt_e0se2⟩
    · refine ⟨hv, ?_, ?_⟩
      · show OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 +
          (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1))
        rw [hid1]
        exact MonoN0Hyp.orbN_neg h (monoCount_orbN_of_wt_two hFK hu hu2 hwt_e0se1)
      · show OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 -
          (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1))
        rw [hid2]
        exact MonoN0Hyp.orbN_neg h (monoCount_orbN_of_wt_one hFK
          (monoCount_wt_single (1 : Fin (n + 1))))
    · refine ⟨monoCount_orbN_of_wt_two hFK hu hu2 hwt_e0se1, ?_, ?_⟩
      · show OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 +
          (Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1))
        rw [hid3]
        exact MonoN0Hyp.orbN_neg h hv
      · show OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 -
          (Pi.single (0 : Fin (n + 1)) 1 - Pi.single (1 : Fin (n + 1)) 1))
        rw [hid4]
        exact monoCount_orbN_of_wt_one hFK (monoCount_wt_single (1 : Fin (n + 1)))
  let Q : Fin 4 → ZMod 3 × ZMod 3 := fun i =>
    Fin.cases (motive := fun _ => ZMod 3 × ZMod 3) (0, 1)
      (fun i1 => Fin.cases (motive := fun _ => ZMod 3 × ZMod 3) (0, 0)
        (fun i2 => Fin.cases (motive := fun _ => ZMod 3 × ZMod 3) (1, 1)
          (fun _ => (1, -1)) i2)
        i1)
      i
  have hq : ∀ i : Fin 4, (r i 0, r i 1) = Q i := by
    intro i
    fin_cases i
    · show ((Pi.single (1 : Fin (n + 1)) (1 : ZMod 3) : Coords (n + 1)) 0,
          (Pi.single (1 : Fin (n + 1)) (1 : ZMod 3) : Coords (n + 1)) 1) = (0, 1)
      simp [Pi.single_apply, h01]
    · show ((Pi.single (2 : Fin (n + 1)) (1 : ZMod 3) : Coords (n + 1)) 0,
          (Pi.single (2 : Fin (n + 1)) (1 : ZMod 3) : Coords (n + 1)) 1) = (0, 0)
      simp [Pi.single_apply, h02, h12]
    · show ((Pi.single (0 : Fin (n + 1)) (1 : ZMod 3) +
          Pi.single (1 : Fin (n + 1)) (1 : ZMod 3) : Coords (n + 1)) 0,
          (Pi.single (0 : Fin (n + 1)) (1 : ZMod 3) +
          Pi.single (1 : Fin (n + 1)) (1 : ZMod 3) : Coords (n + 1)) 1) = (1, 1)
      simp [Pi.add_apply, Pi.single_apply, h01, h10]
    · show ((Pi.single (0 : Fin (n + 1)) (1 : ZMod 3) -
          Pi.single (1 : Fin (n + 1)) (1 : ZMod 3) : Coords (n + 1)) 0,
          (Pi.single (0 : Fin (n + 1)) (1 : ZMod 3) -
          Pi.single (1 : Fin (n + 1)) (1 : ZMod 3) : Coords (n + 1)) 1) = (1, -1)
      simp [Pi.sub_apply, Pi.single_apply, h01, h10]
  have hQ : ∀ i i' : Fin 4, i ≠ i' → Q i ≠ Q i' ∧ Q i ≠ -Q i' := by
    decide
  have hne : ∀ i i' : Fin 4, i ≠ i' → r i ≠ r i' ∧ r i ≠ -(r i') := by
    intro i i' hii
    obtain ⟨hQ1, hQ2⟩ := hQ i i' hii
    constructor
    · intro hrs
      apply hQ1
      have h2 : (r i 0, r i 1) = (r i' 0, r i' 1) := by rw [hrs]
      rwa [hq i, hq i'] at h2
    · intro hrs
      apply hQ2
      have h2 : (r i 0, r i 1) = -(r i' 0, r i' 1) := by
        rw [hrs]
        simp [Pi.neg_apply]
      rwa [hq i, hq i'] at h2
  obtain ⟨x, hxX, hxe⟩ := hv
  have hcover : ∀ i : Fin 4, ∃ j : Fin 3,
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i = y j ∨
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i = -(y j) := by
    intro i
    obtain ⟨hz, hzp, hzm⟩ := hmem i
    have h1 : OrbN Xg ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i) :=
      orbN_mulVec hz hxX
    have h2 : OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 +
        (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i) := by
      have e : (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 +
          (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i) =
          (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
            (Pi.single (0 : Fin (n + 1)) 1 + r i) := by
        rw [Matrix.mulVec_add, hxe]
      rw [e]
      exact orbN_mulVec hzp hxX
    have h3 : OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 -
        (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i) := by
      have e : (Pi.single (0 : Fin (n + 1)) 1 + Pi.single (1 : Fin (n + 1)) 1 -
          (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i) =
          (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
            (Pi.single (0 : Fin (n + 1)) 1 - r i) := by
        rw [Matrix.mulVec_sub, hxe]
      rw [e]
      exact orbN_mulVec hzm hxX
    have hj := monoCount_P_classify h hFK hn h1 h2 h3
    rcases hj with hj | hj | hj | hj | hj | hj
    · exact ⟨0, Or.inl (hj : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i =
        y 0)⟩
    · exact ⟨0, Or.inr (hj : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i =
        -(y 0))⟩
    · exact ⟨1, Or.inl (hj : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i =
        y 1)⟩
    · exact ⟨1, Or.inr (hj : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i =
        -(y 1))⟩
    · exact ⟨2, Or.inl (hj : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i =
        y 2)⟩
    · exact ⟨2, Or.inr (hj : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ r i =
        -(y 2))⟩
  exact monoCount_pigeonhole (n := n) (m := 4) (m' := 3) (by norm_num)
    (show ∀ z z' : Coords (n + 1),
        (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z =
          (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z' → z = z' from
      monoCount_mulVec_injective x) hcover hne

theorem false_of_orbN_wt_full (hn : 4 ≤ n)
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    (h2 : ∀ v, OrbN Xg v → wt v ≠ 2) {u : Fin (n + 1) → ZMod 3} (hu : OrbN Xg u)
    (hfull : wt u = n + 1) : False := by
  classical
  have h01 : (0 : Fin (n + 1)) ≠ 1 :=
    monoCount_fin_ne (n := n) (a := 0) (b := 1) (by omega) (by omega) (by decide)
  have h02 : (0 : Fin (n + 1)) ≠ 2 :=
    monoCount_fin_ne (n := n) (a := 0) (b := 2) (by omega) (by omega) (by decide)
  have h12 : (1 : Fin (n + 1)) ≠ 2 :=
    monoCount_fin_ne (n := n) (a := 1) (b := 2) (by omega) (by omega) (by decide)
  let beta : Coords (n + 1) := fun _ => 1
  have hbetawt : wt beta = n + 1 := by
    rw [wt_eq_iff_forall_ne_zero]
    intro i
    exact one_ne_zero
  have hbeta : OrbN Xg beta := monoCount_orbN_of_wt_full hFK hu hfull hbetawt
  obtain ⟨x, hxX, hxe⟩ := hbeta
  have hxinv : x⁻¹ ∈ Xg := Xg.inv_mem hxX
  let S : Fin (n + 1) → Finset (Fin (n + 1)) := fun i => if i = 0 then {1, 2} else {0, i}
  let r : Fin (n + 1) → Coords (n + 1) := fun i j => if j ∈ S i then (-1 : ZMod 3) else 1
  let y : Fin n → Coords (n + 1) := fun j => Pi.single (Fin.succ j) 1
  have hScard : ∀ i : Fin (n + 1), (S i).card = 2 := by
    intro i
    by_cases hi : i = 0
    · have hS : S i = ({1, 2} : Finset (Fin (n + 1))) := by simp [S, hi]
      rw [hS]
      exact Finset.card_pair h12
    · have hS : S i = ({0, i} : Finset (Fin (n + 1))) := by simp [S, hi]
      rw [hS]
      exact Finset.card_pair (Ne.symm hi)
  have hSi : ∀ i i' : Fin (n + 1), i ≠ i' → S i ≠ S i' := by
    intro i i' hii heq
    by_cases hi : i = 0
    · subst hi
      have hi' : i' ≠ 0 := fun h => hii h.symm
      have hmem : (0 : Fin (n + 1)) ∈ S i' := by
        have hS : S i' = ({0, i'} : Finset (Fin (n + 1))) := by simp [S, hi']
        rw [hS]
        exact Finset.mem_insert_self _ _
      rw [← heq] at hmem
      have hS0 : S 0 = ({1, 2} : Finset (Fin (n + 1))) := by simp [S]
      rw [hS0] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact h01 h
      · exact h02 h
    · by_cases hi' : i' = 0
      · subst hi'
        have hmem : (0 : Fin (n + 1)) ∈ S i := by
          have hS : S i = ({0, i} : Finset (Fin (n + 1))) := by simp [S, hi]
          rw [hS]
          exact Finset.mem_insert_self _ _
        rw [heq] at hmem
        have hS0 : S 0 = ({1, 2} : Finset (Fin (n + 1))) := by simp [S]
        rw [hS0] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact h01 h
        · exact h02 h
      · have hmem : i ∈ S i := by
          have hS : S i = ({0, i} : Finset (Fin (n + 1))) := by simp [S, hi]
          rw [hS]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self i)
        rw [heq] at hmem
        have hS' : S i' = ({0, i'} : Finset (Fin (n + 1))) := by simp [S, hi']
        rw [hS'] at hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hi h
        · exact hii (Finset.mem_singleton.mp h)
  have hSnc : ∀ i i' : Fin (n + 1), S i ≠ (S i')ᶜ := by
    intro i i' heq
    have h : ((S i')ᶜ).card = 2 := by rw [← heq]; exact hScard i
    rw [Finset.card_compl, Fintype.card_fin, hScard i'] at h
    omega
  have hsep : ∀ i i' : Fin (n + 1), i ≠ i' → r i ≠ r i' ∧ r i ≠ -(r i') := by
    intro i i' hii
    have h1 : S i ≠ S i' := hSi i i' hii
    have h2 : S i ≠ (S i')ᶜ := hSnc i i'
    constructor
    · intro hrs
      apply h1
      apply monoCount_flip_inj
      exact hrs
    · intro hrs
      apply h2
      apply monoCount_flip_inj
      have he : (fun j : Fin (n + 1) => if j ∈ S i then (-1 : ZMod 3) else 1) =
          -(fun j => if j ∈ S i' then -1 else 1) := hrs
      rw [monoCount_neg_flip (S i')] at he
      exact he
  have hrne : ∀ i : Fin (n + 1), r i ≠ beta ∧ r i ≠ -beta := by
    intro i
    constructor
    · intro hrs
      obtain ⟨j, hj⟩ : (S i).Nonempty :=
        Finset.card_pos.mp (by rw [hScard i]; norm_num)
      have h1 : r i j = -1 := by simp [r, hj]
      rw [hrs] at h1
      have h2 : beta j = 1 := rfl
      rw [h2] at h1
      exact absurd h1 (by decide)
    · intro hrs
      obtain ⟨j, hj⟩ : ((S i)ᶜ).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_compl, Fintype.card_fin, hScard i]
        omega)
      have h1 : r i j = 1 := by
        have hjs : j ∉ S i := Finset.mem_compl.mp hj
        simp [r, hjs]
      rw [hrs] at h1
      have h2 : (-beta) j = -1 := by simp [beta]
      rw [h2] at h1
      exact absurd h1 (by decide)
  have hrp : ∀ i : Fin (n + 1), ¬ OrbN Xg (beta + r i) := by
    intro i hcon
    have hwt : wt (beta + r i) = n + 1 - (S i).card := monoCount_wt_add_flip (S i)
    have h1 : wt (beta + r i) = 1 ∨ wt (beta + r i) = 2 ∨ wt (beta + r i) = n + 1 :=
      MonoN0Hyp.wt_orbN h hFK hcon
    rw [hwt, hScard i] at h1
    rcases h1 with h1 | h1 | h1 <;> omega
  have hrm : ∀ i : Fin (n + 1), ¬ OrbN Xg (beta - r i) := by
    intro i hcon
    have hwt : wt (beta - r i) = (S i).card := monoCount_wt_sub_flip (S i)
    exact h2 (beta - r i) hcon (by rw [hwt, hScard i])
  let xi : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3) :=
    ((x⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))
  have hcover : ∀ i : Fin (n + 1), ∃ j : Fin n, xi *ᵥ r i = y j ∨ xi *ᵥ r i = -(y j) := by
    intro i
    have hror : OrbN Xg (r i) :=
      monoCount_orbN_of_wt_full hFK hu hfull (monoCount_wt_flip (S i))
    have hwor : OrbN Xg (xi *ᵥ r i) := orbN_mulVec hror hxinv
    have hwne1 : xi *ᵥ r i ≠ Pi.single (0 : Fin (n + 1)) 1 := by
      intro h
      apply (hrne i).1
      have h' : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ (xi *ᵥ r i) = r i :=
        gl_mulVec_inv_mulVec x (r i)
      rw [h, hxe] at h'
      exact h'.symm
    have hwne2 : xi *ᵥ r i ≠ -Pi.single (0 : Fin (n + 1)) 1 := by
      intro h
      apply (hrne i).2
      have h' : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ (xi *ᵥ r i) = r i :=
        gl_mulVec_inv_mulVec x (r i)
      rw [h, Matrix.mulVec_neg, hxe] at h'
      exact h'.symm
    have hwp : ¬ OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 + xi *ᵥ r i) := by
      intro hcon
      apply hrp i
      have h' : OrbN Xg ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          (Pi.single (0 : Fin (n + 1)) 1 + xi *ᵥ r i)) := orbN_mulVec hcon hxX
      have e : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          (Pi.single (0 : Fin (n + 1)) 1 + xi *ᵥ r i) = beta + r i := by
        rw [Matrix.mulVec_add, hxe, gl_mulVec_inv_mulVec]
      rwa [e] at h'
    have hwm : ¬ OrbN Xg (Pi.single (0 : Fin (n + 1)) 1 - xi *ᵥ r i) := by
      intro hcon
      apply hrm i
      have h' : OrbN Xg ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          (Pi.single (0 : Fin (n + 1)) 1 - xi *ᵥ r i)) := orbN_mulVec hcon hxX
      have e : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          (Pi.single (0 : Fin (n + 1)) 1 - xi *ᵥ r i) = beta - r i := by
        rw [Matrix.mulVec_sub, hxe, gl_mulVec_inv_mulVec]
      rwa [e] at h'
    obtain ⟨k, hk0, hk | hk⟩ :=
      monoCount_N_e0 h hFK h2 hu hfull hwor hwne1 hwne2 hwp hwm
    · obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hk0
      rw [← hj] at hk
      exact ⟨j, Or.inl hk⟩
    · obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hk0
      rw [← hj] at hk
      exact ⟨j, Or.inr hk⟩
  exact monoCount_pigeonhole (n := n) (m := n + 1) (m' := n) (Nat.lt_succ_self n)
    (show ∀ z z' : Coords (n + 1), xi *ᵥ z = xi *ᵥ z' → z = z' from
      monoCount_mulVec_injective x⁻¹) hcover hsep

end MonoN0Hyp

end CFSG.StandardType.FrameRoute.FS81
