module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs2
public import Certificates.Kernel.D43.Tree3S
public import Certificates.Kernel.D43.Tree3A
public import Certificates.Kernel.D43.Tree3B
public import Certificates.Kernel.D43.Tree3C
public import Certificates.Kernel.D43.Pt3
public import Certificates.Kernel.D43.Rel3
public import CFSG.Certificates.Kernel.D43.Tree3Sound
public import CFSG.Certificates.Kernel.D43.OrbGlue
public import CFSG.Milestones.ASVolI.F48.D43.Chain

public section

open CFSG CFSG.ASVolI CFSG.KC.D43 CertificateChecks.KernelD43

namespace CertificateChecks.KernelD43.C7803

theorem chunks1 {P : ℕ → Prop} (h : P 0) : ∀ c < 1, P c := fun c hc => by
  obtain rfl : c = 0 := by omega
  exact h

theorem chunks2 {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) : ∀ c < 2, P c := fun c hc => by
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · exact h0
  · exact h1

theorem mask_P1 : maskGroup chGen TW 131069 = burnsideF48d_P1 := by
  rw [maskGroup_eq (S := Finset.univ.filter fun j : Fin 17 => j ≠ 1) (by norm_num)
    (by decide +kernel) lG_chGen, burnsideF48d_P1]
  congr 2
  ext j
  simp

theorem mask_P2 : maskGroup chGen TW 131070 = burnsideF48d_P2 := by
  rw [maskGroup_eq (S := Finset.univ.filter fun j : Fin 17 => j ≠ 0) (by norm_num)
    (by decide +kernel) lG_chGen, burnsideF48d_P2]
  congr 2
  ext j
  simp

theorem mask_U : maskGroup chGen TW 131040 = burnsideF48d_U := by
  rw [maskGroup_eq (S := Finset.univ.filter fun j : Fin 17 => 5 ≤ j.val) (by norm_num)
    (by decide +kernel) lG_chGen, burnsideF48d_U]
  congr 2
  ext j
  simp

abbrev LevelOK (R Q : ℕ → ℕ) (ℓ o s b M : ℕ) (hb : b < 26572) : Prop :=
  (treePts R o s).card = s ∧
    (treePts R o s : Set (Fin 26572)) ⊆
      MulAction.orbit ↥(maskGroup chGen TW M) (⟨b, hb⟩ : Fin 26572) ∧
    (∀ t < s, ptAt R o t < 26572) ∧ (∀ t < s, posAt Q ℓ (ptAt R o t) = t)

theorem treeFacts {R Q : ℕ → ℕ} {ℓ o s b M C : ℕ} (hs : s ≤ 256 * C) (hb : b < 26572)
    (h : ∀ c < C, treeChunk GX.F TW R Q ℓ o s b M c = true) : LevelOK R Q ℓ o s b M hb :=
  ⟨treePts_card chGen_tab hs hb h, treePts_sub chGen_tab hs hb h, treeChunks_lt hs h,
    treeChunks_pos hs h⟩

theorem small :
    (∀ c < 1, treeChunk GX.F TW T3R T3Q 0 0 84 6 131069 c = true) ∧
    (∀ c < 1, treeChunk GX.F TW T3R T3Q 2 6888 4 0 131070 c = true) ∧
    (∀ c < 2, treeChunk GX.F TW T3R T3Q 3 6892 324 186 131070 c = true) ∧
    (∀ c < 1, treeChunk GX.F TW T3R T3Q 5 33460 3 6 131040 c = true) ∧
    (∀ c < 1, treeChunk GX.F TW T3R T3Q 6 33463 81 186 131040 c = true) ∧
    (∀ c < 1, treeChunk GX.F TW T3R T3Q 7 33544 243 479 131040 c = true) := by
  have h := tree3Small
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h2⟩, h3a⟩, h3b⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨chunks1 h0, chunks1 h2, chunks2 h3a h3b, chunks1 h5, chunks1 h6, chunks1 h7⟩

theorem smallD :
    (∀ c < 1, disjChunk T3R 0 84 T3R T3Q 1 84 6804 c = true) ∧
    (∀ c < 1, disjChunk T3R 0 84 TR TQ 1 26572 19683 c = true) ∧
    (∀ c < 2, disjChunk T3R 6892 324 T3R T3Q 4 7216 26244 c = true) ∧
    (∀ c < 1, disjChunk T3R 33460 3 T3R T3Q 6 33463 81 c = true) ∧
    (∀ c < 1, disjChunk T3R 33544 243 T3R T3Q 8 33787 6561 c = true) := by
  have h := disj3Small
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2a⟩, h2b⟩, h3⟩, h4⟩ := h
  exact ⟨chunks1 h0, chunks1 h1, chunks2 h2a h2b, chunks1 h3, chunks1 h4⟩

theorem fP6 : LevelOK T3R T3Q 0 0 84 6 131069 (by norm_num) :=
  treeFacts (C := 1) (by norm_num) _ small.1
theorem fP479 : LevelOK T3R T3Q 1 84 6804 479 131069 (by norm_num) :=
  treeFacts (C := 27) (by norm_num) _
    (tree3A : ∀ c < 27, treeChunk GX.F TW T3R T3Q 1 84 6804 479 131069 c = true)
theorem fP26571 : LevelOK TR TQ 1 26572 19683 26571 131069 (by norm_num) :=
  treeFacts (C := 77) (by norm_num) _
    (treeX1 : ∀ c < 77, treeChunk GX.F TW TR TQ 1 26572 19683 26571 131069 c = true)
theorem fL0 : LevelOK T3R T3Q 2 6888 4 0 131070 (by norm_num) :=
  treeFacts (C := 1) (by norm_num) _ small.2.1
theorem fL186 : LevelOK T3R T3Q 3 6892 324 186 131070 (by norm_num) :=
  treeFacts (C := 2) (by norm_num) _ small.2.2.1
theorem fL26571 : LevelOK T3R T3Q 4 7216 26244 26571 131070 (by norm_num) :=
  treeFacts (C := 103) (by norm_num) _
    (tree3B : ∀ c < 103, treeChunk GX.F TW T3R T3Q 4 7216 26244 26571 131070 c = true)
theorem fU6 : LevelOK T3R T3Q 5 33460 3 6 131040 (by norm_num) :=
  treeFacts (C := 1) (by norm_num) _ small.2.2.2.1
theorem fU186 : LevelOK T3R T3Q 6 33463 81 186 131040 (by norm_num) :=
  treeFacts (C := 1) (by norm_num) _ small.2.2.2.2.1
theorem fU479 : LevelOK T3R T3Q 7 33544 243 479 131040 (by norm_num) :=
  treeFacts (C := 1) (by norm_num) _ small.2.2.2.2.2
theorem fU15916 : LevelOK T3R T3Q 8 33787 6561 15916 131040 (by norm_num) :=
  treeFacts (C := 26) (by norm_num) _
    (tree3C8 : ∀ c < 26, treeChunk GX.F TW T3R T3Q 8 33787 6561 15916 131040 c = true)
theorem fU26571 : LevelOK T3R T3Q 9 40348 19683 26571 131040 (by norm_num) :=
  treeFacts (C := 77) (by norm_num) _
    (tree3C9 : ∀ c < 77, treeChunk GX.F TW T3R T3Q 9 40348 19683 26571 131040 c = true)

theorem dP6_P479 : Disjoint (treePts T3R 0 84) (treePts T3R 84 6804) :=
  disjoint_treePts (C := 1) (by norm_num) smallD.1 fP479.2.2.2 fP6.2.2.1 fP479.2.2.1

theorem dP6_P26571 : Disjoint (treePts T3R 0 84) (treePts TR 26572 19683) :=
  disjoint_treePts (C := 1) (by norm_num) smallD.2.1 fP26571.2.2.2 fP6.2.2.1 fP26571.2.2.1

theorem dP479_P26571 : Disjoint (treePts T3R 84 6804) (treePts TR 26572 19683) :=
  disjoint_treePts (C := 27) (by norm_num)
    (disj3A : ∀ c < 27, disjChunk T3R 84 6804 TR TQ 1 26572 19683 c = true)
    fP26571.2.2.2 fP479.2.2.1 fP26571.2.2.1

theorem dL186_L26571 : Disjoint (treePts T3R 6892 324) (treePts T3R 7216 26244) :=
  disjoint_treePts (C := 2) (by norm_num) smallD.2.2.1 fL26571.2.2.2 fL186.2.2.1 fL26571.2.2.1

theorem dU6_U186 : Disjoint (treePts T3R 33460 3) (treePts T3R 33463 81) :=
  disjoint_treePts (C := 1) (by norm_num) smallD.2.2.2.1 fU186.2.2.2 fU6.2.2.1 fU186.2.2.1

theorem dU479_U15916 : Disjoint (treePts T3R 33544 243) (treePts T3R 33787 6561) :=
  disjoint_treePts (C := 1) (by norm_num) smallD.2.2.2.2 fU15916.2.2.2 fU479.2.2.1 fU15916.2.2.1

theorem mem3_pts {ℓ o s q : ℕ} (hq : q < 26572) (hlt : ∀ t < s, ptAt T3R o t < 26572)
    (h : mem3 ℓ o s q = true) : (⟨q, hq⟩ : Fin 26572) ∈ treePts T3R o s :=
  (mem_treePts hlt).2 (memChk_spec h)

theorem mems :
    (186 : Fin 26572) ∈ treePts T3R 0 84 ∧ (15916 : Fin 26572) ∈ treePts T3R 84 6804 ∧
    (1 : Fin 26572) ∈ treePts T3R 33460 3 ∧ (2 : Fin 26572) ∈ treePts T3R 33460 3 := by
  have h := mem3All
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨m186, m15916⟩, -⟩, -⟩, -⟩, m1⟩, m2⟩ := h
  exact ⟨mem3_pts (by norm_num) fP6.2.2.1 m186, mem3_pts (by norm_num) fP479.2.2.1 m15916,
    mem3_pts (by norm_num) fU6.2.2.1 m1, mem3_pts (by norm_num) fU6.2.2.1 m2⟩

theorem mem_line_of {x : Fin 26572} (h : lineB x = true) : x ∈ burnsideF48d_line := by
  simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton]
  rcases lineB_cases h with e | e | e | e
  · exact Or.inl (Fin.ext e)
  · exact Or.inr (Or.inl (Fin.ext e))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext e)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext e)))

theorem lineB_of_mem {x : Fin 26572} (h : x ∈ burnsideF48d_line) : lineB x = true := by
  simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem aptB_cases {q : ℕ} (h : aptB q = true) :
    q = 0 ∨ q = 6 ∨ q = 479 ∨ q = 26571 ∨ q = 15916 ∨ q = 186 := by
  unfold aptB at h
  revert h
  rcases h0 : Nat.beq q (nat_lit 0) with _ | _
  · rcases h1 : Nat.beq q (nat_lit 6) with _ | _
    · rcases h2 : Nat.beq q (nat_lit 479) with _ | _
      · rcases h3 : Nat.beq q (nat_lit 26571) with _ | _
        · rcases h4 : Nat.beq q (nat_lit 15916) with _ | _
          · intro h
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true h)))))
          · intro _
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h4)))))
        · intro _
          exact Or.inr (Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h3))))
      · intro _
        exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2)))
    · intro _
      exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h1))
  · intro _
    exact Or.inl (Nat.eq_of_beq_eq_true h0)

theorem mem_apt_of {x : Fin 26572} (h : aptB x = true) : x ∈ burnsideF48d_aptF := by
  simp only [burnsideF48d_aptF, Finset.mem_insert, Finset.mem_singleton]
  rcases aptB_cases h with e | e | e | e | e | e
  · exact Or.inl (Fin.ext e)
  · exact Or.inr (Or.inl (Fin.ext e))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext e)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext e)))))

theorem L_line {j : Fin 17} (hj : j ≠ 0) {p : Fin 26572} (hp : p ∈ burnsideF48d_line) :
    ((burnsideF48d_L j : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line := by
  have hj1 : 1 ≤ j.val := Nat.pos_of_ne_zero fun h => hj (Fin.ext h)
  have hj16 : j.val ≤ 16 := by have := j.2; omega
  have h := lineAll_spec chGen_tab line3 hj1 hj16 (lineB_of_mem hp)
  rw [lG_chGen] at h
  exact mem_line_of h

theorem pts_T (p : Fin 26572) (hp : p ∉ burnsideF48d_aptF) :
    ((burnsideF48d_L 2 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ≠ p ∨
      ((burnsideF48d_L 3 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ≠ p := by
  have e2 : lG chGen TW 2 = burnsideF48d_L 2 := lG_chGen 2
  have e3 : lG chGen TW 3 = burnsideF48d_L 3 := lG_chGen 3
  rcases ptChunks_spec (F := GX.F) (W := TW) chGen_tab pt3 p with h | h | h
  · exact absurd (mem_apt_of h) hp
  · rw [e2] at h
    exact Or.inl h
  · rw [e3] at h
    exact Or.inr h

theorem img (j : Fin 17) (p q : Fin 26572) (h : Nat.beq (lAp GX.F TW j p) q = true) :
    ((burnsideF48d_L j : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = q := by
  have e := Nat.eq_of_beq_eq_true h
  have hs := lAp_spec chGen_tab (W := TW) (j := j) (p := p) (by rw [e]; exact q.isLt)
  rw [lG_chGen] at hs
  exact Fin.ext (hs.symm.trans e)

@[expose] noncomputable def lineStab : Subgroup ↥burnsideF48d_X where
  carrier := {z | ∀ p ∈ burnsideF48d_line, (z : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line}
  mul_mem' {a b} ha hb p hp := ha _ (hb p hp)
  one_mem' p hp := hp
  inv_mem' {z} hz p hp := by
    have hmaps : Set.MapsTo (z : Equiv.Perm (Fin 26572)) (burnsideF48d_line : Set (Fin 26572))
        (burnsideF48d_line : Set (Fin 26572)) := fun q hq => hz q hq
    have hinj : Set.InjOn (z : Equiv.Perm (Fin 26572)) (burnsideF48d_line : Set (Fin 26572)) :=
      (z : Equiv.Perm (Fin 26572)).injective.injOn
    have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Finset.finite_toSet _) hmaps).1 hinj
    obtain ⟨q, hq, hqp⟩ := hbij.2.2 (show p ∈ (burnsideF48d_line : Set (Fin 26572)) from hp)
    change ((z⁻¹ : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line
    rw [Subgroup.coe_inv, ← hqp, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    exact hq

theorem P2_le_lineStab : burnsideF48d_P2 ≤ lineStab := by
  rw [burnsideF48d_P2, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact fun p hp => L_line hj hp

noncomputable abbrev Bp : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' {j | 2 ≤ j.val})

theorem Bp_le_P1 : Bp ≤ burnsideF48d_P1 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact Subgroup.subset_closure ⟨j, fun h => by
    have : j.val = 1 := congrArg Fin.val h
    simp only [Set.mem_setOf_eq] at hj
    omega, rfl⟩

theorem Bp_le_lineStab : Bp ≤ lineStab := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact fun p hp => L_line (fun h => by
    have : j.val = 0 := congrArg Fin.val h
    simp only [Set.mem_setOf_eq] at hj
    omega) hp

theorem U_le_Bp : burnsideF48d_U ≤ Bp := by
  rw [burnsideF48d_U]
  exact Subgroup.closure_mono (Set.image_mono fun j hj => by
    simp only [Set.mem_setOf_eq] at hj ⊢
    omega)

theorem U_le_P1 : burnsideF48d_U ≤ burnsideF48d_P1 := U_le_Bp.trans Bp_le_P1

theorem orbit_P1_sub {r : Fin 26572} (hr : r ≠ 0) :
    MulAction.orbit ↥burnsideF48d_P1 r ⊆ ((Finset.univ.erase 0 : Finset (Fin 26572)) : Set _) := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  rw [Finset.coe_erase, Finset.coe_univ]
  refine ⟨Set.mem_univ _, fun h => hr ?_⟩
  have h0 := (burnsideF48d_mem_P1 g).1 hg
  have h' : (g : Equiv.Perm (Fin 26572)) r = (g : Equiv.Perm (Fin 26572)) 0 := by
    rw [h0]
    exact h
  exact (g : Equiv.Perm (Fin 26572)).injective h'

theorem sub_P6 : (treePts T3R 0 84 : Set (Fin 26572)) ⊆
    MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572) := by
  have h := fP6.2.1
  rw [mask_P1] at h
  exact h

theorem sub_P479 : (treePts T3R 84 6804 : Set (Fin 26572)) ⊆
    MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572) := by
  have h := fP479.2.1
  rw [mask_P1] at h
  exact h

theorem sub_P26571 : (treePts TR 26572 19683 : Set (Fin 26572)) ⊆
    MulAction.orbit ↥burnsideF48d_P1 (26571 : Fin 26572) := by
  have h := fP26571.2.1
  rw [mask_P1] at h
  exact h

theorem dvd_X (K : Subgroup ↥burnsideF48d_X) : Nat.card ↥K ∣ 20560831566912 := by
  rw [← burnsideF48d_card_X]
  exact Subgroup.card_subgroup_dvd_card _

theorem orbits_P1 :
    MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572) = treePts T3R 0 84 ∧
    MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572) = treePts T3R 84 6804 ∧
    MulAction.orbit ↥burnsideF48d_P1 (26571 : Fin 26572) = treePts TR 26572 19683 := by
  have key := orbit_eq_of_partition (H := ↥burnsideF48d_P1) (N := 20560831566912)
    ![(6 : Fin 26572), 479, 26571] ![treePts T3R 0 84, treePts T3R 84 6804, treePts TR 26572 19683]
    (Finset.univ.erase 0) ![84, 6804, 19683]
    (by
      intro i
      fin_cases i
      exacts [sub_P6, sub_P479, sub_P26571])
    (by
      intro i
      fin_cases i <;> exact orbit_P1_sub (by decide))
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      exacts [absurd rfl hij, dP6_P479, dP6_P26571, dP6_P479.symm, absurd rfl hij, dP479_P26571,
        dP6_P26571.symm, dP479_P26571.symm, absurd rfl hij])
    (by
      intro i
      fin_cases i
      exacts [fP6.1, fP479.1, fP26571.1])
    (by
      rw [Fin.sum_univ_three, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
      rfl)
    (dvd_X _) (by decide +kernel)
  exact ⟨key 0, key 1, key 2⟩

theorem card_orbit_finset {G : Type*} [Group G] [MulAction G (Fin 26572)] {r : Fin 26572}
    {A : Finset (Fin 26572)} (h : MulAction.orbit G r = A) : Nat.card (MulAction.orbit G r) = A.card := by
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem cover_P1 (p : Fin 26572) (hp : p ≠ 0) :
    p ∈ treePts T3R 0 84 ∨ p ∈ treePts T3R 84 6804 ∨ p ∈ treePts TR 26572 19683 := by
  have key := mem_of_partition ![treePts T3R 0 84, treePts T3R 84 6804, treePts TR 26572 19683]
    (Finset.univ.erase 0) ![84, 6804, 19683]
    (by
      intro i
      fin_cases i
      · exact fun q hq => by
          have := orbit_P1_sub (r := 6) (by decide) (sub_P6 hq)
          exact this
      · exact fun q hq => by
          have := orbit_P1_sub (r := 479) (by decide) (sub_P479 hq)
          exact this
      · exact fun q hq => by
          have := orbit_P1_sub (r := 26571) (by decide) (sub_P26571 hq)
          exact this)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      exacts [absurd rfl hij, dP6_P479, dP6_P26571, dP6_P479.symm, absurd rfl hij, dP479_P26571,
        dP6_P26571.symm, dP479_P26571.symm, absurd rfl hij])
    (by
      intro i
      fin_cases i
      exacts [fP6.1, fP479.1, fP26571.1])
    (by
      rw [Fin.sum_univ_three, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
      rfl)
    p (Finset.mem_erase.2 ⟨hp, Finset.mem_univ _⟩)
  obtain ⟨i, hi⟩ := key
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

theorem card_P1 : Nat.card ↥burnsideF48d_P1 = 773778096 := by
  have h := CFSG.Perm.card_eq_orbit_mul (⊤ : Subgroup ↥burnsideF48d_X) burnsideF48d_P1
    (0 : Fin 26572) le_top (fun l hl => Fin.ext (by
      have := (burnsideF48d_mem_P1 l).1 hl
      exact congrArg Fin.val this))
    (fun h _ hh => (burnsideF48d_mem_P1 h).2 hh)
  have htop : MulAction.orbit ↥(⊤ : Subgroup ↥burnsideF48d_X) (0 : Fin 26572) = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    obtain ⟨z, hz⟩ := burnsideF48d_trans q
    exact ⟨⟨z, Subgroup.mem_top _⟩, hz⟩
  rw [Subgroup.card_top, burnsideF48d_card_X, htop, Nat.card_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  omega

theorem card_P1_6 :
    Nat.card ↥(burnsideF48d_P1 ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572)) = 9211644 := by
  have h := CFSG.Perm.card_eq_orbit_mul_inf burnsideF48d_P1 (6 : Fin 26572)
  rw [card_P1, card_orbit_finset orbits_P1.1, fP6.1] at h
  omega

theorem card_Bp_le : Nat.card ↥Bp ≤ 27634932 := by
  have h := CFSG.Perm.card_eq_orbit_mul_inf Bp (6 : Fin 26572)
  have h1 : Nat.card (MulAction.orbit ↥Bp (6 : Fin 26572)) ≤ 3 := by
    have hsub : MulAction.orbit ↥Bp (6 : Fin 26572) ⊆ ({1, 2, 6} : Finset (Fin 26572)) := by
      rintro _ ⟨⟨q, hq⟩, rfl⟩
      have h6 : (q : Equiv.Perm (Fin 26572)) 6 ∈ burnsideF48d_line :=
        Bp_le_lineStab hq 6 (by decide)
      have h0 : (q : Equiv.Perm (Fin 26572)) 0 = 0 := (burnsideF48d_mem_P1 q).1 (Bp_le_P1 hq)
      have hne : (q : Equiv.Perm (Fin 26572)) 6 ≠ 0 := fun h => by
        rw [← h0] at h
        exact absurd ((q : Equiv.Perm (Fin 26572)).injective h) (by decide)
      change (q : Equiv.Perm (Fin 26572)) 6 ∈ (({1, 2, 6} : Finset (Fin 26572)) : Set (Fin 26572))
      simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton] at h6
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases h6 with h6 | h6 | h6 | h6
      · exact absurd h6 hne
      · exact Or.inl h6
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr h6)
    calc Nat.card (MulAction.orbit ↥Bp (6 : Fin 26572))
        ≤ Nat.card (({1, 2, 6} : Finset (Fin 26572)) : Set (Fin 26572)) :=
          Nat.card_mono (Finset.finite_toSet _) hsub
      _ = 3 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]; decide
  have h2 : Nat.card ↥(Bp ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572)) ≤ 9211644 := by
    rw [← card_P1_6]
    exact Subgroup.card_le_of_le (inf_le_inf_right _ Bp_le_P1)
  rw [h]
  calc _ ≤ 3 * 9211644 := Nat.mul_le_mul h1 h2
    _ = 27634932 := by norm_num

theorem card_Bp_ge : 27634932 ≤ Nat.card ↥Bp := by
  have h := burnsideF48d_lvH_prod_le burnsideF48d_chain_cert.2 burnsideF48d_nestedB 0
    (Nat.zero_le _)
  have e : ∏ l ∈ Finset.Ico 0 burnsideF48d_chainBL.length,
      (burnsideF48d_chainBL.getD l burnsideF48d_lv0).2.2 = 27634932 := by
    decide +kernel
  have hS : ∀ j : Fin 17, j ∈ (burnsideF48d_chainBL.getD 0 burnsideF48d_lv0).2.1 ↔ 2 ≤ j.val := by
    decide +kernel
  have hB : burnsideF48d_lvH burnsideF48d_chainBL 0 = Bp := by
    unfold burnsideF48d_lvH
    congr 2
    ext j
    exact hS j
  rw [e, hB] at h
  exact h

theorem dvd_B (K : Subgroup ↥burnsideF48d_X) (hK : K ≤ Bp) : Nat.card ↥K ∣ 27634932 := by
  rw [← le_antisymm card_Bp_le card_Bp_ge]
  exact Subgroup.card_dvd_of_le hK

theorem sub_L0 : (treePts T3R 6888 4 : Set (Fin 26572)) ⊆
    MulAction.orbit ↥burnsideF48d_P2 (0 : Fin 26572) := by
  have h := fL0.2.1
  rw [mask_P2] at h
  exact h

theorem sub_L186 : (treePts T3R 6892 324 : Set (Fin 26572)) ⊆
    MulAction.orbit ↥burnsideF48d_P2 (186 : Fin 26572) := by
  have h := fL186.2.1
  rw [mask_P2] at h
  exact h

theorem sub_L26571 : (treePts T3R 7216 26244 : Set (Fin 26572)) ⊆
    MulAction.orbit ↥burnsideF48d_P2 (26571 : Fin 26572) := by
  have h := fL26571.2.1
  rw [mask_P2] at h
  exact h

theorem orbit_P2_line : MulAction.orbit ↥burnsideF48d_P2 (0 : Fin 26572) =
    (burnsideF48d_line : Set (Fin 26572)) := by
  have hsub : MulAction.orbit ↥burnsideF48d_P2 (0 : Fin 26572) ⊆ (burnsideF48d_line : Set _) := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact P2_le_lineStab hg 0 (by decide)
  have hA : treePts T3R 6888 4 ⊆ burnsideF48d_line := fun q hq => hsub (sub_L0 hq)
  have hAe : treePts T3R 6888 4 = burnsideF48d_line :=
    Finset.eq_of_subset_of_card_le hA (by rw [fL0.1]; decide)
  refine le_antisymm hsub ?_
  rw [← hAe]
  exact sub_L0

theorem orbit_P2_sub {r : Fin 26572} (hr : r ∉ burnsideF48d_line) :
    MulAction.orbit ↥burnsideF48d_P2 r ⊆
      ((Finset.univ \ burnsideF48d_line : Finset (Fin 26572)) : Set _) := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  rw [Finset.coe_sdiff, Finset.coe_univ]
  refine ⟨Set.mem_univ _, fun h => hr ?_⟩
  have h' := P2_le_lineStab (burnsideF48d_P2.inv_mem hg) _ h
  change ((g⁻¹ : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572))
    ((g : Equiv.Perm (Fin 26572)) r) ∈ burnsideF48d_line at h'
  rwa [Subgroup.coe_inv, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply] at h'

theorem card_univ_line : (Finset.univ \ burnsideF48d_line : Finset (Fin 26572)).card = 26568 := by
  rw [Finset.card_univ_diff, Fintype.card_fin]
  rfl

theorem orbits_P2 :
    MulAction.orbit ↥burnsideF48d_P2 (186 : Fin 26572) = treePts T3R 6892 324 ∧
    MulAction.orbit ↥burnsideF48d_P2 (26571 : Fin 26572) = treePts T3R 7216 26244 := by
  have key := orbit_eq_of_partition (H := ↥burnsideF48d_P2) (N := 20560831566912)
    ![(186 : Fin 26572), 26571] ![treePts T3R 6892 324, treePts T3R 7216 26244]
    (Finset.univ \ burnsideF48d_line) ![324, 26244]
    (by
      intro i
      fin_cases i
      exacts [sub_L186, sub_L26571])
    (by
      intro i
      fin_cases i <;> exact orbit_P2_sub (by decide))
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      exacts [absurd rfl hij, dL186_L26571, dL186_L26571.symm, absurd rfl hij])
    (by
      intro i
      fin_cases i
      exacts [fL186.1, fL26571.1])
    (by rw [Fin.sum_univ_two, card_univ_line]; rfl)
    (dvd_X _) (by decide +kernel)
  exact ⟨key 0, key 1⟩

theorem cover_P2 (p : Fin 26572) :
    p ∈ MulAction.orbit ↥burnsideF48d_P2 (0 : Fin 26572) ∨
      p ∈ MulAction.orbit ↥burnsideF48d_P2 (186 : Fin 26572) ∨
      p ∈ MulAction.orbit ↥burnsideF48d_P2 (26571 : Fin 26572) := by
  by_cases hp : p ∈ burnsideF48d_line
  · left
    rw [orbit_P2_line]
    exact hp
  right
  have key := mem_of_partition ![treePts T3R 6892 324, treePts T3R 7216 26244]
    (Finset.univ \ burnsideF48d_line) ![324, 26244]
    (by
      intro i
      fin_cases i
      · exact fun q hq => by
          have := orbit_P2_sub (r := 186) (by decide) (sub_L186 hq)
          exact this
      · exact fun q hq => by
          have := orbit_P2_sub (r := 26571) (by decide) (sub_L26571 hq)
          exact this)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      exacts [absurd rfl hij, dL186_L26571, dL186_L26571.symm, absurd rfl hij])
    (by
      intro i
      fin_cases i
      exacts [fL186.1, fL26571.1])
    (by rw [Fin.sum_univ_two, card_univ_line]; rfl)
    p (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hp⟩)
  obtain ⟨i, hi⟩ := key
  fin_cases i
  · exact Or.inl (sub_L186 hi)
  · exact Or.inr (sub_L26571 hi)

theorem sub_U (A : Finset (Fin 26572)) {b : ℕ} (hb : b < 26572)
    (h : (A : Set (Fin 26572)) ⊆ MulAction.orbit ↥(maskGroup chGen TW 131040) (⟨b, hb⟩ : Fin 26572)) :
    (A : Set (Fin 26572)) ⊆ MulAction.orbit ↥burnsideF48d_U (⟨b, hb⟩ : Fin 26572) := by
  rw [mask_U] at h
  exact h

theorem orbit_U_sub {r s : Fin 26572} {A : Finset (Fin 26572)}
    (hA : MulAction.orbit ↥burnsideF48d_P1 s = A) (hr : r ∈ MulAction.orbit ↥burnsideF48d_P1 s) :
    MulAction.orbit ↥burnsideF48d_U r ⊆ A := by
  rw [← hA, ← MulAction.orbit_eq_iff.2 hr]
  exact orbit_subset_of_le U_le_P1 r

theorem m186 : (186 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572) :=
  sub_P6 mems.1

theorem m15916 : (15916 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572) :=
  sub_P479 mems.2.1

theorem orbits_U_6 :
    MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572) = treePts T3R 33460 3 ∧
    MulAction.orbit ↥burnsideF48d_U (186 : Fin 26572) = treePts T3R 33463 81 := by
  have key := orbit_eq_of_partition (H := ↥burnsideF48d_U) (N := 27634932)
    ![(6 : Fin 26572), 186] ![treePts T3R 33460 3, treePts T3R 33463 81]
    (treePts T3R 0 84) ![3, 81]
    (by
      intro i
      fin_cases i
      exacts [sub_U _ (by norm_num) fU6.2.1, sub_U _ (by norm_num) fU186.2.1])
    (by
      intro i
      fin_cases i
      · exact orbit_U_sub orbits_P1.1 (MulAction.mem_orbit_self _)
      · exact orbit_U_sub orbits_P1.1 m186)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      exacts [absurd rfl hij, dU6_U186, dU6_U186.symm, absurd rfl hij])
    (by
      intro i
      fin_cases i
      exacts [fU6.1, fU186.1])
    (by rw [Fin.sum_univ_two, fP6.1]; rfl)
    (dvd_B _ U_le_Bp) (by decide +kernel)
  exact ⟨key 0, key 1⟩

theorem orbits_U_479 :
    MulAction.orbit ↥burnsideF48d_U (479 : Fin 26572) = treePts T3R 33544 243 ∧
    MulAction.orbit ↥burnsideF48d_U (15916 : Fin 26572) = treePts T3R 33787 6561 := by
  have key := orbit_eq_of_partition (H := ↥burnsideF48d_U) (N := 27634932)
    ![(479 : Fin 26572), 15916] ![treePts T3R 33544 243, treePts T3R 33787 6561]
    (treePts T3R 84 6804) ![243, 6561]
    (by
      intro i
      fin_cases i
      exacts [sub_U _ (by norm_num) fU479.2.1, sub_U _ (by norm_num) fU15916.2.1])
    (by
      intro i
      fin_cases i
      · exact orbit_U_sub orbits_P1.2.1 (MulAction.mem_orbit_self _)
      · exact orbit_U_sub orbits_P1.2.1 m15916)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      exacts [absurd rfl hij, dU479_U15916, dU479_U15916.symm, absurd rfl hij])
    (by
      intro i
      fin_cases i
      exacts [fU479.1, fU15916.1])
    (by rw [Fin.sum_univ_two, fP479.1]; rfl)
    (dvd_B _ U_le_Bp) (by decide +kernel)
  exact ⟨key 0, key 1⟩

theorem U26571_eq : treePts T3R 40348 19683 = treePts TR 26572 19683 := by
  have hA := sub_U _ (by norm_num) fU26571.2.1
  have hS := orbit_U_sub orbits_P1.2.2 (MulAction.mem_orbit_self (26571 : Fin 26572))
  exact Finset.eq_of_subset_of_card_le (fun q hq => hS (hA hq)) (by rw [fU26571.1, fP26571.1])

theorem orbit_U_26571 :
    MulAction.orbit ↥burnsideF48d_U (26571 : Fin 26572) = treePts T3R 40348 19683 := by
  refine le_antisymm ?_ (sub_U _ (by norm_num) fU26571.2.1)
  rw [U26571_eq]
  exact orbit_U_sub orbits_P1.2.2 (MulAction.mem_orbit_self _)

theorem cover2 {A B S : Finset (Fin 26572)} (hAS : ∀ q ∈ A, q ∈ S) (hBS : ∀ q ∈ B, q ∈ S)
    (hd : Disjoint A B) (hc : A.card + B.card = S.card) {p : Fin 26572} (hp : p ∈ S) :
    p ∈ A ∨ p ∈ B := by
  have hU : A ∪ B = S := Finset.eq_of_subset_of_card_le (Finset.union_subset hAS hBS)
    (by rw [Finset.card_union_of_disjoint hd, hc])
  rw [← hU] at hp
  exact Finset.mem_union.1 hp

theorem cover_U (p : Fin 26572) (hp : p ≠ 0) :
    p ∈ MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572) ∨
      p ∈ MulAction.orbit ↥burnsideF48d_U (186 : Fin 26572) ∨
      p ∈ MulAction.orbit ↥burnsideF48d_U (479 : Fin 26572) ∨
      p ∈ MulAction.orbit ↥burnsideF48d_U (15916 : Fin 26572) ∨
      p ∈ MulAction.orbit ↥burnsideF48d_U (26571 : Fin 26572) := by
  rw [orbits_U_6.1, orbits_U_6.2, orbits_U_479.1, orbits_U_479.2, orbit_U_26571]
  simp only [Finset.mem_coe]
  have h6 : ∀ q ∈ MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572), q ∈ treePts T3R 0 84 :=
    fun q hq => orbit_U_sub orbits_P1.1 (MulAction.mem_orbit_self _) hq
  have h186 : ∀ q ∈ MulAction.orbit ↥burnsideF48d_U (186 : Fin 26572), q ∈ treePts T3R 0 84 :=
    fun q hq => orbit_U_sub orbits_P1.1 m186 hq
  have h479 : ∀ q ∈ MulAction.orbit ↥burnsideF48d_U (479 : Fin 26572), q ∈ treePts T3R 84 6804 :=
    fun q hq => orbit_U_sub orbits_P1.2.1 (MulAction.mem_orbit_self _) hq
  have h15916 : ∀ q ∈ MulAction.orbit ↥burnsideF48d_U (15916 : Fin 26572),
      q ∈ treePts T3R 84 6804 :=
    fun q hq => orbit_U_sub orbits_P1.2.1 m15916 hq
  rw [orbits_U_6.1] at h6
  rw [orbits_U_6.2] at h186
  rw [orbits_U_479.1] at h479
  rw [orbits_U_479.2] at h15916
  rcases cover_P1 p hp with h | h | h
  · rcases cover2 h6 h186 dU6_U186 (by rw [fU6.1, fU186.1, fP6.1]) h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases cover2 h479 h15916 dU479_U15916 (by rw [fU479.1, fU15916.1, fP479.1]) h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [U26571_eq]
    exact h

theorem ev_apply (w : List (Fin 17 × Bool)) (hw : w.length ≤ 40) (p : Fin 26572)
    (h : evR GX.F TW (enc3 w) p < 26572) :
    evR GX.F TW (enc3 w) p =
      (((burnsideF48s_ev burnsideF48d_L w : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p : ℕ) := by
  have e := evRF_enc3 (LW := fun j => burnsideF48d_LW.getD j []) chGen_tab TW_eq LW_len w 40 p hw h
  rw [show (fun j : Fin 17 => lG chGen TW j) = burnsideF48d_L from funext lG_chGen] at e
  exact e

@[expose] def rels : List (List (Fin 17 × Bool)) := burnsideF48d_R1 ++ burnsideF48d_R2 ++
  [(List.replicate 6 burnsideF48d_xyW).flatten, burnsideF48d_W1, burnsideF48d_W2]

theorem rels_len : rels.length = 179 := by decide +kernel

theorem R3W_eq : ∀ i < 179, R3W i = enc3 (rels.getD i []) := by decide +kernel

theorem rels_short : ∀ r ∈ rels, r.length ≤ 40 := by decide +kernel

theorem KW_len : burnsideF48d_KW.length = 52 := by decide +kernel

theorem K3W_eq : ∀ i < 52, K3W i = enc3 (burnsideF48d_KW.getD i []) := by decide +kernel

theorem KW_short : ∀ w ∈ burnsideF48d_KW, w.length ≤ 38 := by decide +kernel

theorem KW_nodup : burnsideF48d_KW.Nodup := by decide +kernel

theorem XY3W_eq : ∀ i < 51, X3W i = enc3 (burnsideF48d_xyW ++ burnsideF48d_KW.tail.getD i []) ∧
    Y3W i = enc3 (burnsideF48d_KW.tail.getD i [] ++ burnsideF48d_xyW) := by decide +kernel

theorem base_lt : ∀ u < 8, bAt B3X u < 26572 := by decide +kernel

theorem base_cov : ∀ p ∈ burnsideF48d_baseF, ∃ u < 8, bAt B3X u = (p : ℕ) := by
  intro p hp
  simp only [burnsideF48d_baseF, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, by norm_num, by decide +kernel⟩, ⟨1, by norm_num, by decide +kernel⟩,
    ⟨2, by norm_num, by decide +kernel⟩, ⟨3, by norm_num, by decide +kernel⟩,
    ⟨4, by norm_num, by decide +kernel⟩, ⟨5, by norm_num, by decide +kernel⟩,
    ⟨6, by norm_num, by decide +kernel⟩, ⟨7, by norm_num, by decide +kernel⟩]

theorem getD_mem {l : List (List (Fin 17 × Bool))} {r : List (Fin 17 × Bool)} (hr : r ∈ l) :
    ∃ i < l.length, l.getD i [] = r := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hr
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi, e]⟩

theorem rels_one : ∀ r ∈ rels, burnsideF48s_ev burnsideF48d_L r = 1 := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := getD_mem hr
  have hi' : i < 179 := by rw [rels_len] at hi; exact hi
  have hc := (brelChunks_spec (C := 12) (by norm_num)
    (rel3 : ∀ c < 12, brelChunk GX.F TW B3X R3W 179 c = true) i hi').2
  apply burnsideF48d_base
  intro p hp
  obtain ⟨u, hu, hpu⟩ := base_cov p hp
  have hfix := hc u hu
  rw [hpu, R3W_eq i hi'] at hfix
  have e := ev_apply _ (rels_short _ hr) p (by rw [hfix]; exact p.isLt)
  exact Fin.ext (e.symm.trans hfix)

theorem key_congr {w w' : List (Fin 17 × Bool)} (hw : w.length ≤ 40) (hw' : w'.length ≤ 40)
    (h : ∀ u < 8, evR GX.F TW (enc3 w) (bAt B3X u) < 26572)
    (h' : ∀ u < 8, evR GX.F TW (enc3 w') (bAt B3X u) < 26572)
    (he : burnsideF48s_ev burnsideF48d_L w = burnsideF48s_ev burnsideF48d_L w') :
    key8 GX.F TW B3X (enc3 w) = key8 GX.F TW B3X (enc3 w') := by
  apply key8F_congr
  intro u hu
  rw [ev_apply w hw ⟨bAt B3X u, base_lt u hu⟩ (h u hu),
    ev_apply w' hw' ⟨bAt B3X u, base_lt u hu⟩ (h' u hu), he]

theorem KW_key (i : ℕ) (hi : i < 52) :
    (∀ u < 8, evR GX.F TW (enc3 (burnsideF48d_KW.getD i [])) (bAt B3X u) < 26572) ∧
      key8 GX.F TW B3X (enc3 (burnsideF48d_KW.getD i [])) = K3K i := by
  obtain ⟨hv, hk⟩ := bkeyChunks_spec (C := 4) (by norm_num)
    (key3 : ∀ c < 4, bkeyChunk GX.F TW B3X K3W K3K 52 c = true) i hi
  rw [K3W_eq i hi] at hv hk
  exact ⟨(valid8_spec hv).2, hk⟩

theorem KW_vals : (burnsideF48d_KW.map (burnsideF48s_ev burnsideF48d_L)).Nodup := by
  refine List.Nodup.map_on ?_ KW_nodup
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := getD_mem hx
  obtain ⟨j, hj, rfl⟩ := getD_mem hy
  rw [KW_len] at hi hj
  have hk := key_congr (by have := KW_short _ hx; omega) (by have := KW_short _ hy; omega)
    (KW_key i hi).1 (KW_key j hj).1 hxy
  rw [(KW_key i hi).2, (KW_key j hj).2] at hk
  rw [distinctAll_spec dist3 i hi j hj hk]

theorem comm_ne : ∀ c ∈ burnsideF48d_KW.tail, burnsideF48s_ev burnsideF48d_L (burnsideF48d_xyW ++ c) ≠
    burnsideF48s_ev burnsideF48d_L (c ++ burnsideF48d_xyW) := by
  intro c hc he
  obtain ⟨i, hi, rfl⟩ := getD_mem hc
  have hi' : i < 51 := by
    rw [List.length_tail, KW_len] at hi
    exact hi
  have hlen : (burnsideF48d_KW.tail.getD i []).length ≤ 38 := KW_short _ (List.mem_of_mem_tail hc)
  obtain ⟨hvx, hvy, hne⟩ := neqChunks_spec (C := 3) (by norm_num)
    (neq3 : ∀ c < 3, neqChunk GX.F TW B3X X3W Y3W 51 c = true) i hi'
  rw [(XY3W_eq i hi').1] at hvx hne
  rw [(XY3W_eq i hi').2] at hvy hne
  have hxy : burnsideF48d_xyW.length = 2 := rfl
  exact hne (key_congr (by rw [List.length_append, hxy]; omega)
    (by rw [List.length_append, hxy]; omega) (valid8_spec hvx).2 (valid8_spec hvy).2 he)

theorem cover_fun (p : Fin 26572) (hp : p ≠ 0) :
    p ∈ MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572) ∨
      p ∈ MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572) ∨
      p ∈ MulAction.orbit ↥burnsideF48d_P1 (26571 : Fin 26572) := by
  rw [orbits_P1.1, orbits_P1.2.1, orbits_P1.2.2]
  exact cover_P1 p hp

end CertificateChecks.KernelD43.C7803

namespace Certificates

open CertificateChecks.KernelD43.C7803

open CFSG CFSG.ASVolI in
theorem certificate7803 :
    (Nat.card (MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572)) = 84 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572)) = 6804 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_P1 (26571 : Fin 26572)) = 19683 ∧
      (∀ p : Fin 26572, p ≠ 0 → p ∈ MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_P1 (26571 : Fin 26572)) ∧
      (186 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572) ∧
      (15916 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572)) ∧
    (MulAction.orbit ↥burnsideF48d_P2 (0 : Fin 26572) = (burnsideF48d_line : Set (Fin 26572)) ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_P2 (186 : Fin 26572)) = 324 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_P2 (26571 : Fin 26572)) = 26244 ∧
      ∀ p : Fin 26572, p ∈ MulAction.orbit ↥burnsideF48d_P2 (0 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_P2 (186 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_P2 (26571 : Fin 26572)) ∧
    (Nat.card (MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572)) = 3 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_U (186 : Fin 26572)) = 81 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_U (479 : Fin 26572)) = 243 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_U (15916 : Fin 26572)) = 6561 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_U (26571 : Fin 26572)) = 19683 ∧
      (∀ p : Fin 26572, p ≠ 0 → p ∈ MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_U (186 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_U (479 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_U (15916 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_U (26571 : Fin 26572)) ∧
      (1 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572) ∧
      (2 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572)) ∧
    ((∀ p : Fin 26572, p ∉ burnsideF48d_aptF →
        ((burnsideF48d_L 2 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ≠ p ∨
        ((burnsideF48d_L 3 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ≠ p) ∧
      (∀ j : Fin 17, j ≠ 0 → ∀ p ∈ burnsideF48d_line,
        ((burnsideF48d_L j : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line) ∧
      ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 0 ∧
      ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 6 = 186 ∧
      ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 479 = 15916 ∧
      ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 26571 = 26571 ∧
      ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 15916 = 479 ∧
      ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 186 = 6 ∧
      ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 6 ∧
      ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 6 = 0 ∧
      ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 479 = 186 ∧
      ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 26571 = 15916 ∧
      ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 15916 = 26571 ∧
      ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 186 = 479) ∧
    ((∀ r ∈ burnsideF48d_R1 ++ burnsideF48d_R2 ++
        [(List.replicate 6 burnsideF48d_xyW).flatten, burnsideF48d_W1, burnsideF48d_W2],
        burnsideF48s_ev burnsideF48d_L r = 1) ∧
      (burnsideF48d_KW.map (burnsideF48s_ev burnsideF48d_L)).Nodup ∧
      ∀ c ∈ burnsideF48d_KW.tail, burnsideF48s_ev burnsideF48d_L (burnsideF48d_xyW ++ c) ≠
        burnsideF48s_ev burnsideF48d_L (c ++ burnsideF48d_xyW)) := by
  have hx := aptImg3
  simp only [Bool.and_eq_true] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨x0, x6⟩, x479⟩, x26571⟩, x15916⟩, x186⟩, y0⟩, y6⟩, y479⟩, y26571⟩, y15916⟩,
    y186⟩ := hx
  refine ⟨⟨?_, ?_, ?_, cover_fun, m186, m15916⟩, ⟨orbit_P2_line, ?_, ?_, cover_P2⟩,
    ⟨?_, ?_, ?_, ?_, ?_, cover_U, ?_, ?_⟩, ⟨pts_T, fun j hj p hp => L_line hj hp,
      img 0 0 0 x0, img 0 6 186 x6, img 0 479 15916 x479, img 0 26571 26571 x26571,
      img 0 15916 479 x15916, img 0 186 6 x186, img 1 0 6 y0, img 1 6 0 y6, img 1 479 186 y479,
      img 1 26571 15916 y26571, img 1 15916 26571 y15916, img 1 186 479 y186⟩,
    ⟨rels_one, KW_vals, comm_ne⟩⟩
  · rw [card_orbit_finset orbits_P1.1, fP6.1]
  · rw [card_orbit_finset orbits_P1.2.1, fP479.1]
  · rw [card_orbit_finset orbits_P1.2.2, fP26571.1]
  · rw [card_orbit_finset orbits_P2.1, fL186.1]
  · rw [card_orbit_finset orbits_P2.2, fL26571.1]
  · rw [card_orbit_finset orbits_U_6.1, fU6.1]
  · rw [card_orbit_finset orbits_U_6.2, fU186.1]
  · rw [card_orbit_finset orbits_U_479.1, fU479.1]
  · rw [card_orbit_finset orbits_U_479.2, fU15916.1]
  · rw [card_orbit_finset orbit_U_26571, fU26571.1]
  · rw [orbits_U_6.1]
    exact mems.2.2.1
  · rw [orbits_U_6.1]
    exact mems.2.2.2

end Certificates
