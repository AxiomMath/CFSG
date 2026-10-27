module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Coord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Equiv
open scoped Pointwise

@[expose] def s16c11A11Co (j : Fin 11) : Fin 11 → ZMod 2 := fun i => if i = j then 0 else 1

theorem s16c11A11Co_sum (j : Fin 11) : ∑ i, s16c11A11Co j i = 0 := by
  fin_cases j <;> decide

@[expose] def s16c11A11Cls (j : Fin 11) : (FFModel.altDn 11).Mod :=
  s16c11AltVec 11 (s16c11A11Co j) (s16c11A11Co_sum j)

@[expose] def s16c11A11Fix (α β : ZMod 2) : Fin 11 → ZMod 2 :=
  fun i => if (i : ℕ) < 8 then α else if (i : ℕ) < 10 then β else 0

theorem s16c11A11Fix_sum (α β : ZMod 2) : ∑ i, s16c11A11Fix α β i = 0 := by
  revert α β
  decide

@[expose] def s16c11A11T1 : Subgroup ↥(alternatingGroup (Fin 11)) :=
  s16c11A11T.subgroupOf (alternatingGroup (Fin 11))

private lemma s16c11a11_vec_mk_mem_T1 {m : Perm (Fin 11)} (hm : m ∈ s16c11A11T) :
    (⟨m, s16c11A11_T_le_alt hm⟩ : ↥(alternatingGroup (Fin 11))) ∈ s16c11A11T1 :=
  Subgroup.mem_subgroupOf.2 hm

theorem s16c11A11Cls_injective : Function.Injective s16c11A11Cls := by
  intro j j' h
  have hco : s16c11A11Co j = s16c11A11Co j' :=
    (s16c11AltVec_eq_iff (n := 11) (by decide)).1 (by simpa only [s16c11A11Cls] using h)
  by_contra hne
  have h' := congr_fun hco j
  simp [s16c11A11Co, hne] at h'

theorem s16c11A11Cls_ne_one (j : Fin 11) : s16c11A11Cls j ≠ 1 := by
  intro h
  have hco : s16c11A11Co j = 0 :=
    (s16c11AltVec_eq_one_iff (n := 11) (by decide)).1 (by simpa only [s16c11A11Cls] using h)
  exact (by fin_cases j <;> decide : s16c11A11Co j ≠ 0) hco

theorem s16c11A11_act_cls (g : ↥(alternatingGroup (Fin 11))) (j : Fin 11) :
    S16C11AltAct 11 g (s16c11A11Cls j) = s16c11A11Cls ((g : Perm (Fin 11)) j) := by
  unfold s16c11A11Cls
  have hx' : ∑ i, s16c11A11Co j ((g : Perm (Fin 11))⁻¹ i) = 0 := by
    rw [Equiv.sum_comp]
    exact s16c11A11Co_sum j
  rw [s16c11AltAct_vec 11 g (hx' := hx')]
  congr 1
  ext i
  simp only [s16c11A11Co]
  by_cases h : i = (g : Perm (Fin 11)) j
  · have h1 : (g : Perm (Fin 11))⁻¹ i = j := by
      rw [h]
      exact Equiv.symm_apply_apply (g : Perm (Fin 11)) j
    rw [if_pos h1, if_pos h]
  · have h1 : (g : Perm (Fin 11))⁻¹ i ≠ j := fun hc =>
      h (by
        have h2 := congrArg (g : Perm (Fin 11)) hc
        simpa [Equiv.apply_symm_apply] using h2)
    rw [if_neg h1, if_neg h]

theorem s16c11A11_fix_one_one : s16c11A11Fix 1 1 = s16c11A11Co 10 := by
  funext i
  fin_cases i <;> decide

private lemma s16c11a11_vec_fix_rel {x : Fin 11 → ZMod 2} {hx : ∑ i, x i = 0}
    (h : ∀ t ∈ s16c11A11T1, S16C11AltAct 11 t (s16c11AltVec 11 x hx) = s16c11AltVec 11 x hx)
    {m : Perm (Fin 11)} (hm : m ∈ s16c11A11T) (i : Fin 11) : x i = x (m i) := by
  let t : ↥(alternatingGroup (Fin 11)) := ⟨m, s16c11A11_T_le_alt hm⟩
  have hx' : ∑ i, x ((t : Perm (Fin 11))⁻¹ i) = 0 := by
    rw [Equiv.sum_comp]
    exact hx
  have hv := h t (s16c11a11_vec_mk_mem_T1 hm)
  rw [s16c11AltAct_vec 11 t (hx' := hx')] at hv
  have hfun : (fun i => x ((t : Perm (Fin 11))⁻¹ i)) = x :=
    (s16c11AltVec_eq_iff (n := 11) (by decide)).1 hv
  simpa [t, Equiv.symm_apply_apply] using congr_fun hfun (m i)

theorem s16c11A11_fixed_classify {x : Fin 11 → ZMod 2} {hx : ∑ i, x i = 0}
    (h : ∀ t ∈ s16c11A11T1, S16C11AltAct 11 t (s16c11AltVec 11 x hx) = s16c11AltVec 11 x hx) :
    ∃ α β : ZMod 2, x = s16c11A11Fix α β := by
  have h01 : x 0 = x 1 := by
    simpa [show s16c11A11m1 0 = 1 by decide] using
      s16c11a11_vec_fix_rel h s16c11A11_m1_mem_T 0
  have h02 : x 0 = x 2 := by
    simpa [show s16c11A11m2 0 = 2 by decide] using
      s16c11a11_vec_fix_rel h s16c11A11_m2_mem_T 0
  have h04 : x 0 = x 4 := by
    simpa [show s16c11A11m3 0 = 4 by decide] using
      s16c11a11_vec_fix_rel h s16c11A11_m3_mem_T 0
  have h13 : x 1 = x 3 := by
    simpa [show s16c11A11m2 1 = 3 by decide] using
      s16c11a11_vec_fix_rel h s16c11A11_m2_mem_T 1
  have h15 : x 1 = x 5 := by
    simpa [show s16c11A11m3 1 = 5 by decide] using
      s16c11a11_vec_fix_rel h s16c11A11_m3_mem_T 1
  have h26 : x 2 = x 6 := by
    simpa [show s16c11A11m3 2 = 6 by decide] using
      s16c11a11_vec_fix_rel h s16c11A11_m3_mem_T 2
  have h37 : x 3 = x 7 := by
    simpa [show s16c11A11m3 3 = 7 by decide] using
      s16c11a11_vec_fix_rel h s16c11A11_m3_mem_T 3
  have h89 : x 8 = x 9 := by
    simpa [show s16c11A11u 8 = 9 by decide] using
      s16c11a11_vec_fix_rel h s16c11A11_u_mem_T 8
  have hpoint : ∀ i : Fin 11, x i =
      s16c11A11Fix (x 0) (x 8) i + (if i = 10 then x 10 else 0) := by
    intro i
    fin_cases i <;>
      simp [s16c11A11Fix, h01.symm, h02.symm, h04.symm, h13.symm, h15.symm, h26.symm, h37.symm,
        h89.symm]
  have hfix : (∑ i, s16c11A11Fix (x 0) (x 8) i) = 0 := s16c11A11Fix_sum (x 0) (x 8)
  have hsum : (∑ i, x i) = x 10 := by
    calc (∑ i, x i) = ∑ i,
            (s16c11A11Fix (x 0) (x 8) i + (if i = 10 then x 10 else 0)) :=
          Finset.sum_congr rfl (fun i _ => hpoint i)
      _ = (∑ i, s16c11A11Fix (x 0) (x 8) i) + ∑ i, (if i = 10 then x 10 else 0) :=
          Finset.sum_add_distrib
      _ = 0 + x 10 := by rw [hfix, Finset.sum_ite_eq']; simp
      _ = x 10 := zero_add _
  have hx10 : x 10 = 0 := by rw [← hsum]; exact hx
  refine ⟨x 0, x 8, ?_⟩
  funext i
  fin_cases i <;>
    simp [s16c11A11Fix, h01.symm, h02.symm, h04.symm, h13.symm, h15.symm, h26.symm, h37.symm,
      h89.symm, hx10]

theorem s16c11A11_orbit_cls_ncard :
    {z : (FFModel.altDn 11).Mod | ∃ g : ↥(alternatingGroup (Fin 11)),
      S16C11AltAct 11 g (s16c11A11Cls 10) = z}.ncard ≤ 11 := by
  have hsub : {z : (FFModel.altDn 11).Mod | ∃ g : ↥(alternatingGroup (Fin 11)),
      S16C11AltAct 11 g (s16c11A11Cls 10) = z} ⊆ Set.range s16c11A11Cls := by
    rintro z ⟨g, rfl⟩
    exact ⟨(g : Perm (Fin 11)) 10, by rw [s16c11A11_act_cls]⟩
  calc {z : (FFModel.altDn 11).Mod | ∃ g : ↥(alternatingGroup (Fin 11)),
        S16C11AltAct 11 g (s16c11A11Cls 10) = z}.ncard
      ≤ (Set.range s16c11A11Cls).ncard := Set.ncard_le_ncard hsub (Set.finite_range _)
    _ = 11 := by
        rw [Set.ncard_range_of_injective s16c11A11Cls_injective, Nat.card_eq_fintype_card,
          Fintype.card_fin]

theorem s16c11A11T1_fix_cls_ten {t : ↥(alternatingGroup (Fin 11))} (ht : t ∈ s16c11A11T1) :
    S16C11AltAct 11 t (s16c11A11Cls 10) = s16c11A11Cls 10 := by
  rw [s16c11A11_act_cls]
  have h10 : (t : Perm (Fin 11)) 10 = 10 :=
    (s16c11A11_mem_T_iff.1 (Subgroup.mem_subgroupOf.1 ht)).2
  rw [h10]

private def s16c11a11_vec_gOne : Fin 12 → Perm (Fin 11) :=
  ![1, swap 0 8 * swap 9 10, swap 1 8 * swap 9 10, swap 2 8 * swap 9 10,
    swap 3 8 * swap 9 10, swap 4 8 * swap 9 10, swap 5 8 * swap 9 10, swap 6 8 * swap 9 10,
    swap 7 8 * swap 9 10, swap 0 9 * swap 8 10, swap 1 9 * swap 8 10, swap 2 9 * swap 8 10]

private def s16c11a11_vec_gTwo : Fin 12 → Perm (Fin 11) :=
  ![1, swap 9 0 * swap 10 1, swap 9 1 * swap 10 2, swap 9 2 * swap 10 3,
    swap 9 3 * swap 10 4, swap 9 4 * swap 10 5, swap 9 5 * swap 10 6, swap 9 6 * swap 10 7,
    swap 9 7 * swap 10 0, swap 8 9 * swap 9 0, swap 8 9 * swap 9 1, swap 8 9 * swap 9 2]

private lemma s16c11a11_vec_gOne_mem :
    ∀ k, s16c11a11_vec_gOne k ∈ alternatingGroup (Fin 11) := by
  intro k
  fin_cases k <;>
    rw [Equiv.Perm.mem_alternatingGroup] <;>
    simp [s16c11a11_vec_gOne, Perm.sign_mul, Perm.sign_swap']

private lemma s16c11a11_vec_gTwo_mem :
    ∀ k, s16c11a11_vec_gTwo k ∈ alternatingGroup (Fin 11) := by
  intro k
  fin_cases k <;>
    rw [Equiv.Perm.mem_alternatingGroup] <;>
    simp [s16c11a11_vec_gTwo, Perm.sign_mul, Perm.sign_swap']

private lemma s16c11a11_vec_gOne_dist : ∀ k k' : Fin 12, k ≠ k' →
    (fun i => s16c11A11Fix 1 0 ((s16c11a11_vec_gOne k)⁻¹ i)) ≠
      (fun i => s16c11A11Fix 1 0 ((s16c11a11_vec_gOne k')⁻¹ i)) := by
  intro k k' hne
  fin_cases k <;> fin_cases k' <;> first | exact absurd rfl hne | decide

private lemma s16c11a11_vec_gTwo_dist : ∀ k k' : Fin 12, k ≠ k' →
    (fun i => s16c11A11Fix 0 1 ((s16c11a11_vec_gTwo k)⁻¹ i)) ≠
      (fun i => s16c11A11Fix 0 1 ((s16c11a11_vec_gTwo k')⁻¹ i)) := by
  intro k k' hne
  fin_cases k <;> fin_cases k' <;> first | exact absurd rfl hne | decide

private lemma s16c11a11_vec_orbit_gt_eleven (x : Fin 11 → ZMod 2) (hx : ∑ i, x i = 0)
    (g : Fin 12 → Perm (Fin 11)) (hg : ∀ k, g k ∈ alternatingGroup (Fin 11))
    (hdist : ∀ k k', k ≠ k' →
      (fun i => x ((g k)⁻¹ i)) ≠ (fun i => x ((g k')⁻¹ i))) :
    11 < {z : (FFModel.altDn 11).Mod | ∃ h : ↥(alternatingGroup (Fin 11)),
      S16C11AltAct 11 h (s16c11AltVec 11 x hx) = z}.ncard := by
  have h11 : ¬ 2 ∣ 11 := by decide
  let zF : Fin 12 → (FFModel.altDn 11).Mod := fun k =>
    S16C11AltAct 11 (⟨g k, hg k⟩ : ↥(alternatingGroup (Fin 11))) (s16c11AltVec 11 x hx)
  have hzF : Function.Injective zF := by
    intro k k' h
    by_contra hne
    apply hdist k k' hne
    have hk : zF k = s16c11AltVec 11 (fun i => x ((g k)⁻¹ i))
        (by rw [Equiv.sum_comp]; exact hx) := by
      dsimp only [zF]
      exact s16c11AltAct_vec 11 (⟨g k, hg k⟩ : ↥(alternatingGroup (Fin 11)))
    have hk' : zF k' = s16c11AltVec 11 (fun i => x ((g k')⁻¹ i))
        (by rw [Equiv.sum_comp]; exact hx) := by
      dsimp only [zF]
      exact s16c11AltAct_vec 11 (⟨g k', hg k'⟩ : ↥(alternatingGroup (Fin 11)))
    exact (s16c11AltVec_eq_iff h11).1 (by rw [← hk, ← hk']; exact h)
  have h12 : (Set.range zF).ncard = 12 := by
    rw [Set.ncard_range_of_injective hzF, Nat.card_eq_fintype_card, Fintype.card_fin]
  calc 11 < (Set.range zF).ncard := by rw [h12]; norm_num
    _ ≤ {z : (FFModel.altDn 11).Mod | ∃ h : ↥(alternatingGroup (Fin 11)),
          S16C11AltAct 11 h (s16c11AltVec 11 x hx) = z}.ncard :=
        Set.ncard_le_ncard (by
          rintro z ⟨k, rfl⟩
          exact ⟨(⟨g k, hg k⟩ : ↥(alternatingGroup (Fin 11))), rfl⟩)
          (Set.finite_range (fun h : ↥(alternatingGroup (Fin 11)) =>
            S16C11AltAct 11 h (s16c11AltVec 11 x hx)))

private lemma s16c11a11_vec_orbit_fix_one_zero :
    11 < {z : (FFModel.altDn 11).Mod | ∃ g : ↥(alternatingGroup (Fin 11)),
      S16C11AltAct 11 g (s16c11AltVec 11 (s16c11A11Fix 1 0)
        (s16c11A11Fix_sum 1 0)) = z}.ncard :=
  s16c11a11_vec_orbit_gt_eleven (s16c11A11Fix 1 0) (s16c11A11Fix_sum 1 0)
    s16c11a11_vec_gOne s16c11a11_vec_gOne_mem s16c11a11_vec_gOne_dist

private lemma s16c11a11_vec_orbit_fix_zero_one :
    11 < {z : (FFModel.altDn 11).Mod | ∃ g : ↥(alternatingGroup (Fin 11)),
      S16C11AltAct 11 g (s16c11AltVec 11 (s16c11A11Fix 0 1)
        (s16c11A11Fix_sum 0 1)) = z}.ncard :=
  s16c11a11_vec_orbit_gt_eleven (s16c11A11Fix 0 1) (s16c11A11Fix_sum 0 1)
    s16c11a11_vec_gTwo s16c11a11_vec_gTwo_mem s16c11a11_vec_gTwo_dist

theorem s16c11A11_orbit_fix_big {α β : ZMod 2} (h : (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1)) :
    11 < {z : (FFModel.altDn 11).Mod | ∃ g : ↥(alternatingGroup (Fin 11)),
      S16C11AltAct 11 g
        (s16c11AltVec 11 (s16c11A11Fix α β) (s16c11A11Fix_sum α β)) = z}.ncard := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact s16c11a11_vec_orbit_fix_one_zero
  · exact s16c11a11_vec_orbit_fix_zero_one

private def s16c11a11_vec_mF : Fin 4 → Perm (Fin 11) :=
  ![1, s16c11A11m1, s16c11A11m2, s16c11A11m3]

theorem s16c11A11T1_orbit_ncard_big (j : Fin 11) (hj : (j : ℕ) < 8) :
    2 < {w : (FFModel.altDn 11).Mod | ∃ t ∈ s16c11A11T1,
      S16C11AltAct 11 t (s16c11A11Cls j) = w}.ncard := by
  have hmF : ∀ k, s16c11a11_vec_mF k ∈ s16c11A11T := by
    intro k
    fin_cases k
    · exact s16c11A11T.one_mem
    · exact s16c11A11_m1_mem_T
    · exact s16c11A11_m2_mem_T
    · exact s16c11A11_m3_mem_T
  let zF : Fin 4 → (FFModel.altDn 11).Mod := fun k =>
    S16C11AltAct 11 (⟨s16c11a11_vec_mF k, s16c11A11_T_le_alt (hmF k)⟩ :
      ↥(alternatingGroup (Fin 11))) (s16c11A11Cls j)
  have hsub : Set.range zF ⊆ {w : (FFModel.altDn 11).Mod | ∃ t ∈ s16c11A11T1,
      S16C11AltAct 11 t (s16c11A11Cls j) = w} := by
    rintro w ⟨k, rfl⟩
    exact ⟨_, s16c11a11_vec_mk_mem_T1 (hmF k), rfl⟩
  have hinj : Function.Injective zF := by
    intro k k' h
    have hc : (s16c11a11_vec_mF k) j = (s16c11a11_vec_mF k') j := by
      apply s16c11A11Cls_injective
      have h1 : zF k = s16c11A11Cls ((s16c11a11_vec_mF k) j) := by
        dsimp only [zF]
        exact s16c11A11_act_cls ⟨s16c11a11_vec_mF k, s16c11A11_T_le_alt (hmF k)⟩ j
      have h2 : zF k' = s16c11A11Cls ((s16c11a11_vec_mF k') j) := by
        dsimp only [zF]
        exact s16c11A11_act_cls ⟨s16c11a11_vec_mF k', s16c11A11_T_le_alt (hmF k')⟩ j
      rw [h1, h2] at h
      exact h
    fin_cases k <;> fin_cases k' <;> fin_cases j <;>
      first
        | rfl
        | (exfalso; revert hc; decide)
        | (exfalso; revert hj; decide)
  have h4 : (Set.range zF).ncard = 4 := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have horbfin : {w : (FFModel.altDn 11).Mod | ∃ t ∈ s16c11A11T1,
      S16C11AltAct 11 t (s16c11A11Cls j) = w}.Finite :=
    (Set.finite_range (fun t : ↥(alternatingGroup (Fin 11)) =>
      S16C11AltAct 11 t (s16c11A11Cls j))).subset (by
        rintro w ⟨t, -, rfl⟩
        exact ⟨t, rfl⟩)
  calc 2 < (Set.range zF).ncard := by rw [h4]; norm_num
    _ ≤ {w : (FFModel.altDn 11).Mod | ∃ t ∈ s16c11A11T1,
          S16C11AltAct 11 t (s16c11A11Cls j) = w}.ncard :=
        Set.ncard_le_ncard hsub horbfin

private lemma s16c11a11_vec_cls_image_triple (σ : Perm (Fin 11)) :
    ({s16c11A11Cls (σ 10), s16c11A11Cls (σ 8), s16c11A11Cls (σ 9)} :
        Set (FFModel.altDn 11).Mod) =
      s16c11A11Cls '' ({σ 10, σ 8, σ 9} : Set (Fin 11)) := by
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro (h | h | h)
    · exact ⟨σ 10, Or.inl rfl, h.symm⟩
    · exact ⟨σ 8, Or.inr (Or.inl rfl), h.symm⟩
    · exact ⟨σ 9, Or.inr (Or.inr rfl), h.symm⟩
  · rintro ⟨i, hi, rfl⟩
    rcases hi with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private lemma s16c11a11_vec_cls_triple_eq_iff (σ : Perm (Fin 11)) :
    ({s16c11A11Cls (σ 10), s16c11A11Cls (σ 8), s16c11A11Cls (σ 9)} :
        Set (FFModel.altDn 11).Mod) =
      {s16c11A11Cls 10, s16c11A11Cls 8, s16c11A11Cls 9} ↔
    ({σ 10, σ 8, σ 9} : Set (Fin 11)) = {10, 8, 9} := by
  have hR : ({s16c11A11Cls 10, s16c11A11Cls 8, s16c11A11Cls 9} :
      Set (FFModel.altDn 11).Mod) = s16c11A11Cls '' ({10, 8, 9} : Set (Fin 11)) := by
    simpa using s16c11a11_vec_cls_image_triple (1 : Perm (Fin 11))
  rw [s16c11a11_vec_cls_image_triple σ, hR, Set.image_eq_image s16c11A11Cls_injective]

private lemma s16c11a11_vec_pres_iff (σ : Perm (Fin 11)) :
    σ ∈ s16c11A11Pres ↔ ({σ 10, σ 8, σ 9} : Set (Fin 11)) = {10, 8, 9} := by
  rw [s16c11A11Pres, s16c11A11Set3, MulAction.mem_stabilizer_iff]
  rw [show ({8, 9, 10} : Set (Fin 11)) = {10, 8, 9} from by
    ext i; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  rw [Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton, Perm.smul_def,
    Perm.smul_def, Perm.smul_def]

theorem s16c11A11_setStab_iff (g : ↥(alternatingGroup (Fin 11))) :
    g ∈ S16C11SetStab (S16C11AltAct 11)
        {s16c11A11Cls 10, s16c11A11Cls 8, s16c11A11Cls 9} ↔
      (g : Perm (Fin 11)) ∈ s16c11A11Pres := by
  show S16C11AltAct 11 g ∈ MulAction.stabilizer (MulAut (FFModel.altDn 11).Mod)
        {s16c11A11Cls 10, s16c11A11Cls 8, s16c11A11Cls 9} ↔
      (g : Perm (Fin 11)) ∈ s16c11A11Pres
  rw [MulAction.mem_stabilizer_iff]
  rw [Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton, MulAut.smul_def,
    MulAut.smul_def, MulAut.smul_def, s16c11A11_act_cls, s16c11A11_act_cls, s16c11A11_act_cls]
  rw [s16c11a11_vec_cls_triple_eq_iff, s16c11a11_vec_pres_iff]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
