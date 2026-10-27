module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
public import CFSG.Sporadic.Recognition.CoverTransferWords
public import CFSG.Sporadic.SuzOddCore.Perms
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndK

public section

namespace CFSG.Sporadic.Recognition.SuzMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Suz
  CFSG.Sporadic.Bridge.SuzGPL.Native CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.ComponentClassification.RankTwoSporadic.Suz

@[expose] noncomputable def suzBG (i : ℕ) : Equiv.Perm (Fin 1782) :=
  if i = 0 then suzB0 else suzB1

@[expose] noncomputable def suzGenP (i : ℕ) : Equiv.Perm (Fin 1782) :=
  wordIn 2 suzBG imgWords[i]!

theorem suzBG_mem (i : ℕ) : suzBG i ∈ suzM := by
  unfold suzBG
  split
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem suzGenP_mem (i : ℕ) : suzGenP i ∈ suzM :=
  wordIn_mem (fun j _ => suzBG_mem j) _

@[expose] noncomputable def suzGen (i : Fin gcS) : suzM := ⟨suzGenP i, suzGenP_mem i⟩

theorem tab_facts (h : suzTabCheck = true) :
    allPermsOK 1782 #[b0Arr, b1Arr] = true ∧ imgWords.size = 7 ∧
      imgWords.all (lettersOK 2) = true ∧ allPermsOK 1782 suzGenArrs = true ∧
      (∀ w ∈ suzTabWords, lettersOK gcS (zword w) = true ∧
        eqA 1782 (wordArr 1782 suzGenArrs (zword w)) (idA 1782) = true) ∧
      surjWords.size = 2 ∧ lettersOK 7 surjWords[0]! = true ∧ lettersOK 7 surjWords[1]! = true ∧
      eqA 1782 (wordArr 1782 suzGenArrs surjWords[0]!) b0Arr = true ∧
      eqA 1782 (wordArr 1782 suzGenArrs surjWords[1]!) b1Arr = true ∧
      countBelow (fun x => (suzGenArrs[3]!)[x]! == x) 1782 = 42 := by
  unfold suzTabCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, fun w hw => ?_, h6, h7, h8, h9, h10, h11⟩
  have := List.all_eq_true.1 h5 w hw
  simpa only [Bool.and_eq_true] using this

theorem rep_suzBG :
    ∀ i < 2, Rep 1782 (#[b0Arr, b1Arr] : Array (Array ℕ))[i]! (suzBG i) := by
  intro i hi
  interval_cases i
  · exact rep_b0
  · exact rep_b1

theorem rep_suzGenArrs (h : suzTabCheck = true) :
    ∀ i < 7, Rep 1782 suzGenArrs[i]! (suzGenP i) := by
  obtain ⟨h1, h2, h3, -⟩ := tab_facts h
  intro i hi
  have hi' : i < imgWords.size := by rw [h2]; exact hi
  have e : suzGenArrs[i]! = wordArr 1782 #[b0Arr, b1Arr] imgWords[i]! := by
    rw [suzGenArrs, getElem!_pos _ i (by rw [Array.size_map]; exact hi'), Array.getElem_map,
      getElem!_pos imgWords i hi']
  rw [e]
  refine rep_wordArr (by decide) rep_suzBG (fun j hj => isInvA_of_allPermsOK h1 (by
    simpa using hj)) ?_
  rw [getElem!_pos imgWords i hi']
  exact (Array.all_eq_true.1 h3) i hi'

theorem rep_suzWord (h : suzTabCheck = true)
    {w : List (Fin gcS × Bool)} (hw : lettersOK gcS (zword w) = true) :
    Rep 1782 (wordArr 1782 suzGenArrs (zword w))
      (FreeGroup.lift (fun i : Fin gcS => suzGenP i) (FreeGroup.mk w)) := by
  obtain ⟨-, h2, -, h4, -⟩ := tab_facts h
  have hsize : suzGenArrs.size = 7 := by rw [suzGenArrs, Array.size_map, h2]
  have h7 : gcS = 7 := rfl
  rw [lift_mk_eq_wordIn]
  exact rep_wordArr (by rw [hsize, h7]) (fun i hi => rep_suzGenArrs h i (by omega))
    (fun i hi => isInvA_of_allPermsOK h4 (by omega)) hw

theorem coe_lift_suzGen (x : FreeGroup (Fin gcS)) :
    (FreeGroup.lift suzGen x : Equiv.Perm (Fin 1782)) =
      FreeGroup.lift (fun i : Fin gcS => suzGenP i) x := by
  rw [← Subgroup.coe_subtype, ← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun i => by simp [suzGen]

theorem lift_suzGen_eq_one (h : suzTabCheck = true)
    {w : List (Fin gcS × Bool)} (hw : w ∈ suzTabWords) :
    FreeGroup.lift suzGen (FreeGroup.mk w) = 1 := by
  obtain ⟨hl, he⟩ := (tab_facts h).2.2.2.2.1 w hw
  apply Subtype.ext
  rw [coe_lift_suzGen]
  exact eq_of_eqA (rep_suzWord h hl) rep_idA he

@[expose] def suzCommW (i : Fin gcS) : FreeGroup (Fin gcS) := FreeGroup.mk (suzCommWord i)

theorem suzCommW_mem_commutator (i : Fin gcS) : suzCommW i ∈ commutator (FreeGroup (Fin gcS)) :=
  mk_commWords_mem_commutator _

theorem lift_suzCommW (h : suzTabCheck = true) (i : Fin gcS) :
    FreeGroup.lift suzGen (suzCommW i) = suzGen i := by
  have h1 := lift_suzGen_eq_one h (w := (i, false) :: suzCommWord i) (by
    unfold suzTabWords
    exact List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)))
  rw [show FreeGroup.mk ((i, false) :: suzCommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (suzCommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem lift_suzGen_R0 (h : suzTabCheck = true) :
    ∀ r ∈ wordSet R0, FreeGroup.lift suzGen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact lift_suzGen_eq_one h (by
    unfold suzTabWords
    exact List.mem_append_left _ (List.mem_append_left _ hw))

theorem lift_suzGen_R3 (h : suzTabCheck = true) :
    FreeGroup.lift suzGen (FreeGroup.mk suzR3) = 1 :=
  lift_suzGen_eq_one h (by unfold suzTabWords; exact List.mem_append_right _ List.mem_cons_self)

@[expose] def suzD : Fin gcS := ⟨3, by decide⟩

theorem suzGenP_d_sq (h : suzTabCheck = true) :
    suzGenP 3 ^ 2 = 1 := by
  have h1 := lift_suzGen_eq_one h (w := suzW [6, 6]) (by
    unfold suzTabWords
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have e : FreeGroup.mk (suzW [6, 6]) = FreeGroup.of suzD ^ 2 := by
    rw [show suzW [6, 6] = [(suzD, true), (suzD, true)] by decide, pow_two]
    rfl
  rw [e, map_pow, FreeGroup.lift_apply_of] at h1
  have h2 := congrArg Subtype.val h1
  rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
  exact h2

theorem suzGen_d_sq (h : suzTabCheck = true) :
    suzGen suzD ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact suzGenP_d_sq h

theorem wordArr_surj (h : suzTabCheck = true) {i : ℕ}
    (hi : i < 2) :
    Rep 1782 (wordArr 1782 suzGenArrs surjWords[i]!) (wordIn 7 suzGenP surjWords[i]!) := by
  obtain ⟨-, h2, -, h4, -, -, h7, h8, -⟩ := tab_facts h
  have hsize : suzGenArrs.size = 7 := by rw [suzGenArrs, Array.size_map, h2]
  refine rep_wordArr (by rw [hsize]) (fun j hj => rep_suzGenArrs h j hj)
    (fun j hj => isInvA_of_allPermsOK h4 (by omega)) ?_
  interval_cases i
  · exact h7
  · exact h8

theorem closure_suzGen (h : suzTabCheck = true) :
    Subgroup.closure (Set.range suzGen) = ⊤ := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, h10, -⟩ := tab_facts h
  have hb0 : wordIn 7 suzGenP surjWords[0]! = suzB0 :=
    eq_of_eqA (wordArr_surj h (by decide)) rep_b0 h9
  have hb1 : wordIn 7 suzGenP surjWords[1]! = suzB1 :=
    eq_of_eqA (wordArr_surj h (by decide)) rep_b1 h10
  have hmem : ∀ w : List ℤ,
      wordIn 7 suzGenP w ∈ Subgroup.closure (Set.range fun i : Fin gcS => suzGenP i) :=
    fun w => wordIn_mem (fun i hi =>
      Subgroup.subset_closure (Set.mem_range_self (f := fun i : Fin gcS => suzGenP i) ⟨i, hi⟩)) w
  have hP : Subgroup.closure (Set.range fun i : Fin gcS => suzGenP i) = suzM := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact suzGenP_mem i
    · rw [suzM, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · rw [← hb0]; exact hmem _
      · rw [← hb1]; exact hmem _
  apply Subgroup.map_injective suzM.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
  exact hP

theorem card_filter_fin_eq (n : ℕ) (p : ℕ → Bool) :
    (Finset.univ.filter fun x : Fin n => p x.val = true).card =
      ((Finset.range n).filter fun i => p i = true).card := by
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨x.2, hx⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨⟨i, hi.1⟩, by simpa using hi.2, rfl⟩

theorem fix1782_suzGenP_d (h : suzTabCheck = true) :
    fix1782 (suzGenP 3) = 42 := by
  have hc := (tab_facts h).2.2.2.2.2.2.2.2.2.2
  have hrep := rep_suzGenArrs h 3 (by decide)
  rw [countBelow_eq, ← card_filter_fin_eq] at hc
  have hset : (Finset.univ.filter fun x : Fin 1782 => suzGenP 3 x = x) =
      Finset.univ.filter fun x : Fin 1782 => ((suzGenArrs[3]!)[x.val]! == x.val) = true :=
    Finset.filter_congr fun x _ => by
      rw [beq_iff_eq, hrep x]
      exact ⟨fun hx => by rw [hx], fun hx => Fin.ext hx⟩
  rw [fix1782, hset, hc]

theorem orderOf_suzGenP_d (h : suzTabCheck = true) :
    orderOf (suzGenP 3) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (suzGenP_d_sq h) fun h1 => ?_
  have h42 := fix1782_suzGenP_d h
  have h0 : fix1782 (1 : Equiv.Perm (Fin 1782)) = 1782 := by simp [fix1782]
  rw [h1, h0] at h42
  exact absurd h42 (by decide)

end CFSG.Sporadic.Recognition.SuzMultiplier
