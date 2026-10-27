module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepChart

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def pk5_d (k : Fin 8) : ZMod 3 := ((k.val + 1 : ℕ) : ZMod 3)

@[expose] def pk5_mFunW (w : Fin 7 → ZMod 3) : Fin 8 → ZMod 3 :=
  let m6 : ZMod 3 := - w 6
  let m5 : ZMod 3 := 2 * m6 - w 5
  let m4 : ZMod 3 := 2 * m5 - m6 - w 4
  let m3 : ZMod 3 := 2 * m4 - m5 - w 3
  let m2 : ZMod 3 := 2 * m3 - m4 - w 2
  let m1 : ZMod 3 := 2 * m2 - m3 - w 1
  let m0 : ZMod 3 := 2 * m1 - m2 - w 0
  fun k => if k.val = 0 then m0 else if k.val = 1 then m1 else if k.val = 2 then m2
    else if k.val = 3 then m3 else if k.val = 4 then m4 else if k.val = 5 then m5
    else if k.val = 6 then m6 else 0

@[expose] def pk5_vOf (w : Fin 7 → ZMod 3) : Fin 8 → ZMod 3 :=
  fun k => if k.val = 0 then -(2 * w 0 + 3 * w 1 + 4 * w 2 + 5 * w 3 + 6 * w 4 + 7 * w 5 + 8 * w 6)
           else w ⟨k.val - 1, by omega⟩

def pk5_tail (u : Fin 8 → ZMod 3) : Fin 7 → ZMod 3 :=
  fun i => u ⟨i.val + 1, by omega⟩

lemma pk5_mFunW_spec (w : Fin 7 → ZMod 3) :
    ∀ k : Fin 8, ∑ j : Fin 8, ((cl k.val j.val : ℕ) : ZMod 3) * pk5_mFunW w j = pk5_vOf w k := by
  revert w
  decide +kernel

private lemma pk5_d_vOf (w : Fin 7 → ZMod 3) : ∑ k : Fin 8, pk5_d k * pk5_vOf w k = 0 := by
  revert w
  decide +kernel

@[expose] def pk5_mvW (w : Fin 7 → ZMod 3) : Fin 9 → ZMod 3 :=
  fun j => if h : j.val < 7 then pk5_mFunW w ⟨j.val, by omega⟩ else 0

lemma pk5_ker_zeroW (w : Fin 7 → ZMod 3) (i : Fin 8) :
    ∑ j : Fin 9, ((((alpha8 i).getD j.val 0 : ℕ) : ZMod 3)
        + (if j.val = 8 then pk5_vOf w i else 0)) * ((Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3) - pk5_mvW w) j = 0 := by
  revert w i
  decide +kernel

lemma pk5_hvw (u : Fin 8 → ZMod 3) (h0 : ∑ k : Fin 8, pk5_d k * u k = 0) :
    pk5_vOf (pk5_tail u) = u := by
  have hsum : ∑ k : Fin 8, pk5_d k * (u k - pk5_vOf (pk5_tail u) k) = 0 := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, h0, pk5_d_vOf, sub_zero]
  have hsingle : ∑ k : Fin 8, pk5_d k * (u k - pk5_vOf (pk5_tail u) k)
      = pk5_d 0 * (u 0 - pk5_vOf (pk5_tail u) 0) := by
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro b _ hb
      have hbval : b.val ≠ 0 := fun h => hb (Fin.ext (by simpa using h))
      have hbk : u b = pk5_vOf (pk5_tail u) b := by
        simp only [pk5_vOf, pk5_tail]
        rw [if_neg hbval]
        congr 1
        apply Fin.ext
        simp
        omega
      rw [hbk, sub_self, mul_zero]
    · intro h; exact absurd (Finset.mem_univ 0) h
  have hz : pk5_d 0 * (u 0 - pk5_vOf (pk5_tail u) 0) = 0 := by rw [← hsingle, hsum]
  have hd0 : pk5_d (0 : Fin 8) = 1 := by simp [pk5_d]
  have h0eq : u 0 = pk5_vOf (pk5_tail u) 0 := by
    rw [hd0, one_mul] at hz
    exact sub_eq_zero.mp hz
  funext k
  fin_cases k
  · exact h0eq.symm
  all_goals simp [pk5_vOf, pk5_tail]

private lemma pk5_sum_single (g : Fin 9 → ZMod 3) :
    (∑ j : Fin 9, g j • (Pi.single j (1 : ZMod 3) : Fin 9 → ZMod 3)) = g := by
  funext i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma pk5_dual_expand {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (E' : V ≃ₗ[ZMod 3] (Fin 9 → ZMod 3)) (φ : Module.Dual (ZMod 3) V)
    (f : Fin 9 → ZMod 3) (hf : ∀ j, φ (E'.symm (Pi.single j (1 : ZMod 3))) = f j) (v : V) :
    φ v = ∑ j : Fin 9, f j * E' v j := by
  have key : ∀ x : Fin 9 → ZMod 3, φ (E'.symm x) = ∑ j : Fin 9, x j * f j := by
    intro x
    conv_lhs => rw [show x = ∑ j : Fin 9, x j • (Pi.single j (1 : ZMod 3) : Fin 9 → ZMod 3)
      from (pk5_sum_single x).symm]
    rw [map_sum]
    simp only [map_smul]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hf j, smul_eq_mul]
  conv_lhs => rw [← LinearEquiv.symm_apply_apply E' v]
  rw [key]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

@[expose] def pk5_Tfun (du : ZMod 3) (mvT : Fin 9 → ZMod 3) (w : Fin 9 → ZMod 3) : Fin 9 → ZMod 3 :=
  w - (du * w 8) • mvT + ((du - 1) * w 8) • (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3)

@[expose] def pk5_Tinv (c : ZMod 3) (mvT : Fin 9 → ZMod 3) (w : Fin 9 → ZMod 3) : Fin 9 → ZMod 3 :=
  w + (w 8) • mvT + ((c - 1) * w 8) • (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3)

lemma pk5_Tfun_add (du : ZMod 3) (mvT : Fin 9 → ZMod 3) (x y : Fin 9 → ZMod 3) :
    pk5_Tfun du mvT (x + y) = pk5_Tfun du mvT x + pk5_Tfun du mvT y := by
  funext j
  simp only [pk5_Tfun, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma pk5_Tfun_smul (du : ZMod 3) (mvT : Fin 9 → ZMod 3) (a : ZMod 3) (x : Fin 9 → ZMod 3) :
    pk5_Tfun du mvT (a • x) = a • pk5_Tfun du mvT x := by
  funext j
  simp only [pk5_Tfun, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma pk5_T_left (du c : ZMod 3) (mvT : Fin 9 → ZMod 3) (hmvT8 : mvT 8 = 0)
    (hcd : c * du = 1) (w : Fin 9 → ZMod 3) :
    pk5_Tinv c mvT (pk5_Tfun du mvT w) = w := by
  have hcd' : du * c = 1 := by rw [mul_comm]; exact hcd
  funext j
  by_cases hj : j = 8
  · subst hj
    simp only [pk5_Tfun, pk5_Tinv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same]
    rw [hmvT8]
    ring_nf
    linear_combination (w 8) * hcd'
  · have hs : (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3) j = 0 := by
      simp [Pi.single_apply, hj]
    have h8 : (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3) 8 = 1 := by
      simp [Pi.single_apply]
    simp only [pk5_Tfun, pk5_Tinv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hs, h8, hmvT8]
    ring

lemma pk5_T_right (du c : ZMod 3) (mvT : Fin 9 → ZMod 3) (hmvT8 : mvT 8 = 0)
    (hdc : du * c = 1) (w : Fin 9 → ZMod 3) :
    pk5_Tfun du mvT (pk5_Tinv c mvT w) = w := by
  funext j
  by_cases hj : j = 8
  · subst hj
    simp only [pk5_Tfun, pk5_Tinv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same]
    rw [hmvT8]
    ring_nf
    linear_combination (w 8) * hdc
  · have hs : (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3) j = 0 := by
      simp [Pi.single_apply, hj]
    have h8 : (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3) 8 = 1 := by
      simp [Pi.single_apply]
    simp only [pk5_Tfun, pk5_Tinv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hs, h8, hmvT8]
    ring_nf
    linear_combination (-(w 8 * mvT j)) * hdc

lemma pk5_T_fix (du : ZMod 3) (mvT : Fin 9 → ZMod 3) (w : Fin 9 → ZMod 3) (hw : w 8 = 0) :
    pk5_Tfun du mvT w = w := by
  funext j
  simp only [pk5_Tfun, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hw,
    mul_zero, zero_smul, sub_zero, add_zero]

private lemma pk5_foldl_range_map (p D : ℕ) (F : ℕ → ℕ) :
    ((((List.range D).map F).foldl (· + ·) 0 : ℕ) : ZMod p) = ∑ i : Fin D, (F i.val : ZMod p) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [Nat.cast_add, ih, Fin.sum_univ_castSucc]
      simp

lemma pk5_ofFn_mem_allVecs : ∀ (n : ℕ) (f : Fin n → ℕ), (∀ i, f i < 3) → List.ofFn f ∈ allVecs n
  | 0, f, _ => by simp [allVecs]
  | n + 1, f, hf => by
      rw [List.ofFn_succ]
      simp only [allVecs, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨List.ofFn (fun i : Fin n => f i.succ), pk5_ofFn_mem_allVecs n _ (fun i => hf _), ?_⟩
      refine ⟨f 0, ?_, rfl⟩
      have h0 : f 0 = 0 ∨ f 0 = 1 ∨ f 0 = 2 := by
        have hlt := hf 0
        rcases h : f 0 with _ | _ | _ | n
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · rw [h] at hlt; omega
      simpa using h0

private lemma pk5_zip_map_eq (a b : Vec) (hlen : a.length = b.length) :
    (a.zip b).map (fun xy => xy.1 * xy.2)
      = (List.range a.length).map (fun i => a.getD i 0 * b.getD i 0) := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_zip, List.length_map, List.length_range]
    omega
  · intro i h1 h2
    have hia : i < a.length := by rw [List.length_map, List.length_zip] at h1; omega
    have hib : i < b.length := by rw [List.length_map, List.length_zip] at h1; omega
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_zip]
    rw [List.getD_eq_getElem _ _ hia, List.getD_eq_getElem _ _ hib]

private lemma pk5_zip_map_range (a b : Vec) (ha : a.length = 8) (hb : b.length = 8) :
    (a.zip b).map (fun xy => xy.1 * xy.2)
      = (List.range 8).map (fun i => a.getD i 0 * b.getD i 0) := by
  have hlen : a.length = b.length := by omega
  rw [pk5_zip_map_eq a b hlen, ha]

lemma pk5_dotv_cast (a b : Vec) (ha : a.length = 8) (hb : b.length = 8) :
    ((dotv a b : ℕ) : ZMod 3)
      = ∑ i : Fin 9, (a.getD i.val 0 : ZMod 3) * (b.getD i.val 0 : ZMod 3) := by
  rw [dotv, ZMod.natCast_mod, pk5_zip_map_range a b ha hb]
  rw [pk5_foldl_range_map 3 8 (fun i => a.getD i 0 * b.getD i 0)]
  have hcast : ∑ i : Fin 8, ((a.getD i.val 0 * b.getD i.val 0 : ℕ) : ZMod 3)
      = ∑ i : Fin 8, (a.getD i.val 0 : ZMod 3) * (b.getD i.val 0 : ZMod 3) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul]
  rw [hcast]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  rw [show (a.getD (Fin.last 8).val 0 : ZMod 3) * (b.getD (Fin.last 8).val 0 : ZMod 3) = 0 from by
    rw [show (Fin.last 8).val = 8 from rfl, List.getD_eq_default a 0 (by omega),
      List.getD_eq_default b 0 (by omega)]
    simp]
  rw [add_zero]
  rfl

lemma pk5_natCast3_inj {a b : ℕ} (ha : a < 3) (hb : b < 3) (h : (a : ZMod 3) = b) : a = b := by
  have hh := congrArg (fun z : ZMod 3 => z.val) h
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hh
  exact hh

lemma pk5_sum9_split (f : Fin 9 → ZMod 3) :
    ∑ j : Fin 9, f j = ∑ j : Fin 8, f (Fin.castSucc j) + f 8 := by
  rw [Fin.sum_univ_castSucc]
  rfl

lemma pk5_sum8_split (f : Fin 8 → ZMod 3) :
    ∑ j : Fin 8, f j = ∑ j : Fin 7, f (Fin.castSucc j) + f 7 := by
  rw [Fin.sum_univ_castSucc]
  rfl

lemma pk5_alpha8_length (k : ℕ) : (alpha8 k).length = 8 := by simp [alpha8]

lemma pk5_hvec8_length (k : ℕ) : (hvec8 k).length = 8 := by
  unfold hvec8; split <;> simp

lemma pk5_alpha8_getD (i : ℕ) (j : ℕ) (hj : j < 7) : (alpha8 i).getD j 0 = cl i j := by
  have hlen : j < (alpha8 i).length := by rw [pk5_alpha8_length]; omega
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [alpha8]
  rw [List.getElem_append_left (by simpa [List.length_map, List.length_range] using hj)]
  rw [List.getElem_map, List.getElem_range]

lemma pk5_alpha_chart {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod 3) V} {x : V}
    {u : Fin 8 → ZMod 3} (C : NineDepChart 9 h α x u) (i : Fin 8) (v : Fin 9 → ZMod 3) :
    α i (C.e.symm v) = ∑ j : Fin 9, ((((alpha8 i).getD j.val 0 : ℕ) : ZMod 3)
      + (if j.val = 8 then u i else 0)) * v j := by
  rw [C.α_eq i, LinearEquiv.apply_symm_apply]

lemma pk5_mem_addPairs8 (e : ℕ) (o : ℕ × ℕ × ℕ) (fa ha : Vec)
    (hha : ha ∈ allVecs 8) (hfa : fa ∈ allVecs 8)
    (hH : ∀ jj ∈ (embJ e).zipIdx, dotv (alpha8 jj.1) ha = (if jj.2 = o.1 then o.2.1 else 0))
    (hA : ∀ jj ∈ (embJ e).zipIdx, dotv fa (hvec8 jj.1) = (if jj.2 = o.1 then o.2.2 else 0))
    (h7 : fa.getD 7 0 ≠ 0) (h2 : dotv fa ha = 2) :
    (fa, ha) ∈ addPairs8 e o := by
  simp only [addPairs8]
  rw [List.mem_flatMap]
  refine ⟨ha, ?_, ?_⟩
  · rw [List.mem_filter]
    refine ⟨hha, ?_⟩
    rw [List.all_eq_true]
    intro jj hjj
    rw [hH jj hjj]
    simp
  · rw [List.mem_filterMap]
    refine ⟨fa, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨hfa, ?_⟩
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · simpa using h7
      · rw [List.all_eq_true]
        intro jj hjj
        rw [hA jj hjj]
        simp
    · rw [h2]
      simp

private lemma pk5_frame9m_getD (i : Fin 8) :
    (frame9m ()).getD i.val ⟨[], []⟩
      = ⟨alpha8 i.val ++ [if i.val = 0 then 1 else 0], hvec8 i.val ++ [0]⟩ := by
  rw [show frame9m () = (List.range 8).map (fun k =>
      (⟨alpha8 k ++ [if k = 0 then 1 else 0], hvec8 k ++ [0]⟩ : Refl)) from rfl]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

lemma pk5_gens_getD (fa hb : Vec) (i : Fin 8) :
    (frame9m () ++ [(⟨fa ++ [0], hb ++ [0]⟩ : Refl)]).getD i.val ⟨[], []⟩
      = ⟨alpha8 i.val ++ [if i.val = 0 then 1 else 0], hvec8 i.val ++ [0]⟩ := by
  rw [List.getD_append frame9m [(⟨fa ++ [0], hb ++ [0]⟩ : Refl)] ⟨[], []⟩ i.val
    (by simpa [frame9m] using i.isLt), pk5_frame9m_getD]

lemma pk5_gens_getD8 (fa hb : Vec) :
    (frame9m () ++ [(⟨fa ++ [0], hb ++ [0]⟩ : Refl)]).getD 8 ⟨[], []⟩ = ⟨fa ++ [0], hb ++ [0]⟩ := by
  rw [show frame9m () = (List.range 8).map (fun k =>
      (⟨alpha8 k ++ [if k = 0 then 1 else 0], hvec8 k ++ [0]⟩ : Refl)) from rfl]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right]
  · simp
  · simp

lemma pk5_pts9m_mem (s : ℕ) (o : ℕ × ℕ × ℕ) (hs : s ≤ 2) (ho : o ∈ kopts ()) (fa hb : Vec)
    (hmem : (fa, hb) ∈ addPairs8 s o) :
    (⟨3, 9, 8, frame9m () ++ [⟨fa ++ [0], hb ++ [0]⟩], [0, 0, 0, 0, 0, 0, 0, 1, 0],
      bound9⟩ : Pt) ∈ pts9m () := by
  simp only [pts9m]
  exact List.mem_flatMap.mpr ⟨s, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega,
    List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨(fa, hb), hmem, rfl⟩⟩⟩

end CFSG.TwoNodeSmall
