module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepChart
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallModel

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def pk3_psi {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (e : V ≃ₗ[ZMod 3] (Fin 8 → ZMod 3)) (αa : Module.Dual (ZMod 3) V) : Fin 8 → ZMod 3 :=
  fun i => αa (e.symm (Pi.single i 1))

private def pk3_toVec (w : Fin 8 → ZMod 3) : Vec := List.ofFn (fun i : Fin 8 => (w i).val)

private lemma pk3_getD_ofFn (f : Fin 8 → ℕ) (i : Fin 8) :
    (List.ofFn f).getD i.val 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

private lemma pk3_toVec_getD (w : Fin 8 → ZMod 3) (i : Fin 8) :
    (pk3_toVec w).getD i.val 0 = (w i).val :=
  pk3_getD_ofFn (fun i => (w i).val) i

private lemma pk3_toVec_length (w : Fin 8 → ZMod 3) : (pk3_toVec w).length = 8 := by
  simp [pk3_toVec, List.length_ofFn]

private lemma pk3_mem_allVecs : ∀ (n : ℕ) (l : List ℕ),
    l ∈ allVecs n ↔ l.length = n ∧ ∀ x ∈ l, x < 3
  | 0, l => by
      simp only [allVecs, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | n + 1, l => by
      constructor
      · intro hl
        simp only [allVecs, List.mem_flatMap, List.mem_map] at hl
        rcases hl with ⟨v, hv, a, ha, rfl⟩
        rw [pk3_mem_allVecs n] at hv
        have ha3 : a < 3 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          omega
        exact ⟨by simp [hv.1], fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ha3
          · exact hv.2 x hx⟩
      · rintro ⟨hlen, hlt⟩
        cases l with
        | nil => simp at hlen
        | cons a l' =>
          simp only [allVecs, List.mem_flatMap, List.mem_map]
          refine ⟨l', ?_, a, ?_, rfl⟩
          · rw [pk3_mem_allVecs n]
            exact ⟨by simpa using hlen, fun x hx => hlt x (by simp [hx])⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            have : a < 3 := hlt a (by simp)
            omega

private lemma pk3_toVec_mem_allVecs (w : Fin 8 → ZMod 3) : pk3_toVec w ∈ allVecs 8 := by
  rw [pk3_mem_allVecs]
  refine ⟨pk3_toVec_length w, ?_⟩
  intro x hx
  rw [pk3_toVec, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ZMod.val_lt _

private lemma pk3_zip_map (a b : List ℕ) :
    (a.zip b).map (fun xy => xy.1 * xy.2) = List.zipWith (fun x y => x * y) a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys => rw [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons, ih]

private lemma pk3_foldl_add_eq_sum (l : List ℕ) : l.foldl (· + ·) 0 = l.sum := by
  have h : ∀ a : ℕ, l.foldl (· + ·) a = a + l.sum := by
    induction l with
    | nil => intro a; simp
    | cons x xs ih =>
        intro a
        rw [List.foldl_cons, List.sum_cons, ih (a + x), Nat.add_assoc]
  simpa using h 0

private lemma pk3_sum_zipWith_fin {p : ℕ} :
    ∀ (a b : List ℕ), a.length = b.length →
      ((List.zipWith (fun x y => ((x * y : ℕ) : ZMod p)) a b).sum) =
        ∑ j : Fin a.length,
          (((a.getD j.val 0 : ℕ) : ZMod p) * ((b.getD j.val 0 : ℕ) : ZMod p)) := by
  intro a
  induction a with
  | nil =>
      intro b h
      have hb : b = [] := List.length_eq_zero_iff.mp h.symm
      subst hb
      simp
  | cons x as ih =>
      intro b h
      cases b with
      | nil => simp at h
      | cons y bs =>
          have h' : as.length = bs.length := Nat.succ.inj h
          rw [List.zipWith, List.sum_cons, ih bs h', List.length_cons,
            Fin.sum_univ_succ (n := as.length)]
          simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
          rw [Nat.cast_mul]

private lemma pk3_sum_fin_congr (f : ℕ → ZMod 3) {n : ℕ} (h : n = 8) :
    (∑ j : Fin n, f j) = ∑ j : Fin 8, f j := by
  subst h
  rfl

private lemma pk3_dotv_cast (a b : Vec) (ha : a.length = 8) (hb : b.length = 8) :
    ((dotv a b : ℕ) : ZMod 3)
      = ∑ j : Fin 8, (((a.getD j.val 0 : ℕ) : ZMod 3) * ((b.getD j.val 0 : ℕ) : ZMod 3)) := by
  have hlen : a.length = b.length := by rw [ha, hb]
  have hsum := pk3_sum_zipWith_fin (p := 3) a b hlen
  unfold dotv
  rw [ZMod.natCast_mod, pk3_zip_map, pk3_foldl_add_eq_sum, Nat.cast_list_sum, List.map_zipWith]
  rw [hsum]
  exact pk3_sum_fin_congr
    (fun j : ℕ => (((a.getD j 0 : ℕ) : ZMod 3) * ((b.getD j 0 : ℕ) : ZMod 3))) ha

private lemma pk3_dotv_lt (a b : Vec) : dotv a b < 3 := by
  unfold dotv
  exact Nat.mod_lt _ (by norm_num)

private lemma pk3_nat_eq_of_cast_eq {a b : ℕ} (ha : a < 3) (hb : b < 3)
    (h : (a : ZMod 3) = (b : ZMod 3)) : a = b := by
  have := congrArg ZMod.val h
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

private lemma pk3_pi_eq_sum (w : Fin 8 → ZMod 3) :
    w = ∑ i : Fin 8, w i • (Pi.single i (1 : ZMod 3) : Fin 8 → ZMod 3) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

private lemma pk3_dual_eq_sum (φ : Module.Dual (ZMod 3) (Fin 8 → ZMod 3))
    (w : Fin 8 → ZMod 3) :
    φ w = ∑ i : Fin 8, φ (Pi.single i (1 : ZMod 3)) * w i := by
  conv_lhs => rw [pk3_pi_eq_sum w]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

private lemma pk3_dual_eq_sum_psi {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (e : V ≃ₗ[ZMod 3] (Fin 8 → ZMod 3)) (αa : Module.Dual (ZMod 3) V)
    (w : Fin 8 → ZMod 3) :
    αa (e.symm w) = ∑ j : Fin 8, pk3_psi e αa j * w j := by
  have h := pk3_dual_eq_sum (αa.comp (e.symm : (Fin 8 → ZMod 3) →ₗ[ZMod 3] V)) w
  simpa [pk3_psi, LinearMap.comp_apply] using h

private lemma pk3_kopts_snd_lt (o : ℕ × ℕ × ℕ) (ho : o ∈ kopts ()) :
    o.2.1 < 3 ∧ o.2.2 < 3 := by
  simp only [kopts, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at ho
  rcases ho with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl <;> simp

private lemma pk3_needH_lt (o : ℕ × ℕ × ℕ) (ho : o ∈ kopts ()) (k : ℕ) :
    (if k = o.1 then o.2.1 else 0) < 3 := by
  have := (pk3_kopts_snd_lt o ho).1
  split <;> omega

private lemma pk3_needA_lt (o : ℕ × ℕ × ℕ) (ho : o ∈ kopts ()) (k : ℕ) :
    (if k = o.1 then o.2.2 else 0) < 3 := by
  have := (pk3_kopts_snd_lt o ho).2
  split <;> omega

private lemma pk3_mem_embJ_zipIdx {s : ℕ} {x : ℕ × ℕ} (h : x ∈ (embJ s).zipIdx) :
    x.1 = x.2 + s ∧ x.2 < 6 := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  rw [embJ, List.getElem?_map] at h
  by_cases hk : x.2 < 6
  · simp only [List.getElem?_range hk, Option.map_some, Option.some.injEq] at h
    exact ⟨h.symm, hk⟩
  · have hnone : (List.range 6)[x.2]? = none := by
      rw [List.getElem?_eq_none_iff]
      simpa using Nat.le_of_not_lt hk
    rw [hnone] at h
    simp at h

private lemma pk3_frame8_get (fa hb : Vec) (i : Fin 8) :
    ((frame8 () ++ [(⟨fa, hb⟩ : Refl)]).getD i.val (⟨[], []⟩ : Refl))
      = (⟨alpha8 i.val, hvec8 i.val⟩ : Refl) := by
  have hlen : (frame8 ()).length = 8 := by simp [frame8]
  have hi : i.val < (frame8 () ++ [(⟨fa, hb⟩ : Refl)]).length := by
    simp only [List.length_append, hlen, List.length_cons, List.length_nil]
    omega
  rw [List.getD_eq_getElem _ _ hi, List.getElem_append_left (by omega)]
  simp only [frame8, List.getElem_map, List.getElem_range]

private lemma pk3_frame8_get_last (fa hb : Vec) :
    ((frame8 () ++ [(⟨fa, hb⟩ : Refl)]).getD 8 (⟨[], []⟩ : Refl)) = (⟨fa, hb⟩ : Refl) := by
  have hlen : (frame8 ()).length = 8 := by simp [frame8]
  have h8 : 8 < (frame8 () ++ [(⟨fa, hb⟩ : Refl)]).length := by
    simp only [List.length_append, hlen, List.length_cons, List.length_nil]
    omega
  rw [List.getD_eq_getElem _ _ h8, List.getElem_append_right (by omega)]
  simp

private lemma pk3_x_getD (j : Fin 8) :
    (([0, 0, 0, 0, 0, 0, 0, 1, 0] : List ℕ).getD j.val 0)
      = (([0, 0, 0, 0, 0, 0, 0, 1] : List ℕ).getD j.val 0) := by
  fin_cases j <;> rfl

private lemma pk3_hvec8_length (k : ℕ) : (hvec8 k).length = 8 := by
  rw [hvec8]
  split <;> simp

private lemma pk3_mem_addPairs8 {e : ℕ} {o : ℕ × ℕ × ℕ} {fa hb : Vec}
    (hhb : hb ∈ allVecs 8)
    (hHc : ∀ x ∈ (embJ e).zipIdx, dotv (alpha8 x.1) hb = (if x.2 = o.1 then o.2.1 else 0))
    (hfa : fa ∈ allVecs 8)
    (hfa7 : fa.getD 7 0 ≠ 0)
    (hAc : ∀ x ∈ (embJ e).zipIdx, dotv fa (hvec8 x.1) = (if x.2 = o.1 then o.2.2 else 0))
    (hdot : dotv fa hb = 2) :
    (fa, hb) ∈ addPairs8 e o := by
  simp only [addPairs8]
  refine List.mem_flatMap.mpr ⟨hb, ?_, ?_⟩
  · rw [List.mem_filter]
    refine ⟨hhb, ?_⟩
    rw [List.all_eq_true]
    intro x hx
    simp only [hHc x hx, beq_iff_eq]
  · refine List.mem_filterMap.mpr ⟨fa, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨hfa, ?_⟩
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [bne_iff_ne]; exact hfa7
      · rw [List.all_eq_true]
        intro x hx
        simp only [hAc x hx, beq_iff_eq]
    · rw [if_pos (by simp [hdot])]

theorem ninedep_model_8 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (h : Fin 8 → V)
    (α : Fin 8 → Module.Dual (ZMod 3) V) (x : V) (u : Fin 8 → ZMod 3)
    (C : NineDepChart 8 h α x u) (ha : V) (αa : Module.Dual (ZMod 3) V) (hha : αa ha = 2)
    (hx : αa x ≠ 0) (s : ℕ) (hs : s ≤ 2) (o : ℕ × ℕ × ℕ) (ho : o ∈ kopts ())
    (hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3))
    (hA : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod 3)) :
    ∃ (nF : ℕ) (gens : List Refl) (x' : Vec) (b : ℕ),
      (⟨3, 8, nF, gens, x', b⟩ : Pt) ∈ pts8 () ∧
      ∃ e : V ≃ₗ[ZMod 3] (Fin 8 → ZMod 3), (⟨3, 8, nF, gens, x', b⟩ : Pt).Models e h α x ha αa := by
  set hb : Vec := pk3_toVec (C.e ha) with hb_def
  set fa : Vec := pk3_toVec (pk3_psi C.e αa) with fa_def
  have hx_e : C.e x = (Pi.single (⟨7, by decide⟩ : Fin 8) 1 : Fin 8 → ZMod 3) := by
    funext j
    rw [C.x_eq j]
    fin_cases j <;> simp
  have hfa7 : fa.getD 7 0 ≠ 0 := by
    rw [fa_def]
    change (pk3_toVec (pk3_psi C.e αa)).getD (⟨7, by decide⟩ : Fin 8).val 0 ≠ 0
    rw [pk3_toVec_getD]
    intro hval
    have hpsi7 : pk3_psi C.e αa ⟨7, by decide⟩ = αa x := by
      show αa (C.e.symm (Pi.single ⟨7, by decide⟩ 1)) = αa x
      rw [← hx_e, LinearEquiv.symm_apply_apply]
    rw [hpsi7] at hval
    exact hx ((ZMod.val_eq_zero _).mp hval)
  have hHc : ∀ xx ∈ (embJ s).zipIdx,
      dotv (alpha8 xx.1) hb = (if xx.2 = o.1 then o.2.1 else 0) := by
    intro xx hxx
    obtain ⟨hx1, hx2⟩ := pk3_mem_embJ_zipIdx hxx
    have hx8 : xx.1 < 8 := by omega
    let i : Fin 8 := ⟨xx.1, hx8⟩
    have hi : (i : ℕ) = xx.1 := by simp [i]
    have hle : s ≤ i := by omega
    have hlt : (i : ℕ) < s + 6 := by omega
    have hcast : ((dotv (alpha8 xx.1) hb : ℕ) : ZMod 3) = α i ha := by
      rw [pk3_dotv_cast (alpha8 xx.1) hb (by simp [alpha8]) (pk3_toVec_length _)]
      rw [C.α_eq i ha]
      apply Finset.sum_congr rfl
      intro j _
      rw [hb_def, pk3_toVec_getD, ZMod.natCast_zmod_val,
        if_neg (by omega : ¬ (j : ℕ) = 8)]
      ring
    have hval : α i ha = ((if xx.2 = o.1 then o.2.1 else 0 : ℕ) : ZMod 3) := by
      have hh := hH i hle hlt
      rwa [show (i : ℕ) - s = xx.2 by omega] at hh
    exact pk3_nat_eq_of_cast_eq (pk3_dotv_lt _ _) (pk3_needH_lt o ho xx.2) (hcast.trans hval)
  have hAc : ∀ xx ∈ (embJ s).zipIdx,
      dotv fa (hvec8 xx.1) = (if xx.2 = o.1 then o.2.2 else 0) := by
    intro xx hxx
    obtain ⟨hx1, hx2⟩ := pk3_mem_embJ_zipIdx hxx
    have hx8 : xx.1 < 8 := by omega
    let i : Fin 8 := ⟨xx.1, hx8⟩
    have hi : (i : ℕ) = xx.1 := by simp [i]
    have hle : s ≤ i := by omega
    have hlt : (i : ℕ) < s + 6 := by omega
    have hsum_psi : (∑ j : Fin 8,
          (((fa.getD j.val 0 : ℕ) : ZMod 3) * (((hvec8 xx.1).getD j.val 0 : ℕ) : ZMod 3)))
        = ∑ j : Fin 8, pk3_psi C.e αa j * C.e (h i) j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [fa_def, pk3_toVec_getD, ZMod.natCast_zmod_val]
      congr 1
      exact (C.h_eq i j).symm
    have hcast : ((dotv fa (hvec8 xx.1) : ℕ) : ZMod 3) = αa (h i) := by
      rw [pk3_dotv_cast fa (hvec8 xx.1) (pk3_toVec_length _) (pk3_hvec8_length xx.1), hsum_psi]
      exact (pk3_dual_eq_sum_psi C.e αa (C.e (h i))).symm.trans
        (congrArg αa (LinearEquiv.symm_apply_apply C.e (h i)))
    have hval : αa (h i) = ((if xx.2 = o.1 then o.2.2 else 0 : ℕ) : ZMod 3) := by
      have hh := hA i hle hlt
      rwa [show (i : ℕ) - s = xx.2 by omega] at hh
    exact pk3_nat_eq_of_cast_eq (pk3_dotv_lt _ _) (pk3_needA_lt o ho xx.2) (hcast.trans hval)
  have hdot : dotv fa hb = 2 := by
    have hsum_psi : (∑ j : Fin 8,
          (((fa.getD j.val 0 : ℕ) : ZMod 3) * ((hb.getD j.val 0 : ℕ) : ZMod 3)))
        = ∑ j : Fin 8, pk3_psi C.e αa j * C.e ha j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [fa_def, hb_def, pk3_toVec_getD, pk3_toVec_getD, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val]
    have hcast : ((dotv fa hb : ℕ) : ZMod 3) = αa ha := by
      rw [pk3_dotv_cast fa hb (pk3_toVec_length _) (pk3_toVec_length _), hsum_psi]
      exact (pk3_dual_eq_sum_psi C.e αa (C.e ha)).symm.trans
        (congrArg αa (LinearEquiv.symm_apply_apply C.e ha))
    have h2 : αa ha = ((2 : ℕ) : ZMod 3) := by rw [hha]; rfl
    exact pk3_nat_eq_of_cast_eq (pk3_dotv_lt _ _) (by norm_num) (hcast.trans h2)
  refine ⟨8, frame8 () ++ [⟨fa, hb⟩], [0, 0, 0, 0, 0, 0, 0, 1], bound9, ?_, C.e, ?_⟩
  · unfold pts8
    refine List.mem_flatMap.mpr ⟨s, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    · refine List.mem_flatMap.mpr ⟨o, ho, ?_⟩
      exact List.mem_map.mpr ⟨(fa, hb),
        pk3_mem_addPairs8 (pk3_toVec_mem_allVecs (C.e ha)) hHc
          (pk3_toVec_mem_allVecs (pk3_psi C.e αa)) hfa7 hAc hdot, rfl⟩
  · unfold Pt.Models
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [frame8]
    · funext j
      simp only [C.x_eq j, Pt.vec, pk3_x_getD j]
    · intro i
      refine ⟨?_, ?_⟩
      · funext j
        simp only [pk3_frame8_get fa hb i, C.h_eq i j, Pt.vec]
      · intro w
        simp only [pk3_frame8_get fa hb i, C.α_eq i w, Pt.dot, Pt.vec]
        apply Finset.sum_congr rfl
        intro j _
        simp [if_neg (by omega : ¬ (j : ℕ) = 8)]
    · simp only [pk3_frame8_get_last fa hb]
      funext j
      simp only [Pt.vec, hb_def, pk3_toVec_getD, ZMod.natCast_zmod_val]
    · intro w
      simp only [pk3_frame8_get_last fa hb, Pt.dot, Pt.vec]
      rw [show (∑ j : Fin 8, (((fa.getD j.val 0 : ℕ) : ZMod 3) * C.e w j))
            = ∑ j : Fin 8, pk3_psi C.e αa j * C.e w j from by
          apply Finset.sum_congr rfl
          intro j _
          simp only [fa_def, pk3_toVec_getD, ZMod.natCast_zmod_val]]
      exact (congrArg αa (LinearEquiv.symm_apply_apply C.e w).symm).trans
        (pk3_dual_eq_sum_psi C.e αa (C.e w))

end CFSG.TwoNodeSmall
