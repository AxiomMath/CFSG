module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G2YTransport
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DataG2Y

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def w183finSp44G2Y_corRowValid
    (c : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Bool :=
  validB (c.2.1, c.2.2.1) && validB (c.2.2.2.1, c.2.2.2.2.1) &&
  validB (c.2.2.2.2.2.1, c.2.2.2.2.2.2.1) &&
  validB (c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2)

theorem w183finSp44G2Y_corData_valid :
    corData.all (fun R => R.all w183finSp44G2Y_corRowValid) = true := by decide +kernel

theorem w183finSp44G2Y_pool_valid :
    g2Pool.all (fun q => validB (q / 4, q % 4)) = true := by decide +kernel

theorem w183finSp44G2Y_g2Pool_length : g2Pool.length = 202 := by decide +kernel

theorem w183finSp44G2Y_rows_bound : g2Rows.all (fun R => R.all (fun e => e ≤ 606)) = true := by
  decide +kernel

theorem w183finSp44G2Y_invs_nodup : invs.Nodup := by decide +kernel

theorem w183finSp44G2Y_invsA_ne {i j : Nat} (hi : i < n127) (hj : j < n127) (hij : i < j) :
    invsA[i]! ≠ invsA[j]! := by
  intro h
  have hi' : i < invs.length := hi
  have hj' : j < invs.length := hj
  have h1 : invsA[i]! = invs[i]'hi' := by
    rw [invsA, List.getElem!_toArray, List.getElem!_eq_getElem?_getD,
      ← List.getD_eq_getElem?_getD]
    exact (List.getElem_eq_getD (l := invs) (i := i) (h := hi') default).symm
  have h2 : invsA[j]! = invs[j]'hj' := by
    rw [invsA, List.getElem!_toArray, List.getElem!_eq_getElem?_getD,
      ← List.getD_eq_getElem?_getD]
    exact (List.getElem_eq_getD (l := invs) (i := j) (h := hj') default).symm
  exact absurd ((List.Nodup.getElem_inj_iff w183finSp44G2Y_invs_nodup (hi := hi')
    (hj := hj')).mp (by rw [← h1, ← h2]; exact h)) (ne_of_lt hij)

theorem w183finSp44G2Y_invsA_ne_pair {p : Nat × Nat} (hp : p ∈ pairsL) :
    invsA[p.1]! ≠ invsA[p.2]! := by
  obtain ⟨h12, h2, -⟩ := (mem_pairsL_iff p).mp hp
  have h2n : p.2 < n127 := by
    have : n127 = 127 := invs_length
    rwa [this]
  exact w183finSp44G2Y_invsA_ne (lt_trans h12 h2n) h2n h12

theorem w183finSp44G2Y_gmulE_ne_one {p : Nat × Nat} (hp : p ∈ pairsL) :
    gmulE invsA[p.1]! invsA[p.2]! ≠ oneE := by
  intro h
  have hva := w183finSp44G2Y_valid_a hp
  have hvb := w183finSp44G2Y_valid_b hp
  have hb2 : autOf invsA[p.2]! * autOf invsA[p.2]! = 1 :=
    w183finSp44G2Y_autOf_self_of_klein hp (w183finSp44G2Y_mem_klein_iff.mpr
      (Or.inr (Or.inr (Or.inl rfl))))
  have hauto : autOf invsA[p.1]! = autOf invsA[p.2]! := by
    have h1 : autOf (gmulE invsA[p.1]! invsA[p.2]!) = 1 := by rw [h, autOf_oneE]
    rw [autOf_gmulE hva hvb] at h1
    calc autOf invsA[p.1]! = autOf invsA[p.1]! * (autOf invsA[p.2]! * autOf invsA[p.2]!) := by
          rw [hb2, mul_one]
      _ = (autOf invsA[p.1]! * autOf invsA[p.2]!) * autOf invsA[p.2]! := by group
      _ = 1 * autOf invsA[p.2]! := by rw [h1]
      _ = autOf invsA[p.2]! := by rw [one_mul]
  exact w183finSp44G2Y_invsA_ne_pair hp (autOf_inj hva hvb hauto)

theorem w183finSp44G2Y_lt_n127_a {p : Nat × Nat} (hp : p ∈ pairsL) : p.1 < n127 := by
  obtain ⟨h12, h2, -⟩ := (mem_pairsL_iff p).mp hp
  have h2n : p.2 < n127 := by
    have : n127 = 127 := invs_length
    rwa [this]
  exact lt_trans h12 h2n

theorem w183finSp44G2Y_lt_n127_b {p : Nat × Nat} (hp : p ∈ pairsL) : p.2 < n127 := by
  obtain ⟨-, h2, -⟩ := (mem_pairsL_iff p).mp hp
  have : n127 = 127 := invs_length
  rwa [this]

theorem w183finSp44G2Y_getD_ne_one {p : Nat × Nat} (hp : p ∈ pairsL) {i : Nat}
    (hi : i < 3) :
    [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!].getD i oneE ≠ oneE := by
  have hmem : [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!].getD i oneE ∈
      [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!] := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  intro hone
  rw [hone] at hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact w183finSp44G2Y_ne_one_of_mem_invs (w183finSp44G2Y_mem_invsA
      (w183finSp44G2Y_lt_n127_a hp)) h.symm
  · rcases List.mem_cons.mp h with h | h
    · exact w183finSp44G2Y_ne_one_of_mem_invs (w183finSp44G2Y_mem_invsA
        (w183finSp44G2Y_lt_n127_b hp)) h.symm
    · rcases List.mem_cons.mp h with h | h
      · exact w183finSp44G2Y_gmulE_ne_one hp h.symm
      · simp at h

theorem w183finSp44G2Y_valid_of_mem_map_conj {p : Nat × Nat} (hp : p ∈ pairsL) {g : El}
    (hg : validB g = true) {z : El}
    (hz : z ∈ (klein invsA[p.1]! invsA[p.2]!).map (conjE g)) : validB z = true := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  exact validB_conjE hg (w183finSp44G2Y_valid_klein (w183finSp44G2Y_valid_a hp)
    (w183finSp44G2Y_valid_b hp) hw)

theorem w183finSp44G2Y_exists_autOf_of_mem_map_conj {p : Nat × Nat} (hp : p ∈ pairsL)
    {g : El} (hg : validB g = true) {α : MulAut S4}
    (hα : α ∈ (kleinSub invsA[p.1]! invsA[p.2]!).map
      (MulAut.conj (autOf g)).toMonoidHom) :
    ∃ z, z ∈ (klein invsA[p.1]! invsA[p.2]!).map (conjE g) ∧ autOf z = α := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hα
  obtain ⟨w, hw, rfl⟩ := (mem_kleinSub_iff hp s).mp hs
  have hvw := w183finSp44G2Y_valid_klein (w183finSp44G2Y_valid_a hp)
    (w183finSp44G2Y_valid_b hp) hw
  refine ⟨conjE g w, List.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
  change autOf (conjE g w) = autOf g * autOf w * (autOf g)⁻¹
  exact autOf_conjE hg hvw

theorem w183finSp44G2Y_map_conj_eq_of_sameSet {p : Nat × Nat} (hp : p ∈ pairsL)
    {g1 gA : El} (hg1 : validB g1 = true) (hgA : validB gA = true)
    (h : sameSet ((klein invsA[p.1]! invsA[p.2]!).map (conjE g1))
      ((klein invsA[p.1]! invsA[p.2]!).map (conjE gA)) = true) :
    (kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf g1)).toMonoidHom =
      (kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf gA)).toMonoidHom := by
  have hiff := w183finSp44G2Y_sameSet_eq_true.mp h
  apply le_antisymm
  · intro α hα
    obtain ⟨z, hz, hzα⟩ := w183finSp44G2Y_exists_autOf_of_mem_map_conj hp hg1 hα
    rw [← hzα]
    exact (w183finSp44G2Y_autOf_mem_map_conjE hp hgA
      (w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hz)).mpr ((hiff z).mp hz)
  · intro α hα
    obtain ⟨z, hz, hzα⟩ := w183finSp44G2Y_exists_autOf_of_mem_map_conj hp hgA hα
    rw [← hzα]
    exact (w183finSp44G2Y_autOf_mem_map_conjE hp hg1
      (w183finSp44G2Y_valid_of_mem_map_conj hp hgA hz)).mpr ((hiff z).mpr hz)

theorem w183finSp44G2Y_commute_sub_of_commute_code {p : Nat × Nat} (hp : p ∈ pairsL)
    {g1 gA : El} (hg1 : validB g1 = true) (hgA : validB gA = true)
    (h : ∀ u ∈ (klein invsA[p.1]! invsA[p.2]!).map (conjE gA),
      ∀ v ∈ (klein invsA[p.1]! invsA[p.2]!).map (conjE g1), gmulE u v = gmulE v u) :
    ∀ a ∈ (kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf gA)).toMonoidHom,
      ∀ x ∈ (kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf g1)).toMonoidHom,
        a * x = x * a := by
  intro a ha x hx
  obtain ⟨u, hu, rfl⟩ := w183finSp44G2Y_exists_autOf_of_mem_map_conj hp hgA ha
  obtain ⟨v, hv, rfl⟩ := w183finSp44G2Y_exists_autOf_of_mem_map_conj hp hg1 hx
  rw [← autOf_gmulE (w183finSp44G2Y_valid_of_mem_map_conj hp hgA hu)
      (w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hv),
    ← autOf_gmulE (w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hv)
      (w183finSp44G2Y_valid_of_mem_map_conj hp hgA hu), h u hu v hv]

theorem w183finSp44G2Y_sameSet_map_conjE_of_mem_normalizer {p : Nat × Nat} (hp : p ∈ pairsL)
    {g x : El} (hg : validB g = true) (hx : validB x = true) (hx2 : gmulE x x = oneE)
    (hN : autOf x ∈ Subgroup.normalizer
      ((kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf g)).toMonoidHom :
        Set (MulAut S4))) :
    sameSet (((klein invsA[p.1]! invsA[p.2]!).map (conjE g)).map (conjE x))
      ((klein invsA[p.1]! invsA[p.2]!).map (conjE g)) = true := by
  rw [w183finSp44G2Y_sameSet_eq_true]
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    have hvw := w183finSp44G2Y_valid_of_mem_map_conj hp hg hw
    have hwA : autOf w ∈ (kleinSub invsA[p.1]! invsA[p.2]!).map
        (MulAut.conj (autOf g)).toMonoidHom :=
      (w183finSp44G2Y_autOf_mem_map_conjE hp hg hvw).mpr hw
    have hconj : autOf x * autOf w * (autOf x)⁻¹ ∈
        (kleinSub invsA[p.1]! invsA[p.2]!).map
          (MulAut.conj (autOf g)).toMonoidHom :=
      (Subgroup.mem_normalizer_iff.mp hN) (autOf w) |>.mp hwA
    rw [← autOf_conjE hx hvw] at hconj
    exact (w183finSp44G2Y_autOf_mem_map_conjE hp hg (validB_conjE hx hvw)).mp hconj
  · intro hz
    have hvz := w183finSp44G2Y_valid_of_mem_map_conj hp hg hz
    have hzA : autOf z ∈ (kleinSub invsA[p.1]! invsA[p.2]!).map
        (MulAut.conj (autOf g)).toMonoidHom :=
      (w183finSp44G2Y_autOf_mem_map_conjE hp hg hvz).mpr hz
    have hconj : autOf x * autOf z * (autOf x)⁻¹ ∈
        (kleinSub invsA[p.1]! invsA[p.2]!).map
          (MulAut.conj (autOf g)).toMonoidHom :=
      (Subgroup.mem_normalizer_iff.mp hN) (autOf z) |>.mp hzA
    have hw' : conjE x z ∈ (klein invsA[p.1]! invsA[p.2]!).map (conjE g) :=
      (w183finSp44G2Y_autOf_mem_map_conjE hp hg (validB_conjE hx hvz)).mp (by
        rw [autOf_conjE hx hvz]; exact hconj)
    exact List.mem_map.mpr ⟨conjE x z, hw', w183finSp44G2Y_conjE_conjE hx hvz hx2⟩

theorem w183finSp44G2Y_mem_Z {p : Nat × Nat} {g1 g2 : El} {w : El}
    (hw : memK ((klein invsA[p.1]! invsA[p.2]!).map (conjE g1) |>.flatMap fun u =>
      ((klein invsA[p.1]! invsA[p.2]!).map (conjE g2)).map fun v => gmulE u v) w = true) :
    ∃ u ∈ (klein invsA[p.1]! invsA[p.2]!).map (conjE g1),
      ∃ v ∈ (klein invsA[p.1]! invsA[p.2]!).map (conjE g2), gmulE u v = w := by
  rw [w183finSp44G2Y_memK_eq_true] at hw
  obtain ⟨u, hu, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v, hv, hvu⟩ := List.mem_map.mp hw
  exact ⟨u, hu, v, hv, hvu⟩

theorem w183finSp44G2Y_exists_z_rel {p : Nat × Nat} (hp : p ∈ pairsL) {g1 g2 y : El}
    (hg1 : validB g1 = true) (hg2 : validB g2 = true) (hy : validB y = true)
    (h4 : ∀ s ∈ [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!],
      memK ((klein invsA[p.1]! invsA[p.2]!).map (conjE g1) |>.flatMap fun u =>
        ((klein invsA[p.1]! invsA[p.2]!).map (conjE g2)).map fun v => gmulE u v)
        (gmulE s (conjE y s)) = true) :
    ∀ s ∈ kleinSub invsA[p.1]! invsA[p.2]!,
      ∃ z ∈ Subgroup.closure
        (((kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf g1)).toMonoidHom :
            Set (MulAut S4)) ∪
          ((kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf g2)).toMonoidHom :
            Set (MulAut S4))),
        autOf y * s * (autOf y)⁻¹ = s * z := by
  intro s hs
  have hva := w183finSp44G2Y_valid_a hp
  have hvb := w183finSp44G2Y_valid_b hp
  obtain ⟨sc, hsc, hscs⟩ := (mem_kleinSub_iff hp s).mp hs
  have hvsc := w183finSp44G2Y_valid_klein hva hvb hsc
  rcases w183finSp44G2Y_mem_klein_iff.mp hsc with h | h | h | h
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [← hscs, h, autOf_oneE]
    simp
  · have hmem : sc ∈ [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!] := by
      rw [h]; simp
    obtain ⟨u, hu, v, hv, huv⟩ := w183finSp44G2Y_mem_Z (h4 sc hmem)
    refine ⟨autOf u * autOf v, ?_, ?_⟩
    · apply Subgroup.mul_mem
      · exact Subgroup.subset_closure (Set.mem_union_left _ ((w183finSp44G2Y_autOf_mem_map_conjE
          hp hg1 (w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hu)).mpr hu))
      · exact Subgroup.subset_closure (Set.mem_union_right _ ((w183finSp44G2Y_autOf_mem_map_conjE
          hp hg2 (w183finSp44G2Y_valid_of_mem_map_conj hp hg2 hv)).mpr hv))
    · rw [← hscs]
      have huValid := w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hu
      have hvValid := w183finSp44G2Y_valid_of_mem_map_conj hp hg2 hv
      have hcalc : autOf sc * (autOf u * autOf v) = autOf y * autOf sc * (autOf y)⁻¹ := by
        calc autOf sc * (autOf u * autOf v)
          = autOf sc * autOf (gmulE u v) := by rw [autOf_gmulE huValid hvValid]
          _ = autOf sc * autOf (gmulE sc (conjE y sc)) := by rw [huv]
          _ = autOf sc * (autOf sc * autOf (conjE y sc)) := by
              rw [autOf_gmulE hvsc (validB_conjE hy hvsc)]
          _ = (autOf sc * autOf sc) * autOf (conjE y sc) := by group
          _ = autOf (conjE y sc) := by
              rw [w183finSp44G2Y_autOf_self_of_klein hp hsc, one_mul]
          _ = autOf y * autOf sc * (autOf y)⁻¹ := autOf_conjE hy hvsc
      exact hcalc.symm
  · have hmem : sc ∈ [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!] := by
      rw [h]; simp
    obtain ⟨u, hu, v, hv, huv⟩ := w183finSp44G2Y_mem_Z (h4 sc hmem)
    refine ⟨autOf u * autOf v, ?_, ?_⟩
    · apply Subgroup.mul_mem
      · exact Subgroup.subset_closure (Set.mem_union_left _ ((w183finSp44G2Y_autOf_mem_map_conjE
          hp hg1 (w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hu)).mpr hu))
      · exact Subgroup.subset_closure (Set.mem_union_right _ ((w183finSp44G2Y_autOf_mem_map_conjE
          hp hg2 (w183finSp44G2Y_valid_of_mem_map_conj hp hg2 hv)).mpr hv))
    · rw [← hscs]
      have huValid := w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hu
      have hvValid := w183finSp44G2Y_valid_of_mem_map_conj hp hg2 hv
      have hcalc : autOf sc * (autOf u * autOf v) = autOf y * autOf sc * (autOf y)⁻¹ := by
        calc autOf sc * (autOf u * autOf v)
          = autOf sc * autOf (gmulE u v) := by rw [autOf_gmulE huValid hvValid]
          _ = autOf sc * autOf (gmulE sc (conjE y sc)) := by rw [huv]
          _ = autOf sc * (autOf sc * autOf (conjE y sc)) := by
              rw [autOf_gmulE hvsc (validB_conjE hy hvsc)]
          _ = (autOf sc * autOf sc) * autOf (conjE y sc) := by group
          _ = autOf (conjE y sc) := by
              rw [w183finSp44G2Y_autOf_self_of_klein hp hsc, one_mul]
          _ = autOf y * autOf sc * (autOf y)⁻¹ := autOf_conjE hy hvsc
      exact hcalc.symm
  · have hmem : sc ∈ [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!] := by
      rw [h]; simp
    obtain ⟨u, hu, v, hv, huv⟩ := w183finSp44G2Y_mem_Z (h4 sc hmem)
    refine ⟨autOf u * autOf v, ?_, ?_⟩
    · apply Subgroup.mul_mem
      · exact Subgroup.subset_closure (Set.mem_union_left _ ((w183finSp44G2Y_autOf_mem_map_conjE
          hp hg1 (w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hu)).mpr hu))
      · exact Subgroup.subset_closure (Set.mem_union_right _ ((w183finSp44G2Y_autOf_mem_map_conjE
          hp hg2 (w183finSp44G2Y_valid_of_mem_map_conj hp hg2 hv)).mpr hv))
    · rw [← hscs]
      have huValid := w183finSp44G2Y_valid_of_mem_map_conj hp hg1 hu
      have hvValid := w183finSp44G2Y_valid_of_mem_map_conj hp hg2 hv
      have hcalc : autOf sc * (autOf u * autOf v) = autOf y * autOf sc * (autOf y)⁻¹ := by
        calc autOf sc * (autOf u * autOf v)
          = autOf sc * autOf (gmulE u v) := by rw [autOf_gmulE huValid hvValid]
          _ = autOf sc * autOf (gmulE sc (conjE y sc)) := by rw [huv]
          _ = autOf sc * (autOf sc * autOf (conjE y sc)) := by
              rw [autOf_gmulE hvsc (validB_conjE hy hvsc)]
          _ = (autOf sc * autOf sc) * autOf (conjE y sc) := by group
          _ = autOf (conjE y sc) := by
              rw [w183finSp44G2Y_autOf_self_of_klein hp hsc, one_mul]
          _ = autOf y * autOf sc * (autOf y)⁻¹ := autOf_conjE hy hvsc
      exact hcalc.symm

theorem w183finSp44G2Y_not_isTISub_of_check_aux {p : Nat × Nat} (hp : p ∈ pairsL) {e : Nat}
    (he : 0 < e) (he' : (e - 1) / 3 < g2Pool.length)
    (hc : checkTIfail invsA[p.1]! invsA[p.2]! e = true) :
    ¬ IsTISub (MulAut S4) (kleinSub invsA[p.1]! invsA[p.2]!) := by
  intro hTI
  have hva := w183finSp44G2Y_valid_a hp
  have hvb := w183finSp44G2Y_valid_b hp
  rw [checkTIfail] at hc
  set q : Nat := g2Pool.getD ((e - 1) / 3) 0 with hq
  set g : El := (q / 4, q % 4) with hg
  set t : El := [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!].getD
    ((e - 1) % 3) oneE with ht
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true] at hc
  obtain ⟨hgt, hnotmem⟩ := hc
  have hj : (e - 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hgvalid : validB g = true := by
    rw [hg]
    have hqindex : q = g2Pool[(e - 1) / 3] := by
      rw [hq, List.getD_eq_getElem _ _ he']
    rw [hqindex]
    exact (List.all_eq_true.mp w183finSp44G2Y_pool_valid) _ (List.getElem_mem he')
  have htmem : t ∈ klein invsA[p.1]! invsA[p.2]! := by
    rw [ht, List.getD_eq_getElem _ _ hj]
    have hmem : [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!][(e - 1) % 3] ∈
        [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!] := List.getElem_mem _
    rcases List.mem_cons.mp hmem with h | h
    · rw [h]; exact w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inl rfl))
    · rcases List.mem_cons.mp h with h | h
      · rw [h]; exact w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))
      · rcases List.mem_cons.mp h with h | h
        · rw [h]; exact w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inr rfl)))
        · simp at h
  have htvalid : validB t = true := w183finSp44G2Y_valid_klein hva hvb htmem
  have htne : t ≠ oneE := by
    rw [ht]
    exact w183finSp44G2Y_getD_ne_one hp hj
  have htA : autOf t ∈ kleinSub invsA[p.1]! invsA[p.2]! :=
    (mem_kleinSub_iff hp (autOf t)).mpr ⟨t, htmem, rfl⟩
  have htne' : autOf t ≠ 1 := fun h =>
    htne (autOf_inj htvalid validB_oneE (by rw [h, autOf_oneE]))
  have hcomm : autOf g * autOf t = autOf t * autOf g := by
    rw [← autOf_gmulE hgvalid htvalid, ← autOf_gmulE htvalid hgvalid, hgt]
  have hnot : autOf g ∉ Subgroup.normalizer (kleinSub invsA[p.1]! invsA[p.2]! :
      Set (MulAut S4)) := by
    intro hmem
    have key : ∀ x : El, x ∈ klein invsA[p.1]! invsA[p.2]! →
        memK (klein invsA[p.1]! invsA[p.2]!) (conjE g x) = true := by
      intro x hx
      have hvx := w183finSp44G2Y_valid_klein hva hvb hx
      have hmem' : autOf (conjE g x) ∈ kleinSub invsA[p.1]! invsA[p.2]! := by
        have h2 : autOf g * autOf x * (autOf g)⁻¹ ∈ kleinSub invsA[p.1]! invsA[p.2]! :=
          (Subgroup.mem_normalizer_iff.mp hmem) (autOf x) |>.mp
            ((w183finSp44G2Y_autOf_mem_kleinSub hp hvx).mpr hx)
        rwa [← autOf_conjE hgvalid hvx] at h2
      exact w183finSp44G2Y_memK_eq_true.mpr
        ((w183finSp44G2Y_autOf_mem_kleinSub hp (validB_conjE hgvalid hvx)).mp hmem')
    rcases hnotmem with h | h
    · have hmf : memK (klein invsA[p.1]! invsA[p.2]!) (conjE g invsA[p.1]!) = false := by
        simpa using h
      have hcontra := key invsA[p.1]!
        (w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inl rfl)))
      rw [hmf] at hcontra
      exact Bool.false_ne_true hcontra
    · have hmf : memK (klein invsA[p.1]! invsA[p.2]!) (conjE g invsA[p.2]!) = false := by
        simpa using h
      have hcontra := key invsA[p.2]!
        (w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))
      rw [hmf] at hcontra
      exact Bool.false_ne_true hcontra
  exact hnot (hTI (autOf t) htA htne' (autOf g) hcomm)

theorem w183finSp44G2Y_corConfig_of_check_aux {p : Nat × Nat} (hp : p ∈ pairsL)
    {c : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat}
    (hc : checkCor invsA[p.1]! invsA[p.2]! c = true)
    (hgA0 : validB (c.2.1, c.2.2.1) = true)
    (hg10 : validB (c.2.2.2.1, c.2.2.2.2.1) = true)
    (hg20 : validB (c.2.2.2.2.2.1, c.2.2.2.2.2.2.1) = true)
    (hy0 : validB (c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2) = true) :
    CorConfig (MulAut S4) (kleinSub invsA[p.1]! invsA[p.2]!) := by
  have hva := w183finSp44G2Y_valid_a hp
  have hvb := w183finSp44G2Y_valid_b hp
  rw [checkCor] at hc
  set gA : El := (c.2.1, c.2.2.1) with hgAeq
  set g1 : El := (c.2.2.2.1, c.2.2.2.2.1) with hg1eq
  set g2 : El := (c.2.2.2.2.2.1, c.2.2.2.2.2.2.1) with hg2eq
  set y : El := (c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2) with hyeq
  have hgA : validB gA = true := by rw [hgAeq]; exact hgA0
  have hg1 : validB g1 = true := by rw [hg1eq]; exact hg10
  have hg2 : validB g2 = true := by rw [hg2eq]; exact hg20
  have hy : validB y = true := by rw [hyeq]; exact hy0
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  let A'c : List El := (klein invsA[p.1]! invsA[p.2]!).map (conjE gA)
  let X1c : List El := (klein invsA[p.1]! invsA[p.2]!).map (conjE g1)
  let X2c : List El := (klein invsA[p.1]! invsA[p.2]!).map (conjE g2)
  let Asub : Subgroup (MulAut S4) :=
    (kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf gA)).toMonoidHom
  let X1sub : Subgroup (MulAut S4) :=
    (kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf g1)).toMonoidHom
  let X2sub : Subgroup (MulAut S4) :=
    (kleinSub invsA[p.1]! invsA[p.2]!).map (MulAut.conj (autOf g2)).toMonoidHom
  have hS : (⋃ X ∈ ({X1sub, X2sub} : Set (Subgroup (MulAut S4))),
      (X : Set (MulAut S4))) = (X1sub : Set (MulAut S4)) ∪ (X2sub : Set (MulAut S4)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union,
      SetLike.mem_coe]
    constructor
    · rintro ⟨X, rfl | rfl, hx⟩
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨X1sub, Or.inl rfl, hx⟩
      · exact ⟨X2sub, Or.inr rfl, hx⟩
  refine ⟨Asub, ({X1sub, X2sub} : Set (Subgroup (MulAut S4))), autOf y, ⟨autOf gA, rfl⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl
    · exact ⟨autOf g1, rfl⟩
    · exact ⟨autOf g2, rfl⟩
  · intro heq
    have key : ∀ x : El, x ∈ klein invsA[p.1]! invsA[p.2]! →
        memK (klein invsA[p.1]! invsA[p.2]!) (conjE y x) = true := by
      intro x hx
      have hvx := w183finSp44G2Y_valid_klein hva hvb hx
      have hmem : autOf (conjE y x) ∈ kleinSub invsA[p.1]! invsA[p.2]! := by
        rw [← heq]
        exact Subgroup.mem_map.mpr ⟨autOf x,
          (w183finSp44G2Y_autOf_mem_kleinSub hp hvx).mpr hx, (autOf_conjE hy hvx).symm⟩
      exact w183finSp44G2Y_memK_eq_true.mpr
        ((w183finSp44G2Y_autOf_mem_kleinSub hp (validB_conjE hy hvx)).mp hmem)
    rcases h1 with h | h
    · have hmf : memK (klein invsA[p.1]! invsA[p.2]!) (conjE y invsA[p.1]!) = false := by
        simpa using h
      have hcontra := key invsA[p.1]!
        (w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inl rfl)))
      rw [hmf] at hcontra
      exact Bool.false_ne_true hcontra
    · have hmf : memK (klein invsA[p.1]! invsA[p.2]!) (conjE y invsA[p.2]!) = false := by
        simpa using h
      have hcontra := key invsA[p.2]!
        (w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))
      rw [hmf] at hcontra
      exact Bool.false_ne_true hcontra
  · intro s hs
    obtain ⟨z, hz, hzrel⟩ := w183finSp44G2Y_exists_z_rel hp hg1 hg2 hy h4 s hs
    exact ⟨z, by rwa [hS], hzrel⟩
  · intro hle
    have haN : autOf invsA[p.1]! ∈
        Subgroup.normalizer ((kleinSub invsA[p.1]! invsA[p.2]!).map
          (MulAut.conj (autOf gA)).toMonoidHom : Set (MulAut S4)) :=
      hle ((w183finSp44G2Y_autOf_mem_kleinSub hp hva).mpr
        (w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inl rfl))))
    have hbN : autOf invsA[p.2]! ∈
        Subgroup.normalizer ((kleinSub invsA[p.1]! invsA[p.2]!).map
          (MulAut.conj (autOf gA)).toMonoidHom : Set (MulAut S4)) :=
      hle ((w183finSp44G2Y_autOf_mem_kleinSub hp hvb).mpr
        (w183finSp44G2Y_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))))
    have hsa := w183finSp44G2Y_sameSet_map_conjE_of_mem_normalizer hp hgA hva
      (w183finSp44G2Y_gmulE_self_of_mem_invs (w183finSp44G2Y_mem_invsA
        (w183finSp44G2Y_lt_n127_a hp))) haN
    have hsb := w183finSp44G2Y_sameSet_map_conjE_of_mem_normalizer hp hgA hvb
      (w183finSp44G2Y_gmulE_self_of_mem_invs (w183finSp44G2Y_mem_invsA
        (w183finSp44G2Y_lt_n127_b hp))) hbN
    rcases h2 with h | h
    · have hmf : sameSet (List.map (conjE invsA[p.1]!) A'c) A'c = false := by
        simpa [A'c, X1c, X2c] using h
      rw [hmf] at hsa
      exact Bool.false_ne_true hsa
    · have hmf : sameSet (List.map (conjE invsA[p.2]!) A'c) A'c = false := by
        simpa [A'c, X1c, X2c] using h
      rw [hmf] at hsb
      exact Bool.false_ne_true hsb
  · intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl
    · rcases h5 X1c List.mem_cons_self with h | h
      · exact Or.inl (w183finSp44G2Y_map_conj_eq_of_sameSet hp hg1 hgA h)
      · exact Or.inr (w183finSp44G2Y_commute_sub_of_commute_code hp hg1 hgA h)
    · rcases h5 X2c (List.mem_cons_of_mem _ List.mem_cons_self) with h | h
      · exact Or.inl (w183finSp44G2Y_map_conj_eq_of_sameSet hp hg2 hgA h)
      · exact Or.inr (w183finSp44G2Y_commute_sub_of_commute_code hp hg2 hgA h)

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
