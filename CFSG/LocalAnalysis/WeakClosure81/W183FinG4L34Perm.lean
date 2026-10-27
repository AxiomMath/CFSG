module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Fix
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Blk

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.Quasithin CFSG.Open
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

private theorem w183finL34perm_e8Idx_length : e8Idx.length = 6 := by decide +kernel

private theorem w183finL34perm_e16Idx_length : e16Idx.length = 2 := by decide +kernel

private theorem w183finL34perm_coverW_length : coverW.length = 9 := by decide +kernel

private theorem w183finL34perm_invN_length : invN.length = 27 := by
  unfold invN
  rw [List.length_map, invI_length]

private theorem w183finL34perm_e8N_length : e8N.length = 6 := by
  unfold e8N
  rw [List.length_map, w183finL34perm_e8Idx_length]

private theorem w183finL34perm_e16N_length : e16N.length = 2 := by
  unfold e16N
  rw [List.length_map, w183finL34perm_e16Idx_length]

private theorem w183finL34perm_coverN_length : coverN.length = 9 := by
  unfold coverN
  rw [List.length_map, w183finL34perm_coverW_length]

private theorem w183finL34perm_e8Idx_lt_all :
    e8Idx.all (fun I => I.all (fun i => decide (i < 64))) = true := by decide +kernel

private theorem w183finL34perm_e16Idx_lt_all :
    e16Idx.all (fun I => I.all (fun i => decide (i < 64))) = true := by decide +kernel

private theorem w183finL34perm_e8Idx_len_all : e8Idx.all (fun I => decide (I.length = 8)) = true :=
  by decide +kernel

private theorem w183finL34perm_e8Idx_zero_all : e8Idx.all (fun I => I.contains 0) = true := by
  decide +kernel

private theorem w183finL34perm_e8Idx_lt {m i : ℕ} (hm : m < 6)
    (hi : i ∈ e8Idx.getD m []) : i < 64 := by
  have hlen : m < e8Idx.length := by rw [w183finL34perm_e8Idx_length]; exact hm
  have hmem : e8Idx.getD m [] ∈ e8Idx := by
    rw [List.getD_eq_getElem (l := e8Idx) (d := ([] : List ℕ)) (n := m) hlen]
    exact List.getElem_mem hlen
  have h := List.all_eq_true.1 w183finL34perm_e8Idx_lt_all (e8Idx.getD m []) hmem
  exact of_decide_eq_true (List.all_eq_true.1 h i hi)

private theorem w183finL34perm_e16Idx_lt {m i : ℕ} (hm : m < 2)
    (hi : i ∈ e16Idx.getD m []) : i < 64 := by
  have hlen : m < e16Idx.length := by rw [w183finL34perm_e16Idx_length]; exact hm
  have hmem : e16Idx.getD m [] ∈ e16Idx := by
    rw [List.getD_eq_getElem (l := e16Idx) (d := ([] : List ℕ)) (n := m) hlen]
    exact List.getElem_mem hlen
  have h := List.all_eq_true.1 w183finL34perm_e16Idx_lt_all (e16Idx.getD m []) hmem
  exact of_decide_eq_true (List.all_eq_true.1 h i hi)

private theorem w183finL34perm_e8Idx_getD_length {m : ℕ} (hm : m < 6) :
    (e8Idx.getD m []).length = 8 := by
  have hlen : m < e8Idx.length := by rw [w183finL34perm_e8Idx_length]; exact hm
  have hmem : e8Idx.getD m [] ∈ e8Idx := by
    rw [List.getD_eq_getElem (l := e8Idx) (d := ([] : List ℕ)) (n := m) hlen]
    exact List.getElem_mem hlen
  exact of_decide_eq_true (List.all_eq_true.1 w183finL34perm_e8Idx_len_all _ hmem)

private theorem w183finL34perm_repN_eq {p : ℕ} {g h : Equiv.Perm (Fin 42)} (hg : RepN p g)
    (hh : RepN p h) : g = h := by
  ext i
  have : (g i : ℕ) = (h i : ℕ) := by rw [← hg i, hh i]
  exact this

private theorem w183finL34perm_c1N_getD {k : ℕ} (hk : k < 64) :
    c1N.getD k 0 = wN (c1W.getD k []) := by
  have hkN : k < (c1W.map wN).length := by rw [List.length_map, c1W_length]; exact hk
  rw [c1N, List.getD_eq_getElem (l := c1W.map wN) (d := 0) (n := k) hkN, List.getElem_map,
    List.getD_eq_getElem (l := c1W) (d := ([] : List ℕ)) (n := k)
      (by rw [c1W_length]; exact hk)]

private theorem w183finL34perm_c1W_getD_mem {i : ℕ} (hi : i < 64) : c1W.getD i [] ∈ c1W := by
  rw [List.getD_eq_getElem (l := c1W) (d := ([] : List ℕ)) (n := i)
    (by rw [c1W_length]; exact hi)]
  exact List.getElem_mem (by rw [c1W_length]; exact hi)

private theorem w183finL34perm_e8N_getD {m : ℕ} (hm : m < 6) :
    e8N.getD m [] = (e8Idx.getD m []).map (fun i => c1N.getD i 0) := by
  have hlen : m < (e8Idx.map pickN).length := by
    rw [List.length_map, w183finL34perm_e8Idx_length]; exact hm
  change (e8Idx.map pickN).getD m [] = (e8Idx.getD m []).map (fun i => c1N.getD i 0)
  rw [List.getD_eq_getElem (l := e8Idx.map pickN) (d := ([] : List ℕ)) (n := m) hlen,
    List.getElem_map]
  rw [← List.getD_eq_getElem (l := e8Idx) (d := ([] : List ℕ)) (n := m)
    (by rw [w183finL34perm_e8Idx_length]; exact hm)]
  rfl

private theorem w183finL34perm_e16N_getD {m : ℕ} (hm : m < 2) :
    e16N.getD m [] = (e16Idx.getD m []).map (fun i => c1N.getD i 0) := by
  have hlen : m < (e16Idx.map pickN).length := by
    rw [List.length_map, w183finL34perm_e16Idx_length]; exact hm
  change (e16Idx.map pickN).getD m [] = (e16Idx.getD m []).map (fun i => c1N.getD i 0)
  rw [List.getD_eq_getElem (l := e16Idx.map pickN) (d := ([] : List ℕ)) (n := m) hlen,
    List.getElem_map]
  rw [← List.getD_eq_getElem (l := e16Idx) (d := ([] : List ℕ)) (n := m)
    (by rw [w183finL34perm_e16Idx_length]; exact hm)]
  rfl

private theorem w183finL34perm_e8N_mem {m : ℕ} (hm : m < 6) : e8N.getD m [] ∈ e8N := by
  have hlen : m < e8N.length := by rw [w183finL34perm_e8N_length]; exact hm
  rw [List.getD_eq_getElem (l := e8N) (d := ([] : List ℕ)) (n := m) hlen]
  exact List.getElem_mem hlen

private theorem w183finL34perm_e16N_mem {m : ℕ} (hm : m < 2) : e16N.getD m [] ∈ e16N := by
  have hlen : m < e16N.length := by rw [w183finL34perm_e16N_length]; exact hm
  rw [List.getD_eq_getElem (l := e16N) (d := ([] : List ℕ)) (n := m) hlen]
  exact List.getElem_mem hlen

private theorem w183finL34perm_invI_getD_lt {i : ℕ} (hi : i < 27) : invI.getD i 0 < 64 := by
  have hlen : i < invI.length := by rw [invI_length]; exact hi
  rw [List.getD_eq_getElem (l := invI) (d := 0) (n := i) hlen]
  exact List.mem_range.1 (List.mem_filter.1 (List.getElem_mem hlen)).1

private theorem w183finL34perm_repN_invN {i : ℕ} (hi : i < 27) :
    RepN (invN.getD i 0) (invP i) := by
  have hlenI : i < invI.length := by rw [invI_length]; exact hi
  have h1 : invN.getD i 0 = wN (c1W.getD (invI.getD i 0) []) := by
    rw [invN, List.getD_eq_getElem (l := invI.map (fun k => c1N.getD k 0)) (d := 0) (n := i)
        (by rw [List.length_map]; exact hlenI), List.getElem_map,
      ← List.getD_eq_getElem (l := invI) (d := 0) (n := i) hlenI,
      w183finL34perm_c1N_getD (w183finL34perm_invI_getD_lt hi)]
  rw [h1]
  exact repN_wN _

private theorem w183finL34perm_coverN_getD {t : ℕ} (ht : t < 9) :
    coverN.getD t 0 = wN (coverW.getD t []) := by
  have hlen : t < (coverW.map wN).length := by
    rw [List.length_map, w183finL34perm_coverW_length]; exact ht
  change (coverW.map wN).getD t 0 = wN (coverW.getD t [])
  rw [List.getD_eq_getElem (l := coverW.map wN) (d := 0) (n := t) hlen, List.getElem_map]
  rw [← List.getD_eq_getElem (l := coverW) (d := ([] : List ℕ)) (n := t)
    (by rw [w183finL34perm_coverW_length]; exact ht)]

private theorem w183finL34perm_nCos_getD {t : ℕ} (ht : t < 9) :
    nCos.getD t [] = e8N.map (fun N => N.map fun n => compN n (coverN.getD t 0)) := by
  have hlen : t < (coverN.map (fun g => e8N.map fun N => N.map fun n => compN n g)).length := by
    rw [List.length_map, w183finL34perm_coverN_length]; exact ht
  change (coverN.map (fun g => e8N.map fun N => N.map fun n => compN n g)).getD t [] =
    e8N.map (fun N => N.map fun n => compN n (coverN.getD t 0))
  rw [List.getD_eq_getElem
      (l := coverN.map (fun g => e8N.map fun N => N.map fun n => compN n g))
      (d := ([] : List (List ℕ))) (n := t) hlen, List.getElem_map]
  rw [← List.getD_eq_getElem (l := coverN) (d := 0) (n := t)
    (by rw [w183finL34perm_coverN_length]; exact ht)]

private theorem w183finL34perm_nCos_getD_getD {t m : ℕ} (ht : t < 9) (hm : m < 6) :
    (nCos.getD t []).getD m [] =
      (e8N.getD m []).map (fun n => compN n (coverN.getD t 0)) := by
  rw [w183finL34perm_nCos_getD ht]
  have hlen : m < (e8N.map fun N => N.map fun n => compN n (coverN.getD t 0)).length := by
    rw [List.length_map, w183finL34perm_e8N_length]; exact hm
  rw [List.getD_eq_getElem (l := e8N.map fun N => N.map fun n => compN n (coverN.getD t 0))
    (d := ([] : List ℕ)) (n := m) hlen, List.getElem_map]
  have hlenE : m < e8N.length := by rw [w183finL34perm_e8N_length]; exact hm
  rw [← List.getD_eq_getElem (l := e8N) (d := ([] : List ℕ)) (n := m) hlenE]

private theorem w183finL34perm_imgs_getD {t : ℕ} (ht : t < 9) :
    imgs.getD t [] = invN.map (fun x => compN (coverN.getD t 0) x) := by
  have hlen : t < (coverN.map (fun g => invN.map fun x => compN g x)).length := by
    rw [List.length_map, w183finL34perm_coverN_length]; exact ht
  change (coverN.map (fun g => invN.map fun x => compN g x)).getD t [] =
    invN.map (fun x => compN (coverN.getD t 0) x)
  rw [List.getD_eq_getElem (l := coverN.map (fun g => invN.map fun x => compN g x))
    (d := ([] : List ℕ)) (n := t) hlen, List.getElem_map]
  rw [← List.getD_eq_getElem (l := coverN) (d := 0) (n := t)
    (by rw [w183finL34perm_coverN_length]; exact ht)]

private theorem w183finL34perm_imgs_getD_getD {t i : ℕ} (ht : t < 9) (hi : i < 27) :
    (imgs.getD t []).getD i 0 = compN (coverN.getD t 0) (invN.getD i 0) := by
  rw [w183finL34perm_imgs_getD ht]
  have hlen : i < (invN.map (fun x => compN (coverN.getD t 0) x)).length := by
    rw [List.length_map, w183finL34perm_invN_length]; exact hi
  rw [List.getD_eq_getElem (l := invN.map (fun x => compN (coverN.getD t 0) x))
    (d := 0) (n := i) hlen, List.getElem_map]
  have hlenI : i < invN.length := by rw [w183finL34perm_invN_length]; exact hi
  rw [← List.getD_eq_getElem (l := invN) (d := 0) (n := i) hlenI]

private theorem w183finL34perm_e8Set_of_mem_e8N {m : ℕ} (hm : m < 6) {p : ℕ}
    (hp : p ∈ e8N.getD m []) {x : Equiv.Perm (Fin 42)} (hrep : RepN p x) : x ∈ e8Set m := by
  rw [w183finL34perm_e8N_getD hm] at hp
  obtain ⟨i, hi, hip⟩ := List.mem_map.1 hp
  have hi64 := w183finL34perm_e8Idx_lt hm hi
  refine ⟨i, hi, ?_⟩
  rw [← hip, w183finL34perm_c1N_getD hi64] at hrep
  exact w183finL34perm_repN_eq (repN_wN _) hrep

private theorem w183finL34perm_e8Set_exists_repN_of_mem_e8N {m : ℕ} (hm : m < 6) {p : ℕ}
    (hp : p ∈ e8N.getD m []) : ∃ x ∈ e8Set m, RepN p x := by
  rw [w183finL34perm_e8N_getD hm] at hp
  obtain ⟨i, hi, hip⟩ := List.mem_map.1 hp
  have hi64 := w183finL34perm_e8Idx_lt hm hi
  refine ⟨wordPerm (c1W.getD i []), ⟨i, hi, rfl⟩, ?_⟩
  rw [← hip, w183finL34perm_c1N_getD hi64]
  exact repN_wN _

private theorem w183finL34perm_e16Set_exists_repN_of_mem_e16N {m : ℕ} (hm : m < 2) {p : ℕ}
    (hp : p ∈ e16N.getD m []) : ∃ x ∈ e16Set m, RepN p x := by
  rw [w183finL34perm_e16N_getD hm] at hp
  obtain ⟨i, hi, hip⟩ := List.mem_map.1 hp
  have hi64 := w183finL34perm_e16Idx_lt hm hi
  refine ⟨wordPerm (c1W.getD i []), ⟨i, hi, rfl⟩, ?_⟩
  rw [← hip, w183finL34perm_c1N_getD hi64]
  exact repN_wN _

private theorem w183finL34perm_exists_repN_of_mem_e8Set {m : ℕ} (hm : m < 6)
    {x : Equiv.Perm (Fin 42)} (hx : x ∈ e8Set m) :
    ∃ p ∈ e8N.getD m [], RepN p x := by
  obtain ⟨i, hi, rfl⟩ := hx
  have hi64 := w183finL34perm_e8Idx_lt hm hi
  refine ⟨c1N.getD i 0, ?_, ?_⟩
  · rw [w183finL34perm_e8N_getD hm]; exact List.mem_map.2 ⟨i, hi, rfl⟩
  · rw [w183finL34perm_c1N_getD hi64]; exact repN_wN _

private theorem w183finL34perm_e8Set_mul {m : ℕ} (hm : m < 6) {x y : Equiv.Perm (Fin 42)}
    (hx : x ∈ e8Set m) (hy : y ∈ e8Set m) : x * y ∈ e8Set m := by
  obtain ⟨px, hpx, hxrep⟩ := w183finL34perm_exists_repN_of_mem_e8Set hm hx
  obtain ⟨py, hpy, hyrep⟩ := w183finL34perm_exists_repN_of_mem_e8Set hm hy
  have hclosed := List.all_eq_true.1 e8_closed (e8N.getD m []) (w183finL34perm_e8N_mem hm)
  have h1 := List.all_eq_true.1 hclosed px hpx
  have h2 := List.all_eq_true.1 h1 py hpy
  exact w183finL34perm_e8Set_of_mem_e8N hm (List.contains_iff_mem.1 h2) (hxrep.comp hyrep)

private theorem w183finL34perm_e8Set_one {m : ℕ} (hm : m < 6) :
    (1 : Equiv.Perm (Fin 42)) ∈ e8Set m := by
  have hlen : m < e8Idx.length := by rw [w183finL34perm_e8Idx_length]; exact hm
  have hmemE : e8Idx.getD m [] ∈ e8Idx := by
    rw [List.getD_eq_getElem (l := e8Idx) (d := ([] : List ℕ)) (n := m) hlen]
    exact List.getElem_mem hlen
  have hmem : 0 ∈ e8Idx.getD m [] :=
    List.contains_iff_mem.1 (List.all_eq_true.1 w183finL34perm_e8Idx_zero_all _ hmemE)
  exact ⟨0, hmem, rfl⟩

private theorem w183finL34perm_e8Set_normal {m : ℕ} (hm : m < 6)
    {h k : Equiv.Perm (Fin 42)} (hh : h ∈ C₁) (hk : k ∈ e8Set m) : h * k * h⁻¹ ∈ e8Set m := by
  obtain ⟨w, hw, rfl⟩ := mem_c1 hh
  obtain ⟨i, hi, rfl⟩ := hk
  have hi64 := w183finL34perm_e8Idx_lt hm hi
  have huN : wN w ∈ c1N := List.mem_map.2 ⟨w, hw, rfl⟩
  have hnN : c1N.getD i 0 ∈ e8N.getD m [] := by
    rw [w183finL34perm_e8N_getD hm]
    exact List.mem_map.2 ⟨i, hi, rfl⟩
  have hnorm := List.all_eq_true.1 e8_normal (e8N.getD m []) (w183finL34perm_e8N_mem hm)
  have h1 := List.all_eq_true.1 hnorm (wN w) huN
  have h2 := List.all_eq_true.1 h1 (c1N.getD i 0) hnN
  have hmem : compN (wN w) (c1N.getD i 0) ∈ (e8N.getD m []).map (fun n => compN n (wN w)) :=
    List.contains_iff_mem.1 h2
  obtain ⟨n', hn', hn'eq⟩ := List.mem_map.1 hmem
  obtain ⟨x', hx'mem, hx'rep⟩ := w183finL34perm_e8Set_exists_repN_of_mem_e8N hm hn'
  have hrep_u : RepN (wN w) (wordPerm w) := repN_wN w
  have hrep_n : RepN (c1N.getD i 0) (wordPerm (c1W.getD i [])) := by
    rw [w183finL34perm_c1N_getD hi64]; exact repN_wN _
  have heq : x' * wordPerm w = wordPerm w * wordPerm (c1W.getD i []) := by
    have h1 : RepN (compN n' (wN w)) (x' * wordPerm w) := hx'rep.comp hrep_u
    rw [hn'eq] at h1
    exact w183finL34perm_repN_eq h1 (hrep_u.comp hrep_n)
  have hfin : wordPerm w * wordPerm (c1W.getD i []) * (wordPerm w)⁻¹ = x' := by
    rw [← heq]; group
  rw [hfin]
  exact hx'mem

private theorem w183finL34perm_e16Set_normal {m : ℕ} (hm : m < 2)
    {h k : Equiv.Perm (Fin 42)} (hh : h ∈ C₁) (hk : k ∈ e16Set m) : h * k * h⁻¹ ∈ e16Set m := by
  obtain ⟨w, hw, rfl⟩ := mem_c1 hh
  obtain ⟨i, hi, rfl⟩ := hk
  have hi64 := w183finL34perm_e16Idx_lt hm hi
  have huN : wN w ∈ c1N := List.mem_map.2 ⟨w, hw, rfl⟩
  have hnN : c1N.getD i 0 ∈ e16N.getD m [] := by
    rw [w183finL34perm_e16N_getD hm]
    exact List.mem_map.2 ⟨i, hi, rfl⟩
  have hnorm := List.all_eq_true.1 e16_normal (e16N.getD m []) (w183finL34perm_e16N_mem hm)
  have h1 := List.all_eq_true.1 hnorm (wN w) huN
  have h2 := List.all_eq_true.1 h1 (c1N.getD i 0) hnN
  have hmem : compN (wN w) (c1N.getD i 0) ∈ (e16N.getD m []).map (fun n => compN n (wN w)) :=
    List.contains_iff_mem.1 h2
  obtain ⟨n', hn', hn'eq⟩ := List.mem_map.1 hmem
  obtain ⟨x', hx'mem, hx'rep⟩ := w183finL34perm_e16Set_exists_repN_of_mem_e16N hm hn'
  have hrep_u : RepN (wN w) (wordPerm w) := repN_wN w
  have hrep_n : RepN (c1N.getD i 0) (wordPerm (c1W.getD i [])) := by
    rw [w183finL34perm_c1N_getD hi64]; exact repN_wN _
  have heq : x' * wordPerm w = wordPerm w * wordPerm (c1W.getD i []) := by
    have h1 : RepN (compN n' (wN w)) (x' * wordPerm w) := hx'rep.comp hrep_u
    rw [hn'eq] at h1
    exact w183finL34perm_repN_eq h1 (hrep_u.comp hrep_n)
  have hfin : wordPerm w * wordPerm (c1W.getD i []) * (wordPerm w)⁻¹ = x' := by
    rw [← heq]; group
  rw [hfin]
  exact hx'mem

private theorem w183finL34perm_e8Set_subset_C1 {m : ℕ} (hm : m < 6) : e8Set m ⊆ C₁ := by
  rintro x ⟨i, hi, rfl⟩
  exact wordPerm_mem_c1 (w183finL34perm_c1W_getD_mem (w183finL34perm_e8Idx_lt hm hi))

private theorem w183finL34perm_e8Set_eq_image (m : ℕ) :
    e8Set m = wordPerm '' {w : List ℕ | w ∈ (e8Idx.getD m []).map (fun i => c1W.getD i [])} := by
  ext x
  constructor
  · rintro ⟨i, hi, hix⟩
    exact ⟨c1W.getD i [], List.mem_map.mpr ⟨i, hi, rfl⟩, hix⟩
  · rintro ⟨w, hw, hwx⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact ⟨i, hi, hwx⟩

private theorem w183finL34perm_ncard_e8Set_le {m : ℕ} (hm : m < 6) : (e8Set m).ncard ≤ 8 := by
  rw [w183finL34perm_e8Set_eq_image]
  have hs : {w : List ℕ | w ∈ (e8Idx.getD m []).map (fun i => c1W.getD i [])} =
      (((e8Idx.getD m []).map (fun i => c1W.getD i [])).toFinset : Set (List ℕ)) := by
    ext w; simp
  calc (wordPerm '' {w : List ℕ | w ∈ (e8Idx.getD m []).map (fun i => c1W.getD i [])}).ncard
      = (wordPerm '' (((e8Idx.getD m []).map (fun i => c1W.getD i [])).toFinset :
          Set (List ℕ))).ncard := by rw [hs]
    _ ≤ (((e8Idx.getD m []).map (fun i => c1W.getD i [])).toFinset : Set (List ℕ)).ncard :=
        Set.ncard_image_le
          (hs := ((e8Idx.getD m []).map (fun i => c1W.getD i [])).toFinset.finite_toSet)
    _ = (((e8Idx.getD m []).map (fun i => c1W.getD i [])).toFinset).card := Set.ncard_coe_finset _
    _ ≤ ((e8Idx.getD m []).map (fun i => c1W.getD i [])).length := List.toFinset_card_le _
    _ = 8 := by rw [List.length_map, w183finL34perm_e8Idx_getD_length hm]

private theorem w183finL34perm_conj_invP_mem_e8Set {t m i : ℕ} (ht : t < 9) (hm : m < 6)
    (hi : i < 27)
    (h : compN (coverN.getD t 0) (invN.getD i 0) ∈ (nCos.getD t []).getD m []) :
    wordPerm (coverW.getD t []) * invP i * (wordPerm (coverW.getD t []))⁻¹ ∈ e8Set m := by
  rw [w183finL34perm_nCos_getD_getD ht hm] at h
  obtain ⟨n', hn', hn'eq⟩ := List.mem_map.1 h
  obtain ⟨x', hx'mem, hx'rep⟩ := w183finL34perm_e8Set_exists_repN_of_mem_e8N hm hn'
  have hg : RepN (coverN.getD t 0) (wordPerm (coverW.getD t [])) := by
    rw [w183finL34perm_coverN_getD ht]; exact repN_wN _
  have hx : RepN (invN.getD i 0) (invP i) := w183finL34perm_repN_invN hi
  have heq : x' * wordPerm (coverW.getD t []) = wordPerm (coverW.getD t []) * invP i := by
    have h1 : RepN (compN n' (coverN.getD t 0)) (x' * wordPerm (coverW.getD t [])) :=
      hx'rep.comp hg
    rw [hn'eq] at h1
    exact w183finL34perm_repN_eq h1 (hg.comp hx)
  have hfin : wordPerm (coverW.getD t []) * invP i * (wordPerm (coverW.getD t []))⁻¹ = x' := by
    rw [← heq]; group
  rw [hfin]
  exact hx'mem

private theorem w183finL34perm_tripleOK_exists {i j k : ℕ} (hi : i < 27) (hj : j < 27)
    (hk : k < 27) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hcij : cm i j = true)
    (hcik : cm i k = true) (hcjk : cm j k = true) :
    ∃ t < 9, ∃ m < 6,
      compN (coverN.getD t 0) (invN.getD i 0) ∈ (nCos.getD t []).getD m [] ∧
      compN (coverN.getD t 0) (invN.getD j 0) ∈ (nCos.getD t []).getD m [] ∧
      compN (coverN.getD t 0) (invN.getD k 0) ∈ (nCos.getD t []).getD m [] := by
  have h1 : ((List.range 27).all fun j =>
      !(i != j && cm i j) ||
        (List.range 27).all fun k => !(k != i && k != j && cm i k && cm j k) ||
          tripleOK i j k) = true :=
    List.all_eq_true.1 core_normalConj i (List.mem_range.2 hi)
  have h2 : (!(i != j && cm i j) ||
      (List.range 27).all fun k => !(k != i && k != j && cm i k && cm j k) ||
        tripleOK i j k) = true := List.all_eq_true.1 h1 j (List.mem_range.2 hj)
  have e1 : (i != j && cm i j) = true := by
    rw [Bool.and_eq_true]; exact ⟨(bne_iff_ne).mpr hij, hcij⟩
  have h3 : ((List.range 27).all fun k =>
      !(k != i && k != j && cm i k && cm j k) || tripleOK i j k) = true := by
    rw [e1] at h2
    simpa using h2
  have h4 : (!(k != i && k != j && cm i k && cm j k) || tripleOK i j k) = true :=
    List.all_eq_true.1 h3 k (List.mem_range.2 hk)
  have e2 : (k != i && k != j && cm i k && cm j k) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨⟨(bne_iff_ne).mpr hki, (bne_iff_ne).mpr hkj⟩, hcik⟩, hcjk⟩
  have h5 : tripleOK i j k = true := by
    rw [e2] at h4
    simpa using h4
  unfold tripleOK at h5
  obtain ⟨t, ht, ht'⟩ := List.any_eq_true.1 h5
  obtain ⟨m, hm, hm'⟩ := List.any_eq_true.1 ht'
  simp only [Bool.and_eq_true] at hm'
  obtain ⟨⟨h1', h2'⟩, h3'⟩ := hm'
  refine ⟨t, List.mem_range.1 ht, m, List.mem_range.1 hm, ?_, ?_, ?_⟩
  · rw [w183finL34perm_imgs_getD_getD (List.mem_range.1 ht) hi] at h1'
    exact List.contains_iff_mem.1 h1'
  · rw [w183finL34perm_imgs_getD_getD (List.mem_range.1 ht) hj] at h2'
    exact List.contains_iff_mem.1 h2'
  · rw [w183finL34perm_imgs_getD_getD (List.mem_range.1 ht) hk] at h3'
    exact List.contains_iff_mem.1 h3'

@[expose] def NormalConjPerm : Prop :=
  ∀ P₀ : Subgroup (Equiv.Perm (Fin 42)), IsSylowIn 2 P₀ S →
    ∀ A : Subgroup (Equiv.Perm (Fin 42)), A ≤ S → IsElemAbelian 2 A → 8 ≤ Nat.card A →
      ∃ g ∈ S, A.map (MulAut.conj g).toMonoidHom ≤ P₀ ∧
        P₀ ≤ Subgroup.normalizer
          ((A.map (MulAut.conj g).toMonoidHom : Subgroup (Equiv.Perm (Fin 42))) :
            Set (Equiv.Perm (Fin 42)))

@[expose] def DynkinMovesPerm : Prop :=
  ∀ P₀ : Subgroup (Equiv.Perm (Fin 42)), IsSylowIn 2 P₀ S →
    ∀ A : Subgroup (Equiv.Perm (Fin 42)), A ≤ P₀ → IsElemAbelian 2 A → 8 ≤ Nat.card A →
      P₀ ≤ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42))) →
        ∀ τ ∈ R, τ ∈ Subgroup.normalizer (P₀ : Set (Equiv.Perm (Fin 42))) →
          ActsOnDynkinMod ⊥ S τ → τ ∉ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42)))

theorem normalConj_C1 {A : Subgroup (Equiv.Perm (Fin 42))}
    (hAC : A ≤ C₁) (hel : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A) :
    ∃ g ∈ S, A.map (MulAut.conj g).toMonoidHom ≤ C₁ ∧
      C₁ ≤ Subgroup.normalizer
        ((A.map (MulAut.conj g).toMonoidHom : Subgroup (Equiv.Perm (Fin 42))) :
          Set (Equiv.Perm (Fin 42))) := by
  rcases card_eight_or_sixteen hAC hel h8 with h8c | h16c
  · obtain ⟨i, hi, j, hj, k, hk, hij, hki, hkj, hcij, hcik, hcjk, _hprod, hAeq⟩ :=
      exists_triple hAC hel h8c
    obtain ⟨t, ht, m, hm, hti, htj, htk⟩ :=
      w183finL34perm_tripleOK_exists hi hj hk hij hki hkj hcij hcik hcjk
    let g : Equiv.Perm (Fin 42) := wordPerm (coverW.getD t [])
    have hgS : g ∈ S := wordPerm_mem _
    have hxg : g * invP i * g⁻¹ ∈ e8Set m := w183finL34perm_conj_invP_mem_e8Set ht hm hi hti
    have hyg : g * invP j * g⁻¹ ∈ e8Set m := w183finL34perm_conj_invP_mem_e8Set ht hm hj htj
    have hzg : g * invP k * g⁻¹ ∈ e8Set m := w183finL34perm_conj_invP_mem_e8Set ht hm hk htk
    have hsub : (A.map (MulAut.conj g).toMonoidHom : Set (Equiv.Perm (Fin 42))) ⊆ e8Set m := by
      rintro b ⟨a, ha, rfl⟩
      have ha' : a ∈ span3 (invP i) (invP j) (invP k) := hAeq ▸ ha
      simp only [span3, Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
      rcases ha' with h | h | h | h | h | h | h | h
      · rw [h]; simpa using w183finL34perm_e8Set_one hm
      · rw [h]; exact hxg
      · rw [h]; exact hyg
      · rw [h]; exact hzg
      · rw [h]
        simpa [map_mul] using w183finL34perm_e8Set_mul (m := m) hm hxg hyg
      · rw [h]
        simpa [map_mul] using w183finL34perm_e8Set_mul (m := m) hm hxg hzg
      · rw [h]
        simpa [map_mul] using w183finL34perm_e8Set_mul (m := m) hm hyg hzg
      · rw [h]
        simpa [map_mul] using w183finL34perm_e8Set_mul (m := m) hm
          (w183finL34perm_e8Set_mul (m := m) hm hxg hyg) hzg
    have hncard : (e8Set m).ncard ≤
        (A.map (MulAut.conj g).toMonoidHom : Set (Equiv.Perm (Fin 42))).ncard := by
      have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = 8 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h8c]
      calc (e8Set m).ncard ≤ 8 := w183finL34perm_ncard_e8Set_le hm
        _ = Nat.card (A.map (MulAut.conj g).toMonoidHom) := hcard.symm
        _ = (A.map (MulAut.conj g).toMonoidHom : Set (Equiv.Perm (Fin 42))).ncard :=
            Nat.card_coe_set_eq _
    have hAeq' : (A.map (MulAut.conj g).toMonoidHom : Set (Equiv.Perm (Fin 42))) = e8Set m :=
      Set.eq_of_subset_of_ncard_le (s := (A.map (MulAut.conj g).toMonoidHom :
        Set (Equiv.Perm (Fin 42)))) (t := e8Set m) hsub hncard
    refine ⟨g, hgS, ?_, ?_⟩
    · exact hsub.trans (w183finL34perm_e8Set_subset_C1 hm)
    · rw [hAeq']
      refine (Subgroup.le_set_normalizer_iff).2 ?_
      intro h hh k' hk'
      exact w183finL34perm_e8Set_normal hm hh hk'
  · obtain ⟨m, hm2, hAeq⟩ := eq_e16_of_card hAC hel h16c
    have hmap : A.map (MulAut.conj (1 : Equiv.Perm (Fin 42))).toMonoidHom = A := by
      ext x
      simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨a, ha, hax⟩
        have hax' : a = x := by
          rwa [show (MulAut.conj (1 : Equiv.Perm (Fin 42))).toMonoidHom a = a from by
            simp [MulAut.conj_apply]] at hax
        rwa [← hax']
      · intro hx
        exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    refine ⟨1, S.one_mem, ?_, ?_⟩
    · rw [hmap]; exact hAC
    · rw [hmap, hAeq]
      refine (Subgroup.le_set_normalizer_iff).2 ?_
      intro h hh k hk
      exact w183finL34perm_e16Set_normal hm2 hh hk

theorem normalConjPerm_holds : NormalConjPerm := by
  intro P₀ hP0 A hAS hel h8
  have hA2 : IsPGroup 2 A := by
    intro x
    exact ⟨1, Subtype.ext (by simpa [pow_two] using hel.2 x x.2)⟩
  obtain ⟨k, hkS, hk⟩ := exists_conj_le_isSylowIn hAS hA2 isSylowIn_C1
  set B : Subgroup (Equiv.Perm (Fin 42)) := A.map (MulAut.conj k).toMonoidHom with hBdef
  have helB : IsElemAbelian 2 B := by
    rw [hBdef]; exact CFSG.Open.IsElemAbelian.map hel _
  have h8B : 8 ≤ Nat.card B := by
    rw [hBdef, Subgroup.card_map_of_injective (MulAut.conj k).injective]; exact h8
  obtain ⟨g, hgS, hgC, hgN⟩ := normalConj_C1 hk helB h8B
  obtain ⟨h, hhS, hh⟩ := exists_conj_isSylowIn (P := C₁) (Q := P₀) isSylowIn_C1 hP0
  have hcomp : ((MulAut.conj h).toMonoidHom.comp (MulAut.conj g).toMonoidHom).comp
      (MulAut.conj k).toMonoidHom = (MulAut.conj (h * g * k)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hmap : A.map (MulAut.conj (h * g * k)).toMonoidHom
      = (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom := by
    rw [hBdef, Subgroup.map_map, Subgroup.map_map, hcomp]
  refine ⟨h * g * k, S.mul_mem (S.mul_mem hhS hgS) hkS, ?_, ?_⟩
  · rw [hmap]
    exact (Subgroup.map_mono hgC).trans (le_of_eq hh.symm)
  · rw [hmap]
    calc P₀ = C₁.map (MulAut.conj h).toMonoidHom := hh
      _ ≤ (Subgroup.normalizer (B.map (MulAut.conj g).toMonoidHom : Set _)).map
            (MulAut.conj h).toMonoidHom := Subgroup.map_mono hgN
      _ ≤ Subgroup.normalizer
            (((B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom :
              Subgroup (Equiv.Perm (Fin 42))) : Set (Equiv.Perm (Fin 42))) :=
          Subgroup.le_normalizer_map _

theorem dynkinMovesPerm_holds :
    DynkinMovesPerm := by
  intro P₀ hP0 A hAP0 hel h8 hP0norm τ hτR hτP0 hτdyn hτA
  obtain ⟨k, hkS, hk⟩ := exists_conj_isSylowIn (P := C₁) (Q := P₀) isSylowIn_C1 hP0
  set A' : Subgroup (Equiv.Perm (Fin 42)) := conjSubgroup A k with hA'def
  have hk' : P₀ = conjSubgroup C₁ k⁻¹ := by rw [hk]; rfl
  have hA'C : A' ≤ C₁ := by
    rw [hA'def]
    calc conjSubgroup A k ≤ conjSubgroup P₀ k :=
          Subgroup.map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hAP0
      _ = C₁ := by rw [hk', conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hel' : IsElemAbelian 2 A' := by
    rw [hA'def]; exact CFSG.Open.IsElemAbelian.map hel _
  have h8' : 8 ≤ Nat.card A' := by
    rw [hA'def]
    unfold conjSubgroup
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]
    exact h8
  let τ' : Equiv.Perm (Fin 42) := k⁻¹ * τ * k
  have hkR : k ∈ R := S_le_R hkS
  have hτ'R : τ' ∈ R := by
    dsimp only [τ']
    exact R.mul_mem (R.mul_mem (R.inv_mem hkR) hτR) hkR
  have hτ'A' : τ' ∈ Subgroup.normalizer (A' : Set (Equiv.Perm (Fin 42))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      refine (mem_conjSubgroup_iff).2 ?_
      have h1 : k * x * k⁻¹ ∈ A := (mem_conjSubgroup_iff).1 hx
      have h2 : τ * (k * x * k⁻¹) * τ⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.1 hτA (k * x * k⁻¹)).1 h1
      rwa [show k * (τ' * x * τ'⁻¹) * k⁻¹ = τ * (k * x * k⁻¹) * τ⁻¹ by
        dsimp only [τ']; group]
    · intro hx
      refine (mem_conjSubgroup_iff).2 ?_
      have h1 : k * (τ' * x * τ'⁻¹) * k⁻¹ ∈ A := (mem_conjSubgroup_iff).1 hx
      have h2 : τ⁻¹ * (k * (τ' * x * τ'⁻¹) * k⁻¹) * τ ∈ A :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hτA) _).1 h1
      rwa [show k * x * k⁻¹ = τ⁻¹ * (k * (τ' * x * τ'⁻¹) * k⁻¹) * τ by
        dsimp only [τ']; group]
  have hτ'dyn : ActsOnDynkinMod ⊥ S τ' := by
    dsimp only [τ']
    exact actsOnDynkinMod_conj hkS hτdyn
  have hpres := preserves_block_of_normalizes hA'C hel' h8' hτ'R hτ'A'
  exact (not_actsOnDynkinMod_of_preserves hτ'R hpres) hτ'dyn

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
