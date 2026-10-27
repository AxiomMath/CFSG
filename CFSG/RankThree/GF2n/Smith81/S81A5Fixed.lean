module

public import CFSG.RankThree.GF2n.Smith81.S81A5Cent
public import CFSG.RankThree.GF2n.Smith81.S81A5Pure
public import CFSG.LieType.Chevalley.C2E6ExteriorCube

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

@[expose] def replSet (I : Set.powersetCard (Fin 6) 3) (a b : Fin 6) (hb : b ∈ I.val) (ha : a ∉ I.val) :
    Set.powersetCard (Fin 6) 3 :=
  ⟨insert a (I.val.erase b), by
    show (insert a (I.val.erase b)).card = 3
    rw [Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_of_mem_erase h')),
      Finset.card_erase_of_mem hb, I.prop]⟩

theorem cubeBasis_eq_wedgeBasis (I : Set.powersetCard (Fin 6) 3) :
    cubeBasis K I = CFSG.LieType.Chevalley.ExteriorCube.wedgeBasis I :=
  (CFSG.LieType.Chevalley.ExteriorCube.wedgeBasis_eq_basis (R := K) I).symm

theorem rho_apply_eq_map (g : GL (Fin 6) K) (x : Cube K) :
    rho K g x = exteriorPower.map 3 (Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) K)) x := by
  rw [rho, Representation.exteriorPower_apply, TauCeti.stdRep_apply, ← Matrix.toLin'_apply']

theorem coord_cubeBasis (I J : Set.powersetCard (Fin 6) 3) :
    coord K (cubeBasis K I) J = if I = J then 1 else 0 := by
  unfold coord
  rw [Module.Basis.repr_self, Finsupp.single_apply]

theorem replSet_eq_iff {a b : Fin 6} {I J : Set.powersetCard (Fin 6) 3}
    (hb : b ∈ I.val) (ha : a ∉ I.val) (haJ : a ∈ J.val) (hbJ : b ∉ J.val) :
    replSet I a b hb ha = J ↔ I = replSet J b a haJ hbJ := by
  constructor
  · intro h
    have h' : insert a (I.val.erase b) = J.val := congrArg Subtype.val h
    have ha' : a ∉ I.val.erase b := fun h'' => ha (Finset.mem_of_mem_erase h'')
    apply Subtype.ext
    show I.val = insert b (J.val.erase a)
    rw [← h', Finset.erase_insert_eq_erase, Finset.erase_eq_of_notMem ha', Finset.insert_erase hb]
  · intro h
    have h' : I.val = insert b (J.val.erase a) := congrArg Subtype.val h
    have hb' : b ∉ J.val.erase a := fun h'' => hbJ (Finset.mem_of_mem_erase h'')
    apply Subtype.ext
    show insert a (I.val.erase b) = J.val
    rw [h', Finset.erase_insert hb', Finset.insert_erase haJ]

theorem replSet_eq_imp {a b : Fin 6} (hne : a ≠ b) {I J : Set.powersetCard (Fin 6) 3}
    (hb : b ∈ I.val) (ha : a ∉ I.val) (h : replSet I a b hb ha = J) : a ∈ J.val ∧ b ∉ J.val := by
  subst h
  show a ∈ insert a (I.val.erase b) ∧ b ∉ insert a (I.val.erase b)
  refine ⟨Finset.mem_insert_self a _, fun h' => ?_⟩
  rcases Finset.mem_insert.mp h' with h'' | h''
  · exact hne h''.symm
  · exact Finset.notMem_erase b I.val h''

theorem replSet_mem_imp {a b : Fin 6} (hne : a ≠ b) {I J : Set.powersetCard (Fin 6) 3}
    (haJ : a ∈ J.val) (hbJ : b ∉ J.val) (h : I = replSet J b a haJ hbJ) :
    b ∈ I.val ∧ a ∉ I.val := by
  subst h
  show b ∈ insert b (J.val.erase a) ∧ a ∉ insert b (J.val.erase a)
  refine ⟨Finset.mem_insert_self b _, fun h' => ?_⟩
  rcases Finset.mem_insert.mp h' with h'' | h''
  · exact hne h''
  · exact Finset.notMem_erase a J.val h''

theorem rho_transvGL_cubeBasis {a b : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) (hne : a ≠ b)
    (c : K) (I : Set.powersetCard (Fin 6) 3) :
    rho K (transvGL K a b hne c) (cubeBasis K I) =
      if h : b ∈ I.val ∧ a ∉ I.val then cubeBasis K I + c • cubeBasis K (replSet I a b h.1 h.2)
      else cubeBasis K I := by
  have hmap := CFSG.LieType.Chevalley.ExteriorCube.map_transvection_wedgeBasis (R := K) (n := 6)
    (k := 3) hab c I
  rw [rho_apply_eq_map, transvGL_val]
  simp only [cubeBasis_eq_wedgeBasis]
  exact hmap

theorem coord_rho_cubeBasis_pos {a b : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hne : a ≠ b) (c : K) (I J : Set.powersetCard (Fin 6) 3) (hJ : a ∈ J.val ∧ b ∉ J.val) :
    coord K (rho K (transvGL K a b hne c) (cubeBasis K I)) J =
      coord K (cubeBasis K I) J + c * coord K (cubeBasis K I) (replSet J b a hJ.1 hJ.2) := by
  rw [rho_transvGL_cubeBasis hab hne c I]
  by_cases h : b ∈ I.val ∧ a ∉ I.val
  · rw [dif_pos h]
    simp only [coord_add, coord_smul, coord_cubeBasis, smul_eq_mul]
    by_cases hq : replSet I a b h.1 h.2 = J
    · rw [if_pos hq, if_pos ((replSet_eq_iff h.1 h.2 hJ.1 hJ.2).mp hq)]
    · rw [if_neg hq, if_neg (fun h' => hq ((replSet_eq_iff h.1 h.2 hJ.1 hJ.2).mpr h'))]
  · rw [dif_neg h]
    simp only [coord_cubeBasis]
    have hq : ¬ (I = replSet J b a hJ.1 hJ.2) := fun h' => h (replSet_mem_imp hne hJ.1 hJ.2 h')
    rw [if_neg hq, mul_zero, add_zero]

theorem coord_rho_cubeBasis_neg {a b : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hne : a ≠ b) (c : K) (I J : Set.powersetCard (Fin 6) 3) (hJ : ¬ (a ∈ J.val ∧ b ∉ J.val)) :
    coord K (rho K (transvGL K a b hne c) (cubeBasis K I)) J = coord K (cubeBasis K I) J := by
  rw [rho_transvGL_cubeBasis hab hne c I]
  by_cases h : b ∈ I.val ∧ a ∉ I.val
  · rw [dif_pos h]
    simp only [coord_add, coord_smul, coord_cubeBasis, smul_eq_mul]
    by_cases hq : replSet I a b h.1 h.2 = J
    · exact absurd (replSet_eq_imp hne h.1 h.2 hq) hJ
    · rw [if_neg hq, mul_zero, add_zero]
  · rw [dif_neg h]

theorem coord_rho_transvGL {a b : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) (hne : a ≠ b)
    (c : K) (ξ : Cube K) (J : Set.powersetCard (Fin 6) 3) :
    coord K (rho K (transvGL K a b hne c) ξ) J =
      coord K ξ J + (if h : a ∈ J.val ∧ b ∉ J.val then c * coord K ξ (replSet J b a h.1 h.2) else 0) := by
  have hξ : ξ ∈ Submodule.span K (Set.range (cubeBasis K)) := by
    rw [(cubeBasis K).span_eq]
    exact Submodule.mem_top
  by_cases hJ : a ∈ J.val ∧ b ∉ J.val
  · rw [dif_pos hJ]
    induction hξ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨I, rfl⟩ := hx
      exact coord_rho_cubeBasis_pos hab hne c I J hJ
    | zero => simp only [map_zero, coord_zero, mul_zero, add_zero]
    | add x y _ _ hx hy =>
      simp only [map_add, coord_add]
      rw [hx, hy]
      ring
    | smul r x _ hx =>
      simp only [map_smul, coord_smul]
      rw [hx]
      ring
  · rw [dif_neg hJ, add_zero]
    induction hξ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨I, rfl⟩ := hx
      exact coord_rho_cubeBasis_neg hab hne c I J hJ
    | zero => simp only [map_zero, coord_zero]
    | add x y _ _ hx hy =>
      simp only [map_add, coord_add]
      rw [hx, hy]
    | smul r x _ hx =>
      simp only [map_smul, coord_smul]
      rw [hx]

theorem coord_eq_zero_of_fixed {a b : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) (hne : a ≠ b)
    {ξ : Cube K} (h : rho K (transvGL K a b hne 1) ξ = ξ) {I : Set.powersetCard (Fin 6) 3}
    (hb : b ∈ I.val) (ha : a ∉ I.val) : coord K ξ I = 0 := by
  have hJ := replSet_eq_imp hne hb ha rfl
  have key := coord_rho_transvGL hab hne 1 ξ (replSet I a b hb ha)
  rw [dif_pos hJ, h] at key
  have hI : I = replSet (replSet I a b hb ha) b a hJ.1 hJ.2 :=
    (replSet_eq_iff hb ha hJ.1 hJ.2).mp rfl
  rw [← hI, one_mul] at key
  linear_combination -key

theorem coord_ιMulti_e_sorted {i j k : Fin 6} (hij : i < j) (hjk : j < k)
    (J : Set.powersetCard (Fin 6) 3) :
    coord K (ιMulti K 3 ![e K i, e K j, e K k]) J = if J.val = {i, j, k} then 1 else 0 := by
  have hv : ∀ r : Fin 3, (![e K i, e K j, e K k] : Fin 3 → Fin 6 → K) r = e K (![i, j, k] r) := by
    intro r
    fin_cases r <;> rfl
  by_cases hJ : J.val = {i, j, k}
  · rw [if_pos hJ]
    have hJe : J = tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne := Subtype.ext hJ
    rw [hJe, coord_ιMulti_sorted _ hij hjk]
    unfold minor3
    have hM : (Matrix.of fun r (s : Fin 3) =>
        (![e K i, e K j, e K k] : Fin 3 → Fin 6 → K) r (![i, j, k] s)) = 1 := by
      ext r s
      rw [Matrix.of_apply, hv, Matrix.one_apply]
      fin_cases r <;> fin_cases s <;>
        simp [e, Pi.single_apply, hij.ne, hij.ne', hjk.ne, hjk.ne', (hij.trans hjk).ne,
          (hij.trans hjk).ne']
    rw [hM, Matrix.det_one]
  · rw [if_neg hJ]
    have hex : ∃ r : Fin 3, ![i, j, k] r ∉ J.val := by
      by_contra hcon
      push_neg at hcon
      apply hJ
      have hsub : ({i, j, k} : Finset (Fin 6)) ⊆ J.val := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hcon 0
        · exact hcon 1
        · exact hcon 2
      have hc3 : ({i, j, k} : Finset (Fin 6)).card = 3 :=
        Finset.card_eq_three.mpr ⟨i, j, k, hij.ne, (hij.trans hjk).ne, hjk.ne, rfl⟩
      have hJc : J.val.card = 3 := J.prop
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    obtain ⟨r, hr⟩ := hex
    rw [coord_ιMulti]
    apply Matrix.det_eq_zero_of_row_eq_zero r
    intro s
    rw [Matrix.of_apply, hv]
    simp only [e, Pi.single_apply]
    apply if_neg
    intro heq
    apply hr
    rw [← heq]
    exact CFSG.LieType.Chevalley.ExteriorCube.enum_mem J s

end CFSG.RankThree.GF2n.Smith81.A5Cube
