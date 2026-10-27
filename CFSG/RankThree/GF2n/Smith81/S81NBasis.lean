module

public import CFSG.RankThree.GF2n.Smith81.S81A5Fixed

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

@[expose] noncomputable def ub (K : Type*) [Field K] (i j k : Fin 6) (hij : i < j := by decide)
    (hjk : j < k := by decide) : Cube K :=
  cubeBasis K (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne)

private theorem neg_eq_self_cube [CharP K 2] (x : Cube K) : -x = x := by
  have h2 : (2 : K) • x = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  rw [two_smul] at h2
  exact neg_eq_of_add_eq_zero_left h2

private theorem units_smul_eq_self_of_charTwo [CharP K 2] (u : ℤˣ) (x : Cube K) :
    u • x = x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [Units.smul_def, Units.val_one, one_smul]
  · rw [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul, neg_eq_self_cube]

private theorem exists_perm_enum {I : Set.powersetCard (Fin 6) 3} {a b c : Fin 6} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hI : I.val = {a, b, c}) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ s, enum I (σ s) = ![a, b, c] s := by
  have hf := vecCons_triple_injective hab hac hbc
  have hg : ∀ s, enum I (Function.invFun (enum I) (![a, b, c] s)) = ![a, b, c] s :=
    fun s => Function.invFun_eq (Set.mem_range.mp (mem_range_enum_of_triple hI s))
  have hinj : Function.Injective (fun s => Function.invFun (enum I) (![a, b, c] s)) := by
    intro s t hst
    apply hf
    calc ![a, b, c] s = enum I (Function.invFun (enum I) (![a, b, c] s)) := (hg s).symm
      _ = enum I (Function.invFun (enum I) (![a, b, c] t)) := congrArg (⇑(enum I)) hst
      _ = ![a, b, c] t := hg t
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), hg⟩

theorem ι3_e_eq_cubeBasis [CharP K 2] {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (I : Set.powersetCard (Fin 6) 3) (hI : I.val = {a, b, c}) :
    ιMulti K 3 ![e K a, e K b, e K c] = cubeBasis K I := by
  obtain ⟨σ, hσ⟩ := exists_perm_enum (I := I) hab hac hbc hI
  have hv : (![e K a, e K b, e K c] : Fin 3 → Fin 6 → K) = (fun s => e K (enum I s)) ∘ σ := by
    funext s
    simp only [Function.comp_apply]
    rw [hσ s]
    fin_cases s <;> rfl
  rw [cubeBasis_apply, hv, AlternatingMap.map_perm, units_smul_eq_self_of_charTwo]

private theorem transvGL_mulVec_e_self {i j : Fin 6} (hij : i ≠ j) (c : K) :
    ((transvGL K i j hij c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ e K j =
      e K j + c • e K i := by
  rw [transvGL_val, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_single_one]
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Matrix.single_apply, Matrix.col_apply, e, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.col_apply, e, Pi.single_apply, hki, Ne.symm hki]

private theorem transvGL_mulVec_e_of_ne {i j m : Fin 6} (hij : i ≠ j) (c : K) (hm : m ≠ j) :
    ((transvGL K i j hij c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ e K m = e K m := by
  rw [transvGL_val, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_single_one]
  funext k
  simp [Matrix.single_apply, Matrix.col_apply, Ne.symm hm]

private theorem rho_ι3_e (g : GL (Fin 6) K) (x y z : Fin 6) :
    rho K g (ιMulti K 3 ![e K x, e K y, e K z]) =
      ιMulti K 3 ![(g : Matrix (Fin 6) (Fin 6) K) *ᵥ e K x,
        (g : Matrix (Fin 6) (Fin 6) K) *ᵥ e K y, (g : Matrix (Fin 6) (Fin 6) K) *ᵥ e K z] := by
  rw [rho_ιMulti]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem exists_triple_of_mem (I : Set.powersetCard (Fin 6) 3) {j : Fin 6}
    (hj : j ∈ I.val) :
    ∃ b d : Fin 6, j ≠ b ∧ j ≠ d ∧ b ≠ d ∧ I.val.erase j = {b, d} ∧ I.val = {j, b, d} := by
  have hc : (I.val.erase j).card = 2 := by
    simp [Finset.card_erase_of_mem hj, I.prop]
  obtain ⟨b, d, hbd, hI'⟩ := Finset.card_eq_two.mp hc
  have hb : b ∈ I.val.erase j := by rw [hI']; simp
  have hd : d ∈ I.val.erase j := by rw [hI']; simp
  refine ⟨b, d, (Finset.ne_of_mem_erase hb).symm, (Finset.ne_of_mem_erase hd).symm, hbd, hI', ?_⟩
  rw [← Finset.insert_erase hj, hI']

theorem rho_transvGL_cubeBasis_gen [CharP K 2] (i j : Fin 6) (hij : i ≠ j) (c : K)
    (I : Set.powersetCard (Fin 6) 3) :
    rho K (transvGL K i j hij c) (cubeBasis K I) =
      if h : j ∈ I.val ∧ i ∉ I.val then cubeBasis K I + c • cubeBasis K (replSet I i j h.1 h.2)
      else cubeBasis K I := by
  by_cases hjI : j ∈ I.val
  · obtain ⟨b, d, hjb, hjd, hbd, hbd', hI⟩ := exists_triple_of_mem I hjI
    rw [← ι3_e_eq_cubeBasis hjb hjd hbd I hI, rho_ι3_e, transvGL_mulVec_e_self hij c,
      transvGL_mulVec_e_of_ne hij c hjb.symm, transvGL_mulVec_e_of_ne hij c hjd.symm,
      ι3_add_fst, ι3_smul_fst]
    by_cases hiI : i ∈ I.val
    · have hn : ¬ (j ∈ I.val ∧ i ∉ I.val) := fun h => h.2 hiI
      have hz : ιMulti K 3 ![e K i, e K b, e K d] = 0 := by
        rw [hI] at hiI
        simp only [Finset.mem_insert, Finset.mem_singleton] at hiI
        rcases hiI with h | h | h
        · exact absurd h hij
        · rw [h]; exact ι3_eq_fst_snd _ _
        · rw [h]; exact ι3_eq_fst_thd _ _
      rw [dif_neg hn, hz, smul_zero, add_zero]
    · have hn : j ∈ I.val ∧ i ∉ I.val := ⟨hjI, hiI⟩
      have hib : i ≠ b := fun h => hiI (by rw [hI, h]; simp)
      have hid : i ≠ d := fun h => hiI (by rw [hI, h]; simp)
      have hRval : (replSet I i j hn.1 hn.2).val = {i, b, d} := by
        show insert i (I.val.erase j) = {i, b, d}
        rw [hbd']
      rw [dif_pos hn, ι3_e_eq_cubeBasis hib hid hbd (replSet I i j hn.1 hn.2) hRval]
  · obtain ⟨x, y, z, hxy, hxz, hyz, hI⟩ := exists_triple I
    have hxj : x ≠ j := fun h => hjI (by rw [hI, h]; simp)
    have hyj : y ≠ j := fun h => hjI (by rw [hI, h]; simp)
    have hzj : z ≠ j := fun h => hjI (by rw [hI, h]; simp)
    have hn : ¬ (j ∈ I.val ∧ i ∉ I.val) := fun h => hjI h.1
    rw [dif_neg hn, ← ι3_e_eq_cubeBasis hxy hxz hyz I hI, rho_ι3_e,
      transvGL_mulVec_e_of_ne hij c hxj, transvGL_mulVec_e_of_ne hij c hyj,
      transvGL_mulVec_e_of_ne hij c hzj]

private theorem coord_rho_cubeBasis_pos_gen [CharP K 2] {i j : Fin 6} (hij : i ≠ j) (c : K)
    (I J : Set.powersetCard (Fin 6) 3) (hJ : i ∈ J.val ∧ j ∉ J.val) :
    coord K (rho K (transvGL K i j hij c) (cubeBasis K I)) J =
      coord K (cubeBasis K I) J + c * coord K (cubeBasis K I) (replSet J j i hJ.1 hJ.2) := by
  rw [rho_transvGL_cubeBasis_gen i j hij c I]
  by_cases h : j ∈ I.val ∧ i ∉ I.val
  · rw [dif_pos h]
    simp only [coord_add, coord_smul, coord_cubeBasis, smul_eq_mul]
    by_cases hq : replSet I i j h.1 h.2 = J
    · rw [if_pos hq, if_pos ((replSet_eq_iff h.1 h.2 hJ.1 hJ.2).mp hq)]
    · rw [if_neg hq, if_neg (fun h' => hq ((replSet_eq_iff h.1 h.2 hJ.1 hJ.2).mpr h'))]
  · rw [dif_neg h]
    simp only [coord_cubeBasis]
    have hq : ¬ (I = replSet J j i hJ.1 hJ.2) := fun h' => h (replSet_mem_imp hij hJ.1 hJ.2 h')
    rw [if_neg hq, mul_zero, add_zero]

private theorem coord_rho_cubeBasis_neg_gen [CharP K 2] {i j : Fin 6} (hij : i ≠ j) (c : K)
    (I J : Set.powersetCard (Fin 6) 3) (hJ : ¬ (i ∈ J.val ∧ j ∉ J.val)) :
    coord K (rho K (transvGL K i j hij c) (cubeBasis K I)) J = coord K (cubeBasis K I) J := by
  rw [rho_transvGL_cubeBasis_gen i j hij c I]
  by_cases h : j ∈ I.val ∧ i ∉ I.val
  · rw [dif_pos h]
    simp only [coord_add, coord_smul, coord_cubeBasis, smul_eq_mul]
    by_cases hq : replSet I i j h.1 h.2 = J
    · exact absurd (replSet_eq_imp hij h.1 h.2 hq) hJ
    · rw [if_neg hq, mul_zero, add_zero]
  · rw [dif_neg h]

theorem coord_rho_transvGL_gen [CharP K 2] (i j : Fin 6) (hij : i ≠ j) (c : K) (ξ : Cube K)
    (J : Set.powersetCard (Fin 6) 3) :
    coord K (rho K (transvGL K i j hij c) ξ) J =
      coord K ξ J + (if h : i ∈ J.val ∧ j ∉ J.val then c * coord K ξ (replSet J j i h.1 h.2)
        else 0) := by
  have hξ : ξ ∈ Submodule.span K (Set.range (cubeBasis K)) := by
    rw [(cubeBasis K).span_eq]
    exact Submodule.mem_top
  by_cases hJ : i ∈ J.val ∧ j ∉ J.val
  · rw [dif_pos hJ]
    induction hξ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨I, rfl⟩ := hx
      exact coord_rho_cubeBasis_pos_gen hij c I J hJ
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
      exact coord_rho_cubeBasis_neg_gen hij c I J hJ
    | zero => simp only [map_zero, coord_zero]
    | add x y _ _ hx hy =>
      simp only [map_add, coord_add]
      rw [hx, hy]
    | smul r x _ hx =>
      simp only [map_smul, coord_smul]
      rw [hx]

private theorem coord_finset_sum {ι : Type*} (s : Finset ι) (g : ι → K) (f : ι → Cube K)
    (I : Set.powersetCard (Fin 6) 3) :
    coord K (∑ j ∈ s, g j • f j) I = ∑ j ∈ s, g j * coord K (f j) I := by
  unfold coord
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

open _root_.Classical in
theorem linearIndependent_of_pivots {ι : Type*} [Fintype ι] (f : ι → Cube K)
    (J : ι → Set.powersetCard (Fin 6) 3)
    (h : ∀ i j, coord K (f i) (J j) = if i = j then 1 else 0) : LinearIndependent K f := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have key : coord K (∑ j ∈ s, g j • f j) (J i) = coord K 0 (J i) := by rw [hg]
  rw [coord_finset_sum, coord_zero, Finset.sum_eq_single i] at key
  · simpa [h i i] using key
  · intro j _ hji
    rw [h j i, if_neg hji, mul_zero]
  · intro hi'
    exact absurd hi hi'

theorem finrank_cube : Module.finrank K (Cube K) = 20 := by
  rw [Module.finrank_eq_nat_card_basis (cubeBasis K), Set.powersetCard.card,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  all_goals decide

end CFSG.RankThree.GF2n.Smith81.A5Cube
