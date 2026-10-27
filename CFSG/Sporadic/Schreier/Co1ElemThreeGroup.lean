module

public import CFSG.Sporadic.Schreier.Co1ElemThreeCheck

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_apply toVecD toVecD_injective)
open ElemThree Matrix

theorem ws_rep :
    List.Forall₂ MRep Native.elemDag.1 Ws := by
  unfold Ws
  have h := elem_check
  simp only [Native.elemCheck, Bool.and_eq_true] at h
  exact dag_rep (List.Forall₂.cons rep_y (List.Forall₂.cons rep_t
    (List.Forall₂.cons rep_z List.Forall₂.nil))) _ h.1.1

theorem W_rep
    (k : ℕ) : MRep (Native.elemDag.1.getD k Native.one) (W k) :=
  getD_rep ws_rep MRep.one k

theorem a_rep
    (i : Fin 6) : MRep (Native.aRows i.val) (a i) := W_rep _

theorem rowsMatrix_injective_of_wf {X Y : Native.Rows} (hX : Native.wf X = true)
    (hY : Native.wf Y = true) (h : rowsMatrix 24 X = rowsMatrix 24 Y) : X = Y := by
  simp only [Native.wf, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at hX hY
  apply Array.ext (hX.1.trans hY.1.symm)
  intro i hi₁ hi₂
  have hi : i < 24 := hX.1 ▸ hi₁
  apply toVecD_injective (d := 24) (hX.2 i hi₁) (hY.2 i hi₂)
  funext j
  have := congrFun (congrFun h ⟨i, hi⟩) j
  simp only [rowsMatrix_apply, Array.getElem?_eq_getElem hi₁, Array.getElem?_eq_getElem hi₂,
    Option.getD_some] at this
  exact this

theorem a_comm
    (i j : Fin 6) : Commute (a i) (a j) := by
  have h := elem_check
  simp only [Native.elemCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  have hij := h.1.2 i.val i.isLt j.val j.isLt
  have h1 := (a_rep i).mul (a_rep j)
  have h2 := (a_rep j).mul (a_rep i)
  rw [hij] at h1
  exact h1.eq h2

theorem a_pow_three
    (i : Fin 6) : a i ^ 3 = 1 := by
  have h := elem_check
  simp only [Native.elemCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  have h3 := h.2 i.val i.isLt
  have := (a_rep i).pow 3
  rw [h3] at this
  exact this.eq MRep.one

theorem a_mem_E (i : Fin 6) : a i ∈ E := Subgroup.subset_closure ⟨i, rfl⟩

theorem E_comm :
    ∀ x ∈ E, ∀ y ∈ E, Commute x y := by
  have h1 : ∀ i : Fin 6, ∀ y ∈ E, Commute (a i) y := by
    intro i y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact a_comm i j
    | one => exact Commute.one_right _
    | mul y z _ _ hy hz => exact Commute.mul_right hy hz
    | inv y _ hy => exact Commute.inv_right hy
  intro x hx y hy
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h1 i y hy
  | one => exact Commute.one_left _
  | mul x z _ _ hx hz => exact Commute.mul_left hx hz
  | inv x _ hx => exact Commute.inv_left hx

@[expose] noncomputable def eProd (b : Fin 6 → ZMod 3) : GL24 :=
  ((List.finRange 6).map fun i => a i ^ (b i).val).prod

theorem MRep.listProd {Rs : List Native.Rows} {gs : List GL24} (h : List.Forall₂ MRep Rs gs) :
    MRep (Rs.foldr Native.mul Native.one) gs.prod := by
  induction h with
  | nil => exact MRep.one
  | cons hab _ ih =>
    rw [List.foldr_cons, List.prod_cons]
    exact hab.mul ih

theorem eProd_rep
    (b : Fin 6 → ZMod 3) : MRep (Native.eRows b) (eProd b) := by
  unfold Native.eRows eProd
  apply MRep.listProd
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun i _ => (a_rep i).pow _

theorem list_prod_map_mul_of_commute {ι G : Type*} [Monoid G] (l : List ι) (f g : ι → G)
    (h : ∀ i ∈ l, ∀ j ∈ l, Commute (g i) (f j)) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih fun i hi j hj => h i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj)]
    have hc : Commute (g i) (l.map f).prod := Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact h i List.mem_cons_self j (List.mem_cons_of_mem _ hj)
    rw [mul_assoc, ← mul_assoc (g i), Commute.eq hc, mul_assoc, mul_assoc]

theorem pow_val_add_of_pow_three {G : Type*} [Monoid G] {x : G} (hx : x ^ 3 = 1) (m n : ZMod 3) :
    x ^ (m + n).val = x ^ m.val * x ^ n.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (m.val + n.val) 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem eProd_add
    (b b' : Fin 6 → ZMod 3) : eProd (b + b') = eProd b * eProd b' := by
  have hc : ∀ i ∈ List.finRange 6, ∀ j ∈ List.finRange 6,
      Commute (a i ^ (b' i).val) (a j ^ (b j).val) := by
    intro i _ j _
    apply Commute.pow_pow
    exact a_comm i j
  have h := @list_prod_map_mul_of_commute (Fin 6) GL24 Units.instMonoid (List.finRange 6)
    (fun i => a i ^ (b i).val) (fun i => a i ^ (b' i).val) hc
  have h2 : ∀ i : Fin 6, a i ^ (b i + b' i).val = a i ^ (b i).val * a i ^ (b' i).val :=
    fun i => @pow_val_add_of_pow_three GL24 Units.instMonoid (a i) (a_pow_three i) _ _
  unfold eProd
  rw [← h]
  simp only [Pi.add_apply, h2]

theorem eProd_zero : eProd 0 = 1 := by
  unfold eProd
  simp

theorem eProd_mem (b : Fin 6 → ZMod 3) : eProd b ∈ E := by
  unfold eProd
  refine Subgroup.list_prod_mem E fun x hx => ?_
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact pow_mem (a_mem_E i) _

theorem eProd_single
    (i : Fin 6) : eProd (Pi.single i 1) = a i := by
  have hc := e_check
  simp only [Native.eCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hc
  have h1 := eProd_rep (Pi.single i 1)
  rw [hc.2 i (List.mem_finRange i)] at h1
  exact h1.eq (a_rep i)

@[expose] noncomputable def eHom :
    Multiplicative (Fin 6 → ZMod 3) →* GL24 where
  toFun b := eProd b.toAdd
  map_one' := eProd_zero
  map_mul' b b' := eProd_add b.toAdd b'.toAdd

theorem eHom_injective :
    Function.Injective eHom := by
  intro b b' h
  have h1 := eProd_rep b.toAdd
  have h2 := eProd_rep b'.toAdd
  change eProd b.toAdd = eProd b'.toAdd at h
  rw [h] at h1
  have hc := e_check
  simp only [Native.eCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hrows := rowsMatrix_injective_of_wf (hc.1.1 _ (Finset.mem_univ _))
    (hc.1.1 _ (Finset.mem_univ _)) (h1.trans h2.symm)
  exact Multiset.inj_on_of_nodup_map hc.1.2 _ (Finset.mem_val.mpr (Finset.mem_univ _)) _
    (Finset.mem_val.mpr (Finset.mem_univ _)) hrows

theorem eHom_range :
    eHom.range = E := by
  apply le_antisymm
  · rintro _ ⟨b, rfl⟩
    exact eProd_mem _
  · rw [E, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd (Pi.single i 1), eProd_single i⟩

@[expose] noncomputable def eEquiv :
    Multiplicative (Fin 6 → ZMod 3) ≃* E :=
  (MonoidHom.ofInjective eHom_injective).trans (MulEquiv.subgroupCongr eHom_range)

theorem eEquiv_apply
    (b : Fin 6 → ZMod 3) :
    ((eEquiv (Multiplicative.ofAdd b) : E) : GL24) = eProd b := rfl

theorem card_E :
    Nat.card E = 3 ^ 6 := by
  rw [← Nat.card_congr eEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_fin]

theorem E_le_K : E ≤ ThreeLocal.K := by
  have hy : ThreeLocal.y ∈ ThreeLocal.K := Subgroup.subset_closure (Set.mem_insert _ _)
  have ht : ThreeLocal.t ∈ ThreeLocal.K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hz : ThreeLocal.z ∈ ThreeLocal.K := by
    unfold ThreeLocal.z
    exact pow_mem (mul_mem (mul_mem (mul_mem ht hy) (inv_mem ht)) (inv_mem hy)) 7
  have hW : ∀ g ∈ Ws, g ∈ ThreeLocal.K := by
    unfold Ws
    apply dagG_mem
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    exacts [hy, ht, hz]
  rw [E, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact getD_mem_of_forall hW _

theorem E_pow_three :
    ∀ x ∈ E, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨b, rfl⟩ : x ∈ eHom.range := eHom_range ▸ hx
  rw [← map_pow]
  have hb : b ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [hb, map_one]

end CFSG.Sporadic.Co1Schreier
