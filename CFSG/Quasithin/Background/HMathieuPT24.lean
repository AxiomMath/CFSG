module

public import CFSG.Quasithin.Background.HMathieuCent

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

@[expose] def PT.allOK {d : ℕ} (T : PT d) (ok : Array ℕ → Array ℕ → Bool) : Bool :=
  (List.range T.n).all fun p => ok T.elems[p]! T.elems[T.invIdx p]!

theorem PT.ok_of_allOK {d : ℕ} {T : PT d} [Fact (T.check = true)]
    {ok : Array ℕ → Array ℕ → Bool} (h : T.allOK ok = true) (p : T.Elem) :
    ok (T.arr p) (T.arr p⁻¹) = true :=
  List.all_eq_true.1 h p.idx (List.mem_range.2 p.lt)

@[expose] def PT.posArr {d : ℕ} (T : PT d) (R : List T.Elem) : Array ℕ :=
  Array.ofFn fun i : Fin T.n => R.idxOf (T.elemEquiv.symm i)

theorem PT.posArr_spec {d : ℕ} (T : PT d) (R : List T.Elem) (x : T.Elem) :
    (T.posArr R)[x.idx]! = pos R x := by
  rw [PT.posArr, getElem!_pos _ x.idx (by simpa using x.lt), Array.getElem_ofFn]
  rfl

@[expose] def okAut (a b : Array ℕ) : Bool := autArrOK a b

@[expose] def okM23 (a b : Array ℕ) : Bool := autArrOK a b && a[0]! == 0

@[expose] def okPlus (a b : Array ℕ) : Bool :=
  autArrOK a b && ((a[0]! == 0 && a[1]! == 1) || (a[0]! == 1 && a[1]! == 0))

variable (T : PT 24) [Fact (T.check = true)]

theorem PT.hasArr_perm (p : T.Elem) : HasArr (T.perm p) (T.arr p) := T.perm_val p

theorem PT.mem_autPerm {ok : Array ℕ → Array ℕ → Bool}
    (hok : ∀ a b, ok a b = true → autArrOK a b = true) (h : T.allOK ok = true) (p : T.Elem) :
    T.perm p ∈ AutPerm :=
  mem_AutPerm_of_arr (T.invPairOK_arr p) (hok _ _ (PT.ok_of_allOK h p))

theorem PT.mem_mog23 (h : T.allOK okM23 = true) (p : T.Elem) : T.perm p ∈ mog23 := by
  have hok := PT.ok_of_allOK h p
  simp only [okM23, Bool.and_eq_true, beq_iff_eq] at hok
  exact ⟨mem_AutPerm_of_arr (T.invPairOK_arr p) hok.1,
    (mem_stab_iff 0 _).2 (HasArr.apply_eq (T.hasArr_perm p) 0 hok.2)⟩

theorem PT.mem_mog22plus (h : T.allOK okPlus = true) (p : T.Elem) : T.perm p ∈ mog22plus := by
  have hok := PT.ok_of_allOK h p
  simp only [okPlus, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
  have harr := T.hasArr_perm p
  refine ⟨mem_AutPerm_of_arr (T.invPairOK_arr p) hok.1, ?_⟩
  rcases hok.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨HasArr.apply_eq harr 0 h0, HasArr.apply_eq harr 1 h1⟩
  · exact Or.inr ⟨HasArr.apply_eq harr 0 h0, HasArr.apply_eq harr 1 h1⟩

@[expose] def PT.toSub (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : ∀ p : T.Elem, T.perm p ∈ Γ) :
    T.Elem →* ↥Γ where
  toFun p := ⟨T.perm p, hΓ p⟩
  map_one' := Subtype.ext T.perm_one
  map_mul' p q := Subtype.ext (T.perm_mul p q)

theorem PT.toSub_injective (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hΓ : ∀ p : T.Elem, T.perm p ∈ Γ) : Function.Injective (T.toSub Γ hΓ) :=
  fun _ _ hpq => T.perm_injective (congrArg Subtype.val hpq)

theorem PT.hasArr_toSub (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : ∀ p : T.Elem, T.perm p ∈ Γ)
    (p : T.Elem) : HasArr ((T.toSub Γ hΓ p : ↥Γ) : Equiv.Perm (Fin 24)) (T.arr p) :=
  T.perm_val p

@[expose] def matsOf10 (T : PT 24) : Array (List ℕ) := T.elems.map fun a => matOf 10 (act10 a)

@[expose] def matsOf11 (T : PT 24) : Array (List ℕ) := T.elems.map fun a => matOf 11 (act11 a)

theorem matsOf10_get (p : T.Elem) : (matsOf10 T)[p.idx]! = matOf 10 (act10 (T.arr p)) := by
  have hlt : p.idx < T.elems.size := by rw [T.size_elems]; exact p.lt
  rw [matsOf10, getElem!_pos _ p.idx (by simpa using hlt), Array.getElem_map, PT.arr,
    getElem!_pos _ p.idx hlt]

theorem matsOf11_get (p : T.Elem) : (matsOf11 T)[p.idx]! = matOf 11 (act11 (T.arr p)) := by
  have hlt : p.idx < T.elems.size := by rw [T.size_elems]; exact p.lt
  rw [matsOf11, getElem!_pos _ p.idx (by simpa using hlt), Array.getElem_map, PT.arr,
    getElem!_pos _ p.idx hlt]

theorem actM_mats10 {mats : Array (List ℕ)} (hm : mats = matsOf10 T) (p : T.Elem) {m : ℕ}
    (hm2 : m < 2 ^ 10) : actM (mats[p.idx]!) m = act10 (T.arr p) m := by
  rw [hm, matsOf10_get, actM_matOf (xorLin_act10 _) 10 m hm2]

theorem actM_mats11 {mats : Array (List ℕ)} (hm : mats = matsOf11 T) (p : T.Elem) {m : ℕ}
    (hm2 : m < 2 ^ 11) : actM (mats[p.idx]!) m = act11 (T.arr p) m := by
  rw [hm, matsOf11_get, actM_matOf (xorLin_act11 _) 11 m hm2]

end CFSG.Quasithin.H.Mathieu
