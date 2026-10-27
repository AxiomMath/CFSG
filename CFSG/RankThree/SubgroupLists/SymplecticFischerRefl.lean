module

public import CFSG.RankThree.SubgroupLists.SymplecticFischerOrth
public import CFSG.Fischer.Classification.Recognition.R3Order

public section

namespace CFSG.RankThree.SubgroupLists

open CFSG.Open CFSG.Fischer.Classification CFSG.Fischer.Classification.Recognition.R3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace ReflFischer

theorem sign_eq_of_mul_self {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h : σ * σ = 1) :
    Equiv.Perm.sign σ = (-1) ^ ((Nat.card α - Nat.card (Function.fixedPoints σ)) / 2) := by
  classical
  have h2 : σ ^ 2 = 1 := by rw [sq, h]
  have hct : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 ((Equiv.Perm.pow_prime_eq_one_iff (p := 2)).1 h2)
  rw [Equiv.Perm.sign_of_cycleType_eq_replicate (by norm_num) hct, ite_eq_right (by decide),
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem coe_normPerm_apply {g : GL (Fin m) (ZMod 3)} (hg : F3.IsIsom f g)
    (x : {x : Fin m → ZMod 3 // f x x = 1}) :
    ((normPerm hg 1 x : {x : Fin m → ZMod 3 // f x x = 1}) : Fin m → ZMod 3) = F3.act g x := by
  simpa using coe_normPerm_pow hg 1 1 x

@[expose] noncomputable def normAction (hf : IsF3Form f) :
    F3.reflGroup f →* Equiv.Perm {x : Fin m → ZMod 3 // f x x = 1} where
  toFun g := normPerm (F3.isIsom_of_mem hf g.2) 1
  map_one' := Equiv.ext fun x => Subtype.ext (by
    rw [coe_normPerm_apply, OneMemClass.coe_one, F3.act_one]
    rfl)
  map_mul' g h := Equiv.ext fun x => Subtype.ext (by
    rw [Equiv.Perm.mul_apply, coe_normPerm_apply, coe_normPerm_apply, coe_normPerm_apply,
      Subgroup.coe_mul, F3.act_mul])

theorem coe_normAction_apply (hf : IsF3Form f) (g : F3.reflGroup f)
    (x : {x : Fin m → ZMod 3 // f x x = 1}) :
    ((normAction hf g x : {x : Fin m → ZMod 3 // f x x = 1}) : Fin m → ZMod 3) =
      F3.act (g : GL (Fin m) (ZMod 3)) x :=
  coe_normPerm_apply _ x

theorem normCount_le_two_mul_card_D3 (hf : IsF3Form f) (hm : 4 ≤ m) :
    normCount f 1 ≤ 2 * Nat.card (D3 f) := by
  classical
  have : Fintype (D3 f) := Fintype.ofFinite _
  let φ : {x : Fin m → ZMod 3 // f x x = 1} → D3 f := fun x => ⟨reflBar f x, reflBar_mem_D3 x.2⟩
  let ng : {x : Fin m → ZMod 3 // f x x = 1} → {x : Fin m → ZMod 3 // f x x = 1} := fun x =>
    ⟨-x.1, by rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg]; exact x.2⟩
  have hfib : ∀ b ∈ (Finset.univ : Finset {x : Fin m → ZMod 3 // f x x = 1}).image φ,
      (Finset.univ.filter fun a => φ a = b).card ≤ 2 := by
    intro b hb
    obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hb
    calc (Finset.univ.filter fun a => φ a = φ a₀).card ≤ ({a₀, ng a₀} : Finset _).card := by
          refine Finset.card_le_card fun a ha => ?_
          have hφ : reflBar f a₀ = reflBar f a :=
            (congrArg Subtype.val (Finset.mem_filter.1 ha).2).symm
          rcases (reflBar_eq_reflBar_iff hf hm a₀.2 a.2).1 hφ with h | h
          · simp [Subtype.ext h]
          · have : a = ng a₀ := Subtype.ext h
            simp [this]
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have h1 := Finset.card_le_mul_card_image (Finset.univ : Finset {x : Fin m → ZMod 3 // f x x = 1})
    2 hfib
  have h2 : ((Finset.univ : Finset {x : Fin m → ZMod 3 // f x x = 1}).image φ).card ≤
      Fintype.card (D3 f) := Finset.card_le_univ _
  rw [Finset.card_univ] at h1
  rw [normCount_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

theorem le_T_iterate (k : ℕ) (t : ℕ × ℕ × ℕ) : t.2.1 ≤ (T^[k] t).2.1 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (by simp only [T]; omega)

theorem le_normCount_of_five_le {n : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3)}
    (hf : IsF3Form f) (hn : 5 ≤ n) : 234 ≤ normCount f 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h5 : (T^[5] (1, 2, 0)).2.1 = 252 ∧ (T^[5] (1, 0, 2)).2.1 = 234 := by decide
  rcases normCount_one_mem hf with h | h <;> rw [h, Function.iterate_add_apply]
  · exact (by omega : 234 ≤ 252).trans (h5.1 ▸ le_T_iterate k _)
  · exact h5.2 ▸ le_T_iterate k _

theorem normCount_five {f : LinearMap.BilinForm (ZMod 3) (Fin (4 + 1) → ZMod 3)}
    (hf : IsF3Form f) : normCount f 1 = 90 ∨ normCount f 1 = 72 := by
  have h4 : (T^[4] (1, 2, 0)).2.1 = 90 ∧ (T^[4] (1, 0, 2)).2.1 = 72 := by decide
  rcases normCount_one_mem hf with h | h
  · exact Or.inl (h.trans h4.1)
  · exact Or.inr (h.trans h4.2)

theorem card_norm_one_perp {n : ℕ} {v : Fin m → ZMod 3}
    (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    Nat.card {x : Fin m → ZMod 3 // f x x = 1 ∧ f x v = 0} = normCount (restrictForm f e) 1 := by
  rw [normCount_def]
  refine Nat.card_congr
    { toFun := fun x => ⟨e ⟨x.1, F3.mem_perpOne.2 x.2.2⟩, by rw [restrictForm_apply]; exact x.2.1⟩
      invFun := fun y => ⟨(e.symm y : Fin m → ZMod 3), by
        have h := restrictForm_apply e (e.symm y) (e.symm y)
        rw [e.apply_symm_apply] at h
        exact ⟨h ▸ y.2, F3.mem_perpOne.1 (e.symm y).2⟩⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }

theorem not_isPerfect_R3 {f : LinearMap.BilinForm (ZMod 3) (Fin (4 + 1) → ZMod 3)}
    (hf : IsF3Form f) (hN : normCount f 1 = 72) : ¬ Group.IsPerfect (R3 f) := by
  intro hP
  classical
  have hN' : Nat.card {x : Fin (4 + 1) → ZMod 3 // f x x = 1} = 72 := hN
  obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  have hv0 : v ≠ 0 := F3.ne_zero_of_norm_one hv
  let e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne hv, Module.finrank_fin_fun])
  have hf' : IsF3Form (restrictForm f e) := isF3Form_restrictForm hf hv e
  have hrec := normCount_eq hf hv e 1
  rw [sub_self, hN] at hrec
  have h30 : normCount (restrictForm f e) 1 = 30 := by
    have h3 : T^[3] (1, 2, 0) = (33, 24, 24) ∧ T^[3] (1, 0, 2) = (21, 30, 30) := by decide
    rcases normTriple_eq 3 (restrictForm f e) hf' with h | h
    · rw [h3.1, Prod.mk.injEq, Prod.mk.injEq] at h
      omega
    · rw [h3.2, Prod.mk.injEq, Prod.mk.injEq] at h
      omega
  let ψ : F3.reflGroup f →* ℤˣ := Equiv.Perm.sign.comp (normAction hf)
  have hker : Subgroup.center (F3.reflGroup f) ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    rcases F3.coe_eq_of_mem_center hf (by omega) hz with h | h
    · rw [show z = 1 from Subtype.ext h, map_one]
    · have hσ : ∀ x, ((normAction hf z x : {x : Fin (4 + 1) → ZMod 3 // f x x = 1}) :
          Fin (4 + 1) → ZMod 3) = -x := fun x => by
        rw [coe_normAction_apply, h, F3.act_neg_one]
      have hsq : normAction hf z * normAction hf z = 1 :=
        Equiv.ext fun x => Subtype.ext (by rw [Equiv.Perm.mul_apply, hσ, hσ, neg_neg]; rfl)
      have hfix : Nat.card (Function.fixedPoints (normAction hf z)) = 0 := by
        refine Nat.card_eq_zero.2 (Or.inl ⟨fun x => ?_⟩)
        have hx : (x.1 : Fin (4 + 1) → ZMod 3) = -x.1 := by
          rw [← hσ]
          exact congrArg Subtype.val x.2.symm
        have h0 := F3.eq_zero_of_eq_neg hx
        have h1 := x.1.2
        rw [h0, LinearMap.BilinForm.zero_left] at h1
        exact zero_ne_one h1
      change Equiv.Perm.sign (normAction hf z) = 1
      rw [sign_eq_of_mul_self hsq, hfix, hN']
      decide
  let ψ' : R3 f →* ℤˣ := QuotientGroup.lift _ ψ hker
  have hone := eq_one_of_isPerfect hP ψ' (reflBar f v)
  set σ := normAction hf (reflElt f v)
  have hsq : σ * σ = 1 := by
    rw [← map_mul, show reflElt f v * reflElt f v = 1 from Subtype.ext (F3.refl_mul_self v),
      map_one]
  have hmemfix : ∀ x, x ∈ Function.fixedPoints σ ↔ f x.1 v = 0 := fun x => by
    rw [Function.mem_fixedPoints, Function.IsFixedPt, Subtype.ext_iff, coe_normAction_apply,
      coe_reflElt, F3.act_refl hv, add_eq_left, smul_eq_zero, or_iff_left hv0]
  have hfix : Nat.card (Function.fixedPoints σ) = 30 := by
    rw [← h30, ← card_norm_one_perp e]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (hmemfix x.1).1 x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, (hmemfix _).2 y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsign : ψ' (reflBar f v) = -1 := by
    rw [reflBar_def, QuotientGroup.lift_mk]
    change Equiv.Perm.sign σ = -1
    rw [sign_eq_of_mul_self hsq, hfix, hN']
    decide
  rw [hsign] at hone
  exact absurd hone (by decide)

end ReflFischer

open ReflFischer

theorem fischerReflectionCard : FischerReflectionCard := by
  intro m hm f hsymm hnd hP
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  change 45 ≤ Nat.card (D3 f)
  have hle := normCount_le_two_mul_card_D3 hf (by omega)
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn
  · rcases normCount_five hf with h | h
    · omega
    · exact (not_isPerfect_R3 hf h hP).elim
  · have := le_normCount_of_five_le hf hn
    omega
