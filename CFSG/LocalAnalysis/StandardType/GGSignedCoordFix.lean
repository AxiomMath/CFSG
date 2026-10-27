module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

open scoped BigOperators

variable {n p : ℕ}

private theorem fix_of_mem_closure {V : Type*} [Mul V] (S : Set (MulAut V)) (f : V)
    (hS : ∀ u ∈ S, u f = f) {u : MulAut V} (hu : u ∈ Subgroup.closure S) : u f = f := by
  induction hu using Subgroup.closure_induction with
  | mem u hu => exact hS u hu
  | one => rfl
  | mul u v _ _ ihu ihv => rw [MulAut.mul_apply, ihv, ihu]
  | inv u _ ihu => simpa [ihu] using MulAut.inv_apply_self (M := V) u f

private theorem sgnAut_fix_of_axis {j : Fin n} {f : Fin n → Multiplicative (ZMod p)}
    (hf : ∀ k, k ≠ j → f k = 1) {i : Fin n} (hi : i ≠ j) : sgnAut i f = f := by
  rw [sgnAut_apply]
  funext k
  by_cases hk : k = i
  · rw [hk, Function.update_self, hf i hi, inv_one]
  · rw [Function.update_of_ne hk]

private theorem permAut_swap_fix_of_axis {j : Fin n} {f : Fin n → Multiplicative (ZMod p)}
    (hf : ∀ k, k ≠ j → f k = 1) {a b : Fin n} (ha : a ≠ j) (hb : b ≠ j) :
    permAut (Equiv.swap a b) f = f := by
  rw [permAut_apply]
  funext k
  change f (Equiv.swap a b k) = f k
  by_cases hk : k = j
  · rw [hk, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]
  · have hsk : Equiv.swap a b k ≠ j := by
      intro h
      have hfixj : Equiv.swap a b j = j :=
        Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)
      have : k = j := by
        calc k = Equiv.swap a b (Equiv.swap a b k) :=
              (Equiv.swap_apply_self a b k).symm
          _ = Equiv.swap a b j := by rw [h]
          _ = j := hfixj
      exact hk this
    rw [hf (Equiv.swap a b k) hsk, hf k hk]

theorem negTrans_apply (a b : Fin n) (hab : a ≠ b)
    (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    ((sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ :
      MulAut (Fin n → Multiplicative (ZMod p))) f i) =
      if i = a then (f b)⁻¹ else if i = b then (f a)⁻¹ else f i := by
  have h2 : (sgnAut a : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut a = 1 := by
    simpa [sq] using sgnAut_sq a
  have hinv : (sgnAut a : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = sgnAut a :=
    inv_eq_of_mul_eq_one_right h2
  rw [hinv, MulAut.mul_apply, MulAut.mul_apply, sgnAut_apply, Function.update_apply]
  by_cases hia : i = a
  · rw [if_pos hia, if_pos hia, permAut_apply, Function.comp_apply]
    change ((sgnAut a f) (Equiv.swap a b a))⁻¹ = (f b)⁻¹
    rw [Equiv.swap_apply_left, sgnAut_apply, Function.update_of_ne (Ne.symm hab)]
  · rw [if_neg hia]
    by_cases hib : i = b
    · rw [hib, if_neg (Ne.symm hab), if_pos rfl, permAut_apply, Function.comp_apply]
      change (sgnAut a f) (Equiv.swap a b b) = (f a)⁻¹
      rw [Equiv.swap_apply_right, sgnAut_apply, Function.update_self]
    · rw [if_neg hia, if_neg hib, permAut_apply, Function.comp_apply]
      change (sgnAut a f) (Equiv.swap a b i) = f i
      rw [Equiv.swap_apply_of_ne_of_ne hia hib, sgnAut_apply, Function.update_of_ne hia]

theorem bCoordinateBlock_le_bSignedFull (j : Fin n) :
    bCoordinateBlock n p j ≤ bSignedFull n p := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro r (⟨i, _, rfl⟩ | ⟨a, b, hab, _, _, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨a, b, hab, rfl⟩)

theorem aPermutationFull_le_bSignedFull : aPermutationFull n p ≤ bSignedFull n p := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro r ⟨a, b, hab, rfl⟩
  exact Subgroup.subset_closure (Or.inr ⟨a, b, hab, rfl⟩)

theorem forall_bCoordinateBlock_fix_iff (hp : p.Prime) (hp2 : p ≠ 2) (j : Fin n)
    (f : Fin n → Multiplicative (ZMod p)) :
    (∀ u ∈ bCoordinateBlock n p j, u f = f) ↔ ∀ k, k ≠ j → f k = 1 := by
  constructor
  · intro h k hk
    have hfix := h (sgnAut k) (Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩))
    have hk' := congrArg (fun g : Fin n → Multiplicative (ZMod p) => toAdd (g k)) hfix
    rw [sgnAut_apply, Function.update_self, toAdd_inv] at hk'
    have hzero : toAdd (f k) = 0 := coord_eq_zero_of_eq_neg hp hp2 hk'.symm
    exact toAdd.injective (by simpa using hzero)
  · intro hf u hu
    refine fix_of_mem_closure _ f ?_ hu
    rintro r (⟨i, hi, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩)
    · exact sgnAut_fix_of_axis hf hi
    · exact permAut_swap_fix_of_axis hf ha hb

theorem forall_dCoordinateBlock_fix_iff (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) (j : Fin n)
    (f : Fin n → Multiplicative (ZMod p)) :
    (∀ u ∈ dCoordinateBlock n p j, u f = f) ↔ ∀ k, k ≠ j → f k = 1 := by
  constructor
  · intro h k hk
    obtain ⟨b, hbk, hbj⟩ := coord_exists_ne_ne hn k j
    have hkb : k ≠ b := fun h' => hbk h'.symm
    have hP := h (permAut (Equiv.swap k b))
      (Subgroup.subset_closure (Or.inl ⟨k, b, hkb, hk, hbj, rfl⟩))
    have hPk : f b = f k := by
      have := congrArg (fun g : Fin n → Multiplicative (ZMod p) => g k) hP
      rw [permAut_apply, Function.comp_apply] at this
      change f (Equiv.swap k b k) = f k at this
      rwa [Equiv.swap_apply_left] at this
    have hN := h (sgnAut k * permAut (Equiv.swap k b) * (sgnAut k)⁻¹)
      (Subgroup.subset_closure (Or.inr ⟨k, b, hkb, hk, hbj, rfl⟩))
    have hNk : (f b)⁻¹ = f k := by
      have := congrArg (fun g : Fin n → Multiplicative (ZMod p) => g k) hN
      rw [negTrans_apply (p := p) k b hkb f k] at this
      simpa [hkb] using this
    have hb_eq : f b = (f b)⁻¹ := by
      calc f b = f k := hPk
        _ = (f b)⁻¹ := hNk.symm
    have hz : toAdd (f b) = 0 := coord_eq_zero_of_eq_neg hp hp2 (congrArg toAdd hb_eq)
    have hb1 : f b = 1 := toAdd.injective (by simpa using hz)
    rw [← hPk, hb1]
  · intro hf u hu
    refine fix_of_mem_closure _ f ?_ hu
    rintro r (⟨a, b, hab, ha, hb, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩)
    · exact permAut_swap_fix_of_axis hf ha hb
    · have h1 : sgnAut a f = f := sgnAut_fix_of_axis hf ha
      have h2 : permAut (Equiv.swap a b) f = f := permAut_swap_fix_of_axis hf ha hb
      have h3 : (sgnAut a)⁻¹ f = f := by
        simpa [h1] using
          MulAut.inv_apply_self (M := Fin n → Multiplicative (ZMod p)) (sgnAut a) f
      rw [MulAut.mul_apply, MulAut.mul_apply, h3, h2, h1]

theorem forall_aPermutationFull_fix_iff (f : Fin n → Multiplicative (ZMod p)) :
    (∀ u ∈ aPermutationFull n p, u f = f) ↔ ∀ a b, f a = f b := by
  constructor
  · intro h a b
    by_cases hab : a = b
    · rw [hab]
    · have hP := h (permAut (Equiv.swap a b)) (Subgroup.subset_closure ⟨a, b, hab, rfl⟩)
      have := congrArg (fun g : Fin n → Multiplicative (ZMod p) => g a) hP
      rw [permAut_apply, Function.comp_apply] at this
      change f (Equiv.swap a b a) = f a at this
      rw [Equiv.swap_apply_left] at this
      exact this.symm
  · intro hf u hu
    refine fix_of_mem_closure _ f ?_ hu
    rintro r ⟨a, b, _hab, rfl⟩
    rw [permAut_apply]
    funext k
    change f (Equiv.swap a b k) = f k
    exact hf (Equiv.swap a b k) k

theorem forall_map_conj_fix_iff {V : Type*} [Mul V] (S : Subgroup (MulAut V)) (δ : MulAut V)
    (f : V) :
    (∀ u ∈ S.map (MulAut.conj δ).toMonoidHom, u f = f) ↔ ∀ u ∈ S, u (δ⁻¹ f) = δ⁻¹ f := by
  constructor
  · intro h u hu
    have hfix := h ((MulAut.conj δ).toMonoidHom u) (Subgroup.mem_map_of_mem _ hu)
    have h2 := congrArg (fun g => δ⁻¹ g) hfix
    simpa [MulAut.conj_apply, MulAut.mul_apply] using h2
  · intro h u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    have h2 := congrArg (fun g => δ g) (h v hv)
    simpa [MulAut.conj_apply, MulAut.mul_apply] using h2

theorem exists_const_of_forall_map_conj_aPermutationFull_fix
    (δ : MulAut (Fin n → Multiplicative (ZMod p))) {f : Fin n → Multiplicative (ZMod p)}
    (h : ∀ u ∈ (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom, u f = f) :
    ∃ c : ZMod p, f = δ (fun _ => ofAdd c) := by
  rcases n with _ | m
  · refine ⟨0, ?_⟩
    funext i
    exact i.elim0
  · have hfix : ∀ u ∈ aPermutationFull (m + 1) p, u (δ⁻¹ f) = δ⁻¹ f :=
      (forall_map_conj_fix_iff (aPermutationFull (m + 1) p) δ f).mp h
    have hconst := (forall_aPermutationFull_fix_iff (n := m + 1) (p := p) (δ⁻¹ f)).mp hfix
    let i : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
    refine ⟨toAdd ((δ⁻¹ f) i), ?_⟩
    have hδinv : δ⁻¹ f = fun _ => ofAdd (toAdd ((δ⁻¹ f) i)) := by
      refine eq_of_toAdd_eq fun k => ?_
      rw [hconst k i, toAdd_ofAdd]
    calc f = δ (δ⁻¹ f) :=
          (MulAut.apply_inv_self (M := Fin (m + 1) → Multiplicative (ZMod p)) δ f).symm
      _ = δ (fun _ => ofAdd (toAdd ((δ⁻¹ f) i))) := congrArg δ hδinv

@[expose] def negOff (j : Fin n) : MulAut (Fin n → Multiplicative (ZMod p)) :=
  diagAut (fun i => if i = j then 1 else -1) fun i => by split_ifs <;> simp

theorem negOff_apply (j : Fin n) (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    negOff j f i = if i = j then f i else (f i)⁻¹ := by
  rw [negOff, diagAut_apply]
  split_ifs with h
  · simp [h]
  · rw [neg_one_mul, ← toAdd_inv, ofAdd_toAdd]

private theorem diagAut_mem_bCoordinateBlock (j : Fin n) :
    ∀ (s : Finset (Fin n)), (∀ i ∈ s, i ≠ j) →
      ∀ (u : MulAut (Fin n → Multiplicative (ZMod p))) (ε : Fin n → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) → (∀ i, i ∉ s → ε i = 1) →
        (∀ f i, toAdd (u f i) = ε i * toAdd (f i)) → u ∈ bCoordinateBlock n p j := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _hs u ε _ hS hu
      have h1 : u = 1 := by
        refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
        rw [hu, hS i (Finset.notMem_empty i), one_mul]
        rfl
      rw [h1]
      exact Subgroup.one_mem _
  | insert a s ha ih =>
      intro hs u ε hε hS hu
      have haj : a ≠ j := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, i ≠ j := fun i hi => hs i (Finset.mem_insert_of_mem hi)
      rcases hε a with hεa | hεa
      · refine ih hs' u ε hε (fun i hi => ?_) hu
        by_cases hia : i = a
        · rw [hia, hεa]
        · exact hS i (by simp [hia, hi])
      · have h1 : u * sgnAut a ∈ bCoordinateBlock n p j := by
          refine ih hs' _ (Function.update ε a 1) (fun i => ?_) (fun i hi => ?_)
            (fun f i => ?_)
          · by_cases hia : i = a
            · subst hia
              simp
            · rw [Function.update_of_ne hia]
              exact hε i
          · by_cases hia : i = a
            · subst hia
              simp
            · rw [Function.update_of_ne hia]
              exact hS i (by simp [hia, hi])
          · rw [MulAut.mul_apply, hu, sgnAut_apply]
            by_cases hia : i = a
            · subst hia
              simp [hεa]
            · rw [Function.update_of_ne hia, Function.update_of_ne hia]
        have h2 := Subgroup.mul_mem _ h1
          (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl ⟨a, haj, rfl⟩)))
        rwa [mul_inv_cancel_right] at h2

theorem negOff_mem_bCoordinateBlock (j : Fin n) : negOff (p := p) j ∈ bCoordinateBlock n p j := by
  set ε : Fin n → ZMod p := fun i => if i = j then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    by_cases hi : i = j <;> simp [ε, hi]
  have hS : ∀ i, i ∉ Finset.univ.erase j → ε i = 1 := by
    intro i hi
    have : i = j := by simpa using hi
    subst this
    simp [ε]
  have hu : ∀ f i, toAdd (negOff (p := p) j f i) = ε i * toAdd (f i) := by
    intro f i
    rw [negOff, diagAut_apply, toAdd_ofAdd]
  exact diagAut_mem_bCoordinateBlock (p := p) j (Finset.univ.erase j)
    (fun i hi => (Finset.mem_erase.mp hi).1) (negOff j) ε hε hS hu

theorem exists_involution_mem_bCoordinateBlock_dCoordinateBlock (hp : p.Prime) (hn : 3 ≤ n)
    (j : Fin n) :
    ∃ τ : MulAut (Fin n → Multiplicative (ZMod p)), τ ∈ bCoordinateBlock n p j ∧
      τ ∈ dCoordinateBlock n p j ∧ τ ^ 2 = 1 ∧ τ ≠ 1 := by
  obtain ⟨a, haj, -⟩ := coord_exists_ne_ne hn j j
  obtain ⟨b, hbj, hba⟩ := coord_exists_ne_ne hn j a
  have hab : a ≠ b := fun h => hba h.symm
  refine ⟨permAut (Equiv.swap a b), ?_, ?_, permAut_swap_sq a b, ?_⟩
  · exact Subgroup.subset_closure (Or.inr ⟨a, b, hab, haj, hbj, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨a, b, hab, haj, hbj, rfl⟩)
  · intro h
    have hx := congrArg
      (fun g : MulAut (Fin n → Multiplicative (ZMod p)) =>
        g (Pi.mulSingle a (ofAdd 1))) h
    rw [permAut_mulSingle, Equiv.swap_apply_left, MulAut.one_apply] at hx
    have hx2 := congrArg (fun f : Fin n → Multiplicative (ZMod p) => toAdd (f a)) hx
    rw [toAdd_mulSingle, toAdd_mulSingle, if_pos rfl, if_neg hab] at hx2
    exact coord_zero_ne_one hp hx2

theorem exists_involution_mem_aPermutationFull_map_conj (hp : p.Prime) (hn : 2 ≤ n)
    (δ : MulAut (Fin n → Multiplicative (ZMod p))) :
    ∃ τ ∈ (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom, τ ^ 2 = 1 ∧ τ ≠ 1 := by
  rcases n with _ | _ | m
  · omega
  · omega
  · let a : Fin (m + 2) := ⟨0, by omega⟩
    let b : Fin (m + 2) := ⟨1, by omega⟩
    have hab : a ≠ b := by simp [a, b]
    have hg : (permAut (Equiv.swap a b) :
        MulAut (Fin (m + 2) → Multiplicative (ZMod p))) ^ 2 = 1 :=
      permAut_swap_sq a b
    have hgne : permAut (Equiv.swap a b) ≠
        (1 : MulAut (Fin (m + 2) → Multiplicative (ZMod p))) := by
      intro h1
      have hx := congrArg
        (fun g : MulAut (Fin (m + 2) → Multiplicative (ZMod p)) =>
          g (Pi.mulSingle a (ofAdd 1))) h1
      rw [permAut_mulSingle, Equiv.swap_apply_left, MulAut.one_apply] at hx
      have hx2 := congrArg
        (fun f : Fin (m + 2) → Multiplicative (ZMod p) => toAdd (f a)) hx
      rw [toAdd_mulSingle, toAdd_mulSingle, if_pos rfl, if_neg hab] at hx2
      exact coord_zero_ne_one hp hx2
    refine ⟨δ * permAut (Equiv.swap a b) * δ⁻¹, ?_, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨permAut (Equiv.swap a b),
        Subgroup.subset_closure ⟨a, b, hab, rfl⟩, rfl⟩
    · calc (δ * permAut (Equiv.swap a b) * δ⁻¹) ^ 2
          = (MulAut.conj δ (permAut (Equiv.swap a b))) ^ 2 := rfl
        _ = MulAut.conj δ ((permAut (Equiv.swap a b)) ^ 2) := by rw [map_pow]
        _ = 1 := by rw [hg, map_one]
    · intro h1
      have hconj : MulAut.conj δ (permAut (Equiv.swap a b)) = 1 := h1
      have h2 : permAut (p := p) (Equiv.swap a b) = 1 := by
        simpa using (MulAut.conj δ).injective (by simpa using hconj)
      exact hgne h2

theorem sgnAut_not_mem_bCoordinateBlock (hp : p.Prime) (hp2 : p ≠ 2) (j : Fin n) :
    sgnAut j ∉ bCoordinateBlock n p j := by
  intro h
  let x : Fin n → Multiplicative (ZMod p) := Pi.mulSingle j (ofAdd 1)
  have haxis : ∀ k, k ≠ j → x k = 1 := by
    intro k hk
    have hx : x = (Pi.mulSingle j (ofAdd (1 : ZMod p)) :
        Fin n → Multiplicative (ZMod p)) := rfl
    rw [hx, Pi.mulSingle_eq_of_ne hk]
  have hfix : sgnAut j x = x :=
    (forall_bCoordinateBlock_fix_iff hp hp2 j x).mpr haxis (sgnAut j) h
  have hcoord : x j = (x j)⁻¹ := by
    have h := congrArg (fun g : Fin n → Multiplicative (ZMod p) => g j) hfix
    rw [sgnAut_apply, Function.update_self] at h
    exact h.symm
  have hz : toAdd (x j) = 0 := coord_eq_zero_of_eq_neg hp hp2 (congrArg toAdd hcoord)
  have hxj : x j = 1 := toAdd.injective (by simpa using hz)
  have hxj1 : x j = ofAdd (1 : ZMod p) := by
    simp [x]
  have h10 : (1 : ZMod p) = 0 := by
    have h := congrArg (fun z : Multiplicative (ZMod p) => toAdd z) (hxj1.symm.trans hxj)
    simpa using h
  exact coord_zero_ne_one hp h10.symm

end CFSG.StandardType

end
