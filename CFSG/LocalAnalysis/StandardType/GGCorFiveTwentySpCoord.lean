module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSp

public section

namespace CFSG.StandardType

namespace SpCoord

open Multiplicative

variable {p k : ℕ}

@[expose] def sgnAut (i : Fin k) : MulAut (Fin k → Multiplicative (ZMod p)) where
  toFun f := Function.update f i (f i)⁻¹
  invFun f := Function.update f i (f i)⁻¹
  left_inv f := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  right_inv f := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  map_mul' f g := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [mul_comm]
    · simp [Function.update_of_ne hj]

theorem sgnAut_apply (i : Fin k) (f : Fin k → Multiplicative (ZMod p)) :
    sgnAut i f = Function.update f i (f i)⁻¹ :=
  rfl

@[expose] def permAut (σ : Equiv.Perm (Fin k)) : MulAut (Fin k → Multiplicative (ZMod p)) where
  toFun f := f ∘ ⇑σ⁻¹
  invFun f := f ∘ ⇑σ
  left_inv f := by
    funext j
    simp
  right_inv f := by
    funext j
    simp
  map_mul' _ _ := rfl

theorem permAut_apply (σ : Equiv.Perm (Fin k)) (f : Fin k → Multiplicative (ZMod p)) :
    permAut σ f = f ∘ ⇑σ⁻¹ :=
  rfl

theorem permAut_inv_apply (σ : Equiv.Perm (Fin k)) (f : Fin k → Multiplicative (ZMod p)) :
    (permAut σ)⁻¹ f = f ∘ ⇑σ :=
  rfl

@[expose] def diagAut (ε : Fin k → ZMod p) (hε : ∀ i, ε i * ε i = 1) :
    MulAut (Fin k → Multiplicative (ZMod p)) where
  toFun f i := ofAdd (ε i * toAdd (f i))
  invFun f i := ofAdd (ε i * toAdd (f i))
  left_inv f := by
    funext i
    simp [← mul_assoc, hε i]
  right_inv f := by
    funext i
    simp [← mul_assoc, hε i]
  map_mul' f g := by
    funext i
    simp [mul_add]

theorem diagAut_apply (ε : Fin k → ZMod p) (hε : ∀ i, ε i * ε i = 1)
    (f : Fin k → Multiplicative (ZMod p)) (i : Fin k) :
    diagAut ε hε f i = ofAdd (ε i * toAdd (f i)) :=
  rfl

@[expose] def IsSignedPerm
    (u : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))) : Prop :=
  ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)

theorem eq_of_toAdd_eq {f g : Fin k → Multiplicative (ZMod p)}
    (h : ∀ i, toAdd (f i) = toAdd (g i)) : f = g :=
  funext fun i => toAdd.injective (h i)

theorem eq_of_toAdd_perm_eq (π : Equiv.Perm (Fin k)) {f g : Fin k → Multiplicative (ZMod p)}
    (h : ∀ i, toAdd (f (π i)) = toAdd (g (π i))) : f = g := by
  refine eq_of_toAdd_eq fun i => ?_
  have := h (π⁻¹ i)
  simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using this

theorem toAdd_mulSingle (i j : Fin k) (c : ZMod p) :
    toAdd ((Pi.mulSingle i (ofAdd c) : Fin k → Multiplicative (ZMod p)) j) =
      if j = i then c else 0 := by
  rw [Pi.mulSingle_apply]
  split_ifs <;> rfl

theorem coord_sign_mul_self {ε : ZMod p} (h : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases h with rfl | rfl <;> ring

theorem coord_zero_ne_one (hp : p.Prime) : (0 : ZMod p) ≠ 1 := by
  have := Fact.mk hp
  exact zero_ne_one

theorem coord_sign_ne_zero (hp : p.Prime) {ε : ZMod p} (h : ε = 1 ∨ ε = -1) : ε ≠ 0 := by
  have := Fact.mk hp
  rcases h with rfl | rfl
  · exact one_ne_zero
  · exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)

theorem coord_mul_eq_zero (hp : p.Prime) {a b : ZMod p} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have := Fact.mk hp
  exact mul_eq_zero.mp h

theorem coord_mul_ne_zero (hp : p.Prime) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  fun h => (coord_mul_eq_zero hp h).elim ha hb

theorem exists_natCast_mul_eq (hp : p.Prime) {a : ZMod p} (ha : a ≠ 0) (b : ZMod p) :
    ∃ n : ℕ, (n : ZMod p) * a = b := by
  have := Fact.mk hp
  refine ⟨(b * a⁻¹).val, ?_⟩
  rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha, mul_one]

theorem coord_two_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem coord_eq_zero_of_eq_neg (hp : p.Prime) (hp2 : p ≠ 2) {x : ZMod p} (h : x = -x) : x = 0 := by
  have := Fact.mk hp
  have h2 : (2 : ZMod p) * x = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (coord_two_ne_zero hp hp2)

theorem mulSingle_ofAdd_eq_iff {a b : Fin k} {x y : ZMod p} (hx : x ≠ 0) :
    (Pi.mulSingle a (ofAdd x) : Fin k → Multiplicative (ZMod p)) = Pi.mulSingle b (ofAdd y) →
      a = b ∧ x = y := by
  intro h
  have h1 := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f a)) h
  simp only [toAdd_mulSingle] at h1
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte] at h1
    exact ⟨rfl, h1⟩
  · simp only [↓reduceIte, hab] at h1
    exact absurd h1 hx

theorem mulSingle_ofAdd_pow (i : Fin k) (c : ZMod p) (n : ℕ) :
    (Pi.mulSingle i (ofAdd c) : Fin k → Multiplicative (ZMod p)) ^ n =
      Pi.mulSingle i (ofAdd ((n : ZMod p) * c)) := by
  rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul]

theorem mulSingle_ofAdd_eq_pow [NeZero p] (i : Fin k) (c : ZMod p) :
    (Pi.mulSingle i (ofAdd c) : Fin k → Multiplicative (ZMod p)) =
      Pi.mulSingle i (ofAdd 1) ^ c.val := by
  rw [mulSingle_ofAdd_pow, ZMod.natCast_zmod_val, mul_one]

theorem hom_ext_mulSingle [NeZero p] {M : Type*} [Monoid M]
    {F₁ F₂ : (Fin k → Multiplicative (ZMod p)) →* M}
    (h : ∀ i, F₁ (Pi.mulSingle i (ofAdd 1)) = F₂ (Pi.mulSingle i (ofAdd 1))) : F₁ = F₂ := by
  refine MonoidHom.pi_ext fun i x => ?_
  rw [← ofAdd_toAdd x, mulSingle_ofAdd_eq_pow, map_pow, map_pow, h i]

theorem isSignedPerm_sgnAut (i : Fin k) :
    IsSignedPerm (⇑(sgnAut i : MulAut (Fin k → Multiplicative (ZMod p)))) := by
  refine ⟨1, fun j => if j = i then -1 else 1, fun j => ?_, fun f j => ?_⟩
  · by_cases hj : j = i
    · exact Or.inr (ite_eq_left hj)
    · exact Or.inl (ite_eq_right hj)
  · rw [Equiv.Perm.one_apply, sgnAut_apply]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

theorem isSignedPerm_permAut (σ : Equiv.Perm (Fin k)) :
    IsSignedPerm (⇑(permAut σ : MulAut (Fin k → Multiplicative (ZMod p)))) :=
  ⟨σ, 1, fun _ => Or.inl rfl, fun f i => by simp [permAut_apply]⟩

theorem isSignedPerm_permAut_mul_diagAut (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    IsSignedPerm (⇑(permAut π * diagAut ε fun i => coord_sign_mul_self (hε i) :
      MulAut (Fin k → Multiplicative (ZMod p)))) :=
  ⟨π, ε, hε, fun f i => by
    rw [MulAut.mul_apply, permAut_apply, Function.comp_apply]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    rw [diagAut_apply, toAdd_ofAdd]⟩

theorem IsSignedPerm.apply_mulSingle {u : MulAut (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (i : Fin k) (c : ZMod p) :
    u (Pi.mulSingle i (ofAdd c)) = Pi.mulSingle (π i) (ofAdd (ε i * c)) := by
  refine eq_of_toAdd_perm_eq π fun j => ?_
  rw [hu, toAdd_mulSingle, toAdd_mulSingle]
  by_cases hj : j = i
  · subst hj
    simp
  · rw [ite_eq_right hj, ite_eq_right (fun h => hj (π.injective h)), mul_zero]

theorem permAut_mulSingle (σ : Equiv.Perm (Fin k)) (i : Fin k) (c : Multiplicative (ZMod p)) :
    permAut σ (Pi.mulSingle i c) = Pi.mulSingle (σ i) c := by
  rw [permAut_apply]
  funext j
  simp only [Function.comp_apply, Pi.mulSingle_apply]
  by_cases hj : j = σ i
  · subst hj
    simp
  · rw [ite_eq_right hj, ite_eq_right]
    intro h
    exact hj (by rw [← h]; simp)

theorem permAut_inv_mulSingle (σ : Equiv.Perm (Fin k)) (i : Fin k)
    (c : Multiplicative (ZMod p)) :
    (permAut σ)⁻¹ (Pi.mulSingle i c) = Pi.mulSingle (σ⁻¹ i) c := by
  rw [permAut_inv_apply]
  funext j
  simp only [Function.comp_apply, Pi.mulSingle_apply]
  by_cases hj : j = σ⁻¹ i
  · subst hj
    simp
  · rw [ite_eq_right hj, ite_eq_right]
    intro h
    exact hj (by rw [← h]; simp)

theorem IsSignedPerm.mul_sgnAut {u : MulAut (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (i : Fin k) :
    u * sgnAut i = sgnAut (π i) * u := by
  refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun j => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, hu, sgnAut_apply, sgnAut_apply]
  by_cases hj : j = i
  · subst hj
    simp [hu]
  · rw [Function.update_of_ne hj, Function.update_of_ne (fun h => hj (π.injective h)), hu]

theorem sgnAut_mul_comm (i j : Fin k) :
    (sgnAut i : MulAut (Fin k → Multiplicative (ZMod p))) * sgnAut j = sgnAut j * sgnAut i := by
  refine MulEquiv.ext fun f => funext fun l => ?_
  simp only [MulAut.mul_apply, sgnAut_apply, Function.update_apply]
  by_cases hli : l = i <;> by_cases hlj : l = j <;> by_cases hij : i = j <;>
    simp_all

theorem toAdd_mul_apply (f g : Fin k → Multiplicative (ZMod p)) (j : Fin k) :
    toAdd ((f * g) j) = toAdd (f j) + toAdd (g j) :=
  toAdd_mul _ _

theorem toAdd_inv_apply (f : Fin k → Multiplicative (ZMod p)) (j : Fin k) :
    toAdd (f⁻¹ j) = -toAdd (f j) :=
  toAdd_inv _

theorem toAdd_pow_apply (f : Fin k → Multiplicative (ZMod p)) (n : ℕ) (j : Fin k) :
    toAdd ((f ^ n) j) = (n : ZMod p) * toAdd (f j) := by
  rw [Pi.pow_apply, toAdd_pow, nsmul_eq_mul]

theorem mem_of_diag {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hs : ∀ i, sgnAut i ∈ H) (S : Finset (Fin k)) :
    ∀ (u : MulAut (Fin k → Multiplicative (ZMod p))) (ε : Fin k → ZMod p),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ i, i ∉ S → ε i = 1) →
      (∀ f i, toAdd (u f i) = ε i * toAdd (f i)) → u ∈ H := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro u ε _ hS hu
    have h1 : u = 1 := by
      refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
      rw [hu, hS i (Finset.notMem_empty i), one_mul]
      rfl
    rw [h1]
    exact H.one_mem
  | insert a S ha ih =>
    intro u ε hε hS hu
    rcases hε a with hεa | hεa
    · refine ih u ε hε (fun i hi => ?_) hu
      by_cases hia : i = a
      · rw [hia, hεa]
      · exact hS i (by simp [hia, hi])
    · have h1 : u * sgnAut a ∈ H := by
        refine ih _ (Function.update ε a 1) (fun i => ?_) (fun i hi => ?_) (fun f i => ?_)
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
      have h2 := H.mul_mem h1 (H.inv_mem (hs a))
      rwa [mul_inv_cancel_right] at h2

theorem mem_of_isSignedPerm {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hs : ∀ i, sgnAut i ∈ H) (ht : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H)
    {u : MulAut (Fin k → Multiplicative (ZMod p))} (hu : IsSignedPerm u) : u ∈ H := by
  classical
  obtain ⟨π, ε, hε, hu⟩ := hu
  have key : ∀ (π : Equiv.Perm (Fin k)) (u : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) → u ∈ H := by
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one =>
      intro u hu
      exact mem_of_diag hs Finset.univ u ε hε (fun i hi => absurd (Finset.mem_univ i) hi)
        fun f i => by simpa using hu f i
    | swap_mul π x y hxy ih =>
      intro u hu
      have h1 : (permAut (Equiv.swap x y))⁻¹ * u ∈ H := by
        refine ih _ fun f i => ?_
        rw [MulAut.mul_apply, permAut_inv_apply, Function.comp_apply, ← Equiv.Perm.mul_apply]
        exact hu f i
      have h2 := H.mul_mem (ht x y hxy) h1
      rwa [mul_inv_cancel_left] at h2
  exact key π u hu

theorem sgnAut_mulSingle_self (i : Fin k) (c : Multiplicative (ZMod p)) :
    sgnAut i (Pi.mulSingle i c) = (Pi.mulSingle i c)⁻¹ := by
  rw [sgnAut_apply]
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]

theorem sgnAut_sq (i : Fin k) : (sgnAut i : MulAut (Fin k → Multiplicative (ZMod p))) ^ 2 = 1 := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [sq, MulAut.mul_apply, sgnAut_apply, sgnAut_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

theorem permAut_swap_sq (a b : Fin k) :
    (permAut (Equiv.swap a b) : MulAut (Fin k → Multiplicative (ZMod p))) ^ 2 = 1 := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [sq, MulAut.mul_apply, permAut_apply, permAut_apply]
  simp

theorem pow_sub_one_eq_one_of_sq {M : Type*} [Monoid M] (hp : p.Prime) (hp2 : p ≠ 2) {x : M}
    (hx : x ^ 2 = 1) : x ^ (p - 1) = 1 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  rw [show p - 1 = 2 * m by omega, pow_mul, hx, one_pow]

theorem card_fix_sgnAut (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin k) :
    Nat.card {f : Fin k → Multiplicative (ZMod p) // sgnAut i f = f} * p =
      Nat.card (Fin k → Multiplicative (ZMod p)) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  refine card_fix_mul_of_le_zpowers hp (fun a b => mul_comm a b) (sgnAut i)
    (a₁ := (Pi.mulSingle i (ofAdd 1) : Fin k → Multiplicative (ZMod p))) ?_
    (fun a : Fin k → Multiplicative (ZMod p) => ⟨(2 * toAdd (a i)).val, ?_⟩) ?_
  · rw [mulSingle_ofAdd_pow, ZMod.natCast_self, zero_mul, ofAdd_zero, Pi.mulSingle_one]
  · rw [sgnAut_apply, NbrSp.mul_inv_update_eq, mulSingle_ofAdd_pow, ZMod.natCast_zmod_val,
      mul_one]
    congr 1
    rw [← ofAdd_toAdd (a i ^ 2), toAdd_pow, nsmul_eq_mul]
    norm_num
  · rw [sgnAut_apply, NbrSp.mul_inv_update_eq, Pi.mulSingle_eq_same]
    intro h
    have h1 := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f i)) h
    simp only [Pi.mulSingle_eq_same, Pi.one_apply, toAdd_one, toAdd_pow, toAdd_ofAdd,
      nsmul_eq_mul, mul_one] at h1
    exact coord_two_ne_zero hp hp2 (by exact_mod_cast h1)

theorem card_fix_permAut_swap (hp : p.Prime) (hp2 : p ≠ 2) {a b : Fin k} (hab : a ≠ b) :
    Nat.card {f : Fin k → Multiplicative (ZMod p) // permAut (Equiv.swap a b) f = f} * p =
      Nat.card (Fin k → Multiplicative (ZMod p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine card_fix_mul_of_le_zpowers hp (fun x y => mul_comm x y) (permAut (Equiv.swap a b))
    (a₁ := (Pi.mulSingle a (ofAdd 1) * Pi.mulSingle b (ofAdd (-1)) :
      Fin k → Multiplicative (ZMod p))) ?_
    (fun f : Fin k → Multiplicative (ZMod p) => ⟨(toAdd (f a) - toAdd (f b)).val, ?_⟩) ?_
  · refine eq_of_toAdd_eq fun j => ?_
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.one_apply, toAdd_pow, toAdd_mul, toAdd_one,
      nsmul_eq_mul, toAdd_mulSingle, ZMod.natCast_self, zero_mul]
  · refine eq_of_toAdd_eq fun j => ?_
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, toAdd_pow, toAdd_mul, toAdd_inv,
      nsmul_eq_mul, toAdd_mulSingle, permAut_apply, Function.comp_apply, Equiv.swap_inv,
      ZMod.natCast_zmod_val]
    by_cases hja : j = a
    · subst hja
      simp only [↓reduceIte, hab, Equiv.swap_apply_left]
      ring
    · by_cases hjb : j = b
      · subst hjb
        simp only [hja, ↓reduceIte, Equiv.swap_apply_right]
        ring
      · simp [hja, hjb, Equiv.swap_apply_of_ne_of_ne hja hjb]
  · intro h
    have h1 := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f a)) h
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, toAdd_mul, toAdd_inv, toAdd_one,
      toAdd_mulSingle, permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_left, ↓reduceIte, hab, Ne.symm hab] at h1
    exact coord_two_ne_zero hp hp2 (by linear_combination h1)

theorem exists_pow_of_commute (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (F : (Fin k → Multiplicative (ZMod p)) →* (Fin k → Multiplicative (ZMod p)))
    (hs : ∀ i f, F (sgnAut i f) = sgnAut i (F f))
    (ht : ∀ (a b : Fin k) f, F (permAut (Equiv.swap a b) f) = permAut (Equiv.swap a b) (F f)) :
    ∃ c : ℕ, ∀ f, F f = f ^ c := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hline : ∀ i, F (Pi.mulSingle i (ofAdd 1)) =
      Pi.mulSingle i (F (Pi.mulSingle i (ofAdd 1)) i) := by
    intro i
    have h1 : sgnAut i (F (Pi.mulSingle i (ofAdd 1))) = (F (Pi.mulSingle i (ofAdd 1)))⁻¹ := by
      rw [← hs, sgnAut_mulSingle_self, map_inv]
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj]
      have h2 := congrFun h1 j
      rw [sgnAut_apply, Function.update_of_ne hj] at h2
      apply toAdd.injective
      rw [toAdd_one]
      refine coord_eq_zero_of_eq_neg hp hp2 ?_
      conv_lhs => rw [h2]
      exact toAdd_inv_apply _ _
  set i₀ : Fin k := ⟨0, hk⟩
  have hall : ∀ i, F (Pi.mulSingle i (ofAdd 1)) =
      Pi.mulSingle i (ofAdd (toAdd (F (Pi.mulSingle i₀ (ofAdd 1)) i₀))) := by
    intro i
    have h1 := ht i₀ i (Pi.mulSingle i₀ (ofAdd 1))
    rw [permAut_mulSingle, Equiv.swap_apply_left, hline i₀, permAut_mulSingle,
      Equiv.swap_apply_left] at h1
    rw [h1, ofAdd_toAdd]
  refine ⟨(toAdd (F (Pi.mulSingle i₀ (ofAdd 1)) i₀)).val, fun f => ?_⟩
  have h := hom_ext_mulSingle (F₁ := F)
    (F₂ := powMonoidHom (toAdd (F (Pi.mulSingle i₀ (ofAdd 1)) i₀)).val) fun i => by
      rw [powMonoidHom_apply, hall i, mulSingle_ofAdd_pow, ZMod.natCast_zmod_val, mul_one]
  exact DFunLike.congr_fun h f

theorem coord_exists_ne_ne (hk : 3 ≤ k) (a b : Fin k) : ∃ c : Fin k, c ≠ a ∧ c ≠ b := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ {a, b} := fun w _ => by
    by_cases h1 : w = a
    · simp [h1]
    · simp [h w h1]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({a, b} : Finset (Fin k)).card ≤ 2 := Finset.card_le_two
  omega

theorem diagAut_mulSingle (ε : Fin k → ZMod p) (hε : ∀ i, ε i * ε i = 1) (i : Fin k)
    (x : ZMod p) :
    diagAut ε hε (Pi.mulSingle i (ofAdd x)) = Pi.mulSingle i (ofAdd (ε i * x)) := by
  refine eq_of_toAdd_eq fun j => ?_
  rw [diagAut_apply, toAdd_ofAdd, toAdd_mulSingle, toAdd_mulSingle]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

theorem exists_mulSingle_of_normalizes (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k)
    {φ : MulAut (Fin k → Multiplicative (ZMod p))}
    (hφ : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      IsSignedPerm ⇑(φ * u * φ⁻¹))
    (hφ' : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      IsSignedPerm ⇑(φ⁻¹ * u * φ)) (i : Fin k) :
    ∃ (j : Fin k) (c : ZMod p), c ≠ 0 ∧
      φ (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle j (ofAdd c) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨π, ε, hε, hr⟩ := hφ _ (isSignedPerm_sgnAut i)
  set r := φ * sgnAut i * φ⁻¹ with hrdef
  set u := φ (Pi.mulSingle i (ofAdd 1)) with hu
  have hF1 : r u = u⁻¹ := by
    rw [hrdef, MulAut.mul_apply, MulAut.mul_apply, hu, MulAut.inv_apply_self,
      sgnAut_mulSingle_self, map_inv]
  have hF2 : ∀ g, ∃ e : ℕ, r g * g⁻¹ = u ^ e := by
    intro g
    obtain ⟨h, rfl⟩ := φ.surjective g
    refine ⟨(-(2 * toAdd (h i))).val, ?_⟩
    have h1 : sgnAut i h * h⁻¹ = Pi.mulSingle i (ofAdd 1) ^ (-(2 * toAdd (h i))).val := by
      rw [mulSingle_ofAdd_pow, ZMod.natCast_zmod_val, mul_one]
      refine eq_of_toAdd_eq fun j => ?_
      rw [toAdd_mul_apply, toAdd_inv_apply, sgnAut_apply, toAdd_mulSingle]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, toAdd_inv, ite_eq_left rfl]
        ring
      · rw [Function.update_of_ne hj, ite_eq_right hj, add_neg_cancel]
    rw [hrdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, ← map_inv, ← map_mul,
      h1, map_pow]
  have hu1 : u ≠ 1 := by
    rw [hu, Ne, ← map_one φ]
    intro h
    have h1 := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f i)) (φ.injective h)
    simp only [toAdd_mulSingle, ↓reduceIte, Pi.one_apply, toAdd_one] at h1
    exact coord_zero_ne_one hp h1.symm
  have hrδ : ∀ l j, toAdd ((r (Pi.mulSingle l (ofAdd 1)) * (Pi.mulSingle l (ofAdd 1))⁻¹ :
      Fin k → Multiplicative (ZMod p)) j) =
      (if j = π l then ε l else 0) - (if j = l then 1 else 0) := by
    intro l j
    rw [toAdd_mul_apply, toAdd_inv_apply, IsSignedPerm.apply_mulSingle hr, toAdd_mulSingle,
      toAdd_mulSingle, mul_one, sub_eq_add_neg]
  by_cases hπ : ∃ a, π a ≠ a
  ·
    exfalso
    obtain ⟨a, ha⟩ := hπ
    obtain ⟨c, hca, hcb⟩ := coord_exists_ne_ne hk a (π a)
    obtain ⟨e, he⟩ := hF2 (Pi.mulSingle a (ofAdd 1))
    have hea := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f a)) he
    have hec := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f c)) he
    rw [hrδ, toAdd_pow_apply, ite_eq_right (Ne.symm ha), ite_eq_left rfl, zero_sub] at hea
    rw [hrδ, toAdd_pow_apply, ite_eq_right hcb, ite_eq_right hca, sub_zero] at hec
    have he0 : (e : ZMod p) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, neg_eq_zero] at hea
      exact coord_zero_ne_one hp hea.symm
    have huc : toAdd (u c) = 0 :=
      ((coord_mul_eq_zero hp hec.symm).resolve_left he0)
    obtain ⟨e', he'⟩ := hF2 (Pi.mulSingle c (ofAdd 1))
    have hec' := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f c)) he'
    rw [hrδ, toAdd_pow_apply, huc, mul_zero, ite_eq_left rfl] at hec'
    have hπc : π c = c := by
      by_contra h
      rw [ite_eq_right (Ne.symm h), zero_sub, neg_eq_zero] at hec'
      exact coord_zero_ne_one hp hec'.symm
    rw [ite_eq_left hπc.symm, sub_eq_zero] at hec'
    have hrc : ∀ x : ZMod p, r (Pi.mulSingle c (ofAdd x)) = Pi.mulSingle c (ofAdd x) := by
      intro x
      rw [IsSignedPerm.apply_mulSingle hr, hπc, hec', one_mul]
    set w : MulAut (Fin k → Multiplicative (ZMod p)) := permAut (Equiv.swap (π a) c) with hw
    obtain ⟨π', ε', -, hw'⟩ := hφ' w (isSignedPerm_permAut _)
    have hcomm := IsSignedPerm.mul_sgnAut hw' i
    have hwr : w * r * w⁻¹ = φ * sgnAut (π' i) * φ⁻¹ := by
      have e1 : w * r * w⁻¹ = φ * ((φ⁻¹ * w * φ) * sgnAut i) * (φ⁻¹ * w * φ)⁻¹ * φ⁻¹ := by
        rw [hrdef]
        group
      rw [e1, hcomm]
      group
    have hF3 : r * (w * r * w⁻¹) = (w * r * w⁻¹) * r := by
      rw [hwr, hrdef]
      calc φ * sgnAut i * φ⁻¹ * (φ * sgnAut (π' i) * φ⁻¹) =
            φ * (sgnAut i * sgnAut (π' i)) * φ⁻¹ := by group
        _ = φ * (sgnAut (π' i) * sgnAut i) * φ⁻¹ := by rw [sgnAut_mul_comm]
        _ = φ * sgnAut (π' i) * φ⁻¹ * (φ * sgnAut i * φ⁻¹) := by group
    have hεa : ε a ≠ 0 := coord_sign_ne_zero hp (hε a)
    have hwa : w⁻¹ (Pi.mulSingle a (ofAdd 1)) = Pi.mulSingle a (ofAdd 1) := by
      rw [hw, permAut_inv_mulSingle, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne ha.symm hca.symm]
    have hra : r (Pi.mulSingle a (ofAdd 1)) = Pi.mulSingle (π a) (ofAdd (ε a)) := by
      rw [IsSignedPerm.apply_mulSingle hr, mul_one]
    have hwb : ∀ x, w (Pi.mulSingle (π a) x) = Pi.mulSingle c x := fun x => by
      rw [hw, permAut_mulSingle, Equiv.swap_apply_left]
    have hwc : ∀ x, w (Pi.mulSingle c x) = Pi.mulSingle (π a) x := fun x => by
      rw [hw, permAut_mulSingle, Equiv.swap_apply_right]
    have hwb' : ∀ x, w⁻¹ (Pi.mulSingle (π a) x) = Pi.mulSingle c x := fun x => by
      rw [hw, permAut_inv_mulSingle, Equiv.swap_inv, Equiv.swap_apply_left]
    have h1 := congrArg (fun g : MulAut (Fin k → Multiplicative (ZMod p)) =>
      g (Pi.mulSingle a (ofAdd 1))) hF3
    simp only [MulAut.mul_apply] at h1
    rw [hwa, hra, hwb, hrc, hwb', hrc, hwc] at h1
    exact hcb (mulSingle_ofAdd_eq_iff hεa h1).1
  ·
    push Not at hπ
    have hdiag : ∀ f l, toAdd (r f l) = ε l * toAdd (f l) := fun f l => by
      have := hr f l
      rwa [hπ l] at this
    have hsupp : ∀ l, toAdd (u l) ≠ 0 → ε l = -1 := by
      intro l hl
      have h1 := hdiag u l
      rw [hF1, toAdd_inv_apply] at h1
      rcases hε l with h | h
      · rw [h, one_mul] at h1
        exact absurd (coord_eq_zero_of_eq_neg hp hp2 h1.symm) hl
      · exact h
    obtain ⟨l₀, hl₀⟩ : ∃ l₀, toAdd (u l₀) ≠ 0 := by
      by_contra h
      push Not at h
      exact hu1 (funext fun l => toAdd.injective (by rw [h l, Pi.one_apply, toAdd_one]))
    refine ⟨l₀, toAdd (u l₀), hl₀, eq_of_toAdd_eq fun l => ?_⟩
    rw [toAdd_mulSingle]
    by_cases hl : l = l₀
    · rw [hl, ite_eq_left rfl]
    · rw [ite_eq_right hl]
      by_contra hul
      obtain ⟨e, he⟩ := hF2 (Pi.mulSingle l₀ (ofAdd 1))
      have hel₀ := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f l₀)) he
      have hel := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f l)) he
      rw [hrδ, toAdd_pow_apply, hπ, ite_eq_left rfl, ite_eq_left rfl, hsupp l₀ hl₀] at hel₀
      rw [hrδ, toAdd_pow_apply, hπ, ite_eq_right hl, ite_eq_right hl, sub_zero] at hel
      have he0 : (e : ZMod p) = 0 := (coord_mul_eq_zero hp hel.symm).resolve_right hul
      rw [he0, zero_mul] at hel₀
      exact coord_two_ne_zero hp hp2 (by linear_combination -hel₀)

theorem exists_isSignedPerm_pow (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k)
    {φ : MulAut (Fin k → Multiplicative (ZMod p))}
    (hφ : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      IsSignedPerm ⇑(φ * u * φ⁻¹))
    (hφ' : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      IsSignedPerm ⇑(φ⁻¹ * u * φ)) :
    ∃ w : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑w ∧
      ∃ c : ℕ, ∀ f, φ f = (w f) ^ c := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  choose j c hc hjc using exists_mulSingle_of_normalizes hp hp2 hk hφ hφ'
  have hjinj : Function.Injective j := by
    intro i i' hii'
    by_contra hne
    obtain ⟨n, hn⟩ := exists_natCast_mul_eq hp (hc i) (c i')
    have h1 : φ (Pi.mulSingle i (ofAdd 1) ^ n) = φ (Pi.mulSingle i' (ofAdd 1)) := by
      rw [map_pow, hjc, hjc, mulSingle_ofAdd_pow, hn, hii']
    have h2 := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f i'))
      (φ.injective h1)
    simp only [mulSingle_ofAdd_pow, toAdd_mulSingle, ↓reduceIte, Ne.symm hne] at h2
    exact coord_zero_ne_one hp h2
  set J : Equiv.Perm (Fin k) := Equiv.ofBijective j hjinj.bijective_of_finite with hJ
  have hpm : ∀ i i', c i' = c i ∨ c i' = -c i := by
    intro i i'
    by_cases hii : i = i'
    · subst hii
      exact Or.inl rfl
    obtain ⟨π, ε, hε, hq⟩ := hφ _ (isSignedPerm_permAut (Equiv.swap i i'))
    have h1 : (φ * permAut (Equiv.swap i i') * φ⁻¹ : MulAut (Fin k → Multiplicative (ZMod p)))
        (φ (Pi.mulSingle i (ofAdd 1))) = φ (Pi.mulSingle i' (ofAdd 1)) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, permAut_mulSingle,
        Equiv.swap_apply_left]
    rw [hjc, hjc, IsSignedPerm.apply_mulSingle hq] at h1
    have h2 := (mulSingle_ofAdd_eq_iff
      (coord_mul_ne_zero hp (coord_sign_ne_zero hp (hε _)) (hc i)) h1).2
    rcases hε (j i) with h | h <;> rw [h] at h2
    · exact Or.inl (by rw [← h2, one_mul])
    · exact Or.inr (by rw [← h2, neg_one_mul])
  set i₀ : Fin k := ⟨0, by omega⟩
  set ε : Fin k → ZMod p := fun i => if c i = c i₀ then 1 else -1 with hεdef
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by
    by_cases h : c i = c i₀
    · exact Or.inl (by rw [hεdef]; exact ite_eq_left h)
    · exact Or.inr (by rw [hεdef]; exact ite_eq_right h)
  have hεc : ∀ i, c i₀ * ε i = c i := by
    intro i
    by_cases h : c i = c i₀
    · rw [hεdef]
      simp only [h, ↓reduceIte, mul_one]
    · rw [hεdef]
      simp only [h, ↓reduceIte, mul_neg, mul_one]
      exact ((hpm i₀ i).resolve_left h).symm
  refine ⟨permAut J * diagAut ε (fun i => coord_sign_mul_self (hε i)),
    isSignedPerm_permAut_mul_diagAut J ε hε, (c i₀).val, fun f => ?_⟩
  have h := hom_ext_mulSingle (F₁ := φ.toMonoidHom)
    (F₂ := (powMonoidHom (c i₀).val).comp
      (permAut J * diagAut ε (fun i => coord_sign_mul_self (hε i))).toMonoidHom) fun i => by
      rw [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, powMonoidHom_apply, MulAut.mul_apply, diagAut_mulSingle,
        permAut_mulSingle, mulSingle_ofAdd_pow, ZMod.natCast_zmod_val, mul_one, hεc, hjc]
      rfl
  exact DFunLike.congr_fun h f

theorem sgnAut_mulSingle_of_ne {i j : Fin k} (hji : j ≠ i) (c : Multiplicative (ZMod p)) :
    sgnAut i (Pi.mulSingle j c) = Pi.mulSingle j c := by
  rw [sgnAut_apply, Pi.mulSingle_eq_of_ne (Ne.symm hji), inv_one]
  funext l
  by_cases hl : l = i
  · subst hl
    rw [Function.update_self, Pi.mulSingle_eq_of_ne (Ne.symm hji)]
  · rw [Function.update_of_ne hl]

end SpCoord

end CFSG.StandardType

end
