module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.YamakiRec

private abbrev Vec7 : Type := Multiplicative (Fin 7 → ZMod 2)

private def betaHom {H : Type*} [CommGroup H] (hsq : ∀ x : H, x * x = 1) (c : Fin 7 → H) :
    Vec7 →* H where
  toFun v := ∏ i, c i ^ (Multiplicative.toAdd v i).val
  map_one' := by simp
  map_mul' v w := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h2 : c i ^ 2 = 1 := by rw [pow_two]; exact hsq _
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ h2, pow_add]

private theorem betaHom_apply {H : Type*} [CommGroup H] (hsq : ∀ x : H, x * x = 1)
    (c : Fin 7 → H) (v : Vec7) :
    betaHom hsq c v = ∏ i, c i ^ (Multiplicative.toAdd v i).val := rfl

private theorem zmod_two_val_one : (1 : ZMod 2).val = 1 := rfl

private theorem betaHom_single {H : Type*} [CommGroup H] (hsq : ∀ x : H, x * x = 1)
    (c : Fin 7 → H) (i : Fin 7) :
    betaHom hsq c (Multiplicative.ofAdd (Pi.single i 1)) = c i := by
  rw [betaHom_apply, Finset.prod_eq_single i]
  · simp [zmod_two_val_one]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private def ones : Vec7 := Multiplicative.ofAdd fun _ => 1

private theorem betaHom_ones {H : Type*} [CommGroup H] (hsq : ∀ x : H, x * x = 1)
    (c : Fin 7 → H) (hprod : ∏ i, c i = 1) : betaHom hsq c ones = 1 := by
  rw [betaHom_apply]
  simpa [ones, zmod_two_val_one] using hprod

private def permHom (σ : Equiv.Perm (Fin 7)) : Vec7 →* Vec7 where
  toFun v := Multiplicative.ofAdd fun j => Multiplicative.toAdd v (σ.symm j)
  map_one' := rfl
  map_mul' _ _ := rfl

private def wt : Vec7 →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd (∑ i, Multiplicative.toAdd v i)
  map_one' := by simp
  map_mul' v w := by simp [Finset.sum_add_distrib]

private theorem wt_apply (v : Vec7) :
    wt v = Multiplicative.ofAdd (∑ i, Multiplicative.toAdd v i) := rfl

private theorem mem_wt_ker (v : Vec7) : v ∈ wt.ker ↔ ∑ i, Multiplicative.toAdd v i = 0 := by
  rw [MonoidHom.mem_ker, wt_apply, ofAdd_eq_one]

private theorem ones_not_mem_wt_ker : ones ∉ wt.ker := by
  rw [mem_wt_ker]
  decide

private theorem ones_ne_one : ones ≠ 1 := fun h => ones_not_mem_wt_ker (h ▸ one_mem _)

private theorem mul_ones_mem_wt_ker {v : Vec7} (hv : v ∉ wt.ker) : v * ones ∈ wt.ker := by
  rw [mem_wt_ker] at hv ⊢
  have h7 : ∑ _i : Fin 7, (1 : ZMod 2) = 1 := by decide
  simp only [ones, toAdd_mul, toAdd_ofAdd, Pi.add_apply, Finset.sum_add_distrib, h7]
  generalize ∑ i, Multiplicative.toAdd v i = s at hv ⊢
  revert s
  decide

private theorem card_vec7 : Nat.card Vec7 = 128 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
  simp

private theorem exists_vec_aux {H : Type*} [CommGroup H] (hsq : ∀ x : H, x * x = 1)
    (hcard : Nat.card H = 64) (c : Fin 7 → H) (hprod : ∏ i, c i = 1)
    (hcl : Subgroup.closure (Set.range c) = ⊤) :
    ∃ vec : H →* Vec7, Function.Injective vec ∧
      (∀ x, ∑ i, Multiplicative.toAdd (vec x) i = 0) ∧
      (∀ i, Multiplicative.toAdd (vec (c i)) = fun j => if j = i then 0 else 1) ∧
      ∀ (f : H →* H) (σ : Equiv.Perm (Fin 7)), (∀ i, f (c i) = c (σ i)) →
        ∀ x, Multiplicative.toAdd (vec (f x)) =
          fun j => Multiplicative.toAdd (vec x) (σ.symm j) := by
  obtain ⟨β, hβ1, hβones⟩ : ∃ β : Vec7 →* H,
      (∀ i, β (Multiplicative.ofAdd (Pi.single i 1)) = c i) ∧ β ones = 1 :=
    ⟨betaHom hsq c, betaHom_single hsq c, betaHom_ones hsq c hprod⟩
  have hsurj : Function.Surjective β := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨_, hβ1 i⟩
  have hker : Nat.card β.ker = 2 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hsurj
    rw [hcard, card_vec7] at h
    omega
  have hinj : Function.Injective (β.comp wt.ker.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hne
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : β.ker)).1 hker
    have e1 : (⟨x, hx⟩ : β.ker) = y := huniq _ fun h => by
      have h' : (x : Vec7) = 1 := congrArg Subtype.val h
      exact hne (Subtype.ext h')
    have e2 : (⟨ones, hβones⟩ : β.ker) = y :=
      huniq _ fun h => ones_ne_one (congrArg Subtype.val h)
    have e3 : ones = (x : Vec7) := congrArg Subtype.val (e2.trans e1.symm)
    exact ones_not_mem_wt_ker (e3 ▸ x.2)
  have hsurj' : Function.Surjective (β.comp wt.ker.subtype) := by
    intro h
    obtain ⟨v, rfl⟩ := hsurj h
    by_cases hv : v ∈ wt.ker
    · exact ⟨⟨v, hv⟩, rfl⟩
    · refine ⟨⟨v * ones, mul_ones_mem_wt_ker hv⟩, ?_⟩
      show β (v * ones) = β v
      rw [map_mul, hβones, mul_one]
  obtain ⟨vec, hvecmem, hvec⟩ : ∃ vec : H →* Vec7, (∀ x, vec x ∈ wt.ker) ∧ ∀ x, β (vec x) = x := by
    let e : wt.ker ≃* H := MulEquiv.ofBijective _ ⟨hinj, hsurj'⟩
    refine ⟨wt.ker.subtype.comp e.symm.toMonoidHom, fun x => (e.symm x).2, fun x => ?_⟩
    exact e.apply_symm_apply x
  have huniq : ∀ (x : H) (w : Vec7), w ∈ wt.ker → β w = x → vec x = w := by
    intro x w hw hβw
    have := @hinj ⟨vec x, hvecmem x⟩ ⟨w, hw⟩ (by
      show β (vec x) = β w
      rw [hvec, hβw])
    exact congrArg Subtype.val this
  have hvecc : ∀ i, Multiplicative.toAdd (vec (c i)) = fun j => if j = i then 0 else 1 := by
    intro i
    have hw : (Multiplicative.ofAdd fun j => if j = i then (0 : ZMod 2) else 1 : Vec7) =
        ones * Multiplicative.ofAdd (Pi.single i 1) := by
      apply Multiplicative.toAdd.injective
      funext j
      by_cases h : j = i
      · subst h
        simp only [ones, toAdd_mul, toAdd_ofAdd, Pi.add_apply, Pi.single_eq_same, if_true]
        decide
      · simp [ones, Pi.single_eq_of_ne h, h]
    have hmem : (Multiplicative.ofAdd fun j => if j = i then (0 : ZMod 2) else 1 : Vec7) ∈
        wt.ker := by
      rw [mem_wt_ker, toAdd_ofAdd]
      revert i
      decide
    have := huniq (c i) _ hmem (by rw [hw, map_mul, hβones, hβ1, one_mul])
    rw [this, toAdd_ofAdd]
  refine ⟨vec, ?_, fun x => (mem_wt_ker _).1 (hvecmem x), hvecc, ?_⟩
  · intro x y hxy
    rw [← hvec x, ← hvec y, hxy]
  · intro f σ hf x
    have key : vec.comp f = (permHom σ).comp vec := by
      refine MonoidHom.eq_of_eqOn_dense hcl ?_
      rintro _ ⟨i, rfl⟩
      show vec (f (c i)) = permHom σ (vec (c i))
      rw [hf i]
      apply Multiplicative.toAdd.injective
      show Multiplicative.toAdd (vec (c (σ i))) =
        fun j => Multiplicative.toAdd (vec (c i)) (σ.symm j)
      rw [hvecc, hvecc]
      funext j
      simp [Equiv.symm_apply_eq]
    exact congrArg (fun g : H →* Vec7 => Multiplicative.toAdd (g x)) key

theorem exists_vec {G : Type*} [Group G] {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1)
    (hcard : Nat.card A = 64) (b : Fin 7 → G) (hb : ∀ i, b i ∈ A)
    (hprod : (List.ofFn b).prod = 1) (hcl : Subgroup.closure (Set.range b) = A) :
    ∃ vec : ↥A →* Multiplicative (Fin 7 → ZMod 2), Function.Injective vec ∧
      (∀ x, ∑ i, Multiplicative.toAdd (vec x) i = 0) ∧
      (∀ i, Multiplicative.toAdd (vec ⟨b i, hb i⟩) = fun j => if j = i then 0 else 1) ∧
      ∀ (f : ↥A →* ↥A) (σ : Equiv.Perm (Fin 7)), (∀ i, f ⟨b i, hb i⟩ = ⟨b (σ i), hb (σ i)⟩) →
        ∀ x, Multiplicative.toAdd (vec (f x)) =
          fun j => Multiplicative.toAdd (vec x) (σ.symm j) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun x y => Subtype.ext (hcomm _ x.2 _ y.2) }
  have hprod' : ∏ i, (⟨b i, hb i⟩ : A) = 1 := by
    rw [← List.prod_ofFn]
    apply A.subtype_injective
    rw [map_list_prod, List.map_ofFn, map_one]
    exact hprod
  have hcl' : Subgroup.closure (Set.range fun i => (⟨b i, hb i⟩ : A)) = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top, Subgroup.range_subtype]
    exact hcl
  exact exists_vec_aux (fun x => Subtype.ext (hsq x x.2)) hcard (fun i => ⟨b i, hb i⟩) hprod' hcl'

end CFSG.RankThree.PartTwo.Sec19.SolEven.YamakiRec
