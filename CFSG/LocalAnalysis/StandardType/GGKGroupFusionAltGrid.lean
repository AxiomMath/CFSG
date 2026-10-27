module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltSat
public import Mathlib.GroupTheory.Perm.ViaEmbedding

public section

namespace CFSG.StandardType

open Equiv Equiv.Perm

section Powers

variable {V : Type}

theorem ggPow_eq_pow_mod {x : Perm V} {p : ℕ} (hxp : x ^ p = 1) (m : ℕ) :
    x ^ m = x ^ (m % p) := by
  conv_lhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, hxp, one_pow, one_mul]

theorem ggDvd_of_pow_apply_eq {p : ℕ} (hp : p.Prime) {x : Perm V} (hxp : x ^ p = 1) {b : V}
    (hb : x b ≠ b) {m : ℕ} (hm : (x ^ m) b = b) : p ∣ m := by
  by_contra hpm
  have hcop : Nat.Coprime m p := Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr hpm)
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hiter : ∀ k : ℕ, ((x ^ m) ^ k) b = b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Perm.coe_mul, Function.comp_apply, hm, ih]
  have h1 := hiter a
  rw [← pow_mul, ggPow_eq_pow_mod hxp, ha, pow_one] at h1
  exact hb h1

theorem ggSign_eq_one_of_pow_eq_one [DecidableEq V] [Fintype V] {p : ℕ} (hp : Odd p) {g : Perm V}
    (hg : g ^ p = 1) : Perm.sign g = 1 := by
  have h1 : Perm.sign g ^ p = 1 := by rw [← map_pow, hg, map_one]
  rwa [Int.units_pow_eq_pow_mod_two, Nat.odd_iff.mp hp, pow_one] at h1

end Powers

section Via

variable {V : Type} {α : Type} (ι : α ↪ V)

theorem ggVia_apply (π : Perm α) (a : α) : π.viaEmbedding ι (ι a) = ι (π a) :=
  Perm.viaEmbedding_apply π ι a

theorem ggVia_apply_of_notMem (π : Perm α) {z : V} (hz : z ∉ Set.range ι) :
    π.viaEmbedding ι z = z :=
  Perm.viaEmbedding_apply_of_notMem π ι z hz

theorem ggVia_mul (π π' : Perm α) :
    (π * π').viaEmbedding ι = π.viaEmbedding ι * π'.viaEmbedding ι :=
  map_mul (Perm.viaEmbeddingHom ι) π π'

theorem ggVia_inv (π : Perm α) : π⁻¹.viaEmbedding ι = (π.viaEmbedding ι)⁻¹ :=
  map_inv (Perm.viaEmbeddingHom ι) π

theorem ggVia_pow (π : Perm α) (n : ℕ) : (π ^ n).viaEmbedding ι = (π.viaEmbedding ι) ^ n :=
  map_pow (Perm.viaEmbeddingHom ι) π n

theorem ggSign_via [DecidableEq V] [Fintype V] [Fintype α] [DecidableEq α] (π : Perm α) :
    Perm.sign (π.viaEmbedding ι) = Perm.sign π := by
  unfold Perm.viaEmbedding
  rw [Perm.sign_extendDomain]

theorem ggVia_commute {y : Perm V} {S π : Perm α} (hy : ∀ a, y (ι a) = ι (S a))
    (hy' : ∀ z, z ∉ Set.range ι → y z ∉ Set.range ι) (hπS : π * S = S * π) :
    π.viaEmbedding ι * y = y * π.viaEmbedding ι := by
  ext z
  simp only [Perm.coe_mul, Function.comp_apply]
  by_cases hz : z ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hz
    rw [hy, ggVia_apply, ggVia_apply, hy]
    exact congrArg ι (congrArg (fun f : Perm α => f a) hπS)
  · rw [ggVia_apply_of_notMem ι π (hy' z hz), ggVia_apply_of_notMem ι π hz]

theorem ggNotMem_range_of_apply {y : Perm V} {S : Perm α} (hy : ∀ a, y (ι a) = ι (S a))
    {z : V} (hz : z ∉ Set.range ι) : y z ∉ Set.range ι := by
  rintro ⟨a, ha⟩
  apply hz
  refine ⟨S⁻¹ a, y.injective ?_⟩
  rw [hy, ← ha]
  simp

end Via

section GridPerms

variable (p : ℕ)

@[expose] def ggGridR : Perm (ZMod p × ZMod p) where
  toFun a := (a.1, a.2 + 1)
  invFun a := (a.1, a.2 - 1)
  left_inv a := by simp
  right_inv a := by simp

@[expose] def ggGridS : Perm (ZMod p × ZMod p) where
  toFun a := (a.1 + 1, a.2)
  invFun a := (a.1 - 1, a.2)
  left_inv a := by simp
  right_inv a := by simp

@[expose] def ggGridT : Perm (ZMod p × ZMod p) := Equiv.prodComm (ZMod p) (ZMod p)

@[expose] def ggGridRow (i : ZMod p) : Perm (ZMod p × ZMod p) where
  toFun a := (a.1, if a.1 = i then a.2 + 1 else a.2)
  invFun a := (a.1, if a.1 = i then a.2 - 1 else a.2)
  left_inv a := by rcases a with ⟨a1, a2⟩; by_cases h : a1 = i <;> simp [h]
  right_inv a := by rcases a with ⟨a1, a2⟩; by_cases h : a1 = i <;> simp [h]

@[expose] def ggGridCol (j : ZMod p) : Perm (ZMod p × ZMod p) where
  toFun a := (if a.2 = j then a.1 + 1 else a.1, a.2)
  invFun a := (if a.2 = j then a.1 - 1 else a.1, a.2)
  left_inv a := by rcases a with ⟨a1, a2⟩; by_cases h : a2 = j <;> simp [h]
  right_inv a := by rcases a with ⟨a1, a2⟩; by_cases h : a2 = j <;> simp [h]

@[expose] def ggGridSwap : Perm (ZMod p × ZMod p) :=
  Equiv.prodCongrLeft fun _ => Equiv.swap (0 : ZMod p) 1

@[simp] theorem ggGridR_apply (a : ZMod p × ZMod p) : ggGridR p a = (a.1, a.2 + 1) := rfl

@[simp] theorem ggGridS_apply (a : ZMod p × ZMod p) : ggGridS p a = (a.1 + 1, a.2) := rfl

@[simp] theorem ggGridT_apply (a : ZMod p × ZMod p) : ggGridT p a = (a.2, a.1) := rfl

@[simp] theorem ggGridRow_apply (i : ZMod p) (a : ZMod p × ZMod p) :
    ggGridRow p i a = (a.1, if a.1 = i then a.2 + 1 else a.2) := rfl

@[simp] theorem ggGridCol_apply (j : ZMod p) (a : ZMod p × ZMod p) :
    ggGridCol p j a = (if a.2 = j then a.1 + 1 else a.1, a.2) := rfl

@[simp] theorem ggGridSwap_apply (a : ZMod p × ZMod p) :
    ggGridSwap p a = (Equiv.swap (0 : ZMod p) 1 a.1, a.2) := rfl

theorem ggGridT_conj : ggGridT p * ggGridR p * (ggGridT p)⁻¹ = ggGridS p := by
  ext ⟨i, j⟩ <;> simp [ggGridT, Perm.inv_def]

theorem ggGridSwap_comm : ggGridSwap p * ggGridR p = ggGridR p * ggGridSwap p := by
  ext ⟨i, j⟩ <;> simp

theorem ggGridS_comm : ggGridS p * ggGridR p = ggGridR p * ggGridS p := by
  ext ⟨i, j⟩ <;> simp

theorem ggGridRow_comm (i : ZMod p) : ggGridRow p i * ggGridR p = ggGridR p * ggGridRow p i := by
  ext ⟨i', j⟩
  · simp
  · by_cases h : i' = i <;> simp [h]

theorem ggGridCol_comm (j : ZMod p) : ggGridCol p j * ggGridS p = ggGridS p * ggGridCol p j := by
  ext ⟨i, j'⟩
  · by_cases h : j' = j <;> simp [h]
  · simp

theorem ggGridRow_pow_apply (i : ZMod p) (n : ℕ) (a : ZMod p × ZMod p) :
    (ggGridRow p i ^ n) a = (a.1, if a.1 = i then a.2 + n else a.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.coe_mul, Function.comp_apply, ih]
    by_cases h : a.1 = i <;> simp [h, add_assoc]

theorem ggGridCol_pow_apply (j : ZMod p) (n : ℕ) (a : ZMod p × ZMod p) :
    (ggGridCol p j ^ n) a = (if a.2 = j then a.1 + n else a.1, a.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.coe_mul, Function.comp_apply, ih]
    by_cases h : a.2 = j <;> simp [h, add_assoc]

theorem ggGridRow_pow (i : ZMod p) : ggGridRow p i ^ p = 1 := by
  ext a <;> simp [ggGridRow_pow_apply]

theorem ggGridCol_pow (j : ZMod p) : ggGridCol p j ^ p = 1 := by
  ext a <;> simp [ggGridCol_pow_apply]

variable [Fact p.Prime]

theorem ggSign_gridSwap (hp2 : p ≠ 2) : Perm.sign (ggGridSwap p) = -1 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  unfold ggGridSwap
  rw [Perm.sign_prodCongrLeft, Finset.prod_const, Perm.sign_swap zero_ne_one, Finset.card_univ,
    ZMod.card, hodd.neg_one_pow]

theorem ggGridRow_apply_ne_iff (i : ZMod p) (a : ZMod p × ZMod p) :
    ggGridRow p i a ≠ a ↔ a.1 = i := by
  by_cases h : a.1 = i
  · simp only [h, iff_true, ggGridRow_apply, ↓reduceIte, ne_eq, Prod.ext_iff, true_and]
    intro h'
    exact one_ne_zero (add_eq_left.mp h')
  · simp [h]

theorem ggGridCol_apply_ne_iff (j : ZMod p) (a : ZMod p × ZMod p) :
    ggGridCol p j a ≠ a ↔ a.2 = j := by
  by_cases h : a.2 = j
  · simp only [h, iff_true, ggGridCol_apply, ↓reduceIte, ne_eq, Prod.ext_iff, and_true]
    intro h'
    exact one_ne_zero (add_eq_left.mp h')
  · simp [h]

end GridPerms

section GridMap

variable {V : Type} {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def ggGridMap (x : Perm V) (β : ZMod p → V) (a : ZMod p × ZMod p) : V :=
  (x ^ a.2.val) (β a.1)

theorem ggGridMap_succ {x : Perm V} (hxp : x ^ p = 1) (β : ZMod p → V) (a : ZMod p × ZMod p) :
    x (ggGridMap x β a) = ggGridMap x β (ggGridR p a) := by
  have hp1 : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  unfold ggGridMap
  simp only [ggGridR_apply]
  rw [ZMod.val_add, ZMod.val_one, ← ggPow_eq_pow_mod hxp, pow_succ', Perm.coe_mul,
    Function.comp_apply]

theorem ggGridMap_injective {x : Perm V} (hxp : x ^ p = 1) {β : ZMod p → V}
    (hβ : ∀ i, x (β i) ≠ β i) (horb : ∀ i i' (k : ℕ), (x ^ k) (β i) = β i' → i = i') :
    Function.Injective (ggGridMap x β) := by
  have hp : p.Prime := Fact.out
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  unfold ggGridMap at h
  simp only at h
  have hj' := ZMod.val_lt j'
  have hj := ZMod.val_lt j
  have key : (x ^ (p - j'.val + j.val)) (β i) = β i' := by
    calc (x ^ (p - j'.val + j.val)) (β i) = (x ^ (p - j'.val)) ((x ^ j.val) (β i)) := by
          rw [pow_add, Perm.coe_mul, Function.comp_apply]
      _ = (x ^ (p - j'.val)) ((x ^ j'.val) (β i')) := by rw [h]
      _ = (x ^ (p - j'.val + j'.val)) (β i') := by rw [pow_add, Perm.coe_mul, Function.comp_apply]
      _ = β i' := by rw [Nat.sub_add_cancel hj'.le, hxp, Perm.one_apply]
  have hii : i = i' := horb i i' _ key
  subst hii
  obtain ⟨t, ht⟩ := ggDvd_of_pow_apply_eq hp hxp (hβ i) key
  have hjj : j.val = j'.val := by
    rcases t with _ | _ | t
    · simp at ht
      omega
    · simp at ht
      omega
    · have h2 : p * 2 ≤ p * (t + 1 + 1) := Nat.mul_le_mul_left p (by omega)
      omega
  rw [ZMod.val_injective p hjj]

end GridMap

section Main

variable {V : Type} [DecidableEq V] [Fintype V] {p : ℕ} [Fact p.Prime]

theorem ggAltIn_grid_of_rows {N : Subgroup (Perm V)} (ι : ZMod p × ZMod p ↪ V)
    (hrow : ∀ i, (ggGridRow p i).viaEmbedding ι ∈ N)
    (hcol : ∀ j, (ggGridCol p j).viaEmbedding ι ∈ N) :
    ∃ Y : Finset V, p ^ 2 ≤ Y.card ∧ GGAltIn N Y := by
  have hone : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hne1 : ∀ a : ZMod p × ZMod p, (a.1, a.2 + 1) ≠ a := fun a h =>
    hone (add_eq_left.mp (congrArg Prod.snd h))
  have hne2 : ∀ a : ZMod p × ZMod p, (a.1 + 1, a.2) ≠ a := fun a h =>
    hone (add_eq_left.mp (congrArg Prod.fst h))
  have hne3 : ∀ a : ZMod p × ZMod p, (a.1, a.2 + 1) ≠ (a.1 + 1, a.2) := fun a h =>
    hone (add_eq_left.mp (congrArg Prod.fst h).symm)
  have hthree : ∀ a, GGContains3 N (ι a) (ι (a.1, a.2 + 1)) (ι (a.1 + 1, a.2)) := by
    intro a
    set c := (ggGridRow p a.1).viaEmbedding ι with hc
    set d := (ggGridCol p a.2).viaEmbedding ι with hd
    have hsupp : ∀ z, c z ≠ z → d z ≠ z → z = ι a := by
      intro z hcz hdz
      by_cases hz : z ∈ Set.range ι
      · obtain ⟨b, rfl⟩ := hz
        rw [hc, ggVia_apply] at hcz
        rw [hd, ggVia_apply] at hdz
        have h1 : ggGridRow p a.1 b ≠ b := fun h => hcz (by rw [h])
        have h2 : ggGridCol p a.2 b ≠ b := fun h => hdz (by rw [h])
        rw [ggGridRow_apply_ne_iff] at h1
        rw [ggGridCol_apply_ne_iff] at h2
        rw [Prod.ext h1 h2]
      · exact absurd (ggVia_apply_of_notMem ι _ hz) hcz
    have hcr : c (ι a) = ι (a.1, a.2 + 1) := by rw [hc, ggVia_apply]; simp
    have hdr : d (ι a) = ι (a.1 + 1, a.2) := by rw [hd, ggVia_apply]; simp
    have hcomm := ggCommutator_eq_swap_mul_swap hsupp
      (by rw [hcr]; exact fun h => hne1 a (ι.injective h))
      (by rw [hdr]; exact fun h => hne2 a (ι.injective h))
    unfold GGContains3
    rw [← hcr, ← hdr, ← hcomm]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hrow a.1) (hcol a.2)) (N.inv_mem (hrow a.1)))
      (N.inv_mem (hcol a.2))
  set Tset : ZMod p × ZMod p → Finset V := fun a : ZMod p × ZMod p =>
    {ι a, ι (a.1, a.2 + 1), ι (a.1 + 1, a.2)} with hTset
  have hd1 : ∀ a, ι a ≠ ι (a.1, a.2 + 1) := fun a h => hne1 a (ι.injective h).symm
  have hd2 : ∀ a : ZMod p × ZMod p, ι (a.1, a.2 + 1) ≠ ι (a.1 + 1, a.2) := fun a h =>
    hne3 a (ι.injective h)
  have hd3 : ∀ a, ι a ≠ ι (a.1 + 1, a.2) := fun a h => hne2 a (ι.injective h).symm
  have hTcard : ∀ a, (Tset a).card = 3 := by
    intro a
    rw [hTset, Finset.card_insert_of_notMem (by simp [hd1 a, hd3 a]), Finset.card_pair (hd2 a)]
  have hTalt : ∀ a, GGAltIn N (Tset a) := fun a => ggAltIn_triple (hthree a) (hd1 a) (hd2 a)
    (hd3 a)
  obtain ⟨Z, hTZ, hZ⟩ := ggExists_absorbing (hTcard (0, 0)).ge (hTalt (0, 0))
  have hstep : ∀ a, ι a ∈ Z → Tset a ⊆ Z := fun a ha =>
    hZ.2.2 _ (hTcard a).ge (hTalt a) ⟨ι a, Finset.mem_inter.mpr ⟨ha, by simp [hTset]⟩⟩
  have hall : ∀ n m : ℕ, ι ((n : ZMod p), (m : ZMod p)) ∈ Z := by
    intro n
    induction n with
    | zero =>
      intro m
      induction m with
      | zero => exact hTZ (by simp [hTset])
      | succ m ih => exact hstep _ ih (by simp [hTset, Nat.cast_succ])
    | succ n ih =>
      intro m
      exact hstep _ (ih m) (by simp [hTset, Nat.cast_succ])
  have hgrid : Finset.univ.map ι ⊆ Z := by
    intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hz
    have h := hall a.1.val a.2.val
    simpa [ZMod.natCast_zmod_val] using h
  refine ⟨Z, ?_, hZ.2.1⟩
  calc p ^ 2 = (Finset.univ.map ι).card := by
        rw [Finset.card_map, Finset.card_univ, Fintype.card_prod, ZMod.card, sq]
    _ ≤ Z.card := Finset.card_le_card hgrid

theorem ggAltIn_grid (hp2 : p ≠ 2) {N : Subgroup (Perm V)} {x : Perm V} (hxp : x ^ p = 1)
    {β : ZMod p → V} (hβ : ∀ i, x (β i) ≠ β i)
    (horb : ∀ i i' (k : ℕ), (x ^ k) (β i) = β i' → i = i')
    (hC : ∀ k ∈ alternatingGroup V, k * x = x * k → k ∈ N)
    (hfus : ∀ g ∈ alternatingGroup V, g⁻¹ * x * g ∈ N → g ∈ N) :
    ∃ Y : Finset V, p ^ 2 ≤ Y.card ∧ GGAltIn N Y := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set ι : ZMod p × ZMod p ↪ V := ⟨ggGridMap x β, ggGridMap_injective hxp hβ horb⟩ with hιdef
  have hxι : ∀ a, x (ι a) = ι (ggGridR p a) := fun a => ggGridMap_succ hxp β a
  have hxout : ∀ z, z ∉ Set.range ι → x z ∉ Set.range ι :=
    fun z hz => ggNotMem_range_of_apply ι hxι hz
  have hxN : x ∈ N := hC x (ggSign_eq_one_of_pow_eq_one hodd hxp) rfl
  set T : Perm V := (ggGridT p).viaEmbedding ι with hTdef
  set f : Perm V := T * x * T⁻¹ with hfdef
  have hfι : ∀ a, f (ι a) = ι (ggGridS p a) := by
    intro a
    simp only [hfdef, hTdef, Perm.coe_mul, Function.comp_apply]
    rw [← ggVia_inv, ggVia_apply, hxι, ggVia_apply, ← ggGridT_conj p]
    rfl
  have hfout : ∀ z, z ∉ Set.range ι → f z = x z := by
    intro z hz
    simp only [hfdef, hTdef, Perm.coe_mul, Function.comp_apply]
    rw [← ggVia_inv, ggVia_apply_of_notMem ι _ hz, ggVia_apply_of_notMem ι _ (hxout z hz)]
  have hfout' : ∀ z, z ∉ Set.range ι → f z ∉ Set.range ι := fun z hz => by
    rw [hfout z hz]
    exact hxout z hz
  have hfx : f * x = x * f := by
    ext z
    simp only [Perm.coe_mul, Function.comp_apply]
    by_cases hz : z ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hz
      rw [hxι, hfι, hfι, hxι]
      exact congrArg ι (congrArg (fun g : Perm (ZMod p × ZMod p) => g a) (ggGridS_comm p))
    · rw [hfout _ (hxout z hz), hfout z hz]
  have hfN : f ∈ N := by
    have h1 : f * x⁻¹ ∈ N := by
      refine hC _ ?_ ?_
      · rw [mem_alternatingGroup, map_mul, hfdef, map_mul, map_mul, map_inv, map_inv,
          mul_comm (Perm.sign T) (Perm.sign x), mul_inv_cancel_right, mul_inv_cancel]
      · calc f * x⁻¹ * x = x * f * x⁻¹ := by rw [← hfx]; group
          _ = x * (f * x⁻¹) := by group
    have h2 := N.mul_mem h1 hxN
    rwa [inv_mul_cancel_right] at h2
  obtain ⟨τ, hτA, hτ⟩ : ∃ τ ∈ alternatingGroup V, τ * x * τ⁻¹ = f := by
    by_cases hT : Perm.sign T = 1
    · exact ⟨T, hT, rfl⟩
    · refine ⟨T * (ggGridSwap p).viaEmbedding ι, ?_, ?_⟩
      · rw [mem_alternatingGroup, map_mul, ggSign_via ι (ggGridSwap p), ggSign_gridSwap p hp2]
        rcases Int.units_eq_one_or (Perm.sign T) with h | h
        · exact absurd h hT
        · rw [h]
          rfl
      · have hcomm := ggVia_commute ι hxι hxout (ggGridSwap_comm p)
        calc T * (ggGridSwap p).viaEmbedding ι * x * (T * (ggGridSwap p).viaEmbedding ι)⁻¹
            = T * ((ggGridSwap p).viaEmbedding ι * x * ((ggGridSwap p).viaEmbedding ι)⁻¹) *
                T⁻¹ := by group
          _ = f := by rw [hcomm, mul_inv_cancel_right]
  have hτN : τ ∈ N := by
    have h := hfus τ⁻¹ (inv_mem hτA) (by rw [inv_inv, hτ]; exact hfN)
    simpa using h
  have hCf : ∀ k ∈ alternatingGroup V, k * f = f * k → k ∈ N := by
    intro k hk hkf
    have hk' : τ⁻¹ * k * τ ∈ N := by
      refine hC _ (mul_mem (mul_mem (inv_mem hτA) hk) hτA) ?_
      rw [← hτ] at hkf
      calc τ⁻¹ * k * τ * x = τ⁻¹ * (k * (τ * x * τ⁻¹)) * τ := by group
        _ = τ⁻¹ * ((τ * x * τ⁻¹) * k) * τ := by rw [hkf]
        _ = x * (τ⁻¹ * k * τ) := by group
    have h := N.mul_mem (N.mul_mem hτN hk') (N.inv_mem hτN)
    simpa [mul_assoc] using h
  have hrow : ∀ i, (ggGridRow p i).viaEmbedding ι ∈ N := fun i =>
    hC _ (by rw [mem_alternatingGroup, ggSign_via]
             exact ggSign_eq_one_of_pow_eq_one hodd (ggGridRow_pow p i))
      (ggVia_commute ι hxι hxout (ggGridRow_comm p i))
  have hcol : ∀ j, (ggGridCol p j).viaEmbedding ι ∈ N := fun j =>
    hCf _ (by rw [mem_alternatingGroup, ggSign_via]
              exact ggSign_eq_one_of_pow_eq_one hodd (ggGridCol_pow p j))
      (ggVia_commute ι hfι hfout' (ggGridCol_comm p j))
  exact ggAltIn_grid_of_rows ι hrow hcol

end Main

end CFSG.StandardType
