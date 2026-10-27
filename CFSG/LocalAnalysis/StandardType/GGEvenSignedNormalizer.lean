module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven

public section

namespace CFSG.StandardType.OrthExcEven

open SpCoord Multiplicative

variable {p k : ℕ}

theorem pow_prime_eq_one (f : Fin k → Multiplicative (ZMod p)) : f ^ p = 1 := by
  refine eq_of_toAdd_eq fun j => ?_
  rw [toAdd_pow_apply, Pi.one_apply, toAdd_one, ZMod.natCast_self, zero_mul]

theorem mem_of_sq_mem {G : Type*} [Group G] (hp : p.Prime) (hp2 : p ≠ 2)
    (hexp : ∀ x : G, x ^ p = 1) {P : Subgroup G} {x : G} (h : x ^ 2 ∈ P) : x ∈ P := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have h2 : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hx : x = (x ^ 2) ^ ((p + 1) / 2) := by
    rw [← pow_mul, h2, pow_succ, hexp x, one_mul]
  rw [hx]
  exact P.pow_mem h _

def coordSub (S : Finset (Fin k)) : Subgroup (Fin k → Multiplicative (ZMod p)) where
  carrier := {f | ∀ j, j ∉ S → f j = 1}
  mul_mem' hf hg j hj := by rw [Pi.mul_apply, hf j hj, hg j hj, one_mul]
  one_mem' _ _ := rfl
  inv_mem' hf j hj := by rw [Pi.inv_apply, hf j hj, inv_one]

theorem mem_coordSub {S : Finset (Fin k)} {f : Fin k → Multiplicative (ZMod p)} :
    f ∈ coordSub S ↔ ∀ j, j ∉ S → f j = 1 :=
  Iff.rfl

@[expose] def transp (a b : Fin k) : MulAut (Fin k → Multiplicative (ZMod p)) :=
  permAut (Equiv.swap a b)

@[expose] def sgnTransp (a b : Fin k) : MulAut (Fin k → Multiplicative (ZMod p)) :=
  sgnAut a * sgnAut b * permAut (Equiv.swap a b)

def reflAut (a b : Fin k) (s : ZMod p) (hs : s = 1 ∨ s = -1) :
    MulAut (Fin k → Multiplicative (ZMod p)) :=
  permAut (Equiv.swap a b) * diagAut (fun i => if i = a ∨ i = b then s else 1) fun i => by
    by_cases h : i = a ∨ i = b
    · rw [ite_eq_left h]; exact coord_sign_mul_self hs
    · rw [ite_eq_right h]; exact one_mul 1

theorem swap_mem_pair_iff {a b i : Fin k} :
    (Equiv.swap a b i = a ∨ Equiv.swap a b i = b) ↔ (i = a ∨ i = b) := by
  constructor
  · rintro (h | h)
    · exact Or.inr (by
        have := congrArg (Equiv.swap a b) h
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this)
    · exact Or.inl (by
        have := congrArg (Equiv.swap a b) h
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this)
  · rintro (h | h)
    · rw [h, Equiv.swap_apply_left]; exact Or.inr rfl
    · rw [h, Equiv.swap_apply_right]; exact Or.inl rfl

theorem reflAut_apply {a b : Fin k} (s : ZMod p) (hs : s = 1 ∨ s = -1)
    (f : Fin k → Multiplicative (ZMod p)) (j : Fin k) :
    toAdd (reflAut a b s hs f j) =
      (if j = a ∨ j = b then s else 1) * toAdd (f (Equiv.swap a b j)) := by
  rw [reflAut, MulAut.mul_apply, permAut_apply, Function.comp_apply, diagAut_apply, toAdd_ofAdd,
    Equiv.swap_inv]
  by_cases h : j = a ∨ j = b
  · rw [ite_eq_left h, ite_eq_left (swap_mem_pair_iff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (swap_mem_pair_iff.not.mpr h)]

theorem reflAut_signed_data {a b : Fin k} (s : ZMod p) (hs : s = 1 ∨ s = -1)
    (f : Fin k → Multiplicative (ZMod p)) (i : Fin k) :
    toAdd (reflAut a b s hs f (Equiv.swap a b i)) =
      (if i = a ∨ i = b then s else 1) * toAdd (f i) := by
  rw [reflAut_apply, Equiv.swap_apply_self]
  by_cases h : i = a ∨ i = b
  · rw [ite_eq_left h, ite_eq_left (swap_mem_pair_iff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (swap_mem_pair_iff.not.mpr h)]

theorem eq_of_signed_data {u w : MulAut (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (hw : ∀ f i, toAdd (w f (π i)) = ε i * toAdd (f i)) : u = w := by
  refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun i => ?_
  rw [hu, hw]

theorem reflAut_apply_mulSingle {a b : Fin k} (s : ZMod p) (hs : s = 1 ∨ s = -1)
    (i : Fin k) (x : ZMod p) :
    reflAut a b s hs (Pi.mulSingle i (ofAdd x)) =
      Pi.mulSingle (Equiv.swap a b i) (ofAdd ((if i = a ∨ i = b then s else 1) * x)) :=
  IsSignedPerm.apply_mulSingle (reflAut_signed_data s hs) i x


theorem reflAut_sign_swap {a b j : Fin k} (s : ZMod p) :
    (if Equiv.swap a b j = a ∨ Equiv.swap a b j = b then s else 1) =
      (if j = a ∨ j = b then s else 1) := by
  by_cases h : j = a ∨ j = b
  · rw [ite_eq_left h, ite_eq_left (swap_mem_pair_iff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (swap_mem_pair_iff.not.mpr h)]

theorem sign_ite {s : ZMod p} (hs : s = 1 ∨ s = -1) (c : Prop) [Decidable c] :
    (if c then s else 1) = 1 ∨ (if c then s else 1) = -1 := by
  by_cases h : c
  · rw [ite_eq_left h]; exact hs
  · rw [ite_eq_right h]; exact Or.inl rfl

theorem sgnAut_mul_sgnAut_diag {a b : Fin k} (hab : a ≠ b) :
    (sgnAut a * sgnAut b : MulAut (Fin k → Multiplicative (ZMod p))) =
      diagAut (fun i => if i = a ∨ i = b then -1 else 1) fun i => by
        by_cases h : i = a ∨ i = b
        · rw [ite_eq_left h]; ring
        · rw [ite_eq_right h]; ring := by
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
  rw [sgnAut_mul_sgnAut_apply, OrthNs.dinv_apply_eq, ite_eq_right hab, diagAut_apply,
    toAdd_ofAdd]
  by_cases h : j = a ∨ j = b
  · rw [ite_eq_left h, ite_eq_left h, toAdd_inv]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    ring

theorem reflAut_one (a b : Fin k) :
    reflAut a b (1 : ZMod p) (Or.inl rfl) = transp a b := by
  refine eq_of_signed_data (π := Equiv.swap a b) (ε := fun _ => 1) ?_ ?_
  · intro f i
    rw [reflAut_signed_data]
    simp
  · intro f i
    rw [transp, permAut_apply, Equiv.swap_inv, Function.comp_apply, Equiv.swap_apply_self,
      one_mul]

theorem reflAut_neg_one {a b : Fin k} (hab : a ≠ b) :
    reflAut a b (-1 : ZMod p) (Or.inr rfl) = sgnTransp a b := by
  refine (eq_of_signed_data (u := sgnTransp a b) (w := reflAut a b (-1) (Or.inr rfl))
    (π := Equiv.swap a b) (ε := fun i => if i = a ∨ i = b then -1 else 1) ?_ ?_).symm
  · intro f i
    rw [sgnTransp, sgnAut_mul_sgnAut_diag hab, MulAut.mul_apply, diagAut_apply, permAut_apply,
      Function.comp_apply, toAdd_ofAdd, Equiv.swap_inv, Equiv.swap_apply_self,
      reflAut_sign_swap]
  · intro f i
    rw [reflAut_signed_data]

theorem reflAut_one_mul_inv (hp : p.Prime) {a b : Fin k} (hab : a ≠ b)
    (g : Fin k → Multiplicative (ZMod p)) :
    reflAut a b (1 : ZMod p) (Or.inl rfl) g * g⁻¹ =
      (Pi.mulSingle b (ofAdd 1) * (Pi.mulSingle a (ofAdd 1))⁻¹) ^
        (toAdd (g a) - toAdd (g b)).val := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine eq_of_toAdd_eq fun j => ?_
  rw [toAdd_mul_apply, toAdd_inv_apply, reflAut_apply, toAdd_pow_apply, toAdd_mul_apply,
    toAdd_inv_apply, toAdd_mulSingle, toAdd_mulSingle, ZMod.natCast_zmod_val]
  by_cases hja : j = a
  · rw [hja, ite_eq_left (Or.inl rfl), Equiv.swap_apply_left, ite_eq_left rfl,
      ite_eq_right hab]
    ring
  · by_cases hjb : j = b
    · rw [hjb, ite_eq_left (Or.inr rfl), Equiv.swap_apply_right, ite_eq_left rfl,
        ite_eq_right (Ne.symm hab)]
      ring
    · rw [ite_eq_right (not_or.mpr ⟨hja, hjb⟩), Equiv.swap_apply_of_ne_of_ne hja hjb,
        ite_eq_right hjb, ite_eq_right hja]
      ring

theorem reflAut_neg_one_mul_inv (hp : p.Prime) {a b : Fin k} (hab : a ≠ b)
    (g : Fin k → Multiplicative (ZMod p)) :
    reflAut a b (-1 : ZMod p) (Or.inr rfl) g * g⁻¹ =
      ((Pi.mulSingle a (ofAdd 1) * Pi.mulSingle b (ofAdd 1))⁻¹) ^
        (toAdd (g a) + toAdd (g b)).val := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine eq_of_toAdd_eq fun j => ?_
  rw [toAdd_mul_apply, toAdd_inv_apply, reflAut_apply, toAdd_pow_apply, toAdd_inv_apply,
    toAdd_mul_apply, toAdd_mulSingle, toAdd_mulSingle, ZMod.natCast_zmod_val]
  by_cases hja : j = a
  · rw [hja, ite_eq_left (Or.inl rfl), Equiv.swap_apply_left, ite_eq_left rfl,
      ite_eq_right hab]
    ring
  · by_cases hjb : j = b
    · rw [hjb, ite_eq_left (Or.inr rfl), Equiv.swap_apply_right, ite_eq_left rfl,
        ite_eq_right (Ne.symm hab)]
      ring
    · rw [ite_eq_right (not_or.mpr ⟨hja, hjb⟩), Equiv.swap_apply_of_ne_of_ne hja hjb,
        ite_eq_right hjb, ite_eq_right hja]
      ring

def IsRefl (u : MulAut (Fin k → Multiplicative (ZMod p))) : Prop :=
  u * u = 1 ∧ u ≠ 1 ∧
    ∃ v : Fin k → Multiplicative (ZMod p), ∀ g, ∃ e : ℕ, u g * g⁻¹ = v ^ e

theorem isRefl_of_fixed_card [Fact p.Prime]
    (u : MulAut (Fin k → Multiplicative (ZMod p)))
    (hu : u ^ 2 = 1 ∧ Nat.card {f : Fin k → Multiplicative (ZMod p) // u f = f} * p =
      Nat.card (Fin k → Multiplicative (ZMod p))) : IsRefl u := by
  let δ : (Fin k → Multiplicative (ZMod p)) →* (Fin k → Multiplicative (ZMod p)) :=
    { toFun := fun f => u f * f⁻¹
      map_one' := by rw [map_one]; exact mul_inv_cancel (1 : Fin k → Multiplicative (ZMod p))
      map_mul' := fun f g => by
        rw [map_mul]
        calc
          _ = (u f * u g) * (g⁻¹ * f⁻¹) :=
            congrArg (fun z => (u f * u g) * z) (mul_inv_rev f g)
          _ = (u f * f⁻¹) * (u g * g⁻¹) := by ac_rfl }
  have hfix : Nat.card ↥δ.ker = Nat.card {f : Fin k → Multiplicative (ZMod p) // u f = f} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun (f : Fin k → Multiplicative (ZMod p)) => by
      change u f * f⁻¹ = 1 ↔ u f = f
      exact mul_inv_eq_one)
  have hcard : Nat.card ↥δ.range = p := by
    have hc : Nat.card ↥δ.ker * p = Nat.card (Fin k → Multiplicative (ZMod p)) := by
      rw [hfix]
      exact hu.2
    have heq : Nat.card ↥δ.ker * Nat.card ↥δ.range = Nat.card ↥δ.ker * p :=
      (Subgroup.card_ker_mul_card_range δ).trans hc.symm
    exact mul_left_cancel₀ (Nat.card_pos (α := ↥δ.ker)).ne' heq
  have : IsCyclic ↥δ.range := isCyclic_of_prime_card hcard
  obtain ⟨a, ha⟩ := IsCyclic.exists_monoid_generator (α := ↥δ.range)
  have hne : u ≠ 1 := by
    intro h
    have hd1 : ∀ f, δ f = 1 := by
      intro f
      change u f * f⁻¹ = 1
      rw [h]
      exact mul_inv_cancel f
    have hd : δ.range = ⊥ := by
      apply le_antisymm _ bot_le
      rintro f ⟨a, rfl⟩
      exact hd1 a
    rw [hd, Subgroup.card_bot] at hcard
    exact (Fact.out : p.Prime).ne_one hcard.symm
  refine ⟨by simpa only [pow_two] using hu.1, hne, (a : Fin k → Multiplicative (ZMod p)), ?_⟩
  intro f
  obtain ⟨n, hn⟩ := ha ⟨δ f, ⟨f, rfl⟩⟩
  refine ⟨n, ?_⟩
  exact (congrArg Subtype.val hn).symm

theorem isRefl_reflAut (hp : p.Prime) {a b : Fin k} (hab : a ≠ b) (s : ZMod p)
    (hs : s = 1 ∨ s = -1) : IsRefl (reflAut a b s hs) := by
  have hsq : reflAut a b s hs * reflAut a b s hs = 1 := by
    refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
    rw [MulAut.mul_apply]
    show toAdd (reflAut a b s hs (reflAut a b s hs f) j) = toAdd (f j)
    have h1 := reflAut_signed_data (a := a) (b := b) s hs (reflAut a b s hs f)
      (Equiv.swap a b j)
    rw [Equiv.swap_apply_self] at h1
    rw [h1, reflAut_signed_data s hs f j, reflAut_sign_swap s]
    rw [← mul_assoc, coord_sign_mul_self (sign_ite hs (j = a ∨ j = b)), one_mul]
  refine ⟨hsq, ?_, ?_⟩
  · intro hcon
    have h2 : reflAut a b s hs (Pi.mulSingle a (ofAdd 1)) = Pi.mulSingle a (ofAdd 1) := by
      rw [hcon]; rfl
    rw [reflAut_apply_mulSingle, Equiv.swap_apply_left, ite_eq_left (Or.inl rfl)] at h2
    have hx : s * 1 ≠ 0 := by rw [mul_one]; exact coord_sign_ne_zero hp hs
    exact hab (mulSingle_ofAdd_eq_iff hx h2).1.symm
  · rcases hs with h1 | h1
    · subst h1
      exact ⟨_, fun g => ⟨_, reflAut_one_mul_inv hp hab g⟩⟩
    · subst h1
      exact ⟨_, fun g => ⟨_, reflAut_neg_one_mul_inv hp hab g⟩⟩

theorem isRefl_conj {u φ : MulAut (Fin k → Multiplicative (ZMod p))} (h : IsRefl u) :
    IsRefl (φ * u * φ⁻¹) := by
  obtain ⟨hsq, hne, v, hv⟩ := h
  refine ⟨?_, ?_, φ v, fun g => ?_⟩
  · rw [show (φ * u * φ⁻¹) * (φ * u * φ⁻¹) = φ * (u * u) * φ⁻¹ by group, hsq]
    group
  · intro hcon
    refine hne ?_
    have h4 : φ⁻¹ * (φ * u * φ⁻¹) * φ = u := by group
    rw [hcon, show φ⁻¹ * (1 : MulAut (Fin k → Multiplicative (ZMod p))) * φ = 1 by group] at h4
    exact h4.symm
  · obtain ⟨e, he⟩ := hv (φ⁻¹ g)
    have hg : g⁻¹ = φ ((φ⁻¹ g)⁻¹) := by rw [map_inv, MulAut.apply_inv_self]
    have h1 : (φ * u * φ⁻¹) g = φ (u (φ⁻¹ g)) := rfl
    rw [h1, hg, ← map_mul, he, map_pow]
    exact ⟨e, rfl⟩


local notation "δ" i => (Pi.mulSingle i (ofAdd 1) : Fin k → Multiplicative (ZMod p))

theorem delta_ne_one (hp : p.Prime) (i : Fin k) : (δ i) ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f i)) h
  rw [toAdd_mulSingle, ite_eq_left rfl, Pi.one_apply, toAdd_one] at h1
  exact coord_zero_ne_one hp h1.symm

theorem toAdd_mul_inv_mulSingle {u : MulAut (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (x j : Fin k) :
    toAdd ((u (δ x) * (δ x)⁻¹) j) =
      (if j = π x then ε x else 0) - (if j = x then 1 else 0) := by
  rw [toAdd_mul_apply, toAdd_inv_apply, IsSignedPerm.apply_mulSingle hu x 1,
    toAdd_mulSingle, toAdd_mulSingle, mul_one, sub_eq_add_neg]

theorem refl_pi_shape (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (Fin k → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin k)}
    {ε : Fin k → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (hr : IsRefl u) :
    (π = 1 ∧ ∀ x z : Fin k, x ≠ z → ¬(ε x = -1 ∧ ε z = -1)) ∨
      ∃ x y : Fin k, x ≠ y ∧ π = Equiv.swap x y ∧ ε y = ε x ∧
        ∀ z : Fin k, z ≠ x → z ≠ y → ε z = 1 := by
  classical
  obtain ⟨hu2, -, v, hv⟩ := hr
  have hcoef : ∀ g : Fin k → Multiplicative (ZMod p), ∃ c : ZMod p,
      ∀ j, toAdd ((u g * g⁻¹) j) = c * toAdd (v j) := by
    intro g
    obtain ⟨e, he⟩ := hv g
    exact ⟨(e : ZMod p), fun j => by rw [he, toAdd_pow_apply]⟩
  choose cc hcc using hcoef
  have hkey : ∀ x j : Fin k, (if j = π x then ε x else 0) - (if j = x then 1 else 0) =
      cc (δ x) * toAdd (v j) := by
    intro x j
    rw [← hcc (δ x) j]
    exact (toAdd_mul_inv_mulSingle hu x j).symm
  have hval_x : ∀ x : Fin k, π x ≠ x →
      toAdd ((u (δ x) * (δ x)⁻¹) x) = -1 := by
    intro x hx
    rw [toAdd_mul_inv_mulSingle hu x x, ite_eq_right (Ne.symm hx), ite_eq_left rfl, zero_sub]
  have hval_px : ∀ x : Fin k, π x ≠ x →
      toAdd ((u (δ x) * (δ x)⁻¹) (π x)) = ε x := by
    intro x hx
    rw [toAdd_mul_inv_mulSingle hu x (π x), ite_eq_left rfl, ite_eq_right hx, sub_zero]
  have hval_zero : ∀ {x j : Fin k}, π x ≠ x → j ≠ x → j ≠ π x →
      toAdd ((u (δ x) * (δ x)⁻¹) j) = 0 := by
    intro x j hx hjx hjp
    rw [toAdd_mul_inv_mulSingle hu x j, ite_eq_right hjp, ite_eq_right hjx, sub_zero]
  have hval_diag : ∀ {z : Fin k}, π z = z → ∀ j,
      toAdd ((u (δ z) * (δ z)⁻¹) j) = (if j = z then ε z - 1 else 0) := by
    intro z hz j
    rw [toAdd_mul_inv_mulSingle hu z j, hz]
    by_cases hj : j = z
    · rw [hj]; simp
    · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_right hj, sub_self]
  have hneg : (-1 : ZMod p) ≠ 0 :=
    fun h => coord_zero_ne_one hp (neg_eq_zero.mp h).symm
  have hneg2 : (-2 : ZMod p) ≠ 0 :=
    fun h => coord_two_ne_zero hp hp2 (neg_eq_zero.mp h)
  have hzero : ∀ y : Fin k, cc (δ y) = 0 → π y = y ∧ ε y = 1 := by
    intro y hy0
    have h1 : π y = y := by
      by_contra hne
      have h := hkey y (π y)
      rw [ite_eq_left rfl, ite_eq_right hne, sub_zero, hy0, zero_mul] at h
      exact coord_sign_ne_zero hp (hε y) h
    refine ⟨h1, ?_⟩
    have h := hkey y y
    rw [h1, ite_eq_left rfl, ite_eq_left rfl, hy0, zero_mul] at h
    exact sub_eq_zero.mp h
  have hcc_ne : ∀ {x : Fin k}, π x ≠ x → cc (δ x) ≠ 0 := by
    intro x hx h0
    have h := hkey x (π x)
    rw [ite_eq_left rfl, ite_eq_right hx, sub_zero, h0, zero_mul] at h
    exact coord_sign_ne_zero hp (hε x) h
  have hP : ∀ {x z : Fin k}, cc (δ x) ≠ 0 → cc (δ z) ≠ 0 → ∀ j,
      (toAdd ((u (δ x) * (δ x)⁻¹) j) = 0 ↔
        toAdd ((u (δ z) * (δ z)⁻¹) j) = 0) := by
    intro x z hx hz j
    rw [hcc (δ x) j, hcc (δ z) j]
    constructor
    · intro h
      rw [(coord_mul_eq_zero hp h).resolve_left hx, mul_zero]
    · intro h
      rw [(coord_mul_eq_zero hp h).resolve_left hz, mul_zero]
  have hsupp : ∀ {x z : Fin k}, π x ≠ x → π z ≠ z →
      (({x, π x} : Finset (Fin k)) = {z, π z}) := by
    intro x z hx hz
    refine Finset.ext fun j => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · rw [h]
        by_contra hcon
        rw [not_or] at hcon
        have h1 := (hP (hcc_ne hx) (hcc_ne hz) x).mpr (hval_zero hz hcon.1 hcon.2)
        rw [hval_x x hx] at h1
        exact hneg h1
      · rw [h]
        by_contra hcon
        rw [not_or] at hcon
        have h1 := (hP (hcc_ne hx) (hcc_ne hz) (π x)).mpr (hval_zero hz hcon.1 hcon.2)
        rw [hval_px x hx] at h1
        exact coord_sign_ne_zero hp (hε x) h1
    · rintro (h | h)
      · rw [h]
        by_contra hcon
        rw [not_or] at hcon
        have h1 := (hP (hcc_ne hz) (hcc_ne hx) z).mpr (hval_zero hx hcon.1 hcon.2)
        rw [hval_x z hz] at h1
        exact hneg h1
      · rw [h]
        by_contra hcon
        rw [not_or] at hcon
        have h1 := (hP (hcc_ne hz) (hcc_ne hx) (π z)).mpr (hval_zero hx hcon.1 hcon.2)
        rw [hval_px z hz] at h1
        exact coord_sign_ne_zero hp (hε z) h1
  by_cases hmv : ∃ x, π x ≠ x
  · obtain ⟨x, hx⟩ := hmv
    have hy_moved : π (π x) ≠ π x := fun h => hx (π.injective h)
    have hsupp2 := hsupp hx hy_moved
    have hπy : π (π x) = x := by
      have hmem : π (π x) ∈ ({x, π x} : Finset (Fin k)) := by
        rw [hsupp2]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact h
      · exact absurd h hy_moved
    refine Or.inr ⟨x, π x, Ne.symm hx, ?_, ?_, ?_⟩
    · ext z
      by_cases hzx : z = x
      · rw [hzx, Equiv.swap_apply_left]
      · by_cases hzy : z = π x
        · rw [hzy, Equiv.swap_apply_right, hπy]
        · have hzf : π z = z := by
            by_contra hcon
            have hmem : z ∈ ({x, π x} : Finset (Fin k)) := by
              have h := hsupp hx hcon
              rw [h] at *
              exact Finset.mem_insert_self _ _
            rw [Finset.mem_insert, Finset.mem_singleton] at hmem
            exact absurd hmem (not_or.mpr ⟨hzx, hzy⟩)
          rw [hzf, Equiv.swap_apply_of_ne_of_ne hzx hzy]
    ·
      have h1 : u (u (δ x)) = δ x := by
        rw [← MulAut.mul_apply, hu2]
        rfl
      rw [IsSignedPerm.apply_mulSingle hu x 1] at h1
      rw [IsSignedPerm.apply_mulSingle hu (π x) (ε x * 1), hπy, mul_one] at h1
      have h2 := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f x)) h1
      rw [toAdd_mulSingle, ite_eq_left rfl, toAdd_mulSingle, ite_eq_left rfl] at h2
      have h3 : (ε (π x) - ε x) * ε x = 0 := by
        rw [sub_mul, h2, coord_sign_mul_self (hε x), sub_self]
      exact sub_eq_zero.mp ((coord_mul_eq_zero hp h3).resolve_right
        (coord_sign_ne_zero hp (hε x)))
    ·
      intro z hzx hzy
      have hzf : π z = z := by
        by_contra hcon
        have hmem : z ∈ ({x, π x} : Finset (Fin k)) := by
          have h := hsupp hx hcon
          rw [h] at *
          exact Finset.mem_insert_self _ _
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem
        exact absurd hmem (not_or.mpr ⟨hzx, hzy⟩)
      rcases hε z with hz1 | hz1
      · exact hz1
      · exfalso
        have hwz : toAdd ((u (δ z) * (δ z)⁻¹) z) = -2 := by
          rw [hval_diag hzf z, ite_eq_left rfl, hz1]
          ring
        have hcz : cc (δ z) ≠ 0 := by
          intro h0
          rw [hcc (δ z) z, h0, zero_mul] at hwz
          exact hneg2 hwz.symm
        have hwx : toAdd ((u (δ x) * (δ x)⁻¹) z) = 0 := hval_zero hx hzx hzy
        have h := (hP (hcc_ne hx) hcz z).mp hwx
        rw [hwz] at h
        exact hneg2 h
  · push Not at hmv
    refine Or.inl ⟨Equiv.ext hmv, ?_⟩
    intro x z hxz ⟨hx1, hz1⟩
    have hwx2 : toAdd ((u (δ x) * (δ x)⁻¹) x) = -2 := by
      rw [hval_diag (hmv x) x, ite_eq_left rfl, hx1]
      ring
    have hwz2 : toAdd ((u (δ z) * (δ z)⁻¹) z) = -2 := by
      rw [hval_diag (hmv z) z, ite_eq_left rfl, hz1]
      ring
    have hcx : cc (δ x) ≠ 0 := by
      intro h0
      rw [hcc (δ x) x, h0, zero_mul] at hwx2
      exact hneg2 hwx2.symm
    have hcz : cc (δ z) ≠ 0 := by
      intro h0
      rw [hcc (δ z) z, h0, zero_mul] at hwz2
      exact hneg2 hwz2.symm
    have hwx : toAdd ((u (δ x) * (δ x)⁻¹) z) = 0 := by
      rw [hval_diag (hmv x) z, ite_eq_right (Ne.symm hxz)]
    have h := (hP hcx hcz z).mp hwx
    rw [hwz2] at h
    exact hneg2 h


theorem swap_comm (a b : Fin k) : Equiv.swap a b = Equiv.swap b a := by
  ext z
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  by_cases h1 : z = a <;> by_cases h2 : z = b <;> simp_all

theorem reflAut_swap_args (hp : p.Prime) {a b : Fin k} (s : ZMod p) (hs : s = 1 ∨ s = -1) :
    reflAut a b s hs = reflAut b a s hs := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine MulEquiv.ext fun f => ?_
  have h := hom_ext_mulSingle (M := Fin k → Multiplicative (ZMod p))
    (F₁ := (reflAut a b s hs).toMonoidHom) (F₂ := (reflAut b a s hs).toMonoidHom) ?_
  · exact DFunLike.congr_fun h f
  · intro i
    simp only [MulEquiv.coe_toMonoidHom]
    rw [reflAut_apply_mulSingle, reflAut_apply_mulSingle, swap_comm (a := a) (b := b)]
    congr 2
    by_cases h : i = a ∨ i = b
    · rw [ite_eq_left h, ite_eq_left (by tauto)]
    · rw [ite_eq_right h, ite_eq_right (by tauto)]

theorem commute_reflAut_same (hp : p.Prime) {a b : Fin k} (s t : ZMod p)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    Commute (reflAut a b s hs) (reflAut a b t ht) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine MulEquiv.ext fun f => ?_
  have h := hom_ext_mulSingle (M := Fin k → Multiplicative (ZMod p))
    (F₁ := (reflAut a b s hs * reflAut a b t ht).toMonoidHom)
    (F₂ := (reflAut a b t ht * reflAut a b s hs).toMonoidHom) ?_
  · exact DFunLike.congr_fun h f
  · intro i
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
    rw [reflAut_apply_mulSingle, reflAut_apply_mulSingle, reflAut_apply_mulSingle,
      reflAut_apply_mulSingle]
    rw [reflAut_sign_swap (a := a) (b := b) (j := i) t,
      reflAut_sign_swap (a := a) (b := b) (j := i) s]
    congr 2
    ring

theorem swap_mem_pair_iff' {a b c d j : Fin k} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : (Equiv.swap a b j = c ∨ Equiv.swap a b j = d) ↔ (j = c ∨ j = d) := by
  constructor
  · rintro (h | h)
    · left
      have := congrArg (Equiv.swap a b) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm] at this
    · right
      have := congrArg (Equiv.swap a b) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm] at this
  · rintro (h | h)
    · left
      rw [h, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
    · right
      rw [h, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]

theorem swap_swap_comm {a b c d j : Fin k} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    Equiv.swap c d (Equiv.swap a b j) = Equiv.swap a b (Equiv.swap c d j) := by
  by_cases h1 : j = a
  · rw [h1, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbc hbd,
      Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left]
  · by_cases h2 : j = b
    · rw [h2, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbc hbd,
        Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_right]
    · by_cases h3 : j = c
      · rw [h3, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
      · by_cases h4 : j = d
        · rw [h4, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4,
            Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem commute_reflAut_disjoint (hp : p.Prime) {a b c d : Fin k}
    (s t : ZMod p) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (reflAut a b s hs) (reflAut c d t ht) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine MulEquiv.ext fun f => ?_
  have h := hom_ext_mulSingle (M := Fin k → Multiplicative (ZMod p))
    (F₁ := (reflAut a b s hs * reflAut c d t ht).toMonoidHom)
    (F₂ := (reflAut c d t ht * reflAut a b s hs).toMonoidHom) ?_
  · exact DFunLike.congr_fun h f
  · intro i
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
    rw [reflAut_apply_mulSingle, reflAut_apply_mulSingle, reflAut_apply_mulSingle,
      reflAut_apply_mulSingle, swap_swap_comm hac had hbc hbd]
    congr 2
    have hAB : (Equiv.swap c d i = a ∨ Equiv.swap c d i = b) ↔ (i = a ∨ i = b) :=
      swap_mem_pair_iff' (a := c) (b := d) (c := a) (d := b) hac.symm hbc.symm had.symm hbd.symm
    have hCD : (Equiv.swap a b i = c ∨ Equiv.swap a b i = d) ↔ (i = c ∨ i = d) :=
      swap_mem_pair_iff' hac had hbc hbd
    by_cases hi1 : i = a ∨ i = b
    · have hi2 : ¬(i = c ∨ i = d) := by
        rintro (h | h)
        · rcases hi1 with h' | h'
          · exact hac (h'.symm.trans h)
          · exact hbc (h'.symm.trans h)
        · rcases hi1 with h' | h'
          · exact had (h'.symm.trans h)
          · exact hbd (h'.symm.trans h)
      have hs1 : (if Equiv.swap c d i = a ∨ Equiv.swap c d i = b then s else 1) = s :=
        ite_eq_left (hAB.mpr hi1)
      have hs2 : (if i = a ∨ i = b then s else 1) = s := ite_eq_left hi1
      have ht1 : (if i = c ∨ i = d then t else 1) = 1 := ite_eq_right hi2
      have ht2 : (if Equiv.swap a b i = c ∨ Equiv.swap a b i = d then t else 1) = 1 :=
        ite_eq_right (hCD.not.mpr hi2)
      rw [hs1, hs2, ht1, ht2]
      ring
    · by_cases hi2 : i = c ∨ i = d
      · have hs1 : (if Equiv.swap c d i = a ∨ Equiv.swap c d i = b then s else 1) = 1 :=
          ite_eq_right (hAB.not.mpr hi1)
        have hs2 : (if i = a ∨ i = b then s else 1) = 1 := ite_eq_right hi1
        have ht1 : (if i = c ∨ i = d then t else 1) = t := ite_eq_left hi2
        have ht2 : (if Equiv.swap a b i = c ∨ Equiv.swap a b i = d then t else 1) = t :=
          ite_eq_left (hCD.mpr hi2)
        rw [hs1, hs2, ht1, ht2]
        ring
      · have hs1 : (if Equiv.swap c d i = a ∨ Equiv.swap c d i = b then s else 1) = 1 :=
          ite_eq_right (hAB.not.mpr hi1)
        have hs2 : (if i = a ∨ i = b then s else 1) = 1 := ite_eq_right hi1
        have ht1 : (if i = c ∨ i = d then t else 1) = 1 := ite_eq_right hi2
        have ht2 : (if Equiv.swap a b i = c ∨ Equiv.swap a b i = d then t else 1) = 1 :=
          ite_eq_right (hCD.not.mpr hi2)
        rw [hs1, hs2, ht1, ht2]


theorem not_commute_reflAut_share (hp : p.Prime) {a b d : Fin k} (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (s t : ZMod p) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    ¬ Commute (reflAut a b s hs) (reflAut a d t ht) := by
  intro hcomm
  have h := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod p)) =>
    toAdd (u (δ b) a)) hcomm.eq
  simp only [MulAut.mul_apply] at h
  simp only [reflAut_apply] at h
  simp only [true_or, ite_true] at h
  rw [Equiv.swap_apply_left] at h
  rw [ite_eq_right (not_or.mpr ⟨Ne.symm hab, hbd⟩)] at h
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbd] at h
  rw [toAdd_mulSingle, ite_eq_left rfl] at h
  rw [Equiv.swap_apply_left] at h
  rw [ite_eq_right (not_or.mpr ⟨Ne.symm had, Ne.symm hbd⟩)] at h
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)] at h
  rw [toAdd_mulSingle, ite_eq_right (Ne.symm hbd)] at h
  ring_nf at h
  exact coord_sign_ne_zero hp hs h

theorem commute_reflAut_iff (hp : p.Prime) {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d)
    (s t : ZMod p) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    Commute (reflAut a b s hs) (reflAut c d t ht) ↔
      ((a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d)) := by
  constructor
  · intro hcomm
    by_cases hsame : (a = c ∧ b = d) ∨ (a = d ∧ b = c)
    · rcases hsame with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · by_cases hdisj : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
      · exact Or.inr (Or.inr hdisj)
      · exfalso
        have hnot1 : ¬(a = c ∧ b = d) := fun h => hsame (Or.inl h)
        have hnot2 : ¬(a = d ∧ b = c) := fun h => hsame (Or.inr h)
        have hdisj' : a = c ∨ a = d ∨ b = c ∨ b = d := by
          by_contra hcon
          push Not at hcon
          exact hdisj hcon
        rcases hdisj' with hac | had | hbc | hbd
        · have hbd' : b ≠ d := fun h => hnot1 ⟨hac, h⟩
          rw [hac] at hcomm
          exact not_commute_reflAut_share hp (fun h => hab (hac.trans h)) hcd hbd' s t hs ht hcomm
        · have hbc' : b ≠ c := fun h => hnot2 ⟨had, h⟩
          rw [had, reflAut_swap_args hp t ht] at hcomm
          exact not_commute_reflAut_share hp (fun h => hab (had.trans h)) hcd.symm hbc'
            s t hs ht hcomm
        · have had' : a ≠ d := fun h => hnot2 ⟨h, hbc⟩
          rw [hbc, reflAut_swap_args hp s hs] at hcomm
          exact not_commute_reflAut_share hp (fun h => hab (h.symm.trans hbc.symm)) hcd had'
            s t hs ht hcomm
        · have hac' : a ≠ c := fun h => hnot1 ⟨h, hbd⟩
          rw [hbd, reflAut_swap_args hp s hs, reflAut_swap_args hp t ht] at hcomm
          exact not_commute_reflAut_share hp (fun h => hab (h.symm.trans hbd.symm)) hcd.symm hac'
            s t hs ht hcomm
  · rintro (h | h | h)
    · obtain ⟨rfl, rfl⟩ := h
      exact commute_reflAut_same hp s t hs ht
    · obtain ⟨rfl, rfl⟩ := h
      rw [reflAut_swap_args hp s hs]
      exact commute_reflAut_same hp s t hs ht
    · obtain ⟨hac, had, hbc, hbd⟩ := h
      exact commute_reflAut_disjoint hp s t hs ht hac had hbc hbd


theorem reflAut_mul_inv_mem {a b : Fin k} (s : ZMod p) (hs : s = 1 ∨ s = -1)
    (g : Fin k → Multiplicative (ZMod p)) :
    reflAut a b s hs g * g⁻¹ ∈ coordSub ({a, b} : Finset (Fin k)) := by
  rw [mem_coordSub]
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  apply toAdd.injective
  rw [toAdd_mul_apply, toAdd_inv_apply, reflAut_apply,
    ite_eq_right (not_or.mpr ⟨hj.1, hj.2⟩), Equiv.swap_apply_of_ne_of_ne hj.1 hj.2,
    toAdd_one]
  ring

theorem transp_apply_delta (a b : Fin k) :
    transp a b (δ a) = δ b := by
  rw [transp, permAut_mulSingle, Equiv.swap_apply_left]

theorem sgnTransp_apply_delta {a b : Fin k} (hab : a ≠ b) :
    sgnTransp a b (δ a) = (δ b)⁻¹ := by
  rw [sgnTransp, MulAut.mul_apply, MulAut.mul_apply, permAut_mulSingle, Equiv.swap_apply_left,
    sgnAut_mulSingle_self, map_inv, sgnAut_mulSingle_of_ne (Ne.symm hab)]

theorem commute_conj_iff (φ u w : MulAut (Fin k → Multiplicative (ZMod p))) :
    Commute (φ * u * φ⁻¹) (φ * w * φ⁻¹) ↔ Commute u w := by
  rw [commute_iff_eq, commute_iff_eq]
  constructor
  · intro h
    have h' := congrArg (fun x => φ⁻¹ * x * φ) h
    group at h'
    exact h'
  · intro h
    rw [show φ * u * φ⁻¹ * (φ * w * φ⁻¹) = φ * (u * w) * φ⁻¹ by group,
      show φ * w * φ⁻¹ * (φ * u * φ⁻¹) = φ * (w * u) * φ⁻¹ by group, h]

theorem mul_inv_mul_inv_mul_inv (A B : Fin k → Multiplicative (ZMod p)) :
    A * B⁻¹ * (A⁻¹ * B⁻¹) = (B ^ 2)⁻¹ := by
  refine eq_of_toAdd_eq fun j => ?_
  simp only [toAdd_mul_apply, toAdd_inv_apply, toAdd_pow_apply]
  ring

theorem not_commute_transp (hp : p.Prime) {a b b' : Fin k} (hab : a ≠ b) (hab' : a ≠ b')
    (hbb' : b ≠ b') : ¬ Commute (transp (p := p) a b) (transp (p := p) a b') := by
  rw [← reflAut_one a b, ← reflAut_one a b']
  intro hcomm
  rcases (commute_reflAut_iff hp hab hab' 1 1 (Or.inl rfl) (Or.inl rfl)).mp hcomm with
    ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -, -, -⟩
  · exact hbb' h2
  · exact hab' h1
  · exact h1 rfl

theorem commute_transp_sgnTransp (hp : p.Prime) {a b : Fin k} (hab : a ≠ b) :
    Commute (transp (p := p) a b) (sgnTransp (p := p) a b) := by
  rw [← reflAut_one a b, ← reflAut_neg_one hab]
  exact commute_reflAut_same hp 1 (-1) (Or.inl rfl) (Or.inr rfl)

theorem commute_reflAut_neg_iff (hp : p.Prime) {e f : Fin k} (hef : e ≠ f) {a b : Fin k}
    (hab : a ≠ b) (s : ZMod p) (hs : s = 1 ∨ s = -1) :
    Commute (reflAut e f s hs) (reflAut a b 1 (Or.inl rfl)) ↔
      Commute (reflAut e f s hs) (reflAut a b (-1) (Or.inr rfl)) := by
  rw [commute_reflAut_iff hp hef hab s 1 hs (Or.inl rfl),
    commute_reflAut_iff hp hef hab s (-1) hs (Or.inr rfl)]

theorem exists_ne_four (hk : 5 ≤ k) (c d c' d' : Fin k) :
    ∃ y : Fin k, y ≠ c ∧ y ≠ d ∧ y ≠ c' ∧ y ≠ d' := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ {c, d, c', d'} := by
    intro y _
    have := h y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({c, d, c', d'} : Finset (Fin k)).card ≤ 4 := by
    have h3 : ({c, d, c', d'} : Finset (Fin k)).card ≤
        ({d, c', d'} : Finset (Fin k)).card + 1 := Finset.card_insert_le _ _
    have h4 : ({d, c', d'} : Finset (Fin k)).card ≤ ({c', d'} : Finset (Fin k)).card + 1 :=
      Finset.card_insert_le _ _
    have h5 : ({c', d'} : Finset (Fin k)).card ≤ ({d'} : Finset (Fin k)).card + 1 :=
      Finset.card_insert_le _ _
    have h6 : ({d'} : Finset (Fin k)).card = 1 := Finset.card_singleton _
    omega
  omega

theorem shape_of_refl (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (Fin k → Multiplicative (ZMod p))} (hu : IsSignedPerm ⇑u) (hr : IsRefl u) :
    (∃ a : Fin k, u = sgnAut a) ∨
      ∃ (a b : Fin k) (_ : a ≠ b) (s : ZMod p) (hs : s = 1 ∨ s = -1), u = reflAut a b s hs := by
  classical
  obtain ⟨π, ε, hε, hu⟩ := hu
  rcases refl_pi_shape hp hp2 hε hu hr with ⟨hπ1, hneg⟩ | ⟨x, y, hxy, hπ, hεy, hε1⟩
  ·
    obtain ⟨a, ha⟩ : ∃ a, ε a = -1 := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ i, ε i = 1 := fun i => (hε i).resolve_right (hcon i)
      have : u = 1 := by
        refine eq_of_signed_data (π := π) (ε := fun _ => 1) ?_ ?_
        · intro f i; rw [hu, hall i, one_mul]
        · intro f i; rw [hπ1]; simp
      exact hr.2.1 this
    refine Or.inl ⟨a, ?_⟩
    refine eq_of_signed_data (w := sgnAut a) (π := π)
      (ε := fun i => if i = a then (-1 : ZMod p) else 1) ?_ ?_
    · intro f i
      rw [hu]
      congr 1
      by_cases hia : i = a
      · rw [hia, ite_eq_left rfl]
        exact ha
      · rw [ite_eq_right hia]
        rcases hε i with h | h
        · exact h
        · exact absurd ⟨h, ha⟩ (hneg i a hia)
    · intro f i
      rw [hπ1, Equiv.Perm.one_apply, sgnAut_apply]
      by_cases hia : i = a
      · rw [hia, ite_eq_left rfl, Function.update_self, toAdd_inv]
        ring
      · rw [ite_eq_right hia, Function.update_of_ne hia, one_mul]
  ·
    refine Or.inr ⟨x, y, hxy, ε x, hε x, ?_⟩
    refine eq_of_signed_data (w := reflAut x y (ε x) (hε x)) (π := Equiv.swap x y)
      (ε := fun i => if i = x ∨ i = y then ε x else 1) ?_ ?_
    · intro f i
      rw [← hπ, hu]
      congr 1
      by_cases hix : i = x
      · rw [hix, ite_eq_left (Or.inl rfl)]
      · by_cases hiy : i = y
        · rw [hiy, ite_eq_left (Or.inr rfl), hεy]
        · rw [ite_eq_right (not_or.mpr ⟨hix, hiy⟩), hε1 i hix hiy]
    · intro f i
      rw [reflAut_signed_data]

theorem eq_pair_of_mem_pair {c d z j : Fin k} (hcd : c ≠ d) (hzj : z ≠ j)
    (hz : z ∈ ({c, d} : Finset (Fin k))) (hj : j ∈ ({c, d} : Finset (Fin k))) :
    ({c, d} : Finset (Fin k)) = {z, j} := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
  · rw [Finset.card_pair hcd, Finset.card_pair hzj]

theorem exists_support (hp : p.Prime) (hp2 : p ≠ 2) (hk : 5 ≤ k)
    {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hHs : ∀ u ∈ H, IsSignedPerm ⇑u)
    (hHd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H)
    (hHp : ∀ σ : Equiv.Perm (Fin k), permAut σ ∈ H)
    (hA : ∀ i, sgnAut i ∉ H)
    {φ : MulAut (Fin k → Multiplicative (ZMod p))}
    (hφ : ∀ u ∈ H, φ * u * φ⁻¹ ∈ H) (hφ' : ∀ u ∈ H, φ⁻¹ * u * φ ∈ H)
    {a b : Fin k} (hab : a ≠ b) :
    ∃ (c d : Fin k) (_ : c ≠ d) (s : ZMod p) (hs : s = 1 ∨ s = -1),
      φ * transp (p := p) a b * φ⁻¹ = reflAut c d s hs ∧
        φ (δ a) ∈ coordSub ({c, d} : Finset (Fin k)) := by
  classical
  have hτH : transp (p := p) a b ∈ H := hHp (Equiv.swap a b)
  have hσH : sgnTransp (p := p) a b ∈ H := by
    rw [sgnTransp]
    exact H.mul_mem (hHd a b hab) (hHp (Equiv.swap a b))
  have hτ : φ * transp (p := p) a b * φ⁻¹ ∈ H := hφ _ hτH
  have hσ : φ * sgnTransp (p := p) a b * φ⁻¹ ∈ H := hφ _ hσH
  have hreflτ : IsRefl (transp (p := p) a b) := by
    rw [← reflAut_one a b]
    exact isRefl_reflAut hp hab 1 (Or.inl rfl)
  have hreflσ : IsRefl (sgnTransp (p := p) a b) := by
    rw [← reflAut_neg_one hab]
    exact isRefl_reflAut hp hab (-1) (Or.inr rfl)
  have hR : IsRefl (φ * transp (p := p) a b * φ⁻¹) := isRefl_conj hreflτ
  have hR' : IsRefl (φ * sgnTransp (p := p) a b * φ⁻¹) := isRefl_conj hreflσ
  obtain ⟨c, d, hcd, s, hs, hRcd⟩ :
      ∃ (c d : Fin k) (hcd : c ≠ d) (s : ZMod p) (hs : s = 1 ∨ s = -1),
        φ * transp (p := p) a b * φ⁻¹ = reflAut c d s hs := by
    rcases shape_of_refl hp hp2 (hHs _ hτ) hR with ⟨i, hi⟩ | h
    · exact absurd (hi ▸ hτ) (hA i)
    · exact h
  obtain ⟨c', d', hcd', t, ht, hRc'd'⟩ :
      ∃ (c' d' : Fin k) (hcd' : c' ≠ d') (t : ZMod p) (ht : t = 1 ∨ t = -1),
        φ * sgnTransp (p := p) a b * φ⁻¹ = reflAut c' d' t ht := by
    rcases shape_of_refl hp hp2 (hHs _ hσ) hR' with ⟨i, hi⟩ | h
    · exact absurd (hi ▸ hσ) (hA i)
    · exact h
  have key : ∀ {x : MulAut (Fin k → Multiplicative (ZMod p))}, x ∈ H → IsRefl x →
      (Commute x (φ * transp (p := p) a b * φ⁻¹) ↔
        Commute x (φ * sgnTransp (p := p) a b * φ⁻¹)) := by
    intro x hxH hxr
    have hx'H : φ⁻¹ * x * φ ∈ H := hφ' x hxH
    have hx'r : IsRefl (φ⁻¹ * x * φ) := by
      have h := isRefl_conj (φ := φ⁻¹) hxr
      simpa using h
    have hxeq : φ * (φ⁻¹ * x * φ) * φ⁻¹ = x := by group
    rw [← hxeq, commute_conj_iff φ (φ⁻¹ * x * φ) (transp (p := p) a b),
      commute_conj_iff φ (φ⁻¹ * x * φ) (sgnTransp (p := p) a b), ← reflAut_one a b,
      ← reflAut_neg_one hab]
    rcases shape_of_refl hp hp2 (hHs _ hx'H) hx'r with ⟨i, hi⟩ | ⟨e, f, hef, u, hu, hx'⟩
    · exact absurd (hi ▸ hx'H) (hA i)
    · rw [hx']
      exact commute_reflAut_neg_iff hp hef hab u hu
  have hcomm : Commute (reflAut c d s hs) (reflAut c' d' t ht) := by
    rw [← hRcd, ← hRc'd']
    exact (commute_conj_iff φ (transp (p := p) a b) (sgnTransp (p := p) a b)).mpr
      (commute_transp_sgnTransp hp hab)
  have hpair : (c = c' ∧ d = d') ∨ (c = d' ∧ d = c') := by
    rcases (commute_reflAut_iff hp hcd hcd' s t hs ht).mp hcomm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (by
        rintro ⟨hac, had, hbc, hbd⟩
        obtain ⟨y, hyc, hyd, hyc', hyd'⟩ := exists_ne_four hk c d c' d'
        have hcy : c ≠ y := Ne.symm hyc
        have hxH : transp (p := p) c y ∈ H := hHp _
        have hxr : IsRefl (transp (p := p) c y) := by
          rw [← reflAut_one c y]
          exact isRefl_reflAut hp hcy 1 (Or.inl rfl)
        have hnc : ¬ Commute (transp (p := p) c y) (φ * transp (p := p) a b * φ⁻¹) := by
          rw [hRcd, ← reflAut_one c y]
          exact not_commute_reflAut_share hp hcy hcd hyd 1 s (Or.inl rfl) hs
        have hc : Commute (transp (p := p) c y) (φ * sgnTransp (p := p) a b * φ⁻¹) := by
          rw [hRc'd', ← reflAut_one c y]
          exact commute_reflAut_disjoint hp 1 t (Or.inl rfl) ht hac had hyc' hyd'
        exact hnc ((key hxH hxr).mpr hc))
  obtain ⟨t', ht', hRcd'⟩ : ∃ (t' : ZMod p) (ht' : t' = 1 ∨ t' = -1),
      φ * sgnTransp (p := p) a b * φ⁻¹ = reflAut c d t' ht' := by
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨t, ht, by rw [hRc'd', ← h1, ← h2]⟩
    · refine ⟨t, ht, ?_⟩
      rw [hRc'd', ← h2, ← h1, reflAut_swap_args hp t ht]
  have hmem1 : (φ * transp (p := p) a b * φ⁻¹) (φ (δ a)) * (φ (δ a))⁻¹ ∈
      coordSub ({c, d} : Finset (Fin k)) := by
    rw [hRcd]
    exact reflAut_mul_inv_mem s hs _
  have hmem2 : (φ * sgnTransp (p := p) a b * φ⁻¹) (φ (δ a)) * (φ (δ a))⁻¹ ∈
      coordSub ({c, d} : Finset (Fin k)) := by
    rw [hRcd']
    exact reflAut_mul_inv_mem t' ht' _
  have e1 : (φ * transp (p := p) a b * φ⁻¹) (φ (δ a)) = φ (δ b) := by
    rw [show (φ * transp (p := p) a b * φ⁻¹) (φ (δ a)) = φ (transp (p := p) a b (δ a)) by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self], transp_apply_delta a b]
  have e2 : (φ * sgnTransp (p := p) a b * φ⁻¹) (φ (δ a)) = (φ (δ b))⁻¹ := by
    rw [show (φ * sgnTransp (p := p) a b * φ⁻¹) (φ (δ a)) =
        φ (sgnTransp (p := p) a b (δ a)) by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self], sgnTransp_apply_delta hab, map_inv]
  rw [e1] at hmem1
  rw [e2] at hmem2
  have hprod : (φ (δ a)) ^ 2 ∈ coordSub ({c, d} : Finset (Fin k)) := by
    have hm := (coordSub ({c, d} : Finset (Fin k))).mul_mem hmem1 hmem2
    rw [mul_inv_mul_inv_mul_inv] at hm
    simpa using (coordSub ({c, d} : Finset (Fin k))).inv_mem hm
  exact ⟨c, d, hcd, s, hs, hRcd, mem_of_sq_mem hp hp2 pow_prime_eq_one hprod⟩

theorem exists_mulSingle_of_two_pairs {f : Fin k → Multiplicative (ZMod p)}
    {c d c' d' : Fin k} (hcd : c ≠ d) (hc'd' : c' ≠ d')
    (hne : ¬((c = c' ∧ d = d') ∨ (c = d' ∧ d = c')))
    (h1 : f ∈ coordSub ({c, d} : Finset (Fin k)))
    (h2 : f ∈ coordSub ({c', d'} : Finset (Fin k))) (hf : f ≠ 1) :
    ∃ (j : Fin k) (x : ZMod p), x ≠ 0 ∧ f = Pi.mulSingle j (ofAdd x) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin k, f j ≠ 1 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  have hj1 : j ∈ ({c, d} : Finset (Fin k)) := by
    by_contra h
    exact hj ((mem_coordSub.mp h1) j h)
  have hj2 : j ∈ ({c', d'} : Finset (Fin k)) := by
    by_contra h
    exact hj ((mem_coordSub.mp h2) j h)
  refine ⟨j, toAdd (f j), ?_, ?_⟩
  · intro h0
    exact hj (by rw [← ofAdd_toAdd (f j), h0, ofAdd_zero])
  · refine eq_of_toAdd_eq fun z => ?_
    rw [toAdd_mulSingle]
    by_cases hz : z = j
    · rw [hz, ite_eq_left rfl]
    · rw [ite_eq_right hz]
      by_contra hfz
      have hz1 : z ∈ ({c, d} : Finset (Fin k)) := by
        by_contra h
        exact hfz (by rw [(mem_coordSub.mp h1) z h]; rfl)
      have hz2 : z ∈ ({c', d'} : Finset (Fin k)) := by
        by_contra h
        exact hfz (by rw [(mem_coordSub.mp h2) z h]; rfl)
      have e1 : ({c, d} : Finset (Fin k)) = {z, j} := eq_pair_of_mem_pair hcd hz hz1 hj1
      have e2 : ({c', d'} : Finset (Fin k)) = {z, j} := eq_pair_of_mem_pair hc'd' hz hz2 hj2
      have hEq : ({c, d} : Finset (Fin k)) = {c', d'} := by rw [e1, e2]
      have hc : c ∈ ({c', d'} : Finset (Fin k)) := by
        rw [← hEq]
        exact Finset.mem_insert_self _ _
      have hd : d ∈ ({c', d'} : Finset (Fin k)) := by
        rw [← hEq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
      rcases hc with h1 | h1 <;> rcases hd with h2 | h2
      · exact hcd (h2.trans h1.symm).symm
      · exact hne (Or.inl ⟨h1, h2⟩)
      · exact hne (Or.inr ⟨h1, h2⟩)
      · exact hcd (h1.trans h2.symm)

theorem exists_mulSingle_of_normalizes_dk (hp : p.Prime) (hp2 : p ≠ 2) (hk : 5 ≤ k)
    {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hHs : ∀ u ∈ H, IsSignedPerm ⇑u)
    (hHd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H)
    (hHp : ∀ σ : Equiv.Perm (Fin k), permAut σ ∈ H)
    (hA : ∀ i, sgnAut i ∉ H)
    {φ : MulAut (Fin k → Multiplicative (ZMod p))}
    (hφ : ∀ u ∈ H, φ * u * φ⁻¹ ∈ H) (hφ' : ∀ u ∈ H, φ⁻¹ * u * φ ∈ H) (a : Fin k) :
    ∃ (j : Fin k) (x : ZMod p), x ≠ 0 ∧ φ (δ a) = Pi.mulSingle j (ofAdd x) := by
  classical
  obtain ⟨b₁, hb₁a⟩ : ∃ b₁ : Fin k, b₁ ≠ a :=
    ⟨_, (coord_exists_ne_ne (k := k) (by omega) a a).choose_spec.1⟩
  obtain ⟨b₂, hb₂a, hb₂b₁⟩ := coord_exists_ne_ne (k := k) (by omega) a b₁
  obtain ⟨c₁, d₁, hc₁d₁, s₁, hs₁, hR₁, hmem₁⟩ :=
    exists_support hp hp2 hk hHs hHd hHp hA hφ hφ' (a := a) (b := b₁) (Ne.symm hb₁a)
  obtain ⟨c₂, d₂, hc₂d₂, s₂, hs₂, hR₂, hmem₂⟩ :=
    exists_support hp hp2 hk hHs hHd hHp hA hφ hφ' (a := a) (b := b₂) (Ne.symm hb₂a)
  have hne : ¬((c₁ = c₂ ∧ d₁ = d₂) ∨ (c₁ = d₂ ∧ d₁ = c₂)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hcomm : Commute (transp (p := p) a b₁) (transp (p := p) a b₂) := by
        rw [← commute_conj_iff φ (transp (p := p) a b₁) (transp (p := p) a b₂), hR₁, hR₂,
          h1, h2]
        exact commute_reflAut_same hp s₁ s₂ hs₁ hs₂
      exact not_commute_transp hp (Ne.symm hb₁a) (Ne.symm hb₂a) (Ne.symm hb₂b₁) hcomm
    · have hcomm : Commute (transp (p := p) a b₁) (transp (p := p) a b₂) := by
        rw [← commute_conj_iff φ (transp (p := p) a b₁) (transp (p := p) a b₂), hR₁, hR₂,
          h1, h2, reflAut_swap_args hp s₂ hs₂]
        exact commute_reflAut_same hp s₁ s₂ hs₁ hs₂
      exact not_commute_transp hp (Ne.symm hb₁a) (Ne.symm hb₂a) (Ne.symm hb₂b₁) hcomm
  refine exists_mulSingle_of_two_pairs hc₁d₁ hc₂d₂ hne hmem₁ hmem₂ ?_
  intro hf
  exact delta_ne_one hp a (φ.injective (by rw [hf, map_one]))

theorem exists_isSignedPerm_pow_of_mulSingle (hp : p.Prime) (hk : 3 ≤ k)
    {φ : MulAut (Fin k → Multiplicative (ZMod p))} {j : Fin k → Fin k}
    {c : Fin k → ZMod p} (hc : ∀ i, c i ≠ 0)
    (hjc : ∀ i, φ (δ i) = Pi.mulSingle (j i) (ofAdd (c i)))
    (hperm : ∀ i i' : Fin k, i ≠ i' →
      IsSignedPerm ⇑(φ * permAut (p := p) (Equiv.swap i i') * φ⁻¹)) :
    ∃ w : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑w ∧
      ∃ c₀ : ℕ, ∀ f, φ f = (w f) ^ c₀ := by
  classical
  have hne0 : NeZero p := ⟨hp.ne_zero⟩
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
  set J : Equiv.Perm (Fin k) := Equiv.ofBijective j hjinj.bijective_of_finite
  have hpm : ∀ i i', c i' = c i ∨ c i' = -c i := by
    intro i i'
    by_cases hii : i = i'
    · subst hii
      exact Or.inl rfl
    obtain ⟨π, ε, hε, hq⟩ := hperm i i' hii
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

theorem exists_isSignedPerm_pow_of_normalizes_dk (hp : p.Prime) (hp2 : p ≠ 2) (hk : 5 ≤ k)
    {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hHs : ∀ u ∈ H, IsSignedPerm ⇑u)
    (hHd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H)
    (hHp : ∀ σ : Equiv.Perm (Fin k), permAut σ ∈ H)
    {φ : MulAut (Fin k → Multiplicative (ZMod p))}
    (hφ : ∀ u ∈ H, φ * u * φ⁻¹ ∈ H) (hφ' : ∀ u ∈ H, φ⁻¹ * u * φ ∈ H) :
    ∃ w : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑w ∧
      ∃ c : ℕ, ∀ f, φ f = (w f) ^ c := by
  classical
  by_cases hA : ∃ i : Fin k, sgnAut i ∈ H
  ·
    obtain ⟨i₀, hi₀⟩ := hA
    have hs : ∀ i : Fin k, sgnAut i ∈ H := by
      intro i
      by_cases hii : i = i₀
      · simpa [hii] using hi₀
      · have h := H.mul_mem (hHd i i₀ hii) hi₀
        rwa [mul_assoc, sgnAut_mul_self, mul_one] at h
    have ht : ∀ a b : Fin k, a ≠ b → permAut (p := p) (Equiv.swap a b) ∈ H :=
      fun a b _ => hHp _
    have hnorm : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
        IsSignedPerm ⇑(φ * u * φ⁻¹) :=
      fun u hu => hHs _ (hφ u (mem_of_isSignedPerm hs ht hu))
    have hnorm' : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
        IsSignedPerm ⇑(φ⁻¹ * u * φ) :=
      fun u hu => hHs _ (hφ' u (mem_of_isSignedPerm hs ht hu))
    exact exists_isSignedPerm_pow hp hp2 (by omega) hnorm hnorm'
  ·
    push Not at hA
    have hmul : ∀ i : Fin k,
        ∃ (j : Fin k) (x : ZMod p), x ≠ 0 ∧ φ (δ i) = Pi.mulSingle j (ofAdd x) :=
      fun i => exists_mulSingle_of_normalizes_dk hp hp2 hk hHs hHd hHp hA hφ hφ' i
    choose j c hc hjc using hmul
    have hperm : ∀ i i' : Fin k, i ≠ i' →
        IsSignedPerm ⇑(φ * permAut (p := p) (Equiv.swap i i') * φ⁻¹) :=
      fun i i' _ => hHs _ (hφ _ (hHp _))
    exact exists_isSignedPerm_pow_of_mulSingle hp (by omega) hc hjc hperm

end CFSG.StandardType.OrthExcEven

end

