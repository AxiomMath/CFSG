module

public import CFSG.Quasithin.Background.HPair
public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin

namespace H

namespace PairG

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

section Basic

variable {ι : Type} {K : Type} [Field K]

abbrev PairMod (ι K : Type) [Field K] := StdMod ι K × StdMod ι K

@[expose] def pairAut (a b : MulAut (StdMod ι K)) : MulAut (PairMod ι K) :=
  MulEquiv.prodCongr a b

@[simp] theorem pairAut_apply (a b : MulAut (StdMod ι K)) (x : PairMod ι K) :
    pairAut a b x = (a x.1, b x.2) := rfl

theorem pairAut_mul (a b a' b' : MulAut (StdMod ι K)) :
    pairAut a b * pairAut a' b' = pairAut (a * a') (b * b') := rfl

theorem pairAut_one : pairAut (1 : MulAut (StdMod ι K)) 1 = 1 := rfl

theorem pairAut_inv (a b : MulAut (StdMod ι K)) : (pairAut a b)⁻¹ = pairAut a⁻¹ b⁻¹ := rfl

theorem pairAut_pow (a b : MulAut (StdMod ι K)) (k : ℕ) :
    pairAut a b ^ k = pairAut (a ^ k) (b ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, pairAut_mul, ← pow_succ, ← pow_succ]

theorem pairAut_injective {a b c d : MulAut (StdMod ι K)} (h : pairAut a b = pairAut c d) :
    a = c ∧ b = d := by
  constructor
  · refine MulEquiv.ext fun v => ?_
    have := congrArg (fun z : MulAut (PairMod ι K) => (z (v, 1)).1) h
    simpa using this
  · refine MulEquiv.ext fun w => ?_
    have := congrArg (fun z : MulAut (PairMod ι K) => (z (1, w)).2) h
    simpa using this

variable (ι K) in
@[expose] def V₁ : Subgroup (PairMod ι K) := (⊤ : Subgroup _).prod ⊥

variable (ι K) in
@[expose] def V₂ : Subgroup (PairMod ι K) := (⊥ : Subgroup _).prod ⊤

theorem mem_V₁ {x : PairMod ι K} : x ∈ V₁ ι K ↔ x.2 = 1 := by
  simp [V₁, Subgroup.mem_prod]

theorem mem_V₂ {x : PairMod ι K} : x ∈ V₂ ι K ↔ x.1 = 1 := by
  simp [V₂, Subgroup.mem_prod]

theorem V₁_inf_V₂ : V₁ ι K ⊓ V₂ ι K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  rw [mem_V₁] at h1
  rw [mem_V₂] at h2
  exact Prod.ext h2 h1

theorem V₁_sup_V₂ : V₁ ι K ⊔ V₂ ι K = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  refine Subgroup.mem_sup.mpr ⟨(a, 1), mem_V₁.mpr rfl, (1, b), mem_V₂.mpr rfl, ?_⟩
  simp

theorem V₁_ne_V₂ [DecidableEq ι] [Nonempty ι] : V₁ ι K ≠ V₂ ι K := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 : ((Multiplicative.ofAdd (Pi.single i (1 : K)), 1) : PairMod ι K) ∈ V₁ ι K :=
    mem_V₁.mpr rfl
  rw [h, mem_V₂] at h1
  have := congrArg (fun x : StdMod ι K => Multiplicative.toAdd x i) h1
  simp at this

theorem V₁_ne_bot [DecidableEq ι] [Nonempty ι] : V₁ ι K ≠ ⊥ := by
  intro h
  have h1 : ((Multiplicative.ofAdd (Pi.single (Classical.arbitrary ι) (1 : K)), 1) :
      PairMod ι K) ∈ V₁ ι K := mem_V₁.mpr rfl
  rw [h, Subgroup.mem_bot] at h1
  have := congrArg (fun x : PairMod ι K => Multiplicative.toAdd x.1 (Classical.arbitrary ι)) h1
  simp at this

theorem V₂_ne_bot [DecidableEq ι] [Nonempty ι] : V₂ ι K ≠ ⊥ := by
  intro h
  have h1 : ((1, Multiplicative.ofAdd (Pi.single (Classical.arbitrary ι) (1 : K))) :
      PairMod ι K) ∈ V₂ ι K := mem_V₂.mpr rfl
  rw [h, Subgroup.mem_bot] at h1
  have := congrArg (fun x : PairMod ι K => Multiplicative.toAdd x.2 (Classical.arbitrary ι)) h1
  simp at this

theorem map_V₁_pairAut (a b : MulAut (StdMod ι K)) :
    (V₁ ι K).map (pairAut a b).toMonoidHom = V₁ ι K := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : v.2 = 1 := mem_V₁.mp hv
    rw [mem_V₁]
    change b v.2 = 1
    rw [hv', map_one]
  · intro v hv
    have hv' : v.2 = 1 := mem_V₁.mp hv
    refine ⟨(pairAut a b)⁻¹ v, ?_, ?_⟩
    · show (pairAut a b)⁻¹ v ∈ V₁ ι K
      rw [mem_V₁]
      change b⁻¹ v.2 = 1
      rw [hv', map_one]
    · change pairAut a b ((pairAut a b)⁻¹ v) = v
      exact MulEquiv.apply_symm_apply _ v

@[expose] def pairHom₂ (ι K : Type) [Field K] :
    MulAut (StdMod ι K) × MulAut (StdMod ι K) →* MulAut (PairMod ι K) where
  toFun p := pairAut p.1 p.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def pairSub (ι K : Type) [Field K] : Subgroup (MulAut (PairMod ι K)) :=
  (pairHom₂ ι K).range

theorem pairAut_mem_pairSub (a b : MulAut (StdMod ι K)) : pairAut a b ∈ pairSub ι K :=
  ⟨(a, b), rfl⟩

theorem mem_pairSub_iff {x : MulAut (PairMod ι K)} :
    x ∈ pairSub ι K ↔ ∃ a b : MulAut (StdMod ι K), x = pairAut a b := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact pairAut_mem_pairSub a b

theorem exists_pairAut_of_map {x : MulAut (PairMod ι K)}
    (h1 : (V₁ ι K).map x.toMonoidHom = V₁ ι K) (h2 : (V₂ ι K).map x.toMonoidHom = V₂ ι K) :
    ∃ a b : MulAut (StdMod ι K), x = pairAut a b := by
  have hid : x⁻¹.toMonoidHom.comp x.toMonoidHom = MonoidHom.id (PairMod ι K) :=
    MonoidHom.ext fun v => by simp
  have hinv1 : (V₁ ι K).map x⁻¹.toMonoidHom = V₁ ι K := by
    conv_lhs => rw [← h1]
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  have hinv2 : (V₂ ι K).map x⁻¹.toMonoidHom = V₂ ι K := by
    conv_lhs => rw [← h2]
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  have m1 : ∀ (y : MulAut (PairMod ι K)), (V₁ ι K).map y.toMonoidHom = V₁ ι K →
      ∀ v : StdMod ι K, y (v, 1) = ((y (v, 1)).1, 1) := by
    intro y hy v
    have : y (v, 1) ∈ V₁ ι K := by rw [← hy]; exact ⟨(v, 1), mem_V₁.mpr rfl, rfl⟩
    exact Prod.ext rfl (mem_V₁.mp this)
  have m2 : ∀ (y : MulAut (PairMod ι K)), (V₂ ι K).map y.toMonoidHom = V₂ ι K →
      ∀ w : StdMod ι K, y (1, w) = (1, (y (1, w)).2) := by
    intro y hy w
    have : y (1, w) ∈ V₂ ι K := by rw [← hy]; exact ⟨(1, w), mem_V₂.mpr rfl, rfl⟩
    exact Prod.ext (mem_V₂.mp this) rfl
  let x₁ : MulAut (StdMod ι K) :=
    { toFun := fun v => (x (v, 1)).1
      invFun := fun v => (x⁻¹ (v, 1)).1
      left_inv := fun v => by
        change (x⁻¹ ((x (v, 1)).1, 1)).1 = v
        rw [← m1 x h1 v]
        simp
      right_inv := fun v => by
        change (x ((x⁻¹ (v, 1)).1, 1)).1 = v
        rw [← m1 x⁻¹ hinv1 v]
        simp
      map_mul' := fun v w => by
        rw [show ((v * w, 1) : PairMod ι K) = (v, 1) * (w, 1) by simp, map_mul]
        rfl }
  let x₂ : MulAut (StdMod ι K) :=
    { toFun := fun w => (x (1, w)).2
      invFun := fun w => (x⁻¹ (1, w)).2
      left_inv := fun w => by
        change (x⁻¹ (1, (x (1, w)).2)).2 = w
        rw [← m2 x h2 w]
        simp
      right_inv := fun w => by
        change (x (1, (x⁻¹ (1, w)).2)).2 = w
        rw [← m2 x⁻¹ hinv2 w]
        simp
      map_mul' := fun v w => by
        rw [show ((1, v * w) : PairMod ι K) = (1, v) * (1, w) by simp, map_mul]
        rfl }
  refine ⟨x₁, x₂, MulEquiv.ext fun ⟨v, w⟩ => Prod.ext ?_ ?_⟩
  · change (x (v, w)).1 = (x (v, 1)).1
    rw [show ((v, w) : PairMod ι K) = (v, 1) * (1, w) by simp, map_mul, Prod.fst_mul,
      m2 x h2 w, mul_one]
  · change (x (v, w)).2 = (x (1, w)).2
    rw [show ((v, w) : PairMod ι K) = (v, 1) * (1, w) by simp, map_mul, Prod.snd_mul,
      m1 x h1 v, one_mul]

theorem eq_one_of_fix_of_map_V₂ {x : MulAut (PairMod ι K)}
    (h : (V₁ ι K).map x.toMonoidHom = V₂ ι K) {v : PairMod ι K} (hv : v ∈ V₁ ι K)
    (hxv : x v = v) : v = 1 := by
  have h2 : x v ∈ V₂ ι K := by rw [← h]; exact ⟨v, hv, rfl⟩
  rw [hxv] at h2
  have : v ∈ V₁ ι K ⊓ V₂ ι K := ⟨hv, h2⟩
  rwa [V₁_inf_V₂, Subgroup.mem_bot] at this

theorem card_fix_pairAut (a b : MulAut (StdMod ι K)) :
    Nat.card {x : PairMod ι K // pairAut a b x = x} =
      Nat.card {v : StdMod ι K // a v = v} * Nat.card {w : StdMod ι K // b w = w} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun x => (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), Prod.ext p.1.2 p.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }

end Basic

section Img

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
variable (Γ : Subgroup (GL ι K)) (θ : ↥Γ →* ↥Γ)

@[expose] def pairHom : ↥Γ →* MulAut (PairMod ι K) where
  toFun γ := pairAut (natAut Γ γ) (natAut Γ (θ γ))
  map_one' := by simp only [map_one]; rfl
  map_mul' γ δ := by simp only [map_mul, pairAut_mul]

theorem pairHom_apply (γ : ↥Γ) : pairHom Γ θ γ = pairAut (natAut Γ γ) (natAut Γ (θ γ)) := rfl

@[expose] def pairImg : Subgroup (MulAut (PairMod ι K)) := (pairHom Γ θ).range

abbrev pairNorm : Subgroup (MulAut (PairMod ι K)) :=
  Subgroup.normalizer (pairImg Γ θ : Set (MulAut (PairMod ι K)))

theorem pairHom_mem_pairImg (γ : ↥Γ) : pairHom Γ θ γ ∈ pairImg Γ θ := ⟨γ, rfl⟩

theorem pairImg_le_pairNorm : pairImg Γ θ ≤ pairNorm Γ θ := Subgroup.le_normalizer

@[expose] def IsNatIrr (Γ : Subgroup (GL ι K)) : Prop :=
  ∀ U : AddSubgroup (ι → K), (∀ γ ∈ Γ, ∀ u ∈ U, (γ : Matrix ι ι K) *ᵥ u ∈ U) → U = ⊥ ∨ U = ⊤

theorem isInv_V₁ : Pair.IsInv (pairImg Γ θ) (V₁ ι K) := by
  rintro _ ⟨g, rfl⟩ x hx
  rw [mem_V₁] at hx ⊢
  rw [pairHom_apply, pairAut_apply, hx, map_one]

theorem isInv_V₂ : Pair.IsInv (pairImg Γ θ) (V₂ ι K) := by
  rintro _ ⟨g, rfl⟩ x hx
  rw [mem_V₂] at hx ⊢
  rw [pairHom_apply, pairAut_apply, hx, map_one]

variable {Γ θ}

private theorem isIrr_aux (hΓ : IsNatIrr Γ) {W U : Subgroup (PairMod ι K)}
    (f : StdMod ι K →* PairMod ι K) (g : PairMod ι K → StdMod ι K)
    (hW : ∀ x, x ∈ W ↔ f (g x) = x) (hUW : U ≤ W)
    (hU : ∀ γ ∈ Γ, ∀ v, f v ∈ U → f (matAut γ v) ∈ U) : U = ⊥ ∨ U = W := by
  let U' : AddSubgroup (ι → K) :=
    { carrier := {v | f (Multiplicative.ofAdd v) ∈ U}
      add_mem' := fun {a b} ha hb => by
        change f (Multiplicative.ofAdd (a + b)) ∈ U
        rw [ofAdd_add, map_mul]
        exact U.mul_mem ha hb
      zero_mem' := by
        change f (Multiplicative.ofAdd 0) ∈ U
        rw [ofAdd_zero, map_one]
        exact U.one_mem
      neg_mem' := fun {a} ha => by
        change f (Multiplicative.ofAdd (-a)) ∈ U
        rw [ofAdd_neg, map_inv]
        exact U.inv_mem ha }
  have hU' : ∀ γ ∈ Γ, ∀ u ∈ U', (γ : Matrix ι ι K) *ᵥ u ∈ U' := fun γ hγ u hu => hU γ hγ _ hu
  have hmem : ∀ x ∈ W, x ∈ U ↔ Multiplicative.toAdd (g x) ∈ U' := by
    intro x hx
    change x ∈ U ↔ f (Multiplicative.ofAdd (Multiplicative.toAdd (g x))) ∈ U
    rw [ofAdd_toAdd, (hW x).mp hx]
  rcases hΓ U' hU' with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have h1 := (hmem x (hUW hx)).mp hx
    rw [h, AddSubgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, ← (hW x).mp (hUW hx)]
    have : g x = 1 := by
      rw [← ofAdd_toAdd (g x), h1, ofAdd_zero]
    rw [this, map_one]
  · right
    apply le_antisymm hUW
    intro x hx
    rw [hmem x hx, h]
    trivial

theorem isIrr_V₁ [Nonempty ι] (hΓ : IsNatIrr Γ) : Pair.IsIrr (pairImg Γ θ) (V₁ ι K) := by
  refine ⟨V₁_ne_bot, fun U hUV hU => ?_⟩
  refine isIrr_aux hΓ (MonoidHom.inl _ _) Prod.fst (fun x => ?_) hUV ?_
  · rw [mem_V₁]
    constructor
    · intro h
      exact Prod.ext rfl h.symm
    · intro h
      rw [← h]
      rfl
  · intro γ hγ v hv
    have := hU _ (pairHom_mem_pairImg Γ θ ⟨γ, hγ⟩) _ hv
    simp only [pairHom_apply, pairAut_apply, MonoidHom.inl_apply, map_one] at this
    exact this

theorem isIrr_V₂ [Nonempty ι] (hΓ : IsNatIrr Γ) (hθ : Function.Surjective θ) :
    Pair.IsIrr (pairImg Γ θ) (V₂ ι K) := by
  refine ⟨V₂_ne_bot, fun U hUV hU => ?_⟩
  refine isIrr_aux hΓ (MonoidHom.inr _ _) Prod.snd (fun x => ?_) hUV ?_
  · rw [mem_V₂]
    constructor
    · intro h
      exact Prod.ext h.symm rfl
    · intro h
      rw [← h]
      rfl
  · intro γ hγ v hv
    obtain ⟨δ, hδ⟩ := hθ ⟨γ, hγ⟩
    have := hU _ (pairHom_mem_pairImg Γ θ δ) _ hv
    simp only [pairHom_apply, pairAut_apply, MonoidHom.inr_apply, map_one, hδ] at this
    exact this

theorem map_V₁_eq_or [Nonempty ι] (hΓ : IsNatIrr Γ) (hθ : Function.Surjective θ)
    (hniso : ¬ Pair.IsoMod (pairImg Γ θ) (V₁ ι K) (V₂ ι K)) {x : MulAut (PairMod ι K)}
    (hx : x ∈ pairNorm Γ θ) :
    (V₁ ι K).map x.toMonoidHom = V₁ ι K ∨ (V₁ ι K).map x.toMonoidHom = V₂ ι K :=
  Pair.map_eq_or_map_eq V₁_inf_V₂ V₁_sup_V₂ (isInv_V₁ Γ θ) (isInv_V₂ Γ θ) (isIrr_V₁ hΓ)
    (isIrr_V₂ hΓ hθ) hniso hx

theorem map_V₂_eq [Nonempty ι] (hΓ : IsNatIrr Γ) (hθ : Function.Surjective θ)
    (hniso : ¬ Pair.IsoMod (pairImg Γ θ) (V₁ ι K) (V₂ ι K)) {x : MulAut (PairMod ι K)}
    (hx : x ∈ pairNorm Γ θ) (h1 : (V₁ ι K).map x.toMonoidHom = V₁ ι K) :
    (V₂ ι K).map x.toMonoidHom = V₂ ι K := by
  have hinf : V₂ ι K ⊓ V₁ ι K = ⊥ := by rw [inf_comm]; exact V₁_inf_V₂
  have hsup : V₂ ι K ⊔ V₁ ι K = ⊤ := by rw [sup_comm]; exact V₁_sup_V₂
  rcases Pair.map_eq_or_map_eq hinf hsup (isInv_V₂ Γ θ) (isInv_V₁ Γ θ) (isIrr_V₂ hΓ hθ)
    (isIrr_V₁ hΓ) (fun h => hniso (h.symm (isInv_V₂ Γ θ))) hx with h | h
  · exact h
  · exfalso
    apply V₁_ne_V₂ (ι := ι) (K := K)
    have := h.trans h1.symm
    exact (Subgroup.map_injective (f := x.toMonoidHom) x.injective this).symm

theorem exists_pairAut [Nonempty ι] (hΓ : IsNatIrr Γ) (hθ : Function.Surjective θ)
    (hniso : ¬ Pair.IsoMod (pairImg Γ θ) (V₁ ι K) (V₂ ι K)) {x : MulAut (PairMod ι K)}
    (hx : x ∈ pairNorm Γ θ) (h1 : (V₁ ι K).map x.toMonoidHom = V₁ ι K) :
    ∃ a b : MulAut (StdMod ι K), x = pairAut a b :=
  exists_pairAut_of_map h1 (map_V₂_eq hΓ hθ hniso hx h1)

theorem exists_conj {a b : MulAut (StdMod ι K)} (hx : pairAut a b ∈ pairNorm Γ θ) (γ : ↥Γ) :
    ∃ δ : ↥Γ, a * natAut Γ γ * a⁻¹ = natAut Γ δ ∧
      b * natAut Γ (θ γ) * b⁻¹ = natAut Γ (θ δ) := by
  obtain ⟨δ, hδ⟩ := (Subgroup.mem_normalizer_iff.mp hx (pairHom Γ θ γ)).mp
    (pairHom_mem_pairImg Γ θ γ)
  rw [pairHom_apply, pairHom_apply, pairAut_inv, pairAut_mul, pairAut_mul] at hδ
  obtain ⟨h1, h2⟩ := pairAut_injective hδ
  exact ⟨δ, h1.symm, h2.symm⟩

theorem fst_mem_natNorm {a b : MulAut (StdMod ι K)} (hx : pairAut a b ∈ pairNorm Γ θ) :
    a ∈ natNorm Γ := by
  have hx' : pairAut a⁻¹ b⁻¹ ∈ pairNorm Γ θ := by
    rw [← pairAut_inv]
    exact Subgroup.inv_mem _ hx
  rw [natNorm, Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨δ, h, -⟩ := exists_conj hx γ
    exact ⟨δ, h.symm⟩
  · rintro ⟨δ, hδ⟩
    obtain ⟨γ, h, -⟩ := exists_conj hx' δ
    refine ⟨γ, ?_⟩
    rw [← h, hδ, inv_inv]
    group

theorem snd_mem_natNorm (hθ : Function.Surjective θ) {a b : MulAut (StdMod ι K)}
    (hx : pairAut a b ∈ pairNorm Γ θ) : b ∈ natNorm Γ := by
  have hx' : pairAut a⁻¹ b⁻¹ ∈ pairNorm Γ θ := by
    rw [← pairAut_inv]
    exact Subgroup.inv_mem _ hx
  rw [natNorm, Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨γ₀, rfl⟩ := hθ γ
    obtain ⟨δ, -, h⟩ := exists_conj hx γ₀
    exact ⟨θ δ, h.symm⟩
  · rintro ⟨δ, hδ⟩
    obtain ⟨δ₀, rfl⟩ := hθ δ
    obtain ⟨γ, -, h⟩ := exists_conj hx' δ₀
    refine ⟨θ γ, ?_⟩
    rw [← h, hδ, inv_inv]
    group

end Img

end PairG

end H

end CFSG.Quasithin
