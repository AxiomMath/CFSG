module

public import CFSG.Quasithin.Background.Module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

section General

variable {G : Type*} [Group G]

@[expose] noncomputable def rk (W : Type*) [Group W] : ℕ := padicValNat 2 (Nat.card W)

@[expose] noncomputable def rkIdx (H : Subgroup G) : ℕ := padicValNat 2 H.index

theorem card_subgroup_pos [Finite G] (H : Subgroup G) : 0 < Nat.card H := Nat.card_pos

theorem rk_add_rkIdx [Finite G] (H : Subgroup G) : rk H + rkIdx H = rk G := by
  unfold rk rkIdx
  rw [← padicValNat.mul (card_subgroup_pos H).ne' H.index_ne_zero_of_finite, H.card_mul_index]

theorem padicValNat_two_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat 2 a ≤ padicValNat 2 b := by
  by_cases ha : a = 0
  · subst ha; exact absurd (zero_dvd_iff.mp h) hb
  · exact (padicValNat_dvd_iff_le hb).mp ((pow_padicValNat_dvd).trans h)

theorem rk_mono [Finite G] {H K : Subgroup G} (h : H ≤ K) : rk H ≤ rk K :=
  padicValNat_two_le_of_dvd (card_subgroup_pos K).ne' (Subgroup.card_dvd_of_le h)

theorem rk_bot : rk (⊥ : Subgroup G) = 0 := by simp [rk]

theorem rk_top : rk (⊤ : Subgroup G) = rk G := by simp [rk]

end General

omit [CommGroup V] in
theorem isPGroup_two_of_sq_eq_one {V : Type*} [Group V] (hV : ∀ v : V, v ^ 2 = 1) :
    IsPGroup 2 V :=
  fun v => ⟨1, by simpa using hV v⟩

omit [CommGroup V] in
theorem card_eq_two_pow_of_isPGroup {W : Type*} [Group W] [Finite W] (h : IsPGroup 2 W) :
    Nat.card W = 2 ^ rk W := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp h
  unfold rk
  rw [hn, padicValNat.prime_pow]

theorem card_eq_two_pow [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (H : Subgroup V) :
    Nat.card H = 2 ^ rk H :=
  card_eq_two_pow_of_isPGroup ((isPGroup_two_of_sq_eq_one hV).to_subgroup H)

theorem eq_of_le_of_rk_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {H K : Subgroup V} (h : H ≤ K)
    (hr : rk K ≤ rk H) : H = K := by
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [card_eq_two_pow hV H, card_eq_two_pow hV K]
  exact Nat.pow_le_pow_right (by norm_num) hr

omit [CommGroup V] in
theorem rk_eq_zero_iff_of_isPGroup {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : IsPGroup 2 H) : rk H = 0 ↔ H = ⊥ := by
  constructor
  · intro h0
    have := card_eq_two_pow_of_isPGroup h
    rw [h0, pow_zero] at this
    exact (Subgroup.card_eq_one).mp this
  · rintro rfl
    simp [rk]

theorem rk_eq_zero_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup V} :
    rk H = 0 ↔ H = ⊥ :=
  rk_eq_zero_iff_of_isPGroup ((isPGroup_two_of_sq_eq_one hV).to_subgroup H)

theorem card_sup_mul_card_inf (U W : Subgroup V) :
    Nat.card ↥(U ⊔ W) * Nat.card ↥(U ⊓ W) = Nat.card U * Nat.card W := by
  have h1 : W.relIndex (U ⊔ W) = W.relIndex U := Subgroup.relIndex_sup_right U W
  have h2 : W.relIndex (U ⊔ W) * Nat.card ↥(W ⊓ (U ⊔ W)) = Nat.card ↥(U ⊔ W) :=
    Subgroup.relIndex_mul_card W (U ⊔ W)
  have h3 : W.relIndex U * Nat.card ↥(W ⊓ U) = Nat.card U := Subgroup.relIndex_mul_card W U
  have h4 : W ⊓ (U ⊔ W) = W := inf_eq_left.mpr le_sup_right
  rw [h4, h1] at h2
  rw [inf_comm] at h3
  rw [← h2, ← h3]
  ring

theorem rk_sup_add_rk_inf [Finite V] (U W : Subgroup V) :
    rk ↥(U ⊔ W) + rk ↥(U ⊓ W) = rk U + rk W := by
  unfold rk
  rw [← padicValNat.mul (card_subgroup_pos _).ne' (card_subgroup_pos _).ne',
    ← padicValNat.mul (card_subgroup_pos _).ne' (card_subgroup_pos _).ne', card_sup_mul_card_inf]

theorem rkIdx_anti [Finite V] {H K : Subgroup V} (h : H ≤ K) : rkIdx K ≤ rkIdx H := by
  have := rk_add_rkIdx H
  have := rk_add_rkIdx K
  have := rk_mono h
  omega

@[expose] def commSub (W : Subgroup V) (X : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {c | ∃ x ∈ X, ∃ w ∈ W, x w * w⁻¹ = c}

theorem commV_eq_commSub (X : Subgroup (MulAut V)) : commV X = commSub ⊤ X := by
  unfold commV commSub
  congr 1
  ext c
  simp

theorem commSub_eq_bot_iff {W : Subgroup V} {X : Subgroup (MulAut V)} :
    commSub W X = ⊥ ↔ W ≤ fixV X := by
  constructor
  · intro h w hw x hx
    have : x w * w⁻¹ ∈ commSub W X := Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  · intro h
    rw [commSub, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    simp [h hw x hx]

theorem commSub_mono {W W' : Subgroup V} {X X' : Subgroup (MulAut V)} (hW : W ≤ W')
    (hX : X ≤ X') : commSub W X ≤ commSub W' X' := by
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, w, hw, rfl⟩
  exact ⟨x, hX hx, w, hW hw, rfl⟩

theorem commSub_le_of_invariant {W : Subgroup V} {X : Subgroup (MulAut V)}
    (h : ∀ x ∈ X, ∀ w ∈ W, x w ∈ W) : commSub W X ≤ W := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  exact W.mul_mem (h x hx w hw) (W.inv_mem hw)

@[expose] def commIter (W : Subgroup V) (X : Subgroup (MulAut V)) : ℕ → Subgroup V
  | 0 => W
  | k + 1 => commSub (commIter W X k) X

@[expose] def commSeries (X : Subgroup (MulAut V)) (k : ℕ) : Subgroup V := commIter ⊤ X k

theorem commIter_mono {W W' : Subgroup V} {X X' : Subgroup (MulAut V)} (hW : W ≤ W')
    (hX : X ≤ X') (k : ℕ) : commIter W X k ≤ commIter W' X' k := by
  induction k with
  | zero => exact hW
  | succ k ih => exact commSub_mono ih hX

theorem commSeries_mono {X X' : Subgroup (MulAut V)} (hX : X ≤ X') (k : ℕ) :
    commSeries X k ≤ commSeries X' k :=
  commIter_mono le_rfl hX k

theorem commSeries_one (X : Subgroup (MulAut V)) : commSeries X 1 = commV X := by
  simp [commSeries, commIter, commV_eq_commSub]

theorem isQuadratic_iff_commSeries_two (A : Subgroup (MulAut V)) :
    IsQuadratic A ↔ commSeries A 2 = ⊥ := by
  have : commSeries A 2 = commSub (commV A) A := by
    simp [commSeries, commIter, commV_eq_commSub]
  rw [this, commSub_eq_bot_iff]
  rfl

@[expose] def stabSub (U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ u : V, g u ∈ U ↔ u ∈ U}
  one_mem' := fun u => Iff.rfl
  mul_mem' := by
    intro a b ha hb u
    show a (b u) ∈ U ↔ u ∈ U
    rw [ha, hb]
  inv_mem' := by
    intro a ha u
    show a.symm u ∈ U ↔ u ∈ U
    rw [← ha (a.symm u)]
    simp

theorem mem_stabSub {U : Subgroup V} {g : MulAut V} :
    g ∈ stabSub U ↔ ∀ u : V, g u ∈ U ↔ u ∈ U := Iff.rfl

@[expose] def centSub (U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ u ∈ U, g u = u}
  one_mem' := fun u _ => rfl
  mul_mem' := by
    intro a b ha hb u hu
    show a (b u) = u
    rw [hb u hu, ha u hu]
  inv_mem' := by
    intro a ha u hu
    show a.symm u = u
    rw [MulEquiv.symm_apply_eq]
    exact (ha u hu).symm

theorem mem_centSub {U : Subgroup V} {g : MulAut V} :
    g ∈ centSub U ↔ ∀ u ∈ U, g u = u := Iff.rfl

theorem centSub_le_stabSub (U : Subgroup V) : centSub U ≤ stabSub U := by
  intro g hg u
  constructor
  · intro h
    have h1 : g (g u) = g u := hg _ h
    have h2 : g u = u := g.injective h1
    rw [← h2]; exact h
  · intro h
    rw [hg u h]; exact h

@[expose] def resAut (U : Subgroup V) (g : stabSub U) : MulAut U where
  toFun u := ⟨g.1 u, (g.2 u).2 u.2⟩
  invFun u := ⟨g.1.symm u, (g.2 _).1 (by simp)⟩
  left_inv u := by ext; simp
  right_inv u := by ext; simp
  map_mul' a b := by ext; simp

@[expose] def resHom (U : Subgroup V) : stabSub U →* MulAut U where
  toFun := resAut U
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl

theorem resHom_apply (U : Subgroup V) (g : stabSub U) (u : U) :
    ((resHom U g u : U) : V) = g.1 u := rfl

theorem ker_resHom (U : Subgroup V) :
    (resHom U).ker = (centSub U).subgroupOf (stabSub U) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centSub]
  constructor
  · intro h u hu
    exact congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : V)) h
  · intro h
    ext u
    exact h u u.2

@[expose] def autSub (X : Subgroup (MulAut V)) (U : Subgroup V) : Subgroup (MulAut U) :=
  (X.subgroupOf (stabSub U)).map (resHom U)

theorem mem_autSub {X : Subgroup (MulAut V)} {U : Subgroup V} {φ : MulAut U} :
    φ ∈ autSub X U ↔ ∃ g : stabSub U, (g : MulAut V) ∈ X ∧ resHom U g = φ := by
  simp [autSub, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem autSub_mono {X X' : Subgroup (MulAut V)} (h : X ≤ X') (U : Subgroup V) :
    autSub X U ≤ autSub X' U :=
  Subgroup.map_mono fun _ hg => h hg

theorem card_autSub_mul {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    Nat.card (autSub A U) * Nat.card ↥(A ⊓ centSub U) = Nat.card A := by
  have h1 : (resHom U).ker.relIndex (A.subgroupOf (stabSub U)) =
      Nat.card ((A.subgroupOf (stabSub U)).map (resHom U)) :=
    Subgroup.relIndex_ker (A.subgroupOf (stabSub U)) (resHom U)
  have h2 := Subgroup.relIndex_mul_card (resHom U).ker (A.subgroupOf (stabSub U))
  have h3 : (resHom U).ker ⊓ A.subgroupOf (stabSub U) =
      (A ⊓ centSub U).subgroupOf (stabSub U) := by
    ext g
    simp [ker_resHom, Subgroup.mem_subgroupOf, and_comm]
  have h4 : Nat.card (A.subgroupOf (stabSub U)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have h5 : Nat.card ↥((A ⊓ centSub U).subgroupOf (stabSub U)) = Nat.card ↥(A ⊓ centSub U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hA)).toEquiv
  rw [h1, h3, h5, h4] at h2
  exact h2

theorem mem_fixV_autSub {X : Subgroup (MulAut V)} {U : Subgroup V} {u : U} :
    u ∈ fixV (autSub X U) ↔ ∀ g ∈ X, g ∈ stabSub U → g (u : V) = u := by
  constructor
  · intro h g hg hgs
    have := h (resHom U ⟨g, hgs⟩) (mem_autSub.mpr ⟨⟨g, hgs⟩, hg, rfl⟩)
    exact congrArg (fun w : U => (w : V)) this
  · intro h φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    ext
    exact h g hg g.2

theorem map_subtype_fixV_autSub {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    (fixV (autSub A U)).map U.subtype = U ⊓ fixV A := by
  ext v
  simp only [Subgroup.mem_map, Subgroup.subtype_apply, Subgroup.mem_inf]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, fun g hg => (mem_fixV_autSub.mp hu) g hg (hA hg)⟩
  · rintro ⟨hvU, hv⟩
    exact ⟨⟨v, hvU⟩, mem_fixV_autSub.mpr fun g hg _ => hv g hg, rfl⟩

theorem rk_fixV_autSub {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    rk (fixV (autSub A U)) = rk ↥(U ⊓ fixV A) := by
  unfold rk
  rw [← map_subtype_fixV_autSub hA, Subgroup.card_map_of_injective U.subtype_injective]

end CFSG.Quasithin
