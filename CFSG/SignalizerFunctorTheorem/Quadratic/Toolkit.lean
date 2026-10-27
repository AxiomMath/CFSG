module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

section Basic

theorem inv_apply_apply' (g : LGL p V) (v : V) : g⁻¹ (g v) = v := g.symm_apply_apply v

theorem apply_inv_apply' (g : LGL p V) (v : V) : g (g⁻¹ v) = v := g.apply_symm_apply v

variable (A B : Subgroup (LGL p V))

theorem mem_fixSub {v : V} : v ∈ fixSub A ↔ ∀ a ∈ A, a v = v := Iff.rfl

theorem fixSub_anti (h : A ≤ B) : fixSub B ≤ fixSub A := fun _ hv a ha => hv a (h ha)

theorem fixSub_bot : fixSub (⊥ : Subgroup (LGL p V)) = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true]
  intro a ha
  rw [Subgroup.mem_bot] at ha
  rw [ha]
  rfl

theorem fixSub_eq_top_iff : fixSub A = ⊤ ↔ A = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ fixSub A := by rw [h]; trivial
    exact hv a ha
  · rintro rfl
    exact fixSub_bot

theorem commSub_mono (h : A ≤ B) : commSub A ≤ commSub B :=
  Submodule.span_mono fun _ ⟨a, ha, v, hw⟩ => ⟨a, h ha, v, hw⟩

theorem commSub_bot : commSub (⊥ : Subgroup (LGL p V)) = ⊥ := by
  unfold commSub
  rw [Submodule.span_eq_bot]
  rintro w ⟨a, ha, v, rfl⟩
  rw [Subgroup.mem_bot] at ha
  rw [ha]
  simp

theorem sub_mem_commSub {a : LGL p V} (ha : a ∈ A) (v : V) : a v - v ∈ commSub A :=
  Submodule.subset_span ⟨a, ha, v, rfl⟩

theorem commSub_le_iff {U : Submodule (ZMod p) V} :
    commSub A ≤ U ↔ ∀ a ∈ A, ∀ v : V, a v - v ∈ U := by
  unfold commSub
  rw [Submodule.span_le]
  constructor
  · intro h a ha v
    exact h ⟨a, ha, v, rfl⟩
  · rintro h w ⟨a, ha, v, rfl⟩
    exact h a ha v

theorem commSub_eq_bot_iff : commSub A = ⊥ ↔ A = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    apply LinearEquiv.ext
    intro v
    have hv : a v - v ∈ commSub A := sub_mem_commSub A ha v
    rw [h, Submodule.mem_bot, sub_eq_zero] at hv
    exact hv
  · rintro rfl
    exact commSub_bot

theorem map_mem_commSub {a : LGL p V} (ha : a ∈ A) {w : V} (hw : w ∈ commSub A) :
    a w ∈ commSub A := by
  unfold commSub at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, rfl⟩ := hx
    have h1 : (a * b) v - v ∈ commSub A := sub_mem_commSub A (A.mul_mem ha hb) v
    have h2 : a v - v ∈ commSub A := sub_mem_commSub A ha v
    have h3 := Submodule.sub_mem _ h1 h2
    have h4 : a (b v - v) = (a * b) v - v - (a v - v) := by
      rw [map_sub]
      change a (b v) - a v = a (b v) - v - (a v - v)
      abel
    rw [h4]
    exact h3
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem commSub_cj (g : LGL p V) : commSub (cj g A) = (commSub A).map (g : V →ₗ[ZMod p] V) := by
  apply le_antisymm
  · rw [commSub_le_iff]
    intro b hb v
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    refine Submodule.mem_map.mpr ⟨a (g⁻¹ v) - g⁻¹ v, sub_mem_commSub A ha _, ?_⟩
    change g (a (g⁻¹ v) - g⁻¹ v) = (g * a * g⁻¹) v - v
    rw [map_sub]
    change g (a (g⁻¹ v)) - g (g⁻¹ v) = g (a (g⁻¹ v)) - v
    rw [apply_inv_apply']
  · rw [Submodule.map_le_iff_le_comap, commSub_le_iff]
    intro a ha v
    rw [Submodule.mem_comap]
    have hb : g * a * g⁻¹ ∈ cj g A := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have := sub_mem_commSub (cj g A) hb (g v)
    convert this using 1
    change g (a v - v) = (g * a * g⁻¹) (g v) - g v
    rw [map_sub]
    change g (a v) - g v = g (a (g⁻¹ (g v))) - g v
    rw [inv_apply_apply']

theorem fixSub_cj (g : LGL p V) : fixSub (cj g A) = (fixSub A).map (g : V →ₗ[ZMod p] V) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨g⁻¹ v, ?_, ?_⟩
    · intro a ha
      have hb : g * a * g⁻¹ ∈ cj g A := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have := hv _ hb
      change g (a (g⁻¹ v)) = v at this
      have h2 := congrArg g.symm this
      rw [LinearEquiv.symm_apply_apply] at h2
      exact h2
    · exact LinearEquiv.apply_symm_apply g v
  · rintro ⟨y, hy, rfl⟩ b hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    change g (a (g⁻¹ (g y))) = g y
    rw [inv_apply_apply', hy a ha]

theorem card_cj (g : LGL p V) : Nat.card (cj g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_fixSub_cj (g : LGL p V) : Nat.card (fixSub (cj g A)) = Nat.card (fixSub A) := by
  rw [fixSub_cj]
  exact Nat.card_congr (g.submoduleMap (fixSub A)).symm.toEquiv

theorem map_mem_commSub_of_mem_normalizer {g : LGL p V}
    (hg : g ∈ Subgroup.normalizer (A : Set (LGL p V))) {w : V} (hw : w ∈ commSub A) :
    g w ∈ commSub A := by
  unfold commSub at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, rfl⟩ := hx
    have hb' : g * b * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg b).mp hb
    have h1 : (g * b * g⁻¹) (g v) - g v ∈ commSub A := sub_mem_commSub A hb' (g v)
    have h4 : g (b v - v) = (g * b * g⁻¹) (g v) - g v := by
      rw [map_sub]
      change g (b v) - g v = g (b (g⁻¹ (g v))) - g v
      rw [inv_apply_apply']
    rw [h4]
    exact h1
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem map_mem_fixSub_of_mem_normalizer {g : LGL p V}
    (hg : g ∈ Subgroup.normalizer (A : Set (LGL p V))) {w : V} (hw : w ∈ fixSub A) :
    g w ∈ fixSub A := by
  intro a ha
  have hb : g⁻¹ * a * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * a * g)).mp
    have h2 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [← h2] at ha
    exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * a * g)).mpr ha
  have h3 := hw _ hb
  change g⁻¹ (a (g w)) = w at h3
  have h4 := congrArg g h3
  rw [apply_inv_apply'] at h4
  exact h4

end Basic

section Coprime

variable [Fact p.Prime] [Finite V]

theorem card_eq_pow_finrank (U : Submodule (ZMod p) V) :
    Nat.card U = p ^ Module.finrank (ZMod p) U := by
  have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := U)
  simpa [Nat.card_zmod] using this

theorem card_modEq_card_fixed {P : Subgroup (LGL p V)} (hP : IsPGroup p P)
    (U : Submodule (ZMod p) V) (hinv : ∀ g ∈ P, ∀ u ∈ U, g u ∈ U) :
    Nat.card U ≡ Nat.card ↥(U ⊓ fixSub P) [MOD p] := by
  let _ : MulAction P U :=
    { smul := fun g u => ⟨(g : LGL p V) u, hinv g g.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun g h u => Subtype.ext rfl }
  have h := hP.card_modEq_card_fixedPoints U
  have hcard : Nat.card (MulAction.fixedPoints P U) = Nat.card ↥(U ⊓ fixSub P) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : V), ⟨x.1.2, fun g hg => ?_⟩⟩
        invFun := fun y => ⟨⟨(y : V), y.2.1⟩, fun g => ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have := x.2 ⟨g, hg⟩
      exact congrArg Subtype.val this
    · exact Subtype.ext (y.2.2 g g.2)
  rwa [hcard] at h

theorem exists_fixed_of_isPGroup {P : Subgroup (LGL p V)} (hP : IsPGroup p P)
    {U : Submodule (ZMod p) V} (hU : U ≠ ⊥) (hinv : ∀ g ∈ P, ∀ u ∈ U, g u ∈ U) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ g ∈ P, g u = u := by
  have h := card_modEq_card_fixed hP U hinv
  have hpd : p ∣ Nat.card U := by
    rw [card_eq_pow_finrank]
    apply dvd_pow_self
    intro h0
    apply hU
    exact (Submodule.finrank_eq_zero (S := U)).mp h0
  have h2 : p ∣ Nat.card ↥(U ⊓ fixSub P) :=
    Nat.modEq_zero_iff_dvd.mp (h.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpd))
  have hpos : 0 < Nat.card ↥(U ⊓ fixSub P) := Nat.card_pos
  have hp1 : 1 < Nat.card ↥(U ⊓ fixSub P) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos h2)
  have := Finite.one_lt_card_iff_nontrivial.mp hp1
  obtain ⟨⟨x, hx⟩, hx0⟩ := exists_ne (0 : ↥(U ⊓ fixSub P))
  refine ⟨x, hx.1, ?_, fun g hg => hx.2 g hg⟩
  intro h0
  apply hx0
  exact Subtype.ext h0

theorem isCompl_fixSub_commSub {Q : Subgroup (LGL p V)} (hQ : Nat.Coprime p (Nat.card Q)) :
    IsCompl (fixSub Q) (commSub Q) := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hunit : IsUnit ((Nat.card Q : ℕ) : ZMod p) := (ZMod.isUnit_iff_coprime _ _).mpr hQ.symm
  obtain ⟨u, hu⟩ := hunit
  let S : V →ₗ[ZMod p] V := ∑ q : Q, ((q : LGL p V) : V →ₗ[ZMod p] V)
  have hS : ∀ v, S v = ∑ q : Q, (q : LGL p V) v := fun v => by
    simp [S, LinearMap.sum_apply]
  have hS1 : ∀ v, ∀ q₀ ∈ Q, q₀ (S v) = S v := by
    intro v q₀ hq₀
    rw [hS, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨q₀, hq₀⟩ : Q)) _ _ (fun q => ?_)
    rfl
  have hS2 : ∀ v, ∀ q₀ ∈ Q, S (q₀ v) = S v := by
    intro v q₀ hq₀
    rw [hS, hS]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨q₀, hq₀⟩ : Q)) _ _ (fun q => ?_)
    rfl
  have hS3 : ∀ w ∈ fixSub Q, S w = ((Nat.card Q : ℕ) : ZMod p) • w := by
    intro w hw
    rw [hS]
    have : ∀ q : Q, (q : LGL p V) w = w := fun q => hw q q.2
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card]
    exact Nat.cast_smul_eq_nsmul (ZMod p) _ w |>.symm
  have hS4 : ∀ x ∈ commSub Q, S x = 0 := by
    intro x hx
    unfold commSub at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, v, rfl⟩ := hy
      rw [map_sub, hS2 v b hb, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hdec : ∀ v, v - (↑(u⁻¹) : ZMod p) • S v ∈ commSub Q := by
    intro v
    have h1 : ((Nat.card Q : ℕ) : ZMod p) • v - S v ∈ commSub Q := by
      have hsum : ∑ _q : Q, v = ((Nat.card Q : ℕ) : ZMod p) • v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, Nat.cast_smul_eq_nsmul]
      have : ((Nat.card Q : ℕ) : ZMod p) • v - S v = ∑ q : Q, (v - (q : LGL p V) v) := by
        rw [hS, Finset.sum_sub_distrib, hsum]
      rw [this]
      refine Submodule.sum_mem _ (fun q _ => ?_)
      have := sub_mem_commSub Q q.2 v
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
    have h2 := Submodule.smul_mem _ (↑(u⁻¹) : ZMod p) h1
    have h3 : (↑(u⁻¹) : ZMod p) • (((Nat.card Q : ℕ) : ZMod p) • v - S v) =
        v - (↑(u⁻¹) : ZMod p) • S v := by
      rw [smul_sub, smul_smul, ← hu, Units.inv_mul, one_smul]
    rwa [h3] at h2
  rw [isCompl_iff]
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have h1 := hS3 x hx1
    rw [hS4 x hx2, ← hu] at h1
    have h2 : (↑u : ZMod p) • x = 0 := h1.symm
    have h3 : (↑(u⁻¹) : ZMod p) • ((↑u : ZMod p) • x) = 0 := by rw [h2, smul_zero]
    rwa [smul_smul, Units.inv_mul, one_smul] at h3
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    refine ⟨(↑(u⁻¹) : ZMod p) • S v, ?_, v - (↑(u⁻¹) : ZMod p) • S v, hdec v, by abel⟩
    intro q hq
    rw [map_smul, hS1 v q hq]

theorem eq_bot_of_pq {P Q : Subgroup (LGL p V)} (hP : IsPGroup p P)
    (hQ : Nat.Coprime p (Nat.card Q)) (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    (hfix : fixSub P ≤ fixSub Q) : Q = ⊥ := by
  by_contra hne
  have hc : commSub Q ≠ ⊥ := fun h => hne ((commSub_eq_bot_iff Q).mp h)
  have hinv : ∀ g ∈ P, ∀ u ∈ commSub Q, g u ∈ commSub Q := by
    intro g hg u hu
    unfold commSub at hu ⊢
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, rfl⟩ := hx
      have h1 : b (g v) - g v ∈ Submodule.span (ZMod p) {w | ∃ a ∈ Q, ∃ v : V, w = a v - v} :=
        Submodule.subset_span ⟨b, hb, g v, rfl⟩
      have h2 : g (b v - v) = b (g v) - g v := by
        rw [map_sub]
        have := hcomm g hg b hb
        change g (b v) - g v = b (g v) - g v
        have h3 : (g * b) v = (b * g) v := by rw [this]
        exact congrArg (· - g v) h3
      rw [h2]
      exact h1
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  obtain ⟨u, hu, hu0, hufix⟩ := exists_fixed_of_isPGroup hP hc hinv
  have h1 : u ∈ fixSub P := hufix
  have h2 : u ∈ fixSub Q := hfix h1
  have hcompl := isCompl_fixSub_commSub hQ
  have := (Submodule.disjoint_def.mp hcompl.disjoint) u h2 hu
  exact hu0 this

omit [Finite V] in
theorem pow_eq_one_of_trivial {g : LGL p V} {W : Submodule (ZMod p) V}
    (h1 : ∀ w ∈ W, g w = w) (h2 : ∀ v : V, g v - v ∈ W) : g ^ p = 1 := by
  have key : ∀ (k : ℕ) (v : V), (g ^ k) v = v + (k : ZMod p) • (g v - v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ']
      change g ((g ^ k) v) = _
      rw [ih v, map_add, map_smul, h1 _ (h2 v)]
      push_cast
      rw [add_smul, one_smul]
      abel
  apply LinearEquiv.ext
  intro v
  rw [key p v]
  simp

omit [Finite V] in
theorem eq_bot_of_trivial {Q : Subgroup (LGL p V)} (hQ : Nat.Coprime p (Nat.card Q))
    {W : Submodule (ZMod p) V} (h1 : ∀ g ∈ Q, ∀ w ∈ W, g w = w)
    (h2 : ∀ g ∈ Q, ∀ v : V, g v - v ∈ W) : Q = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h := pow_eq_one_of_trivial (h1 g hg) (h2 g hg)
  have h3 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one h
  have h4 : orderOf (⟨g, hg⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
  have h5 : orderOf (⟨g, hg⟩ : Q) = orderOf g := Subgroup.orderOf_mk g hg
  rw [h5] at h4
  have h6 : orderOf g ∣ Nat.gcd p (Nat.card Q) := Nat.dvd_gcd h3 h4
  rw [Nat.Coprime.gcd_eq_one hQ] at h6
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h6)

theorem commSub_le_fixSub_of_card {A : Subgroup (LGL p V)} (hA : IsPGroup p A)
    (hc : Nat.card (commSub A) = p) : commSub A ≤ fixSub A := by
  have hinv : ∀ g ∈ A, ∀ u ∈ commSub A, g u ∈ commSub A :=
    fun g hg u hu => map_mem_commSub A hg hu
  have h := card_modEq_card_fixed hA (commSub A) hinv
  rw [hc] at h
  have hd : p ∣ Nat.card ↥(commSub A ⊓ fixSub A) := by
    have h0 : p ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl
    exact Nat.modEq_zero_iff_dvd.mp (h.symm.trans h0)
  have hle : Nat.card ↥(commSub A ⊓ fixSub A) ≤ Nat.card (commSub A) :=
    Nat.card_le_card_of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hpos : 0 < Nat.card ↥(commSub A ⊓ fixSub A) := Nat.card_pos
  have heq : Nat.card ↥(commSub A ⊓ fixSub A) = Nat.card (commSub A) := by
    rw [hc] at hle ⊢
    exact Nat.le_antisymm hle (Nat.le_of_dvd hpos hd)
  have hfr : Module.finrank (ZMod p) ↥(commSub A ⊓ fixSub A) =
      Module.finrank (ZMod p) (commSub A) := by
    have h1 := card_eq_pow_finrank (commSub A ⊓ fixSub A)
    have h2 := card_eq_pow_finrank (commSub A)
    rw [heq] at h1
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h1.symm.trans h2)
  have := Submodule.eq_of_le_of_finrank_eq (inf_le_left : commSub A ⊓ fixSub A ≤ commSub A) hfr
  exact inf_eq_left.mp this

end Coprime

end CFSG.SignalizerFunctorTheorem.Quadratic
