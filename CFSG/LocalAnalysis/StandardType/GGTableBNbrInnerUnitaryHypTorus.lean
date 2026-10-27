module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred

public section

namespace CFSG.StandardType

open Multiplicative Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n r p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def hypEntries (ζ : K) (t : Fin r → ZMod p) : HypIndex r 0 → K
  | .inl i => ζ ^ (t i).val
  | .inr (.inl k) => k.elim0
  | .inr (.inr i) => (ζ ^ (t i).val)⁻¹

theorem hypEntries_add {ζ : K} (hp : p.Prime) (hpow : ζ ^ p = 1) (t t' : Fin r → ZMod p) :
    hypEntries (r := r) ζ (t + t') = hypEntries ζ t * hypEntries ζ t' := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  funext x
  rcases x with i | k | i
  · simp only [hypEntries, Pi.add_apply, Pi.mul_apply, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hpow, pow_add]
  · exact k.elim0
  · simp only [hypEntries, Pi.add_apply, Pi.mul_apply, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hpow, pow_add, mul_inv]

theorem exists_hypTorusHom (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hbar : h.bar ζ = ζ) :
    ∃ ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 0, ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hbar_pow : ∀ m : ℕ, h.bar (ζ ^ m) = ζ ^ m := fun m => by rw [map_pow, hbar]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  let a : (Fin r → ZMod p) → Fin r → Kˣ :=
    fun t i => Units.mk0 (ζ ^ (t i).val) (pow_ne_zero _ hζ0)
  let d0 : Fin 0 → Kˣ := fun k => k.elim0
  have hd : ∀ k : Fin 0, h.norm (d0 k : K) = 1 := fun k => k.elim0
  have hratio : ∀ t, torusRatio h (a t) d0 = 1 := by
    intro t
    have hprod : (∏ i, (a t i : K) / h.bar (a t i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hb : h.bar (a t i : K) = (a t i : K) := by
        rw [Units.val_mk0]
        exact hbar_pow _
      rw [hb]
      exact div_self (by rw [Units.val_mk0]; exact pow_ne_zero _ hζ0)
    rw [torusRatio, hprod, Finset.prod_eq_one (fun k _ => k.elim0), mul_one]
  have hex : ∀ t : Fin r → ZMod p, ∃ g : hypSU h r 0,
      (((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
        diagonal (hypEntries ζ t)) := by
    intro t
    obtain ⟨g, -, hg⟩ := torusMat_mem_hypSU (d := d0) h (a t) hd (hratio t)
    refine ⟨g, ?_⟩
    rw [hg]
    congr 1
    funext x
    rcases x with i | k | i
    · simp [torusEntries, hypEntries, a]
    · exact k.elim0
    · simp [torusEntries, hypEntries, a, hbar_pow]
  let g : (Fin r → ZMod p) → hypSU h r 0 := fun t => Classical.choose (hex t)
  have hg : ∀ t : Fin r → ZMod p,
      (((g t : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t) :=
    fun t => Classical.choose_spec (hex t)
  have hmul : ∀ t t' : Fin r → ZMod p, g (t + t') = g t * g t' := by
    intro t t'
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hg, hg, hg, diagonal_mul_diagonal,
      hypEntries_add hp hζ.pow_eq_one]
    rfl
  refine ⟨MonoidHom.mk' (fun m : Multiplicative (Fin r → ZMod p) =>
    g (Multiplicative.toAdd m)) ?_, ?_⟩
  · intro m m'
    exact hmul (Multiplicative.toAdd m) (Multiplicative.toAdd m')
  · intro t
    exact hg t

theorem hypEntries_hypPartner (ζ : K) (t : Fin r → ZMod p) (a : HypIndex r 0) :
    hypEntries ζ t (hypPartner a) = (hypEntries ζ t a)⁻¹ := by
  rcases a with i | k | i
  · rfl
  · exact k.elim0
  · simp [hypEntries]

theorem hypEntries_neg {ζ : K} (hp : p.Prime) (hpow : ζ ^ p = 1) (a : ZMod p) :
    ζ ^ ((-a).val) = (ζ ^ a.val)⁻¹ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h1 : (a + -a).val = 0 := by rw [add_neg_cancel, ZMod.val_zero]
  rw [ZMod.val_add] at h1
  have h2 : ζ ^ (a.val + (-a).val) = 1 := by
    rw [pow_eq_pow_mod _ hpow, h1, pow_zero]
  rw [pow_add] at h2
  exact eq_inv_of_mul_eq_one_right h2

theorem sumCongr_mem_hypWeyl (π : Equiv.Perm (Fin r)) :
    Equiv.sumCongr π π ∈ hypWeyl r := by
  rw [mem_hypWeyl]
  intro x
  rcases x with i | i <;> simp

theorem swapSet_mem_hypWeyl (M : Finset (Fin r)) : swapSet M ∈ hypWeyl r := by
  rw [mem_hypWeyl]
  intro x
  rcases x with i | i <;> by_cases hi : i ∈ M <;> simp [swapSet, hi]

theorem weylMat_mul_diagonal {f ε : ℕ} (h : UnitaryFieldData p f K) (c : K)
    (w : Equiv.Perm (Fin r ⊕ Fin r)) (d : HypIndex r ε → K) :
    weylMat h c w * diagonal d =
      diagonal (fun a => d ((weylPerm (ε := ε) w).symm a)) * weylMat h c w := by
  rw [weylMat, CFSG.LieType.Universal.SpecialLinear.signedPerm_mul_diagonal]

theorem exists_hypTorus_move (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hbar : h.bar ζ = ζ)
    (ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 0)
    (hι : ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t))
    (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ)
    (hη : ∀ i, η i ∈ Subgroup.zpowers (-1 : (ZMod p)ˣ)) :
    ∃ w ∈ Subgroup.normalizer (ι.range : Set (hypSU h r 0)), ∀ t : Fin r → ZMod p,
      w⁻¹ * ι (ofAdd t) * w = ι (ofAdd fun i => (η i : ZMod p) * t (π i)) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hηi : ∀ i, η i = 1 ∨ η i = -1 := by
    intro i
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hη i)
    rw [← hk]
    rcases Int.even_or_odd k with he | ho
    · exact Or.inl he.neg_one_zpow
    · exact Or.inr ho.neg_one_zpow
  let M : Finset (Fin r) := Finset.univ.filter fun i => η i = -1
  let w₀ : Equiv.Perm (Fin r ⊕ Fin r) := Equiv.sumCongr π π * swapSet M
  have hw₀ : w₀ ∈ hypWeyl r :=
    (hypWeyl r).mul_mem (sumCongr_mem_hypWeyl π) (swapSet_mem_hypWeyl M)
  have hw₀_inl : ∀ i, w₀ (.inl i) = if η i = -1 then .inr (π i) else .inl (π i) := by
    intro i
    show (Equiv.sumCongr π π) (if i ∈ M then Sum.inr i else Sum.inl i) =
      if η i = -1 then Sum.inr (π i) else Sum.inl (π i)
    by_cases hneg : η i = -1
    · have hiM : i ∈ M := by simp [M, hneg]
      rw [if_pos hiM, if_pos hneg]
      rfl
    · have hiM : i ∉ M := by simp [M, hneg]
      rw [if_neg hiM, if_neg hneg]
      rfl
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  let w : hypSU h r 0 := weylElt h hc hc0 hw₀
  have hwmat : (((w : hypSU h r 0) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) = weylMat h c w₀ :=
    coe_weylElt h hc hc0 hw₀
  let mv : (Fin r → ZMod p) → Fin r → ZMod p := fun s i => (η i : ZMod p) * s (π i)
  let imv : (Fin r → ZMod p) → Fin r → ZMod p :=
    fun s j => (η (π.symm j) : ZMod p) * s (π.symm j)
  have hmv_imv : ∀ s, mv (imv s) = s := by
    intro s
    funext i
    have hsq : (η i : ZMod p) * (η i : ZMod p) = 1 := by
      rcases hηi i with h | h
      · rw [h, Units.val_one, one_mul]
      · rw [h, Units.val_neg, Units.val_one, neg_mul_neg, one_mul]
    show (η i : ZMod p) * imv s (π i) = s i
    rw [show imv s (π i) = (η i : ZMod p) * s i from by
      simp [imv, Equiv.symm_apply_apply]]
    rw [← mul_assoc, hsq, one_mul]
  have hfun : ∀ t, hypEntries ζ t =
      fun a => hypEntries ζ (mv t) ((weylPerm (ε := 0) w₀).symm a) := by
    intro t
    have hpt_inl : ∀ i, hypEntries ζ t (weylPerm (ε := 0) w₀ (.inl i)) =
        hypEntries ζ (mv t) (.inl i) := by
      intro i
      rw [weylPerm_inl, hw₀_inl i]
      split_ifs with hneg
      · change (ζ ^ (t (π i)).val)⁻¹ = ζ ^ ((mv t i).val)
        have hmvi : mv t i = -(t (π i)) := by
          simp [mv, hneg, neg_one_mul]
        rw [hmvi, hypEntries_neg hp hζ.pow_eq_one]
      · change ζ ^ (t (π i)).val = ζ ^ ((mv t i).val)
        have hone : η i = 1 := by
          rcases hηi i with h | h
          · exact h
          · exact absurd h hneg
        rw [show mv t i = t (π i) from by simp [mv, hone]]
    have hpt : ∀ b, hypEntries ζ t (weylPerm (ε := 0) w₀ b) = hypEntries ζ (mv t) b := by
      intro b
      rcases b with i | k | i
      · exact hpt_inl i
      · exact k.elim0
      · have h1 : weylPerm (ε := 0) w₀ (.inr (.inr i)) =
            hypPartner (weylPerm (ε := 0) w₀ (.inl i)) := by
          rw [weylPerm_inr_inr, apply_inr_of_mem_hypWeyl hw₀, lineCoord_swap, ← weylPerm_inl]
        rw [h1, hypEntries_hypPartner, hpt_inl i, ← hypEntries_hypPartner]
        rfl
    funext a
    simpa using hpt ((weylPerm (ε := 0) w₀).symm a)
  have hmul_eq : ∀ t, ι (ofAdd t) * w = w * ι (ofAdd (mv t)) := by
    intro t
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      hι t, hι (mv t), hwmat, hfun t, weylMat_mul_diagonal]
  have hmove_inv : ∀ t, w⁻¹ * ι (ofAdd t) * w = ι (ofAdd (mv t)) := by
    intro t
    calc w⁻¹ * ι (ofAdd t) * w = w⁻¹ * (ι (ofAdd t) * w) := by rw [mul_assoc]
      _ = w⁻¹ * (w * ι (ofAdd (mv t))) := by rw [hmul_eq t]
      _ = ι (ofAdd (mv t)) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hmul_inv' : ∀ s, w * ι (ofAdd s) * w⁻¹ = ι (ofAdd (imv s)) := by
    intro s
    have h := hmove_inv (imv s)
    rw [hmv_imv s] at h
    calc w * ι (ofAdd s) * w⁻¹ = w * (w⁻¹ * ι (ofAdd (imv s)) * w) * w⁻¹ := by rw [← h]
      _ = ι (ofAdd (imv s)) := by group
  refine ⟨w, ?_, ?_⟩
  · rw [Subgroup.mem_set_normalizer_iff]
    intro h'
    constructor
    · intro hh'
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hh'
      refine MonoidHom.mem_range.mpr ⟨ofAdd (imv s.toAdd), ?_⟩
      have hs' : ι (ofAdd s.toAdd) = h' := by rw [ofAdd_toAdd]; exact hs
      calc ι (ofAdd (imv s.toAdd)) = w * ι (ofAdd s.toAdd) * w⁻¹ := (hmul_inv' s.toAdd).symm
        _ = w * h' * w⁻¹ := by rw [hs']
    · intro hh'
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hh'
      refine MonoidHom.mem_range.mpr ⟨ofAdd (mv s.toAdd), ?_⟩
      have hs' : w * h' * w⁻¹ = ι (ofAdd s.toAdd) := by rw [ofAdd_toAdd]; exact hs.symm
      calc ι (ofAdd (mv s.toAdd)) = w⁻¹ * ι (ofAdd s.toAdd) * w := (hmove_inv s.toAdd).symm
        _ = w⁻¹ * (w * h' * w⁻¹) * w := by rw [← hs']
        _ = h' := by group
  · intro t
    exact hmove_inv t

theorem hypTorusHom_injective (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 0)
    (hι : ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t)) :
    Function.Injective ι := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hker : ∀ t : Fin r → ZMod p, ι (ofAdd t) = 1 → t = 0 := by
    intro t ht
    funext i
    have hmat : diagonal (hypEntries ζ t) = (1 : Matrix (HypIndex r 0) (HypIndex r 0) K) := by
      have h1 := (hι t).symm
      rw [ht] at h1
      simpa using h1
    have hentry := congrFun (congrFun hmat (.inl i)) (.inl i)
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hentry
    have hpow : ζ ^ (t i).val = 1 := by simpa [hypEntries] using hentry
    exact (ZMod.val_eq_zero (t i)).mp
      (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd _).mp hpow) (ZMod.val_lt (t i)))
  intro x y hxy
  have hz : ι (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hzt : (x * y⁻¹).toAdd = 0 := by
    rw [← ofAdd_toAdd (x * y⁻¹)] at hz
    exact hker _ hz
  rw [toAdd_mul, toAdd_inv] at hzt
  rw [← sub_eq_add_neg] at hzt
  exact Multiplicative.toAdd.injective (sub_eq_zero.mp hzt)

theorem card_range_hypTorusHom (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 0)
    (hι : ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t)) :
    Nat.card ι.range = p ^ r := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hinj := hypTorusHom_injective h hp hζ ι hι
  have hcard : Nat.card ι.range = Nat.card (Multiplicative (Fin r → ZMod p)) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp [Nat.card_zmod, Finset.prod_const]

theorem zpowers_neg_one_ne_bot (hp : p.Prime) (hp2 : p ≠ 2) :
    Subgroup.zpowers (-1 : (ZMod p)ˣ) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  rw [Ne, Subgroup.zpowers_eq_bot]
  intro h1
  exact ZMod.neg_one_ne_one (Units.ext_iff.mp h1)

theorem ggWeylIrred_hypTorusRange (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hbar : h.bar ζ = ζ)
    (ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 0)
    (hι : ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t)) :
    GGWeylIrred ι.range := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ggWeylIrred_of_monomialModel ι (Subgroup.zpowers (-1 : (ZMod p)ˣ))
    (zpowers_neg_one_ne_bot hp hp2) fun π η hη =>
      exists_hypTorus_move h hp hp2 hζ hbar ι hι π η hη

end CFSG.StandardType

end
