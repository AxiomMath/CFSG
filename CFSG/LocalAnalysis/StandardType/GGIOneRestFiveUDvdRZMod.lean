module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDvdEndNode
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType.IOneUDvdR

section Roots

variable {K : Type} [Field K]

theorem exists_isPrimitiveRoot_of_dvd [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) : ∃ ζ : K, IsPrimitiveRoot ζ p := by
  haveI := Fact.mk hp
  haveI : Fintype Kˣ := Fintype.ofFinite _
  have hcard : p ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    exact hpK
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hcard
  exact ⟨(x : K), IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hx)⟩

open scoped Classical in
noncomputable def dlog (p : ℕ) (ζ : K) (x : K) : ZMod p :=
  if h : ∃ i : Fin p, ζ ^ (i : ℕ) = x then (((Classical.choose h : Fin p) : ℕ) : ZMod p) else 0

section Prime

variable {p : ℕ} [hp : Fact p.Prime] {ζ : K}

theorem dlog_pow (hζ : IsPrimitiveRoot ζ p) (m : ℕ) : dlog p ζ (ζ ^ m) = (m : ZMod p) := by
  have hmod : m % p < p := Nat.mod_lt _ hp.out.pos
  have hmm : ζ ^ m = ζ ^ (m % p) := pow_eq_pow_mod m hζ.pow_eq_one
  have h : ∃ i : Fin p, ζ ^ (i : ℕ) = ζ ^ m := ⟨⟨m % p, hmod⟩, hmm.symm⟩
  unfold dlog
  rw [dif_pos h]
  have hi : ((Classical.choose h : Fin p) : ℕ) = m % p :=
    hζ.pow_inj (Classical.choose h).2 hmod ((Classical.choose_spec h).trans hmm)
  rw [hi, ZMod.natCast_mod]

theorem exists_lt_of_pow_eq_one (hζ : IsPrimitiveRoot ζ p) {x : K} (hx : x ^ p = 1) :
    ∃ i : ℕ, i < p ∧ x = ζ ^ i := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨i, hi, hx'⟩ := hζ.eq_pow_of_pow_eq_one hx
  exact ⟨i, hi, hx'.symm⟩

theorem dlog_mul (hζ : IsPrimitiveRoot ζ p) {x y : K} (hx : x ^ p = 1) (hy : y ^ p = 1) :
    dlog p ζ (x * y) = dlog p ζ x + dlog p ζ y := by
  obtain ⟨i, -, rfl⟩ := exists_lt_of_pow_eq_one hζ hx
  obtain ⟨j, -, rfl⟩ := exists_lt_of_pow_eq_one hζ hy
  rw [← pow_add, dlog_pow hζ, dlog_pow hζ, dlog_pow hζ, Nat.cast_add]

theorem dlog_one (hζ : IsPrimitiveRoot ζ p) : dlog p ζ (1 : K) = 0 := by
  have h := dlog_pow hζ 0
  rw [pow_zero, Nat.cast_zero] at h
  exact h

theorem dlog_injOn (hζ : IsPrimitiveRoot ζ p) {x y : K} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (h : dlog p ζ x = dlog p ζ y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := exists_lt_of_pow_eq_one hζ hx
  obtain ⟨j, hj, rfl⟩ := exists_lt_of_pow_eq_one hζ hy
  rw [dlog_pow hζ, dlog_pow hζ, ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  rw [h]

theorem dlog_eq_zero_iff (hζ : IsPrimitiveRoot ζ p) {x : K} (hx : x ^ p = 1) :
    dlog p ζ x = 0 ↔ x = 1 :=
  ⟨fun h => dlog_injOn hζ hx (one_pow p) (by rw [dlog_one hζ]; exact h),
    fun h => by rw [h, dlog_one hζ]⟩

theorem exists_zmod_span {G : Type*} [Group G] {d : ℕ} (hζ : IsPrimitiveRoot ζ p)
    (F : Finset (Fin d)) (f : G →* (Fin d → Kˣ))
    (hpow : ∀ (g : G) (k : Fin d), ((f g k : Kˣ) : K) ^ p = 1)
    (hF : ∀ (g : G) (k : Fin d), k ∉ F → f g k = 1)
    (hinj : Function.Injective f) (r : ℕ) (hr : p ^ r ≤ Nat.card G) :
    ∃ v : G → (F → ZMod p),
      (∀ g h, v (g * h) = v g + v h) ∧ (∀ g (k : F), v g k = 0 ↔ f g k = 1) ∧
      (∀ g (k : F), v g k = dlog p ζ ((f g k : Kˣ) : K)) ∧
      Function.Injective v ∧ (∀ g (m : ℕ), v (g ^ m) = (m : ZMod p) • v g) ∧
      ∃ M : Submodule (ZMod p) (F → ZMod p), (∀ x, x ∈ M ↔ ∃ g, v g = x) ∧
        r ≤ Module.finrank (ZMod p) M := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set v : G → (F → ZMod p) := fun g k => dlog p ζ ((f g k.1 : Kˣ) : K) with hv
  have hmul : ∀ g h, v (g * h) = v g + v h := by
    intro g h
    funext k
    simp only [hv, map_mul, Pi.mul_apply, Units.val_mul, Pi.add_apply]
    exact dlog_mul hζ (hpow g k.1) (hpow h k.1)
  have hv1 : v 1 = 0 := by
    funext k
    simp only [hv, map_one, Pi.one_apply, Units.val_one, Pi.zero_apply]
    exact dlog_one hζ
  have hzero : ∀ (g : G) (k : F), v g k = 0 ↔ f g k.1 = 1 := by
    intro g k
    simp only [hv]
    rw [dlog_eq_zero_iff hζ (hpow g k.1)]
    exact Units.val_eq_one
  have hvinj : Function.Injective v := by
    intro g h hgh
    apply hinj
    funext k
    by_cases hk : k ∈ F
    · apply Units.ext
      exact dlog_injOn hζ (hpow g k) (hpow h k) (congrFun hgh ⟨k, hk⟩)
    · rw [hF g k hk, hF h k hk]
  have hsmul : ∀ (g : G) (m : ℕ), v (g ^ m) = (m : ZMod p) • v g := by
    intro g m
    induction m with
    | zero => simp [hv1]
    | succ m ih =>
      rw [pow_succ, hmul, ih, Nat.cast_succ, add_smul, one_smul]
  let M : Submodule (ZMod p) (F → ZMod p) :=
    { carrier := Set.range v
      add_mem' := by
        rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
        exact ⟨g * h, hmul g h⟩
      zero_mem' := ⟨1, hv1⟩
      smul_mem' := by
        rintro c _ ⟨g, rfl⟩
        refine ⟨g ^ c.val, ?_⟩
        rw [hsmul, ZMod.natCast_zmod_val] }
  have hM_mem : ∀ x, x ∈ M ↔ ∃ g, v g = x := fun x => Iff.rfl
  haveI : Module.Finite (ZMod p) M := FiniteDimensional.finiteDimensional_submodule M
  have hbij : Function.Bijective (fun g : G => (⟨v g, ⟨g, rfl⟩⟩ : M)) := by
    refine ⟨fun g h hgh => hvinj (congrArg Subtype.val hgh), fun x => ?_⟩
    obtain ⟨g, hg⟩ := (hM_mem x.1).mp x.2
    exact ⟨g, Subtype.ext hg⟩
  have hcardM : Nat.card G = p ^ Module.finrank (ZMod p) M := by
    rw [Nat.card_congr (Equiv.ofBijective _ hbij),
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := M), Nat.card_zmod]
  refine ⟨v, hmul, hzero, fun g k => rfl, hvinj, hsmul, M, hM_mem, ?_⟩
  rw [hcardM] at hr
  exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hr

end Prime

end Roots

end CFSG.StandardType.IOneUDvdR

end
