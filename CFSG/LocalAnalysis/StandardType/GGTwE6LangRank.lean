module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LangFrame
public import CFSG.LieType.Steinberg.Exceptional.Fields

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

namespace TwE6Lang


section General

variable {k : Type*} [Field k]

variable (k) in
@[expose] noncomputable def torusConj (θ : k →+* k) (l : k) (ζ : kˣ) :
    (Fin (Tag.rank .E6) → Subgroup.zpowers ζ) →* e6Data_valid.minGroup k :=
  (MulAut.conj (langG k θ l)).toMonoidHom.comp
    ((torusHom k).comp (MonoidHom.compLeft (Subgroup.zpowers ζ).subtype _))

theorem torusConj_injective (θ : k →+* k) (l : k) (ζ : kˣ) :
    Function.Injective (torusConj k θ l ζ) := by
  intro w w' h
  simp only [torusConj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  have h2 := torusHom_injective ((MulAut.conj (langG k θ l)).injective h)
  funext a
  exact Subtype.ext (congrFun h2 a)

theorem exists_torusConj_eq (θ : k →+* k) (l : k) (ζ : kˣ)
    (w : Fin (Tag.rank .E6) → Subgroup.zpowers ζ) :
    ∃ v : Fin (Tag.rank .E6) → ℤ,
      torusConj k θ l ζ w = langG k θ l * torusPow ζ v * (langG k θ l)⁻¹ := by
  have hw : ∀ a, ∃ m : ℤ, ζ ^ m = (w a : kˣ) := fun a => Subgroup.mem_zpowers_iff.1 (w a).2
  choose v hv using hw
  refine ⟨v, ?_⟩
  have hfun : MonoidHom.compLeft (Subgroup.zpowers ζ).subtype (Fin (Tag.rank .E6)) w =
      fun a => ζ ^ v a := by
    funext a
    rw [MonoidHom.compLeft_apply, Function.comp_apply, Subgroup.coe_subtype, hv]
  rw [torusConj, MonoidHom.comp_apply, MonoidHom.comp_apply, hfun, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, torusPow]

theorem torusPow_neg_smul {ζ : kˣ} {m : ℤ} (hm : ζ ^ (m + 1) = 1) (v : Fin (Tag.rank .E6) → ℤ) :
    torusPow ζ (-(m • v)) = torusPow ζ v := by
  rw [torusPow, torusPow]
  congr 1
  funext a
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  calc ζ ^ (-(m * v a)) = ζ ^ ((m + 1) * (-v a) + v a) := by ring_nf
    _ = (ζ ^ (m + 1)) ^ (-v a) * ζ ^ v a := by rw [zpow_add, zpow_mul]
    _ = ζ ^ v a := by rw [hm, one_zpow, one_mul]

theorem torusConj_mem_fixedGroup (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l)
    {ζ : kˣ} {m : ℤ} (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (hm : ζ ^ (m + 1) = 1)
    (w : Fin (Tag.rank .E6) → Subgroup.zpowers ζ) : torusConj k θ l ζ w ∈ fixedGroup k θ := by
  obtain ⟨v, hv⟩ := exists_torusConj_eq θ l ζ w
  rw [hv, mem_fixedGroup, sigma_langG_conj_torusPow θ hθ hl hζ, torusPow_neg_smul hm]

variable (k) in
@[expose] noncomputable def langTorusE (θ : k →+* k) (l : k) (ζ : kˣ) :
    Subgroup (e6Data_valid.minGroup k) :=
  (torusConj k θ l ζ).range

theorem langTorusE_le_fixedGroup (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l)
    {ζ : kˣ} {m : ℤ} (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (hm : ζ ^ (m + 1) = 1) :
    langTorusE k θ l ζ ≤ fixedGroup k θ := by
  rintro _ ⟨w, rfl⟩
  exact torusConj_mem_fixedGroup θ hθ hl hζ hm w

theorem card_langTorusE (θ : k →+* k) (l : k) (ζ : kˣ) :
    Nat.card (langTorusE k θ l ζ) = orderOf ζ ^ 6 := by
  rw [langTorusE, ← Nat.card_congr (MonoidHom.ofInjective (torusConj_injective θ l ζ)).toEquiv,
    Nat.card_fun, Nat.card_zpowers, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem langTorusE_commute (θ : k →+* k) (l : k) (ζ : kˣ) {x y : e6Data_valid.minGroup k}
    (hx : x ∈ langTorusE k θ l ζ) (hy : y ∈ langTorusE k θ l ζ) : Commute x y := by
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', rfl⟩ := hy
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

theorem langTorusE_pow (θ : k →+* k) (l : k) {ζ : kˣ} {N : ℕ} (hN : ζ ^ N = 1)
    {x : e6Data_valid.minGroup k} (hx : x ∈ langTorusE k θ l ζ) : x ^ N = 1 := by
  obtain ⟨w, rfl⟩ := hx
  rw [← map_pow]
  convert map_one (torusConj k θ l ζ)
  funext a
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (w a).2
  apply Subtype.ext
  rw [Pi.pow_apply, SubgroupClass.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hN, one_zpow]
  rfl

end General

section Galois

variable {n : ℕ}

theorem units_map_frobQ (ζ : (GaloisField 2 (2 * n))ˣ) :
    Units.map (frobQ 2 n : GaloisField 2 (2 * n) →* GaloisField 2 (2 * n)) ζ =
      ζ ^ ((2 : ℤ) ^ n) := by
  apply Units.ext
  rw [Units.coe_map, show ((2 : ℤ) ^ n) = ((2 ^ n : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    Units.val_pow_eq_pow_val]
  exact frobQ_apply 2 n _

theorem card_units_galoisField (hn : 1 ≤ n) :
    Nat.card (GaloisField 2 (2 * n))ˣ = (2 ^ n) ^ 2 - 1 := by
  rw [Nat.card_units, GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]

theorem add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by rw [← Nat.sq_sub_sq, one_pow]⟩

theorem exists_generator (hn : 1 ≤ n) :
    ∃ g : (GaloisField 2 (2 * n))ˣ, orderOf g = (2 ^ n) ^ 2 - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 2 (2 * n))ˣ)
  exact ⟨g, by rw [hg, card_units_galoisField hn]⟩

theorem exists_frobQ_ne (hn : 1 ≤ n) : ∃ l : GaloisField 2 (2 * n), frobQ 2 n l ≠ l := by
  obtain ⟨g, hg⟩ := exists_generator hn
  refine ⟨g, fun h => ?_⟩
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq : g ^ (2 ^ n) = g := Units.ext (by rw [Units.val_pow_eq_pow_val, ← frobQ_apply, h])
  have h1 : g ^ (2 ^ n - 1) = 1 := by
    have e : g ^ (2 ^ n - 1) * g = 1 * g := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hq, one_mul]
    exact mul_right_cancel e
  have hd := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at hd
  have hle := Nat.le_of_dvd (by omega) hd
  have : 2 ^ n ≤ (2 ^ n) ^ 2 - 2 ^ n := by
    rw [sq]
    have : 2 ^ n * 2 ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_left _ h2
    omega
  omega

end Galois

end TwE6Lang

end CFSG.StandardType
