module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Chi


public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup

variable {G : Type} [Group G] {n : ℕ}

structure IsChiEmb₁ (ζ : GaloisField 2 n) (d : G) (C S : Subgroup G) (x : ZMod (2 ^ n - 1))
    (β : G → GaloisField 2 n) : Prop where
  map_mul : ∀ s ∈ S, ∀ t ∈ S, β (s * t) = β s + β t
  eq_zero_iff : ∀ s ∈ S, β s = 0 ↔ s ∈ C
  conj : ∀ s ∈ S, β (d * s * d⁻¹) = ζ ^ x.val * β s

namespace IsChiEmb₁

variable {ζ : GaloisField 2 n} {d : G} {C S : Subgroup G} {x : ZMod (2 ^ n - 1)}
  {β : G → GaloisField 2 n}

theorem toIsChiEmb_self (h : IsChiEmb₁ ζ d C S x β) : IsChiEmb ζ d d C S (x, x) β :=
  ⟨h.map_mul, h.eq_zero_iff, h.conj, h.conj⟩

theorem conj_of_trivial (h : IsChiEmb₁ ζ d C S x β) (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (hS : d ∈ normalizer (S : Set G)) (hCS : C ≤ S) (hd : d ^ (2 ^ n - 1) = 1) {e : G}
    {m : ZMod (2 ^ n - 1)}
    (htriv : ∀ s ∈ S, (d ^ (-m).val * e) * s * (d ^ (-m).val * e)⁻¹ * s⁻¹ ∈ C) :
    ∀ s ∈ S, β (e * s * e⁻¹) = ζ ^ (m * x).val * β s := by
  intro s hs
  have : NeZero (2 ^ n - 1) := ⟨by have := Nat.one_lt_two_pow hn; omega⟩
  have hdvd : 2 ^ n - 1 ∣ m.val + (-m).val := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id, add_neg_cancel]
  obtain ⟨k, hk⟩ := hdvd
  set t := d ^ (-m).val * e with ht
  have he : e = d ^ m.val * t := by
    rw [ht, ← mul_assoc, ← pow_add, hk, pow_mul, hd, one_pow, one_mul]
  set c := t * s * t⁻¹ * s⁻¹ with hc
  have hcC : c ∈ C := htriv s hs
  have hes : e * s * e⁻¹ =
      (d ^ m.val * c * (d ^ m.val)⁻¹) * (d ^ m.val * s * (d ^ m.val)⁻¹) := by
    rw [he, hc]
    group
  have h' := h.toIsChiEmb_self
  obtain ⟨hc1, hc2⟩ := h'.conj₁_pow hS m.val c (hCS hcC)
  obtain ⟨hs1, hs2⟩ := h'.conj₁_pow hS m.val s hs
  rw [hes, h.map_mul _ hc1 _ hs1, hc2, hs2, (h.eq_zero_iff c (hCS hcC)).mpr hcC, mul_zero,
    zero_add, ← pow_mul]
  congr 1
  apply pow_eq_pow_of_natCast_eq hζ
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  ring

theorem toIsChiEmb {d₁ : G} (h : IsChiEmb₁ ζ d₁ C S x β) (hn : n ≠ 0)
    (hζ : orderOf ζ = 2 ^ n - 1) (hS : d₁ ∈ normalizer (S : Set G)) (hCS : C ≤ S)
    (hd : d₁ ^ (2 ^ n - 1) = 1) {d₂ : G} {m : ZMod (2 ^ n - 1)}
    (htriv : ∀ s ∈ S, (d₁ ^ (-m).val * d₂) * s * (d₁ ^ (-m).val * d₂)⁻¹ * s⁻¹ ∈ C) :
    IsChiEmb ζ d₁ d₂ C S (x, m * x) β :=
  ⟨h.map_mul, h.eq_zero_iff, h.conj, h.conj_of_trivial hn hζ hS hCS hd htriv⟩

theorem toIsChiEmb' {d₂ : G} (h : IsChiEmb₁ ζ d₂ C S x β) (hn : n ≠ 0)
    (hζ : orderOf ζ = 2 ^ n - 1) (hS : d₂ ∈ normalizer (S : Set G)) (hCS : C ≤ S)
    (hd : d₂ ^ (2 ^ n - 1) = 1) {d₁ : G} {m : ZMod (2 ^ n - 1)}
    (htriv : ∀ s ∈ S, (d₂ ^ (-m).val * d₁) * s * (d₂ ^ (-m).val * d₁)⁻¹ * s⁻¹ ∈ C) :
    IsChiEmb ζ d₁ d₂ C S (m * x, x) β :=
  ⟨h.map_mul, h.eq_zero_iff, h.conj_of_trivial hn hζ hS hCS hd htriv, h.conj⟩

end IsChiEmb₁

theorem commutator_mem_of_trivial {L K S C : Subgroup G} {t : G} (hSLC : S = (S ⊓ L) ⊔ C)
    (hSC : S ≤ normalizer (C : Set G)) (hKC : K ≤ C) (htC : t ∈ normalizer (C : Set G))
    (htL : ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ K) : ∀ s ∈ S, t * s * t⁻¹ * s⁻¹ ∈ C := by
  intro s hs
  have hs' : s ∈ (((S ⊓ L) ⊔ C : Subgroup G) : Set G) := by
    rw [← hSLC]
    exact hs
  rw [coe_mul_of_left_le_normalizer_right (S ⊓ L) C (inf_le_left.trans hSC)] at hs'
  obtain ⟨l, hl, c, hc, rfl⟩ := hs'
  have e : t * (l * c) * t⁻¹ * (l * c)⁻¹ =
      (t * l * t⁻¹ * l⁻¹) * (l * (t * c * t⁻¹ * c⁻¹) * l⁻¹) := by group
  rw [e]
  refine C.mul_mem (hKC (htL l (mem_inf.mp hl).2)) ?_
  have h1 : t * c * t⁻¹ * c⁻¹ ∈ C :=
    C.mul_mem ((mem_normalizer_iff.mp htC c).mp hc) (C.inv_mem hc)
  exact (mem_normalizer_iff.mp (hSC (mem_inf.mp hl).1) _).mp h1

end CFSG.Quasithin.Stroth.G5

end
