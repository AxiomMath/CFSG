module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

private theorem jordan_core {V : Type*} [Group V] [Finite V] (φ : V →* V)
    (hcomm : ∀ x y : V, x * y = y * x) (hφ3 : ∀ x : V, φ (φ (φ x)) = x)
    (hV3 : ∀ x : V, x ^ 3 = 1)
    (hcard : Nat.card V = Nat.card (φ.eqLocus (MonoidHom.id V)) ^ 3)
    {b : V} (hφb : φ b = b) : ∃ u : V, (φ u)⁻¹ * u = b := by
  letI : CommGroup V := { (inferInstance : Group V) with mul_comm := hcomm }
  obtain ⟨t, ht⟩ : ∃ t : V →* V, ∀ x, t x = φ x * x⁻¹ :=
    ⟨MonoidHom.mk' (fun x => φ x * x⁻¹) fun a b => by
      simp only [map_mul, mul_inv_rev]
      ac_rfl, fun x => rfl⟩
  have ht1 : ∀ x, t x = 1 ↔ φ x = x := fun x => by
    rw [ht, mul_inv_eq_one]
  have ht3 : ∀ y : V, t (t (t y)) = 1 := by
    intro y
    have h2 : t (t y) = φ (φ y) * (φ y)⁻¹ * (y * (φ y)⁻¹) := by
      rw [ht (t y), ht y, map_mul, map_inv, mul_inv_rev, inv_inv]
    have ha : φ y * φ y * φ y = 1 := by
      rw [← pow_three']
      exact hV3 _
    have hb : (φ (φ y))⁻¹ * (φ (φ y))⁻¹ * (φ (φ y))⁻¹ = 1 := by
      rw [← pow_three', inv_pow, hV3, inv_one]
    have key : (φ y * φ y * φ y) * ((φ (φ y))⁻¹ * (φ (φ y))⁻¹ * (φ (φ y))⁻¹)
        * (y * y⁻¹) = 1 := by
      rw [ha, hb, mul_inv_cancel, mul_one, mul_one]
    rw [ht (t (t y)), h2]
    simp only [map_mul, map_inv, hφ3, mul_inv_rev, inv_inv]
    refine Eq.trans ?_ key
    ac_rfl
  have hK1 : t.ker = φ.eqLocus (MonoidHom.id V) := by
    ext x
    exact MonoidHom.mem_ker.trans (ht1 x)
  rw [← hK1] at hcard
  have hRK : (t.comp t).range ≤ t.ker := by
    rintro _ ⟨x, rfl⟩
    exact MonoidHom.mem_ker.mpr (ht3 x)
  have hm : Nat.card (t.comp t).ker ≤ Nat.card t.ker * Nat.card t.ker := by
    set f : (t.comp t).ker →* V := t.comp (t.comp t).ker.subtype
    have hfk : Nat.card f.ker ≤ Nat.card t.ker := by
      refine Nat.card_le_card_of_injective
        (fun x : f.ker => (⟨x.1.1, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)⟩ :
          t.ker)) ?_
      intro x y hxy
      have hv := congrArg (fun z : t.ker => z.1) hxy
      exact Subtype.ext (Subtype.ext hv)
    have hfr : Nat.card f.range ≤ Nat.card t.ker := by
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨x, rfl⟩
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)
    calc Nat.card (t.comp t).ker = Nat.card f.ker * Nat.card f.range :=
          (Subgroup.card_ker_mul_card_range f).symm
      _ ≤ Nat.card t.ker * Nat.card t.ker := Nat.mul_le_mul hfk hfr
  have hr : Nat.card (t.comp t).range ≤ Nat.card t.ker := Subgroup.card_le_of_le hRK
  have hpos : 0 < Nat.card t.ker := Nat.card_pos
  have hrk : Nat.card (t.comp t).range = Nat.card t.ker := by
    have h1 : Nat.card t.ker * Nat.card t.ker * Nat.card t.ker ≤
        Nat.card t.ker * Nat.card t.ker * Nat.card (t.comp t).range := by
      calc Nat.card t.ker * Nat.card t.ker * Nat.card t.ker = Nat.card V := by
            rw [hcard]
            ring
        _ = Nat.card (t.comp t).ker * Nat.card (t.comp t).range :=
            (Subgroup.card_ker_mul_card_range (t.comp t)).symm
        _ ≤ Nat.card t.ker * Nat.card t.ker * Nat.card (t.comp t).range :=
            Nat.mul_le_mul hm le_rfl
    have h2 : Nat.card t.ker ≤ Nat.card (t.comp t).range :=
      Nat.le_of_mul_le_mul_left h1 (mul_pos hpos hpos)
    omega
  have hRK' : (t.comp t).range = t.ker :=
    Subgroup.eq_of_le_of_card_ge hRK (le_of_eq hrk.symm)
  have hbK : b ∈ t.ker := MonoidHom.mem_ker.mpr (by rw [ht, hφb, mul_inv_cancel])
  have hbK' : b⁻¹ ∈ (t.comp t).range := by
    rw [hRK']
    exact t.ker.inv_mem hbK
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hbK'
  have h3 : t (t w) = b⁻¹ := hw
  have h4 : φ (t w) * (t w)⁻¹ = b⁻¹ := (ht (t w)).symm.trans h3
  refine ⟨t w, ?_⟩
  calc (φ (t w))⁻¹ * t w = (φ (t w) * (t w)⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv, mul_comm]
    _ = b⁻¹⁻¹ := by rw [h4]
    _ = b := inv_inv b

theorem exists_div_of_card_fixed {H : Type*} [Group H] [Finite H] (U : Subgroup H)
    (τ : MulAut H) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU3 : ∀ x ∈ U, x ^ 3 = 1)
    (hτU : ∀ x ∈ U, τ x ∈ U) (hτ3 : τ ^ 3 = 1)
    (hcard : Nat.card U =
      Nat.card (U ⊓ τ.toMonoidHom.eqLocus (MonoidHom.id H) : Subgroup H) ^ 3)
    {b : H} (hbU : b ∈ U) (hτb : τ b = b) :
    ∃ u ∈ U, (τ u)⁻¹ * u = b := by
  have h3 : ∀ x : H, τ (τ (τ x)) = x := by
    intro x
    have h := congrArg (fun f : MulAut H => f x) hτ3
    simpa [pow_three', MulAut.mul_apply, MulAut.one_apply] using h
  obtain ⟨φ, hφ⟩ : ∃ φ : U →* U, ∀ x : U, (φ x : H) = τ x :=
    ⟨{ toFun := fun x => ⟨τ x, hτU x x.2⟩
       map_one' := Subtype.ext (map_one τ)
       map_mul' := fun x y => Subtype.ext (map_mul τ (x : H) (y : H)) }, fun x => rfl⟩
  have hφ3 : ∀ x : U, φ (φ (φ x)) = x := fun x =>
    Subtype.ext (by rw [hφ, hφ, hφ]; exact h3 x)
  have hU3' : ∀ x : U, x ^ 3 = 1 := fun x => Subtype.ext (hU3 x x.2)
  have hcomm : ∀ x y : U, x * y = y * x := fun x y => Subtype.ext (hUc x x.2 y y.2)
  have hEq : φ.eqLocus (MonoidHom.id U) =
      (U ⊓ τ.toMonoidHom.eqLocus (MonoidHom.id H)).subgroupOf U := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h' : φ x = x := h
      have hv : τ (x : H) = (x : H) := by
        have := congrArg Subtype.val h'
        rwa [hφ] at this
      exact ⟨x.2, hv⟩
    · intro h
      have hv : τ (x : H) = (x : H) := h.2
      show φ x = x
      exact Subtype.ext ((hφ x).trans hv)
  have hfix : Nat.card (φ.eqLocus (MonoidHom.id U)) =
      Nat.card (U ⊓ τ.toMonoidHom.eqLocus (MonoidHom.id H) : Subgroup H) := by
    rw [hEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hφb : φ ⟨b, hbU⟩ = ⟨b, hbU⟩ := Subtype.ext (by rw [hφ]; exact hτb)
  obtain ⟨u, hu⟩ := jordan_core φ hcomm hφ3 hU3' (by rw [hfix]; exact hcard) hφb
  refine ⟨u.1, u.2, ?_⟩
  have h := congrArg Subtype.val hu
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφ] at h
  exact h

end CFSG.RankThree.PartTwo.Sec8.Hering611
