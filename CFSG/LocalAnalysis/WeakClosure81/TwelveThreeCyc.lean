module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

section Cyc

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_centralizing_element_of_regular {ρ : G →* LGL 2 V} {T T₀ : Subgroup G}
    {Z : Submodule (ZMod 2) V} {n m : ℕ} (hT : IsCyclic T) (hTcard : Nat.card T = 2 ^ n - 1)
    (hT₀ : T₀ ≤ T) (hT₀card : Nat.card T₀ = 2 ^ m - 1) (hZcard : Nat.card Z = 2 ^ m)
    (hZinv : ∀ x ∈ T, ∀ z ∈ Z, ρ x z ∈ Z) (hreg : RegularOnNonzero ρ T₀ Z) (hm : 1 ≤ m)
    (hn : 1 ≤ n) :
    ∃ x₀ ∈ T, (∀ z ∈ Z, ρ x₀ z = z) ∧ orderOf x₀ * (2 ^ m - 1) = 2 ^ n - 1 ∧
      Nat.Coprime (orderOf x₀) (2 ^ m - 1) := by
  classical
  have hm2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hn2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Finite T := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite T₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI := hT
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    have h := (IsCyclic.isMulCommutative (α := T)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  let X : Subgroup G :=
    { carrier := {x | x ∈ T ∧ ∀ z ∈ Z, ρ x z = z}
      mul_mem' := by
        rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
        refine ⟨T.mul_mem ha hb, fun z hz => ?_⟩
        rw [map_mul, LinearEquiv.mul_apply, hfb z hz, hfa z hz]
      one_mem' := ⟨T.one_mem, fun z _ => by rw [map_one]; rfl⟩
      inv_mem' := by
        rintro a ⟨ha, hfa⟩
        refine ⟨T.inv_mem ha, fun z hz => ?_⟩
        rw [map_inv]
        exact (LinearEquiv.symm_apply_eq _).2 (hfa z hz).symm }
  have hXT : X ≤ T := fun x hx => hx.1
  haveI : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨z₀', hz₀'⟩ := exists_ne (0 : Z)
  have hz₀ : (z₀' : V) ∈ Z := z₀'.2
  have hz₀ne : (z₀' : V) ≠ 0 := fun h => hz₀' (Subtype.ext h)
  set z₀ : V := (z₀' : V)
  have hXT₀ : ∀ x, x ∈ T₀ → x ∈ X → x = 1 := by
    intro x hx hxX
    by_contra hne
    exact hz₀ne (hreg.1 x hx hne z₀ hz₀ (hxX.2 z₀ hz₀))
  have hdecomp : ∀ x ∈ T, ∃ y ∈ T₀, ∃ w ∈ X, x = y * w := by
    intro x hx
    have hxz : ρ x z₀ ≠ 0 := by
      intro h
      apply hz₀ne
      apply (ρ x).injective
      rw [h, map_zero]
    obtain ⟨y, hy, hyz⟩ := hreg.2 z₀ hz₀ hz₀ne (ρ x z₀) (hZinv x hx z₀ hz₀) hxz
    have hwT : y⁻¹ * x ∈ T := T.mul_mem (T.inv_mem (hT₀ hy)) hx
    refine ⟨y, hy, y⁻¹ * x, ⟨hwT, ?_⟩, by group⟩
    have hw0 : ρ (y⁻¹ * x) z₀ = z₀ := by
      rw [map_mul, LinearEquiv.mul_apply, ← hyz, map_inv]
      exact (ρ y).symm_apply_apply z₀
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, map_zero]
    · obtain ⟨u, hu, huz⟩ := hreg.2 z₀ hz₀ hz₀ne z hz hz0
      have hcu : (y⁻¹ * x) * u = u * (y⁻¹ * x) := hcomm _ hwT u (hT₀ hu)
      calc ρ (y⁻¹ * x) z = ρ (y⁻¹ * x) (ρ u z₀) := by rw [huz]
        _ = ρ ((y⁻¹ * x) * u) z₀ := by rw [map_mul ρ (y⁻¹ * x) u]; rfl
        _ = ρ (u * (y⁻¹ * x)) z₀ := by rw [hcu]
        _ = ρ u (ρ (y⁻¹ * x) z₀) := by rw [map_mul ρ u (y⁻¹ * x)]; rfl
        _ = ρ u z₀ := by rw [hw0]
        _ = z := huz
  have hcard : Nat.card T = Nat.card T₀ * Nat.card X := by
    let f : T₀ × X → T := fun p => ⟨(p.1 : G) * (p.2 : G), T.mul_mem (hT₀ p.1.2) (hXT p.2.2)⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
        have h' : a * b = a' * b' := congrArg Subtype.val h
        have h1 : a'⁻¹ * a = b' * b⁻¹ := by
          calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
            _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
            _ = b' * b⁻¹ := by group
        have h2 : a'⁻¹ * a = 1 :=
          hXT₀ _ (T₀.mul_mem (T₀.inv_mem ha') ha) (h1 ▸ X.mul_mem hb' (X.inv_mem hb))
        have h3 : a = a' := by
          have := inv_mul_eq_one.1 h2
          exact this.symm
        subst h3
        have h4 : b = b' := mul_left_cancel h'
        subst h4
        rfl
      · rintro ⟨x, hx⟩
        obtain ⟨y, hy, w, hw, rfl⟩ := hdecomp x hx
        exact ⟨(⟨y, hy⟩, ⟨w, hw⟩), rfl⟩
    rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]
  haveI hXcyc : IsCyclic X := Subgroup.isCyclic_of_le hXT
  obtain ⟨x₀', hx₀'⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := X)
  have hord : orderOf (x₀' : G) = Nat.card X := by rw [Subgroup.orderOf_coe, hx₀']
  have hmul : Nat.card X * (2 ^ m - 1) = 2 ^ n - 1 := by
    rw [← hT₀card, ← hTcard, hcard, mul_comm]
  refine ⟨(x₀' : G), hXT x₀'.2, x₀'.2.2, by rw [hord]; exact hmul, ?_⟩
  rw [hord, ← hT₀card]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := T)
  obtain ⟨y, hy, w, hw, hgyw⟩ := hdecomp (g : G) g.2
  have hcm : Commute y w := hcomm y (hT₀ hy) w (hXT hw)
  have h1 : orderOf (g : G) ∣ Nat.lcm (Nat.card T₀) (Nat.card X) := by
    rw [hgyw]
    refine hcm.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd ?_ ?_)
    · exact (Subgroup.orderOf_dvd_natCard T₀ hy).trans (Nat.dvd_lcm_left _ _)
    · exact (Subgroup.orderOf_dvd_natCard X hw).trans (Nat.dvd_lcm_right _ _)
  rw [Subgroup.orderOf_coe, hg, hcard] at h1
  have hpos : 0 < Nat.card T₀ * Nat.card X := hcard ▸ Nat.card_pos
  have hl : Nat.lcm (Nat.card T₀) (Nat.card X) = Nat.card T₀ * Nat.card X :=
    Nat.dvd_antisymm (Nat.lcm_dvd_mul _ _) h1
  have hgl : Nat.gcd (Nat.card T₀) (Nat.card X) * Nat.lcm (Nat.card T₀) (Nat.card X) =
      Nat.card T₀ * Nat.card X := Nat.gcd_mul_lcm _ _
  rw [hl] at hgl
  have : Nat.gcd (Nat.card T₀) (Nat.card X) = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [hgl, one_mul])
  exact (Nat.coprime_comm).1 this

end Cyc

end CFSG.LocalAnalysis.WeakClosure81
