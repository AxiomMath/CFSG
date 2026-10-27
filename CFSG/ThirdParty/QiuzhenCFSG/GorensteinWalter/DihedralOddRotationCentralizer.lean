module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Centralizer of an odd-order rotation subgroup in a dihedral group

In a finite dihedral group, no nontrivial odd-order rotation is centralized
by a reflection.  Hence the centralizer of a nontrivial odd-order rotation
subgroup is contained in the rotation subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem centralizer_odd_rotation_le_rotationSubgroup
    {n : ℕ} [NeZero n]
    (A : Subgroup (DihedralGroup n))
    (hAne : A ≠ ⊥)
    (hArot : ∀ x : DihedralGroup n, x ∈ A →
      ∃ i : ZMod n, x = DihedralGroup.r i)
    (hAodd : ∀ x : DihedralGroup n, x ∈ A → Odd (orderOf x)) :
    Subgroup.centralizer (A : Set (DihedralGroup n)) ≤
      Subgroup.zpowers (DihedralGroup.r 1) := by
  intro x hx
  rcases x with j | j
  · exact Subgroup.mem_zpowers_iff.mpr ⟨j.val, by
      simpa [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]⟩
  · exfalso
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    have haA : (a : DihedralGroup n) ∈ A := a.2
    obtain ⟨i, hi⟩ := hArot (a : DihedralGroup n) haA
    have haG : (a : DihedralGroup n) = DihedralGroup.r i := hi
    have hai : i ≠ 0 := by
      intro hi
      apply ha1
      apply Subtype.ext
      simp [haG, hi]
    have hrA : DihedralGroup.r i ∈ A := by
      rw [← haG]
      exact haA
    have hodd : Odd (orderOf (DihedralGroup.r i)) :=
      hAodd (DihedralGroup.r i) hrA
    have hnot2 : (DihedralGroup.r i) ^ 2 ≠ 1 := by
      intro h
      have hord2 : orderOf (DihedralGroup.r i) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h)
      have hordne : orderOf (DihedralGroup.r i) ≠ 1 := by
        intro h
        have hone : DihedralGroup.r i = 1 := (orderOf_eq_one_iff).1 h
        exact ha1 (Subtype.ext (by simpa [haG] using hone))
      have hle : orderOf (DihedralGroup.r i) ≤ 2 :=
        Nat.le_of_dvd (by omega) hord2
      have hne2 : orderOf (DihedralGroup.r i) ≠ 2 := by
        intro h
        exact hodd.not_two_dvd_nat (by rw [h])
      have hpos : 0 < orderOf (DihedralGroup.r i) :=
        orderOf_pos (DihedralGroup.r i)
      omega
    have hcomm : DihedralGroup.sr j * DihedralGroup.r i =
        DihedralGroup.r i * DihedralGroup.sr j :=
      ((Subgroup.mem_centralizer_iff.mp hx) (DihedralGroup.r i) hrA).symm
    have hEq : DihedralGroup.sr (j + i) = DihedralGroup.sr (j - i) := by
      simpa using hcomm
    have hEq' : j + i = j - i := by
      injection hEq with hEq'
    have h2i : (2 : ZMod n) * i = 0 := by
      linear_combination hEq'
    have h2i' : i * 2 = 0 := by
      rw [mul_comm]
      exact h2i
    have hsq : (DihedralGroup.r i) ^ 2 = 1 := by
      rw [DihedralGroup.r_pow]
      simpa [h2i']
    exact hnot2 hsq

public theorem mem_sup_zpowers_of_involution_inverts
    {G : Type u} [Group G] {U : Subgroup G} {w : G}
    (_hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) {x : G} :
    x ∈ U ⊔ Subgroup.zpowers w ↔ ∃ u : G, u ∈ U ∧ (x = u ∨ x = u * w) := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ u : G, u ∈ U ∧ (x = u ∨ x = u * w)}
        one_mem' := ⟨1, U.one_mem, Or.inl rfl⟩
        mul_mem' := by
          intro a b ha hb
          rcases ha with ⟨u, hu, hu_or⟩
          rcases hb with ⟨v, hv, hv_or⟩
          rcases hu_or with heq | heq
          · rw [heq]
            rcases hv_or with heqv | heqv
            · rw [heqv]
              exact ⟨u * v, U.mul_mem hu hv, Or.inl rfl⟩
            · rw [heqv]
              exact ⟨u * v, U.mul_mem hu hv, Or.inr (by group)⟩
          · rw [heq]
            rcases hv_or with heqv | heqv
            · rw [heqv]
              have hwv : w * v * w⁻¹ = v⁻¹ := hwinv v hv
              have hstep : (u * w) * v = (u * v⁻¹) * w := by
                calc
                  (u * w) * v = u * (w * v) := by group
                  _ = u * ((w * v * w⁻¹) * w) := by group
                  _ = u * (v⁻¹ * w) := by rw [hwv]
                  _ = (u * v⁻¹) * w := by group
              exact ⟨u * v⁻¹, U.mul_mem hu (U.inv_mem hv), Or.inr (by rw [hstep])⟩
            · rw [heqv]
              have hwv : w * v * w⁻¹ = v⁻¹ := hwinv v hv
              have hstep : (u * w) * (v * w) = u * v⁻¹ := by
                calc
                  (u * w) * (v * w) = u * (w * v) * w := by group
                  _ = u * ((w * v * w⁻¹) * w) * w := by group
                  _ = u * (v⁻¹ * w) * w := by rw [hwv]
                  _ = u * v⁻¹ := by
                    calc
                      u * (v⁻¹ * w) * w = u * v⁻¹ * (w * w) := by group
                      _ = u * v⁻¹ := by simp [hwsq]
              exact ⟨u * v⁻¹, U.mul_mem hu (U.inv_mem hv), Or.inl (by rw [hstep])⟩
        inv_mem' := by
          intro a ha
          rcases ha with ⟨u, hu, hu_or⟩
          rcases hu_or with heq | heq
          · rw [heq]
            exact ⟨u⁻¹, U.inv_mem hu, Or.inl (by simp)⟩
          · rw [heq]
            have hwinvu : w * u⁻¹ * w⁻¹ = u := by
              simpa using hwinv (u⁻¹) (U.inv_mem hu)
            have hstep : (u * w)⁻¹ = u * w := by
              calc
                (u * w)⁻¹ = w⁻¹ * u⁻¹ := by simp
                _ = w * u⁻¹ := by rw [inv_eq_of_mul_eq_one_right hwsq]
                _ = (w * u⁻¹ * w⁻¹) * w := by group
                _ = u * w := by rw [hwinvu]
            exact ⟨u, hu, Or.inr (by rw [hstep])⟩ }
    have hUS : U ≤ S := by
      intro x hx
      exact ⟨x, hx, Or.inl rfl⟩
    have hwS : Subgroup.zpowers w ≤ S := by
      rw [Subgroup.zpowers_le]
      exact ⟨1, U.one_mem, Or.inr (by simp)⟩
    exact (sup_le hUS hwS) hx
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact Subgroup.mem_sup_left hu
    · exact Subgroup.mul_mem_sup hu (Subgroup.mem_zpowers w)

/-- If a nontrivial odd-order rotation subgroup is centralized by a
dihedral join `U ⊔ ⟨w⟩`, then every centralizer element lies in the rotation
subgroup `U`.  This is the abstract core of the Klein-four attack. -/
public theorem centralizer_odd_rotation_le_U_of_dihedral_join
    {G : Type u} [Group G] [Finite G]
    (U A : Subgroup G) (w : G)
    (hAne : A ≠ ⊥) (hArot : A ≤ U)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hUcyc : IsCyclic U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hC : Subgroup.centralizer (A : Set G) ≤ U ⊔ Subgroup.zpowers w) :
    Subgroup.centralizer (A : Set G) ≤ U := by
  intro x hx
  have hxD : x ∈ U ⊔ Subgroup.zpowers w := hC hx
  rcases (mem_sup_zpowers_of_involution_inverts hwU hwsq hwinv).mp hxD with
    ⟨u, hu, hx_or⟩
  rcases hx_or with hxU | hxuw
  · rw [hxU]
    exact hu
  · exfalso
    let : CommGroup U := IsCyclic.commGroup
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    have haA : (a : G) ∈ A := a.2
    have haU : (a : G) ∈ U := hArot haA
    have haodd : Odd (orderOf (a : G)) := hAodd (a : G) haA
    have hcommU : (a : G) * u = u * (a : G) := by
      exact congrArg Subtype.val
        (mul_comm (⟨a, haU⟩ : U) (⟨u, hu⟩ : U))
    have hxcomm : (u * w) * (a : G) = (a : G) * (u * w) := by
      rw [hxuw] at hx
      rw [Subgroup.mem_centralizer_iff] at hx
      exact (hx (a : G) haA).symm
    have hconj_eq_a : (u * w) * (a : G) * (u * w)⁻¹ = (a : G) := by
      calc
        (u * w) * (a : G) * (u * w)⁻¹ =
            (u * w) * (a : G) * (u * w)⁻¹ := rfl
        _ = (a : G) * (u * w) * (u * w)⁻¹ := by rw [hxcomm]
        _ = (a : G) := by group
    have hconj_eq_inv : (u * w) * (a : G) * (u * w)⁻¹ = (a : G)⁻¹ := by
      calc
        (u * w) * (a : G) * (u * w)⁻¹ =
            u * (w * (a : G) * w⁻¹) * u⁻¹ := by group
        _ = u * (a : G)⁻¹ * u⁻¹ := by rw [hwinv (a : G) haU]
        _ = (a : G)⁻¹ := by
          have hcomm : u * (a : G)⁻¹ = (a : G)⁻¹ * u := by
            exact congrArg Subtype.val
              (mul_comm (⟨u, hu⟩ : U) (⟨a, haU⟩ : U)⁻¹)
          rw [hcomm]
          group
    have ha_inv : (a : G) = (a : G)⁻¹ :=
      hconj_eq_a.symm.trans hconj_eq_inv
    have hsq : (a : G) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [ha_inv]
      simp
    have hord2 : orderOf (a : G) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    have hordne : orderOf (a : G) ≠ 1 := by
      intro h
      exact ha1 (Subtype.ext (orderOf_eq_one_iff.mp h))
    have hle : orderOf (a : G) ≤ 2 :=
      Nat.le_of_dvd (by omega) hord2
    have hne2 : orderOf (a : G) ≠ 2 := by
      intro h
      exact haodd.not_two_dvd_nat (by rw [h])
    have hpos : 0 < orderOf (a : G) := orderOf_pos (a : G)
    omega

/-- Bridge from a normalizer-equal-to-dihedral-join hypothesis to the
rotation-subgroup centralizer bound. -/
public theorem centralizer_odd_rotation_le_U_of_normalizer
    {G : Type u} [Group G] [Finite G]
    (U A : Subgroup G) (w : G)
    (hAne : A ≠ ⊥) (hArot : A ≤ U)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hUcyc : IsCyclic U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hN : Subgroup.normalizer (A : Set G) = U ⊔ Subgroup.zpowers w) :
    Subgroup.centralizer (A : Set G) ≤ U :=
  centralizer_odd_rotation_le_U_of_dihedral_join U A w
    hAne hArot hAodd hUcyc hwU hwsq hwinv (by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
        Subgroup.centralizer_le_normalizer (A : Set G) hx
      rw [hN] at hxN
      exact hxN)

/-- No Klein four subgroup centralizes a nontrivial odd-order rotation
subgroup whose normalizer is a dihedral join of a cyclic torus and a
reflection. -/
public theorem no_kleinFour_centralizes_odd_rotation_of_normalizer
    {G : Type u} [Group G] [Finite G]
    (U A V : Subgroup G) (w : G)
    (hAne : A ≠ ⊥) (hArot : A ≤ U)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hUcyc : IsCyclic U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hN : Subgroup.normalizer (A : Set G) = U ⊔ Subgroup.zpowers w)
    (hVK : IsKleinFour V) (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  have hC_le_U : Subgroup.centralizer (A : Set G) ≤ U :=
    centralizer_odd_rotation_le_U_of_normalizer U A w
      hAne hArot hAodd hUcyc hwU hwsq hwinv hN
  have hVU : V ≤ U := hVleC.trans hC_le_U
  have hVcyc : IsCyclic V := Subgroup.isCyclic_of_le hVU
  have : IsKleinFour V := hVK
  exact IsKleinFour.not_isCyclic hVcyc

/-- The full statement needed from `PSL₂`: if a nontrivial odd-order cyclic
subgroup has a dihedral normalizer (cyclic rotation torus plus reflection),
no Klein four can centralize it. -/
public theorem no_kleinFour_centralizes_odd_cyclic_of_dihedral_normalizer
    {G : Type u} [Group G] [Finite G]
    (A V : Subgroup G)
    (hAne : A ≠ ⊥)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hVK : IsKleinFour V) (hVleC : V ≤ Subgroup.centralizer (A : Set G))
    (hD : ∃ U : Subgroup G, ∃ w : G,
      A ≤ U ∧ IsCyclic U ∧ w ∉ U ∧ w * w = 1 ∧
        (∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) ∧
        Subgroup.normalizer (A : Set G) = U ⊔ Subgroup.zpowers w) :
    False := by
  rcases hD with ⟨U, w, hArot, hUcyc, hwU, hwsq, hwinv, hN⟩
  exact no_kleinFour_centralizes_odd_rotation_of_normalizer
    U A V w hAne hArot hAodd hUcyc hwU hwsq hwinv hN hVK hVleC

/-- Every central element of a finite dihedral group with odd order is
the identity. -/
public theorem center_dihedral_odd_eq_one
    {n : ℕ} [NeZero n] (a : DihedralGroup n)
    (ha : a ∈ Subgroup.center (DihedralGroup n))
    (hodd : Odd (orderOf a)) :
    a = 1 := by
  rcases a with i | i
  · have hcomm : DihedralGroup.sr 0 * DihedralGroup.r i =
      DihedralGroup.r i * DihedralGroup.sr 0 :=
      (Subgroup.mem_center_iff.mp ha) (DihedralGroup.sr 0)
    have hEq : DihedralGroup.sr (0 + i) = DihedralGroup.sr (0 - i) := by
      simpa using hcomm
    have hEq' : 0 + i = 0 - i := by
      injection hEq with hEq'
    have h2i : (2 : ZMod n) * i = 0 := by
      linear_combination hEq'
    have h2i' : i * 2 = 0 := by
      rw [mul_comm]
      exact h2i
    have hsq : (DihedralGroup.r i) ^ 2 = 1 := by
      rw [DihedralGroup.r_pow]
      simpa [h2i']
    have hord2 : orderOf (DihedralGroup.r i) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    have hord1 : orderOf (DihedralGroup.r i) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact h
      · exfalso
        exact hodd.not_two_dvd_nat (by rw [h])
    exact orderOf_eq_one_iff.mp hord1
  · exfalso
    have hne : DihedralGroup.sr i ≠ 1 := by
      intro h
      cases h
    have hord2 : orderOf (DihedralGroup.sr i) = 2 :=
      orderOf_eq_prime (by simp [pow_two]) hne
    exact hodd.not_two_dvd_nat (by rw [hord2])

end CFSG.GorensteinWalter
