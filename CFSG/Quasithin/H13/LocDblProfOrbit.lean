module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.LocDbl.M24Prof

theorem orbit_card_eq_one_or_six_le {Y : Type*} [Group Y] [Finite Y] (h9 : 9 ∣ Nat.card Y)
    (hnormal2 : ∀ K : Subgroup Y, K.Normal → K ≠ ⊤ → IsPGroup 2 K)
    {X : Type*} [MulAction Y X] (x : X) :
    Nat.card (MulAction.orbit Y x) = 1 ∨ 6 ≤ Nat.card (MulAction.orbit Y x) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hlt6⟩ := hcon
  set f := MulAction.toPermHom Y (MulAction.orbit Y x) with hf
  haveI : Finite (MulAction.orbit Y x) :=
    Finite.of_surjective (fun y : Y => (⟨y • x, y, rfl⟩ : MulAction.orbit Y x))
      (fun ⟨z, y, hy⟩ => ⟨y, Subtype.ext hy⟩)
  by_cases hK : f.ker = ⊤
  · apply hne1
    have htriv : ∀ (y : Y) (z : MulAction.orbit Y x), y • z = z := by
      intro y z
      have hy : y ∈ f.ker := by rw [hK]; exact Subgroup.mem_top y
      have := MonoidHom.mem_ker.1 hy
      exact congrArg (fun σ => σ z) this
    have hsub : Subsingleton (MulAction.orbit Y x) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨ya, hya⟩ := a.2
      obtain ⟨yb, hyb⟩ := b.2
      apply Subtype.ext
      have h1 : (ya • (⟨x, MulAction.mem_orbit_self x⟩ : MulAction.orbit Y x) : MulAction.orbit Y x)
          = ⟨x, MulAction.mem_orbit_self x⟩ := htriv ya _
      have h2 : (yb • (⟨x, MulAction.mem_orbit_self x⟩ : MulAction.orbit Y x) : MulAction.orbit Y x)
          = ⟨x, MulAction.mem_orbit_self x⟩ := htriv yb _
      have e1 := congrArg Subtype.val h1
      have e2 := congrArg Subtype.val h2
      simp only [Submonoid.smul_def, Subgroup.smul_def] at e1 e2
      rw [← hya, ← hyb]
      exact e1.trans e2.symm
    exact Nat.card_of_subsingleton ⟨x, MulAction.mem_orbit_self x⟩
  · have h2 : IsPGroup 2 f.ker := hnormal2 _ inferInstance hK
    obtain ⟨a, ha⟩ := h2.exists_card_eq
    have hcard : Nat.card f.ker * Nat.card f.range = Nat.card Y := Subgroup.card_ker_mul_card_range f
    have hrange : Nat.card f.range ∣ Nat.card (Equiv.Perm (MulAction.orbit Y x)) :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_perm] at hrange
    have h9r : 9 ∣ Nat.card f.range := by
      have h9' : 9 ∣ 2 ^ a * Nat.card f.range := by rw [← ha, hcard]; exact h9
      have hcop : Nat.Coprime 9 (2 ^ a) := by
        apply Nat.Coprime.pow_right
        norm_num
      exact hcop.dvd_of_dvd_mul_left h9'
    have hfac : Nat.factorial (Nat.card (MulAction.orbit Y x)) ∣ 120 := by
      have hm : Nat.card (MulAction.orbit Y x) ≤ 5 := by omega
      have : Nat.factorial (Nat.card (MulAction.orbit Y x)) ∣ Nat.factorial 5 :=
        Nat.factorial_dvd_factorial hm
      simpa [Nat.factorial] using this
    have := h9r.trans (hrange.trans hfac)
    omega

end CFSG.Quasithin.H13.LocDbl.M24Prof
