module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Syl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Psu3Ord

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin CFSG.Quasithin.A312U3 CFSG.LinearGroups
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

@[expose] noncomputable def sl2ToSU3 (hF : Nat.card F = p ^ 2) : SL(2, ZMod p) →* SU3F p F :=
  (ofSU2 hF).comp (Classical.choice (exists_su2_equiv hF)).toMonoidHom

theorem sl2ToSU3_injective (hF : Nat.card F = p ^ 2) : Function.Injective (sl2ToSU3 hF) :=
  (ofSU2_injective hF).comp (Classical.choice (exists_su2_equiv hF)).injective

theorem sl2ToSU3_mem_leviU (hF : Nat.card F = p ^ 2) (x : SL(2, ZMod p)) :
    sl2ToSU3 hF x ∈ leviU hF :=
  ofSU2_mem_leviU hF _

theorem not_isSolvable_of_leviU_le (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hF : Nat.card F = p ^ 2)
    {Y : Subgroup (SU3F p F)} (hB : leviU hF ≤ Y) : ¬ Group.IsSolvable ↥Y := by
  intro hsolv
  let f : SL(2, ZMod p) →* ↥Y :=
    (sl2ToSU3 hF).codRestrict Y fun x => hB (sl2ToSU3_mem_leviU hF x)
  have hinj : Function.Injective f := fun a b h => sl2ToSU3_injective hF (congrArg Subtype.val h)
  have hs := Group.isSolvable_of_isSolvable_injective hinj
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  have := CFSG.ClassicalInvolution.natCard_eq_three_of_isSolvable_sl2 hodd hs
  rw [Nat.card_zmod] at this
  exact hp3 this

theorem card_sl2_five : Nat.card SL(2, ZMod 5) = 120 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Matrix.card_SL_field (𝔽 := ZMod 5) 2, Fin.prod_univ_two]
  simp [ZMod.card]

theorem card_alternating_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem false_of_hat_a6 (hp5 : p = 5) (hF : Nat.card F = p ^ 2) {Y : Subgroup (SU3F p F)}
    (hB : leviU hF ≤ Y) (hHat : IsHat ↥(perfectCore Y) (alternatingGroup (Fin 6))) : False := by
  subst hp5
  set P : Subgroup (SU3F 5 F) := perfectCore Y with hPdef
  have hPperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr (perfectCore_perfect Y)
  have hsl : Group.IsPerfect SL(2, ZMod 5) := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (ZMod 5))) (n := 4) (by simp [ZMod.card])
    exact special_linear_dimension_two_perfect ⟨t, ht⟩
  set f₁ := sl2ToSU3 hF with hf₁
  have hS : ⁅f₁.range, f₁.range⁆ = f₁.range := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f₁)
  have hSY : f₁.range ≤ Y := by
    rintro _ ⟨x, rfl⟩
    exact hB (sl2ToSU3_mem_leviU hF x)
  have hSP : f₁.range ≤ P := le_perfectCore_of_perfect hSY hS
  let g₀ : SL(2, ZMod 5) →* ↥P := f₁.codRestrict P fun x => hSP ⟨x, rfl⟩
  have hg₀ : Function.Injective g₀ := fun a b h => sl2ToSU3_injective hF (congrArg Subtype.val h)
  let g : SL(2, ZMod 5) →* (↥P ⧸ Subgroup.center ↥P) :=
    (QuotientGroup.mk' (Subgroup.center ↥P)).comp g₀
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : g₀ x ∈ Subgroup.center ↥P := (QuotientGroup.eq_one_iff _).mp hx
    have h3 : g₀ x ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center ↥P)) (x := ⟨g₀ x, hxZ⟩)
      rw [hHat.2.1] at this
      simpa using congrArg Subtype.val this
    have hx3 : x ^ 3 = 1 := hg₀ (by rw [map_pow, h3, map_one])
    have hxc : x ∈ Subgroup.center SL(2, ZMod 5) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply hg₀
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hxZ (g₀ y)
    obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    have hx2 : x ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow]
      have hr2 : r ^ 2 = 1 := by simpa using hr
      rw [hr2, map_one]
      rfl
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx3, hx2]; simp
  have hRcard : Nat.card g.range = 120 := by
    rw [← card_sl2_five]
    exact (Nat.card_congr (Equiv.ofInjective g hginj)).symm
  have hQcard : Nat.card (↥P ⧸ Subgroup.center ↥P) = 360 := by
    obtain ⟨e6⟩ := hHat.2.2
    rw [Nat.card_congr e6.toEquiv, card_alternating_six]
  have hidx : g.range.index = 3 := by
    have := g.range.card_mul_index
    rw [hRcard, hQcard] at this
    omega
  have htop := eq_top_of_index_three hidx
  have h360 : Nat.card g.range = 360 := by
    rw [htop, Subgroup.card_top, hQcard]
  omega

end CFSG.Quasithin.E2P.Asc80
