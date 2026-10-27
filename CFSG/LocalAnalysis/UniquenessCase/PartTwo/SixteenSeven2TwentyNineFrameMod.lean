module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c167_frame_faithful_of_conj_sup {W : Type*} [CommGroup W] {X Z : Subgroup (MulAut W)}
    {U : Subgroup W} {p : ℕ} (hp : p.Prime) (hZ : Nat.card ↥Z = p)
    (hZX : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hsup : sSup {Y : Subgroup W | ∃ g ∈ X, Y = U.map g.toMonoidHom} = ⊤) :
    ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ U, z w ≠ w := by
  let K : Subgroup (MulAut W) :=
    { carrier := {a | ∀ u ∈ U, a u = u}
      one_mem' := by intro u _; simp
      mul_mem' := by intro a b ha hb u hu; rw [MulAut.mul_apply, hb u hu, ha u hu]
      inv_mem' := by
        intro a ha u hu
        simpa [ha u hu] using MulAut.inv_apply_self (M := W) a u }
  intro z hzZ hz1
  by_contra hcon
  rw [not_exists] at hcon
  have hfix : ∀ u ∈ U, z u = u := by
    intro u hu
    exact not_not.mp (not_and.mp (hcon u) hu)
  have hzK : z ∈ K := hfix
  haveI : Fact (Nat.card ↥Z).Prime := ⟨by rw [hZ]; exact hp⟩
  have hZK : Z ≤ K := by
    have hmem : (⟨z, hzZ⟩ : ↥Z) ∈ K.subgroupOf Z := by
      rw [Subgroup.mem_subgroupOf]; exact hzK
    have hne : (⟨z, hzZ⟩ : ↥Z) ≠ 1 := by
      intro h
      exact hz1 (by simpa using Subtype.ext_iff.mp h)
    have htop : K.subgroupOf Z = ⊤ := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card (K.subgroupOf Z) with h | h
      · rw [h, Subgroup.mem_bot] at hmem
        exact absurd hmem hne
      · exact h
    intro z' hz'Z
    have hmem' : (⟨z', hz'Z⟩ : ↥Z) ∈ K.subgroupOf Z := by
      rw [htop]; exact Subgroup.mem_top _
    rwa [Subgroup.mem_subgroupOf] at hmem'
  have hconj : ∀ g ∈ X, ∀ z' ∈ Z, ∀ w ∈ U.map g.toMonoidHom, z' w = w := by
    intro g hg z' hz'Z w hw
    rw [Subgroup.mem_map] at hw
    rcases hw with ⟨u, hu, rfl⟩
    have hmem : (MulAut.conj g⁻¹) z' ∈ Z.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz'Z
    rw [hZX g⁻¹ (X.inv_mem hg)] at hmem
    have h1 : (MulAut.conj g⁻¹) z' u = u := hZK hmem u hu
    simp only [MulAut.conj_apply, MulAut.mul_apply, inv_inv] at h1
    have h2 := congrArg g h1
    rwa [MulAut.apply_inv_self] at h2
  have hZbot : Z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z' hz'Z
    have htop : (⊤ : Subgroup W) ≤ MonoidHom.eqLocus z'.toMonoidHom (MonoidHom.id W) := by
      rw [← hsup]
      apply sSup_le
      intro Y hY
      rcases hY with ⟨g, hg, rfl⟩
      intro w hw
      show z'.toMonoidHom w = (MonoidHom.id W) w
      simpa using hconj g hg z' hz'Z w hw
    ext w
    have hw : z'.toMonoidHom w = (MonoidHom.id W) w := htop (Subgroup.mem_top w)
    simpa using hw
  have hz1' : z = 1 := by
    rw [hZbot, Subgroup.mem_bot] at hzZ
    exact hzZ
  exact hz1 hz1'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
