module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.LocalRank (aschbacherSolvableCore
  solvable_prime_complement_core_characterization)

variable {G : Type} [Group G] [Finite G]

theorem theta_le (H : Subgroup G) : Theta H ≤ H := Subgroup.map_subtype_le _

theorem theta_norm (H : Subgroup G) {h x : G} (hh : h ∈ H) (hx : x ∈ Theta H) :
    h * x * h⁻¹ ∈ Theta H := by
  obtain ⟨t, ht, rfl⟩ := hx
  have hN := (inferInstance : (aschbacherSolvableCore 3 ↥H).Normal).conj_mem t ht ⟨h, hh⟩
  exact ⟨_, hN, rfl⟩

theorem theta_solv (H : Subgroup G) : Group.IsSolvable ↥(Theta H) := by
  obtain ⟨hs, -⟩ := solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three
  let e := (aschbacherSolvableCore 3 ↥H).equivMapOfInjective H.subtype H.subtype_injective
  exact solvable_of_solvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem theta_three (H : Subgroup G) : ¬ 3 ∣ Nat.card ↥(Theta H) := by
  obtain ⟨-, -, h3, -⟩ := solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three
  have : Nat.card ↥(Theta H) = Nat.card ↥(aschbacherSolvableCore 3 ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rwa [this]

theorem le_theta_of_normal {N H : Subgroup G} (hNH : N ≤ H)
    (hn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hs : Group.IsSolvable ↥N)
    (h3 : ¬ 3 ∣ Nat.card ↥N) : N ≤ Theta H := by
  obtain ⟨-, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization (H := ↥H)
    Nat.prime_three
  have hnorm : (N.subgroupOf H).Normal := ⟨fun n hnn g => by
    rw [Subgroup.mem_subgroupOf] at hnn ⊢
    exact hn g.1 g.2 n hnn⟩
  have hsolv : Group.IsSolvable ↥(N.subgroupOf H) := by
    have e := Subgroup.subgroupOfEquivOfLe hNH
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  have h3' : ¬ 3 ∣ Nat.card ↥(N.subgroupOf H) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hle := hmax _ hnorm hsolv h3'
  have := Subgroup.map_mono (f := H.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNH] at this

theorem theta_conj_mem {H H' : Subgroup G} {g : G} (hg : ∀ y, y ∈ H' ↔ g⁻¹ * y * g ∈ H) {x : G}
    (hx : x ∈ Theta H) : g * x * g⁻¹ ∈ Theta H' := by
  set N' : Subgroup G := (Theta H).map (MulAut.conj g).toMonoidHom with hN'
  have hmem : ∀ y, y ∈ N' ↔ g⁻¹ * y * g ∈ Theta H := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have e : g⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g) z) * g = z := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hz
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hle : N' ≤ Theta H' := by
    refine le_theta_of_normal ?_ ?_ ?_ ?_
    · intro y hy
      exact (hg y).2 (theta_le H ((hmem y).1 hy))
    · intro h' hh' n hn
      rw [hmem] at hn ⊢
      have hh : g⁻¹ * h' * g ∈ H := (hg h').1 hh'
      have := theta_norm H hh hn
      rwa [show g⁻¹ * (h' * n * h'⁻¹) * g =
        (g⁻¹ * h' * g) * (g⁻¹ * n * g) * (g⁻¹ * h' * g)⁻¹ by group]
    · have e := (Theta H).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective
      have := theta_solv H
      exact solvable_of_solvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    · have : Nat.card ↥N' = Nat.card ↥(Theta H) :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      rw [this]
      exact theta_three H
  exact hle ((hmem _).2 (by simpa [mul_assoc] using hx))

theorem theta_mono_normal {X C : Subgroup G} (hXC : X ≤ C)
    (hn : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X) : Theta X ≤ Theta C := by
  refine le_theta_of_normal ((theta_le X).trans hXC) ?_ (theta_solv X) (theta_three X)
  intro c hc x hx
  have hcN : c ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hn c hc y hy, fun hy => ?_⟩
    have := hn c⁻¹ (inv_mem hc) _ hy
    simpa [mul_assoc] using this
  obtain ⟨t, ht, rfl⟩ := hx
  set σ := X.normalizerMonoidHom ⟨c, hcN⟩
  have h := CFSG.RankThree.PartTwo.Sec4.map_aschbacherSolvableCore σ
  have hmem : σ t ∈ aschbacherSolvableCore 3 X := h ▸ ⟨t, ht, rfl⟩
  exact ⟨σ t, hmem, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
