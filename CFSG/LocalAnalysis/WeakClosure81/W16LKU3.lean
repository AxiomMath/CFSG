module

public import CFSG.LocalAnalysis.WeakClosure81.W16QKInput
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.Quasithin.Background.SylowOddCentralKernel
public import CFSG.Quasithin.Recognition.Stroth.Str86Frame
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open Subgroup
open CFSG.GH74.Uniqueness.Bender

variable {X : Type} [Group X] [Finite X] {n : ℕ}

section Certified


private theorem w16l_u3_odd_center (hX : IsU3Shape X n) :
    Odd (Nat.card (Subgroup.center X)) := by
  rcases (Nat.dvd_prime Nat.prime_three).1 hX.2.2 with h | h <;> rw [h] <;> decide

private theorem w16l_u3_inf_center_eq_bot (hX : IsU3Shape X n) (R : Sylow 2 X) :
    (R : Subgroup X) ⊓ Subgroup.center X = ⊥ :=
  CFSG.RankThree.OddKernel.inf_eq_bot_of_odd R.isPGroup' (w16l_u3_odd_center hX)

private theorem w16l_sylowCenter_le (R : Sylow 2 X) :
    sylowCenter R ≤ (R : Subgroup X) := by
  unfold sylowCenter
  exact inf_le_left

private theorem w16l_u3_mem_sylowCenter_iff (hX : IsU3Shape X n) (R : Sylow 2 X) {r : X}
    (hrR : r ∈ (R : Subgroup X)) :
    r ∈ sylowCenter R ↔
      QuotientGroup.mk' (Subgroup.center X) r ∈
        sylowCenter (Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R) := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  let Rbar : Sylow 2 (X ⧸ Subgroup.center X) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R
  have hcoe : (Rbar : Subgroup (X ⧸ Subgroup.center X)) = (R : Subgroup X).map π := rfl
  change r ∈ sylowCenter R ↔ π r ∈ sylowCenter Rbar
  constructor
  · intro hr
    simp only [sylowCenter, Subgroup.mem_inf] at hr
    obtain ⟨hrR', hrc⟩ := hr
    simp only [sylowCenter, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [hcoe]
      exact Subgroup.mem_map_of_mem π hrR'
    · rw [Subgroup.mem_centralizer_iff]
      intro p hp
      rw [hcoe] at hp
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hp
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hrc s hs]
  · intro hr
    simp only [sylowCenter, Subgroup.mem_inf] at hr
    obtain ⟨hrR', hrc⟩ := hr
    simp only [sylowCenter, Subgroup.mem_inf]
    refine ⟨hrR, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : π s * π r = π r * π s :=
      hrc (π s) (by rw [hcoe]; exact Subgroup.mem_map_of_mem π hs)
    have h2 : π (s * r) = π (r * s) := by rw [map_mul, map_mul, h1]
    have hker : s * r * (r * s)⁻¹ ∈ Subgroup.center X := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center X), MonoidHom.mem_ker]
      show π (s * r * (r * s)⁻¹) = 1
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have hmem : s * r * (r * s)⁻¹ ∈ (R : Subgroup X) :=
      R.mul_mem (R.mul_mem hs hrR) (R.inv_mem (R.mul_mem hrR hs))
    have hbot : s * r * (r * s)⁻¹ ∈ (R : Subgroup X) ⊓ Subgroup.center X :=
      Subgroup.mem_inf.mpr ⟨hmem, hker⟩
    rw [w16l_u3_inf_center_eq_bot hX R, Subgroup.mem_bot] at hbot
    exact mul_inv_eq_one.mp hbot

private theorem w16l_u3_exists_benderCore (hX : IsU3Shape X n) (R : Sylow 2 X) :
    ∃ (e : ℕ) (t : X ⧸ Subgroup.center X),
      BenderCore (2 ^ n) 3 e
        ((Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R :
          Sylow 2 (X ⧸ Subgroup.center X)) : Subgroup (X ⧸ Subgroup.center X)) t := by
  have hB : BenderType (X ⧸ Subgroup.center X) n 3
      ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender.benderType_of_lieModel_PSU3 hX.2.1
  obtain ⟨t, ht⟩ := hB.exists_benderCore
    (Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R)
  exact ⟨_, t, ht⟩

theorem IsU3Shape.sylow_inf_eq_bot (hX : IsU3Shape X n) {R R' : Sylow 2 X} (hne : R ≠ R') :
    (R : Subgroup X) ⊓ (R' : Subgroup X) = ⊥ := by
  let Z := Subgroup.center X
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hodd : Odd (Nat.card Z) := w16l_u3_odd_center hX
  have hoddker : Odd (Nat.card π.ker) := by rw [QuotientGroup.ker_mk']; exact hodd
  have hB : BenderType (X ⧸ Z) n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender.benderType_of_lieModel_PSU3 hX.2.1
  have hTI : CFSG.Quasithin.SylowTwoTI (X ⧸ Z) :=
    CFSG.Quasithin.Stroth.BenderType.sylowTwoTI hB
  exact CFSG.Quasithin.SylowTwoTI.of_central_odd_ker π (QuotientGroup.mk'_surjective Z)
    (le_of_eq (QuotientGroup.ker_mk' Z)) hoddker hTI R R' hne

theorem IsU3Shape.map_sylowCenter (hX : IsU3Shape X n) (R : Sylow 2 X) :
    (sylowCenter R).map (QuotientGroup.mk' (Subgroup.center X)) =
      sylowCenter (Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R) := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  let Rbar : Sylow 2 (X ⧸ Subgroup.center X) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R
  change (sylowCenter R).map π = sylowCenter Rbar
  apply le_antisymm
  · rintro y ⟨r, hr, rfl⟩
    exact (w16l_u3_mem_sylowCenter_iff hX R (w16l_sylowCenter_le R hr)).mp hr
  · intro y hy
    have hyR : y ∈ (Rbar : Subgroup (X ⧸ Subgroup.center X)) := w16l_sylowCenter_le Rbar hy
    have hcoe : (Rbar : Subgroup (X ⧸ Subgroup.center X)) = (R : Subgroup X).map π := rfl
    rw [hcoe] at hyR
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hyR
    exact Subgroup.mem_map.mpr
      ⟨r, (w16l_u3_mem_sylowCenter_iff hX R hr).mpr hy, rfl⟩

theorem IsU3Shape.card_sylowCenter (hX : IsU3Shape X n) (R : Sylow 2 X) :
    Nat.card (sylowCenter R) = 2 ^ n := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  let Rbar : Sylow 2 (X ⧸ Subgroup.center X) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R
  obtain ⟨e, t, hc⟩ := w16l_u3_exists_benderCore hX R
  have hinf : sylowCenter R ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    refine le_bot_iff.mp (le_trans ?_ (le_of_eq (w16l_u3_inf_center_eq_bot hX R)))
    exact le_inf (le_trans inf_le_left (w16l_sylowCenter_le R)) inf_le_right
  have hcard := CFSG.card_map_eq_card_of_inf_ker_eq_bot π hinf
  calc Nat.card (sylowCenter R)
      = Nat.card ((sylowCenter R).map π) := hcard.symm
    _ = Nat.card (sylowCenter Rbar) := by
        rw [IsU3Shape.map_sylowCenter hX R]
    _ = Nat.card (rootCenter (Rbar : Subgroup (X ⧸ Subgroup.center X))) := rfl
    _ = 2 ^ n := hc.card_center

theorem IsU3Shape.mul_self_eq_one_iff (hX : IsU3Shape X n) (R : Sylow 2 X) {g : X}
    (hg : g ∈ (R : Subgroup X)) : g * g = 1 ↔ g ∈ sylowCenter R := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  let Rbar : Sylow 2 (X ⧸ Subgroup.center X) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R
  obtain ⟨e, t, hc⟩ := w16l_u3_exists_benderCore hX R
  have hcoe : (Rbar : Subgroup (X ⧸ Subgroup.center X)) = (R : Subgroup X).map π := rfl
  constructor
  · intro hgg
    have hsq : π g * π g = 1 := by rw [← map_mul, hgg, map_one]
    have hmem : π g ∈ (Rbar : Subgroup (X ⧸ Subgroup.center X)) := by
      rw [hcoe]
      exact Subgroup.mem_map_of_mem π hg
    exact (w16l_u3_mem_sylowCenter_iff hX R hg).mpr
      (hc.mem_rootCenter_of_mul_self hmem hsq)
  · intro hcen
    have hroot : π g ∈ rootCenter (Rbar : Subgroup (X ⧸ Subgroup.center X)) :=
      (w16l_u3_mem_sylowCenter_iff hX R hg).mp hcen
    have hsq : π g * π g = 1 := hc.center_sq (π g) hroot
    have hker : g * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, hsq]
    rw [QuotientGroup.ker_mk' (Subgroup.center X)] at hker
    have hmem : g * g ∈ (R : Subgroup X) := R.mul_mem hg hg
    have hbot : g * g ∈ (R : Subgroup X) ⊓ Subgroup.center X :=
      Subgroup.mem_inf.mpr ⟨hmem, hker⟩
    rw [w16l_u3_inf_center_eq_bot hX R, Subgroup.mem_bot] at hbot
    exact hbot

theorem IsU3Shape.card_sylow (hX : IsU3Shape X n) :
    Nat.card (Sylow 2 X) = (2 ^ n) ^ 3 + 1 := by
  let Z := Subgroup.center X
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hodd : Odd (Nat.card Z) := w16l_u3_odd_center hX
  have hoddker : Odd (Nat.card π.ker) := by rw [QuotientGroup.ker_mk']; exact hodd
  have hbij : Function.Bijective
      (fun T : Sylow 2 X => Sylow.mapSurjective (QuotientGroup.mk'_surjective Z) T) :=
    CFSG.Quasithin.sylow_mapSurjective_bijective_of_odd_central_ker π
      (QuotientGroup.mk'_surjective Z) (le_of_eq (QuotientGroup.ker_mk' Z)) hoddker
  have hcard : Nat.card (Sylow 2 X) = Nat.card (Sylow 2 (X ⧸ Z)) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  have hcl : StatedClassicalModel (X ⧸ Z) .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX.2.1 (by decide)
  rw [hcard, CFSG.CGT.Timmesfeld75.card_sylow_psu3 hcl, mul_comm 3 n, pow_mul]

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
