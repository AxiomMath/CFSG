module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ModA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Perm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_relIndex_inf_centralizer_eq (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil ⊥ V) {Y₁ Y₂ : Subgroup (Vtil ⊥ V hV)}
    {A₁ A₂ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hcore : C23Core Y₁ Y₂ A₁ A₂ (Mbar D.M ⊥ V hV)) {z : IntMod V hV}
    (hz : mkTil ⊥ V hV z ∈ c23Omega Y₁ Y₂) :
    (centralizer ({z.val} : Set G) ⊓ D.M).relIndex D.M = 49 := by
  classical
  let O : Set G := {y : G | ∃ h ∈ D.M, y = h * z.val * h⁻¹}
  let O' : Set (IntMod V hV) := {w | w.val ∈ O}
  have hOdef : O = {y : G | ∃ h ∈ D.M, y = h * z.val * h⁻¹} := rfl
  have hO'def : O' = {w : IntMod V hV | w.val ∈ O} := rfl
  have hO'card : O'.ncard = 49 := by
    have hψ : mkTil ⊥ V hV '' O' = c23Omega Y₁ Y₂ := by
      ext u
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [hO'def] at hw
        rw [hOdef] at hw
        obtain ⟨h, hh, hweq⟩ := hw
        have hhs : h ∈ stabTil ⊥ V := hMs hh
        have hact : mkTil ⊥ V hV w = actTil ⊥ V hV ⟨h, hhs⟩ (mkTil ⊥ V hV z) := by
          rw [actTil_mk]
          have hstabz : actStab ⊥ V hV ⟨h, hhs⟩ z = w := by
            apply IntMod.val_injective
            rw [actStab_apply_val]
            exact hweq.symm
          rw [hstabz]
        rw [hact]
        exact c23_omega_stable hcore (actTil_mem_barSub ⊥ V hV hh hhs) hz
      · intro hu
        obtain ⟨a, ha, b, hb, hab⟩ := c23_omega_trans hcore hz hu
        obtain ⟨g₁, hg₁, hg₁eq⟩ := (mem_barSub ⊥ V hV D.M a).1 (hcore.le₁ ha)
        obtain ⟨g₂, hg₂, hg₂eq⟩ := (mem_barSub ⊥ V hV D.M b).1 (hcore.le₂ hb)
        refine ⟨actStab ⊥ V hV (g₁ * g₂) z, ?_, ?_⟩
        · rw [hO'def, hOdef]
          exact ⟨((g₁ * g₂ : ↥(stabTil ⊥ V)) : G), by simpa using D.M.mul_mem hg₁ hg₂,
            actStab_apply_val ⊥ V hV (g₁ * g₂) z⟩
        · rw [← actTil_mk, map_mul, MulAut.mul_apply, hg₂eq, hg₁eq]
          exact hab
    have h1 : (mkTil ⊥ V hV '' O').ncard = O'.ncard :=
      Set.ncard_image_of_injective O' (s16c7_mkTil_injective V hV)
    rw [← h1, hψ, c23_ncard_omega hcore]
  have hOeq : O = IntMod.val '' O' := by
    ext y
    constructor
    · rintro ⟨h, hh, hy⟩
      refine ⟨IntMod.mk hV ⟨y, ?_⟩, ?_, rfl⟩
      · rw [hy]
        exact (Subgroup.mem_normalizer_iff.1
          (stabTil_le_normalizer ⊥ V (hMs hh)) z.val).1 z.val_mem
      · change y ∈ O
        exact ⟨h, hh, hy⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw
  have h2 : (IntMod.val '' O').ncard = O'.ncard :=
    Set.ncard_image_of_injective O' IntMod.val_injective
  have hO : O.ncard = 49 := by rw [hOeq, h2, hO'card]
  have hstab := c23_card_eq_ncard_orbit_mul D.M z.val
  rw [← hOdef] at hstab
  have hrel := Subgroup.relIndex_mul_card
    (Subgroup.centralizer ({z.val} : Set G) ⊓ D.M) D.M
  have hinf : (Subgroup.centralizer ({z.val} : Set G) ⊓ D.M) ⊓ D.M =
      Subgroup.centralizer ({z.val} : Set G) ⊓ D.M := by rw [inf_assoc, inf_idem]
  have hstep : (Subgroup.centralizer ({z.val} : Set G) ⊓ D.M).relIndex D.M *
      Nat.card ↥(Subgroup.centralizer ({z.val} : Set G) ⊓ D.M) =
      49 * Nat.card ↥(Subgroup.centralizer ({z.val} : Set G) ⊓ D.M) := by
    calc (Subgroup.centralizer ({z.val} : Set G) ⊓ D.M).relIndex D.M *
          Nat.card ↥(Subgroup.centralizer ({z.val} : Set G) ⊓ D.M)
        = (Subgroup.centralizer ({z.val} : Set G) ⊓ D.M).relIndex D.M *
          Nat.card ↥((Subgroup.centralizer ({z.val} : Set G) ⊓ D.M) ⊓ D.M) := by rw [hinf]
      _ = Nat.card ↥D.M := hrel
      _ = O.ncard * Nat.card ↥(D.M ⊓ Subgroup.centralizer ({z.val} : Set G)) := hstab
      _ = 49 * Nat.card ↥(Subgroup.centralizer ({z.val} : Set G) ⊓ D.M) := by
            rw [hO, inf_comm]
  haveI : Nonempty ↥(Subgroup.centralizer ({z.val} : Set G) ⊓ D.M) :=
    ⟨⟨1, (Subgroup.centralizer ({z.val} : Set G) ⊓ D.M).one_mem⟩⟩
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hstep

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
