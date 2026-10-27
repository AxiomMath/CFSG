module

public import CFSG.RankThree.PartOne.U5LIFT.Perm
public import CFSG.RankThree.PartOne.KF.U4Refl

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.LSTD

theorem perm_five_cases : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 → σ ≠ 1 →
    (∃ a b : Fin 5, a ≠ b ∧ σ = Equiv.swap a b) ∨
      ∃ a b c d : Fin 5, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d ∧
        σ a = b ∧ σ b = a ∧ σ c = d ∧ σ d = c := by decide +kernel

theorem exists_fifth : ∀ a b c d : Fin 5, a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c ≠ d →
    ∃ e : Fin 5, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by decide

theorem exists_third : ∀ a b : Fin 5, ∃ k : Fin 5, k ≠ a ∧ k ≠ b := by decide

namespace U5Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  {K : Type} [Field K] (C : U5Ctx A c L E f K)

theorem eq_one_of_ker_ent {y : unitarySU 2 f K 5} (hy : C.φ y = 1) {m : Fin 5}
    (hm : ent (y : GL (Fin 5) K) m m = 1) : y = 1 := by
  obtain ⟨κ, hκ⟩ := exists_of_mem_scalarsU (C.φ_ker y hy)
  have h1 : κ = 1 := by
    have h2 := hm
    rw [hκ] at h2
    simp only [ent, diagU_val, Matrix.diagonal_apply_eq] at h2
    exact Units.ext h2
  apply Subtype.ext
  rw [hκ, h1]
  exact diagU_one

namespace PermData

variable {C} (P : C.PermData)

theorem τ_mul_self_eq_one (ht2 : P.t * P.t = 1) : P.τ * P.τ = 1 :=
  (t_eq_iff C (P.mul P) (one C)).mp (by rw [t_mul, ht2, t_one])

theorem τ_ne_one (hord : orderOf P.t = 2) : P.τ ≠ 1 := by
  intro h
  have h1 : P.t = 1 := by
    rw [← t_one C]
    exact (t_eq_iff C P (one C)).mpr h
  rw [h1, orderOf_one] at hord
  omega

include P in
theorem moved_elt {a b : Fin 5} (hab : a ≠ b) (ha : P.τ a = b) (hb : P.τ b = a) {ζ : Kˣ}
    (hζp : ζ ^ 5 = 1) :
    ∃ (m : E) (y : unitarySU 2 f K 5), m ∈ autMoved E P.t ∧ (m : G) = C.φ y ∧
      (y : GL (Fin 5) K) = diagU ((torusElt a b ζ)⁻¹ * (torusElt a b ζ)⁻¹) := by
  have hv : torusElt a b ζ ∈ torusVec 5 5 K := torusElt_mem hab hζp
  have hxT : diagU (torusElt a b ζ) ∈ torusSU 5 5 K :=
    mem_torusSU_iff.mpr ⟨_, hv.1, hv.2, rfl⟩
  set x : unitarySU 2 f K 5 := ⟨diagU (torusElt a b ζ), C.torus_le _ hxT⟩ with hx
  have hxE : C.φ x ∈ E := (C.phi_mem_E_iff x).mpr hxT
  have hkey : (P.g : GL (Fin 5) K) * diagU (torusElt a b ζ) * (P.g : GL (Fin 5) K)⁻¹ =
      (diagU (torusElt a b ζ))⁻¹ := by
    rw [P.hperm.conj_diagU hv, torusElt_comp_symm hab ha hb, diagU_inv]
  have hgx : P.g * x * P.g⁻¹ = x⁻¹ := Subtype.ext (by
    show (P.g : GL (Fin 5) K) * diagU (torusElt a b ζ) * (P.g : GL (Fin 5) K)⁻¹ = _
    rw [hkey]
    rfl)
  refine ⟨P.t ⟨C.φ x, hxE⟩ * ⟨C.φ x, hxE⟩⁻¹, x⁻¹ * x⁻¹,
    Subgroup.subset_closure ⟨⟨C.φ x, hxE⟩, rfl⟩, ?_, ?_⟩
  · show C.φ P.g * C.φ x * (C.φ P.g)⁻¹ * (C.φ x)⁻¹ = C.φ (x⁻¹ * x⁻¹)
    have : C.φ P.g * C.φ x * (C.φ P.g)⁻¹ = C.φ (x⁻¹) := by
      rw [← hgx]
      simp [map_mul, map_inv]
    rw [this]
    simp [map_mul, map_inv]
  · show (diagU (torusElt a b ζ))⁻¹ * (diagU (torusElt a b ζ))⁻¹ = _
    rw [← diagU_inv, diagU_mul]

include P in
theorem not_card_autMoved_of_double {a b c' d : Fin 5} (hab : a ≠ b)
    (hca : c' ≠ a) (hcb : c' ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c' ≠ d)
    (hτa : P.τ a = b) (hτb : P.τ b = a) (hτc : P.τ c' = d) (hτd : P.τ d = c') :
    Nat.card (autMoved E P.t) ≠ 5 := by
  obtain ⟨e, hea, heb, hec, hed⟩ := exists_fifth a b c' d hab hca hcb hda hdb hcd
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have hp := C.h.prime
  have hζ2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hζinv : ζ⁻¹ * ζ⁻¹ ≠ 1 := by
    intro h'
    apply hζ2
    have : ζ ^ 2 = (ζ⁻¹ * ζ⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, sq]
    rw [this, h', inv_one]
  obtain ⟨m₁, y₁, hm₁, hm₁y, hy₁⟩ := P.moved_elt hab hτa hτb hζ.pow_eq_one
  obtain ⟨m₂, y₂, hm₂, hm₂y, hy₂⟩ := P.moved_elt hcd hτc hτd hζ.pow_eq_one
  refine card_ne_prime_of_two_independent hp _ hm₁ hm₂ ?_ ?_
  · intro h1
    have h2 : C.φ y₁ = 1 := by rw [← hm₁y, h1]; rfl
    have h4 : y₁ = 1 := by
      refine C.eq_one_of_ker_ent h2 (m := c') ?_
      rw [hy₁]
      simp only [ent, diagU_val, Matrix.diagonal_apply_eq, Pi.mul_apply, Pi.inv_apply,
        torusElt_apply_other hca hcb, inv_one, mul_one, Units.val_one]
    have h5 : diagU ((torusElt a b ζ)⁻¹ * (torusElt a b ζ)⁻¹) = 1 := by
      rw [← hy₁, h4]; rfl
    have h6 := congrArg (fun z : GL (Fin 5) K => ent z a a) h5
    simp only [ent, diagU_val, Matrix.diagonal_apply_eq, Pi.mul_apply, Pi.inv_apply,
      torusElt_apply_left hab, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one,
      Matrix.one_apply_eq] at h6
    apply hζinv
    apply Units.ext
    simpa [Units.val_mul, Units.val_inv_eq_inv_val] using h6
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : (m₂ : G) = (m₁ : G) ^ k := by rw [← hk]; rfl
    rw [hm₁y, hm₂y, ← map_zpow] at h1
    have h2 : C.φ (y₂⁻¹ * y₁ ^ k) = 1 := by
      rw [map_mul, map_inv, ← h1, inv_mul_cancel]
    have h3 : y₂⁻¹ * y₁ ^ k = 1 := by
      refine C.eq_one_of_ker_ent h2 (m := e) ?_
      have h7 : ((y₂⁻¹ * y₁ ^ k : unitarySU 2 f K 5) : GL (Fin 5) K) =
          diagU ((torusElt c' d ζ)⁻¹ * (torusElt c' d ζ)⁻¹)⁻¹ *
            diagU (((torusElt a b ζ)⁻¹ * (torusElt a b ζ)⁻¹) ^ k) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
        rw [hy₁, hy₂, diagU_zpow, diagU_inv]
      rw [h7]
      simp only [ent, diagU_mul, diagU_val, Matrix.diagonal_apply_eq, Pi.mul_apply, Pi.inv_apply,
        Pi.pow_apply, torusElt_apply_other hea heb, torusElt_apply_other hec hed, inv_one,
        mul_one, one_zpow, Units.val_one]
    have h8 : y₂ = y₁ ^ k := by
      have := congrArg (fun z : unitarySU 2 f K 5 => y₂ * z) h3
      simpa using this.symm
    have h9 := congrArg (fun z : unitarySU 2 f K 5 => (z : GL (Fin 5) K)) h8
    simp only [Subgroup.coe_zpow] at h9
    rw [hy₁, hy₂, diagU_zpow] at h9
    have h10 : (torusElt c' d ζ)⁻¹ * (torusElt c' d ζ)⁻¹ =
        ((torusElt a b ζ)⁻¹ * (torusElt a b ζ)⁻¹) ^ k := diagU_injective h9
    have h11 := congrFun h10 c'
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, torusElt_apply_left hcd,
      torusElt_apply_other hca hcb] at h11
    simp only [inv_one, mul_one, one_zpow] at h11
    exact hζinv h11

include P in
theorem exists_swap_of_reflection (hrefl : IsAutReflection 5 E P.t) :
    ∃ a b : Fin 5, a ≠ b ∧ P.τ = Equiv.swap a b := by
  have ht2 : P.t * P.t = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one P.t
    rwa [hrefl.1] at this
  have hττ := P.τ_mul_self_eq_one ht2
  have hτ1 := P.τ_ne_one hrefl.1
  rcases perm_five_cases P.τ hττ hτ1 with h | ⟨a, b, c', d, hab, hca, hcb, hda, hdb, hcd, hτa, hτb,
      hτc, hτd⟩
  · exact h
  · exact absurd hrefl.2
      (P.not_card_autMoved_of_double hab hca hcb hda hdb hcd hτa hτb hτc hτd)

end PermData

end U5Ctx

end CFSG.RankThree.PartOne.U5LIFT
