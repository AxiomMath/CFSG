module

public import CFSG.RankThree.PartOne.KF.U4Ctx
public import CFSG.RankThree.PartOne.KF.U4Perm
public import CFSG.RankThree.PartOne.S12.Sec12A

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace U4Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] (C : U4Ctx p A c L E f K)

include C in
theorem exists_unit_root : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot C.hU C.h.prime C.hpq
  have hz0 : z ≠ 0 := hz.ne_zero C.h.prime.ne_zero
  exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩

include C in
theorem hdist : ∀ i j : Fin 4, i ≠ j → ∃ x ∈ torusSU p 4 K, ent x i i ≠ ent x j j := by
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have h3 := C.h.three_lt
  intro i j hij
  exact torus_char_distinct hζ.pow_eq_one
    (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)) i j hij

theorem exists_perm {w : G} (hwL : w ∈ L) (hwE : w ∈ Subgroup.normalizer (E : Set G)) :
    ∃ (g : unitarySU 2 f K 4) (τ : Equiv.Perm (Fin 4)), C.phi g = w ∧
      NormPerm p (g : GL (Fin 4) K) τ := by
  obtain ⟨g, hg⟩ := C.exists_phi_eq hwL
  obtain ⟨h1, h2⟩ := C.normalizes_torus hwE hg
  obtain ⟨τ, hτ⟩ := exists_normPerm C.hdist h1 h2
  exact ⟨g, τ, hg, hτ⟩

omit [Finite G] in
theorem coe_conj_apply (w : G) (hwE : w ∈ Subgroup.normalizer (E : Set G)) (e : E) :
    ((E.normalizerMonoidHom ⟨w, hwE⟩ e : E) : G) = w * e * w⁻¹ := rfl

theorem conj_eq_self_of_perm_one {g : unitarySU 2 f K 4} (hτ : NormPerm p (g : GL (Fin 4) K) 1)
    {e : G} (he : e ∈ E) : C.phi g * e * (C.phi g)⁻¹ = e := by
  obtain ⟨x, hx, i, rfl⟩ := C.exists_decomp he
  have hgx : g * x * g⁻¹ = x := by
    apply Subtype.ext
    exact hτ.conj_eq hx hx (fun m => rfl)
  have := C.conj_phi_mul_zpow g x i
  rw [hgx] at this
  exact this

include C in
theorem perm_mul_self_eq_one {w : G} (hwE : w ∈ Subgroup.normalizer (E : Set G))
    {g : unitarySU 2 f K 4} (hg : C.phi g = w) {τ : Equiv.Perm (Fin 4)}
    (hτ : NormPerm p (g : GL (Fin 4) K) τ)
    (ht2 : E.normalizerMonoidHom ⟨w, hwE⟩ * E.normalizerMonoidHom ⟨w, hwE⟩ = 1) :
    τ * τ = 1 := by
  refine NormPerm.eq_of_conj_eq C.hdist (hτ.mul hτ) NormPerm.one fun x hx => ?_
  have hxΓ := C.torus_le x hx
  have hmem : C.phi ⟨x, hxΓ⟩ ∈ E := (C.phi_mem_E_iff _).mpr hx
  have h1 := congrArg (fun φ : MulAut E => ((φ ⟨C.phi ⟨x, hxΓ⟩, hmem⟩ : E) : G)) ht2
  simp only [MulAut.mul_apply, coe_conj_apply, MulAut.one_apply] at h1
  have h2 : C.phi (g * (g * ⟨x, hxΓ⟩ * g⁻¹) * g⁻¹) = C.phi ⟨x, hxΓ⟩ := by
    rw [← h1, ← hg]
    simp [map_mul, map_inv]
  have h3 := C.phi_injective h2
  have h4 := congrArg (fun y : unitarySU 2 f K 4 => (y : GL (Fin 4) K)) h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
  simp only [one_mul, inv_one, mul_one]
  have : (g : GL (Fin 4) K) * (g : GL (Fin 4) K) * x *
      ((g : GL (Fin 4) K) * (g : GL (Fin 4) K))⁻¹ =
      (g : GL (Fin 4) K) * ((g : GL (Fin 4) K) * x * (g : GL (Fin 4) K)⁻¹) *
        (g : GL (Fin 4) K)⁻¹ := by group
  rw [this]
  exact h4

include C in
theorem perm_ne_one {w : G} (hwE : w ∈ Subgroup.normalizer (E : Set G)) {g : unitarySU 2 f K 4}
    (hg : C.phi g = w) {τ : Equiv.Perm (Fin 4)} (hτ : NormPerm p (g : GL (Fin 4) K) τ)
    (hord : orderOf (E.normalizerMonoidHom ⟨w, hwE⟩) = 2) : τ ≠ 1 := by
  rintro rfl
  have h1 : E.normalizerMonoidHom ⟨w, hwE⟩ = 1 := by
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [coe_conj_apply, ← hg]
    exact C.conj_eq_self_of_perm_one hτ e.2
  rw [h1, orderOf_one] at hord
  omega

end U4Ctx

theorem fpf_decomp : ∀ τ : Equiv.Perm (Fin 4), τ * τ = 1 → (∀ i, τ i ≠ i) →
    ∃ a b c d : Fin 4, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d ∧
      τ a = b ∧ τ b = a ∧ τ c = d ∧ τ d = c := by decide

section Aux

variable {K : Type} [Field K]

theorem torusElt_comp_symm {n : ℕ} {a b : Fin n} (hab : a ≠ b) {τ : Equiv.Perm (Fin n)}
    (ha : τ a = b) (hb : τ b = a) (η : Kˣ) :
    (torusElt a b η) ∘ τ.symm = (torusElt a b η)⁻¹ := by
  funext m
  by_cases hma : m = a
  · subst hma
    have : τ.symm m = b := by rw [Equiv.symm_apply_eq]; exact hb.symm
    simp [this, torusElt_apply_right hab, torusElt_apply_left hab]
  · by_cases hmb : m = b
    · subst hmb
      have : τ.symm m = a := by rw [Equiv.symm_apply_eq]; exact ha.symm
      simp [this, torusElt_apply_right hab, torusElt_apply_left hab]
    · have h1 : τ.symm m ≠ a := by
        intro h'
        apply hmb
        rw [Equiv.symm_apply_eq] at h'
        rw [h', ha]
      have h2 : τ.symm m ≠ b := by
        intro h'
        apply hma
        rw [Equiv.symm_apply_eq] at h'
        rw [h', hb]
      simp [torusElt_apply_other hma hmb, torusElt_apply_other h1 h2]

end Aux


namespace U4Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] (C : U4Ctx p A c L E f K)

include C in
theorem moved_elt {w : G} (hwE : w ∈ Subgroup.normalizer (E : Set G)) {g : unitarySU 2 f K 4}
    (hg : C.phi g = w) {τ : Equiv.Perm (Fin 4)} (hτ : NormPerm p (g : GL (Fin 4) K) τ)
    {a b : Fin 4} (hab : a ≠ b) (ha : τ a = b) (hb : τ b = a) {ζ : Kˣ} (hζp : ζ ^ p = 1) :
    ∃ (m : E) (y : unitarySU 2 f K 4),
      m ∈ autMoved E (E.normalizerMonoidHom ⟨w, hwE⟩) ∧ (m : G) = C.phi y ∧
        (y : GL (Fin 4) K) = diagU ((torusElt a b ζ)⁻¹ * (torusElt a b ζ)⁻¹) := by
  have hv : torusElt a b ζ ∈ torusVec p 4 K := torusElt_mem hab hζp
  have hxT : diagU (torusElt a b ζ) ∈ torusSU p 4 K :=
    mem_torusSU_iff.mpr ⟨_, hv.1, hv.2, rfl⟩
  set x : unitarySU 2 f K 4 := ⟨diagU (torusElt a b ζ), C.torus_le _ hxT⟩ with hx
  have hxE : C.phi x ∈ E := (C.phi_mem_E_iff x).mpr hxT
  have hkey : (g : GL (Fin 4) K) * diagU (torusElt a b ζ) * (g : GL (Fin 4) K)⁻¹ =
      (diagU (torusElt a b ζ))⁻¹ := by
    rw [hτ.conj_diagU hv, torusElt_comp_symm hab ha hb, diagU_inv]
  have hgx : g * x * g⁻¹ = x⁻¹ := Subtype.ext (by
    show (g : GL (Fin 4) K) * diagU (torusElt a b ζ) * (g : GL (Fin 4) K)⁻¹ = _
    rw [hkey]
    rfl)
  refine ⟨E.normalizerMonoidHom ⟨w, hwE⟩ ⟨C.phi x, hxE⟩ * ⟨C.phi x, hxE⟩⁻¹, x⁻¹ * x⁻¹,
    Subgroup.subset_closure ⟨⟨C.phi x, hxE⟩, rfl⟩, ?_, ?_⟩
  · show w * C.phi x * w⁻¹ * (C.phi x)⁻¹ = C.phi (x⁻¹ * x⁻¹)
    rw [← hg]
    have : C.phi g * C.phi x * (C.phi g)⁻¹ = C.phi (x⁻¹) := by
      rw [← hgx]
      simp [map_mul, map_inv]
    rw [this]
    simp [map_mul, map_inv]
  · show (diagU (torusElt a b ζ))⁻¹ * (diagU (torusElt a b ζ))⁻¹ = _
    rw [← diagU_inv, diagU_mul]

include C in
theorem not_card_autMoved_of_fpf {w : G} (hwE : w ∈ Subgroup.normalizer (E : Set G))
    {g : unitarySU 2 f K 4} (hg : C.phi g = w) {τ : Equiv.Perm (Fin 4)}
    (hτ : NormPerm p (g : GL (Fin 4) K) τ) (hττ : τ * τ = 1) (hfpf : ∀ i, τ i ≠ i) :
    Nat.card (autMoved E (E.normalizerMonoidHom ⟨w, hwE⟩)) ≠ p := by
  obtain ⟨a, b, c', d, hab, hca, hcb, hda, hdb, hcd, hτa, hτb, hτc, hτd⟩ :=
    fpf_decomp τ hττ hfpf
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have hp := C.h.prime
  have h3 := C.h.three_lt
  have hζ2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
  have hζinv : ζ⁻¹ * ζ⁻¹ ≠ 1 := by
    intro h'
    apply hζ2
    have : ζ ^ 2 = (ζ⁻¹ * ζ⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, sq]
    rw [this, h', inv_one]
  obtain ⟨m₁, y₁, hm₁, hm₁y, hy₁⟩ := C.moved_elt hwE hg hτ hab hτa hτb hζ.pow_eq_one
  obtain ⟨m₂, y₂, hm₂, hm₂y, hy₂⟩ := C.moved_elt hwE hg hτ hcd hτc hτd hζ.pow_eq_one
  refine card_ne_prime_of_two_independent hp _ hm₁ hm₂ ?_ ?_
  · intro h1
    have h2 : C.phi y₁ = 1 := by rw [← hm₁y, h1]; rfl
    have h4 : y₁ = 1 := C.phi_injective (by rw [h2, map_one])
    have h5 : diagU ((torusElt a b ζ)⁻¹ * (torusElt a b ζ)⁻¹) = 1 := by
      rw [← hy₁, h4]; rfl
    have h6 := congrArg (fun z : GL (Fin 4) K => ent z a a) h5
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
    have h2 := C.phi_injective h1
    have h3' := congrArg (fun z : unitarySU 2 f K 4 => (z : GL (Fin 4) K)) h2
    simp only [Subgroup.coe_zpow] at h3'
    rw [hy₁, hy₂, diagU_zpow] at h3'
    have h4 : (torusElt c' d ζ)⁻¹ * (torusElt c' d ζ)⁻¹ =
        ((torusElt a b ζ)⁻¹ * (torusElt a b ζ)⁻¹) ^ k := diagU_injective h3'
    have h5 := congrFun h4 c'
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, torusElt_apply_left hcd,
      torusElt_apply_other hca hcb] at h5
    simp only [inv_one, mul_one, one_zpow] at h5
    exact hζinv h5

include C in
theorem exists_swap_of_reflection {w : G} (hwE : w ∈ Subgroup.normalizer (E : Set G))
    {g : unitarySU 2 f K 4} (hg : C.phi g = w) {τ : Equiv.Perm (Fin 4)}
    (hτ : NormPerm p (g : GL (Fin 4) K) τ)
    (hrefl : IsAutReflection p E (E.normalizerMonoidHom ⟨w, hwE⟩)) :
    ∃ a b : Fin 4, a ≠ b ∧ τ = Equiv.swap a b := by
  have ht2 : E.normalizerMonoidHom ⟨w, hwE⟩ * E.normalizerMonoidHom ⟨w, hwE⟩ = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one (E.normalizerMonoidHom ⟨w, hwE⟩)
    rwa [hrefl.1] at this
  have hττ := C.perm_mul_self_eq_one hwE hg hτ ht2
  have hτ1 := C.perm_ne_one hwE hg hτ hrefl.1
  rcases perm_four_cases τ hττ hτ1 with h | h
  · exact h
  · exact absurd hrefl.2 (C.not_card_autMoved_of_fpf hwE hg hτ hττ h)

end U4Ctx

end CFSG.RankThree.PartOne.KFU
