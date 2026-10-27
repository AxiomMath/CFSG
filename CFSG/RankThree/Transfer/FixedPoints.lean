module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.RankThree.Transfer

open MulAction Subgroup

variable {G : Type*} [Group G]

section CosetValue

variable {H : Subgroup G} {A : Type*} [CommGroup A] (ϕ : H →* A) (g : G)

noncomputable def cosetValue (X : G ⧸ H) : A :=
  open _root_.Classical in
  if h : (Quotient.out X)⁻¹ * g * Quotient.out X ∈ H then ϕ ⟨_, h⟩ else 1

variable {g}

theorem smul_coe_eq_iff {x : G} : g • (x : G ⧸ H) = x ↔ x⁻¹ * g * x ∈ H := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
  have e : (g * x)⁻¹ * x = (x⁻¹ * g * x)⁻¹ := by group
  rw [e, inv_mem_iff]

theorem smul_eq_self_iff_out {X : G ⧸ H} :
    g • X = X ↔ (Quotient.out X)⁻¹ * g * Quotient.out X ∈ H := by
  conv_lhs => rw [← QuotientGroup.out_eq' X]
  exact smul_coe_eq_iff

theorem cosetValue_of_mem {X : G ⧸ H} (h : (Quotient.out X)⁻¹ * g * Quotient.out X ∈ H) :
    cosetValue ϕ g X = ϕ ⟨_, h⟩ := by
  unfold cosetValue
  simp only [h, ↓reduceDIte]

theorem cosetValue_coe {x : G} (hx : x⁻¹ * g * x ∈ H) :
    cosetValue ϕ g (x : G ⧸ H) = ϕ ⟨_, hx⟩ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H x
  have hmem : (Quotient.out (x : G ⧸ H))⁻¹ * g * Quotient.out (x : G ⧸ H) ∈ H := by
    rw [hh]
    have : (x * h)⁻¹ * g * (x * h) = (h : G)⁻¹ * (x⁻¹ * g * x) * h := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem h.2) hx) h.2
  unfold cosetValue
  simp only [hmem, ↓reduceDIte]
  have : (⟨_, hmem⟩ : H) = h⁻¹ * ⟨_, hx⟩ * h := by
    apply Subtype.ext
    simp only [hh, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [this, map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    one_mul]

end CosetValue

theorem eq_of_mem_orbit_zpowers {α : Type*} [MulAction G α] {g : G} {X Y : α}
    (hY : Y ∈ orbit (zpowers g) X) (hX : g • X = X) : Y = X := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hY
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
  have hg : g ∈ stabilizer G X := hX
  exact (stabilizer G X).zpow_mem hg n

theorem minimalPeriod_dvd_orderOf {α : Type*} [MulAction G α] (g : G) (X : α) :
    Function.minimalPeriod (fun x => g • x) X ∣ orderOf g := by
  apply Function.IsPeriodicPt.minimalPeriod_dvd
  change (fun x => g • x)^[orderOf g] X = X
  rw [smul_iterate]
  simp [pow_orderOf_eq_one]

theorem orderOf_conj (x g : G) : orderOf (x⁻¹ * g * x) = orderOf g := by
  rw [← orderOf_injective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective g]
  congr 1
  simp

theorem transfer_eq_prod_fixed_of_orderOf_lt [Finite G] {H : Subgroup G} {A : Type*}
    [CommGroup A] (ϕ : H →* A) (g : G) [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)]
    (hϕ : ∀ h : H, orderOf (h : G) < orderOf g → ϕ h = 1) :
    ϕ.transfer g = ∏ X : G ⧸ H, (if g • X = X then cosetValue ϕ g X else 1) := by
  classical
  have : Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H))) := Fintype.ofFinite _
  rw [ϕ.transfer_eq_prod_quotient_orbitRel_zpowers_quot g,
    ← Finset.prod_fiberwise Finset.univ
      (fun X : G ⧸ H => (Quotient.mk'' X : Quotient (orbitRel (zpowers g) (G ⧸ H))))]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hfib : ∀ X : G ⧸ H,
      (Quotient.mk'' X : Quotient (orbitRel (zpowers g) (G ⧸ H))) = q ↔
        X ∈ orbit (zpowers g) (Quotient.out q) := by
    intro X
    conv_lhs => rw [← Quotient.out_eq q]
    rw [Quotient.mk''_eq_mk, Quotient.eq, orbitRel_apply]
  by_cases hX₀ : g • Quotient.out q = Quotient.out q
  · have hper : Function.minimalPeriod (fun x => g • x) (Quotient.out q) = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hX₀
    have hfiber : (Finset.univ.filter fun X : G ⧸ H =>
        (Quotient.mk'' X : Quotient (orbitRel (zpowers g) (G ⧸ H))) = q) =
          {Quotient.out q} := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hfib]
      exact ⟨fun h => eq_of_mem_orbit_zpowers h hX₀, fun h => h ▸ mem_orbit_self _⟩
    rw [hfiber, Finset.prod_singleton, ite_eq_left hX₀]
    have h1 : (Quotient.out (Quotient.out q))⁻¹ * g * Quotient.out (Quotient.out q) ∈ H := by
      rw [← smul_coe_eq_iff, QuotientGroup.out_eq']
      exact hX₀
    have e : cosetValue ϕ g (Quotient.out q) = ϕ ⟨_, h1⟩ := by
      have := cosetValue_coe ϕ h1
      rwa [QuotientGroup.out_eq'] at this
    rw [e]
    congr 2
    rw [hper, pow_one]
  · have hone : ∀ X ∈ Finset.univ.filter fun X : G ⧸ H =>
        (Quotient.mk'' X : Quotient (orbitRel (zpowers g) (G ⧸ H))) = q,
        (if g • X = X then cosetValue ϕ g X else 1) = 1 := by
      intro X hX
      rw [Finset.mem_filter, hfib] at hX
      refine ite_eq_right fun hfix => hX₀ ?_
      have hsymm : Quotient.out q ∈ orbit (zpowers g) X := mem_orbit_symm.mpr hX.2
      rw [eq_of_mem_orbit_zpowers hsymm hfix]
      exact hfix
    rw [Finset.prod_eq_one hone]
    apply hϕ
    set k := Function.minimalPeriod (fun x => g • x) (Quotient.out q)
    have hk1 : k ≠ 1 := fun h => hX₀ (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
    have hkdvd : k ∣ orderOf g := minimalPeriod_dvd_orderOf g _
    have hpos : 0 < orderOf g := orderOf_pos g
    have hk0 : k ≠ 0 := by
      rintro h
      rw [h, zero_dvd_iff] at hkdvd
      omega
    rw [Subgroup.coe_mk, orderOf_conj, orderOf_pow_of_dvd hk0 hkdvd]
    exact Nat.div_lt_self hpos (by omega)

theorem transfer_comp {H : Subgroup G} [H.FiniteIndex] {A B : Type*} [CommGroup A]
    [CommGroup B] (ϕ : H →* A) (χ : A →* B) : (χ.comp ϕ).transfer = χ.comp ϕ.transfer := by
  ext g
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  rw [MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default]
  simp only [Subgroup.leftTransversals.diff, map_prod, MonoidHom.coe_comp, Function.comp_apply]

end CFSG.RankThree.Transfer

end
