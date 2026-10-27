module

public import CFSG.Holt.PSL2Natural.Basic

public section

namespace CFSG.Quasithin.F112Crit

open MulAction CFSG.Holt
open scoped LinearAlgebra.Projectivization

structure IsTorusQuot (K : Type*) [Group K] : Prop where
  trans : ∀ P : Sylow 2 K, ∀ x y y' : K,
    x ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    y ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    y' ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    x⁻¹ * y ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    x⁻¹ * y' ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    ∃ t ∈ Subgroup.normalizer ((P : Subgroup K) : Set K),
      x⁻¹ * t * x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) ∧
      y'⁻¹ * t * y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)
  reg : ∀ P : Sylow 2 K, ∀ t ∈ Subgroup.normalizer ((P : Subgroup K) : Set K), ∀ x y : K,
    x ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    y ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    x⁻¹ * y ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    x⁻¹ * t * x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    y⁻¹ * t * y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) → t = 1

section Sharp

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem stabilizer_le_normalizer_unipotentRadical {a : Ω}
    (hmem : ∀ g : G, g ∈ unipotentRadical G a ↔ g • a = a ∧ g ^ 2 = 1) :
    stabilizer G a ≤ Subgroup.normalizer (unipotentRadical G a : Set G) := by
  intro g hg
  have hga : g • a = a := hg
  have hga' : g⁻¹ • a = a := inv_smul_eq_iff.mpr hga.symm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hmem, hmem]
  constructor
  · rintro ⟨hha, hh2⟩
    exact ⟨by rw [mul_smul, mul_smul, hga', hha, hga],
      by rw [conj_pow, hh2, mul_one, mul_inv_cancel]⟩
  · rintro ⟨hha, hh2⟩
    have e : h = g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [e, inv_inv, mul_smul, mul_smul, hga, hha, hga']
    · rw [e, conj_pow, hh2, mul_one, mul_inv_cancel]

variable [Finite Ω]

private theorem exists_ne_ne (h3 : 3 ≤ Nat.card Ω) (a b : Ω) : ∃ c : Ω, c ≠ a ∧ c ≠ b :=
  ENat.exists_ne_ne_of_three_le (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast h3) a b

variable (hS : IsSharplyThreeTransitive G Ω) (hodd : Odd (Nat.card Ω)) (h3 : 3 ≤ Nat.card Ω)
  (hU : ∃ (a₀ : Ω) (U : Subgroup G), (∀ u ∈ U, u • a₀ = a₀ ∧ u ^ 2 = 1) ∧
    ∀ b c, b ≠ a₀ → c ≠ a₀ → ∃ u ∈ U, u • b = c)
include hS hodd h3 hU

theorem normalizer_unipotentRadical_eq (a : Ω) :
    Subgroup.normalizer (unipotentRadical G a : Set G) = stabilizer G a := by
  have hmem : ∀ g : G, g ∈ unipotentRadical G a ↔ g • a = a ∧ g ^ 2 = 1 := fun g =>
    hS.mem_unipotentRadical_iff hodd h3 hU
  refine le_antisymm (fun g hg => ?_) (stabilizer_le_normalizer_unipotentRadical hmem)
  obtain ⟨b, hba, -⟩ := exists_ne_ne h3 a a
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne h3 a b
  obtain ⟨u, hu, -⟩ := hS.existsUnique_unipotentRadical_smul_eq hodd hmem hba hca
  have hu1 : (u : G) ≠ 1 := fun h => hcb (by
    rw [← hu, Subgroup.smul_def, h, one_smul])
  have hu2 : orderOf (u : G) = 2 := orderOf_eq_prime ((hmem u).mp u.2).2 hu1
  have hconj : g⁻¹ * u * g ∈ unipotentRadical G a := by
    have hg' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) (u : G)).mp u.2
    rwa [inv_inv] at hg'
  have hfix : (u : G) • (g • a) = g • a := by
    have h1 := ((hmem _).mp hconj).1
    rw [mul_smul, mul_smul, inv_smul_eq_iff] at h1
    exact h1
  obtain ⟨x, -, hxu⟩ := hS.existsUnique_fixed hodd hu2
  exact (hxu _ hfix).trans (hxu a ((hmem u).mp u.2).1).symm

variable [Finite G]

theorem sylow_eq_unipotentRadical (P : Sylow 2 G) :
    ∃ a : Ω, (P : Subgroup G) = unipotentRadical G a := by
  have hP : IsPGroup 2 (P : Subgroup G) := P.isPGroup'
  obtain ⟨a, ha⟩ := fixSet_nonempty_of_odd hodd hP
  have hPa : ∀ g ∈ (P : Subgroup G), g • a = a := fun g hg => ha g hg
  refine ⟨a, ?_⟩
  have hmem : ∀ g : G, g ∈ unipotentRadical G a ↔ g • a = a ∧ g ^ 2 = 1 := fun g =>
    hS.mem_unipotentRadical_iff hodd h3 hU
  have hU2 : IsPGroup 2 (unipotentRadical G a) := fun u =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact ((hmem u).mp u.2).2)⟩
  have hnorm : (P : Subgroup G) ≤ Subgroup.normalizer (unipotentRadical G a : Set G) :=
    fun g hg => stabilizer_le_normalizer_unipotentRadical hmem (hPa g hg)
  have hUP : unipotentRadical G a ≤ P :=
    le_sup_right.trans (P.is_maximal' (hP.to_sup_of_normal_right' hU2 hnorm) le_sup_left).le
  refine le_antisymm (fun g hg => ?_) hUP
  obtain ⟨b, hba, -⟩ := exists_ne_ne h3 a a
  have hgb : g • b ≠ a := fun e => hba (smul_left_cancel g (e.trans (hPa g hg).symm))
  obtain ⟨u, hu, -⟩ := hS.existsUnique_unipotentRadical_smul_eq hodd hmem hgb hba
  have hxP : (u : G) * g ∈ (P : Subgroup G) := (P : Subgroup G).mul_mem (hUP u.2) hg
  have hxb : ((u : G) * g) • b = b := by
    rw [mul_smul]
    exact hu
  have hx1 : (u : G) * g = 1 := by
    have hcard := hS.card_stabilizer_inf h3 (Ne.symm hba)
    have h1 : orderOf ((u : G) * g) ∣ Nat.card Ω - 2 :=
      hcard ▸ Subgroup.orderOf_dvd_natCard _ ⟨hPa _ hxP, hxb⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨_, hxP⟩
    rw [Subgroup.orderOf_mk] at hk
    have hodd2 : Odd (Nat.card Ω - 2) := by
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m - 1, by omega⟩
    rcases k with _ | k
    · rwa [pow_zero, orderOf_eq_one_iff] at hk
    · exfalso
      rw [hk, pow_succ] at h1
      exact (Nat.not_even_iff_odd.mpr hodd2) (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans h1))
  rw [eq_inv_of_mul_eq_one_right hx1]
  exact (unipotentRadical G a).inv_mem u.2

theorem isTorusQuot_of_sharp : IsTorusQuot G := by
  have key : ∀ P : Sylow 2 G, ∃ a : Ω, ∀ g : G,
      g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ↔ g • a = a := by
    intro P
    obtain ⟨a, ha⟩ := sylow_eq_unipotentRadical hS hodd h3 hU P
    refine ⟨a, fun g => ?_⟩
    rw [ha, normalizer_unipotentRadical_eq hS hodd h3 hU a, mem_stabilizer_iff]
  refine ⟨fun P x y y' hx hy hy' hxy hxy' => ?_, fun P t ht x y hx hy hxy hxt hyt => ?_⟩
  · obtain ⟨a, ha⟩ := key P
    simp only [ha, mul_smul, inv_smul_eq_iff] at hx hy hy' hxy hxy' ⊢
    obtain ⟨t, hta, htx, hty⟩ := hS.exists_smul_eq (Ne.symm hx) (Ne.symm hy) (Ne.symm hxy)
      (Ne.symm hx) (Ne.symm hy') (Ne.symm hxy')
    exact ⟨t, hta, htx, hty⟩
  · obtain ⟨a, ha⟩ := key P
    simp only [ha, mul_smul, inv_smul_eq_iff] at ht hx hy hxy hxt hyt
    exact hS.eq_one_of_smul_eq (Ne.symm hx) (Ne.symm hy) (Ne.symm hxy) ht hxt hyt

end Sharp

theorem isTorusQuot_of_mulEquiv {K F : Type*} [Group K] [Finite K] [Field F] [Finite F]
    [CharP F 2] (e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) : IsTorusQuot K := by
  letI : MulAction K (ℙ F (Fin 2 → F)) := MulAction.compHom _ e.toMonoidHom
  have hsmul : ∀ (k : K) (ω : ℙ F (Fin 2 → F)), k • ω = e k • ω := fun _ _ => rfl
  have hS : IsSharplyThreeTransitive K (ℙ F (Fin 2 → F)) :=
    (PSL2Natural.isSharplyThreeTransitive F).of_equivariant e.symm (Equiv.refl _)
      (fun g p => by rw [Equiv.refl_apply, Equiv.refl_apply, hsmul, MulEquiv.apply_symm_apply])
  have hcard := PSL2Natural.card_projectiveLine (F := F)
  obtain ⟨m, hm⟩ := PSL2Natural.even_card (F := F)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hodd : Odd (Nat.card (ℙ F (Fin 2 → F))) := ⟨m, by omega⟩
  have h3 : 3 ≤ Nat.card (ℙ F (Fin 2 → F)) := by omega
  obtain ⟨a₀, U, hU1, hU2⟩ := PSL2Natural.exists_unipotent (F := F)
  refine isTorusQuot_of_sharp hS hodd h3
    ⟨a₀, U.comap e.toMonoidHom, fun u hu => ⟨?_, ?_⟩, fun b c hb hc => ?_⟩
  · rw [hsmul]
    exact (hU1 _ hu).1
  · apply e.injective
    rw [map_pow, map_one]
    exact (hU1 _ hu).2
  · obtain ⟨u, hu, huc⟩ := hU2 b c hb hc
    refine ⟨e.symm u, ?_, ?_⟩
    · show e (e.symm u) ∈ U
      rw [MulEquiv.apply_symm_apply]
      exact hu
    · rw [hsmul, MulEquiv.apply_symm_apply]
      exact huc

end CFSG.Quasithin.F112Crit

end
