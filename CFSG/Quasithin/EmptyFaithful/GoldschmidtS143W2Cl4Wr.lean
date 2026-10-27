module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

open CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine

section Wreath

variable {F : Type} [Field F]

theorem exists_wreath_noncomm (hF : Nat.card F = 9) :
    ∃ P : Sylow 2 (StatedSU 3 3 F), ∃ a ∈ (P : Subgroup (StatedSU 3 3 F)),
      ∃ b ∈ (P : Subgroup (StatedSU 3 3 F)), a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a := by
  obtain ⟨i, hi⟩ := exists_units_orderOf_eq_four hF
  obtain ⟨⟨s, t, w, hs, ht, hw⟩, H⟩ := wreath_sylow_model hF i hi
  obtain ⟨hst, hs4, -, hinter, hw2, -, hwst, hwts, -, ⟨P, hP⟩, -⟩ := H s t w hs ht hw
  have hww : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at h
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  rw [hwinv] at hwst hwts
  have hwsw : w * s * w = t := hwst
  have hwtw : w * t * w = s := hwts
  have hwti : w * t⁻¹ * w = s⁻¹ := by
    have h := congrArg (fun y => y⁻¹) hwtw
    simp only [mul_inv_rev, hwinv] at h
    rw [← h]
    group
  have hs : s ∈ (P : Subgroup (StatedSU 3 3 F)) := by
    rw [hP]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have ht : t ∈ (P : Subgroup (StatedSU 3 3 F)) := by
    rw [hP]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hw : w ∈ (P : Subgroup (StatedSU 3 3 F)) := by
    rw [hP]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  refine ⟨P, w, hw, s * t⁻¹ * w, mul_mem (mul_mem hs (inv_mem ht)) hw, hww, ?_, ?_⟩
  · calc s * t⁻¹ * w * (s * t⁻¹ * w) = s * t⁻¹ * ((w * s * w) * (w * t⁻¹ * w)) := by
          rw [← mul_assoc, ← mul_assoc]
          calc s * t⁻¹ * w * s * t⁻¹ * w = s * t⁻¹ * (w * s * (w * w) * t⁻¹ * w) := by
                rw [hww]; group
            _ = _ := by group
      _ = 1 := by rw [hwsw, hwti]; group
  · intro h
    have h1 : w * (s * t⁻¹ * w) = t * s⁻¹ := by
      calc w * (s * t⁻¹ * w) = (w * s * w) * (w * t⁻¹ * w) := by
            calc w * (s * t⁻¹ * w) = w * s * (w * w) * t⁻¹ * w := by rw [hww]; group
              _ = _ := by group
        _ = t * s⁻¹ := by rw [hwsw, hwti]
    have h2 : s * t⁻¹ * w * w = s * t⁻¹ := by rw [mul_assoc, hww, mul_one]
    rw [h1, h2] at h
    have h3 : t * t = s * s := by
      calc t * t = t * s⁻¹ * (s * t) := by group
        _ = s * t⁻¹ * (s * t) := by rw [h]
        _ = s * t⁻¹ * (t * s) := by rw [hst]
        _ = s * s := by group
    have h4 : s ^ 2 ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers t :=
      ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers s) 2, by
        rw [pow_two, ← h3, ← pow_two]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers t) 2⟩
    rw [hinter, Subgroup.mem_bot] at h4
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [hs4] at h5
    omega

end Wreath

section Transport

theorem exists_noncomm_invol {K : Type} [Group K] [Finite K]
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 3 1) (S : Subgroup K)
    (hS : Nat.card ↥S = 32) :
    ∃ a ∈ S, ∃ b ∈ S, a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hmod
  have hF9 : Nat.card F = 9 := by simpa using hcard
  let e2 : K ≃* StatedProj (StatedSU 3 3 F) := e
  let e' : K ≃* StatedSU 3 3 F :=
    e2.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_statedSU_eq_bot hF9)).trans QuotientGroup.quotientBot)
  have : Finite (StatedSU 3 3 F) := Finite.of_equiv K e'.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, a0, ha0, b0, hb0, haa, hbb, hab⟩ := exists_wreath_noncomm hF9
  let S' : Subgroup (StatedSU 3 3 F) := S.map e'.toMonoidHom
  have hS' : Nat.card S' = 32 := by
    rw [Subgroup.card_map_of_injective e'.injective, hS]
  have hP2 : IsPGroup 2 S' := IsPGroup.of_card (n := 5) (by rw [hS']; norm_num)
  have hind : S'.index = 189 := by
    have h := S'.card_mul_index
    rw [hS', card_statedSU hF9] at h
    omega
  let Q : Sylow 2 (StatedSU 3 3 F) := hP2.toSylow (by rw [hind]; decide)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (StatedSU 3 3 F) P Q
  have hcP : (P : Subgroup (StatedSU 3 3 F)).map (MulAut.conj c).toMonoidHom = S' := by
    have h := congrArg (fun T : Sylow 2 (StatedSU 3 3 F) => (T : Subgroup (StatedSU 3 3 F))) hc
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h
  have hmem : ∀ y ∈ (P : Subgroup (StatedSU 3 3 F)), e'.symm (c * y * c⁻¹) ∈ S := by
    intro y hy
    have h1 : c * y * c⁻¹ ∈ S' := hcP ▸ Subgroup.mem_map_of_mem _ hy
    obtain ⟨x, hx, hxe⟩ := h1
    have : e'.symm (c * y * c⁻¹) = x := by rw [← hxe]; exact e'.symm_apply_apply x
    rw [this]
    exact hx
  have hconj : ∀ u v : StatedSU 3 3 F, c * u * c⁻¹ * (c * v * c⁻¹) = c * (u * v) * c⁻¹ :=
    fun u v => by group
  refine ⟨e'.symm (c * a0 * c⁻¹), hmem a0 ha0, e'.symm (c * b0 * c⁻¹), hmem b0 hb0, ?_, ?_, ?_⟩
  · rw [← map_mul, hconj, haa]
    simp
  · rw [← map_mul, hconj, hbb]
    simp
  · intro h
    apply hab
    have key : ∀ u v : StatedSU 3 3 F, e'.symm u * e'.symm v = e'.symm v * e'.symm u →
        u * v = v * u := fun u v huv => e'.symm.injective (by rw [map_mul, map_mul]; exact huv)
    have h1 := key _ _ h
    rw [hconj, hconj] at h1
    exact mul_left_cancel (mul_right_cancel h1)

end Transport

end InspW2

end S143

end CFSG.Quasithin
