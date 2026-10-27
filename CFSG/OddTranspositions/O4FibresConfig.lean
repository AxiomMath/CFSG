module

public import CFSG.OddTranspositions.FourEightBase
public import CFSG.OddTranspositions.O4FibresW

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

omit [Finite G] in
theorem K₁_le_X (hQ : Config D u w v z a K₁ S') {X : Subgroup G}
    (hKX : thirdK D z ≤ X) : K₁ ≤ X :=
  ((le_sup_left : K₁ ≤ K₁ ⊔ Subgroup.zpowers z).trans hQ.K_eq.ge).trans hKX

theorem u_mem_X_config (hQ : Config D u w v z a K₁ S') {X : Subgroup G}
    (hKX : thirdK D z ≤ X) : u ∈ X :=
  hKX (Delta_subset_thirdK (hQ.z_facts).2.2.1)

theorem v_mem_X_config (hQ : Config D u w v z a K₁ S') {X : Subgroup G}
    (hKX : thirdK D z ≤ X) : v ∈ X :=
  hKX (Delta_subset_thirdK (hQ.z_facts).2.2.2.1)

theorem K₁_inf_R_eq_bot (hQ : Config D u w v z a K₁ S') {X : Subgroup G} {R : Subgroup X}
    [R.Normal] (hR : Group.IsSolvable R) (hKX : thirdK D z ≤ X) :
    K₁ ⊓ (R.map (Subgroup.subtype X)) = ⊥ := by
  obtain ⟨eK⟩ := hQ.K₁_A5
  have hRN : R.Normal := inferInstance
  have hOn : ∀ h ∈ K₁, ∀ o ∈ R.map (Subgroup.subtype X),
      h * o * h⁻¹ ∈ R.map (Subgroup.subtype X) := by
    intro h hh o ho
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ho
    refine Subgroup.mem_map.mpr
      ⟨⟨h, K₁_le_X hQ hKX hh⟩ * r * ⟨h, K₁_le_X hQ hKX hh⟩⁻¹,
        hRN.conj_mem r hr ⟨h, K₁_le_X hQ hKX hh⟩, ?_⟩
    simp
  have hOs : Group.IsSolvable (R.map (Subgroup.subtype X)) := by
    have : Group.IsSolvable R := hR
    let f := (R.equivMapOfInjective (Subgroup.subtype X) (Subgroup.subtype_injective X)).symm
    exact solvable_of_solvable_injective (f := f.toMonoidHom) f.injective
  exact inf_eq_bot_of_mulEquiv_A5 eK hOn hOs

theorem u_mul_v_mem_K₁ (hQ : Config D u w v z a K₁ S') : u * v ∈ K₁ := by
  obtain ⟨hz2, -, huΔ, hvΔ, -, -⟩ := hQ.z_facts
  have hzu : z * u ∈ K₁ := hQ.delta_sub u huΔ
  have hzv : z * v ∈ K₁ := hQ.delta_sub v hvΔ
  have hcomm : Commute (z * u) z :=
    Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm hzu)
  have hprod : (z * u) * (z * v) = u * v := by
    rw [← mul_assoc (z * u) z v, hcomm.eq, ← mul_assoc z z u, hz2, one_mul]
  rw [← hprod]
  exact K₁.mul_mem hzu hzv

theorem v_not_congruent_u (hQ : Config D u w v z a K₁ S') {X : Subgroup G} {R : Subgroup X}
    [R.Normal] (hR : Group.IsSolvable R) (hKX : thirdK D z ≤ X) :
    QuotientGroup.mk' R ⟨v, v_mem_X_config hQ hKX⟩ ≠
      QuotientGroup.mk' R ⟨u, u_mem_X_config hQ hKX⟩ := by
  intro h
  let huX : u ∈ X := u_mem_X_config hQ hKX
  let hvX : v ∈ X := v_mem_X_config hQ hKX
  let uX : X := ⟨u, huX⟩
  let vX : X := ⟨v, hvX⟩
  have hRN : R.Normal := inferInstance
  have h1 : QuotientGroup.mk' R (vX * uX⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hmemR : vX * uX⁻¹ ∈ R :=
    (QuotientGroup.eq_one_iff (x := vX * uX⁻¹)).mp h1
  let w : X := uX⁻¹ * vX
  have hwR : w ∈ R := hRN.mem_comm hmemR
  have hui : u⁻¹ = u :=
    inv_eq_of_mul_eq_one_right (hQ.setup.oddT.mul_self_eq_one
      (Delta_subset_D (hQ.z_facts).2.2.1))
  have hv2 : v * v = 1 :=
    hQ.setup.oddT.mul_self_eq_one (Delta_subset_D (hQ.z_facts).2.2.2.1)
  have hwG : (w : G) = u * v := by
    simp [w, uX, vX, hui]
  have hwK : (w : G) ∈ K₁ := by
    rw [hwG]
    exact u_mul_v_mem_K₁ hQ
  have hwmap : (w : G) ∈ R.map (Subgroup.subtype X) := ⟨w, hwR, rfl⟩
  have hwbot : (w : G) ∈ K₁ ⊓ (R.map (Subgroup.subtype X)) := ⟨hwK, hwmap⟩
  rw [K₁_inf_R_eq_bot hQ hR hKX, Subgroup.mem_bot] at hwbot
  have huv : u * v = 1 := by
    rw [← hwG]
    exact hwbot
  have huv_eq : u = v := by
    calc u = u * v * v := by rw [mul_assoc, hv2, mul_one]
      _ = 1 * v := by rw [huv]
      _ = v := one_mul v
  exact hQ.tri.2.2.2.1 huv_eq

theorem W_subset_DalphaStar_config (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hKX : thirdK D z ≤ X)
    (hR : Group.IsSolvable R) (hPX : O4PairData (X ⧸ R) (Omega D X R)) :
    ∀ y : X, y ∈ W D u X R (u_mem_X_config hQ hKX) → (y : G) ∈ DalphaStar D hC.alpha := by
  let huX : u ∈ X := u_mem_X_config hQ hKX
  let hvX : v ∈ X := v_mem_X_config hQ hKX
  obtain ⟨e, he, heu⟩ := exists_normalized_iso hC htri hu hQ.third hKX huX hPX
  exact W_subset_DalphaStar_of_v_not_mem hC htri hu hv huX hvX e he heu
    (v_not_congruent_u hQ hR hKX)

theorem W_eq_preimage_ten (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hKX : thirdK D z ≤ X)
    (hPX : O4PairData (X ⧸ R) (Omega D X R)) :
    ∃ e : (X ⧸ R) ≃* PSigmaL225, e '' Omega D X R = class65 ∧
      e (QuotientGroup.mk' R ⟨u, u_mem_X_config hQ hKX⟩) =
        SemidirectProduct.inr frob25 ∧
      e '' {z : X ⧸ R | ∃ y : X, y ∈ W D u X R (u_mem_X_config hQ hKX) ∧
        QuotientGroup.mk' R y = z} = Set.range y := by
  let huX : u ∈ X := u_mem_X_config hQ hKX
  obtain ⟨e, he, heu⟩ := exists_normalized_iso hC htri hu hQ.third hKX huX hPX
  exact ⟨e, he, heu,
    image_W_eq_ten hC.setup.oddT (hC.isBlock_alpha.subset hu) huX e he heu⟩

end CFSG.OddTranspositions.QZ

end
