module

public import CFSG.RankThree.PartTwo.Sec13.Notation
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem mem_of_three_dvd_card_center (hD : Sec13Data G A c L)
    (h3 : 3 ∣ Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))) : c ∈ L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set ρ := QuotientGroup.mk' θ with hρ
  set Zh : Subgroup L := (Subgroup.center (L ⧸ θ)).comap ρ with hZh
  set W : Subgroup G := Zh.map L.subtype with hW
  have hW3 : 3 ∣ Nat.card W := by
    rw [hW, Subgroup.card_map_of_injective L.subtype_injective]
    exact h3.trans (Subgroup.card_dvd_of_surjective
      (ρ.subgroupComap_surjective _ (QuotientGroup.mk'_surjective θ)))
  have hAW : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W := by
    intro a ha w hw
    obtain ⟨l, hl, rfl⟩ := hw
    have haN : a ∈ Subgroup.normalizer (L : Set G) := hD.le_normalizer ha
    set σ := L.normalizerMonoidHom ⟨a, haN⟩ with hσ
    refine ⟨σ l, ?_, rfl⟩
    have hl' : ρ l ∈ Subgroup.center (L ⧸ θ) := hl
    change ρ (σ l) ∈ Subgroup.center (L ⧸ θ)
    have hmap : ρ (σ l) = Sec4.thetaQuotMulAut L σ (ρ l) := rfl
    rw [hmap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := (Sec4.thetaQuotMulAut L σ).surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hl' y']
  have hAe := hD.isElemAbelian
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  let _ : MulAction A W :=
    { smul := fun a w => ⟨(a : G) * w * (a : G)⁻¹, hAW a a.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : A) : G) * (w : G) * ((1 : A) : G)⁻¹ = (w : G)
        simp)
      mul_smul := fun a₁ a₂ w => Subtype.ext (by
        show ((a₁ * a₂ : A) : G) * (w : G) * ((a₁ * a₂ : A) : G)⁻¹ =
          (a₁ : G) * ((a₂ : G) * (w : G) * (a₂ : G)⁻¹) * (a₁ : G)⁻¹
        simp [mul_assoc]) }
  have hsmul : ∀ (a : A) (w : W), ((a • w : W) : G) = (a : G) * w * (a : G)⁻¹ := fun _ _ => rfl
  set F : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G) with hF
  have hfix : Nat.card (MulAction.fixedPoints A W) = Nat.card F := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(w.1 : G), w.1.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
        invFun := fun f => ⟨⟨f.1, f.2.1⟩, fun a => Subtype.ext ?_⟩
        left_inv := fun w => rfl
        right_inv := fun f => rfl }
    · have h1 := congrArg Subtype.val (w.2 ⟨a, ha⟩)
      rw [hsmul] at h1
      calc a * (w.1 : G) = a * (w.1 : G) * a⁻¹ * a := by group
        _ = (w.1 : G) * a := by rw [h1]
    · rw [hsmul]
      have h1 := Subgroup.mem_centralizer_iff.mp f.2.2 a a.2
      change (a : G) * f.1 * (a : G)⁻¹ = f.1
      rw [h1, mul_inv_cancel_right]
  have hF3 : 3 ∣ Nat.card F := by
    have hmod := hAp.card_modEq_card_fixedPoints W
    rw [hfix] at hmod
    exact (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hW3)))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := F) 3 hF3
  have hzW : (z : G) ∈ W := z.2.1
  have hzA' : ∀ a ∈ A, a * (z : G) = (z : G) * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp z.2.2 a ha
  have hz3 : (z : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hzo : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hsup := isElemAbelian_sup hAe (isElemAbelian_zpowers hz3) (by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hzA' x hx) k).eq)
  have hzA : (z : G) ∈ A := by
    rw [← hD.eq_of_le hsup le_sup_left]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨zl, hzl, hzle⟩ := hzW
  have hzL : (z : G) ∈ L := hzle ▸ zl.2
  have hzC : (z : G) ∈ Sec4.thetaQuotCentralizer L := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr
      ⟨Subgroup.le_normalizer hzL, fun l hl => ?_⟩
    have hcen : ρ zl ∈ Subgroup.center (L ⧸ θ) := hzl
    have h1 : ρ ((⟨l, hl⟩ : L)⁻¹ * (zl * ⟨l, hl⟩ * zl⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv,
        (Subgroup.mem_center_iff.mp hcen (ρ ⟨l, hl⟩)).symm, mul_inv_cancel_right, inv_mul_cancel]
    refine ⟨_, (QuotientGroup.eq_one_iff _).mp h1, ?_⟩
    have hzle' : (zl : G) = (z : G) := hzle
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hzle']
  have hsc := hD.sectionCentralizer_eq
  rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
  have hzc : (z : G) ∈ Subgroup.zpowers c := by
    have : (z : G) ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := ⟨hzA, hzC⟩
    rw [hsc] at this
    exact this
  have heq : Subgroup.zpowers (z : G) = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzc) ?_
    rw [hD.card_zpowers, Nat.card_zpowers, hzo]
  have hcz : c ∈ Subgroup.zpowers (z : G) := heq ▸ Subgroup.mem_zpowers c
  exact Subgroup.zpowers_le.mpr hzL hcz

theorem not_mem_of_hypS (hD : Sec13Data G A c L) (hS : HypS A) : c ∉ L :=
  hS.2.2 c hD.zpowers_mem_omegaA L hD.mem_lA

end CFSG.RankThree.PartTwo.Sec13.ResProof
