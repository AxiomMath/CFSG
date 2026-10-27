module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdTwoPar
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Cent

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.Ree.LargeReeCover (torusPair)

set_option linter.unusedSectionVars false

section Model


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem cls_gm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ x : Gm K a, orderOf x = 2 → IsConj (zg hK) x ∨ IsConj (tg hK) x := by
  intro x hx
  have hx2 : (x : ModGL F4.tag K) ^ 2 = 1 := by
    have h : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    exact congrArg Subtype.val h
  have hx1 : (x : ModGL F4.tag K) ≠ 1 := fun h => by
    have h' : x = 1 := Subtype.ext h
    rw [h', orderOf_one] at hx
    exact absurd hx (by norm_num)
  obtain ⟨hfus, -⟩ := large_Ree_every_involution_fuses a ha K hK
  have key : ∀ (w : Gm K a) (y : ModGL F4.tag K) (hy : y ∈ F4.reeGamma K a),
      y * (x : ModGL F4.tag K) * y⁻¹ = (w : ModGL F4.tag K) → IsConj w x := by
    intro w y hy hyx
    rw [isConj_iff]
    refine ⟨⟨y⁻¹, inv_mem hy⟩, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    show y⁻¹ * (w : ModGL F4.tag K) * (y⁻¹)⁻¹ = x
    rw [← hyx]
    group
  rcases hfus _ x.2 hx2 hx1 with ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
  · exact Or.inl (key (zg hK) y hy (by rw [coe_zg]; exact hyx))
  · exact Or.inr (key (tg hK) y hy (by rw [coe_tg]; exact hyx))

theorem reeGammaFieldAut_zg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K) :
    F4.reeGammaFieldAut K a σ (zg hK) = zg hK := by
  refine Subtype.ext ?_
  rw [coe_reeGammaFieldAut ha hK, coe_zg]
  change Units.map (entrywiseHom σ.toRingHom) (rootElt K a .i12 1) = rootElt K a .i12 1
  rw [entrywiseHom_rootElt, map_one]

theorem reeGammaFieldAut_tg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K) :
    F4.reeGammaFieldAut K a σ (tg hK) = tg hK := by
  refine Subtype.ext ?_
  rw [coe_reeGammaFieldAut ha hK, coe_tg]
  change Units.map (entrywiseHom σ.toRingHom) (rootElt K a .i10 1) = rootElt K a .i10 1
  rw [entrywiseHom_rootElt, map_one]

theorem noconj_gm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ φ : MulAut (Gm K a), φ (zg hK) ≠ tg hK := by
  intro φ hφ
  obtain ⟨x, σ, rfl⟩ := exists_conj_fieldAut ha hK φ
  rw [MulAut.mul_apply, reeGammaFieldAut_zg ha hK, MulAut.conj_apply] at hφ
  have h := congrArg Subtype.val hφ
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_zg, coe_tg] at h
  exact (reeGamma_inf_centralizer_invE_invF ha hK).2.2.2.2 x x.2 h

theorem center_gm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ w ∈ Ug K a, (∀ y ∈ Ug K a, y * w = w * y) → w ≠ 1 →
      ∃ h ∈ Pg K a ⟨1, by decide⟩ ⊓ Pg K a ⟨0, by decide⟩, h * zg hK * h⁻¹ = w := by
  intro w hw hc hw1
  have hwP : (w : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a := hw
  have hmem : (w : ModGL F4.tag K) ∈
      (((Subgroup.center ↥(F4.reeFixedPosUnipotent K a)).map
        (F4.reeFixedPosUnipotent K a).subtype : Subgroup (ModGL F4.tag K)) :
          Set (ModGL F4.tag K)) :=
    ⟨⟨w, hwP⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (by
      have hgU : (⟨(g : ModGL F4.tag K), reeFixedPosUnipotent_le_reeGamma (t := F4) (K := K)
          (a := a) g.2⟩ : Gm K a) ∈ Ug K a := g.2
      have h := congrArg Subtype.val (hc _ hgU)
      exact h), rfl⟩
  rw [coe_center_eq_range_centralZ ha hK] at hmem
  obtain ⟨c, hcw⟩ := hmem
  have hc0 : c ≠ 0 := fun h => hw1 (Subtype.ext (by
    rw [Subgroup.coe_one, ← hcw, h, ← sylowH_zero_eq_centralZ, wordH_zero]))
  have hu0 : c ^ (2 * 2 ^ a) ≠ 0 := pow_ne_zero _ hc0
  have hτ : torusPair a (Units.mk0 _ hu0, 1) * centralZ K a 1 *
      (torusPair a (Units.mk0 _ hu0, 1))⁻¹ = centralZ K a c := by
    rw [torusPair_conj_centralZ hK, Units.val_mk0, mul_one,
      CFSG.Quasithin.H13.Sec53F.ReeF4.pow_two_mul_two_pow_pow hK]
  have hmemP : ∀ j : Fin F4.fixedOrbitCount,
      (⟨torusPair a (Units.mk0 _ hu0, 1), LargeReeCover.torusPair_mem_reeGamma a hK _⟩ :
        Gm K a) ∈ Pg K a j := fun j =>
    Subgroup.mem_subgroupOf.2
      (CFSG.Quasithin.H13.Sec53F.ReeF4.torusPair_mem_reeLocalParabolic hK j _ _)
  refine ⟨⟨torusPair a (Units.mk0 _ hu0, 1), LargeReeCover.torusPair_mem_reeGamma a hK _⟩,
    Subgroup.mem_inf.2 ⟨hmemP _, hmemP _⟩, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_zg, (invE_eq_centralZ).1]
  exact hτ.trans hcw

theorem aut_z_gm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ φ : MulAut (Gm K a), φ ∈ autStab (Pg K a ⟨1, by decide⟩) →
      φ ∈ autStab (Pg K a ⟨0, by decide⟩) →
        ∃ b ∈ Pg K a ⟨1, by decide⟩ ⊓ Pg K a ⟨0, by decide⟩, φ (zg hK) = b * zg hK * b⁻¹ := by
  intro φ h1 h0
  obtain ⟨b, hb, σ, rfl⟩ := exists_of_autStab_Pg ha hK h1 h0
  exact ⟨b, hb, by rw [MulAut.mul_apply, reeGammaFieldAut_zg ha hK, MulAut.conj_apply]⟩

theorem aut_t_gm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ φ : MulAut (Gm K a), φ ∈ autStab (Pg K a ⟨1, by decide⟩) →
      φ ∈ autStab (Pg K a ⟨0, by decide⟩) →
        ∃ b ∈ Pg K a ⟨1, by decide⟩ ⊓ Pg K a ⟨0, by decide⟩, φ (tg hK) = b * tg hK * b⁻¹ := by
  intro φ h1 h0
  obtain ⟨b, hb, σ, rfl⟩ := exists_of_autStab_Pg ha hK h1 h0
  exact ⟨b, hb, by rw [MulAut.mul_apply, reeGammaFieldAut_tg ha hK, MulAut.conj_apply]⟩

end Model

end CFSG.Quasithin.H13.F431.TwoF4
