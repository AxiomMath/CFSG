module

public import CFSG.Quasithin.Background.F7TwoInv2F4Z
public import CFSG.Quasithin.Background.F7TwoInv2F4T
public import CFSG.Quasithin.Background.F7TwoInvSQTKFam
public import CFSG.Quasithin.Background.F7TwoInvSeed
public import CFSG.LieType.Ree.LargeReeInvolutionFusion
public import CFSG.LieType.Ree.LargeReeCenterTrivial
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel

public section

namespace CFSG.Quasithin.F7Two

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.UnbalancedCatalog

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {m : ℕ}

theorem invAutGen_reeGamma_conj (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {g : ↥(F4.reeGamma K m)} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    InvAutGen ↥(F4.reeGamma K m) (MulAut.conj g) := by
  have hg2' : (g : ModGL F4.tag K) ^ 2 = 1 := by
    have h := congrArg Subtype.val hg2
    simpa [sq] using h
  have hg1' : (g : ModGL F4.tag K) ≠ 1 := fun h => hg1 (Subtype.ext h)
  rcases (large_Ree_every_involution_fuses m hm K hK).1 g g.2 hg2' hg1' with
    ⟨x, hx, hxg⟩ | ⟨x, hx, hxg⟩
  · have hz := sylowH_zero_one_mem (m := m) (K := K) hK
    refine invAutGen_conj_of_isConj (r := ⟨sylowH m K 0 1, hz⟩) ?_
      (invAutGen_conj_of_le_closure hz (invGen_zOne hm hK).ge)
    refine isConj_iff.2 ⟨⟨x⁻¹, inv_mem hx⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hxg]
    group
  · have ht : sylowL m K 1 ∈ F4.reeGamma K m := tKernel_le_reeGamma (sylowL_mem_tKernel hK 1)
    refine invAutGen_conj_of_isConj (r := ⟨sylowL m K 1, ht⟩) ?_
      (invAutGen_conj_of_le_closure ht (invGen_tOne hm hK).ge)
    refine isConj_iff.2 ⟨⟨x⁻¹, inv_mem hx⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hxg]
    group

theorem invAutGenFam2F4 : InvAutGenFam2F4 := by
  unfold InvAutGenFam2F4
  intro f S _ _ hodd h3 hmodel φ hφ2 hφ1
  obtain ⟨-, -, -, -, -, hinner, htr⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions S 2 f hmodel
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e₀⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  have hKa : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have ha : 1 ≤ a := by omega
  obtain ⟨⟨e⟩, -⟩ := htr a K hfa hK ⟨e₀⟩
  obtain ⟨s, hs⟩ := hinner φ (by rw [sq]; exact hφ2)
  have hZ : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ Subgroup.center ↥(F4.reeGamma K a) :=
      (MulEquivClass.apply_mem_center_iff e).2 hx
    rw [large_Ree_fixed_group_center_trivial a K hKa, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (e.injective (h1.trans (map_one e).symm))
  have hs2 : s * s = 1 := mul_self_eq_one_of_conj_mul_self hZ (by rw [hs]; exact hφ2)
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hφ1 (by rw [← hs, map_one])
  have hg := invAutGen_reeGamma_conj ha hKa (g := e s)
    (by rw [← map_mul, hs2, map_one]) (fun h => hs1 (e.injective (h.trans (map_one e).symm)))
  have hφe : φ = (e.symm.symm.trans (MulAut.conj (e s))).trans e.symm := by
    refine MulEquiv.ext fun x => ?_
    rw [← hs]
    simp [MulAut.conj_apply]
  rw [hφe]
  exact InvAutGen.congr e.symm hg

end CFSG.Quasithin.F7Two
