module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrameData
public import Certificates.Certificate1953
public import Certificates.Certificate1954
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrame
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem excPlusFrameModelOn_E6Two_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    GGExcPlusFrameModelOn .F4 3 4 (adjointGroup .E6 K) := by
  classical
  have h3 : 3 ∣ Nat.card K + 1 := by rw [hK]
  obtain ⟨F, hsurj⟩ := ExcFrames.E6QPlusThree.exists_e6QPlusThreeFrame_weyl_surjective h3
  intro E hE hcard hsc
  have hFel : IsElemAbelian 3 F.frame.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨s, hs⟩ := a.2
      obtain ⟨t, ht⟩ := b.2
      apply Subtype.ext
      change (a : adjointGroup .E6 K) * b = b * a
      rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨s, rfl⟩ := hx
      rw [← map_pow]
      have : s ^ 3 = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
        have h3z : ((3 : ℕ) : ZMod 3) = 0 := ZMod.natCast_self 3
        rw [h3z, zero_mul]
      rw [this, map_one]
  have hFcard : 3 ^ 4 ≤ Nat.card F.frame.range := by
    rw [Nat.card_congr (MonoidHom.ofInjective F.frame_injective).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨d, hd⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hE hcard
  obtain ⟨d', hd'⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hFel hFcard
  have hc : E = F.frame.range.map (MulAut.conj (d⁻¹ * d')).toMonoidHom := by
    have h1 : E = ((TableBExc.E6Three.torusE6Two (K := K) h2).range).map
        (MulAut.conj d⁻¹).toMonoidHom := by
      rw [← hd, Subgroup.map_map]
      have hcomp : (MulAut.conj d⁻¹).toMonoidHom.comp (MulAut.conj d).toMonoidHom =
          MonoidHom.id _ := by
        refine MonoidHom.ext fun x => ?_
        show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x
        group
      rw [hcomp, Subgroup.map_id]
    rw [h1, ← hd', Subgroup.map_map]
    congr 1
  set c := d⁻¹ * d' with hcdef
  choose a ha using hsurj
  refine ⟨(MulAut.conj c).toMonoidHom.comp F.frame,
    fun i => c * ((a (simple .F4 i) : F.N) : adjointGroup .E6 K) * c⁻¹,
    (MulAut.conj c).injective.comp F.frame_injective, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hc]
  · intro i s
    have h1 := F.conj_frame (a (simple .F4 i)) s
    rw [ha] at h1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h1]
    group
  · intro g hg
    set x : adjointGroup .E6 K := c⁻¹ * g * c with hx
    have hxN : x ∈ F.N := by
      refine F.mem_N_of_conj x fun s => ?_
      have hmem : g * (c * F.frame s * c⁻¹) * g⁻¹ ∈ E := by
        refine (Subgroup.mem_normalizer_iff.mp hg _).mp ?_
        rw [hc]
        exact ⟨F.frame s, ⟨s, rfl⟩, rfl⟩
      rw [hc] at hmem
      obtain ⟨y, hy, hyeq⟩ := hmem
      have : x * F.frame s * x⁻¹ = y := by
        have hyeq' : c * y * c⁻¹ = g * (c * F.frame s * c⁻¹) * g⁻¹ := hyeq
        rw [hx]
        calc c⁻¹ * g * c * F.frame s * (c⁻¹ * g * c)⁻¹
            = c⁻¹ * (g * (c * F.frame s * c⁻¹) * g⁻¹) * c := by group
          _ = c⁻¹ * (c * y * c⁻¹) * c := by rw [hyeq']
          _ = y := by group
      rw [this]
      exact hy
    refine ⟨F.weyl ⟨x, hxN⟩, fun s => ?_⟩
    have h1 := F.conj_frame ⟨x, hxN⟩ s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h1]
    change g * (c * F.frame (Multiplicative.ofAdd s) * c⁻¹) * g⁻¹ =
      c * (x * F.frame (Multiplicative.ofAdd s) * x⁻¹) * c⁻¹
    rw [hx]
    group

theorem ggTorusReflGenW_E6Two_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusReflGenW 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  exact ggTorusReflGenW_of_excPlusModel Nat.prime_three (by norm_num)
    (ggExcPlusWeylModelSCr_of_frameModelOn Nat.prime_three
      (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK hφ)
      (ggCenterPrime_recipe_E6_two hK Nat.prime_three)
      ((excPlusFrameModelOn_E6Two_three hK).of_mulEquiv (TableBExc.recipeEquiv .E6 K)))

theorem ggNbrTableBWeylNonSplitOn_e6Two :
    GGNbrTableBWeylNonSplitOn GGNbrNonSplitE6TwoLabel := by
  intro p _ _ lab _ hS _
  obtain ⟨htag, hn1, rfl⟩ := hS
  have hW : LargeEvenLabelAll lab fun R _ I _ => GGTorusReflGenW 3 4 R I := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hn1
    subst htag
    subst hn1
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusReflGenW_E6Two_three (by rw [hK]; rfl)⟩
  exact (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_E6_two ⟨htag, hn1⟩) hW).mono
    fun _ _ _ _ ⟨hl, hw⟩ _ _ => ⟨4, hl, hw⟩

end CFSG.StandardType

end
