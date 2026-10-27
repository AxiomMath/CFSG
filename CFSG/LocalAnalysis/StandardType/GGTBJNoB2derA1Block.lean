module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1Sp
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCent
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derFixOrth
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
import all CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open Polynomial CFSG.Open CFSG.Assembly CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.StandardType.ChoiceTwo
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Bridge

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} [NeZero r]

theorem sympA6_spRep_proj (x : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    (SmallRule.spRep (proj r K x) : Module.End K (Fin r ⊕ Fin r → K)) v = spEnd x v := by
  have h : TableBSymp.spProjEquivSp (K := K) (m := r) (proj r K x) = x :=
    CFSG.SeitzReduction.F4Pilot.spProjEquiv_symm_proj x
  rw [SmallRule.spRep_apply, h, spEnd_apply, mat_apply]

theorem sympA6_mem_fixSpace (x : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    v ∈ SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x)) ↔
      spEnd x v = v := by
  constructor
  · intro h
    have := SmallRule.mem_fixSpaceOf.mp h (proj r K x) (Subgroup.mem_zpowers _)
    rwa [sympA6_spRep_proj] at this
  · intro h
    let ρ : LargeEvenProj (LargeEvenSpGroup K r) →* (Module.End K (Fin r ⊕ Fin r → K))ˣ :=
      SmallRule.spRep
    let S : Subgroup (LargeEvenProj (LargeEvenSpGroup K r)) :=
      { carrier := {u | (ρ u : Module.End K (Fin r ⊕ Fin r → K)) v = v}
        one_mem' := by
          change (ρ 1 : Module.End K (Fin r ⊕ Fin r → K)) v = v
          rw [map_one, Units.val_one, Module.End.one_apply]
        mul_mem' := by
          intro a b ha hb
          change (ρ (a * b) : Module.End K (Fin r ⊕ Fin r → K)) v = v
          rw [SmallRule.rho_mul_apply]
          have ha' : (ρ a : Module.End K (Fin r ⊕ Fin r → K)) v = v := ha
          have hb' : (ρ b : Module.End K (Fin r ⊕ Fin r → K)) v = v := hb
          rw [hb', ha']
        inv_mem' := by
          intro a ha
          change (ρ a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) v = v
          have ha' : (ρ a : Module.End K (Fin r ⊕ Fin r → K)) v = v := ha
          calc (ρ a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) v
              = (ρ a⁻¹ : Module.End K (Fin r ⊕ Fin r → K))
                  ((ρ a : Module.End K (Fin r ⊕ Fin r → K)) v) := by rw [ha']
            _ = (ρ (a⁻¹ * a) : Module.End K (Fin r ⊕ Fin r → K)) v :=
                  (SmallRule.rho_mul_apply ρ a⁻¹ a v).symm
            _ = v := by rw [inv_mul_cancel, map_one, Units.val_one, Module.End.one_apply] }
    have hxS : proj r K x ∈ S := by
      change (ρ (proj r K x) : Module.End K (Fin r ⊕ Fin r → K)) v = v
      exact (sympA6_spRep_proj x v).trans h
    intro u hu
    have hu' : u ∈ S := Subgroup.zpowers_le.mpr hxS hu
    exact hu'

theorem sympA6_finrank_fixSpace (x : StatedSp r K) :
    Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x))) =
      spFixedDim x := by
  have h : SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x)) =
      primaryComponent (spEnd x) (X - 1) := by
    ext v
    rw [sympA6_mem_fixSpace, mem_primaryComponent, aeval_X_sub_one_apply, sub_eq_zero]
  rw [h]
  rfl

end Bridge

section Fixer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} [NeZero r]

theorem sympA6_spEnd_cube {x : StatedSp r K} (hx3 : x ^ 3 = 1) (v : Fin r ⊕ Fin r → K) :
    spEnd x (spEnd x (spEnd x v)) = v := by
  rw [← spEnd_mul_apply, ← spEnd_mul_apply, ← pow_three', hx3, spEnd_one_apply]

theorem sympA6_spBilin_spEnd (x : StatedSp r K) (a b : Fin r ⊕ Fin r → K) :
    SmallRule.spBilin K r (spEnd x a) (spEnd x b) = SmallRule.spBilin K r a b := by
  rw [← sympA6_spRep_proj, ← sympA6_spRep_proj]
  exact SmallRule.spRep_isometry _ a b

theorem sympA6_decomp (hK : Nat.card K = 2) {x : StatedSp r K} (hx3 : x ^ 3 = 1) :
    IsCompl (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x)))
        ((SmallRule.spBilin K r).orthogonal
          (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x)))) ∧
      ∀ v ∈ (SmallRule.spBilin K r).orthogonal
          (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x))),
        spEnd x v ∈ (SmallRule.spBilin K r).orthogonal
          (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x))) := by
  have hz3 : (proj r K x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨hc, -, hU, -⟩ := ggB2der_fix_orth_decomp hK (SmallRule.spRep (K := K) (m := r))
    (SmallRule.spBilin K r) SmallRule.spBilin_nondegenerate SmallRule.spBilin_isRefl
    (fun g v w => SmallRule.spRep_isometry g v w) hz3
  refine ⟨hc, fun v hv => ?_⟩
  have := hU (proj r K x) rfl v hv
  rwa [sympA6_spRep_proj] at this

theorem sympA6_orthogonal_iff (hK : Nat.card K = 2) {x : StatedSp r K} (hx3 : x ^ 3 = 1)
    (v : Fin r ⊕ Fin r → K) :
    v ∈ (SmallRule.spBilin K r).orthogonal
        (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x))) ↔
      spEnd x (spEnd x v) + spEnd x v + v = 0 := by
  obtain ⟨hcompl, hTU⟩ := sympA6_decomp hK hx3
  set W := SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x)) with hW
  set B := SmallRule.spBilin K r with hB
  have hT3 := sympA6_spEnd_cube hx3
  have hc2 : ∀ w : K, w + w = 0 := fun w => CharTwo.add_self_eq_zero w
  constructor
  · intro hv
    have h1 : spEnd x v ∈ B.orthogonal W := hTU v hv
    have h2 : spEnd x (spEnd x v) ∈ B.orthogonal W := hTU _ h1
    have hPU : spEnd x (spEnd x v) + spEnd x v + v ∈ B.orthogonal W :=
      Submodule.add_mem _ (Submodule.add_mem _ h2 h1) hv
    have hPW : spEnd x (spEnd x v) + spEnd x v + v ∈ W := by
      rw [hW, sympA6_mem_fixSpace, map_add, map_add, hT3 v]
      abel
    exact (Submodule.disjoint_def.mp hcompl.disjoint) _ hPW hPU
  · intro hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have hTw : spEnd x w = w := (sympA6_mem_fixSpace x w).mp hw
    have e1 : B w (spEnd x v) = B w v := by
      have := sympA6_spBilin_spEnd x w v
      rwa [hTw] at this
    have e2 : B w (spEnd x (spEnd x v)) = B w (spEnd x v) := by
      have := sympA6_spBilin_spEnd x w (spEnd x v)
      rwa [hTw] at this
    have h0 : B w (spEnd x (spEnd x v) + spEnd x v + v) = 0 := by rw [hv, map_zero]
    rw [map_add, map_add, e2, e1] at h0
    have h3 : B w v + B w v + B w v = B w v := by rw [hc2, zero_add]
    exact h3 ▸ h0

theorem sympA6_map_spFixedFactor (hK : Nat.card K = 2) {x : StatedSp r K} (hx3 : x ^ 3 = 1) :
    (spFixedFactor x).map (proj r K) =
      ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x))) := by
  obtain ⟨hcompl, hTU⟩ := sympA6_decomp hK hx3
  set W := SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (proj r K x)) with hW
  set B := SmallRule.spBilin K r with hB
  have hUchar := sympA6_orthogonal_iff hK hx3
  have hnot : phi3 K ∉ ({X - 1} : Set K[X]) := fun h => phi3_ne_X_sub_one h
  have hWU : B.orthogonal (B.orthogonal W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal SmallRule.spBilin_nondegenerate
      SmallRule.spBilin_isRefl W
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    change ∀ v ∈ B.orthogonal W,
      (SmallRule.spRep (proj r K s) : Module.End K (Fin r ⊕ Fin r → K)) v = v
    intro v hv
    rw [sympA6_spRep_proj]
    exact fix_of_mem_spSupported hs (phi3_irreducible hK) monic_phi3 hnot
      (by rw [aeval_phi3_apply]; exact (hUchar v).mp hv)
  · intro ha
    change ∀ v ∈ B.orthogonal W,
      (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v = v at ha
    obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective a
    refine ⟨s, ?_, rfl⟩
    have hfix : ∀ u ∈ B.orthogonal W, spEnd s u = u := fun u hu => by
      have := ha u hu
      rwa [sympA6_spRep_proj] at this
    have hsW : ∀ w ∈ W, spEnd s w ∈ W := fun w hw => by
      have hw' : w ∈ B.orthogonal (B.orthogonal W) := by rw [hWU]; exact hw
      rw [← hWU, LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      have h1 : B u (spEnd s w) = B (spEnd s u) (spEnd s w) := by rw [hfix u hu]
      change B u (spEnd s w) = 0
      rw [h1, sympA6_spBilin_spEnd]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hw') u hu
    have hcomm : s * x = x * s := by
      refine eq_of_spEnd_eq' fun v => ?_
      obtain ⟨w, hw, u, hu, rfl⟩ : ∃ w ∈ W, ∃ u ∈ B.orthogonal W, w + u = v := by
        have : v ∈ W ⊔ B.orthogonal W := by rw [hcompl.sup_eq_top]; trivial
        exact Submodule.mem_sup.mp this
      have hxw : spEnd x w = w := (sympA6_mem_fixSpace x w).mp hw
      have hxu : spEnd x u ∈ B.orthogonal W := hTU u hu
      have hsw : spEnd s w ∈ W := hsW w hw
      calc spEnd (s * x) (w + u) = spEnd s (spEnd x (w + u)) := spEnd_mul_apply _ _ _
        _ = spEnd s w + spEnd x u := by rw [map_add, hxw, map_add, hfix _ hxu]
        _ = spEnd x (spEnd s w) + spEnd x u := by
            rw [(sympA6_mem_fixSpace x _).mp hsw]
        _ = spEnd x (spEnd s (w + u)) := by rw [map_add, hfix u hu, map_add]
        _ = spEnd (x * s) (w + u) := (spEnd_mul_apply _ _ _).symm
    exact mem_spSupported_of hK hx3 hcomm (fun h => absurd (Set.mem_singleton _) h)
      (fun _ v hv => hfix v ((hUchar v).mpr hv))

end Fixer

section Assembly

theorem symplecticBlockPositionInput_holds :
    SymplecticBlockPositionInput := by
  intro K _ _ _ hK r _ hr g hg1 hg3 J hJ hlab
  obtain ⟨x, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective g
  have hbij : Function.Bijective (proj r K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  have hx3 : x ^ 3 = 1 := by
    have h3 : MulAut.conj (proj r K x ^ 3) = 1 := by rw [map_pow]; exact hg3
    have hz : proj r K x ^ 3 ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K r)) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := DFunLike.congr_fun h3 h
      rw [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [TableBSymp.center_spProj_eq_bot, Subgroup.mem_bot] at hz
    exact hbij.1 (by rw [map_pow, hz, map_one])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hg1 (by rw [map_one, map_one])
  have hfix : ggFixSub (MulAut.conj (proj r K x)) = fixSubgroup (MulAut.conj (proj r K x)) :=
    Subgroup.ext fun _ => Iff.rfl
  have hJ' : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj r K x))) := by
    rw [← hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.1 hJ
  obtain ⟨hd4, hJeq⟩ := sp_a6_component_position hK hx3 hx1 hJ' (ggB2der_label_iso_A6 hlab)
  refine ⟨by rw [sympA6_finrank_fixSpace]; exact hd4, ?_⟩
  rw [hJeq, Subgroup.map_commutator, sympA6_map_spFixedFactor hK hx3]

end Assembly

end CFSG.StandardType.S2MathAs4B2der1822

end
