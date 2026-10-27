module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotClasses
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2TwE6Pairs
import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBAssembly
import CFSG.LieType.Chevalley.SubsystemComponent
import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootPerfectness
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalDihedralTwisted
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.OuterInv
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic
import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Cover
import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.OuterG
import CFSG.LieType.Chevalley.LangNormalizerInvolutionTorus
import CFSG.LieType.Chevalley.OrthogonalFixedOrbitRankOne
import CFSG.LieType.Chevalley.SignKernelComponentBruhat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6 CFSG.SeitzReduction

section Reps


@[expose] noncomputable def tw2e6InnerRep (K : Type) [Field K] : Fin 3 → ModGL TwistTag.E6.tag K :=
  ![CFSG.SeitzReduction.TwistedE6Pilot.repX K 0, CFSG.SeitzReduction.TwistedE6Pilot.repX K 1,
    CFSG.SeitzReduction.twistedE6ClassV K]

end Reps

private theorem tw2e6_sl2_vSL_one {F : Type*} [Field F] [CharP F 2] :
    vSL (1 : F) * uSL (1 : F) * (vSL (1 : F))⁻¹ = WSL := by
  have h1 : (vSL (1 : F))⁻¹ = vSL (1 : F) := by rw [vSL_inv, CharTwo.neg_eq]
  rw [h1]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, coe_vSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem tw2e6_sl2_vSL_inv {F : Type*} [Field F] [CharP F 2] {d : F} (hd : d ≠ 0) :
    vSL (d⁻¹) * uSL d * (vSL (d⁻¹))⁻¹ = WSL * HSL (Units.mk0 d hd)⁻¹ := by
  have h1 : (vSL (d⁻¹))⁻¹ = vSL (d⁻¹) := by rw [vSL_inv, CharTwo.neg_eq]
  rw [h1]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, coe_vSL, coe_WSL, coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero, hd]

private theorem tw2e6_commutator_eq {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) (hy : y * y = 1)
    (hconj : y * (x * y * x⁻¹ * y⁻¹) * y⁻¹ = x * y * x⁻¹ * y⁻¹) :
    x * y * x⁻¹ * y⁻¹ = y * (x * (y * x)) := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [hx', hy'] at hconj
  rw [hx', hy']
  rw [← hconj]
  simp only [mul_assoc, hy, mul_one]

private theorem tw2e6_frame_computation {G : Type*} [Group G] {N₀ N₃ X₀ X₃ Y₀ Y₃ c : G}
    (hX₀Y₃ : Commute X₀ Y₃) (hY₀X₃ : Commute Y₀ X₃) (hY₀Y₃ : Commute Y₀ Y₃)
    (hN₀ : Y₀ * X₀ * Y₀⁻¹ = N₀) (hN₃ : Y₃ * X₃ * Y₃⁻¹ = N₃)
    (hc : ∀ y, c * y = y * c) :
    Y₀ * Y₃ * (X₀ * X₃ * c) * Y₃⁻¹ * Y₀⁻¹ = N₀ * N₃ * c := by
  have hY₃X₀ : Y₃ * X₀ = X₀ * Y₃ := hX₀Y₃.symm.eq
  have hY₀N₃ : Commute Y₀ N₃ := by
    rw [← hN₃]
    exact (hY₀Y₃.mul_right hY₀X₃).mul_right hY₀Y₃.inv_right
  have hconjN₃ : Y₀ * N₃ * Y₀⁻¹ = N₃ := by
    rw [hY₀N₃.eq]
    group
  have hstep1 : Y₃ * (X₀ * X₃ * c) * Y₃⁻¹ = X₀ * N₃ * c := by
    calc Y₃ * (X₀ * X₃ * c) * Y₃⁻¹
        = (Y₃ * X₀ * Y₃⁻¹) * (Y₃ * X₃ * Y₃⁻¹) * (Y₃ * c * Y₃⁻¹) := by group
      _ = X₀ * N₃ * c := by
          rw [hN₃, show Y₃ * X₀ * Y₃⁻¹ = X₀ from by rw [hY₃X₀]; group,
            show Y₃ * c * Y₃⁻¹ = c from by rw [show Y₃ * c = c * Y₃ from (hc Y₃).symm]; group]
  have hstep2 : Y₀ * (X₀ * N₃ * c) * Y₀⁻¹ = N₀ * N₃ * c := by
    calc Y₀ * (X₀ * N₃ * c) * Y₀⁻¹
        = (Y₀ * X₀ * Y₀⁻¹) * (Y₀ * N₃ * Y₀⁻¹) * (Y₀ * c * Y₀⁻¹) := by group
      _ = N₀ * N₃ * c := by
          rw [hN₀, hconjN₃,
            show Y₀ * c * Y₀⁻¹ = c from by rw [show Y₀ * c = c * Y₀ from (hc Y₀).symm]; group]
  calc Y₀ * Y₃ * (X₀ * X₃ * c) * Y₃⁻¹ * Y₀⁻¹
      = Y₀ * (Y₃ * (X₀ * X₃ * c) * Y₃⁻¹) * Y₀⁻¹ := by group
    _ = Y₀ * (X₀ * N₃ * c) * Y₀⁻¹ := by rw [hstep1]
    _ = N₀ * N₃ * c := hstep2


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

local instance tw2e6FramesNeZero : NeZero TwistTag.E6.foldedTag.rank := ⟨by decide +kernel⟩

local instance tw2e6FramesNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide +kernel⟩

local instance tw2e6FramesNeZeroE6' : NeZero Tag.E6.rank := ⟨by decide +kernel⟩

local notation "ν₀" => (⟨0, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)

local notation "ν₃" => (⟨3, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)

private theorem tw2e6_rhat_WSL (a : Fin TwistTag.E6.foldedTag.rank) :
    Rhat hf hK σ hσ a WSL = (twistedE6CoverData hf hK σ hσ).nhat a := by
  refine Subtype.ext ?_
  rw [nhat_coe hf hK σ hσ a]
  rfl

private theorem tw2e6_commute_of_commute_coverHom {x y : ↥(TwistedE6.fixedGroup K σ)}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (h : Commute (coverHom hf hK σ hσ x) (coverHom hf hK σ hσ y)) : Commute x y := by
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx
  have hyy : y * y = 1 := by rw [← pow_two]; exact hy
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  set e : ↥(TwistedE6.fixedGroup K σ) := x * y * x⁻¹ * y⁻¹ with he
  have hker : e ∈ (coverHom hf hK σ hσ).ker := by
    rw [MonoidHom.mem_ker, he]
    simp only [map_mul, map_inv, h.eq]
    group
  have hcent : e ∈ Subgroup.center ↥(TwistedE6.fixedGroup K σ) := by
    rw [← ker_coverHom hf hK σ hσ]
    exact hker
  have he0 : e = x * y * x * y := by rw [he, hx', hy']
  have hex : e * x = x * e := (Subgroup.mem_center_iff.1 hcent x).symm
  have hconj : y * (x * y * x⁻¹ * y⁻¹) * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    rw [← he]
    exact (show y * e * y⁻¹ = e from by
      rw [show y * e = e * y from Subgroup.mem_center_iff.1 hcent y]
      group)
  have he1 : e = y * (x * (y * x)) := by
    rw [he]
    exact tw2e6_commutator_eq hxx hyy hconj
  have heinv : e⁻¹ = y * (x * (y * x)) := by
    rw [he0]
    simp only [mul_inv_rev, hx', hy']
  have hee : e * e = 1 := by
    have h2 : e * e⁻¹ = 1 := mul_inv_cancel e
    rw [heinv, ← he1] at h2
    exact h2
  have hpe : IsPElt 2 e := ⟨1, by show e ^ (2 : ℕ) = 1; rw [pow_two]; exact hee⟩
  have he1' : e = 1 := (isCentralCover_coverHom hf hK σ hσ).eq_one_of_isPElt hker hpe
  have h2 : x * y * x⁻¹ * y⁻¹ = 1 := by rw [← he]; exact he1'
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = 1 * (y * x) := by rw [h2]
    _ = y * x := one_mul _

omit
  [Finite K] in
private theorem tw2e6_conj_relWeyl_repX_one :
    twistedE6RelWeyl K [(1 : Fin TwistTag.E6.foldedTag.rank), 2, 1] *
        (pinnedX TwistTag.E6.tag K TwistedE6Pilot.rootE15 1 *
          pinnedX TwistTag.E6.tag K TwistedE6Pilot.rootE26 1) *
        (twistedE6RelWeyl K [(1 : Fin TwistTag.E6.foldedTag.rank), 2, 1])⁻¹ =
      (xC TwistTag.E6 K σ ν₀ 1 : ModGL TwistTag.E6.tag K) := by
  have hxC : (xC TwistTag.E6 K σ ν₀ 1 : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K ⟨0, by decide +kernel⟩ 1 *
        xUnit TwistTag.E6.tag K ⟨5, by decide +kernel⟩ 1 := by
    rw [show (xC TwistTag.E6 K σ ν₀ 1 :
        ModGL TwistTag.E6.tag K) =
      (orbitX TwistTag.E6 K σ ν₀ 1 :
        ModGL TwistTag.E6.tag K) from rfl]
    have h := CFSG.ComponentClassification.UnbalancingLocal.DihedralTwisted.coe_orbitX_E6_zero
      (K := K) (σ := σ) (c := (1 : orbitField TwistTag.E6 K σ ⟨0, by decide +kernel⟩))
    simp at h
    exact h
  rw [hxC]
  have h1 : twistedE6RelAct [(1 : Fin TwistTag.E6.foldedTag.rank), 2, 1]
      TwistedE6Pilot.rootE15 =
        (Pi.single ⟨0, by decide +kernel⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
    decide +kernel
  have h2 : twistedE6RelAct [(1 : Fin TwistTag.E6.foldedTag.rank), 2, 1]
      TwistedE6Pilot.rootE26 =
        (Pi.single ⟨5, by decide +kernel⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
    decide +kernel
  rw [TwistedE6Pilot.conj_mul_distrib,
    twistedE6RelWeyl_conj_pinnedX _ TwistedE6Pilot.isRoot_rootE15.1 1,
    twistedE6RelWeyl_conj_pinnedX _ TwistedE6Pilot.isRoot_rootE15.2 1, h1, h2]
  simp only [pinnedX_single]

omit
  [Finite K] in
private theorem tw2e6_conj_relWeyl_classV :
    twistedE6RelWeyl K [2, 1, 2, 3, 1, 2, 0, 1, 2, 1] * twistedE6ClassV K *
        (twistedE6RelWeyl K [2, 1, 2, 3, 1, 2, 0, 1, 2, 1])⁻¹ =
      (xC TwistTag.E6 K σ ν₀ 1 * xC TwistTag.E6 K σ ν₃ 1 : ModGL TwistTag.E6.tag K) := by
  have hx0 : (xC TwistTag.E6 K σ ν₀ 1 : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K ⟨0, by decide +kernel⟩ 1 *
        xUnit TwistTag.E6.tag K ⟨5, by decide +kernel⟩ 1 := by
    rw [show (xC TwistTag.E6 K σ ν₀ 1 :
        ModGL TwistTag.E6.tag K) =
      (orbitX TwistTag.E6 K σ ν₀ 1 :
        ModGL TwistTag.E6.tag K) from rfl]
    have h := CFSG.ComponentClassification.UnbalancingLocal.DihedralTwisted.coe_orbitX_E6_zero
      (K := K) (σ := σ) (c := (1 : orbitField TwistTag.E6 K σ ⟨0, by decide +kernel⟩))
    simp at h
    exact h
  have hx3 : (xC TwistTag.E6 K σ ν₃ 1 : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K ⟨1, by decide +kernel⟩ 1 := by
    rw [show (xC TwistTag.E6 K σ ν₃ 1 :
        ModGL TwistTag.E6.tag K) =
      (orbitX TwistTag.E6 K σ ν₃ 1 :
        ModGL TwistTag.E6.tag K) from rfl]
    have h := CFSG.ComponentClassification.UnbalancingLocal.DihedralTwisted.coe_orbitX_E6_three
      (K := K) (σ := σ) (d := (1 : orbitField TwistTag.E6 K σ ⟨3, by decide +kernel⟩))
    exact h
  rw [show (xC TwistTag.E6 K σ ν₀ 1 * xC TwistTag.E6 K σ ν₃ 1 :
      ModGL TwistTag.E6.tag K) =
      (xC TwistTag.E6 K σ ν₀ 1 : ModGL TwistTag.E6.tag K) *
        (xC TwistTag.E6 K σ ν₃ 1 : ModGL TwistTag.E6.tag K) from rfl, hx0, hx3]
  have h1 : twistedE6RelAct [2, 1, 2, 3, 1, 2, 0, 1, 2, 1] twistedE6ClassRootA =
      (Pi.single ⟨5, by decide +kernel⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) := by decide +kernel
  have h2 : twistedE6RelAct [2, 1, 2, 3, 1, 2, 0, 1, 2, 1] twistedE6ClassRootA' =
      (Pi.single ⟨0, by decide +kernel⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) := by decide +kernel
  have h3 : twistedE6RelAct [2, 1, 2, 3, 1, 2, 0, 1, 2, 1] twistedE6ClassRootB =
      (Pi.single ⟨1, by decide +kernel⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) := by decide +kernel
  rw [twistedE6ClassV, TwistedE6Pilot.conj_mul_distrib, TwistedE6Pilot.conj_mul_distrib,
    twistedE6RelWeyl_conj_pinnedX _ isRoot_twistedE6ClassRoots.2.2.1 1,
    twistedE6RelWeyl_conj_pinnedX _ isRoot_twistedE6ClassRoots.2.2.2.1 1,
    twistedE6RelWeyl_conj_pinnedX _ isRoot_twistedE6ClassRoots.2.2.2.2 1, h1, h2, h3]
  simp only [pinnedX_single]
  have hcx : xUnit TwistTag.E6.tag K ⟨0, by decide +kernel⟩ 1 *
        xUnit TwistTag.E6.tag K ⟨5, by decide +kernel⟩ 1 =
      xUnit TwistTag.E6.tag K ⟨5, by decide +kernel⟩ 1 *
        xUnit TwistTag.E6.tag K ⟨0, by decide +kernel⟩ 1 :=
    (CFSG.LieType.Chevalley.SubsysComp.commute_xUnit_xUnit_of_cartan_eq_zero
      (i := (⟨0, by decide +kernel⟩ : Fin Tag.E6.rank))
      (j := (⟨5, by decide +kernel⟩ : Fin Tag.E6.rank))
      (by decide +kernel) (by decide +kernel) 1 1).eq
  rw [hcx]

omit
  [Finite K] [CharP K 2] in
private theorem tw2e6_commute_orbitY_E6 {a b : Fin TwistTag.E6.foldedTag.rank}
    (h : ∀ i ∈ TwistTag.E6.orbit a, ∀ j ∈ TwistTag.E6.orbit b,
      TwistTag.E6.tag.symmetrizedCartan i j = 0)
    (c : orbitField TwistTag.E6 K σ a) (d : orbitField TwistTag.E6 K σ b) :
    Commute (orbitY TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K)
      (orbitY TwistTag.E6 K σ b d : ModGL TwistTag.E6.tag K) := by
  rw [coe_orbitY, coe_orbitY]
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
  rw [← pinnedX_neg_single, ← pinnedX_neg_single]
  refine commute_pinnedX_of_rootForm_eq_zero K (isRoot_neg_single _ _) (isRoot_neg_single _ _)
    ?_ _ _
  rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg,
    single_dotProduct_mulVec_single]
  exact h _ (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) k) _
    (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem b) l)

theorem tw2e6_exists_conj_mem_H_inner (i : Fin 3) {z : ↥(TwistedE6.fixedGroup K σ)}
    (hz : ((coverHom hf hK σ hσ z : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
      ModGL TwistTag.E6.tag K) = tw2e6InnerRep K i) :
    ∃ g : ↥(TwistedE6.fixedGroup K σ),
      ((twistedE6CoverData hf hK σ hσ).nhatW
          ((relCs TwistTag.E6).wordProd (tw2e6InnerWord i)))⁻¹ * (g * z * g⁻¹) ∈
        (twistedE6CoverData hf hK σ hσ).datum.H := by
  have hi : i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) := by
    fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  ·
    have hword : (twistedE6CoverData hf hK σ hσ).nhatW
        ((relCs TwistTag.E6).wordProd (tw2e6InnerWord 0)) =
        (twistedE6CoverData hf hK σ hσ).nhat (2 : Fin TwistTag.E6.foldedTag.rank) := by
      have hw := twNhatW_wordProd (f := f) (K := K) (hf := hf) (hK := hK) (σ := σ) (hσ := hσ)
        (l := tw2e6InnerWord 0)
      rw [hw]
      simp only [tw2e6InnerWord]
      congr 1
    have hz2 : coverHom hf hK σ hσ z =
        xC TwistTag.E6 K σ ⟨2, by decide +kernel⟩ 1 := by
      refine Subtype.ext ?_
      rw [hz]
      show tw2e6InnerRep K 0 =
        (xC TwistTag.E6 K σ ⟨2, by decide +kernel⟩ 1 : ModGL TwistTag.E6.tag K)
      rw [show (xC TwistTag.E6 K σ ⟨2, by decide +kernel⟩ 1 : ModGL TwistTag.E6.tag K) =
          (orbitX TwistTag.E6 K σ ⟨2, by decide +kernel⟩ 1 : ModGL TwistTag.E6.tag K) from rfl,
        coe_orbitX_E6_two]
      rw [← pinnedX_single]
      rfl
    set x : ↥(TwistedE6.fixedGroup K σ) :=
      hatX hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 with hxdef
    set c : ↥(TwistedE6.fixedGroup K σ) := x⁻¹ * z with hcdef
    have hxH : coverHom hf hK σ hσ x = xC TwistTag.E6 K σ ⟨2, by decide +kernel⟩ 1 :=
      coverHom_hatX hf hK σ hσ _ 1
    have hcπ : coverHom hf hK σ hσ c = 1 := by
      rw [hcdef, map_mul, map_inv, hxH, hz2, inv_mul_cancel]
    refine ⟨hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1, ?_⟩
    rw [hword]
    have hsl2 : hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 * x *
        (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1)⁻¹ =
        (twistedE6CoverData hf hK σ hσ).nhat (2 : Fin TwistTag.E6.foldedTag.rank) := by
      have h := congrArg (Rhat hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank))
        (tw2e6_sl2_vSL_one (F := orbitField TwistTag.E6 K σ (2 : Fin TwistTag.E6.foldedTag.rank)))
      simp only [map_mul, map_inv] at h
      rw [Rhat_uSL, Rhat_vSL, tw2e6_rhat_WSL] at h
      exact h
    have hcH : c ∈ (twistedE6CoverData hf hK σ hσ).datum.H := by
      show coverHom hf hK σ hσ c ∈ (twistedE6Datum hf hK σ hσ).H
      rw [hcπ]
      exact one_mem _
    have hzc : z = x * c := by rw [hcdef]; group
    have hcc : ∀ y, c * y = y * c := by
      have hcZ : c ∈ Subgroup.center ↥(TwistedE6.fixedGroup K σ) := by
        rw [← ker_coverHom hf hK σ hσ]
        exact MonoidHom.mem_ker.2 hcπ
      exact fun y => (Subgroup.mem_center_iff.1 hcZ y).symm
    have hmain : ((twistedE6CoverData hf hK σ hσ).nhat (2 : Fin TwistTag.E6.foldedTag.rank))⁻¹ *
        (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 * z *
          (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1)⁻¹) = c := by
      have e1 : hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 * z *
          (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1)⁻¹ =
          (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 * x *
            (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1)⁻¹) * c := by
        rw [hzc]
        calc hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 * (x * c) *
            (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1)⁻¹ =
            (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 * x) *
              (c * (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1)⁻¹) := by group
          _ = (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 * x) *
              ((hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1)⁻¹ * c) := by rw [hcc]
          _ = (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1 * x *
              (hatY hf hK σ hσ (2 : Fin TwistTag.E6.foldedTag.rank) 1)⁻¹) * c := by group
      rw [e1, hsl2]
      group
    rw [hmain]
    exact hcH
  ·
    obtain ⟨g₁, hg₁⟩ := (isCentralCover_coverHom hf hK σ hσ).surj
      (⟨twistedE6RelWeyl K [(1 : Fin TwistTag.E6.foldedTag.rank), 2, 1],
        twistedE6RelWeyl_mem σ _⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ))
    have hzrep : ((coverHom hf hK σ hσ z : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
        ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K TwistedE6Pilot.rootE15 1 *
          pinnedX TwistTag.E6.tag K TwistedE6Pilot.rootE26 1 := by
      rw [hz]
      rfl
    have hconj : coverHom hf hK σ hσ (g₁ * z * g₁⁻¹) = xC TwistTag.E6 K σ ν₀ 1 := by
      refine Subtype.ext ?_
      rw [map_mul, map_mul, map_inv, hg₁]
      show twistedE6RelWeyl K [(1 : Fin TwistTag.E6.foldedTag.rank), 2, 1] *
          ((coverHom hf hK σ hσ z : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
            ModGL TwistTag.E6.tag K) *
          (twistedE6RelWeyl K [(1 : Fin TwistTag.E6.foldedTag.rank), 2, 1])⁻¹ =
          (xC TwistTag.E6 K σ ν₀ 1 : ModGL TwistTag.E6.tag K)
      rw [hzrep, tw2e6_conj_relWeyl_repX_one]
    set x : ↥(TwistedE6.fixedGroup K σ) := hatX hf hK σ hσ ν₀ 1 with hxdef
    set c : ↥(TwistedE6.fixedGroup K σ) := x⁻¹ * (g₁ * z * g₁⁻¹) with hcdef
    have hxH : coverHom hf hK σ hσ x = xC TwistTag.E6 K σ ν₀ 1 :=
      coverHom_hatX hf hK σ hσ ν₀ 1
    have hcπ : coverHom hf hK σ hσ c = 1 := by
      rw [hcdef, map_mul, map_inv, hxH, hconj, inv_mul_cancel]
    have hcH : c ∈ (twistedE6CoverData hf hK σ hσ).datum.H := by
      show coverHom hf hK σ hσ c ∈ (twistedE6Datum hf hK σ hσ).H
      rw [hcπ]
      exact one_mem _
    have hcZ : c ∈ Subgroup.center ↥(TwistedE6.fixedGroup K σ) := by
      rw [← ker_coverHom hf hK σ hσ]
      exact MonoidHom.mem_ker.2 hcπ
    have hcc : ∀ y, c * y = y * c := fun y => (Subgroup.mem_center_iff.1 hcZ y).symm
    refine ⟨hatY hf hK σ hσ ν₀ 1 * g₁, ?_⟩
    have hword : (twistedE6CoverData hf hK σ hσ).nhatW
        ((relCs TwistTag.E6).wordProd (tw2e6InnerWord 1)) =
        (twistedE6CoverData hf hK σ hσ).nhat ν₀ := by
      have hw := twNhatW_wordProd (f := f) (K := K) (hf := hf) (hK := hK) (σ := σ) (hσ := hσ)
        (l := tw2e6InnerWord 1)
      rw [hw]
      simp only [tw2e6InnerWord]
      congr 1
    rw [hword]
    have hsl2 : hatY hf hK σ hσ ν₀ 1 * x * (hatY hf hK σ hσ ν₀ 1)⁻¹ =
        (twistedE6CoverData hf hK σ hσ).nhat ν₀ := by
      have h := congrArg (Rhat hf hK σ hσ ν₀)
        (tw2e6_sl2_vSL_one (F := orbitField TwistTag.E6 K σ ν₀))
      simp only [map_mul, map_inv] at h
      rw [Rhat_uSL, Rhat_vSL, tw2e6_rhat_WSL] at h
      exact h
    have hmain : ((twistedE6CoverData hf hK σ hσ).nhat ν₀)⁻¹ *
        ((hatY hf hK σ hσ ν₀ 1 * g₁) * z * (hatY hf hK σ hσ ν₀ 1 * g₁)⁻¹) = c := by
      have e0 : (hatY hf hK σ hσ ν₀ 1 * g₁) * z * (hatY hf hK σ hσ ν₀ 1 * g₁)⁻¹ =
          hatY hf hK σ hσ ν₀ 1 * (g₁ * z * g₁⁻¹) * (hatY hf hK σ hσ ν₀ 1)⁻¹ := by group
      have hzc : g₁ * z * g₁⁻¹ = x * c := by rw [hcdef]; group
      have e1 : hatY hf hK σ hσ ν₀ 1 * (g₁ * z * g₁⁻¹) * (hatY hf hK σ hσ ν₀ 1)⁻¹ =
          (hatY hf hK σ hσ ν₀ 1 * x * (hatY hf hK σ hσ ν₀ 1)⁻¹) * c := by
        rw [hzc]
        calc hatY hf hK σ hσ ν₀ 1 * (x * c) * (hatY hf hK σ hσ ν₀ 1)⁻¹ =
            (hatY hf hK σ hσ ν₀ 1 * x) * (c * (hatY hf hK σ hσ ν₀ 1)⁻¹) := by group
          _ = (hatY hf hK σ hσ ν₀ 1 * x) * ((hatY hf hK σ hσ ν₀ 1)⁻¹ * c) := by rw [hcc]
          _ = (hatY hf hK σ hσ ν₀ 1 * x * (hatY hf hK σ hσ ν₀ 1)⁻¹) * c := by group
      rw [e0, e1, hsl2]
      group
    rw [hmain]
    exact hcH
  ·
    obtain ⟨g₁, hg₁⟩ := (isCentralCover_coverHom hf hK σ hσ).surj
      (⟨twistedE6RelWeyl K [2, 1, 2, 3, 1, 2, 0, 1, 2, 1], twistedE6RelWeyl_mem σ _⟩ :
        ↥(graphFixedRootGroup TwistTag.E6 K σ))
    have hzrep : ((coverHom hf hK σ hσ z : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
        ModGL TwistTag.E6.tag K) = twistedE6ClassV K := by
      rw [hz]
      rfl
    have hconj : coverHom hf hK σ hσ (g₁ * z * g₁⁻¹) =
        xC TwistTag.E6 K σ ν₀ 1 * xC TwistTag.E6 K σ ν₃ 1 := by
      refine Subtype.ext ?_
      rw [map_mul, map_mul, map_inv, hg₁]
      show twistedE6RelWeyl K [2, 1, 2, 3, 1, 2, 0, 1, 2, 1] *
          ((coverHom hf hK σ hσ z : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
            ModGL TwistTag.E6.tag K) *
          (twistedE6RelWeyl K [2, 1, 2, 3, 1, 2, 0, 1, 2, 1])⁻¹ =
          (xC TwistTag.E6 K σ ν₀ 1 * xC TwistTag.E6 K σ ν₃ 1 : ModGL TwistTag.E6.tag K)
      rw [hzrep, tw2e6_conj_relWeyl_classV]
    set x : ↥(TwistedE6.fixedGroup K σ) := hatX hf hK σ hσ ν₀ 1 * hatX hf hK σ hσ ν₃ 1
      with hxdef
    set c : ↥(TwistedE6.fixedGroup K σ) := x⁻¹ * (g₁ * z * g₁⁻¹) with hcdef
    have hxH : coverHom hf hK σ hσ x = xC TwistTag.E6 K σ ν₀ 1 * xC TwistTag.E6 K σ ν₃ 1 := by
      rw [hxdef, map_mul, coverHom_hatX, coverHom_hatX]
    have hcπ : coverHom hf hK σ hσ c = 1 := by
      rw [hcdef, map_mul, map_inv, hxH, hconj, inv_mul_cancel]
    have hcH : c ∈ (twistedE6CoverData hf hK σ hσ).datum.H := by
      show coverHom hf hK σ hσ c ∈ (twistedE6Datum hf hK σ hσ).H
      rw [hcπ]
      exact one_mem _
    have hcZ : c ∈ Subgroup.center ↥(TwistedE6.fixedGroup K σ) := by
      rw [← ker_coverHom hf hK σ hσ]
      exact MonoidHom.mem_ker.2 hcπ
    have hcc : ∀ y, c * y = y * c := fun y => (Subgroup.mem_center_iff.1 hcZ y).symm
    have hX₀Y₃ : Commute (hatX hf hK σ hσ ν₀ 1) (hatY hf hK σ hσ ν₃ 1) := by
      refine tw2e6_commute_of_commute_coverHom hf hK σ hσ (hatX_sq hf hK σ hσ ν₀ 1)
        (hatY_sq hf hK σ hσ ν₃ 1) ?_
      rw [coverHom_hatX, coverHom_hatY]
      exact Subtype.ext (commute_orbitX_orbitY_of_ne (by decide) 1 1).eq
    have hY₀X₃ : Commute (hatY hf hK σ hσ ν₀ 1) (hatX hf hK σ hσ ν₃ 1) := by
      refine tw2e6_commute_of_commute_coverHom hf hK σ hσ (hatY_sq hf hK σ hσ ν₀ 1)
        (hatX_sq hf hK σ hσ ν₃ 1) ?_
      rw [coverHom_hatY, coverHom_hatX]
      exact Subtype.ext (commute_orbitX_orbitY_of_ne (by decide) 1 1).symm.eq
    have hY₀Y₃ : Commute (hatY hf hK σ hσ ν₀ 1) (hatY hf hK σ hσ ν₃ 1) := by
      refine tw2e6_commute_of_commute_coverHom hf hK σ hσ (hatY_sq hf hK σ hσ ν₀ 1)
        (hatY_sq hf hK σ hσ ν₃ 1) ?_
      rw [coverHom_hatY, coverHom_hatY]
      exact Subtype.ext (tw2e6_commute_orbitY_E6 (σ := σ) (fun i hi j hj => by
        revert hi hj
        fin_cases i <;> fin_cases j <;> decide) 1 1).eq
    have hN₀ : hatY hf hK σ hσ ν₀ 1 * hatX hf hK σ hσ ν₀ 1 *
        (hatY hf hK σ hσ ν₀ 1)⁻¹ = (twistedE6CoverData hf hK σ hσ).nhat ν₀ := by
      have h := congrArg (Rhat hf hK σ hσ ν₀)
        (tw2e6_sl2_vSL_one (F := orbitField TwistTag.E6 K σ ν₀))
      simp only [map_mul, map_inv] at h
      rw [Rhat_uSL, Rhat_vSL, tw2e6_rhat_WSL] at h
      exact h
    have hN₃ : hatY hf hK σ hσ ν₃ 1 * hatX hf hK σ hσ ν₃ 1 *
        (hatY hf hK σ hσ ν₃ 1)⁻¹ = (twistedE6CoverData hf hK σ hσ).nhat ν₃ := by
      have h := congrArg (Rhat hf hK σ hσ ν₃)
        (tw2e6_sl2_vSL_one (F := orbitField TwistTag.E6 K σ ν₃))
      simp only [map_mul, map_inv] at h
      rw [Rhat_uSL, Rhat_vSL, tw2e6_rhat_WSL] at h
      exact h
    refine ⟨hatY hf hK σ hσ ν₀ 1 * hatY hf hK σ hσ ν₃ 1 * g₁, ?_⟩
    have hword : (twistedE6CoverData hf hK σ hσ).nhatW
        ((relCs TwistTag.E6).wordProd (tw2e6InnerWord 2)) =
        (twistedE6CoverData hf hK σ hσ).nhat ν₀ *
          (twistedE6CoverData hf hK σ hσ).nhat ν₃ := by
      have hw := twNhatW_wordProd (f := f) (K := K) (hf := hf) (hK := hK) (σ := σ) (hσ := hσ)
        (l := tw2e6InnerWord 2)
      rw [hw]
      simp only [tw2e6InnerWord]
      congr 1
    rw [hword]
    have hmain : ((twistedE6CoverData hf hK σ hσ).nhat ν₀ *
        (twistedE6CoverData hf hK σ hσ).nhat ν₃)⁻¹ *
        ((hatY hf hK σ hσ ν₀ 1 * hatY hf hK σ hσ ν₃ 1 * g₁) * z *
          (hatY hf hK σ hσ ν₀ 1 * hatY hf hK σ hσ ν₃ 1 * g₁)⁻¹) = c := by
      have e0 : (hatY hf hK σ hσ ν₀ 1 * hatY hf hK σ hσ ν₃ 1 * g₁) * z *
          (hatY hf hK σ hσ ν₀ 1 * hatY hf hK σ hσ ν₃ 1 * g₁)⁻¹ =
          hatY hf hK σ hσ ν₀ 1 * hatY hf hK σ hσ ν₃ 1 * (g₁ * z * g₁⁻¹) *
            (hatY hf hK σ hσ ν₃ 1)⁻¹ * (hatY hf hK σ hσ ν₀ 1)⁻¹ := by group
      have hzc : g₁ * z * g₁⁻¹ = x * c := by rw [hcdef]; group
      have e1 : hatY hf hK σ hσ ν₀ 1 * hatY hf hK σ hσ ν₃ 1 * (g₁ * z * g₁⁻¹) *
          (hatY hf hK σ hσ ν₃ 1)⁻¹ * (hatY hf hK σ hσ ν₀ 1)⁻¹ =
          hatY hf hK σ hσ ν₀ 1 * hatY hf hK σ hσ ν₃ 1 *
            ((hatX hf hK σ hσ ν₀ 1 * hatX hf hK σ hσ ν₃ 1) * c) *
            (hatY hf hK σ hσ ν₃ 1)⁻¹ * (hatY hf hK σ hσ ν₀ 1)⁻¹ := by
        rw [hzc, hxdef]
      rw [e0, e1, tw2e6_frame_computation hX₀Y₃ hY₀X₃ hY₀Y₃ hN₀ hN₃ hcc]
      group
    rw [hmain]
    exact hcH

theorem tw2e6_exists_conj_mem_H_outer {d : orbitField TwistTag.E6 K σ twN0} (hd : d ≠ 0)
    {z : ↥(TwistedE6.fixedGroup K σ)}
    (hz : coverHom hf hK σ hσ z = xC TwistTag.E6 K σ twN0 d) :
    ∃ g : ↥(TwistedE6.fixedGroup K σ),
      ((twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd [twN0]))⁻¹ *
          (g * z * g⁻¹) ∈ (twistedE6CoverData hf hK σ hσ).datum.H := by
  set x : ↥(TwistedE6.fixedGroup K σ) := hatX hf hK σ hσ twN0 d with hxdef
  set c : ↥(TwistedE6.fixedGroup K σ) := x⁻¹ * z with hcdef
  have hxH : coverHom hf hK σ hσ x = xC TwistTag.E6 K σ twN0 d :=
    coverHom_hatX hf hK σ hσ twN0 d
  have hcπ : coverHom hf hK σ hσ c = 1 := by
    rw [hcdef, map_mul, map_inv, hxH, hz, inv_mul_cancel]
  have hcH : c ∈ (twistedE6CoverData hf hK σ hσ).datum.H := by
    show coverHom hf hK σ hσ c ∈ (twistedE6Datum hf hK σ hσ).H
    rw [hcπ]
    exact one_mem _
  have hcZ : c ∈ Subgroup.center ↥(TwistedE6.fixedGroup K σ) := by
    rw [← ker_coverHom hf hK σ hσ]
    exact MonoidHom.mem_ker.2 hcπ
  have hcc : ∀ y, c * y = y * c := fun y => (Subgroup.mem_center_iff.1 hcZ y).symm
  refine ⟨hatY hf hK σ hσ twN0 (d⁻¹), ?_⟩
  have hword : (twistedE6CoverData hf hK σ hσ).nhatW
      ((relCs TwistTag.E6).wordProd [twN0]) = (twistedE6CoverData hf hK σ hσ).nhat twN0 := by
    rw [twNhatW_wordProd]
    simp
  rw [hword]
  have hsl2 : hatY hf hK σ hσ twN0 (d⁻¹) * x * (hatY hf hK σ hσ twN0 (d⁻¹))⁻¹ =
      (twistedE6CoverData hf hK σ hσ).nhat twN0 *
        hatH hf hK σ hσ twN0 (Units.mk0 d hd)⁻¹ := by
    have h := congrArg (Rhat hf hK σ hσ twN0)
      (tw2e6_sl2_vSL_inv (F := orbitField TwistTag.E6 K σ twN0) hd)
    simp only [map_mul, map_inv] at h
    rw [Rhat_uSL, Rhat_vSL, Rhat_HSL, tw2e6_rhat_WSL] at h
    exact h
  have hmain : ((twistedE6CoverData hf hK σ hσ).nhat twN0)⁻¹ *
      (hatY hf hK σ hσ twN0 (d⁻¹) * z * (hatY hf hK σ hσ twN0 (d⁻¹))⁻¹) =
      hatH hf hK σ hσ twN0 (Units.mk0 d hd)⁻¹ * c := by
    have hz' : z = x * c := by rw [hcdef]; group
    have e1 : hatY hf hK σ hσ twN0 (d⁻¹) * z * (hatY hf hK σ hσ twN0 (d⁻¹))⁻¹ =
        (hatY hf hK σ hσ twN0 (d⁻¹) * x * (hatY hf hK σ hσ twN0 (d⁻¹))⁻¹) * c := by
      rw [hz']
      calc hatY hf hK σ hσ twN0 (d⁻¹) * (x * c) * (hatY hf hK σ hσ twN0 (d⁻¹))⁻¹ =
          (hatY hf hK σ hσ twN0 (d⁻¹) * x) * (c * (hatY hf hK σ hσ twN0 (d⁻¹))⁻¹) := by group
        _ = (hatY hf hK σ hσ twN0 (d⁻¹) * x) *
            ((hatY hf hK σ hσ twN0 (d⁻¹))⁻¹ * c) := by rw [hcc]
        _ = (hatY hf hK σ hσ twN0 (d⁻¹) * x * (hatY hf hK σ hσ twN0 (d⁻¹))⁻¹) * c := by group
    rw [e1, hsl2]
    group
  rw [hmain]
  exact mul_mem ((twistedE6CoverRankOne hf hK σ hσ).hh_mem twN0 (Units.mk0 d hd)⁻¹) hcH

theorem tw2e6_rep_eq_of_coverHom_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (hχ : ∀ h ∈ (twistedE6CoverData hf hK σ hσ).datum.H, χ h = 1)
    {z z' : ↥(TwistedE6.fixedGroup K σ)}
    (hzz : coverHom hf hK σ hσ z = coverHom hf hK σ hσ z') : ρ z = ρ z' := by
  set c : ↥(TwistedE6.fixedGroup K σ) := z⁻¹ * z' with hcdef
  have hcπ : coverHom hf hK σ hσ c = 1 := by
    rw [hcdef, map_mul, map_inv, hzz, inv_mul_cancel]
  have hcH : c ∈ (twistedE6CoverData hf hK σ hσ).datum.H := by
    show coverHom hf hK σ hσ c ∈ (twistedE6Datum hf hK σ hσ).H
    rw [hcπ]
    exact one_mem _
  have hcZ : c ∈ Subgroup.center ↥(TwistedE6.fixedGroup K σ) := by
    rw [← ker_coverHom hf hK σ hσ]
    exact MonoidHom.mem_ker.2 hcπ
  have hcg : ∀ g : ↥(TwistedE6.fixedGroup K σ), ρ c * ρ g = ρ g * ρ c := by
    intro g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hcZ g).symm]
  have hcy : ρ c y = y := by
    rw [ht.2.2.1 c hcH, hχ c hcH, one_smul]
  set W : Submodule k V := LinearMap.ker (ρ c - 1) with hW
  have hstable : ∀ g : ↥(TwistedE6.fixedGroup K σ), ∀ w ∈ W, ρ g w ∈ W := by
    intro g w hw
    rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw ⊢
    calc ρ c (ρ g w) = (ρ c * ρ g) w := rfl
      _ = (ρ g * ρ c) w := by rw [hcg]
      _ = ρ g (ρ c w) := rfl
      _ = ρ g w := by rw [hw]
  have hyW : y ∈ W := by
    rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hcy
  have hWtop : W = ⊤ := by
    rcases hρ.2 W hstable with h | h
    · exfalso
      have hy0 : y = 0 := by
        have : y ∈ (⊥ : Submodule k V) := h ▸ hyW
        simpa using this
      exact ht.2.1 hy0
    · exact h
  have hc1 : ρ c = 1 := by
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ W := by rw [hWtop]; exact Submodule.mem_top
    rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    simpa using hv
  have hz' : z' = z * c := by rw [hcdef]; group
  rw [hz', map_mul, hc1, mul_one]

end CFSG.LocalAnalysis.WeakClosure81

