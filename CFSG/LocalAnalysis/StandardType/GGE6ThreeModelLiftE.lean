module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K]

private theorem weylElt_conj_zetaVec_eq {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (i : Fin Tag.E6.rank)
    (x : Fin Tag.E6.rank → ZMod 3) :
    (fun j => zetaVec ζ hζ x j * (zetaVec ζ hζ x i) ^ (-Tag.E6.cartan i j)) =
      zetaVec ζ hζ (adRefl .E6 3 i x) := by
  funext j
  simp only [zetaVec, Pi.mul_apply, Pi.pow_apply]
  rw [zmodPowHom_zpow, ← map_mul, ← ofAdd_add, adRefl]
  congr 1
  congr 1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_neg]
  ring

private theorem zetaVec_sub {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (a b : Fin Tag.E6.rank → ZMod 3) :
    zetaVec ζ hζ (a - b) = zetaVec ζ hζ a * (zetaVec ζ hζ b)⁻¹ := by
  funext j
  simp only [zetaVec, Pi.sub_apply, Pi.mul_apply, Pi.inv_apply]
  rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add, ← sub_eq_add_neg]

private theorem conj_weylElt_rootDiagAut (i : Fin Tag.E6.rank) (a : Fin Tag.E6.rank → Kˣ) :
    MulAut.conj (⟨weylElt .E6 K i 1, weylElt_mem_adjointGroup (τ := .E6) (K := K) i 1⟩ :
        adjointGroup .E6 K) * rootDiagAut .E6 K a *
      (MulAut.conj (⟨weylElt .E6 K i 1, weylElt_mem_adjointGroup (τ := .E6) (K := K) i 1⟩ :
        adjointGroup .E6 K))⁻¹ =
    rootDiagAut .E6 K (weylTuple (simple .E6 i) a) := by
  have hconj : weylElt .E6 K i 1 * rootDiagUnit .E6 a * (weylElt .E6 K i 1)⁻¹ =
      rootDiagUnit .E6 (weylTuple (simple .E6 i) a) := by
    rw [← canonicalRep_simple (cs := coxeterSystem .E6) (R := K) i,
      canonicalRep_conj_rootDiagUnit]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, coe_rootDiagAut,
    Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hconj]
  group

private theorem rootDiagUnit_zetaVec_mem_torusGroup {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    {v : Fin Tag.E6.rank → ZMod 3} (hv : v ∈ NoOffRest.hypE6) :
    rootDiagUnit .E6 (zetaVec ζ hζ v) ∈ torusGroup .E6 K := by
  obtain ⟨y, hy⟩ := NoOffE6Three.zetaVec_eq_cartanChar_of_mem_hyp ζ hζ hv
  rw [hy, ← list_prod_torusElt_eq_rootDiagUnit]
  exact Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact Subgroup.subset_closure ⟨(j, zetaVec ζ hζ y j), rfl⟩

private theorem coboundary_eq_rootDiagUnit {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (i : Fin Tag.E6.rank)
    (x : Fin Tag.E6.rank → ZMod 3) :
    ((⟨weylElt .E6 K i 1, weylElt_mem_adjointGroup (τ := .E6) (K := K) i 1⟩ : adjointGroup .E6 K) *
      (NoOffE6Three.diag3 ζ hζ (Multiplicative.ofAdd x)
        ⟨weylElt .E6 K i 1, weylElt_mem_adjointGroup (τ := .E6) (K := K) i 1⟩)⁻¹ :
        ModGL .E6 K) =
      rootDiagUnit .E6 (zetaVec ζ hζ (adRefl .E6 3 i x - x)) := by
  have h1 : weylElt .E6 K i 1 * rootDiagUnit .E6 (zetaVec ζ hζ x) *
      (weylElt .E6 K i 1)⁻¹ = rootDiagUnit .E6 (zetaVec ζ hζ (adRefl .E6 3 i x)) := by
    rw [weylElt_conj_rootDiagUnit, weylElt_conj_zetaVec_eq hζ i x]
  show weylElt .E6 K i 1 * (rootDiagUnit .E6 (zetaVec ζ hζ x) * weylElt .E6 K i 1 *
      (rootDiagUnit .E6 (zetaVec ζ hζ x))⁻¹)⁻¹ =
      rootDiagUnit .E6 (zetaVec ζ hζ (adRefl .E6 3 i x - x))
  calc
    weylElt .E6 K i 1 * (rootDiagUnit .E6 (zetaVec ζ hζ x) * weylElt .E6 K i 1 *
        (rootDiagUnit .E6 (zetaVec ζ hζ x))⁻¹)⁻¹
        = weylElt .E6 K i 1 * rootDiagUnit .E6 (zetaVec ζ hζ x) *
            (weylElt .E6 K i 1)⁻¹ * (rootDiagUnit .E6 (zetaVec ζ hζ x))⁻¹ := by group
    _ = rootDiagUnit .E6 (zetaVec ζ hζ (adRefl .E6 3 i x)) *
            (rootDiagUnit .E6 (zetaVec ζ hζ x))⁻¹ := by rw [h1]
    _ = rootDiagUnit .E6 (zetaVec ζ hζ (adRefl .E6 3 i x) * (zetaVec ζ hζ x)⁻¹) := by
          rw [rootDiagUnit_mul, rootDiagUnit_inv]
    _ = rootDiagUnit .E6 (zetaVec ζ hζ (adRefl .E6 3 i x - x)) := by rw [zetaVec_sub]

theorem eFrame_weyl [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (eFrame K ζ hζ).WeylOK := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hsq : weylElt .E6 K i 1 ^ 2 = torusElt .E6 K i (-1) := weylElt_one_sq .E6 K i
    have htd : torusElt .E6 K i (-1) = 1 := by
      have h1 : (-1 : Kˣ) = 1 := Units.ext (CharTwo.neg_eq (1 : K))
      rw [h1]
      exact torusElt_one (τ := .E6) (R := K) i
    apply Subtype.ext
    show weylElt .E6 K i 1 * weylElt .E6 K i 1 = 1
    rw [← sq, hsq, htd]
  · intro i t ht
    apply Subgroup.mem_subgroupOf.mpr
    exact weylElt_mul_mul_inv_mem_torus (τ := .E6) (R := K) i 1 (Subgroup.mem_subgroupOf.mp ht)
  · intro i x
    have hnb : MulAut.conj ((eFrame K ζ hζ).nb i) = MulAut.conj
        (⟨weylElt .E6 K i 1, weylElt_mem_adjointGroup (τ := .E6) (K := K) i 1⟩ :
          adjointGroup .E6 K) := rfl
    have hadx : (eFrame K ζ hζ).ad x = rootDiagAut .E6 K (zetaVec ζ hζ x) := by
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [show ((eFrame K ζ hζ).ad x g : ModGL .E6 K) =
          rootDiagUnit .E6 (zetaVec ζ hζ x) * (g : ModGL .E6 K) *
            (rootDiagUnit .E6 (zetaVec ζ hζ x))⁻¹ from
          NoOffE6Three.diag3_apply ζ hζ x g]
      rw [coe_rootDiagAut]
    have hadr : (eFrame K ζ hζ).ad (adRefl .E6 3 i x) = rootDiagAut .E6 K
        (zetaVec ζ hζ (adRefl .E6 3 i x)) := by
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [show ((eFrame K ζ hζ).ad (adRefl .E6 3 i x) g : ModGL .E6 K) =
          rootDiagUnit .E6 (zetaVec ζ hζ (adRefl .E6 3 i x)) * (g : ModGL .E6 K) *
            (rootDiagUnit .E6 (zetaVec ζ hζ (adRefl .E6 3 i x)))⁻¹ from
          NoOffE6Three.diag3_apply ζ hζ (adRefl .E6 3 i x) g]
      rw [coe_rootDiagAut]
    have h := conj_weylElt_rootDiagAut (K := K) i (zetaVec ζ hζ x)
    have had : adAct .E6 3 (simple .E6 i) x = adRefl .E6 3 i x :=
      adAct_simple (τ := .E6) (p := 3) i x
    rw [hnb, hadx, hadr, h, weylTuple_zetaVec, had]
  · intro i x
    let v : Fin Tag.E6.rank → ZMod 3 := adRefl .E6 3 i x - x
    have hv : v ∈ NoOffRest.hypE6 := by
      rw [NoOffRest.mem_hypE6, NoOffRest.kDotP_sub,
        NoOffRest.kDotP_adRefl (NoOffRest.kDot_cartan i), sub_self]
    have heq : (((eFrame K ζ hζ).nb i * ((eFrame K ζ hζ).ad x ((eFrame K ζ hζ).nb i))⁻¹ :
        adjointGroup .E6 K) : ModGL .E6 K) = rootDiagUnit .E6 (zetaVec ζ hζ v) :=
      coboundary_eq_rootDiagUnit hζ i x
    refine ⟨?_, v, hv, ?_⟩
    · apply Subgroup.mem_subgroupOf.mpr
      rw [heq]
      exact rootDiagUnit_zetaVec_mem_torusGroup (K := K) hζ hv
    · refine MulEquiv.ext fun g => Subtype.ext ?_
      show (((eFrame K ζ hζ).nb i * ((eFrame K ζ hζ).ad x ((eFrame K ζ hζ).nb i))⁻¹ :
          adjointGroup .E6 K) : ModGL .E6 K) * (g : ModGL .E6 K) *
          ((((eFrame K ζ hζ).nb i * ((eFrame K ζ hζ).ad x ((eFrame K ζ hζ).nb i))⁻¹ :
            adjointGroup .E6 K)) : ModGL .E6 K)⁻¹ =
        rootDiagUnit .E6 (zetaVec ζ hζ v) * (g : ModGL .E6 K) *
          (rootDiagUnit .E6 (zetaVec ζ hζ v))⁻¹
      rw [heq]

end CFSG.StandardType.E6ThreeModel
