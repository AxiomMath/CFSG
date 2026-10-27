module

public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
public import CFSG.LocalAnalysis.StandardType.GGFinModelIndex
public import CFSG.LocalAnalysis.StandardType.GGFinModelCornerModel
import CFSG.RankThree.PartOne.S11c.G2Torus

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped commutatorElement

namespace GGDatumModel

private theorem g4bPowMod (ζ : GGLˣ) (hζ : ζ ^ 3 = 1) {a b : ℤ} (h : a ≡ b [ZMOD 3]) :
    ζ ^ a = ζ ^ b := by
  have hdvd : orderOf ζ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hζ
  have h3 : a ≡ b [ZMOD (orderOf ζ : ℤ)] :=
    Int.ModEq.of_dvd (by exact_mod_cast hdvd) h
  exact (zpow_eq_zpow_iff_modEq).mpr h3

private theorem g4bZModSmulVal {N : ℕ} (c : ℤ) (v : Fin N → ZMod 3) :
    (c : ZMod 3) • v = ZMod.val (c : ZMod 3) • v := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (ZMod 3)]
  simp only [smul_eq_mul]
  rw [ZMod.natCast_zmod_val]

private noncomputable def g4bParamMulHom {R : ℕ} (hR : R = Tag.E6.rank) (ζ : GGLˣ)
    (hζ : ζ ^ 3 = 1) : Multiplicative (Fin R → ZMod 3) →* (Fin Tag.E6.rank → GGLˣ) where
  toFun z := ggParam hR ζ (Multiplicative.toAdd z)
  map_one' := by simp [ggParam_zero hR ζ]
  map_mul' a b := by rw [toAdd_mul, ggParam_add hR hζ]

private theorem g4bParamDecomp {R : ℕ} (hR : R = Tag.E6.rank) (ζ : GGLˣ) (hζ : ζ ^ 3 = 1)
    (c : Fin R → ℤ) (v : Fin R → Fin R → ZMod 3) (w : Fin R → ZMod 3)
    (hw : w = ∑ j, (c j : ZMod 3) • v j) :
    ggParam hR ζ w = ∏ j, (ggParam hR ζ (v j)) ^ (ZMod.val (c j : ZMod 3)) := by
  subst hw
  calc ggParam hR ζ (∑ j, (c j : ZMod 3) • v j)
      = g4bParamMulHom hR ζ hζ
          (Multiplicative.ofAdd (∑ j, (c j : ZMod 3) • v j)) := rfl
    _ = g4bParamMulHom hR ζ hζ
          (∏ j, Multiplicative.ofAdd ((c j : ZMod 3) • v j)) := by rw [ofAdd_sum]
    _ = ∏ j, g4bParamMulHom hR ζ hζ
          (Multiplicative.ofAdd ((c j : ZMod 3) • v j)) := by rw [map_prod]
    _ = ∏ j, (g4bParamMulHom hR ζ hζ
          (Multiplicative.ofAdd (v j))) ^ (ZMod.val (c j : ZMod 3)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [g4bZModSmulVal, ofAdd_nsmul, map_pow]
    _ = ∏ j, (ggParam hR ζ (v j)) ^ (ZMod.val (c j : ZMod 3)) := rfl

private theorem g4bParamGen {R : ℕ} (hR : R = Tag.E6.rank) (ζ : GGLˣ) (hζ : ζ ^ 3 = 1)
    (j : Fin R) :
    ggParam hR ζ (fun i : Fin R => (Tag.E6.cartan (Fin.cast hR j) (Fin.cast hR i) : ZMod 3)) =
      fun i : Fin Tag.E6.rank => ζ ^ Tag.E6.cartan (Fin.cast hR j) i := by
  funext i
  show ζ ^ ZMod.val (Tag.E6.cartan (Fin.cast hR j) (Fin.cast hR (Fin.cast hR.symm i)) : ZMod 3) =
    ζ ^ Tag.E6.cartan (Fin.cast hR j) i
  rw [show Fin.cast hR (Fin.cast hR.symm i) = i from Fin.ext rfl, ← zpow_natCast]
  exact g4bPowMod ζ hζ (by rw [ZMod.val_intCast]; exact Int.mod_modEq _ 3)

private theorem g4bE6_hm
    (j : Fin Tag.E6.rank) (δ : Fin Tag.E6.rank → ℤ) :
    2 * iform (Pi.single j 1) δ / iform (Pi.single j 1) (Pi.single j 1) =
      ∑ i, δ i * Tag.cartan Tag.E6 j i := by
  rw [iform_single_left, iform_single_single]
  have hs : Tag.symmetrizer Tag.E6 = 1 := rfl
  rw [hs]
  simp only [Matrix.one_apply_eq, one_mul, mul_one]
  have hnum : (2 : ℤ) * (∑ i, Tag.cartan Tag.E6 j i * δ i) =
      (∑ i, δ i * Tag.cartan Tag.E6 j i) * 2 := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hnum]
  exact Int.mul_ediv_cancel _ (by norm_num)

private theorem g4bCornerDiag
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t} (M : GGDatumModel t f p ht)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hc : GGCorner t p f)
    (z : Multiplicative (ggFixAdd p (piB t p f)))
    (hz : (Multiplicative.toAdd z).1 ∈ LatCorootSpan (ggU (absTag t) 6 f).D p) :
    rootDiagUnit (langTag t)
      (ggParam (rank_eq_langTag f ht) (ggZeta p hp hp2) (Multiplicative.toAdd z).1) ∈
        M.D.Γ := by
  have hc0 := hc
  rcases hc with ⟨hp3, hcase⟩
  subst hp3
  rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
    (have hz' : (Multiplicative.toAdd z).1 ∈ LatCorootSpan (ggU .E6 6 f).D 3 := hz
     have hR : (ggU .E6 6 f).D.rank = Tag.E6.rank := rank_eq_langTag f ht
     let D : LangDatum Tag.E6 GGL := M.D
     have hζ : (ggZeta 3 hp hp2) ^ 3 = 1 := by
       have h := pow_orderOf_eq_one (ggZeta 3 hp hp2)
       rwa [ggZeta_order 3 hp hp2] at h
     let ζ : GGLˣ := ggZeta 3 hp hp2
     change rootDiagUnit Tag.E6
       (ggParam hR ζ (Multiplicative.toAdd z).1) ∈ D.Γ
     obtain ⟨c, hcsum⟩ := hz'
     let v : Fin ((ggU .E6 6 f).D.rank) →
         Fin ((ggU .E6 6 f).D.rank) → ZMod 3 :=
       fun j i => (Tag.E6.cartan (Fin.cast hR j) (Fin.cast hR i) : ZMod 3)
     have hcart : ∀ j i : Fin ((ggU .E6 6 f).D.rank),
         (ggU .E6 6 f).D.cartan j i =
           Tag.E6.cartan (Fin.cast hR j) (Fin.cast hR i) := fun j i => rfl
     have hwv : (Multiplicative.toAdd z).1 = fun i => ∑ j, (c j : ZMod 3) * v j i := by
       funext i
       rw [hcsum i]
       refine Finset.sum_congr rfl (fun j _ => ?_)
       rw [hcart j i]
     have hdecomp := g4bParamDecomp hR ζ hζ c v (Multiplicative.toAdd z).1 hwv
     have hbase : ∀ j : Fin ((ggU .E6 6 f).D.rank),
         rootDiagUnit Tag.E6 (ggParam hR ζ (v j)) ∈ D.Γ := by
       intro j
       have hgen : ggParam hR ζ
             (fun i : Fin ((ggU .E6 6 f).D.rank) =>
               (Tag.E6.cartan (Fin.cast hR j) (Fin.cast hR i) : ZMod 3)) =
           fun i : Fin Tag.E6.rank => ζ ^ Tag.E6.cartan (Fin.cast hR j) i :=
         g4bParamGen hR ζ hζ j
       change rootDiagUnit Tag.E6 (ggParam hR ζ
         (fun i : Fin ((ggU .E6 6 f).D.rank) =>
           (Tag.E6.cartan (Fin.cast hR j) (Fin.cast hR i) : ZMod 3))) ∈ D.Γ
       rw [hgen]
       obtain ⟨hW, hHSL⟩ := rootSL2_mem_model_of_corner M hc0
         (isRoot_single Tag.E6 (Fin.cast hR j)) hζ
       have hW' : rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) WSL ∈ D.model := hW
       have hHSL' : rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) (HSL ζ⁻¹) ∈
           D.model := hHSL
       have hSLcomm : ⁅(HSL ζ⁻¹ : SL2 GGL), (WSL : SL2 GGL)⁆ = HSL ζ := by
         rw [CFSG.StandardType.LangRat.commutatorElement_HSL_WSL]
         congr 1
         rw [inv_pow, inv_eq_iff_mul_eq_one, ← pow_succ]
         exact hζ
       have hM2 : rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) (HSL ζ) =
           ⁅rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) (HSL ζ⁻¹),
             rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) WSL⁆ := by
         calc rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) (HSL ζ)
             = rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1)
                 ⁅(HSL ζ⁻¹ : SL2 GGL), (WSL : SL2 GGL)⁆ := by rw [hSLcomm]
           _ = ⁅rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) (HSL ζ⁻¹),
                 rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) WSL⁆ :=
                 map_commutatorElement _ _ _
       have hmemΓ : rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) (HSL ζ) ∈ D.Γ := by
         rw [hM2]
         exact Subgroup.commutator_mem_commutator hHSL' hW'
       have hM1 : rootSL2 Tag.E6 GGL (Pi.single (Fin.cast hR j) 1) (HSL ζ) =
           rootDiagUnit Tag.E6
             (fun i : Fin Tag.E6.rank => ζ ^ Tag.E6.cartan (Fin.cast hR j) i) :=
         CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit
           (isRoot_single Tag.E6 (Fin.cast hR j))
           (fun i : Fin Tag.E6.rank => Tag.E6.cartan (Fin.cast hR j) i)
           (fun δ _ => g4bE6_hm (Fin.cast hR j) δ) ζ
       rw [← hM1]
       exact hmemΓ
     let S : Subgroup (Fin Tag.E6.rank → GGLˣ) :=
       D.Γ.comap (rootDiagUnitHom Tag.E6 GGL)
     have hbaseS : ∀ j, ggParam hR ζ (v j) ∈ S :=
       fun j => Subgroup.mem_comap.mpr (hbase j)
     have hgoalS : ggParam hR ζ (Multiplicative.toAdd z).1 ∈ S := by
       rw [hdecomp]
       exact Subgroup.prod_mem S (fun j _ => Subgroup.pow_mem S (hbaseS j) _)
     exact Subgroup.mem_comap.mp hgoalS)

theorem uMap_mem_range_of_corner
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t} (M : GGDatumModel t f p ht) {n : ℕ}
    [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (hc : GGCorner t p f) (z : Multiplicative (ggFixAdd p (piB t p f)))
    (hz : (Multiplicative.toAdd z).1 ∈ LatCorootSpan (ggU (absTag t) 6 f).D p) :
    (M.torusData (n := n) hf hp hp2 hreg).uMap z ∈ (ggIota t n f hf).range := by
  have hΓ := g4bCornerDiag M hp hp2 hc z hz
  rw [(M.torusData (n := n) hf hp hp2 hreg).uMap_apply z]
  have hmap : M.D.Γ.map (MulAut.conj M.D.g0).toMonoidHom = (ggIota t n f hf).range := by
    rw [LangDatum.map_conj_Γ M.D, (M.torusData (n := n) hf hp hp2 hreg).pkg.desc.derived]
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨_, hΓ, rfl⟩

end GGDatumModel

end CFSG.StandardType.GGFinModel
