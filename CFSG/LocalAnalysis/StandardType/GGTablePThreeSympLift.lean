module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.LocalAnalysis.StandardType.GGL45NtClRecipes
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem sympLift_charP {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rwa [← Nat.card_eq_fintype_card])

private theorem sympLift_center_eq_bot {K : Type} [Field K] [Fintype K] [CharP K 2] (m : ℕ) :
    Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) = ⊥ := by
  have hb := CFSG.HardMathSupport.C14Cl.sp_proj_bijective (K := K) m
  let e : CFSG.Open.StatedSp m K ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m)) hb
  have hmap := Subgroup.map_center_eq e
  rw [← hmap, CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := K) m,
    Subgroup.map_bot]

private theorem sympLift_proj_injective {K : Type} [Field K] [Fintype K] [CharP K 2] (m : ℕ) :
    Function.Injective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K) :=
  (CFSG.HardMathSupport.C14Cl.sp_proj_bijective (K := K) m).1

private noncomputable def sympLift_conjHom (m : ℕ) (K : Type) [Field K] :
    CFSG.Open.StatedSp m K →* MulAut (LargeEvenProj (LargeEvenSpGroup K m)) :=
  (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut _).comp
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K)

theorem sympShape_lift {K : Type} [Field K] [Finite K] {n m : ℕ} (hK : Nat.card K = 2 ^ n)
    {Ā : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))}
    {δ' : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    {J' : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hR : RDatum Ā δ' J')
    (hĀ : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m)) :
    ∃ x : CFSG.Open.StatedSp m K, x ^ 3 = 1 ∧ x ≠ 1 ∧
      δ' = MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x) ∧
      ∃ E : Subgroup (CFSG.Open.StatedSp m K),
        E ≤ Subgroup.centralizer ({x} : Set (CFSG.Open.StatedSp m K)) ∧
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = Nat.card Ā := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := sympLift_charP hK
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hZ := sympLift_center_eq_bot (K := K) m
  let c := sympLift_conjHom m K
  have hc_inj : Function.Injective c := by
    intro g h hgh
    have h1 : c (g * h⁻¹) = 1 := by rw [map_mul, map_inv, hgh, mul_inv_cancel]
    have hcentral : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K (g * h⁻¹) ∈
        Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) := by
      rw [Subgroup.mem_center_iff]
      intro r
      have hr : MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K
          (g * h⁻¹)) r = r := by
        have hh := congrArg (fun f : MulAut (LargeEvenProj (LargeEvenSpGroup K m)) => f r) h1
        simpa [c, sympLift_conjHom] using hh
      have hzr : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K (g * h⁻¹) * r =
          r * CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K (g * h⁻¹) := by
        rw [MulAut.conj_apply] at hr
        calc CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K (g * h⁻¹) * r =
            (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K (g * h⁻¹) * r *
              (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K (g * h⁻¹))⁻¹) *
              CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K (g * h⁻¹) := by group
          _ = r * CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K (g * h⁻¹) := by
            rw [hr]
      exact hzr.symm
    rw [hZ, Subgroup.mem_bot] at hcentral
    have hgh1 : g * h⁻¹ = 1 :=
      sympLift_proj_injective (K := K) m (by rw [hcentral, map_one])
    exact mul_inv_eq_one.mp hgh1
  have hsurj : Ā ≤ c.range := by
    intro a ha
    obtain ⟨A, hA⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage
        (hĀ a ha)
    obtain ⟨x, hx⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj h2 A
    exact ⟨x, by show c x = a; exact hx.symm.trans hA⟩
  let E : Subgroup (CFSG.Open.StatedSp m K) := Ā.comap c
  have hEmap : E.map c = Ā := Subgroup.map_comap_eq_self hsurj
  let eE : ↥E ≃* ↥Ā :=
    (Subgroup.equivMapOfInjective E c hc_inj).trans (MulEquiv.subgroupCongr hEmap)
  have hcard : Nat.card E = Nat.card Ā := Nat.card_congr eE.toEquiv
  have hEelem : CFSG.Open.IsElemAbelian 3 E :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.of_mulEquiv eE.symm
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hR.elem))
  have hmem : δ' ∈ E.map c := by rw [hEmap]; exact hR.mem
  obtain ⟨x, hxE, hcx⟩ := Subgroup.mem_map.mp hmem
  refine ⟨x, ?_, ?_, ?_, E, ?_, hEelem, hcard⟩
  · have hxA : c x ∈ Ā := by rw [hcx]; exact hR.mem
    have h3 : (c x) ^ 3 = 1 := hR.elem.2 (c x) hxA
    exact hc_inj (by rw [map_pow, h3, map_one])
  · intro hx1
    exact hR.ne_one (by rw [← hcx, hx1, map_one])
  · exact hcx.symm
  ·
    intro g hg
    haveI : IsMulCommutative E := hEelem.1
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : E) (⟨x, hxE⟩ : E)))

end CFSG.StandardType.TablePThreeKG

end
