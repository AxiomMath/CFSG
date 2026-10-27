module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentralizerPort
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE6Cent
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.Blueprint.Chevalley
open CFSG.StandardType.TableBExc.E6Three

section Certificates


private theorem e6Cent_centralizer_le_adjoint {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup .E6 K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) :
    Subgroup.centralizer (E : Set (adjointGroup .E6 K)) ≤ E := by
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  intro c hc
  obtain ⟨g, hg⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hE hcard
  have hcent : (MulAut.conj g).toMonoidHom c ∈ Subgroup.centralizer
      ((torusE6Two (K := K) h2).range : Set (adjointGroup .E6 K)) := by
    rw [← hg, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    have hce : e * c = c * e := (Subgroup.mem_centralizer_iff.mp hc) e he
    rw [← map_mul, ← map_mul, hce]
  have hmem : (MulAut.conj g).toMonoidHom c ∈ E.map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact CFSG.LocalAnalysis.GLTheoremA.T173O.centralizer_range_torusE6Two_le h2 hK hcent
  exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).mp hmem

private theorem e6Cent_centralizer_le {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    {E : Subgroup (TableBExc.RecipeGroup .E6 K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) :
    Subgroup.centralizer (E : Set (TableBExc.RecipeGroup .E6 K)) ≤ E := by
  let ρ : TableBExc.RecipeGroup .E6 K ≃* adjointGroup .E6 K := TableBExc.recipeEquiv .E6 K
  let E' : Subgroup (adjointGroup .E6 K) := E.map ρ.toMonoidHom
  have hE' : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE ρ.toMonoidHom
  have hcard' : 3 ^ 4 ≤ Nat.card E' := by
    rw [show E' = E.map ρ.toMonoidHom from rfl,
      Subgroup.card_map_of_injective (f := ρ.toMonoidHom) ρ.injective]
    exact hcard
  have hcent' : Subgroup.centralizer (E' : Set (adjointGroup .E6 K)) ≤ E' :=
    e6Cent_centralizer_le_adjoint h2 hK hE' hcard'
  intro c hc
  have hc' : ρ.toMonoidHom c ∈ Subgroup.centralizer (E' : Set (adjointGroup .E6 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    have hce : e * c = c * e := (Subgroup.mem_centralizer_iff.mp hc) e he
    rw [← map_mul, ← map_mul, hce]
  exact (Subgroup.mem_map_iff_mem (K := E) ρ.injective).mp (hcent' hc')

private theorem e6Cent_actionThree_recipe {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    {A : Subgroup (MulAut (TableBExc.RecipeGroup .E6 K))}
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 4 ≤ Nat.card A) : actionThree A := by
  have hZ : Subgroup.center (TableBExc.RecipeGroup .E6 K) = ⊥ :=
    TableBExc.center_recipeGroup_eq_bot .E6 K
  have hinj : Function.Injective (MulAut.conj : TableBExc.RecipeGroup .E6 K →* MulAut _) :=
    CFSG.StandardType.mulAut_conj_injective hZ
  have hAinn : A ≤ (MulAut.conj : TableBExc.RecipeGroup .E6 K →* MulAut _).range :=
    TableBExc.E6Three.isElemAbelian_le_inn_of_card_two hK hA
  let E : Subgroup (TableBExc.RecipeGroup .E6 K) :=
    A.comap (MulAut.conj : TableBExc.RecipeGroup .E6 K →* MulAut _)
  have hEmap : E.map (MulAut.conj : TableBExc.RecipeGroup .E6 K →* MulAut _) = A :=
    Subgroup.map_comap_eq_self hAinn
  have hEelem : IsElemAbelian 3 E := by
    dsimp only [E]
    exact hA.comap hinj
  have hEcard : 3 ^ 4 ≤ Nat.card E := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj :
      TableBExc.RecipeGroup .E6 K →* MulAut _)) hinj, hEmap]
    exact hcard
  have hcent : Subgroup.centralizer (E : Set (TableBExc.RecipeGroup .E6 K)) ≤ E :=
    e6Cent_centralizer_le h2 hK hEelem hEcard
  intro r hfix hrP
  have hcomm : ∀ e ∈ E, e * r = r * e := by
    intro e he
    have hconjA : MulAut.conj e ∈ A := by
      rw [← hEmap]
      exact ⟨e, he, rfl⟩
    have hre : MulAut.conj e r = r := hfix _ hconjA
    have h1 : e * r * e⁻¹ = r := by simpa [MulAut.conj_apply] using hre
    calc e * r = (e * r * e⁻¹) * e := by group
      _ = r * e := by rw [h1]
  have hrE : r ∈ E := hcent (Subgroup.mem_centralizer_iff.mpr hcomm)
  have hmem : MulAut.conj r ∈ E.map (MulAut.conj :
      TableBExc.RecipeGroup .E6 K →* MulAut _) := ⟨r, hrE, rfl⟩
  rwa [hEmap] at hmem

end Certificates

theorem e6TwoInput_holds :
    e6TwoInput := by
  intro G _ _ p B Bs x L D J hS hon R _ θ hN
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hBBs : B ≤ Bs := hS.1.1.2.1.1
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hL : commutator L = ⊤ := hSS.2.2.2.1.2.2.1
  obtain ⟨-, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, hP, -, -⟩ := largeEvenRawDatum_exists hraw
  have hq2 : GGLabQTwo 3 lab := hP.1
  have htag : lab.tag = .E6 := hP.2
  have hn1 : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  have hlabE : lab = ⟨.E6, lab.rank, 1⟩ := by
    obtain ⟨t, r, m⟩ := lab
    change t = .E6 at htag
    change m = 1 at hn1
    subst htag
    subst hn1
    rfl
  rw [hlabE] at hraw
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hKf, hKfin, hKcard, -, -, θ₀, -, -, -⟩ := hraw
  letI : Field K := hKf
  letI : Finite K := hKfin
  let θ' : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E6 K := θ₀
  haveI : Finite (TableBExc.RecipeGroup .E6 K) := TableBExc.finite_recipeGroup .E6 K
  haveI : Finite (MulAut (TableBExc.RecipeGroup .E6 K)) := MulEquiv.finite_left
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK2]; norm_num)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hN
  have hlift : GGTorusLift 3 4 (TableBExc.RecipeGroup .E6 K) :=
    TableBExc.E6Three.ggTorusLift_E6_two
  have hboundB : 3 ^ 4 ≤ Nat.card (ggBeta L θ' hBN).range :=
    pow_le_card_range_ggBeta Nat.prime_three hSS hL θ' hBN hlift
  have hle : (ggBeta L θ' hBN).range ≤ (ggBeta L θ' hN).range :=
    range_ggBeta_le θ' hBBs hBN hN
  have hA'elem : IsElemAbelian 3 (ggBeta L θ' hN).range :=
    isElemAbelian_range_ggBeta θ' hBs hN
  have hcardA : 3 ^ 4 ≤ Nat.card (ggBeta L θ' hN).range :=
    le_trans hboundB (Subgroup.card_le_of_le hle)
  have hconcrete : actionThree (ggBeta L θ' hN).range :=
    e6Cent_actionThree_recipe h2 hK2 hA'elem hcardA
  let e : TableBExc.RecipeGroup .E6 K ≃* R := θ'.symm.trans θ
  have htheta : θ'.trans e = θ := by
    ext y
    simp only [e, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hcomp : ggBeta L θ hN = (MulAut.congr e).toMonoidHom.comp (ggBeta L θ' hN) := by
    rw [QTwoCav.beta_trans θ' e hN, htheta]
  have hAeq : (ggBeta L θ' hN).range.map (MulAut.congr e).toMonoidHom =
      (ggBeta L θ hN).range := by
    rw [hcomp, MonoidHom.range_comp]
  change actionThree (ggBeta L θ hN).range
  rw [← hAeq]
  exact actionThree_map_congr e hconcrete

end CFSG.StandardType.GGQ2CentPort

end
