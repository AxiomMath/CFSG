module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitLayer
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThreeHolds
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGL45E67Center

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley ExcFrames.E6QPlusThree


theorem ggKGRootDatum_E6_three_nonsplit {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K + 1) :
    GGKGRootDatum 3 4 (adjointGroup .E6 K) := by
  intro E hE _ h4 hsc
  obtain ⟨D, F, Fr, ζ, hζ, hw, hFr, hΦ, hζo, hFrζ, hsurj, hcoord⟩ :=
    exists_e6QPlusThreeFrame_excFrame h3
  have hroot := ggKGRootDatumAt_e6QPlusThree D F hw hζo hζ hcoord hq h3 hsurj
  have hSC : ∀ c ∈ Subgroup.centralizer (E : Set (adjointGroup .E6 K)),
      c ^ 3 = 1 → c ∈ E := by
    intro c hc hc3
    exact hsc c (fun e he => ((Subgroup.mem_centralizer_iff.mp hc) e he).symm) hc3
  obtain ⟨c, hc⟩ := ExcFrames.e6ThreeSCReference_holds h3 D hE h4 hSC
  have hmap : E.map (MulAut.conj c).symm.toMonoidHom = D.frame.range := by
    rw [hc, Subgroup.map_map]
    have hf : (MulAut.conj c).symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id (adjointGroup .E6 K) := by
      apply MonoidHom.ext
      intro x
      exact (MulAut.conj c).symm_apply_apply x
    rw [hf, Subgroup.map_id]
  exact ggKGRootDatumAt_of_mulEquiv (MulAut.conj c).symm (hmap.symm ▸ hroot)

theorem ggTorusRootSL2_E6_three_nonsplit {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hq : 4 ≤ Nat.card K)
    (h3 : 3 ∣ Nat.card K + 1) :
    GGTorusRootSL2 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have h3' : ¬ 3 ∣ Nat.card K - 1 := by
    intro hd
    have hsub := Nat.dvd_sub h3 hd
    have hcard : 1 ≤ Nat.card K := Nat.card_pos
    have heq : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
    rw [heq] at hsub
    norm_num at hsub
  have h3n : ¬ 3 ∣ 2 ^ n - 1 := by simpa only [hK] using h3'
  have hcop : Nat.Coprime 3 (Nat.gcd 3 (Nat.card K - 1)) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3').coprime_dvd_right
      (Nat.gcd_dvd_right 3 (Nat.card K - 1))
  exact ggTorusRootSL2_of_rootDatum Nat.prime_three
    (fun φ hφ hφ3 => mem_inn_of_mem_recipeID_E6 hK Nat.prime_three (Or.inr h3n) hφ hφ3)
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (ggCenterPrime_recipe_E6_of_coprime Nat.prime_three (by decide) hcop)
    (ggKGRootDatum_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
      (ggKGRootDatum_E6_three_nonsplit hq h3))

theorem ggRealKGThreeRow_e6Nonsplit : GGRealKGThreeRow .e6Nonsplit := by
  intro p lab hp hlab hreal hs
  obtain ⟨rfl, ⟨htag, hpn⟩, -⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hreal
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hField, hFinite, hK, hQ⟩ := hQ
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := charP_two_of_card hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    have hn : 2 ≤ n := hreal.2.1
    exact (by decide : 4 = 2 ^ 2) ▸ Nat.pow_le_pow_right (by decide) hn
  have h3 : 3 ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  exact ⟨K, hField, hFinite, hK, hQ, 4, TableBExc.E6Three.ggTorusLift_E6_two,
    ggTorusRootSL2_E6_three_nonsplit hK hq h3⟩

end CFSG.StandardType

end
