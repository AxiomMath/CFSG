module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggL45NtRecExU_rec {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
    {p : ℕ}
    (hinn : LargeEvenChevIDImage A K (LargeEvenChevH A K false) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH A K false) →*
        MulAut (LargeEvenCenterQuot (LargeEvenChevH A K false))).range)
    (hcenter : GGCenterPrime p (LargeEvenCenterQuot (LargeEvenChevH A K false))) :
    GGL45NtRec p (LargeEvenCenterQuot (LargeEvenChevH A K false))
      (LargeEvenChevIDImage A K (LargeEvenChevH A K false))
      (LargeEvenChevFieldImage A K (LargeEvenChevH A K false)) := by
  intro _ _
  exact ⟨fun r => Subgroup.subset_closure (Or.inl ⟨r, rfl⟩),
    fun u hu _ => by obtain ⟨r, hr⟩ := hinn hu; exact ⟨r, hr.symm⟩, hcenter⟩

private theorem ggL45NtRecExU_centerPrime_G2
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterPrime p (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* adjointGroup .G2 K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        Nat.Coprime 2 (Nat.card π.ker) →
        ∃ σ : adjointGroup .G2 K →* E, ∀ g, π (σ g) = g := by
    intro E _ _ π hπ hcen hc
    exact CFSG.LieType.Steinberg.CentralExt.G2Four.g2_exists_section_of_coprime E π hπ hcen hc
  exact (OrthRest.center_data (e := (TableBExc.recipeEquiv .G2 K).symm)
    center_adjointGroup_eq_bot hsplit hp hp2).2

theorem ggL45NtRecOn_E7 :
    GGL45NtRecOn fun _ lab => lab.tag = .E7 := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  subst hS
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
  haveI : Finite K := hfin
  haveI : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hf, hfin, hK, hQ, ?_⟩
  exact ggL45NtRecExU_rec (A := LargeEvenCartanE 7)
    (chevIDImage_subset_inn_of_top (τ := .E7) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
      TableB.cartanE7_adj (TableB.exists_sq_eq_of_charTwo K)))
    (ExcSplitL.ggCenterPrime_recipe_E7 hlab.1 hK hp hp2)

theorem ggL45NtRecOn_exU :
    GGL45NtRecOn GGL45NtFamExU := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨-, htag⟩ := hS
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at htag
  rcases htag with h | h | h | h <;> subst tag
  ·
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    haveI : Finite K := hfin
    haveI : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    exact ggL45NtRecExU_rec (A := LargeEvenCartanG2)
      (chevIDImage_subset_inn_of_top (τ := .G2) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩))
      (ggL45NtRecExU_centerPrime_G2 hp hp2)
  ·
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    haveI : Finite K := hfin
    haveI : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    exact ggL45NtRecExU_rec (A := LargeEvenCartanF4)
      (chevIDImage_subset_inn_of_top (τ := .F4) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanF4_inv fun s => ⟨s, pow_one s⟩))
      (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2)
  ·
    exact ggL45NtRecOn_E7 p hp hp2 _ hlab hkg rfl Q hQ
  ·
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    haveI : Finite K := hfin
    haveI : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    exact ggL45NtRecExU_rec (A := LargeEvenCartanE 8)
      (chevIDImage_subset_inn_of_top (τ := .E8) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩))
      (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2)

end CFSG.StandardType
