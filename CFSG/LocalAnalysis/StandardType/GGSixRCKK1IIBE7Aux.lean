module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcDatum
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.LieType.Steinberg.Adjoint.Comm
public import CFSG.LieType.Steinberg.Adjoint.ChevExtras
public import CFSG.LieType.Steinberg.Adjoint.CertE7
public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.LieType.Chevalley.RootOps.All
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Form
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.StandardType CFSG.LieType.Universal
open CFSG.LieType.Steinberg.Adjoint

theorem rckp7_elem_zero_or_one (c : GaloisField 2 1) : c = 0 ∨ c = 1 := by
  have hcard : Nat.card (GaloisField 2 1) = 2 := GaloisField.card 2 1 (by decide)
  have hunits : Nat.card (GaloisField 2 1)ˣ = 1 := by
    rw [Nat.card_units, hcard]
  haveI : Subsingleton (GaloisField 2 1)ˣ :=
    Finite.card_le_one_iff_subsingleton.mp (by rw [hunits])
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have h : (Units.mk0 c hc : (GaloisField 2 1)ˣ) = 1 := Subsingleton.elim _ _
    simpa using congrArg (fun u : (GaloisField 2 1)ˣ => (u : GaloisField 2 1)) h

def rckp7_T {G : Type*} [Group G] (x y : G) (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hxy : x * y = y * x) : Subgroup G where
  carrier := {1, x, y, x * y}
  mul_mem' := by
    have h_yx : y * x = x * y := hxy.symm
    have h_xxy : x * (x * y) = y := by rw [← mul_assoc, hx2, one_mul]
    have h_yxy : y * (x * y) = x := by rw [← mul_assoc, hxy.symm, mul_assoc, hy2, mul_one]
    have h_xyx : (x * y) * x = y := by rw [mul_assoc, hxy.symm, ← mul_assoc, hx2, one_mul]
    have h_xyy : (x * y) * y = x := by rw [mul_assoc, hy2, mul_one]
    have h_xyxy : (x * y) * (x * y) = 1 := by
      have hcomm : Commute x y := hxy
      have h2 : (x * y) ^ 2 = 1 := by
        rw [hcomm.mul_pow]
        rw [show x ^ 2 = 1 by rw [pow_two]; exact hx2,
          show y ^ 2 = 1 by rw [pow_two]; exact hy2, mul_one]
      rwa [pow_two] at h2
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl (by rw [one_mul])
    · exact Or.inr (Or.inl (by rw [one_mul]))
    · exact Or.inr (Or.inr (Or.inl (by rw [one_mul])))
    · exact Or.inr (Or.inr (Or.inr (by rw [one_mul])))
    · exact Or.inr (Or.inl (by rw [mul_one]))
    · exact Or.inl hx2
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl h_xxy))
    · exact Or.inr (Or.inr (Or.inl (by rw [mul_one])))
    · exact Or.inr (Or.inr (Or.inr h_yx))
    · exact Or.inl hy2
    · exact Or.inr (Or.inl h_yxy)
    · exact Or.inr (Or.inr (Or.inr (by rw [mul_one])))
    · exact Or.inr (Or.inr (Or.inl h_xyx))
    · exact Or.inr (Or.inl h_xyy)
    · exact Or.inl h_xyxy
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · left; exact inv_one
    · right; left; exact inv_eq_of_mul_eq_one_right hx2
    · right; right; left; exact inv_eq_of_mul_eq_one_right hy2
    · right; right; right
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx2, inv_eq_of_mul_eq_one_right hy2]
      exact hxy.symm

theorem rckp7_T_mem {G : Type*} [Group G] {x y : G} (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hxy : x * y = y * x) {v : G} :
    v ∈ rckp7_T x y hx2 hy2 hxy ↔ v = 1 ∨ v = x ∨ v = y ∨ v = x * y := by
  change v ∈ ({1, x, y, x * y} : Set G) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem rckp7_T_card {G : Type*} [Group G] {x y : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxney : x ≠ y) (hxy_ne1 : x * y ≠ 1) (hxy_nex : x * y ≠ x)
    (hxy_ney : x * y ≠ y) :
    Nat.card (rckp7_T x y hx2 hy2 hxy) = 4 := by
  classical
  let s : Finset G := {1, x, y, x * y}
  have H : ∀ z, z ∈ s ↔ z ∈ (rckp7_T x y hx2 hy2 hxy : Set G) := by
    intro z
    change z ∈ s ↔ z ∈ ({1, x, y, x * y} : Set G)
    simp only [s, Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  letI : Fintype ↑(rckp7_T x y hx2 hy2 hxy : Set G) := Fintype.ofFinset s H
  rw [show Nat.card ↥(rckp7_T x y hx2 hy2 hxy) =
      Nat.card ↑(rckp7_T x y hx2 hy2 hxy : Set G) from rfl, Nat.card_eq_fintype_card,
    Fintype.card_ofFinset s H]
  rw [show s.card = 4 from by
    rw [Finset.card_eq_four]
    exact ⟨1, x, y, x * y, hx1.symm, hy1.symm, hxy_ne1.symm, hxney, hxy_nex.symm,
      hxy_ney.symm, rfl⟩]

theorem rckp7_iform_self_eq_two
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj, show (Tag.symmetrizer .E7) j j = 1 by simp [Tag.symmetrizer]]
  norm_num

theorem rckp7_not_isRoot_sub_of_isRoot_add
    {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (h : IsRoot .E7 (α + β)) :
    ¬ IsRoot .E7 (β - α) := by
  intro hsub
  have hsum : iform (α + β) (α + β) = 2 := rckp7_iform_self_eq_two h
  rw [iform_add_left, iform_add_right, iform_add_right, rckp7_iform_self_eq_two hα,
    rckp7_iform_self_eq_two hβ, iform_comm β α] at hsum
  have hαβ : iform α β = -1 := by omega
  have hsq : iform (β - α) (β - α) = 6 := by
    rw [iform_sub_left, iform_sub_right, iform_sub_right, rckp7_iform_self_eq_two hβ,
      rckp7_iform_self_eq_two hα, iform_comm β α, hαβ]
    ring
  rcases iform_self_cases noG2_E7 hsub with h2 | h4 <;> omega

theorem rckp7_not_isRoot_add_two_smul
    {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ¬ IsRoot .E7 (α + 2 • β) := by
  intro h
  have h' : IsRoot .E7 (1 • α + 2 • β) := by simpa using h
  rcases exponent_pair_cases noG2_E7 hα hβ hne hne' le_rfl (by norm_num) h' with
    h1 | h2 | h3
  · omega
  · obtain ⟨-, -, h4, -⟩ := h2
    have h2' := rckp7_iform_self_eq_two hα
    omega
  · omega

theorem rckp7_not_isRoot_two_smul_add
    {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ¬ IsRoot .E7 (2 • α + β) := by
  intro h
  have h' : IsRoot .E7 (2 • α + 1 • β) := by simpa using h
  rcases exponent_pair_cases noG2_E7 hα hβ hne hne' (by norm_num) le_rfl h' with
    h1 | h2 | h3
  · omega
  · omega
  · obtain ⟨-, -, -, h4, -⟩ := h3
    have h2' := rckp7_iform_self_eq_two hβ
    omega

theorem rckp7_coeff11_eq_one
    {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (hne' : α ≠ -β)
    (h : IsRoot .E7 (α + β)) :
    (RootOperatorFamily'.coeff11 (rootOperatorFamily .E7) e7AdjData_valid
      ⟨α, hα⟩ ⟨β, hβ⟩ : GaloisField 2 1) = 1 := by
  have hβα : β ≠ -α := fun h' => hne' (by rw [h', neg_neg])
  have hN : (RootOperatorFamily'.coeff11 (rootOperatorFamily .E7) e7AdjData_valid
      ⟨α, hα⟩ ⟨β, hβ⟩).natAbs = 1 := by
    rw [RootOperatorFamily'.coeff11,
      RootOperatorFamily'.bracketCoeff_natAbs (rootOperatorFamily .E7) e7AdjData_valid hβα h]
    exact stringNorm_of_not_isRoot (rckp7_not_isRoot_sub_of_isRoot_add hα hβ h)
  rcases Int.natAbs_eq_iff.1 hN with h1 | h1
  · rw [h1]; norm_num
  · rw [h1]
    simpa using CharTwo.neg_eq (1 : GaloisField 2 1)

end CFSG.StandardType.RCKK1II
