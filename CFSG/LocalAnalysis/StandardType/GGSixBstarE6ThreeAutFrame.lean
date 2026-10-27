module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeSubgroupConj
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiag
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeSteinberg
public import CFSG.LocalAnalysis.StandardType.GGSixBstarModelFrameTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section AutFrame

open TableBExc.E6Three

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggBstarModelFrame_vAd {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (M : Subgroup (MulAut (adjointGroup .E6 K))) :
    GGBstarModelFrame (adPerm .E6 3) 3 M (vAd (K := K) ζ hζ) := by
  refine ⟨diag3 ζ hζ, diag3_injective hζo hζ, rfl, ?_⟩
  intro g _ hgN hg3
  obtain ⟨h, hh, hgh⟩ := exists_inndiag_conj_eq_on_diag3 hζ hg3
  have hW : ∀ x ∈ (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)), ∃ y ∈ (Set.univ : Set _),
      h * diag3 ζ hζ (Multiplicative.ofAdd x) * h⁻¹ = diag3 ζ hζ (Multiplicative.ofAdd y) := by
    intro x _
    have hmem : g * diag3 ζ hζ (Multiplicative.ofAdd x) * g⁻¹ ∈ vAd (K := K) ζ hζ :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mp ⟨Multiplicative.ofAdd x, rfl⟩
    obtain ⟨y', hy'⟩ := hmem
    refine ⟨Multiplicative.toAdd y', Set.mem_univ _, ?_⟩
    rw [← hgh x]
    exact hy'.symm
  obtain ⟨w, hw⟩ := exists_weyl_conj_diag3 hζ hh hW
  exact ⟨w, fun v => (hgh v).trans (hw v (Set.mem_univ v))⟩

theorem ggBstarModelFrame_vHyp {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (M : Subgroup (MulAut (adjointGroup .E6 K))) :
    GGBstarModelFrame NoOffRest.hypPerm 3 M (vHyp (K := K) ζ hζ) := by
  refine ⟨diag3Hyp ζ hζ, diag3Hyp_injective hζo hζ, rfl, ?_⟩
  intro g _ hgN hg3
  obtain ⟨h, hh, hgh⟩ := exists_inndiag_conj_eq_on_diag3 hζ hg3
  have hW : ∀ x ∈ ((NoOffRest.hypE6 : AddSubgroup (Fin Tag.E6.rank → ZMod 3)) :
      Set (Fin Tag.E6.rank → ZMod 3)), ∃ y ∈ ((NoOffRest.hypE6 : AddSubgroup
        (Fin Tag.E6.rank → ZMod 3)) : Set (Fin Tag.E6.rank → ZMod 3)),
      h * diag3 ζ hζ (Multiplicative.ofAdd x) * h⁻¹ = diag3 ζ hζ (Multiplicative.ofAdd y) := by
    intro x hx
    have hmem : g * diag3Hyp (K := K) ζ hζ (Multiplicative.ofAdd ⟨x, hx⟩) * g⁻¹ ∈
        vHyp (K := K) ζ hζ :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mp ⟨Multiplicative.ofAdd ⟨x, hx⟩, rfl⟩
    obtain ⟨y', hy'⟩ := hmem
    refine ⟨(Multiplicative.toAdd y').1, (Multiplicative.toAdd y').2, ?_⟩
    rw [← hgh x]
    exact hy'.symm
  obtain ⟨w, hw⟩ := exists_weyl_conj_diag3 hζ hh hW
  exact ⟨w, fun v => (hgh v.1).trans (hw v.1 v.2)⟩

theorem exists_autFrame_E6 (h3 : 3 ∣ Nat.card K - 1)
    {M' S : Subgroup (MulAut (adjointGroup .E6 K))} (hSM : S ≤ M')
    (hInn : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ M')
    (hSel : IsElemAbelian 3 S) (hSI : S ≤ (hatAut .E6 K).range) (h5 : 3 ^ 5 ≤ Nat.card S)
    (hM2 : ∀ X : Subgroup (MulAut (adjointGroup .E6 K)), X ≤ M' → IsElemAbelian 3 X →
      (∃ U : Subgroup (adjointGroup .E6 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U) →
        Nat.card X ≤ Nat.card S) :
    GGBstarModelFrame (adPerm .E6 3) 3 M' S ∨ GGBstarModelFrame NoOffRest.hypPerm 3 M' S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hvAd : vAd (K := K) ζ hζ ≤ M' → 3 ^ 6 ≤ Nat.card S := fun hle => by
    have := hM2 _ hle (isElemAbelian_vAd ζ hζ) (twoLocal_vAd ζ hζ)
    rwa [card_vAd hζo hζ] at this
  by_cases h6 : 3 ^ 6 ≤ Nat.card S
  · obtain ⟨γ, -, hγ⟩ := exists_conj_eq_vAd h3 hζo hζ hSel hSI h6
    left
    refine GGBstarModelFrame.of_conj γ ?_
    rw [hγ]
    exact ggBstarModelFrame_vAd hζo hζ _
  · by_cases hSInn : S ≤ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range
    · have hnot : ¬ vAd (K := K) ζ hζ ≤
          (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :=
        fun hle => h6 (hvAd (hle.trans hInn))
      obtain ⟨γ, -, hγ⟩ := exists_conj_eq_vHyp h3 hζo hζ hnot hSel hSInn h5
      right
      refine GGBstarModelFrame.of_conj γ ?_
      rw [hγ]
      exact ggBstarModelFrame_vHyp hζo hζ _
    · exfalso
      obtain ⟨s, hsS, hsn⟩ := Set.not_subset.mp hSInn
      have hD1 := exists_sup_zpowers_of_not_mem_innerAut (hSI hsS) hsn
      have hle : (hatAut .E6 K).range ≤ M' :=
        hD1.trans (sup_le hInn ((Subgroup.zpowers_le).mpr (hSM hsS)))
      exact h6 (hvAd ((vAd_le_hatAut_range ζ hζ).trans hle))

end AutFrame

end NoOffE6Three

end CFSG.StandardType
