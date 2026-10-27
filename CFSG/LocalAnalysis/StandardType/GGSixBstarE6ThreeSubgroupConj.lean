module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeConjCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeHyperplane
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section SubgroupConj

open TableBExc.E6Three

variable {K : Type} [Field K] [Finite K]

theorem innerAut_le_hatAut_range :
    (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤
      (hatAut .E6 K).range := by
  rw [hatAut_range_eq_sup]
  exact le_sup_left

theorem exists_conj_eq_vAd (h3 : 3 ∣ Nat.card K - 1) {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (hatAut .E6 K).range) (h6 : 3 ^ 6 ≤ Nat.card X) :
    ∃ γ ∈ (hatAut .E6 K).range, X.map (MulAut.conj γ).toMonoidHom = vAd ζ hζ := by
  obtain ⟨γ, hγ, A, hA, hfix, hcount, hbot⟩ :=
    exists_conj_kernel_fix_of_le_hatAut h3 hζo hζ hX hXI
  have hA1 : A = ⊥ := by
    by_contra hA1
    have hoff := NoOffRest.actNoOffender_adPerm_E6 A hA hA1
    have hle : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        diag3 ζ hζ (Multiplicative.ofAdd x) ∈ X.map (MulAut.conj γ).toMonoidHom} ≤
        Nat.card {v : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adPerm .E6 3 a v = v} :=
      Nat.card_le_card_of_injective
        (fun x => ⟨x.1, fun a ha => hfix a ha x.1 x.2⟩)
        (fun a b h => Subtype.ext (congrArg (fun v => (v.1 : Fin Tag.E6.rank → ZMod 3)) h))
    have hV : Nat.card (Fin Tag.E6.rank → ZMod 3) = 3 ^ 6 := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      rfl
    rw [hV] at hoff
    have h1 : 3 ^ 6 ≤ Nat.card A * Nat.card {v : Fin Tag.E6.rank → ZMod 3 //
        ∀ a ∈ A, adPerm .E6 3 a v = v} :=
      h6.trans (hcount.trans (Nat.mul_le_mul_left _ hle))
    omega
  have hle := hbot hA1
  have hcard : Nat.card (vAd (K := K) ζ hζ) ≤ Nat.card (X.map (MulAut.conj γ).toMonoidHom) := by
    rw [card_vAd hζo hζ, Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    exact h6
  exact ⟨γ, hγ, Subgroup.eq_of_le_of_card_ge hle hcard⟩

theorem exists_conj_eq_vHyp (h3 : 3 ∣ Nat.card K - 1) {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1)
    (hnot : ¬ vAd (K := K) ζ hζ ≤
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range)
    {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range)
    (h5 : 3 ^ 5 ≤ Nat.card X) :
    ∃ γ ∈ (hatAut .E6 K).range, X.map (MulAut.conj γ).toMonoidHom = vHyp ζ hζ := by
  obtain ⟨γ, hγ, A, hA, hfix, hcount, hbot⟩ :=
    exists_conj_kernel_fix_of_le_hatAut h3 hζo hζ hX (hXI.trans innerAut_le_hatAut_range)
  haveI : (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .E6 K)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hYI : ∀ φ ∈ X.map (MulAut.conj γ).toMonoidHom,
      φ ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (inferInstance :
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .E6 K)).Normal).conj_mem
        φ (hXI hφ) γ
  have hhyp : ∀ x : Fin Tag.E6.rank → ZMod 3,
      diag3 ζ hζ (Multiplicative.ofAdd x) ∈ X.map (MulAut.conj γ).toMonoidHom →
        x ∈ NoOffRest.hypE6 := fun x hx =>
    mem_hypE6_of_diag3_mem_innerAut ζ hζ hnot (hYI _ hx)
  have hA1 : A = ⊥ := by
    by_contra hA1
    have hoff := NoOffRest.actNoOffender_hypPerm_E6 A hA hA1
    have hle : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        diag3 ζ hζ (Multiplicative.ofAdd x) ∈ X.map (MulAut.conj γ).toMonoidHom} ≤
        Nat.card {v : NoOffRest.hypE6 // ∀ a ∈ A, NoOffRest.hypPerm a v = v} :=
      Nat.card_le_card_of_injective
        (fun x => ⟨⟨x.1, hhyp x.1 x.2⟩, fun a ha => Subtype.ext (hfix a ha x.1 x.2)⟩)
        (fun a b h => Subtype.ext (congrArg (fun v => (v.1 : Fin Tag.E6.rank → ZMod 3)) h))
    have hH : Nat.card NoOffRest.hypE6 = 3 ^ 5 := NoOffRest.card_hypE6
    rw [hH] at hoff
    have h1 : 3 ^ 5 ≤ Nat.card A * Nat.card {v : NoOffRest.hypE6 //
        ∀ a ∈ A, NoOffRest.hypPerm a v = v} :=
      h5.trans (hcount.trans (Nat.mul_le_mul_left _ hle))
    omega
  have hle : X.map (MulAut.conj γ).toMonoidHom ≤ vHyp ζ hζ := by
    intro φ hφ
    obtain ⟨x, hx⟩ := hbot hA1 hφ
    have hxh : Multiplicative.toAdd x ∈ NoOffRest.hypE6 := by
      refine hhyp _ ?_
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd x) = x from rfl, hx]
      exact hφ
    exact ⟨Multiplicative.ofAdd ⟨Multiplicative.toAdd x, hxh⟩, hx⟩
  have hcard : Nat.card (vHyp (K := K) ζ hζ) ≤ Nat.card (X.map (MulAut.conj γ).toMonoidHom) := by
    rw [card_vHyp hζo hζ, Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    exact h5
  exact ⟨γ, hγ, Subgroup.eq_of_le_of_card_ge hle hcard⟩

end SubgroupConj

end NoOffE6Three

end CFSG.StandardType
