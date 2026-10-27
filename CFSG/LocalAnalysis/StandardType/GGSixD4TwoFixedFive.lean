module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.Blueprint.Catalog

import CFSG.LocalAnalysis.StandardType.GGLieOddCover
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridge
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.Assembly
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.FiveFixedDichotomy
import CFSG.GH74.Generic.S1.CompIdent
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
import Mathlib.GroupTheory.Perm.Cycle.Type
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeDefs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open
open CFSG.StandardType.S2MathFi1035Pos (GGPosTag)
open scoped commutatorElement

section Certificates

theorem exists_plus_four_two_innerDiag_presentation_of_fixed_five
    {X : Type} [Group X] [Finite X] {K J : Subgroup X}
    (hJK : J ≤ K) (hKperf : commutator ↥K = ⊤)
    (hoddK : Odd (Nat.card (Subgroup.center ↥K)))
    (hLM : LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus 4 2 1)
    {d : X} (hdK : d ∈ Subgroup.normalizer (K : Set X))
    (hd3 : d ^ 3 = 1) (hdJ : d ∈ Subgroup.centralizer (J : Set X))
    (h5 : 5 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    ∃ phi : (ggU .POmegaPlus 4 1).K →* X,
      phi.range = K ∧ phi.ker ≤ Subgroup.center (ggU .POmegaPlus 4 1).K ∧
      GGPsiInnerDiag (ggU .POmegaPlus 4 1).D phi d := by
  classical
  haveI : Finite ↥K := Subtype.finite
  haveI : Finite ↥J := Subtype.finite
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

  let f : ↥J →* ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hJK)
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    have h1 : f j = 1 := by simpa using hj
    have hjK : (Subgroup.inclusion hJK j : ↥K) ∈ Subgroup.center ↥K := by
      have h2 : (QuotientGroup.mk' (Subgroup.center ↥K))
          (Subgroup.inclusion hJK j) = 1 := by
        simpa [f] using h1
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hJK j)).mp (by simpa using h2)
    have hcomm := (Subgroup.mem_center_iff.mp hjK) (Subgroup.inclusion hJK j')
    simpa using congrArg Subtype.val hcomm
  have hdiv : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card f.range :=
    CFSG.GH74.Generic.S1.card_quot_center_dvd_range f hfker
  have h5range : 5 ∣ Nat.card f.range := h5.trans hdiv
  obtain ⟨y, hy5⟩ := exists_prime_orderOf_dvd_card' (G := ↥f.range) 5 h5range
  let x0 : ↥K ⧸ Subgroup.center ↥K := (y : ↥K ⧸ Subgroup.center ↥K)
  have hx0ord : orderOf x0 = 5 := by
    simpa [x0] using (Subgroup.orderOf_coe y).trans hy5

  let α : MulAut ↥K := K.normalizerMonoidHom ⟨d⁻¹, Subgroup.inv_mem _ hdK⟩
  let β : MulAut (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α
  have hβapply : ∀ x : ↥K,
      β ((x : ↥K ⧸ Subgroup.center ↥K)) =
        (α x : ↥K ⧸ Subgroup.center ↥K) := by
    intro x
    change (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α)
      ((x : ↥K ⧸ Subgroup.center ↥K)) = (α x : ↥K ⧸ Subgroup.center ↥K)
    exact CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α x
  have hβx0 : β x0 = x0 := by
    obtain ⟨j, hj⟩ := y.2
    have hαj : α (Subgroup.inclusion hJK j) = Subgroup.inclusion hJK j := by
      apply Subtype.ext
      show ((K.normalizerMonoidHom ⟨d⁻¹, Subgroup.inv_mem _ hdK⟩)
          (Subgroup.inclusion hJK j) : X) =
        ((Subgroup.inclusion hJK j : ↥K) : X)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv, Subgroup.coe_inclusion]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hdJ) (j : X) j.2
      calc d⁻¹ * (j : X) * d = d⁻¹ * ((j : X) * d) := by group
        _ = d⁻¹ * (d * (j : X)) := by rw [hcomm]
        _ = (j : X) := by group
    have hx0eq : x0 = ((Subgroup.inclusion hJK j : ↥K) : ↥K ⧸ Subgroup.center ↥K) := by
      simpa [x0, f] using hj.symm
    rw [hx0eq, hβapply, hαj]
  have hd3inv : (⟨d⁻¹, Subgroup.inv_mem _ hdK⟩ :
      Subgroup.normalizer (K : Set X)) ^ 3 = 1 := by
    apply Subtype.ext
    change (d⁻¹) ^ 3 = (1 : X)
    rw [inv_pow, hd3, inv_one]
  have hα3 : α ^ 3 = 1 := by
    change (K.normalizerMonoidHom ⟨d⁻¹, Subgroup.inv_mem _ hdK⟩) ^ 3 = 1
    rw [← map_pow, hd3inv, map_one]
  have hβ3 : β ^ 3 = 1 := by
    change (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α) ^ 3 = 1
    rw [← map_pow, hα3, map_one]

  have hβinner : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (↥K ⧸ Subgroup.center ↥K) := by
    by_contra hβout
    have hclass : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus 4 2 1 :=
      hLM.statedClassicalModel (by decide)
    have hclass' := hclass
    obtain ⟨-, Kf, hFieldKf, hFiniteKf, hKfcard, ⟨e0⟩⟩ := hclass'
    letI : Field Kf := hFieldKf
    letI : Finite Kf := hFiniteKf
    let P := StatedProj (StatedOmega (StatedQuadPlus 4 Kf))
    let e : (↥K ⧸ Subgroup.center ↥K) ≃* P := e0
    let α' : MulAut P := MulAut.congr e β
    have hα'out : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner P := by
      intro hmem
      exact hβout
        ((CFSG.ComponentClassification.OuterAutomorphisms.congr_mem_inner_iff e β).mp hmem)
    have hα'3 : α' ^ 3 = 1 := by
      change (MulAut.congr e β) ^ 3 = 1
      rw [← map_pow, hβ3, map_one]
    have hα'x : α' (e x0) = e x0 := by
      change MulAut.congr e β (e x0) = e x0
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hβx0]
    have hx0e : orderOf (e x0) = 5 := by
      rw [MulEquiv.orderOf_eq, hx0ord]
    exact CFSG.AGLEmbedding.TrialityTwo.false_of_orderOf_eq_five
      CFSG.AGLEmbedding.TrialityTwo.fiveFixedDichotomy_holds
      hclass hKfcard e α' hα'out hα'3 (e x0) hα'x hx0e
  obtain ⟨r, hr⟩ := hβinner

  have hspos : GGPosTag .POmegaPlus := by simp [GGPosTag]
  have hcover := CFSG.StandardType.LieOddCover.ggLieOddCover_holds
  obtain ⟨ψ, hψsurj, hψker0⟩ :=
    hcover.1 .POmegaPlus 4 1 hspos hLM.admissible ↥K hKperf hoddK hLM
  let phi : (ggU .POmegaPlus 4 1).K →* X := K.subtype.comp ψ
  have hφrange : phi.range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  have hφker : phi.ker ≤ Subgroup.center (ggU .POmegaPlus 4 1).K := by
    rw [MonoidHom.ker_comp_of_injective ψ K.subtype K.subtype_injective]
    exact hψker0

  let θ : ↥phi.range ⧸ Subgroup.center ↥phi.range ≃*
      (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center ↥phi.range) (Subgroup.center ↥K)
      (MulEquiv.subgroupCongr hφrange) (Subgroup.map_center_eq _)
  have hθmk : ∀ x : ↥phi.range,
      θ ((x : ↥phi.range ⧸ Subgroup.center ↥phi.range)) =
        ((MulEquiv.subgroupCongr hφrange x : ↥K) : ↥K ⧸ Subgroup.center ↥K) := by
    intro x
    change QuotientGroup.congr (Subgroup.center ↥phi.range) (Subgroup.center ↥K)
      (MulEquiv.subgroupCongr hφrange) (Subgroup.map_center_eq _)
      ((x : ↥phi.range ⧸ Subgroup.center ↥phi.range)) = _
    exact QuotientGroup.congr_mk (Subgroup.center ↥phi.range) (Subgroup.center ↥K)
      (MulEquiv.subgroupCongr hφrange) (Subgroup.map_center_eq _) x
  have hαrel : ∀ l l' : ↥phi.range, (l' : X) = d⁻¹ * (l : X) * d →
      α (MulEquiv.subgroupCongr hφrange l) = MulEquiv.subgroupCongr hφrange l' := by
    intro l l' hrel
    apply Subtype.ext
    show ((K.normalizerMonoidHom ⟨d⁻¹, Subgroup.inv_mem _ hdK⟩)
        (MulEquiv.subgroupCongr hφrange l) : X) =
      ((MulEquiv.subgroupCongr hφrange l' : ↥K) : X)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
    simpa only [MulEquiv.subgroupCongr_apply] using hrel.symm
  have hLarge : LargeEvenInduces θ
      (fun l l' : ↥phi.range => (l' : X) = d⁻¹ * (l : X) * d) (MulAut.conj r) := by
    intro l l' hrel
    rw [hθmk l, hθmk l', hr, hβapply, hαrel l l' hrel]

  refine ⟨phi, hφrange, hφker, ?_⟩
  have hperf' : commutator ↥phi.range = ⊤ := hφrange.symm ▸ hKperf
  have hφN : d ∈ Subgroup.normalizer (phi.range : Set X) := hφrange.symm ▸ hdK
  exact CFSG.StandardType.ggPsiInnerDiag_of_induces_conj
    (ggU .POmegaPlus 4 1).D phi hperf' θ hφN hLarge

end Certificates

end CFSG.StandardType.RCKC1
