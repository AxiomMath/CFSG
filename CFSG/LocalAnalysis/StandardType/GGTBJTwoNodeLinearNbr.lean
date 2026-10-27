module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

theorem exists_diagonal_cover_of_large_linear_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* K),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t := by
  exact exists_diagonal_cover_of_large_linear_side hRig hH
    (Or.inr ⟨y, hH.2.2.2.2.1⟩) (by omega : 3 ≤ r) hpq hLab hΛ

theorem exists_corank_two_block_of_large_linear_K_of_cfg
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hJLab : GGHasLabel ⟨.A, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* K) (S : Finset (Fin (r + 1))),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        (∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t) ∧
        S.card = r - 1 ∧ J = (blockSpecialLinear S).map (K.subtype.comp φ) := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_cfg hRig hcfg hIDA (Or.inr ⟨y, hnb⟩)
      (by omega : 3 ≤ r) hpq hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hpJ : p ∣ Nat.card J :=
    (prime_dvd_card_of_hasLabel_linear hp hp2 (by omega : 1 ≤ r - 2) hpq hJLab).trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _))
  have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 hpJ hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hcfg.2.1.1 (hcfg.2.2.1.1 hxD)
  have hdiag' : ∀ b : Bs, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag φ (K.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma K hN b) ⟨b, rfl⟩
  have hcomp' : IsComponentOf J (K ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcomp
  obtain ⟨S, hS, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    hφs hker hdiag' (Subgroup.zpowers_le.mpr hx) hcomp'
  have hf1 : 1 ≤ f := hΛ.1
  have hf : 2 ≤ f := by
    by_contra hf2
    have hf_eq : f = 1 := by omega
    have hp_one : p ∣ 1 := by simpa only [hf_eq, pow_one] using hpq
    exact hp.not_dvd_one hp_one
  have hk : (K.subtype.comp φ).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (r + 1)) F) := by
    intro g hg
    have hgφ : φ g = 1 := Subtype.ext (MonoidHom.mem_ker.mp hg)
    exact scalars_le_center (r + 1) F (hker g hgφ)
  have hΛJ : LargeEvenInLambda2 ⟨.A, r - 2, f⟩ := by
    change 1 ≤ f ∧ 1 ≤ r - 2 ∧ (r - 2 = 1 → 2 ≤ f)
    exact ⟨by omega, by omega, fun _ => hf⟩
  have hc := card_eq_of_blockSpecialLinear_label hRig hF hf hk hS hΛJ (hJ ▸ hJLab)
  refine ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, ?_, hJ⟩
  omega

theorem exists_corank_two_block_of_large_linear_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hJLab : GGHasLabel ⟨.A, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* K) (S : Finset (Fin (r + 1))),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        (∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t) ∧
        S.card = r - 1 ∧ J = (blockSpecialLinear S).map (K.subtype.comp φ) :=
  exists_corank_two_block_of_large_linear_K_of_cfg hRig hLB hH.1 hH.2.2.1 hH.2.2.2.2.1 hr hpq hLab
    hΛ hJLab

end CFSG.StandardType

end
