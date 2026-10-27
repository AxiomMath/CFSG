module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import Certificates.Certificate271060

import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordAux
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Blueprint.Catalog
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.RankThree.PartOne.F106.F4Three
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CLOF4Aux_card_Bs {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) :
    Nat.card ↥Bs = p ^ (n + 1) := by
  haveI : Finite V := Finite.of_surjective ι.toEquiv ι.toEquiv.surjective
  change Nat.card (Additive ↥Bs) = p ^ (n + 1)
  rw [Nat.card_congr ι.toEquiv, ← FiniteField.pow_finrank_eq_natCard p V]
  congr 1
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

private lemma hdRo7CLOF4Aux_ker_beta {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (R : Type) [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hperf : commutator ↥L = ⊤) :
    (ggBeta L θ hBsN).ker = (Subgroup.zpowers x).subgroupOf Bs := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hb
    have hla : ggLAut L θ ⟨b, hBsN b.2⟩ = 1 := by
      rw [ggBeta_eq] at hb
      exact hb
    have hc := mem_centralizer_of_ggLAut_eq_one L θ hperf hla
    have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, hc⟩
    rwa [hdRo7CLCoordAux_bstar_centralizer_eq hH] at hmem
  · intro hb
    have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rwa [hdRo7CLCoordAux_bstar_centralizer_eq hH]
    rw [ggBeta_eq]
    exact ggLAut_eq_one_of_mem_centralizer L θ hmem.2

theorem c2_lorder_f4
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hp3 : p = 3) (hn : 5 ≤ n)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (htag : lab.tag = .F4) (hn1 : lab.n = 1) :
    False := by
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : commutator ↥L = ⊤ := (hH.2.2.1.1).1
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.1) hlab hLlab
  have hmark2 := largeEvenMarking_and_labelAll_simple
    (P := fun lab' _ _ I _ θ => lab' = lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ)
    (S := fun lab' => lab' = lab)
    (P' := fun R _ I _ => I ⊆ LargeEvenInnSet R)
    (fun lab' hlab' hS => by
      rw [hS] at hlab' ⊢
      exact largeEvenLabelAll_subset_inn hlab' (Or.inr (Or.inr (Or.inl htag))))
    (fun lab' R _ I F θ hP => hP.1)
    hmark
  obtain ⟨-, lab', hlab', hraw''⟩ := hmark2
  obtain ⟨R, hRgrp, I, F, hsimple, hnonab, θ, hP, hInn⟩ := largeEvenRawDatum_exists hraw''
  letI : Group R := hRgrp
  obtain ⟨hlab'_eq, hBsN, hact⟩ := hP
  have hT : CFSG.Blueprint.UntwistedChevalleyModel R .F4 2 := by
    have hlab_eq : lab = ⟨.F4, 0, 1⟩ := by
      obtain ⟨t, l, n⟩ := lab
      have ht : t = .F4 := htag
      have hn : n = 1 := hn1
      have hl : l = 0 := by
        have h := hlab
        dsimp only [LargeEvenInLambda2] at h
        rw [ht] at h
        exact h.2
      subst ht; subst hl; subst hn; rfl
    have hTL : CFSG.Blueprint.UntwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .F4 2 := by
      have h := hLlab
      rw [hlab_eq] at h
      obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ := h
      letI : Field K := hKfld
      letI : Finite K := hKfin
      have hK2 : Nat.card K = 2 := by simpa using hKcard
      obtain ⟨K', iF, iFi, hK', ⟨e'⟩⟩ := untwistedChevalleyModel_largeEven .F4 hK2
      exact ⟨K', iF, iFi, hK', ⟨e.trans e'⟩⟩
    obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ := hTL
    exact ⟨K, hKfld, hKfin, hKcard, ⟨θ.symm.trans e⟩⟩
  have hZ : Subgroup.center R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      refine hab ?_
      have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  let eR : (MulAut.conj : R →* MulAut R).range ≃* R := (MonoidHom.ofInjective hinj).symm
  let f : ↥Bs →* (MulAut.conj : R →* MulAut R).range :=
    (ggBeta L θ hBsN).codRestrict (MulAut.conj : R →* MulAut R).range
      (fun b => hInn (ggBeta_mem L θ hBsN hact b))
  let ρ : ↥Bs →* R := eR.toMonoidHom.comp f
  have hker : (ggBeta L θ hBsN).ker = (Subgroup.zpowers x).subgroupOf Bs :=
    hdRo7CLOF4Aux_ker_beta hH R θ hBsN hperf
  have hkerρ : ρ.ker = (ggBeta L θ hBsN).ker := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : f b = 1 := eR.injective (by simpa [ρ] using h)
      exact congrArg Subtype.val h1
    · intro h
      have h1 : f b = 1 := Subtype.ext h
      simp [ρ, h1]
  have hcardker : Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = p := by
    have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxBs)).toEquiv,
      Nat.card_zpowers]
    exact orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)
  have hcardBs : Nat.card ↥Bs = p ^ (n + 1) := hdRo7CLOF4Aux_card_Bs ι b
  have hcard_im : Nat.card ρ.range = p ^ n := by
    have h1 := TableB.card_range_mul_card_ker ρ
    rw [hkerρ, hker, hcardker, hcardBs] at h1
    have h2 : Nat.card ρ.range * p = p ^ n * p := by rw [h1, pow_succ]
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have htop : CFSG.Open.IsElemAbelian p (⊤ : Subgroup ↥Bs) := by
    refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun a _ => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact TableB.IsElemAbelian.comm hH.1.tableB_facts.2.1 (a : ↥Bs).2 (b : ↥Bs).2
    · apply Subtype.ext
      exact hH.1.tableB_facts.2.1.2 (a : ↥Bs) (a : ↥Bs).2
  have hρab : CFSG.Open.IsElemAbelian p ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.Open.IsElemAbelian.map htop ρ
  rw [hp3] at hρab
  have hdvd : 3 ^ 5 ∣ Nat.card ρ.range := by
    rw [hcard_im, hp3]
    exact Nat.pow_dvd_pow 3 hn
  haveI : Finite ρ.range :=
    Finite.of_surjective ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
  obtain ⟨D, hDcard, -, hDle⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (H := (⊥ : Subgroup R)) (L := ρ.range) (by simp) hdvd bot_le
  have hDab : CFSG.Open.IsElemAbelian 3 D := TableB.isElemAbelian_mono hρab hDle
  exact CFSG.RankThree.PartOne.F106.f4_no_elemAbelian_five hT D
    (fun a ha b hb => TableB.IsElemAbelian.comm hDab ha hb)
    (fun a ha => hDab.2 a ha) hDcard

end CFSG.StandardType.HdRo7C

end
