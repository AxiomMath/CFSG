module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary85
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Section4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma101
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma106
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102ExponentData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingFusion
public import Mathlib.GroupTheory.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Mathlib.Algebra.GroupWithZero.TransferInstance

public section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

noncomputable section

private theorem natCard_ne_eq
    {Ω : Type*} [Finite Ω] (α : Ω) :
    Nat.card {β : Ω // β ≠ α} = Nat.card Ω - 1 := by
  classical
  let : Fintype Ω := Fintype.ofFinite Ω
  simpa only [← Nat.card_eq_fintype_card, Set.coe_ofPred] using Set.card_ne_eq α

theorem IsRegularOn.natCard_compl_point
    {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    {R : Subgroup G} {α : Ω}
    (hreg : IsRegularOn R {β : Ω | β ≠ α})
    (hfix : R ≤ MulAction.stabilizer G α) (hα : ∃ β : Ω, β ≠ α) :
    Nat.card R = Nat.card Ω - 1 := by
  classical
  obtain ⟨β, hβ⟩ := hα
  let f : {γ : Ω // γ ≠ α} → R := fun γ => (hreg hβ γ.property).choose
  have hf : ∀ γ : {γ : Ω // γ ≠ α}, (f γ : G) • β = γ.val :=
    fun γ => (hreg hβ γ.property).choose_spec.1
  have hf_inj : Function.Injective f := by
    intro γ δ h
    apply Subtype.ext
    exact (hf γ).symm.trans ((congrArg (fun r : R => (r : G) • β) h).trans (hf δ))
  have hf_surj : Function.Surjective f := by
    intro r
    have hmove : (r : G) • β ≠ α := by
      intro hr
      have hrfix : (r : G) • α = α :=
        MulAction.mem_stabilizer_iff.mp (hfix r.property)
      exact hβ (MulAction.injective (r : G) (hr.trans hrfix.symm))
    refine ⟨⟨(r : G) • β, hmove⟩, ?_⟩
    exact ((hreg hβ hmove).choose_spec.2 r rfl).symm
  exact (Nat.card_eq_of_bijective f ⟨hf_inj, hf_surj⟩).symm.trans (natCard_ne_eq α)

theorem IsStronglyEmbedded.sylow_card_dvd_nonbase_cosets
    {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : IsStronglyEmbedded H) (S : Sylow 2 X) (hSH : (S : Subgroup X) ≤ H) :
    Nat.card S ∣ Nat.card (conjugateCosetSpace H) - 1 := by
  classical
  let α : conjugateCosetSpace H := QuotientGroup.mk 1
  have hfixα : ∀ s : S, (s : X) • α = α := by
    intro s
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact hSH s.property
  let Away : SubMulAction S (conjugateCosetSpace H) :=
    { carrier := {β | β ≠ α}
      smul_mem' := fun s β hβ => by
        intro h
        exact hβ (MulAction.injective (s : X) (h.trans (hfixα s).symm)) }
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfree : ∀ β : Away, MulAction.stabilizer S β = ⊥ := by
    intro β
    apply le_antisymm _ bot_le
    intro s hs
    change s = 1
    by_contra hsone
    let t : S := s ^ (orderOf s / 2)
    have htord : orderOf t = 2 :=
      orderOf_pow_orderOf_div
        (S.isPGroup'.isOfFinOrder (by decide) s).orderOf_pos.ne'
        (S.isPGroup'.dvd_orderOf hsone)
    have ht : IsInvolution (t : X) := by
      have h := orderOf_eq_prime_iff.mp ((Subgroup.orderOf_coe t).trans htord)
      exact ⟨h.2, h.1⟩
    have htβ : (t : X) • β.val = β.val := by
      have htp : t ∈ MulAction.stabilizer S β :=
        (MulAction.stabilizer S β).pow_mem hs _
      exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp htp)
    obtain ⟨γ, _hγ, huniq⟩ := hH.involution_fixed_coset_unique ht
    exact β.property ((huniq _ htβ).trans (huniq _ (hfixα t)).symm)
  have hcard : Nat.card Away =
      Nat.card (Quotient (MulAction.orbitRel S Away)) * Nat.card S := by
    rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hfree), Nat.card_prod]
  have hdvd : Nat.card S ∣ Nat.card Away := by
    rw [hcard]
    exact dvd_mul_left _ _
  have hAway : Nat.card Away = Nat.card (conjugateCosetSpace H) - 1 :=
    natCard_ne_eq α
  rwa [hAway] at hdvd

end

end CFSG.BenderSuzuki
