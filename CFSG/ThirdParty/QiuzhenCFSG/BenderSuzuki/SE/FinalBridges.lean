module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.RankOne
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.ConjugateAction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c

namespace CFSG
end CFSG
open CFSG

/-!
# Bridges for the final Bender--Suzuki reduction

This file exposes two structural facts used after the Sections 9--11
contradiction: rank transport from the ambient involution core into the
strongly embedded subgroup, and faithfulness of the conjugate-coset action in
the simple ambient case.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u v

private theorem rank_at_least_two_of_sylow_containment
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} (P : Sylow 2 G) (hPM : (P : Subgroup G) ≤ M)
    (hG : TwoRankAtLeastTwo G) : TwoRankAtLeastTwo M := by
  rcases hG with ⟨E, hEcard, hEsq⟩
  have hEp : IsPGroup 2 E := by
    apply IsPGroup.of_card (p := 2) (G := E) (n := 2)
    simp [hEcard]
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  let fG : E →* G := (MulAut.conj g).toMonoidHom.comp E.subtype
  have hfG_inj : Function.Injective fG := by
    intro a b hab
    apply Subtype.ext
    apply (MulAut.conj g).injective
    simpa [fG] using hab
  have hfG_mem_P : ∀ e : E, fG e ∈ (P : Subgroup G) := by
    intro e
    rw [show (P : Subgroup G) = ((g • S : Sylow 2 G) : Subgroup G) from
      congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg.symm]
    rw [Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr ⟨e, hES e.property, rfl⟩
  let fM : E →* M := fG.codRestrict M (fun e => hPM (hfG_mem_P e))
  have hfM_inj : Function.Injective fM := by
    intro a b hab
    exact hfG_inj (by simpa [fM] using congrArg Subtype.val hab)
  let EM : Subgroup M := (⊤ : Subgroup E).map fM
  have hEMcard : Nat.card EM = 4 := by
    rw [Subgroup.card_map_of_injective hfM_inj]
    calc
      Nat.card (⊤ : Subgroup E) = Nat.card E :=
        Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv
      _ = 4 := hEcard
  refine ⟨EM, hEMcard, ?_⟩
  rintro ⟨x, hx⟩
  rcases hx with ⟨e, _he, rfl⟩
  apply Subtype.ext
  simpa using congrArg fM (hEsq e)

private theorem rank_at_least_two_of_four_group_subgroup
    {G : Type u} [Group G]
    {M : Subgroup G} (hM : TwoRankAtLeastTwo M) :
    TwoRankAtLeastTwo (involutionCore M) := by
  rcases hM with ⟨E, hEcard, hEsq⟩
  have hEle : E ≤ involutionCore M := by
    intro x hx
    by_cases hxone : x = 1
    · simp [hxone]
    rw [involutionCore_eq_closure]
    apply Subgroup.subset_closure
    refine ⟨hxone, ?_⟩
    exact congrArg Subtype.val (hEsq ⟨x, hx⟩)
  let EC : Subgroup (involutionCore M) := E.subgroupOf (involutionCore M)
  refine ⟨EC, ?_, ?_⟩
  · rw [natCard_subgroupOf_eq E (involutionCore M) hEle]
    exact hEcard
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val (hEsq ⟨(x : M), x.property⟩)

public theorem rank_involutionCore_of_ambient_rank
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hrank : TwoRankAtLeastTwo (involutionCore X)) :
    TwoRankAtLeastTwo (involutionCore M) := by
  have hXrank : TwoRankAtLeastTwo X :=
    hrank.map_of_injective (involutionCore X).subtype Subtype.val_injective
  obtain ⟨P, hPM⟩ := hM.containsSylowTwo
  exact rank_at_least_two_of_four_group_subgroup
    (rank_at_least_two_of_sylow_containment P hPM hXrank)

public theorem faithful_conjugateCosetSpace_of_simple
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X) :
    FaithfulSMul X (conjugateCosetSpace M) := by
  let C : Subgroup X := pointStabilizerCore X (conjugateCosetSpace M)
  have hCnormal : C.Normal :=
    PFchapter1section1.proposition_4_c_pointStabilizerCore_normal
  have hCproper : C ≠ ⊤ := by
    intro htop
    have hCleM : C ≤ M := by
      have hCle : C ≤ MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) :=
        (le_pointStabilizerCore_iff (G := X)
          (Ω := conjugateCosetSpace M) (K := C)).mp le_rfl _
      simpa only [baseCoset_stabilizer] using hCle
    apply hM.1
    exact top_unique (by simpa [C, htop] using hCleM)
  have hCbot : C = ⊥ := by
    rcases (haveI := hCnormal; hX.eq_bot_or_eq_top_of_normal C) with hbot | htop
    · exact hbot
    · exact (hCproper htop).elim
  apply faithfulSMul_iff.mpr
  intro g hfix
  have hgC : g ∈ C := by
    change g ∈ pointStabilizerCore X (conjugateCosetSpace M)
    simp only [pointStabilizerCore, Subgroup.mem_iInf]
    intro omega
    exact MulAction.mem_stabilizer_iff.mpr (hfix omega)
  have hgBot : g ∈ (⊥ : Subgroup X) := by
    simpa [C, hCbot] using hgC
  exact Subgroup.mem_bot.mp hgBot

end CFSG.BenderSuzuki
