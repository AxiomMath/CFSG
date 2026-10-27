module

public import CFSG.Monster.B.TwoA.Amalgam.TypeFourCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0)

theorem native_type_four_pair_stabilizer_parabolic_projection
    (k : Jhat)
    (hk0 : cvOf (jhatS k) ≠ cv0) (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) :
    (∀ s : Shat, (cvMul cv0 s = cv0 ∧ cvMul (cvOf (jhatS k)) s = cvOf (jhatS k)) ↔
      (s : Dfull) ∈ Q4 k) ∧
    Q4 k ≤ P1 ∧
    ((Q4 k).subgroupOf Jhat).map jhatToKv0 = Unitary.Usig ⊓ wStab (psiW (labE k)) ∧
    Q4 k ⊓ Ehat = cNE k ∧
    CFSG.IsExtraspecialPGroup 2 (cNE k) ∧ Nat.card (cNE k) = 2 ^ 21 ∧
    (∃ e : cNE k ≃* N1 ⧸ Subgroup.zpowers cN1,
      ∀ x : cNE k, e x = QuotientGroup.mk ⟨x, cNE_le_N1 x.2⟩) ∧
    Set.InjOn (QuotientGroup.mk' (Subgroup.zpowers cP1)) ((cNE k).subgroupOf P1) ∧
    ((cNE k).subgroupOf P1).map (QuotientGroup.mk' (Subgroup.zpowers cP1)) =
      (N1.subgroupOf P1).map (QuotientGroup.mk' (Subgroup.zpowers cP1)) ∧
    Set.InjOn (QuotientGroup.mk' (Subgroup.zpowers cP1)) ((Q4 k).subgroupOf P1) ∧
    ((Q4 k).subgroupOf P1).map (QuotientGroup.mk' (Subgroup.zpowers cP1)) =
      ((wStab (psiW (labE k))).subgroupOf Unitary.Usig).comap p1cProj ∧
    Nat.card ((wStab (psiW (labE k))).subgroupOf Unitary.Usig) = 13063680 ∧
    Nat.card (Q4 k) = 2 ^ 21 * 13063680 ∧
    ∃ p : Jhat, (p : Dfull) ∈ P1 ∧ psiW (labE (k * p)) = Unitary.tauW ∧
      (wStab (psiW (labE (k * p)))).subgroupOf Unitary.Usig = Unitary.Atau := by
  have hne : (⟨cv0, jhatS_mem_cPi0 1⟩ : cPi0) ≠ piV k := fun e =>
    hk0 (congrArg Subtype.val e).symm
  have hn : ¬ cgraphPi.Adj ⟨cv0, jhatS_mem_cPi0 1⟩ (piV k) := hk
  obtain ⟨p, hp, hτ⟩ := exists_P1_tauW hk0 hk
  refine ⟨fun s => ?_, Q4_le_P1, map_Q4 hk0 hk, Q4_inf_Ehat, cNE_extraspecial hk0 hk,
    natCard_cNE hk0 hk, ⟨cNEEquiv hk0 hk, cNEEquiv_apply hk0 hk⟩,
    injOn_mk_of_le hk0 hk cNE_le_Q4, map_cNE_quot hk0 hk, injOn_mk_of_le hk0 hk le_rfl,
    map_Q4_quot hk0 hk, natCard_stab_of_mem_tauOrb (by
      rw [← piPt_eq_psiW]
      exact piPt_mem_tauOrb hk0 hk), natCard_Q4 hk0 hk, p, hp, hτ, by rw [hτ]; rfl⟩
  rw [show cvMul cv0 s = cv0 ∧ cvMul (cvOf (jhatS k)) s = cvOf (jhatS k) ↔
    (cvMul (⟨cv0, jhatS_mem_cPi0 1⟩ : cPi0).1 s = (⟨cv0, jhatS_mem_cPi0 1⟩ : cPi0).1 ∧
      cvMul (piV k).1 s = (piV k).1) from Iff.rfl, pairStab_iff hne hn]
  show _ ↔ ((s : Dfull) ∈ Jhat ∧ (s : Dfull) ∈ Subgroup.centralizer {cQ}) ∧
    (s : Dfull) ∈ Subgroup.centralizer {(labE k : Dfull)}
  rw [show clabel (⟨cv0, jhatS_mem_cPi0 1⟩ : cPi0).1 = cQ from clabel_cv0,
    show clabel (piV k).1 = labE k from rfl]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

end CFSG.Monster.B.TwoA.Amalgam
