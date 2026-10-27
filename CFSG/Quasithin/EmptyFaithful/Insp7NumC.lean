module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumB
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin

open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordSuzuki)
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

@[expose] def OddFam (L : Type) [Group L] : Prop :=
  StatedClassicalModel L .PSL 3 3 1 ∨
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel L .PSL 2 p 1

@[expose] def SporSmall (L : Type) [Group L] : Prop :=
  ∃ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) ∧
    Nonempty ((L ⧸ CFSG.pCore 2 L) ≃* NativeSporadic.Carrier s)

theorem pCore_le_center_of_quasisimple {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L) :
    CFSG.pCore 2 L ≤ Subgroup.center L := by
  have hN : (CFSG.pCore 2 L).Normal := CFSG.pCore_normal
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hN with h | h
  · exfalso
    have hp : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
    rw [h] at hp
    have hL : IsPGroup 2 L := hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent L := hL.isNilpotent
    have hnt : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have hperf : Group.IsPerfect L := hq.1
    exact Group.IsPerfect.not_isSolvable L inferInstance
  · exact h

theorem bigDvd_of_cover {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (h : 2 ^ 9 ∣ Nat.card (L ⧸ CFSG.pCore 2 L)) : BigDvd L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQZ : CFSG.pCore 2 L ≤ Subgroup.center L := pCore_le_center_of_quasisimple hq
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(Subgroup.center L)) := inferInstance
  set T : Subgroup L := (P : Subgroup ↥(Subgroup.center L)).map (Subgroup.center L).subtype with hT
  have hTZ : T ≤ Subgroup.center L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hTn : T.Normal := Subgroup.normal_of_le_center hTZ
  have hTp : IsPGroup 2 T := P.isPGroup'.map _
  have hTQ : T ≤ CFSG.pCore 2 L := le_sSup ⟨hTn, hTp⟩
  have hTsub : T.subgroupOf (Subgroup.center L) = (P : Subgroup ↥(Subgroup.center L)) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.center L).subtype_injective _
  have hodd : ¬ 2 ∣ (CFSG.pCore 2 L).relIndex (Subgroup.center L) := by
    intro h2
    have h3 := h2.trans (Subgroup.relIndex_dvd_of_le_left (Subgroup.center L) hTQ)
    have h4 : T.relIndex (Subgroup.center L) = (P : Subgroup ↥(Subgroup.center L)).index := by
      rw [Subgroup.relIndex, hTsub]
    rw [h4] at h3
    exact P.not_dvd_index h3
  have hmul := Subgroup.relIndex_mul_index hQZ
  have hcop : Nat.Coprime (2 ^ 9) ((CFSG.pCore 2 L).relIndex (Subgroup.center L)) :=
    Nat.Coprime.pow_left 9 ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega)))
  unfold BigDvd
  have h' : 2 ^ 9 ∣ (CFSG.pCore 2 L).index := h
  rw [← hmul] at h'
  exact hcop.dvd_of_dvd_mul_left h'

end Insp7

end CFSG.Quasithin
