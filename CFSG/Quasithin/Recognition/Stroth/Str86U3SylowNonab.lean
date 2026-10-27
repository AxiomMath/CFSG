module

public import CFSG.Quasithin.Recognition.Stroth.BenderH7

import CFSG.Quasithin.Recognition.Stroth.BenderSylow

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

private theorem str86U3nonab_not_commutator_le_pCoreOf
    {L T : Subgroup G} {K : Type} [Group K] [Finite K]
    (ψ : oTwoQuot ↥L →* K) (hψ : Function.Surjective ψ)
    {n e : ℕ} (hB : BenderType K n 3 e) (hT : IsSylowTwoOf T L) :
    ¬ ⁅T, T⁆ ≤ pCoreOf 2 L := by
  classical
  intro hcomm
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥L →* K := ψ.comp (QuotientGroup.mk' (pCore 2 ↥L))
  have hf : Function.Surjective f := hψ.comp (QuotientGroup.mk'_surjective _)
  let T1 : Subgroup ↥L := T.subgroupOf L
  have hT1p : IsPGroup 2 ↥T1 := hT.2.1.comap_of_injective L.subtype L.subtype_injective
  let P1 : Sylow 2 ↥L := hT1p.toSylow hT.2.2
  let P2 : Sylow 2 K := P1.mapSurjective hf
  have hP2 : (P2 : Subgroup K) = T1.map f := Sylow.coe_mapSurjective hf P1
  have hT1 : T1.map L.subtype = T := Subgroup.map_subgroupOf_eq_of_le hT.1
  have hcomm1 : ⁅T1, T1⁆ ≤ pCore 2 ↥L := by
    refine (Subgroup.map_le_map_iff_of_injective L.subtype_injective).mp ?_
    rw [Subgroup.map_commutator, hT1]
    exact hcomm
  have hbot : ⁅(P2 : Subgroup K), (P2 : Subgroup K)⁆ = ⊥ := by
    rw [hP2, ← Subgroup.map_commutator, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot]
    have hx1 : (QuotientGroup.mk' (pCore 2 ↥L)) x = 1 :=
      (QuotientGroup.eq_one_iff (N := pCore 2 ↥L) x).mpr (hcomm1 hx)
    change ψ ((QuotientGroup.mk' (pCore 2 ↥L)) x) = 1
    rw [hx1, map_one]
  have hZ : rootCenter (P2 : Subgroup K) = ⊥ := (hB.lemma_3_5_a_unitary P2).1.symm.trans hbot
  obtain ⟨t, hc⟩ := hB.exists_benderCore P2
  have hcard := hc.card_center
  rw [hZ, Subgroup.card_bot] at hcard
  have hq : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := hB.two_le.2; omega)
  exact (ne_of_lt hq) hcard

theorem str86_not_commutator_le_q1 {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    ¬ ⁅S, S⁆ ≤ Q1 L1 L2 S := by
  classical
  intro hcomm
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hT : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hcomm' : ⁅S, S⁆ ≤ pCoreOf 2 (L1 ⊔ Q1 L1 L2 S) := by
    rw [pCoreOf_sup_pCoreOf hF.1]
    exact hcomm
  obtain ⟨e', hBproj⟩ := benderType_statedProj hk hFc
  rcases hU3 with hSU | hPSU
  ·
    obtain ⟨eL⟩ := hSU
    let E := (oTwoQuotSupEquiv hF.1).trans eL
    let Sc : Subgroup (StatedSU 3 (2 ^ k) F) :=
      (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ k) F)
    let ψ : oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) →* StatedProj (StatedSU 3 (2 ^ k) F) :=
      (QuotientGroup.mk' Sc).comp E.toMonoidHom
    have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective Sc).comp E.surjective
    exact str86U3nonab_not_commutator_le_pCoreOf ψ hψ hBproj hT hcomm'
  · obtain ⟨eL⟩ := hPSU
    let E := (oTwoQuotSupEquiv hF.1).trans eL
    exact str86U3nonab_not_commutator_le_pCoreOf E.toMonoidHom E.surjective hBproj hT hcomm'

end CFSG.Quasithin.Stroth

end
