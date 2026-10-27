module


import CFSG.Quasithin.Recognition.Stroth.Str86XOne3
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Vol2.Ch3zCmp

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

private theorem eq_of_le_of_relIndex_le {G : Type*} [Group G] [Finite G]
    {Q C H : Subgroup G} (hQC : Q ≤ C) (hCH : C ≤ H) {a b : ℕ}
    (hQ : Q.relIndex H = a) (hC : C.relIndex H = b) (hab : a ≤ b) :
    C = Q := by
  have hbpos : 0 < b := by
    rw [← hC]
    exact Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero C H)
  have htower : Q.relIndex C * C.relIndex H = Q.relIndex H :=
    Subgroup.relIndex_mul_relIndex (H := Q) (K := C) (L := H) hQC hCH
  have hqle : Q.relIndex C ≤ 1 := by
    refine Nat.le_of_mul_le_mul_right ?_ hbpos
    rw [one_mul, ← hC, htower, hQ, hC]
    exact hab
  have hqne : Q.relIndex C ≠ 0 := D15Proof.relIndex_ne_zero Q C
  have hq1 : Q.relIndex C = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hq1) hQC

private theorem card_oTwoQuot_sup_le
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    Nat.card (oTwoQuot ↥(L1 ⊔ S)) ≤ Nat.card ↥(StatedSU 3 (2 ^ k) F) := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hQeq : oTwoQuot ↥(L1 ⊔ S) ≃* oTwoQuot ↥L1 :=
    u3QEquiv (L1 := L1) (L2 := L2) (S := S) hF hSB h1
  rcases hU3 with h | h
  · obtain ⟨e⟩ := h
    exact le_of_eq (Nat.card_congr (hQeq.trans e).toEquiv)
  · obtain ⟨e⟩ := h
    calc Nat.card (oTwoQuot ↥(L1 ⊔ S)) =
        Nat.card (StatedProj (StatedSU 3 (2 ^ k) F)) :=
          Nat.card_congr (hQeq.trans e).toEquiv
      _ ≤ Nat.card ↥(StatedSU 3 (2 ^ k) F) :=
          Nat.card_le_card_of_surjective
            (QuotientGroup.mk'
              ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ k) F)))
            (QuotientGroup.mk'_surjective _)

private theorem card_chiefAut_eq_natural {H L N : Subgroup G} {k : ℕ} {F : Type}
    [Field F] [Finite F] (hFc : Nat.card F = (2 ^ k) ^ 2)
    {hE : IsElemAbelian 2 (Ch3z.chiefMod L N)}
    (hnat : @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut H L N) ⊤ ⊥ k) :
    Nat.card ↥(Ch3z.chiefAut H L N) = Nat.card ↥(StatedSU 3 (2 ^ k) F) := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    @BinaryNaturalSU3.exists_equiv ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut H L N) k hnat
  letI : Field K := hKfield
  letI : Finite K := hKfin
  rw [← Nat.card_congr e.toEquiv,
    CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq (q := 2 ^ k) hKcard,
    CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq (q := 2 ^ k) hFc]

theorem Str86AbHyp.mem_q1_of_chiefFactor_natural
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {U L N : Subgroup G} (hUH : U ≤ L1 ⊔ S)
    (hstep : IsChiefStep (L1 ⊔ S) U L N) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hnat : @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k)
    {g : G} (hg : g ∈ L1 ⊔ S) (hgc : ∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ L) :
    g ∈ Q1 L1 L2 S := by
  classical
  let H : Subgroup G := L1 ⊔ S
  let C : Subgroup G := centralizerMod L H N
  have hF := hI.hF
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hKsub : C.subgroupOf H = (Ch3z.chiefHom hHL hHN).ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, ← Ch3z.chiefHom_eq_one_iff hHL hHN hNL g, MonoidHom.mem_ker]
  have hcardC : C.relIndex H = Nat.card ↥(Ch3z.chiefAut H L N) := by
    rw [Subgroup.relIndex, hKsub, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (Ch3z.chiefHom_surjective hHL hHN), Subgroup.card_top]
  have hpCoreH : pCoreOf 2 H = Q1 L1 L2 S :=
    u3LS_pCoreOf (k := k) (F := F) hF hI.hSB h1
  have hpCore_sub : CFSG.Open.pCore 2 ↥H = (Q1 L1 L2 S).subgroupOf H :=
    u3LS_pCore_subgroupOf (k := k) (F := F) hF hI.hSB h1
  have hQ1C : Q1 L1 L2 S ≤ C := by
    rw [← hpCoreH]
    exact Ch3z.pCoreOf_le_centralizerMod hUH hstep hE
  have hcardQ : (Q1 L1 L2 S).relIndex H = Nat.card (oTwoQuot ↥H) := by
    rw [Subgroup.relIndex, Subgroup.index, ← hpCore_sub]
  have hSU_le : Nat.card (oTwoQuot ↥H) ≤ Nat.card ↥(StatedSU 3 (2 ^ k) F) :=
    card_oTwoQuot_sup_le hF hI.hSB hI.hk hI.hFc hI.hU3
  have hcardChief : Nat.card ↥(Ch3z.chiefAut H L N) =
      Nat.card ↥(StatedSU 3 (2 ^ k) F) :=
    card_chiefAut_eq_natural (H := H) hI.hFc hnat
  have hle : Nat.card (oTwoQuot ↥H) ≤ Nat.card ↥(Ch3z.chiefAut H L N) := by
    rw [hcardChief]
    exact hSU_le
  have hCeq : C = Q1 L1 L2 S :=
    eq_of_le_of_relIndex_le hQ1C (centralizerMod_le_left L H N) hcardQ hcardC hle
  rw [← hCeq]
  exact ⟨hg, hHL hg, hgc⟩

end CFSG.Quasithin.Stroth

end
