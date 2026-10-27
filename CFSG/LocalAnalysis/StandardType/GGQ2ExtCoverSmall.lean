module

public import CFSG.LocalAnalysis.StandardType.GGQ2NbrD5Frame
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelSplit
public import CFSG.LocalAnalysis.StandardType.GGCSRHolds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Kernel

variable {G : Type} [Group G] [Finite G]

theorem ker_ggBeta_le_zpowers_of_le {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L M : Subgroup G} (hS : LargeEvenSStar p B x L) (hLM : L ≤ M) (hM : commutator M = ⊤)
    {R : Type} [Group R] (θ : M ⧸ Subgroup.center M ≃* R)
    (hBN : B ≤ Subgroup.normalizer (M : Set G)) :
    (ggBeta M θ hBN).ker ≤ (Subgroup.zpowers x).subgroupOf B := by
  intro b hb
  rw [MonoidHom.mem_ker] at hb
  rw [Subgroup.mem_subgroupOf, ← inf_centralizer_eq_zpowers_of_sstar hp hS]
  exact ⟨b.2, Subgroup.centralizer_le hLM (mem_centralizer_of_ggLAut_eq_one M θ hM hb)⟩

theorem card_le_mul_card_range_ggBeta_of_le {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L M : Subgroup G} (hS : LargeEvenSStar p B x L) (hLM : L ≤ M) (hM : commutator M = ⊤)
    {R : Type} [Group R] (θ : M ⧸ Subgroup.center M ≃* R)
    (hBN : B ≤ Subgroup.normalizer (M : Set G)) :
    Nat.card B ≤ p * Nat.card (ggBeta M θ hBN).range := by
  have hxB : x ∈ B := hS.2.1
  have h1 := card_range_mul_card_ker (ggBeta M θ hBN)
  have h2 := Subgroup.card_le_of_le (ker_ggBeta_le_zpowers_of_le hp hS hLM hM θ hBN)
  have h3 : Nat.card ((Subgroup.zpowers x).subgroupOf B) = Nat.card (Subgroup.zpowers x) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxB)).toEquiv
  have h4 : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hS.1.1.2 x hxB))
  calc Nat.card B = Nat.card (ggBeta M θ hBN).range * Nat.card (ggBeta M θ hBN).ker := h1.symm
    _ ≤ Nat.card (ggBeta M θ hBN).range * p := Nat.mul_le_mul_left _ (by omega)
    _ = p * Nat.card (ggBeta M θ hBN).range := mul_comm _ _

end Kernel

section Small

theorem ggG0_not_marking_small {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGCorFiveTwentyHyp 3 B Bs x L D J) :
    ¬ LargeEvenMarking ↥(ggG0 3 B x L D J) (fun lab _ _ _ _ _ => lab.tag = .G2 ∨
      lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
      lab.tag = .G2der ∨ lab.tag = .twF4der) := by
  intro hm
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, htag⟩ := largeEvenMarking_exists_hasLabel hm
  obtain ⟨hperf, lab', hlab', hraw⟩ :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds hC.2.2.2.2 hlab hhas
  obtain ⟨-, -, -, -, -, -, -, heq, -⟩ := largeEvenRawDatum_exists hraw
  subst heq
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hBsN, hact⟩, hbound⟩ :=
    largeEvenRawDatum_exists (ggSmallThreeRank_of_labels _ hlab' htag _ hraw)
  have hSS : LargeEvenSStar 3 B x L := hC.1.1.2.2.2.2.2.2.1
  have hBsB : B ≤ Bs := hC.1.2.1.1
  have hBN : B ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := hBsB.trans hBsN
  have hI : ∀ a ∈ (ggBeta _ θ hBN).range, a ∈ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem _ θ hBN (fun b hb => hact b (hBsB hb)) b
  have h9 := hbound _ hI (isElemAbelian_range_of_isElemAbelian hSS.1.1 _)
  have hLG₀ : L ≤ ggG0 3 B x L D J := le_sup_left
  have hB := card_le_mul_card_range_ggBeta_of_le Nat.prime_three hSS hLG₀ hperf θ hBN
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := GGConfig.card_B_eq hC.1
  have hbeta : 3 ∈ LargeEvenBeta 4 G := hC.1.1.2.2.2.2.2.1
  have h81 : 3 ^ 4 ≤ 3 ^ LargeEvenTwoLocalRank 3 G :=
    Nat.pow_le_pow_right (by norm_num) hbeta.2.2.2
  omega

end Small

end CFSG.StandardType

end
