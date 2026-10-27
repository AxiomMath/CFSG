module

public import CFSG.Quasithin.EmptyFaithful.SmithL3ResMod
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.EmptyFaithful.S151TBA7Aut

public section

namespace CFSG.Quasithin.SmithL3Res

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.S151TB CFSG.Quasithin.H13.U3.GC137 CFSG.LieType.BorelTits
open CFSG.Open hiding StatedSL
open scoped Pointwise

variable {G : Type} [Group G]

theorem relIndex_sup_left_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B hB) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

theorem relIndex_sup_right_of_le_normalizer {B A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hA
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hA).toEquiv.symm

theorem isSylowTwoOf_sup_of_inf {L S : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hS2 : IsPGroup 2 ↥S) (hsyl : IsSylowTwoOf (S ⊓ L) L) : IsSylowTwoOf S (L ⊔ S) := by
  refine ⟨le_sup_right, hS2, ?_⟩
  have hT : S ⊓ L ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hSL
  have h2 : S.relIndex (L ⊔ S) = (S ⊓ L).relIndex (L ⊔ (S ⊓ L)) := by
    rw [relIndex_sup_left_of_le_normalizer hSL, relIndex_sup_left_of_le_normalizer hT]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  have h3 : (S ⊓ L).relIndex (L ⊔ (S ⊓ L)) * (L ⊔ (S ⊓ L)).relIndex L = (S ⊓ L).relIndex L :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right (sup_le le_rfl inf_le_right)
  intro h2d
  apply hsyl.2.2
  have h4 : 2 ∣ S.relIndex (L ⊔ S) := h2d
  rw [h2] at h4
  show 2 ∣ (S ⊓ L).relIndex L
  rw [← h3]
  exact Dvd.dvd.mul_right h4 _

variable [Finite G]

theorem not_isG2Two_quot {L R : Subgroup G} (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hR : IsPGroup 2 ↥R) :
    ¬ IsG2Two (↥(L ⊔ R) ⧸ CFSG.pCore 2 ↥(L ⊔ R)) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(L ⊔ R) = 12096 * Nat.card ↥(CFSG.pCore 2 ↥(L ⊔ R)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(L ⊔ R)), h.1]
  have h2 : Nat.card ↥L = 168 * Nat.card ↥(CFSG.pCore 2 ↥L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), hcard]
  have h3 : L.relIndex (L ⊔ R) * Nat.card ↥L = Nat.card ↥(L ⊔ R) := by
    have := Subgroup.relIndex_mul_card (H := L) (K := L ⊔ R)
    rwa [inf_eq_left.mpr le_sup_left] at this
  have h4 : L.relIndex (L ⊔ R) ∣ Nat.card ↥R := by
    rw [sup_comm, relIndex_sup_right_of_le_normalizer hRN]
    exact Subgroup.relIndex_dvd_card L R
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  rw [ha] at h4
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  have h9 : 9 ∣ 168 * (2 ^ b * 2 ^ c) := by
    have h9' : 9 ∣ Nat.card ↥(L ⊔ R) := by
      rw [h1]
      exact Dvd.dvd.mul_right (by norm_num) _
    rw [← h3, hc, h2, hb] at h9'
    have e : 2 ^ c * (168 * 2 ^ b) = 168 * (2 ^ b * 2 ^ c) := by ring
    rwa [e] at h9'
  have hcop : Nat.Coprime 9 (2 ^ b * 2 ^ c) := by
    rw [← pow_add]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have h168 := hcop.dvd_of_dvd_mul_right h9
  norm_num at h168

theorem pCoreOf_le_of_msPair {G₀ R N : Subgroup G} (hMS : IsMSPair G₀ R)
    (hG2 : ¬ IsG2Two (↥G₀ ⧸ CFSG.pCore 2 ↥G₀)) (hNG : N ≤ G₀)
    (hNR : G₀ ⊓ Subgroup.normalizer (R : Set G) ≤ N) : pCoreOf 2 N ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hMS.2.1 with ⟨H, hHlt, hodd, rfl⟩ | ⟨-, -, hg2, -⟩
  · have hHN : H ≤ N := fun x hx => hNR ⟨hHlt.le hx, le_normalizer_pCoreOf 2 H hx⟩
    obtain ⟨P, hP⟩ := exists_isSylowTwoOf H
    have hPG : IsSylowTwoOf P G₀ := by
      refine ⟨hP.1.trans hHlt.le, hP.2.1, fun h2 => ?_⟩
      have h1 := Subgroup.relIndex_mul_relIndex P H G₀ hP.1 hHlt.le
      have h3 : 2 ∣ P.relIndex H * H.relIndex G₀ := h1 ▸ h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h3 with h | h
      · exact hP.2.2 h
      · exact hodd h
    have hPN : IsSylowTwoOf P N := isSylowTwoOf_of_le_of_le' hPG (hP.1.trans hHN) hNG
    have hON : pCoreOf 2 N ≤ H := (pCoreOf_two_le_of_isSylowTwoOf hPN).trans hP.1
    exact le_pCoreOf_of_le_normalizer 2 hON (hHN.trans (le_normalizer_pCoreOf 2 N))
      (pCoreOf_isPGroup 2 N)
  · exact (hG2 hg2).elim

omit [Finite G] in
theorem mem_centerOf_of_mem_omegaOneCenterOf {X : Subgroup G} {z : G}
    (hz : z ∈ omegaOneCenterOf X) : z ∈ centerOf X :=
  (Subgroup.closure_le (centerOf X)).2 (fun _ hx => hx.1) hz

end CFSG.Quasithin.SmithL3Res

