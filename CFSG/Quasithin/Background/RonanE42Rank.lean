module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem rank_card_image_eq_relIndex {K B : Subgroup G} :
    Nat.card ((B.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K)) =
      (CFSG.pCore 2 ↥K).relIndex (B.subgroupOf K) := by
  have h := Subgroup.relIndex_ker (K := B.subgroupOf K)
    (f := (QuotientGroup.mk' (CFSG.pCore 2 ↥K) : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K))
  rw [QuotientGroup.ker_mk'] at h
  exact h.symm

private theorem rank_relIndex_pCore_eq {K B : Subgroup G} (hBK : B ≤ K) :
    (CFSG.pCore 2 ↥K).relIndex (B.subgroupOf K) = (pCoreOf 2 K).relIndex B := by
  have h := Subgroup.relIndex_map_map_of_injective (f := K.subtype) (CFSG.pCore 2 ↥K)
    (B.subgroupOf K) K.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBK] at h
  exact h.symm

private theorem rank_isElemAbelian_image {K B : Subgroup G} (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 ((B.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have hcomm : ∀ x ∈ (B.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K),
      ∀ y ∈ (B.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K), x * y = y * x := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
  unfold IsElemAbelian
  refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2), ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hu2 : u ^ 2 = 1 :=
    Subtype.ext (by simpa using hB2 (u : G) (Subgroup.mem_subgroupOf.mp hu))
  rw [← map_pow, hu2, map_one]

theorem mQuot_inf_pCoreOf_le {K B : Subgroup G} (hBK : B ≤ K) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    mQuot B (B ⊓ pCoreOf 2 K) ≤
      CFSG.Open.pRank 2 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have hBp : IsPGroup 2 ↥B := by
    intro b
    exact ⟨1, Subtype.ext (by simpa using hB2 (b : G) b.2)⟩
  have key : Nat.card ((B.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K)) =
      2 ^ mQuot B (B ⊓ pCoreOf 2 K) := by
    rw [rank_card_image_eq_relIndex, rank_relIndex_pCore_eq hBK,
      ← Subgroup.inf_relIndex_left (H := B) (K := pCoreOf 2 K)]
    exact relIndex_eq_two_pow hBp _
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K),
      E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card (↥K ⧸ CFSG.pCore 2 ↥K), ?_⟩
    rintro k ⟨E', -, -, hE'⟩
    exact (k.lt_two_pow_self.le).trans
      (hE'.symm.trans_le (Subgroup.card_le_card_group (H := E')))
  have hmem : mQuot B (B ⊓ pCoreOf 2 K) ∈ {k : ℕ | ∃ E : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K),
      E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨_, le_top, rank_isElemAbelian_image hB2 hBc, key⟩
  unfold CFSG.Open.pRank
  exact le_csSup hbdd hmem

end CFSG.Quasithin.RonanE42
