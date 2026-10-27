module

public import CFSG.Quasithin.H13.A6S1372L76P2
public import CFSG.Quasithin.H13.A6S1372L76W
public import CFSG.Quasithin.H13.A6S1372L76F

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

@[expose] def Lem1376NThreeC3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    2 ^ 5 < Nat.card ↥(pCoreOf 2 (L ⊔ T)) →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H → S.L1 ≤ K →
      ¬ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1

@[expose] def Lem1376NThreeBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    Nat.card ↥(pCoreOf 2 (L ⊔ T)) ≤ 2 ^ 5 →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H → S.L1 ≤ K →
      ¬ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1

namespace A6L76N3

theorem card_GL3_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) :
    Nat.card (GL (Fin 3) F) = 168 := by
  rw [Matrix.card_GL_field, hF, Fin.prod_univ_three]
  norm_num

theorem pRank_three_le_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (X : Subgroup (GL (Fin 3) F)) : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 1 := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rwa [← Nat.card_eq_fintype_card]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun A _ hA => ?_
  have hA3 : IsPGroup 3 ↥A := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hA3.exists_card_eq
  have hdvd : Nat.card ↥A ∣ 168 := by
    rw [← card_GL3_two hF']
    exact (Subgroup.card_subgroup_dvd_card A).trans (Subgroup.card_subgroup_dvd_card X)
  rw [hk] at hdvd ⊢
  rcases Nat.lt_or_ge k 2 with h | h
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · have := (Nat.pow_dvd_pow 3 h).trans hdvd
    norm_num at this

end A6L76N3

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem not_isHatA6_of_natSL32 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    (hL1K : S.L1 ≤ K)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1) :
    ¬ IsHatA6 L := by
  intro hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := S.two_le_pRank_L1_of_hat hhat
  obtain ⟨F, _, _, hF, hR⟩ := id hSL
  obtain ⟨E⟩ := S.exists_quotEquiv_of_realizes hNS h13315 h1356two hH hK
    (FFModel.nat_faithful _) hR
  have hker : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥K) := by
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥K)).exists_card_eq
    rw [hj]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have : Finite (GL (Fin 3) F) :=
    Finite.of_injective (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) Units.val_injective
  have : Finite (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Gam := by
    show Finite ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)
    infer_instance
  have hK3 : CFSG.Open.pRank 3 K ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K) hker,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) E]
    rw [pow_one] at hF
    exact A6L76N3.pRank_three_le_one hF _
  have h3 : CFSG.Open.pRank 3 S.L1 ≤ CFSG.Open.pRank 3 K :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hL1K
  omega

end Setting4

theorem lem1376NThree_of (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hC : Lem1376NThreeC3) (hB : Lem1376NThreeBlock) :
    Lem1376NThree := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK hL1K hSL
  have hhat := S.not_isHatA6_of_natSL32 hNS h13315 h1356two hH hK hL1K hSL
  by_cases hQ : 2 ^ 5 < Nat.card ↥(pCoreOf 2 (L ⊔ T))
  · exact hC G T L V S hNS hNU hhat hQ H hH hab K hK hL1K hSL
  · exact hB G T L V S hNS hNU hhat (not_lt.1 hQ) H hH hab K hK hL1K hSL

end CFSG.Quasithin.H13.A6
