module

public import CFSG.Quasithin.H13.A6S1372EighteenB

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76

@[expose] def vecS (n : ℕ) (S : Finset (Fin n)) : G6.PermMod n :=
  Multiplicative.ofAdd fun i => if i ∈ S then 1 else 0

@[expose] def MapsOnto {V : Type*} [CommGroup V] {U : Subgroup V} {D : FFModel}
    (β : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec) (W : Subgroup V) (vs : List D.Amb) : Prop :=
  (∀ x : ↥U, (x : V) ∈ W →
      ∃ m : ↥D.sec, β x = QuotientGroup.mk m ∧ (m : D.Amb) ∈ vs) ∧
    ∀ v ∈ vs, ∃ x : ↥U, (x : V) ∈ W ∧
      ∃ m : ↥D.sec, β x = QuotientGroup.mk m ∧ (m : D.Amb) = v

end A6L76

@[expose] def Lem1376Full : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H →
      (∀ n, 3 ≤ n → BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n 1 →
        n = 4 ∧ IsHatA6 L ∧ BinaryNaturalSL (autSec (autOn H (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤ ⊥ 4 1) ∧
      ¬ SLExteriorTwo (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 5 ∧
      (∀ n, AlternatingNatural (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n →
        ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H ∧ S.L1 ≤ K ∧ H = K ⊔ T ∧
          ((n = 6 ∧ ¬ IsHatA6 L ∧
            (∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 → ∀ u ∈ conjClosure S.V3 H,
              (∀ k ∈ K, k * (c * u * c⁻¹ * u⁻¹) * k⁻¹ * (c * u * c⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V) →
              ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧
            ∃ (π : (FFModel.altDn 6).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
                ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
              (β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
                ↥(FFModel.altDn 6).sec ⧸ (FFModel.altDn 6).ker.subgroupOf
                  (FFModel.altDn 6).sec),
              CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 6)
                (autSec (autOn K (conjClosure S.V3 H)) ⊤
                  ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
                (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                  ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
                (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
                  commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β ∧
              A6L76.MapsOnto β ((S.V2.subgroupOf (conjClosure S.V3 H)).map
                  (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
                ([1, A6L76.vecS 6 {0, 1, 2, 3}] : List (FFModel.altDn 6).Amb)) ∨
          (n = 7 ∧ IsHatA6 L ∧
            ∃ (π : (FFModel.altDn 7).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
                ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
              (β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
                ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf
                  (FFModel.altDn 7).sec),
              CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 7)
                (autSec (autOn K (conjClosure S.V3 H)) ⊤
                  ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
                (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                  ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
                (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
                  commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β ∧
              A6L76.MapsOnto β ((S.V2.subgroupOf (conjClosure S.V3 H)).map
                  (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
                ([1, A6L76.vecS 7 {4, 5}] : List (FFModel.altDn 7).Amb) ∧
              A6L76.MapsOnto β ((S.V3.subgroupOf (conjClosure S.V3 H)).map
                  (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
                ([1, A6L76.vecS 7 {4, 5}, A6L76.vecS 7 {4, 6}, A6L76.vecS 7 {5, 6}] :
                  List (FFModel.altDn 7).Amb)))) ∧
      ¬ SLExteriorTwo (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 4 ∧
      ¬ A7Four (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) ∧
      (∀ n, BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n → n = 1) ∧
      (∀ n, BinaryNaturalSp4 (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n → n = 1) ∧
      (∀ n, G2Natural (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n → n = 1)

theorem lem1376AltNat_of_full (h : Lem1376Full) : Lem1376AltNat := by
  intro G _ _ T L V S hNS hNU hhat H hH hab _ K hK
  obtain ⟨h1, h2, h3, h38, h4, h5a, h5b, h5c⟩ := h G T L V S hNS hNU H hH hab K hK
  refine ⟨fun n hn hb => hhat (h1 n hn hb).2.1, h2, fun n hn => ?_, h38, h4, h5a, h5b, h5c⟩
  obtain ⟨hUK, hL1K, hHKT, h6 | h7⟩ := h3 n hn
  · exact ⟨h6.1, hUK, hL1K, hHKT, h6.2.2.1⟩
  · exact absurd h7.2.1 hhat

end CFSG.Quasithin.H13.A6
