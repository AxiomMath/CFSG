module

public import CFSG.Quasithin.H13.A6S1372L76K
public import CFSG.Quasithin.H13.A6S1372L76A
public import CFSG.Quasithin.H13.A6S1372L76P

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76L

theorem injective_of_simple {Γ Q : Type*} [Group Γ] [Group Q] [IsSimpleGroup Γ] [Nontrivial Q]
    (π : Γ →* Q) (hπ : Function.Surjective π) : Function.Injective π := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact h
  · exfalso
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    obtain ⟨g, rfl⟩ := hπ q
    exact hq ((MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top g))

end A6L76L

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem isPerfect_tilde {H K : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] (hK : K ∈ cComp H) :
    Group.IsPerfect ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
  let κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict _
      fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκ : Function.Surjective κ := by
    intro x
    obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 x.2
    exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩
  exact Group.IsPerfect.ofSurjective hκ

theorem lem1376_three (hB : Lem1376L1K) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) (hNS : ¬ LieModel G .PSp 3 2 1) (hNU : ¬ LieModel G .PSU 4 3 1)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) (n : ℕ)
    (hAN : AlternatingNatural (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n) :
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
              List (FFModel.altDn 7).Amb))) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1K : S.L1 ≤ K := hB G T L V S hNS hNU H hH hab K hK (Or.inr (Or.inr (Or.inl ⟨n, hAN⟩)))
  obtain ⟨π, β, hR⟩ := (CFSG.Quasithin.H.Mathieu.realizes_iff _ _ _ _).1 hAN
  have := S.nontrivial_tilde_of_L1_le hH hKH hL1K
  have hn5 : 5 ≤ n := by
    by_contra hlt
    have hcard : Nat.card (Fin n) ≤ 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    have : Group.IsSolvable (FFModel.altDn n).Gam := alternatingGroup.isSolvable hcard
    have hsolv : Group.IsSolvable ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := Group.isSolvable_of_surjective hR.1
    have := S.isPerfect_tilde hH hK
    exact Group.IsPerfect.not_isSolvable _ hsolv
  have : IsSimpleGroup (FFModel.altDn n).Gam := A6L76A.isSimpleGroup_alt hn5
  have hπ : Function.Injective π := A6L76L.injective_of_simple π hR.1
  have hrad := A6L76A.rad_eq_bot_of_surjective (Γ := (FFModel.altDn n).Gam)
    (A6L76A.not_isSolvable_alt hn5) π hR.1
  have hHK := S.le_normalizer_of_L1_le hH h37 h38 hK hL1K hrad
  have hUK := S.commutator_UH_eq_of_L1_le hKH hHK hL1K
  rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n by omega) with rfl | rfl | rfl | rfl | h9
  · exact (Ctx76.false_five
      ⟨hNS, h13315, h1356two, hH, hab, hK, hL1K, hHK, hUK, π, β, hR, hπ⟩).elim
  · obtain ⟨hhat, hfpf, π', β', hR', hM⟩ := Ctx76.six
      ⟨hNS, h13315, h1356two, hH, hab, hK, hL1K, hHK, hUK, π, β, hR, hπ⟩
    exact ⟨hUK, hL1K, (sup_eq_of_realizes6 hNS h13315 h1356two hH hKH hHK hUK hR hπ).symm,
      Or.inl ⟨rfl, hhat, hfpf, π', β', hR', hM⟩⟩
  · obtain ⟨hhat, π', β', hR', hM2, hM3⟩ := Ctx76.seven h13314 h1337
      ⟨hNS, h13315, h1356two, hH, hab, hK, hL1K, hHK, hUK, π, β, hR, hπ⟩
    exact ⟨hUK, hL1K, (sup_eq_of_realizes7 hNS h13315 h1356two hH hKH hHK hUK hR hπ).symm,
      Or.inr ⟨rfl, hhat, π', β', hR', hM2, hM3⟩⟩
  · exact (Ctx76.false_eight h13314
      ⟨hNS, h13315, h1356two, hH, hab, hK, hL1K, hHK, hUK, π, β, hR, hπ⟩).elim
  · exact (Ctx76.false_ge_nine h9
      ⟨hNS, h13315, h1356two, hH, hab, hK, hL1K, hHK, hUK, π, β, hR, hπ⟩).elim

end Setting4

end CFSG.Quasithin.H13.A6
