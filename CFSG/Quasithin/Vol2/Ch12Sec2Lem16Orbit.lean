module

public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace Lem16

open Orbit

section Abstract

variable {V : Type*} [CommGroup V]

theorem orbitIn_apply_eq {K : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (K : Set (MulAut V))) (a : V) :
    orbitIn K (h a) = h '' orbitIn K a := by
  ext w
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : h⁻¹ * k * h ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) k).mp hk
      rwa [inv_inv] at this
    refine ⟨(h⁻¹ * k * h) a, ⟨h⁻¹ * k * h, hk', rfl⟩, ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨h * k * h⁻¹, (Subgroup.mem_normalizer_iff.mp hh k).mp hk, ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

theorem card_orbitIn_apply {K : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (K : Set (MulAut V))) (a : V) :
    Nat.card (orbitIn K (h a)) = Nat.card (orbitIn K a) := by
  rw [orbitIn_apply_eq hh a]
  exact Nat.card_image_of_injective h.injective (orbitIn K a)

theorem orbitIn_eq_of_le_normalizer {K H : Subgroup (MulAut V)} (hKH : K ≤ H)
    (hHN : H ≤ Subgroup.normalizer (K : Set (MulAut V))) (hK : OrbitsSeparated K) {a : V}
    (ha : a ≠ 1) : orbitIn H a = orbitIn K a := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    have hha : h a ≠ 1 := fun h1 => ha (h.injective (h1.trans (map_one h).symm))
    obtain ⟨k, hk, hka⟩ := hK a (h a) ha hha (card_orbitIn_apply (hHN hh) a).symm
    exact ⟨k, hk, hka⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hKH hk, rfl⟩

theorem orbitsSeparated_of_le_normalizer {K H : Subgroup (MulAut V)} (hKH : K ≤ H)
    (hHN : H ≤ Subgroup.normalizer (K : Set (MulAut V))) (hK : OrbitsSeparated K) :
    OrbitsSeparated H := by
  intro v w hv hw hc
  rw [orbitIn_eq_of_le_normalizer hKH hHN hK hv, orbitIn_eq_of_le_normalizer hKH hHN hK hw] at hc
  obtain ⟨k, hk, hkv⟩ := hK v w hv hw hc
  exact ⟨k, hKH hk, hkv⟩

end Abstract

section Ambient

variable {G : Type} [Group G]

theorem autOn_le_normalizer_of_le {L N V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hNV : N ≤ Subgroup.normalizer (V : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    autOn N V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
  autOn_le_normalizer_autOn hLV hNV hNL

theorem card_orbitIn_mul_card_centralizer [Finite G] {N V : Subgroup G} [IsMulCommutative ↥V]
    (hN : N ≤ Subgroup.normalizer (V : Set G)) (a : ↥V) :
    Nat.card (orbitIn (autOn N V) a) *
        Nat.card ↥(N ⊓ Subgroup.centralizer ({(a : G)} : Set G)) = Nat.card N := by
  classical
  let ρ : ↥N →* MulAut ↥V := A4.actionOn V N hN
  let _ : MulAction ↥N ↥V := MulAction.compHom ↥V ρ
  have hsmul : ∀ (n : ↥N) (w : ↥V), n • w = ρ n w := fun _ _ => rfl
  have horb : orbitIn (autOn N V) a = MulAction.orbit ↥N a := by
    ext w
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨n, rfl⟩ := (A4.mem_autOn_iff hN).mp hh
      exact ⟨n, (hsmul n a).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨ρ n, (A4.mem_autOn_iff hN).mpr ⟨n, rfl⟩, (hsmul n a).symm⟩
  have hstab : MulAction.stabilizer ↥N a =
      (N ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨n.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val h
      rw [A4.actionOn_apply_coe] at h1
      calc (n : G) * (a : G) = (n : G) * (a : G) * (n : G)⁻¹ * n := by group
        _ = (a : G) * n := by rw [h1]
    · rintro ⟨-, hc⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      apply Subtype.ext
      rw [A4.actionOn_apply_coe, hc]
      group
  have hcard : Nat.card (MulAction.stabilizer ↥N a) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({(a : G)} : Set G)) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [horb, ← hcard, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥N a), mul_comm]
  exact (MulAction.stabilizer ↥N a).card_mul_index

theorem exists_conj_of_card_centralizer_eq [Finite G] {N V : Subgroup G} [IsMulCommutative ↥V]
    (hN : N ≤ Subgroup.normalizer (V : Set G)) (hsep : OrbitsSeparated (autOn N V))
    {a b : ↥V} (ha : a ≠ 1) (hb : b ≠ 1)
    (hc : Nat.card ↥(N ⊓ Subgroup.centralizer ({(a : G)} : Set G)) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({(b : G)} : Set G))) :
    ∃ n ∈ N, n * (a : G) * n⁻¹ = b := by
  have h1 := card_orbitIn_mul_card_centralizer hN a
  have h2 := card_orbitIn_mul_card_centralizer hN b
  have hpos : 0 < Nat.card ↥(N ⊓ Subgroup.centralizer ({(b : G)} : Set G)) := Nat.card_pos
  have hcard : Nat.card (orbitIn (autOn N V) a) = Nat.card (orbitIn (autOn N V) b) := by
    rw [hc] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  obtain ⟨h, hh, hab⟩ := hsep a b ha hb hcard
  obtain ⟨n, rfl⟩ := (A4.mem_autOn_iff hN).mp hh
  refine ⟨n, n.2, ?_⟩
  have := congrArg Subtype.val hab
  rwa [A4.actionOn_apply_coe] at this

end Ambient

end Lem16

end CFSG.Quasithin.H13
