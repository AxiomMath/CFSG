module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

namespace U5M

variable {G : Type*} [Group G]

@[expose] noncomputable def tc (L : Subgroup G) : Subgroup G := (CFSG.pCore 2 ↥L).map L.subtype

theorem tc_le (L : Subgroup G) : tc L ≤ L := Subgroup.map_subtype_le _

theorem tc_isPGroup [Finite G] (L : Subgroup G) : IsPGroup 2 ↥(tc L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype

theorem tc_normal (L : Subgroup G) : ∀ y ∈ L, ∀ x ∈ tc L, y * x * y⁻¹ ∈ tc L := by
  rintro y hy _ ⟨x, hx, rfl⟩
  exact ⟨⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥L)).conj_mem x hx ⟨y, hy⟩, rfl⟩

theorem le_tc {L T : Subgroup G} (hTL : T ≤ L) (hT2 : IsPGroup 2 ↥T)
    (hTn : ∀ y ∈ L, ∀ t ∈ T, y * t * y⁻¹ ∈ T) : T ≤ tc L := by
  intro t ht
  refine ⟨⟨t, hTL ht⟩, ?_, rfl⟩
  have hn : (T.subgroupOf L).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hTn g g.2 x hx⟩
  have hp : IsPGroup 2 ↥(T.subgroupOf L) := hT2.comap_subtype
  have hle : T.subgroupOf L ≤ CFSG.pCore 2 ↥L :=
    le_sSup (s := {K : Subgroup ↥L | K.Normal ∧ IsPGroup 2 ↥K}) ⟨hn, hp⟩
  exact hle (Subgroup.mem_subgroupOf.2 ht)

theorem map_tc_le [Finite G] (L : Subgroup G) (c : G ≃* G) (hc : ∀ x, c x ∈ L ↔ x ∈ L) :
    ∀ t ∈ tc L, c t ∈ tc L := by
  intro t ht
  have hT : (tc L).map c.toMonoidHom ≤ tc L := by
    refine le_tc ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (hc x).2 (tc_le L hx)
    · exact (tc_isPGroup L).map c.toMonoidHom
    · rintro y hy _ ⟨x, hx, rfl⟩
      have hy' : c.symm y ∈ L := (hc _).1 (by simpa using hy)
      refine ⟨c.symm y * x * (c.symm y)⁻¹, tc_normal L _ hy' x hx, ?_⟩
      simp
  exact hT ⟨t, ht, rfl⟩

theorem tc_ne_bot_of_nilpotent [Finite G] (L : Subgroup G) (hnil : Group.IsNilpotent ↥L)
    (heven : 2 ∣ Nat.card ↥L) : tc L ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 heven
  have hz : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨P, hP⟩ := hz.exists_le_sylow
  have hPn : (P : Subgroup ↥L).Normal := Group.IsNilpotent.sylow_normal hnil 2 P
  have hPle : (P : Subgroup ↥L) ≤ CFSG.pCore 2 ↥L :=
    le_sSup (s := {K : Subgroup ↥L | K.Normal ∧ IsPGroup 2 ↥K}) ⟨hPn, P.isPGroup'⟩
  have htP : t ∈ CFSG.pCore 2 ↥L := hPle (hP (Subgroup.mem_zpowers t))
  intro h
  have h1 : (t : G) ∈ tc L := ⟨t, htP, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  have h2 : t = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at ht
  omega

end U5M

end Sec1511

end CFSG.RankThree.PartOne
