module

public import CFSG.Quasithin.Background.RonanE114SevenL35Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main

public section

namespace CFSG.Quasithin.RonanE114.Seven.L35

open scoped MatrixGroups
open CFSG.Quasithin CFSG.Quasithin.A1b

theorem isSolvable_normalizer_map_of_range_normal {Γ G : Type*} [Group Γ] [Group G] [Finite G]
    {L : Subgroup G} [L.Normal] (hq : IsPGroup 2 (G ⧸ L)) (f : Γ →* G)
    (hf : Function.Injective f) (hrange : f.range = L) {K : Subgroup Γ}
    (hK : Group.IsSolvable ↥(Subgroup.normalizer (K : Set Γ))) :
    Group.IsSolvable ↥(Subgroup.normalizer ((K.map f : Subgroup G) : Set G)) := by
  set N := Subgroup.normalizer ((K.map f : Subgroup G) : Set G) with hN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent (G ⧸ L) := hq.isNilpotent
  have hmemN : ∀ g : Γ, g ∈ Subgroup.normalizer (K : Set Γ) → f g ∈ N := fun g hg =>
    Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem _ hg)
  let φ : ↥(Subgroup.normalizer (K : Set Γ)) →* ↥N :=
    (f.comp (Subgroup.normalizer (K : Set Γ)).subtype).codRestrict N (fun g => hmemN g.1 g.2)
  refine Group.isSolvable_of_ker_le_range φ ((QuotientGroup.mk' L).comp N.subtype) ?_
  intro n hn
  have hnL : (n : G) ∈ L := (QuotientGroup.eq_one_iff _).mp hn
  rw [← hrange] at hnL
  obtain ⟨γ, hγ⟩ := hnL
  refine ⟨⟨γ, ?_⟩, Subtype.ext hγ⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hy := Subgroup.mem_normalizer_iff.mp n.2 (f y)
  have hmap : ∀ u : Γ, u ∈ K ↔ f u ∈ K.map f := fun u => (Subgroup.mem_map_iff_mem hf).symm
  rw [hmap, hmap, map_mul, map_mul, map_inv, hγ]
  exact hy

theorem mem_normalizer_inf_of_mem {G : Type*} [Group G] {T L : Subgroup G} (hLn : L.Normal) {t : G}
    (ht : t ∈ T) : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyT, hyL⟩
    exact ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht), hLn.conj_mem y hyL t⟩
  · rintro ⟨hyT, hyL⟩
    refine ⟨?_, ?_⟩
    · have := T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) ht
      simpa [mul_assoc] using this
    · have := hLn.conj_mem _ hyL t⁻¹
      simpa [mul_assoc] using this

theorem exists_equiv_conj35 {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    (hSyl : IsSylowIn 2 (T ⊓ L) L) (hP : IsPSL 3 5 1 ↥L) :
    ∃ E : ↥L ≃* SL(3, ZMod 5), ((T ⊓ L).subgroupOf L).map E.toMonoidHom = S35 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := E2P.Asc80.exists_equiv_psl3 (p := 5) hP
  let φ₀ : ↥L ≃* SL(3, ZMod 5) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_SL35).trans QuotientGroup.quotientBot)
  set PL : Sylow 2 ↥L := hSyl.toSylow with hPL
  let PK : Sylow 2 SL(3, ZMod 5) := PL.mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq SL(3, ZMod 5) PK sylowS35
  refine ⟨φ₀.trans (MulAut.conj k), ?_⟩
  have h1 : ((T ⊓ L).subgroupOf L).map φ₀.toMonoidHom = (PK : Subgroup SL(3, ZMod 5)) :=
    (Sylow.coe_mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective PL).symm
  have h2 : ((k • PK : Sylow 2 SL(3, ZMod 5)) : Subgroup SL(3, ZMod 5)) =
      (PK : Subgroup SL(3, ZMod 5)).map (MulAut.conj k).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hk] at h2
  calc ((T ⊓ L).subgroupOf L).map (φ₀.trans (MulAut.conj k)).toMonoidHom
      = (((T ⊓ L).subgroupOf L).map φ₀.toMonoidHom).map (MulAut.conj k).toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
    _ = (PK : Subgroup SL(3, ZMod 5)).map (MulAut.conj k).toMonoidHom := by rw [h1]
    _ = (sylowS35 : Subgroup SL(3, ZMod 5)) := h2.symm
    _ = S35 := rfl

end CFSG.Quasithin.RonanE114.Seven.L35
