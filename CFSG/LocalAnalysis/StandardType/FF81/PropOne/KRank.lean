module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.RankFour

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private theorem ktilHom_eq_one_of_mem {G : Type} [Group G] [Finite G] {R : Subgroup G}
    {E : Subgroup G} (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    {k : ↥(ktil R)} (hk : k ∈ E.subgroupOf (ktil R)) (hker : ktilHom R k = 1) :
    k = 1 := by
  have hkC : (k : G) ∈ Subgroup.centralizer (R : Set G) := ktil_le_centralizer R k.2
  have hmemM : (⟨(k : G), hkC⟩ : ↥(Subgroup.centralizer (R : Set G))) ∈
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (R : Set G)) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change ((ktilHom R k : Ksec R) : Xq R) = 1
    rw [congrArg (fun x : Ksec R => (x : Xq R)) hker]
    rfl
  have hmem : (k : G) ∈ mcore R :=
    Subgroup.mem_map.mpr ⟨⟨(k : G), hkC⟩, hmemM, rfl⟩
  have hcard : Nat.card (mcore R) =
      Nat.card (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (R : Set G))) :=
    Subgroup.card_map_of_injective (Subgroup.centralizer (R : Set G)).subtype_injective
  have hcop : Nat.Coprime 3 (Nat.card (mcore R)) := by
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  have h3 : orderOf (k : G) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (hE3 (k : G) (show (k : G) ∈ E from hk))
  have hM : orderOf (k : G) ∣ Nat.card (mcore R) :=
    Subgroup.orderOf_dvd_natCard (mcore R) hmem
  have hone : orderOf (k : G) = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 hM
  exact Subtype.ext (orderOf_eq_one_iff.mp hone)

private theorem ktilHom_injOn {G : Type} [Group G] [Finite G] {R : Subgroup G}
    {E : Subgroup G} (hE3 : ∀ x ∈ E, x ^ 3 = 1) :
    Set.InjOn (ktilHom R)
      ((E.subgroupOf (ktil R) : Subgroup ↥(ktil R)) : Set ↥(ktil R)) := by
  intro a ha b hb hab
  have hmem : a * b⁻¹ ∈ E.subgroupOf (ktil R) := mul_mem ha (inv_mem hb)
  have hker : ktilHom R (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  exact mul_inv_eq_one.mp (ktilHom_eq_one_of_mem hE3 hmem hker)

theorem four_le_pRank_ksec {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hJ : JData n L z J) (hR : RData b z J B₂ A R) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Ksec R)) := by
  obtain ⟨E, _hE, hEab, hEcard⟩ := exists_rank_four h hJ hR
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hEab.2
  have hinj := ktilHom_injOn (R := R) hE3
  let E' : Subgroup (Ksec R) := (E.subgroupOf (ktil R)).map (ktilHom R)
  have hcoe : (E' : Set (Ksec R)) =
      ktilHom R '' ((E.subgroupOf (ktil R) : Subgroup ↥(ktil R)) : Set ↥(ktil R)) :=
    Subgroup.coe_map _ _
  have hcardE' : Nat.card E' = 3 ^ 4 := by
    calc Nat.card E' =
          Nat.card (ktilHom R '' ((E.subgroupOf (ktil R) : Subgroup ↥(ktil R)) : Set ↥(ktil R))) :=
          Nat.card_congr (Set.equivOfEq hcoe)
      _ = Nat.card ((E.subgroupOf (ktil R) : Subgroup ↥(ktil R)) : Set ↥(ktil R)) :=
          Nat.card_image_of_injOn hinj
      _ = Nat.card (E.subgroupOf (ktil R)) := rfl
      _ = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe _hE).toEquiv
      _ = 3 ^ 4 := hEcard
  have hE'comm : IsMulCommutative E' := by
    refine IsMulCommutative.of_setLike_mul_comm ?_
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hcomm : (a : G) * (b : G) = (b : G) * (a : G) :=
      congrArg Subtype.val (hEab.1.is_comm.comm
        ⟨(a : G), (show (a : G) ∈ E from ha)⟩
        ⟨(b : G), (show (b : G) ∈ E from hb)⟩)
    calc ktilHom R a * ktilHom R b = ktilHom R (a * b) := (map_mul _ _ _).symm
      _ = ktilHom R (b * a) := by rw [show a * b = b * a from Subtype.ext hcomm]
      _ = ktilHom R b * ktilHom R a := map_mul _ _ _
  have hE'exp : ∀ x ∈ E', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have ha3 : a ^ 3 = 1 := by
      apply Subtype.ext
      show ((a ^ 3 : ↥(ktil R)) : G) = 1
      simpa using hE3 (a : G) (show (a : G) ∈ E from ha)
    calc (ktilHom R a) ^ 3 = ktilHom R (a ^ 3) := by rw [map_pow]
      _ = ktilHom R 1 := by rw [ha3]
      _ = 1 := map_one _
  have hE'ab : CFSG.Open.IsElemAbelian 3 E' := ⟨hE'comm, hE'exp⟩
  let S : Set ℕ := {k | ∃ E : Subgroup (Ksec R),
    E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}
  have hbdd : BddAbove S := by
    refine ⟨Nat.card (Ksec R), ?_⟩
    rintro k ⟨F, _hF, _hFab, hFcard⟩
    have hle : 3 ^ k ≤ Nat.card (Ksec R) := by
      rw [← hFcard]
      exact Subgroup.card_le_card_group (H := F)
    exact le_trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num : 1 < 3))) hle
  have hmem : 4 ∈ S := ⟨E', le_top, hE'ab, hcardE'⟩
  change 4 ≤ sSup S
  exact le_csSup hbdd hmem

end CFSG.StandardType.FF81.PropOne

end
