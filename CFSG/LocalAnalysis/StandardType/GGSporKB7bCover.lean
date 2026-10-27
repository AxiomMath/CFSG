module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalCover

public section

open scoped commutatorElement

namespace CFSG.StandardType.SporadicShape

private theorem gk7b_card_dvd_four_comm {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ∣ 4) : IsMulCommutative H := by
  have h4 : Nat.card H ∣ 2 ^ 2 := by simpa using h
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
  interval_cases k
  · have h1 : Nat.card H = 1 := by simpa using hk'
    haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.1 h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · haveI : Fact (Nat.Prime (Nat.card H)) :=
      ⟨by rw [show Nat.card H = 2 by simpa using hk']; exact Nat.prime_two⟩
    haveI : IsCyclic H := isCyclic_of_prime_card (p := Nat.card H) rfl
    infer_instance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hk')

theorem gk7b_card_centralizer_dvd_of_cover {Y R : Type*} [Group Y] [Finite Y] [Group R]
    {Z Y' : Subgroup Y} [(Z.subgroupOf Y').Normal] (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (hZ2 : Nat.card Z = 2) (φ : Y' ⧸ Z.subgroupOf Y' ≃* R)
    (hR : ∀ P : Subgroup R, Nat.card P = 49 →
      Nat.card ↥(Subgroup.centralizer (P : Set R)) = 49)
    {E : Subgroup Y} (hE : Nat.card E = 49) :
    Nat.card ↥(Subgroup.centralizer (E : Set Y)) ∣ 196 := by
  have hEodd : Odd (Nat.card E) := by rw [hE]; decide
  have hEY' : E ≤ Y' := fun e he =>
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.mem_of_index_two_of_odd hY'
      (Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E he))
  let q : Y' →* R := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf Y'))
  have hker : ∀ g : Y', q g = 1 ↔ (g : Y) ∈ Z := by
    intro g
    show φ (QuotientGroup.mk' _ g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hinjE : Set.InjOn q (E.subgroupOf Y' : Set Y') := by
    intro x hx y hy hxy
    have h1 : q (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hZx : ((x * y⁻¹ : Y') : Y) ∈ Z := (hker _).1 h1
    have hEx : ((x * y⁻¹ : Y') : Y) ∈ E := by
      have hmem : x * y⁻¹ ∈ E.subgroupOf Y' :=
        mul_mem (Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 hx))
          (inv_mem (Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 hy)))
      exact Subgroup.mem_subgroupOf.1 hmem
    have h2 : orderOf ((x * y⁻¹ : Y') : Y) ∣ 2 :=
      hZ2 ▸ Subgroup.orderOf_dvd_natCard Z hZx
    have h49 : orderOf ((x * y⁻¹ : Y') : Y) ∣ 49 :=
      hE ▸ Subgroup.orderOf_dvd_natCard E hEx
    have hg1 : ((x * y⁻¹ : Y') : Y) = 1 :=
      orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h49)
    exact mul_inv_eq_one.1 (Subtype.ext hg1)
  let P : Subgroup R := (E.subgroupOf Y').map q
  have hP : Nat.card P = 49 := by
    have e1 : Nat.card P = Nat.card (q '' (E.subgroupOf Y' : Set Y')) := by
      change Nat.card ↥((E.subgroupOf Y').map q) =
        Nat.card (q '' (E.subgroupOf Y' : Set Y'))
      rw [← Subgroup.coe_map]
      rfl
    rw [e1, Nat.card_image_of_injOn hinjE]
    rw [← hE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY').toEquiv
  let C : Subgroup Y := Subgroup.centralizer (E : Set Y)
  let C' : Subgroup Y' := C.subgroupOf Y'
  have hC'map_le : C'.map q ≤ Subgroup.centralizer (P : Set R) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rcases Subgroup.mem_map.1 hp with ⟨e, he, rfl⟩
    have hex : e * x = x * e := by
      refine Subtype.ext ?_
      have hxC : (x : Y) ∈ C := Subgroup.mem_subgroupOf.1 hx
      have heE : (e : Y) ∈ E := Subgroup.mem_subgroupOf.1 he
      exact Subgroup.mem_centralizer_iff.1 hxC (e : Y) heE
    rw [← map_mul, ← map_mul, hex]
  have hC'map_dvd : Nat.card (C'.map q) ∣ 49 := by
    have h := Subgroup.card_dvd_of_le hC'map_le
    rwa [hR P hP] at h
  have hqker : Nat.card q.ker = 2 := by
    have hqker_eq : q.ker = Z.subgroupOf Y' := by
      ext g
      exact hker g
    rw [hqker_eq, ← hZ2]
    have hsub := Subgroup.card_subtype Y' (Z.subgroupOf Y')
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZY'] at hsub
    exact hsub.symm
  let f : C' →* R := q.comp C'.subtype
  have hfker : f.ker = q.ker.subgroupOf C' := by
    change (q.comp C'.subtype).ker = q.ker.subgroupOf C'
    rw [← MonoidHom.comap_ker, Subgroup.comap_subtype]
  have hfker_dvd : Nat.card f.ker ∣ 2 := by
    rw [hfker]
    have hle : (q.ker.subgroupOf C').map C'.subtype ≤ q.ker := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    have h := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_subtype, hqker] at h
    exact h
  have hfrange : f.range = C'.map q := by
    change (q.comp C'.subtype).range = C'.map q
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hC'card : Nat.card C' ∣ 98 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfrange] at h
    rw [← h]
    simpa using Nat.mul_dvd_mul hfker_dvd hC'map_dvd
  have hrel : Y'.relIndex C ∣ 2 := by
    haveI : Y'.Normal := Subgroup.normal_of_index_eq_two hY'
    have h := Subgroup.relIndex_dvd_index_of_normal Y' C
    rwa [hY'] at h
  have hCcard : Nat.card C = Y'.relIndex C * Nat.card C' := by
    have h := Subgroup.relIndex_mul_card Y' C
    rw [inf_comm] at h
    have hcard : Nat.card ↥(C ⊓ Y') = Nat.card C' := by
      have hsub := Subgroup.card_subtype Y' C'
      rw [show C' = C.subgroupOf Y' from rfl, Subgroup.subgroupOf_map_subtype] at hsub
      exact hsub
    rw [hcard] at h
    exact h.symm
  change Nat.card C ∣ 196
  rw [hCcard]
  exact (Nat.mul_dvd_mul hrel hC'card).trans (by norm_num)

theorem gk7b_mul_comm_of_le_center {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : E ≤ Subgroup.center G) (hodd : Odd (Nat.card E)) (h4 : E.index ∣ 4) (a b : G) :
    a * b = b * a := by
  haveI : E.Normal := Subgroup.normal_of_le_center hE
  have hquot : IsMulCommutative (G ⧸ E) :=
    gk7b_card_dvd_four_comm (H := G ⧸ E) (by rw [← Subgroup.index_eq_card]; exact h4)
  have hcE : ⁅a, b⁆ ∈ E :=
    QuotientGroup.commute_mk_iff.mp (hquot.is_comm.comm (QuotientGroup.mk a) (QuotientGroup.mk b))
  have hcZ : ⁅a, b⁆ ∈ Subgroup.center G := hE hcE
  have hac : Commute a ⁅a, b⁆ := Subgroup.mem_center_iff.1 hcZ a
  have hpow : ⁅a, b⁆ ^ E.index = ⁅a ^ E.index, b⁆ :=
    Commute.commutatorElement_pow_left hac E.index
  have hker : ⁅a ^ E.index, b⁆ = 1 := by
    refine commutatorElement_eq_one_iff_mul_comm.2 ?_
    exact (Subgroup.mem_center_iff.1 (hE (Subgroup.pow_index_mem E a)) b).symm
  have hcop : (Nat.card E).Coprime E.index :=
    Nat.Coprime.of_dvd (dvd_refl _) h4 (by
      have h2 : (Nat.card E).Coprime 2 := hodd.coprime_two_right
      simpa using h2.pow_right 2)
  have h1 : orderOf ⁅a, b⁆ ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E hcE
  have h2 : orderOf ⁅a, b⁆ ∣ E.index := orderOf_dvd_of_pow_eq_one (by rw [hpow, hker])
  have hone : orderOf ⁅a, b⁆ = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact commutatorElement_eq_one_iff_mul_comm.1 (orderOf_eq_one_iff.1 hone)

end CFSG.StandardType.SporadicShape
