module

public import CFSG.Monster.GMS.Orbits
import CFSG.Monster.GMS.F1Basic
import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

section Sylow

private theorem exists_isConj_mem_center_sylow [Finite G] {z₀ : G} (hz₀ : GMSLeechCentralizer z₀)
    (P : Sylow 2 G) (hP : Nontrivial (P : Subgroup G)) :
    ∃ t : G, IsConj z₀ t ∧ orderOf t = 2 ∧ t ∈ (P : Subgroup G) ∧
      ∀ x ∈ (P : Subgroup G), x * t = t * x := by
  have : Nontrivial (Subgroup.center (P : Subgroup G)) := P.isPGroup'.center_nontrivial
  have hCp : IsPGroup 2 (Subgroup.center (P : Subgroup G)) := P.isPGroup'.to_subgroup _
  have h2 : 2 ∣ Nat.card (Subgroup.center (P : Subgroup G)) := by
    rcases hCp.card_eq_or_dvd with h | h
    · exact absurd (Nat.card_eq_one_iff_unique.mp h).1 (not_subsingleton _)
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hw' : orderOf ((w : (P : Subgroup G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  refine ⟨((w : (P : Subgroup G)) : G), ?_, hw', (w : (P : Subgroup G)).2, fun x hx => ?_⟩
  · exact isConj_of_mem_center_sylow hz₀.1 hz₀.2.1 hz₀.2.2.2.2 P hw'
      (Subgroup.mem_map.mpr ⟨w, w.2, rfl⟩)
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨x, hx⟩)

end Sylow

private theorem exists_tableV_isConj [Finite G] {d₀ : B} {a z₀ b z u : G}
    (hG : GMSF1Type d₀ a z₀) (hTV : TableV a b z u) :
    ∃ z' : G, TableV a b z' u ∧ IsConj z₀ z' := by
  have ha2 : orderOf a = 2 := hG.1.1
  have hcard := hTV.card_centralizer
  have hcz := hTV.card_z
  have hcen : ∀ T : Subgroup G,
      T ≤ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {z} →
        Nat.card T = 2 ^ 42 → ∀ x : G,
          (x ∈ T ∧ ∀ s ∈ T, x * s = s * x) ↔ (x = 1 ∨ x = a ∨ x = z ∨ x = a * z) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := hTV
    exact h
  set K : Subgroup G := Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {z}
  have h42 : 2 ^ 42 ∣ Nat.card K := by rw [hcz]; norm_num [tableVOrderZ]
  obtain ⟨T₀, hT₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 h42
  set T : Subgroup G := T₀.map K.subtype with hT
  have hTcard : Nat.card T = 2 ^ 42 := by
    rw [hT, Subgroup.card_map_of_injective K.subtype_injective]
    exact hT₀
  have hTK : T ≤ K := Subgroup.map_subtype_le T₀
  obtain ⟨P, hTP⟩ := (IsPGroup.of_card hTcard : IsPGroup 2 T).exists_le_sylow
  have haT : a ∈ T ∧ ∀ s ∈ T, a * s = s * a :=
    (hcen T hTK hTcard a).mpr (Or.inr (Or.inl rfl))
  have hPnt : Nontrivial (P : Subgroup G) :=
    ⟨⟨⟨a, hTP haT.1⟩, 1, fun h => ne_one_of_orderOf ha2 (congrArg Subtype.val h)⟩⟩
  obtain ⟨t, htconj, ht2, htP, htc⟩ := exists_isConj_mem_center_sylow hG.2 P hPnt
  have htCa : t ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (htc a (hTP haT.1)).symm
  have htT : t ∈ T := by
    set T' : Subgroup G := T ⊔ Subgroup.zpowers t
    have hT'P : T' ≤ P := sup_le hTP (Subgroup.zpowers_le.mpr htP)
    have hT'C : T' ≤ Subgroup.centralizer ({a} : Set G) :=
      sup_le (hTK.trans inf_le_left) (Subgroup.zpowers_le.mpr htCa)
    obtain ⟨k, hk⟩ := (P.isPGroup'.to_le hT'P).exists_card_eq
    have hdvd : 2 ^ k ∣ twoBabyOrder := by
      rw [← hk, ← hcard]
      exact Subgroup.card_dvd_of_le hT'C
    have hk42 : k ≤ 42 := by
      by_contra hlt
      have : 2 ^ 43 ∣ twoBabyOrder := (pow_dvd_pow 2 (not_le.mp hlt)).trans hdvd
      norm_num [twoBabyOrder] at this
    have hge : Nat.card T' ≤ Nat.card T := by
      rw [hk, hTcard]
      exact Nat.pow_le_pow_right (by norm_num) hk42
    have hTT' : T = T' := Subgroup.eq_of_le_of_card_ge le_sup_left hge
    rw [hTT']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hcases := (hcen T hTK hTcard t).mp ⟨htT, fun s hs => (htc s (hTP hs)).symm⟩
  rcases hcases with h1 | h1 | h1 | h1
  · exact absurd h1 (ne_one_of_orderOf ht2)
  · exact absurd (h1 ▸ htconj).symm hG.not_isConj
  · exact ⟨z, hTV, h1 ▸ htconj⟩
  · exact ⟨a * z, hTV.swap ha2, h1 ▸ htconj⟩

theorem s31_two
    {G : Type} [Group G] [Finite G] {d₀ : B} (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) :
    ∃ b z u : G, TableV a b z u ∧
      IsConj a b ∧ IsConj a (a * b) ∧
      IsConj z₀ z ∧ IsConj a (a * z) ∧ a ∈ leechQ z ∧
      IsConj z₀ u ∧ IsConj z₀ (a * u) ∧ a ∉ leechQ u ∧
      Nat.card ↥(leechQ u ⊓ Subgroup.centralizer {a}) = 2 ^ 17 := by
  have ha2 : orderOf a = 2 := hG.1.1
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf ha2
  have ha1 : a ≠ 1 := ne_one_of_orderOf ha2
  obtain ⟨b, z, u, hTV₀⟩ := hTV a (hG.1.isTwoBabyCentralizer hSLS)
  obtain ⟨z, hTVz, hz₀z⟩ := exists_tableV_isConj hG hTV₀
  have hnc : ¬ IsConj a z := fun h => hG.not_isConj (h.trans hz₀z.symm)
  have hz2 : orderOf z = 2 := hTVz.orderOf_z
  have hz1 : z ≠ 1 := ne_one_of_orderOf hz2
  have haz : a ≠ z := fun h => hTVz.ne_z h.symm
  have hGz : GMSLeechCentralizer z := hG.2.of_isConj hz₀z
  have hcz : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ 46 * 1982582476875 :=
    hGz.card_centralizer
  have hLz : LeechData z := hL G z hGz
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
      hTVz.mem_z).symm
  have hcard_z : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {a}) =
      tableVOrderZ := by
    rw [inf_comm]
    exact hTVz.card_z
  have haQ : a ∈ leechQ z := mem_leechQ_of_card hLz ha2 haC hcard_z
  have hacz : IsConj a (a * z) := hLz.isConj_mul hz1 haQ ha1 haz haa
  obtain ⟨T₂, T₃, T₄, hT⟩ := hLz.exists_orbits
  have haT : a ∈ T₂ := hT.mem_two hcz hz1 haQ ha1 haz haa hcard_z
  obtain ⟨hab, habb⟩ := hT.isConj_b hTVz ha2 hnc haT
  have hT₄ : ∀ q ∈ T₄, IsConj z q := hT.isConj_of_mem_four hTVz ha2 hcz haT hacz
  obtain ⟨hzu, hzau⟩ := hT.isConj_u hTVz ha2 hnc haT hacz hab hT₄
  have hz₀u : IsConj z₀ u := hz₀z.trans hzu
  have hz₀au : IsConj z₀ (a * u) := hz₀z.trans hzau
  have hu2 : orderOf u = 2 := hTVz.orderOf_u
  have hGu : GMSLeechCentralizer u := hG.2.of_isConj hz₀u
  have hLu : LeechData u := hL G u hGu
  have hauQ : a ∉ leechQ u := fun hQ =>
    hG.not_isConj ((hLu.isConj_mul (ne_one_of_orderOf hu2) hQ ha1 (hTVz.ne_u).symm haa).trans
      hz₀au.symm)
  have haCu : a ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
      hTVz.mem_u).symm
  have h35 : Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer {a}) =
      2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
    rw [inf_comm, hTVz.card_u]
    rfl
  exact ⟨b, z, u, hTVz, hab, habb, hz₀z, hacz, haQ, hz₀u, hz₀au, hauQ,
    hLu.card_eq a haCu ha2 hauQ h35⟩

end CFSG.Monster.GMS
