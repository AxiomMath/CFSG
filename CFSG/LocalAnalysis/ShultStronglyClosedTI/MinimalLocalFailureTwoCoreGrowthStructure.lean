module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairActionQuotient

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

@[expose] def pointTwoCoreImage (H : Subgroup G) : Subgroup G :=
  (CFSG.pCore 2 H).map H.subtype

theorem pointTwoCoreImage_le (H : Subgroup G) : pointTwoCoreImage H ≤ H :=
  Subgroup.map_subtype_le _

theorem pointTwoCoreImage_isPGroup (H : Subgroup G) :
    IsPGroup 2 (pointTwoCoreImage H) :=
  CFSG.pCore_isPGroup.map H.subtype

theorem pointTwoCoreImage_subgroupOf (H : Subgroup G) :
    (pointTwoCoreImage H).subgroupOf H = CFSG.pCore 2 H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem pointTwoCoreImage_normal (H : Subgroup G) :
    ((pointTwoCoreImage H).subgroupOf H).Normal := by
  rw [pointTwoCoreImage_subgroupOf]
  infer_instance

theorem original_point_hull_le_two_core
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hQtwo : IsPGroup 2 (minimalLocalFailurePairActionPointHull H z)) :
    minimalLocalFailurePairActionPointHull H z ≤ pointTwoCoreImage H := by
  let Q := minimalLocalFailurePairActionPointHull H z
  have hQH : Q ≤ H := minimalLocalFailurePairActionPointHull_le_point H
    h.distinguished_mem
  have hnormal : (Q.subgroupOf H).Normal :=
    minimalLocalFailurePairActionPointHull_normal_in_point H h.distinguished_mem
  let e : Q.subgroupOf H ≃* Q := Subgroup.subgroupOfEquivOfLe hQH
  have htwo : IsPGroup 2 (Q.subgroupOf H) := hQtwo.of_injective
    e.toMonoidHom e.injective
  have hcore : Q.subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hnormal, htwo⟩
  have hmap := Subgroup.map_mono (f := H.subtype) hcore
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQH] at hmap

theorem original_point_hull_centralizes_two_core
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hcentral : InvolutionPointCentralSylow z) :
    minimalLocalFailurePairActionPointHull H z ≤
      Subgroup.centralizer (pointTwoCoreImage H : Set G) := by
  let M := pointTwoCoreImage H
  obtain ⟨S, hzS, hzcenter⟩ := hcentral
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    apply point_centralizer_le h
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzcenter (⟨s, hs⟩ : (S : Subgroup G))))
  let SH : Sylow 2 H := S.subtype hSH
  have hcoreSH : CFSG.pCore 2 H ≤ (SH : Subgroup H) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal SH
  have hMS : M ≤ (S : Subgroup G) := by
    intro m hm
    obtain ⟨mH, hmH, rfl⟩ := Subgroup.mem_map.mp hm
    exact hcoreSH hmH
  have hzM : z ∈ Subgroup.centralizer (M : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzcenter (⟨m, hMS hm⟩ : (S : Subgroup G)))
  have hnorm : H ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pointTwoCoreImage_le H)).mp
      (pointTwoCoreImage_normal H)
  apply (Subgroup.closure_le _).mpr
  rintro a ⟨k, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro m hm
  have hmconj : (k : G) * m * (k : G)⁻¹ ∈ M := by
    have hh := (Subgroup.mem_normalizer_iff''.mp
      (hnorm (H.inv_mem k.property)) m).mp hm
    simpa only [inv_inv] using hh
  have hc := Subgroup.mem_centralizer_iff.mp hzM _ hmconj
  change m * ((k : G)⁻¹ * z * k) = ((k : G)⁻¹ * z * k) * m
  calc
    _ = (k : G)⁻¹ * (((k : G) * m * (k : G)⁻¹) * z) * k := by group
    _ = (k : G)⁻¹ * (z * ((k : G) * m * (k : G)⁻¹)) * k := by rw [hc]
    _ = _ := by group

variable [Finite G]

theorem pair_intersection_eq_bot_of_involutions_in_root
    (M Q B : Subgroup G) (hMtwo : IsPGroup 2 M)
    (hinvolutions : ∀ m : G, m ∈ M → orderOf m = 2 → m ∈ Q)
    (hQB : Q ⊓ B = ⊥) : M ⊓ B = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have htwo : IsPGroup 2 (M ⊓ B : Subgroup G) := hMtwo.to_le inf_le_left
  have hdiv : 2 ∣ Nat.card (M ⊓ B : Subgroup G) :=
    htwo.card_eq_or_dvd.resolve_left (fun hcard => hne (Subgroup.card_eq_one.mp hcard))
  obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card'
    (G := (M ⊓ B : Subgroup G)) 2 hdiv
  have hmorder : orderOf (m : G) = 2 := (Subgroup.orderOf_coe m).trans hm
  have hmQ : (m : G) ∈ Q := hinvolutions m m.property.1 hmorder
  have hmone : (m : G) = 1 := by
    have hmem : (m : G) ∈ Q ⊓ B := ⟨hmQ, m.property.2⟩
    rwa [hQB, Subgroup.mem_bot] at hmem
  exact (orderOf_eq_prime_iff.mp hmorder).2 hmone

theorem point_two_core_card_dvd_pair_index
    (H B : Subgroup G) (hBH : B ≤ H)
    (hintersection : pointTwoCoreImage H ⊓ B = ⊥) :
    Nat.card (pointTwoCoreImage H) ∣ B.relIndex H := by
  let M := pointTwoCoreImage H
  let MH := M.subgroupOf H
  let BH := B.subgroupOf H
  let : MH.Normal := pointTwoCoreImage_normal H
  have hMHcard : Nat.card MH = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pointTwoCoreImage_le H)).toEquiv
  have hinf : MH ⊓ BH = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro m hm
    apply Subtype.ext
    have hh : (m : G) ∈ M ⊓ B := hm
    rwa [hintersection, Subgroup.mem_bot] at hh
  have hBHindex : BH.index = B.relIndex H := rfl
  have hMindex : MH.index * Nat.card MH = Nat.card H := MH.index_mul_card
  have hBHcard : Nat.card BH = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hBindex : BH.index * Nat.card B = Nat.card H := by
    rw [← hBHcard]
    exact BH.index_mul_card
  have hrel : MH.relIndex BH = Nat.card BH := by
    have hh := MH.relIndex_mul_card BH
    simpa only [hinf, Subgroup.card_bot, mul_one] using hh
  have hdiv : Nat.card B ∣ MH.index := by
    rw [← hBHcard, ← hrel]
    exact MH.relIndex_dvd_index_of_normal BH
  obtain ⟨k, hk⟩ := hdiv
  have hidx : BH.index = k * Nat.card MH := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := B))
    calc
      BH.index * Nat.card B = Nat.card H := hBindex
      _ = MH.index * Nat.card MH := hMindex.symm
      _ = (k * Nat.card MH) * Nat.card B := by rw [hk]; ac_rfl
  rw [← hBHindex, hidx, hMHcard]
  exact dvd_mul_left _ _

theorem point_two_core_join_pair_eq_point_of_full_order
    (H B : Subgroup G) (hBH : B ≤ H)
    (hintersection : pointTwoCoreImage H ⊓ B = ⊥)
    (hcard : Nat.card (pointTwoCoreImage H) = B.relIndex H) :
    pointTwoCoreImage H ⊔ B = H := by
  let M := pointTwoCoreImage H
  have hjoinH : M ⊔ B ≤ H := sup_le (pointTwoCoreImage_le H) hBH
  let MH := M.subgroupOf H
  let BH := B.subgroupOf H
  let : MH.Normal := pointTwoCoreImage_normal H
  have hinf : MH ⊓ BH = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro m hm
    apply Subtype.ext
    have hh : (m : G) ∈ M ⊓ B := hm
    rwa [hintersection, Subgroup.mem_bot] at hh
  have hMHcard : Nat.card MH = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pointTwoCoreImage_le H)).toEquiv
  have hrel : MH.relIndex BH = Nat.card BH := by
    have hh := MH.relIndex_mul_card BH
    simpa only [hinf, Subgroup.card_bot, mul_one] using hh
  have hprod : Nat.card (MH ⊔ BH : Subgroup H) = Nat.card MH * Nat.card BH := by
    have hh := MH.relIndex_mul_card (MH ⊔ BH)
    rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left, hrel] at hh
    exact hh.symm.trans (Nat.mul_comm _ _)
  have htop : MH ⊔ BH = (⊤ : Subgroup H) := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    rw [hprod, hMHcard, hcard]
    exact BH.index_mul_card
  have hmap := congrArg (fun L : Subgroup H => L.map H.subtype) htop
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (pointTwoCoreImage_le H),
    inf_eq_left.mpr hBH, Subgroup.map_top, Subgroup.range_subtype] at hmap
  exact hmap

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
