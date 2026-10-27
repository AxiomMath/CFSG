module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mk_mem_normalizer {p : ℕ} [Fact p.Prime] {H P : Subgroup G}
    (hPH : P ≤ H) (hP : IsPGroup p P)
    (hPK : ⁅P, (CFSG.pPrimeCore p ↥H).map H.subtype⁆ = ⊥) {h : ↥H}
    (hh : QuotientGroup.mk' (CFSG.pPrimeCore p ↥H) h ∈ normalizer
      (((P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) :
        Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H)) : Set (↥H ⧸ CFSG.pPrimeCore p ↥H))) :
    (h : G) ∈ normalizer (P : Set G) := by
  classical
  set K₀ : Subgroup ↥H := CFSG.pPrimeCore p ↥H with hK₀
  have hcen : P ≤ centralizer ((K₀.map H.subtype : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hPK
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hN : ∀ z ∈ P, z ^ Nat.card P = 1 := fun z hz =>
    orderOf_dvd_iff_pow_eq_one.mp (P.orderOf_dvd_natCard hz)
  have key : ∀ g : ↥H, QuotientGroup.mk' K₀ g ∈ normalizer
      (((P.subgroupOf H).map (QuotientGroup.mk' K₀) : Subgroup (↥H ⧸ K₀)) : Set (↥H ⧸ K₀)) →
      ∀ x ∈ P, (g : G) * x * (g : G)⁻¹ ∈ P := by
    intro g hg x hx
    have h1 : QuotientGroup.mk' K₀ (g * ⟨x, hPH hx⟩ * g⁻¹) ∈
        (P.subgroupOf H).map (QuotientGroup.mk' K₀) := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hg _).mp ⟨⟨x, hPH hx⟩, mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨y, hyP, hy⟩ := mem_map.mp h1
    have hc : y⁻¹ * (g * ⟨x, hPH hx⟩ * g⁻¹) ∈ K₀ := QuotientGroup.eq.mp hy
    set c : ↥H := y⁻¹ * (g * ⟨x, hPH hx⟩ * g⁻¹) with hcdef
    have hyP' : (y : G) ∈ P := mem_subgroupOf.mp hyP
    have hcomm : (c : G) * y = y * c := mem_centralizer_iff.mp (hcen hyP') _ ⟨c, hc, rfl⟩
    have hz : (g : G) * x * (g : G)⁻¹ = y * c := by
      simp [hcdef, mul_assoc]
    have hcN : (c : G) ^ Nat.card P = 1 := by
      have h2 : ((g : G) * x * (g : G)⁻¹) ^ Nat.card P = 1 := by
        rw [conj_pow, hN x hx]
        simp
      rwa [hz, Commute.mul_pow hcomm.symm, hN y hyP', one_mul] at h2
    have hcop : Nat.Coprime (Nat.card P) (orderOf (c : G)) := by
      rw [hm]
      refine Nat.Coprime.pow_left m (Nat.Coprime.coprime_dvd_right ?_
        (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥H)))
      rw [orderOf_coe]
      exact K₀.orderOf_dvd_natCard hc
    have hc1 : (c : G) = 1 :=
      orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm (orderOf_dvd_of_pow_eq_one hcN))
    rw [hz, hc1, mul_one]
    exact hyP'
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => key h hh x hx, fun hx => ?_⟩
  have hh' : QuotientGroup.mk' K₀ h⁻¹ ∈ normalizer
      (((P.subgroupOf H).map (QuotientGroup.mk' K₀) : Subgroup (↥H ⧸ K₀)) : Set (↥H ⧸ K₀)) := by
    rw [map_inv]
    exact inv_mem hh
  simpa [mul_assoc] using key h⁻¹ hh' _ hx

namespace Sec7Core4

theorem isComponentOf_layerLift (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G}
    (hH : Config k H) : CFSG.Open.IsComponentOf (layerLift k.p H) H := by
  classical
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨hsimple, hnab, -, -⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI := hsimple
  set K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H with hK₀
  set L : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀) with hL
  have hJH : layerLift k.p H ≤ H := layerLift_le k.p H
  have hLq : CFSG.IsQuasisimple ↥L := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hmap : ((layerLift k.p H).subgroupOf H).map (QuotientGroup.mk' K₀) = L :=
    map_layerLift_eq k.p H (isPerfect_iff.mp hLq.1)
  let φ : ↥(layerLift k.p H) →* ↥H ⧸ K₀ := (QuotientGroup.mk' K₀).comp (inclusion hJH)
  have hrange : φ.range = L := by
    rw [MonoidHom.range_comp, inclusion_range, hmap]
  have hcen : layerLift k.p H ≤ centralizer ((K₀.map H.subtype : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (h75 H hH)
  have hker : φ.rangeRestrict.ker ≤ center ↥(layerLift k.p H) := by
    rw [MonoidHom.ker_rangeRestrict]
    intro x hx
    have hxK₀ : inclusion hJH x ∈ K₀ := by
      rw [← QuotientGroup.ker_mk' K₀]
      exact hx
    have hxK : (x : G) ∈ K₀.map H.subtype := ⟨inclusion hJH x, hxK₀, rfl⟩
    refine mem_center_iff.mpr fun y => Subtype.ext ?_
    exact (mem_centralizer_iff.mp (hcen y.2) _ hxK).symm
  have hJq : CFSG.IsQuasisimple ↥(layerLift k.p H) :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective
      (isPerfect_iff.mpr (commutator_layerLift k.p H)) φ.rangeRestrict
      φ.rangeRestrict_surjective hker).mpr (by rw [hrange]; exact hLq)
  exact ⟨hJH, CFSG.Open.IsSubnormal.step hJH
    ((normal_subgroupOf_iff_le_normalizer hJH).mpr (le_normalizer_layerLift k.p H))
    (CFSG.Open.IsSubnormal.refl H), Group.isPerfect_def.mp hJq.1, hJq.2.1⟩

theorem layerLift_le_rankThreeLayer (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G}
    (hH : Config k H) : layerLift k.p H ≤ CFSG.Open.rankThreeLayer H := by
  unfold CFSG.Open.rankThreeLayer
  exact le_sSup (k.isComponentOf_layerLift h75 hH)

theorem le_layerLift_of_isPGroup (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G}
    (hH : Config k H) {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup k.p P)
    (hPL : (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :
    P ≤ layerLift k.p H := by
  classical
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨hsimple, hnab, -, -⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI := hsimple
  set K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H with hK₀
  set J : Subgroup G := layerLift k.p H with hJ
  have hmap : (J.subgroupOf H).map (QuotientGroup.mk' K₀) = CFSG.generalizedFitting (↥H ⧸ K₀) :=
    map_layerLift_eq k.p H
      (isPerfect_iff.mp (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1)
  have hcen : J ≤ centralizer ((K₀.map H.subtype : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (h75 H hH)
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  intro x hx
  have hxL : QuotientGroup.mk' K₀ (⟨x, hPH hx⟩ : ↥H) ∈
      (J.subgroupOf H).map (QuotientGroup.mk' K₀) :=
    hmap ▸ hPL ⟨⟨x, hPH hx⟩, mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨j, hjJ, hjx⟩ := mem_map.mp hxL
  have hc : j⁻¹ * ⟨x, hPH hx⟩ ∈ K₀ := QuotientGroup.eq.mp hjx
  set c : ↥H := j⁻¹ * ⟨x, hPH hx⟩ with hcdef
  have hjJ' : (j : G) ∈ J := mem_subgroupOf.mp hjJ
  have hcomm : (c : G) * j = j * c := mem_centralizer_iff.mp (hcen hjJ') _ ⟨c, hc, rfl⟩
  have hxjc : x = (j : G) * c := by
    simp [hcdef]
  have hxN : x ^ Nat.card P = 1 := orderOf_dvd_iff_pow_eq_one.mp (P.orderOf_dvd_natCard hx)
  have hcop : Nat.Coprime (Nat.card P) (orderOf (c : G)) := by
    rw [hm]
    refine Nat.Coprime.pow_left m (Nat.Coprime.coprime_dvd_right ?_
      (CFSG.pPrimeCore_coprime_card (p := k.p) (G := ↥H)))
    rw [orderOf_coe]
    exact K₀.orderOf_dvd_natCard hc
  have hcpow : (c : G) ^ Nat.card P ∈ J := by
    have h1 : ((j : G) * c) ^ Nat.card P = (j : G) ^ Nat.card P * (c : G) ^ Nat.card P :=
      Commute.mul_pow hcomm.symm _
    rw [← hxjc, hxN] at h1
    rw [eq_inv_of_mul_eq_one_right h1.symm]
    exact J.inv_mem (J.pow_mem hjJ' _)
  obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime hcop
  have hcJ : (c : G) ∈ J := by
    rw [← he]
    exact J.pow_mem hcpow e
  rw [hxjc]
  exact J.mul_mem hjJ' hcJ

theorem commutator_pPrimeCore_eq_bot_of_isPGroup (k : Sec7Core4 G) (h75 : Step75 k)
    {H : Subgroup G} (hH : Config k H) {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup k.p P)
    (hPL : (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :
    ⁅P, (CFSG.pPrimeCore k.p ↥H).map H.subtype⁆ = ⊥ :=
  le_bot_iff.mp ((commutator_mono (k.le_layerLift_of_isPGroup h75 hH hPH hP hPL) le_rfl).trans
    (h75 H hH).le)

theorem fstar_inf_normalizer_le_map (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G}
    (hH : Config k H) {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup k.p P)
    (hPL : (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :
    CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) ⊓
        normalizer (((P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) :
          Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≤
      ((layerLift k.p H ⊓ normalizer (P : Set G)).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) := by
  classical
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨hsimple, hnab, -, -⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI := hsimple
  have hmap := map_layerLift_eq k.p H
    (isPerfect_iff.mp (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1)
  have hPK := k.commutator_pPrimeCore_eq_bot_of_isPGroup h75 hH hPH hP hPL
  rintro _ ⟨hxL, hxN⟩
  rw [← hmap] at hxL
  obtain ⟨j, hjJ, rfl⟩ := mem_map.mp hxL
  exact mem_map.mpr ⟨j, mem_subgroupOf.mpr ⟨mem_subgroupOf.mp hjJ,
    mem_normalizer_of_mk_mem_normalizer hPH hP hPK hxN⟩, rfl⟩

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
