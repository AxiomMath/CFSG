module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR1UB
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open Equiv Equiv.Perm Subgroup

section CA

variable {G : Type} [Group G] [Finite G] (L : Subgroup G)

@[expose] def u1N : Subgroup G := Subgroup.normalizer (L : Set G)

theorem le_u1N : L ≤ u1N L := Subgroup.le_normalizer

theorem u1ca_oddCore_characteristic (X : Type) [Group X] [Finite X] :
    (CFSG.oddCore X).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro σ
  have hN : ((CFSG.oddCore X).map σ.toMonoidHom).Normal :=
    (inferInstance : (CFSG.oddCore X).Normal).map _ σ.surjective
  have hodd : Odd (Nat.card ((CFSG.oddCore X).map σ.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective]
    exact CFSG.ABGDGroups.odd_card_oddCore X
  exact le_sSup ⟨hN, hodd⟩

theorem u1ca_conj_oddCore {x : L} (n : u1N L) (hx : x ∈ CFSG.oddCore L) :
    (n : G) * (x : G) * (n : G)⁻¹ ∈ (CFSG.oddCore L).map L.subtype := by
  have hchar := u1ca_oddCore_characteristic ↥L
  have hx' : x ∈ (CFSG.oddCore L).comap (Subgroup.normalizerMonoidHom L n).toMonoidHom := by
    rw [hchar.fixed]
    exact hx
  have hσ : (Subgroup.normalizerMonoidHom L n) x ∈ CFSG.oddCore L := hx'
  have hval : (((Subgroup.normalizerMonoidHom L n) x : L) : G) = (n : G) * (x : G) * (n : G)⁻¹ :=
    rfl
  rw [← hval]
  exact Subgroup.mem_map.mpr ⟨_, hσ, rfl⟩

@[expose] noncomputable def u1R : Subgroup (u1N L) :=
  ((CFSG.oddCore L).map L.subtype).subgroupOf (u1N L)

instance u1R_normal : (u1R L).Normal := by
  refine ⟨fun r hr n => ?_⟩
  have hr' : (r : G) ∈ (CFSG.oddCore L).map L.subtype := Subgroup.mem_subgroupOf.mp hr
  obtain ⟨x, hx, hxr⟩ := Subgroup.mem_map.mp hr'
  have hrx : (r : G) = (x : G) := hxr.symm
  refine Subgroup.mem_subgroupOf.mpr ?_
  show (n : G) * (r : G) * (n : G)⁻¹ ∈ (CFSG.oddCore L).map L.subtype
  rw [hrx]
  exact u1ca_conj_oddCore L n hx

theorem u1R_odd : Odd (Nat.card (u1R L)) := by
  have hle : (CFSG.oddCore L).map L.subtype ≤ u1N L :=
    (Subgroup.map_subtype_le (CFSG.oddCore L)).trans (le_u1N L)
  have h1 : Nat.card (u1R L) = Nat.card ((CFSG.oddCore L).map L.subtype) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h2 : Nat.card ((CFSG.oddCore L).map L.subtype) = Nat.card (CFSG.oddCore L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  rw [h1, h2]
  exact CFSG.ABGDGroups.odd_card_oddCore L

abbrev u1M : Type := ↥(u1N L) ⧸ u1R L

@[expose] noncomputable def u1ψ : L →* u1M L :=
  (QuotientGroup.mk' (u1R L)).comp (Subgroup.inclusion (le_u1N L))

theorem u1ψ_apply (x : L) : u1ψ L x = ((⟨(x : G), le_u1N L x.2⟩ : u1N L) : u1M L) := rfl

theorem u1ψ_ker : (u1ψ L).ker = CFSG.oddCore L := by
  ext x
  rw [MonoidHom.mem_ker, u1ψ_apply, QuotientGroup.eq_one_iff]
  change (x : G) ∈ (CFSG.oddCore L).map L.subtype ↔ x ∈ CFSG.oddCore L
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    have hxy : y = x := Subtype.ext hyx
    rw [hxy] at hy
    exact hy
  · intro h
    exact Subgroup.mem_map.mpr ⟨x, h, rfl⟩

@[expose] noncomputable def u1J : Subgroup (u1M L) := (u1ψ L).range

instance u1J_normal : (u1J L).Normal := by
  refine ⟨fun j hj m => ?_⟩
  obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hj
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective m
  refine MonoidHom.mem_range.mpr ⟨⟨(n : G) * (l : G) * (n : G)⁻¹, ?_⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp n.2 (l : G)).mp l.2
  · rw [u1ψ_apply, u1ψ_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul] <;> rfl

@[expose] noncomputable def u1ΛJ : (L ⧸ CFSG.oddCore L) ≃* u1J L :=
  (QuotientGroup.quotientMulEquivOfEq (u1ψ_ker L).symm).trans
    (QuotientGroup.quotientKerEquivRange (u1ψ L))

theorem u1J_perfect (hperf : Group.IsPerfect (L ⧸ CFSG.oddCore L)) : Group.IsPerfect (u1J L) :=
  Group.IsPerfect.ofSurjective (f := (u1ΛJ L).toMonoidHom) (u1ΛJ L).surjective

theorem u1J_card_center (hcenter : Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 2) :
    Nat.card (Subgroup.center (u1J L)) = 2 := by
  have hmap : (Subgroup.center (L ⧸ CFSG.oddCore L)).map (u1ΛJ L).toMonoidHom =
      Subgroup.center (u1J L) :=
    Subgroup.map_center_eq (u1ΛJ L)
  rw [← hmap, Subgroup.card_map_of_injective (f := (u1ΛJ L).toMonoidHom) (u1ΛJ L).injective,
    hcenter]

@[expose] noncomputable def u1Je
    (e : (L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L) ≃*
      alternatingGroup (Fin 7)) :
    u1J L ⧸ Subgroup.center (u1J L) ≃* alternatingGroup (Fin 7) :=
  (QuotientGroup.congr (Subgroup.center (L ⧸ CFSG.oddCore L)) (Subgroup.center (u1J L))
    (u1ΛJ L) (Subgroup.map_center_eq (u1ΛJ L))).symm.trans e

end CA

theorem u1cb1_c_mem {G : Type} [Group G] {L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) :
    c ∈ Subgroup.normalizer (L : Set G) := by
  have hcomm : ∀ l ∈ L, c * l * c⁻¹ = l := by
    intro l hl
    have h1 : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hcomm h hh]
    exact hh
  · intro hh
    have h3 : c * (c * h * c⁻¹) * c⁻¹ = c * h * c⁻¹ := hcomm _ hh
    have h4 : c * (c * h * c⁻¹) = (c * h * c⁻¹) * c := mul_inv_eq_iff_eq_mul.mp h3
    have h5 : h = c * h * c⁻¹ := by
      calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
        _ = c⁻¹ * ((c * h * c⁻¹) * c) := by rw [mul_assoc]
        _ = c⁻¹ * (c * (c * h * c⁻¹)) := by rw [h4]
        _ = c * h * c⁻¹ := by group
    rw [h5]
    exact hh

theorem u1cb1_exists_inv {J : Type} [Group J] [Finite J] (Z : Subgroup J)
    (hZ : Nat.card Z = 2) : ∃ q : J, q ∈ Z ∧ q * q = 1 ∧ q ≠ 1 := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 2 (by simp [hZ])
  have hw2 : w * w = 1 := by
    rw [← pow_two, ← hw]
    exact pow_orderOf_eq_one w
  refine ⟨w.1, w.2, ?_, ?_⟩
  · have h := congrArg Subtype.val hw2
    simpa using h
  · intro h
    have hw1 : w = 1 := Subtype.ext h
    rw [hw1, orderOf_one] at hw
    norm_num at hw

theorem u1c_zu {G : Type} [Group G] [Finite G] {L : Subgroup G} {c t : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hc3 : orderOf c = 3) (hcL : c ∉ L)
    (htN : t ∈ Subgroup.normalizer (L : Set G))
    (htc : t * c * t⁻¹ = c⁻¹)
    (hperf : Group.IsPerfect (L ⧸ CFSG.oddCore L))
    (hcenter : Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 2)
    (e : (L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L) ≃*
      alternatingGroup (Fin 7)) :
    ∃ z' : L, z' * z' = 1 ∧ z' ≠ 1 ∧ (∀ x : L, x * z' * x⁻¹ * z'⁻¹ ∈ CFSG.oddCore L) ∧
      ∃ u' : G, u' * u' = 1 ∧ u' ≠ 1 ∧ u' ≠ (z' : G) ∧ u' * (z' : G) = (z' : G) * u' ∧
        u' ∈ Subgroup.normalizer (L : Set G) := by
  have hcN : c ∈ u1N L := u1cb1_c_mem hLc
  obtain ⟨tN, htN_eq⟩ : ∃ tN : u1N L, (tN : G) = t := ⟨⟨t, htN⟩, rfl⟩
  obtain ⟨cN, hcN_eq⟩ : ∃ cN : u1N L, (cN : G) = c := ⟨⟨c, hcN⟩, rfl⟩
  obtain ⟨piQ, hpiQ⟩ : ∃ piQ : u1N L →* u1M L, piQ = QuotientGroup.mk' (u1R L) := ⟨_, rfl⟩
  have hpix : ∀ x : u1N L, piQ x = QuotientGroup.mk x := fun x => by
    subst hpiQ
    rfl
  have hψπ : ∀ x : L, u1ψ L x = piQ ⟨(x : G), le_u1N L x.2⟩ := fun x =>
    (u1ψ_apply L x).trans (hpix _).symm
  obtain ⟨th, hth⟩ : ∃ th : u1M L, th = piQ tN := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ ch : u1M L, ch = piQ cN := ⟨_, rfl⟩
  have hchJ : ch ∈ Subgroup.centralizer ((u1J L : Subgroup (u1M L)) : Set (u1M L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hj' : j ∈ (u1ψ L).range := hj
    obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hj'
    have hlc : (l : G) * c = c * (l : G) := Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)
    rw [hψπ, hch, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (l : G) * (cN : G) = (cN : G) * (l : G)
    rw [hcN_eq]
    exact hlc
  have hch2 : ch * ch ≠ 1 := by
    intro h
    rw [hch, ← map_mul, hpix] at h
    have hcc_mem : cN * cN ∈ u1R L := (QuotientGroup.eq_one_iff _).mp h
    have hr2 : ((cN * cN : u1N L) : G) ∈ (CFSG.oddCore L).map L.subtype :=
      Subgroup.mem_subgroupOf.mp hcc_mem
    obtain ⟨r, _, hr_eq⟩ := Subgroup.mem_map.mp hr2
    have hrc : (r : G) = c * c := by
      have h1 : (r : G) = ((cN * cN : u1N L) : G) := hr_eq
      rw [h1, Subgroup.coe_mul, hcN_eq]
    have hcc : c * c ∈ L := by
      rw [← hrc]
      exact r.2
    have hc3' : c ^ 3 = 1 := by
      have h3 := pow_orderOf_eq_one c
      rwa [hc3] at h3
    have h4 : c * c * (c * c) = c := by
      calc c * c * (c * c) = c ^ 4 := by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = c ^ 3 * c := by
            rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ]
        _ = c := by rw [hc3', one_mul]
    apply hcL
    rw [← h4]
    exact L.mul_mem hcc hcc
  have htch : th * ch * th⁻¹ = ch⁻¹ := by
    have key : tN * cN * tN⁻¹ = cN⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, htN_eq, hcN_eq]
      exact htc)
    have key' := congrArg piQ key
    simp only [map_mul, map_inv] at key'
    rw [hth, hch]
    exact key'
  obtain ⟨ub, hub2, hubZ⟩ := u1_main (u1J L) (u1J_perfect L hperf)
    (u1J_card_center L hcenter) (u1Je L e) hchJ hch2 htch
  obtain ⟨q, hqZ, hq2, hq1⟩ :=
    u1cb1_exists_inv (Subgroup.center (u1J L)) (u1J_card_center L hcenter)
  have hqc : ∀ m : u1M L, m * (q : u1M L) = (q : u1M L) * m := fun m =>
    u1_center_central (u1J L) (u1J_card_center L hcenter) hqZ m
  have hq2' : (q : u1M L) * (q : u1M L) = 1 := by
    have h := congrArg Subtype.val hq2
    simpa using h
  have hq1' : (q : u1M L) ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hub1 : ub ≠ 1 := by
    intro h
    apply hubZ
    rw [h]
    exact one_mem _
  have hubq : ub ≠ (q : u1M L) := by
    intro h
    apply hubZ
    rw [h]
    exact Subgroup.mem_map_of_mem _ hqZ
  obtain ⟨xN, yN, hxN2, hyN2, hxyN, hxa, hyb⟩ :=
    u1_lift (u1R L) (u1R_odd L) hub2 hq2' (hqc ub)
  obtain ⟨l, hl⟩ : ∃ l : L, u1ψ L l = (q : u1M L) := MonoidHom.mem_range.mp q.2
  have hyl : (yN : u1M L) = ((⟨(l : G), le_u1N L l.2⟩ : u1N L) : u1M L) :=
    hyb.trans (hl.symm.trans (u1ψ_apply L l))
  have hr : ((yN⁻¹ * ⟨(l : G), le_u1N L l.2⟩ : u1N L) : G) ∈ (CFSG.oddCore L).map L.subtype :=
    Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hyl)
  obtain ⟨r, _, hr_eq⟩ := Subgroup.mem_map.mp hr
  have hr' : (r : G) = (yN : G)⁻¹ * (l : G) := hr_eq
  have hyL : (yN : G) ∈ L := by
    have hy_eq : (yN : G) = (l : G) * (r : G)⁻¹ := by
      rw [hr']
      group
    rw [hy_eq]
    exact L.mul_mem l.2 (L.inv_mem r.2)
  obtain ⟨z', hz'⟩ : ∃ z' : L, (z' : G) = (yN : G) := ⟨⟨(yN : G), hyL⟩, rfl⟩
  have hz'2 : z' * z' = 1 := by
    apply Subtype.ext
    show (z' : G) * (z' : G) = 1
    rw [hz']
    have h := congrArg Subtype.val hyN2
    simpa using h
  have hψz' : u1ψ L z' = (q : u1M L) := by
    have e1 : ((⟨(z' : G), le_u1N L z'.2⟩ : u1N L)) = yN := Subtype.ext hz'
    rw [hψπ, e1, hpix, hyb]
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply hq1'
    have hy1 : yN = 1 := by
      apply Subtype.ext
      simp [← hz', h1]
    simp [← hyb, hy1]
  have hcomm_ker : ∀ x : L, x * z' * x⁻¹ * z'⁻¹ ∈ CFSG.oddCore L := by
    intro x
    rw [← u1ψ_ker L, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hψz', hqc (u1ψ L x)]
    group
  refine ⟨z', hz'2, hz'1, hcomm_ker, (xN : G), ?_, ?_, ?_, ?_, xN.2⟩
  · have h := congrArg Subtype.val hxN2
    simpa using h
  · intro h
    have hx1 : xN = 1 := Subtype.ext h
    apply hub1
    simp [← hxa, hx1]
  · intro h
    have hxy : xN = yN := Subtype.ext (h.trans hz')
    apply hubq
    rw [← hxa, ← hyb, hxy]
  · rw [hz']
    have h := congrArg Subtype.val hxyN
    simpa using h

theorem u1cb2_mod_eq {X : Type*} [Group X] [Finite X] (O : Subgroup X) [O.Normal]
    (hOodd : Odd (Nat.card O)) (hcenter : Nat.card (Subgroup.center (X ⧸ O)) = 2)
    {z z' : X} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hz'2 : z' * z' = 1) (hz'1 : z' ≠ 1)
    (hzc : ∀ x : X, x * z * x⁻¹ * z⁻¹ ∈ O) (hz'c : ∀ x : X, x * z' * x⁻¹ * z'⁻¹ ∈ O) :
    (z : X ⧸ O) = (z' : X ⧸ O) := by
  have hcen : ∀ w : X, (∀ x : X, x * w * x⁻¹ * w⁻¹ ∈ O) →
      (w : X ⧸ O) ∈ Subgroup.center (X ⧸ O) := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : ((x * w * x⁻¹ * w⁻¹ : X) : X ⧸ O) = 1 := (QuotientGroup.eq_one_iff _).mpr (hw x)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    calc (x : X ⧸ O) * (w : X ⧸ O)
        = ((x : X ⧸ O) * (w : X ⧸ O) * (x : X ⧸ O)⁻¹ * (w : X ⧸ O)⁻¹) * (w : X ⧸ O) * (x : X ⧸ O) := by
          group
      _ = (w : X ⧸ O) * (x : X ⧸ O) := by rw [h1, one_mul]
  have hnot : ∀ w : X, w * w = 1 → w ≠ 1 → (w : X ⧸ O) ≠ 1 := by
    intro w hw2 hw1 h1
    have hwO : w ∈ O := (QuotientGroup.eq_one_iff w).mp h1
    exact hw1 (u1_eq_one_of_odd O hOodd hwO ⟨1, by rw [pow_one, pow_two, hw2]⟩)
  have hzZ := hcen z hzc
  have hz'Z := hcen z' hz'c
  have hz1' := hnot z hz2 hz1
  have hz'1' := hnot z' hz'2 hz'1
  rcases CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1c_eq_one_or_eq_of_natCard_two
      (Subgroup.center (X ⧸ O)) hcenter hzZ hz1' hz'Z with h | h
  · exact absurd h hz'1'
  · exact h.symm

theorem u1c_core {G : Type} [Group G] [Finite G] {L : Subgroup G} {c t : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hc3 : orderOf c = 3) (hcL : c ∉ L)
    (htN : t ∈ Subgroup.normalizer (L : Set G))
    (htc : t * c * t⁻¹ = c⁻¹)
    (hperf : Group.IsPerfect (L ⧸ CFSG.oddCore L))
    (hcenter : Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 2)
    (e : (L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L) ≃*
      alternatingGroup (Fin 7))
    (z : L) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ x : L, x * z * x⁻¹ * z⁻¹ ∈ CFSG.oddCore L) :
    ∃ u : G, u * u = 1 ∧ u ≠ 1 ∧ u ≠ (z : G) ∧ u * (z : G) = (z : G) * u ∧
      u ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨z', hz'2, hz'1, hz'c, u', hu'2, hu'1, hu'z, hcomm, hu'N⟩ :=
    u1c_zu hLc hc3 hcL htN htc hperf hcenter e
  have hmk : (z : L ⧸ CFSG.oddCore L) = (z' : L ⧸ CFSG.oddCore L) :=
    u1cb2_mod_eq (CFSG.oddCore L) (CFSG.ABGDGroups.odd_card_oddCore L) hcenter hz2 hz1 hz'2 hz'1
      hzc hz'c
  obtain ⟨h, hhO, hh⟩ :=
    CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1_exists_conj_of_two (CFSG.oddCore L)
      (CFSG.ABGDGroups.odd_card_oddCore L) hz2 hz'2 hmk
  have hhG : (h : G) * (z : G) * (h : G)⁻¹ = (z' : G) := by
    have h' := congrArg Subtype.val hh
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    exact h'
  have hhN : (h : G) ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.le_normalizer (H := L)) h.2
  have hcomm' : u' * ((h : G) * (z : G) * (h : G)⁻¹) = ((h : G) * (z : G) * (h : G)⁻¹) * u' := by
    rw [hhG]
    exact hcomm
  refine ⟨(h : G)⁻¹ * u' * (h : G), ?_, ?_, ?_, ?_, ?_⟩
  · calc (h : G)⁻¹ * u' * (h : G) * ((h : G)⁻¹ * u' * (h : G)) = (h : G)⁻¹ * (u' * u') * (h : G) := by
          group
      _ = 1 := by rw [hu'2]; group
  · intro h1
    apply hu'1
    calc u' = (h : G) * ((h : G)⁻¹ * u' * (h : G)) * (h : G)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    apply hu'z
    rw [← hhG]
    calc u' = (h : G) * ((h : G)⁻¹ * u' * (h : G)) * (h : G)⁻¹ := by group
      _ = (h : G) * (z : G) * (h : G)⁻¹ := by rw [h1]
  · calc (h : G)⁻¹ * u' * (h : G) * (z : G)
        = (h : G)⁻¹ * (u' * ((h : G) * (z : G) * (h : G)⁻¹)) * (h : G) := by group
      _ = (h : G)⁻¹ * (((h : G) * (z : G) * (h : G)⁻¹) * u') * (h : G) := by rw [hcomm']
      _ = (z : G) * ((h : G)⁻¹ * u' * (h : G)) := by group
  · exact mul_mem (mul_mem (inv_mem hhN) hu'N) hhN

end CFSG.RankThree.PartTwo.Sec13.F135Last
