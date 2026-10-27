module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.lemma_5_2_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_b

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.3 from BG Section 5 -/

public theorem CFSG.groupRank_le_one_of_isCyclic
    (G : Type*) [Group G] [Finite G] [IsCyclic G] :
    groupRank G ≤ 1 := by
  have hgen_le_one : generatorRank G ≤ 1 := generatorRank_le_one_of_isCyclic (G := G) (by infer_instance)
  have hprimeRank_le_one :
      ∀ q : ℕ, Nat.Prime q → primeRank q G ≤ 1 := by
    intro q hq
    rw [primeRank]
    refine csSup_le ?_ ?_
    · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := G), inferInstance, Nat.zero_le _⟩
    · intro n hn
      rcases hn with ⟨A, _hApA, hAcomm, hnA⟩
      letI : IsMulCommutative A := hAcomm
      have hAle : generatorRank A ≤ 1 := by
        haveI : IsCyclic A := isCyclic_of_injective A.subtype A.subtype_injective
        exact generatorRank_le_one_of_isCyclic (G := A) (by infer_instance)
      exact hnA.trans hAle
  rw [groupRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, 2, by decide, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨q, hq, hnq⟩
    exact hnq.trans (hprimeRank_le_one q hq)

public theorem CFSG.generatorRank_le_natCard
    (G : Type*) [Group G] [Finite G] :
    generatorRank G ≤ Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec G
  calc
    generatorRank G = Group.rank G := generatorRank_eq_group_rank G
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card G := by simpa using Finset.card_le_univ S
    _ = Nat.card G := by simp [Nat.card_eq_fintype_card]

public theorem CFSG.primeRank_le_natCard
    {p : ℕ} (G : Type*) [Group G] [Finite G] :
    primeRank p G ≤ Nat.card G := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p) (G := G), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, _hApA, _hAcomm, hnA⟩
    exact hnA.trans <| (generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)

private theorem CFSG.primeRank_top_subgroup_eq
    (q : ℕ) (G : Type*) [Group G] [Finite G] :
    primeRank q (⊤ : Subgroup G) = primeRank q G := by
  classical
  rw [primeRank, primeRank]
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := (⊤ : Subgroup G)), inferInstance,
        Nat.zero_le _⟩
    · intro n hn
      rcases hn with ⟨A, hAp, hAcomm, hnA⟩
      let Amap : Subgroup G := A.map (⊤ : Subgroup G).subtype
      have hAmap_p : IsPGroup q Amap := by
        exact hAp.of_equiv
          (Subgroup.equivMapOfInjective (f := (⊤ : Subgroup G).subtype)
            A (⊤ : Subgroup G).subtype_injective)
      have hAmap_comm : IsMulCommutative Amap := by
        letI : IsMulCommutative A := hAcomm
        simpa [Amap] using
          (Subgroup.map_isMulCommutative (f := (⊤ : Subgroup G).subtype) (H := A))
      have hgen_eq : generatorRank A = generatorRank Amap := by
        rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
        exact Group.rank_congr
          (Subgroup.equivMapOfInjective (f := (⊤ : Subgroup G).subtype)
            A (⊤ : Subgroup G).subtype_injective)
      refine le_csSup ?_ ?_
      · refine ⟨Nat.card G, ?_⟩
        intro m hm
        rcases hm with ⟨B, _hBp, _hBcomm, hmB⟩
        exact hmB.trans <| (generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
      · exact ⟨Amap, hAmap_p, hAmap_comm, by simpa [hgen_eq] using hnA⟩
  · refine csSup_le ?_ ?_
    · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := G), inferInstance, Nat.zero_le _⟩
    · intro n hn
      rcases hn with ⟨A, hAp, hAcomm, hnA⟩
      let Atop : Subgroup (⊤ : Subgroup G) := A.subgroupOf (⊤ : Subgroup G)
      have hAtop_p : IsPGroup q Atop := by
        exact hAp.of_equiv
          (Subgroup.subgroupOfEquivOfLe (G := G) (H := A) (K := (⊤ : Subgroup G)) le_top).symm
      have hAtop_comm : IsMulCommutative Atop := by
        letI : IsMulCommutative A := hAcomm
        simpa [Atop] using
          Subgroup.subgroupOf_isMulCommutative (H := A) (K := (⊤ : Subgroup G))
      have hgen_eq : generatorRank A = generatorRank Atop := by
        rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
        let e : Atop ≃* A :=
          Subgroup.subgroupOfEquivOfLe (G := G) (H := A) (K := (⊤ : Subgroup G)) le_top
        exact (Group.rank_congr e).symm
      refine le_csSup ?_ ?_
      · refine ⟨Nat.card (⊤ : Subgroup G), ?_⟩
        intro m hm
        rcases hm with ⟨B, _hBp, _hBcomm, hmB⟩
        exact hmB.trans <| (generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
      · exact ⟨Atop, hAtop_p, hAtop_comm, by simpa [hgen_eq] using hnA⟩

public theorem CFSG.groupRank_top_subgroup_eq
    (G : Type*) [Group G] [Finite G] :
    groupRank (⊤ : Subgroup G) = groupRank G := by
  rw [groupRank, groupRank]
  congr
  ext n
  constructor
  · rintro ⟨q, hq, hnq⟩
    exact ⟨q, hq, by simpa [primeRank_top_subgroup_eq] using hnq⟩
  · rintro ⟨q, hq, hnq⟩
    exact ⟨q, hq, by simpa [primeRank_top_subgroup_eq] using hnq⟩

public theorem CFSG.groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G]
    {B : Subgroup G} [IsElementaryAbelian p B] (hBcard : Nat.card B = p ^ 3) :
    3 ≤ groupRank G := by
  have hBgrank : 3 ≤ generatorRank B :=
    generatorRank_at_least_three_of_elementaryAbelian_card_p3 (p := p) (A := B) hBcard
  have hBprimeRank : 3 ≤ primeRank p G := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card G, ?_⟩
      intro n hn
      rcases hn with ⟨A, _hApA, _hAcomm, hnA⟩
      exact hnA.trans <| (generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
    · exact ⟨B, IsElementaryAbelian.isPGroup p B, inferInstance, hBgrank⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card G, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (primeRank_le_natCard (p := q) G)
  · exact ⟨p, Fact.out, hBprimeRank⟩

public theorem CFSG.isElementaryAbelian_of_prime_card_isCyclic
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hcard : Nat.card G = p) :
    IsElementaryAbelian p G := by
  letI : CommGroup G := IsCyclic.commGroup
  refine
    { toIsMulCommutative := { is_comm := ⟨mul_comm⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  exact orderOf_dvd_iff_pow_eq_one.mp <| by
    simpa [hcard] using (orderOf_dvd_natCard x)

public theorem CFSG.isElementaryAbelian_top
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [IsElementaryAbelian p G] :
    IsElementaryAbelian p (⊤ : Subgroup G) := by
  let hG : IsElementaryAbelian p G := inferInstance
  letI : IsMulCommutative G := hG.toIsMulCommutative
  refine
    { toIsMulCommutative := by
        exact
          { is_comm := ⟨fun x y =>
              Subtype.ext <|
                (IsMulCommutative.is_comm (M := G)).comm (x : G) (y : G)⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p G) (x : G)

public theorem CFSG.isComplement'_of_disjoint_sup_eq_top_of_normal {G : Type*} [Group G]
    (H K : Subgroup G) [H.Normal] (hdisj : Disjoint H K) (hsup : H ⊔ K = ⊤) :
    H.IsComplement' K := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · exact hdisj
  · rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ H ⊔ K := by simp [hsup]
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := H) (t := K)).1 hx with
      ⟨h, hhH, k, hkK, hmul⟩
    refine ⟨h, hhH, k, hkK, ?_⟩
    simpa using hmul

public theorem CFSG.cyclic_prime_kernel_unique
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (H : Subgroup G) (hHcard : Nat.card H = p)
    (hHpow : ∀ x : H, (x : G) ^ p = 1) :
    H = (powMonoidHom (α := G) p).ker := by
  have hpdvd_cardG : p ∣ Nat.card G := by
    rw [← hHcard]
    exact Subgroup.card_subgroup_dvd_card H
  have hker_card : Nat.card ((powMonoidHom (α := G) p).ker) = p := by
    calc
      Nat.card ((powMonoidHom (α := G) p).ker) = (Nat.card G).gcd p := by
        exact IsCyclic.card_powMonoidHom_ker (G := G) p
      _ = p.gcd (Nat.card G) := by rw [Nat.gcd_comm]
      _ = p := by
        exact Nat.dvd_antisymm (Nat.gcd_dvd_left p (Nat.card G))
          (Nat.dvd_gcd (dvd_rfl : p ∣ p) hpdvd_cardG)
  have hH_le_ker : H ≤ (powMonoidHom (α := G) p).ker := by
    intro x hx
    change x ^ p = 1
    exact hHpow ⟨x, hx⟩
  exact Subgroup.eq_of_le_of_card_ge hH_le_ker <| by
    rw [hker_card, hHcard]

public theorem CFSG.narrow_witness_centralizer_not_cyclic
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {R₀ R₁ : Subgroup R} (hR₀card : Nat.card R₀ = p) (_hR₁cyc : IsCyclic R₁)
    (_hdisj : Disjoint R₀ R₁)
    (hcent : Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁) :
    ¬ IsCyclic (Subgroup.centralizer (R₀ : Set R)) := by
  classical
  let C : Subgroup R := Subgroup.centralizer (R₀ : Set R)
  intro hCcyc
  letI : IsCyclic C := hCcyc
  letI : CommGroup C := IsCyclic.commGroup
  have hR₀_le_C : R₀ ≤ C := by
    dsimp [C]
    rw [hcent]
    exact le_sup_left
  have hR₀_ne_bot : R₀ ≠ ⊥ := by
    intro hR₀_bot
    have hp_ne_one : p ≠ 1 := (Fact.out : Nat.Prime p).ne_one
    exact hp_ne_one <| by simpa [hR₀_bot] using hR₀card.symm
  have hR_nontrivial : Nontrivial R := by
    haveI : Nontrivial R₀ := (Subgroup.nontrivial_iff_ne_bot R₀).2 hR₀_ne_bot
    obtain ⟨x, hx⟩ := exists_ne (1 : R₀)
    refine ⟨⟨1, x.1, ?_⟩⟩
    intro h
    apply hx
    apply Subtype.ext
    simpa using h.symm
  have hC_card_ne_one : Nat.card C ≠ 1 := by
    intro hCcard
    have hR₀_eq_bot : R₀ = ⊥ := by
      have hR₀_card_le_one : Nat.card R₀ ≤ 1 := by
        calc
          Nat.card R₀ ≤ Nat.card C := Subgroup.card_le_of_le hR₀_le_C
          _ = 1 := hCcard
      exact R₀.eq_bot_of_card_le hR₀_card_le_one
    have hp_ne_one : p ≠ 1 := (Fact.out : Nat.Prime p).ne_one
    exact hp_ne_one <| by simpa [hR₀_eq_bot] using hR₀card.symm
  have hZ_nontrivial : Nontrivial (Subgroup.center R) := hpR.center_nontrivial
  have hcenter_p : IsPGroup p (Subgroup.center R) := hpR.to_subgroup (Subgroup.center R)
  have hpdvd_center : p ∣ Nat.card (Subgroup.center R) := by
    rcases (IsPGroup.nontrivial_iff_card (p := p) (G := Subgroup.center R)
        (hG := hcenter_p)).1 hZ_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p (Nat.ne_of_gt hn)
  letI : Fintype (Subgroup.center R) := Fintype.ofFinite (Subgroup.center R)
  have hpdvd_center_fintype : p ∣ Fintype.card (Subgroup.center R) := by
    simpa [Nat.card_eq_fintype_card] using hpdvd_center
  obtain ⟨z₀, hz₀_order⟩ :=
    exists_prime_orderOf_dvd_card (G := Subgroup.center R) p hpdvd_center_fintype
  let z : R := z₀
  have hz_center : z ∈ Subgroup.center R := z₀.property
  have hzpow : z ^ p = 1 := by
    have hz₀pow : z₀ ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hz₀_order])
    exact congrArg Subtype.val hz₀pow
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    have hz₀_one : z₀ = 1 := by
      apply Subtype.ext
      exact hz1
    have horder_one : orderOf z₀ = 1 := by simp [hz₀_one]
    exact (Fact.out : Nat.Prime p).ne_one (by simpa [hz₀_order] using horder_one)
  let Z : Subgroup R := Subgroup.zpowers z
  have hZ_card : Nat.card Z = p := by
    calc
      Nat.card Z = orderOf z := by
        simp [Z]
      _ = p := orderOf_eq_prime hzpow hz_ne_one
  have hZ_le_center : Z ≤ Subgroup.center R := by
    exact (Subgroup.zpowers_le).2 hz_center
  have hZ_le_C : Z ≤ C := by
    exact hZ_le_center.trans (Subgroup.center_le_centralizer (R₀ : Set R))
  let ZC : Subgroup C := Z.subgroupOf C
  have hZC_card : Nat.card ZC = p := by
    rw [natCard_subgroupOf_eq Z C hZ_le_C, hZ_card]
  have hZC_pow : ∀ x : ZC, (x : C) ^ p = 1 := by
    intro x
    apply Subtype.ext
    have hx_mem_Z : (((x : ZC) : C) : R) ∈ Z := Subgroup.mem_subgroupOf.mp x.property
    have horder_dvd : orderOf (((x : ZC) : C) : R) ∣ orderOf z := by
      exact orderOf_dvd_of_mem_zpowers hx_mem_Z
    have hpowR : ((((x : ZC) : C) : R) ^ p) = 1 := by
      rw [orderOf_eq_prime hzpow hz_ne_one] at horder_dvd
      exact orderOf_dvd_iff_pow_eq_one.mp (horder_dvd.trans (dvd_rfl : p ∣ p))
    simpa using hpowR
  let R₀C : Subgroup C := R₀.subgroupOf C
  have hR₀C_card : Nat.card R₀C = p := by
    rw [natCard_subgroupOf_eq R₀ C hR₀_le_C, hR₀card]
  have hR₀C_pow : ∀ x : R₀C, (x : C) ^ p = 1 := by
    intro x
    apply Subtype.ext
    let x₀ : R₀ := ⟨(x : C), Subgroup.mem_subgroupOf.mp x.property⟩
    have horder_dvd : orderOf ((x₀ : R₀) : R) ∣ Nat.card R₀ := by
      simpa using (Subgroup.orderOf_dvd_natCard R₀ x₀.2)
    have hxpowR : (((x₀ : R₀) : R) ^ p) = 1 := by
      rw [hR₀card] at horder_dvd
      exact orderOf_dvd_iff_pow_eq_one.mp horder_dvd
    simpa [x₀] using hxpowR
  have hZC_eq_ker :
      ZC = (powMonoidHom (α := C) p).ker :=
    cyclic_prime_kernel_unique (p := p) (G := C) ZC hZC_card hZC_pow
  have hR₀C_eq_ker :
      R₀C = (powMonoidHom (α := C) p).ker :=
    cyclic_prime_kernel_unique (p := p) (G := C) R₀C hR₀C_card hR₀C_pow
  have hZ_le_R₀ : Z ≤ R₀ := by
    intro z' hz'
    have hzC : (⟨z', hZ_le_C hz'⟩ : C) ∈ ZC := hz'
    have hzker : ((⟨z', hZ_le_C hz'⟩ : C) ∈ (powMonoidHom (α := C) p).ker) := by
      simpa [hZC_eq_ker] using hzC
    have hzR₀C : (⟨z', hZ_le_C hz'⟩ : C) ∈ R₀C := by
      simpa [hR₀C_eq_ker] using hzker
    exact Subgroup.mem_subgroupOf.mp hzR₀C
  have hR₀_le_center : R₀ ≤ Subgroup.center R := by
    have hR₀_le_Z : R₀ ≤ Z := by
      intro r hr
      have hrC : r ∈ C := hR₀_le_C hr
      have hrker : ((⟨r, hrC⟩ : C) ∈ (powMonoidHom (α := C) p).ker) := by
        let r₀ : R₀ := ⟨r, hr⟩
        change (⟨r, hrC⟩ : C) ^ p = 1
        apply Subtype.ext
        have horder_dvd : orderOf ((r₀ : R₀) : R) ∣ Nat.card R₀ := by
          simpa using (Subgroup.orderOf_dvd_natCard R₀ r₀.2)
        have hrpow : r₀ ^ p = 1 := by
          rw [hR₀card] at horder_dvd
          rw [Subgroup.orderOf_coe] at horder_dvd
          exact orderOf_dvd_iff_pow_eq_one.mp horder_dvd
        simpa [r₀] using congrArg Subtype.val hrpow
      have hrZC : (⟨r, hrC⟩ : C) ∈ ZC := by simpa [hZC_eq_ker] using hrker
      exact Subgroup.mem_subgroupOf.mp hrZC
    exact hR₀_le_Z.trans hZ_le_center
  have hC_top : C = ⊤ := by
    apply (Subgroup.centralizer_eq_top_iff_subset).2
    exact fun x hx => hR₀_le_center hx
  have hR_cyclic : IsCyclic R := by
    let e : C ≃* R := (MulEquiv.subgroupCongr hC_top).trans Subgroup.topEquiv
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hRank_le_one : groupRank R ≤ 1 :=
    groupRank_le_one_of_isCyclic R
  exact (by decide : ¬ 3 ≤ (1 : ℕ)) (le_trans hR hRank_le_one)

private theorem CFSG.narrow_forward_exists_rank_two_maximal
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {R₀ R₁ : Subgroup R} (hR₀card : Nat.card R₀ = p) (hR₁cyc : IsCyclic R₁)
    (hdisj : Disjoint R₀ R₁)
    (hcent : Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁) :
    ∃ E : Subgroup R, E ∈ elementaryAbelianSubgroupsOfRank p 2 R ∧
      E ∈ maximalElementaryAbelianSubgroups p R := by
  classical
  let C : Subgroup R := Subgroup.centralizer (R₀ : Set R)
  have hCncyc : ¬ IsCyclic C := by
    simpa [C] using
      narrow_witness_centralizer_not_cyclic (p := p) (R := R) hpR hR hR₀card hR₁cyc hdisj hcent
  letI : Fact (IsPGroup p C) := ⟨hpR.to_subgroup C⟩
  have hindex : ∃ S : Subgroup C, IsCyclic S ∧ Nat.card (C ⧸ S) = p := by
    let R₁sub : Subgroup C := R₁.subgroupOf C
    refine ⟨R₁sub, ?_, ?_⟩
    · let e : R₁sub ≃* R₁ :=
        Subgroup.subgroupOfEquivOfLe (H := R₁) (K := C) (by
          simp [C, hcent])
      exact e.isCyclic.2 hR₁cyc
    · have hR₀_le_C : R₀ ≤ C := by
        simp [C, hcent]
      have hR₀sub_normal : (R₀.subgroupOf C).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hR₀_le_C]
        simpa [C] using (centralizer_le_normalizer (R := R₀))
      letI : (R₀.subgroupOf C).Normal := hR₀sub_normal
      have hsupC : R₀.subgroupOf C ⊔ R₁.subgroupOf C = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (A := R₀) (A' := R₁) (B := C)
          (by simp [C, hcent])
          (by simp [C, hcent])]
        simp [C, hcent]
      have hdisjC : Disjoint (R₀.subgroupOf C) (R₁.subgroupOf C) := by
        rw [Subgroup.disjoint_def]
        intro x hx0 hx1
        apply Subtype.ext
        exact Subgroup.disjoint_def.mp hdisj hx0 hx1
      have hcomp : (R₀.subgroupOf C).IsComplement' (R₁.subgroupOf C) :=
        isComplement'_of_disjoint_sup_eq_top_of_normal
          (R₀.subgroupOf C) (R₁.subgroupOf C) hdisjC hsupC
      have hcard_R₀sub : Nat.card (R₀.subgroupOf C) = p := by
        rw [natCard_subgroupOf_eq R₀ C hR₀_le_C, hR₀card]
      rw [← Subgroup.index_eq_card, hcomp.index_eq_card, hcard_R₀sub]
  let E : Subgroup R := omega₁ (G := C) (p := p) |>.map C.subtype
  have hEcard : Nat.card E = p ^ 2 := by
    obtain ⟨hΩcard, _hΩelem⟩ := lemma_4_5_b (R := C) (p := p) hpodd hCncyc hindex
    calc
      Nat.card E = Nat.card (omega₁ (G := C) (p := p)) := by
        simpa [E] using
          (Nat.card_congr
            (Subgroup.equivMapOfInjective (f := C.subtype) (omega₁ (G := C) (p := p))
              C.subtype_injective).toEquiv).symm
      _ = p ^ 2 := hΩcard
  have hEelem : IsElementaryAbelian p E := by
    obtain ⟨_hΩcard, hΩelem⟩ := lemma_4_5_b (R := C) (p := p) hpodd hCncyc hindex
    let Ω : Subgroup C := omega₁ (G := C) (p := p)
    letI : IsElementaryAbelian p Ω := hΩelem
    refine
      { toIsMulCommutative := by
          simpa [E, Ω] using (Subgroup.map_isMulCommutative (f := C.subtype) (H := Ω))
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hyx⟩
    let yΩ : Ω := ⟨y, hy⟩
    have hypow : yΩ ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p Ω) yΩ
    have hy_pow_R : ((((yΩ : Ω) : C) : R) ^ p) = 1 := by
      simpa [Ω] using congrArg (fun z : Ω => (((z : Ω) : C) : R)) hypow
    have hx_eq : ((x : E) : R) = (((yΩ : Ω) : C) : R) := by
      simpa [E, Ω, yΩ] using hyx.symm
    simpa [hx_eq] using hy_pow_R
  have hE_le_C : E ≤ C := by
    simpa [E] using (Subgroup.map_subtype_le (omega₁ (G := C) (p := p)))
  have hEmax : E ∈ maximalElementaryAbelianSubgroups p R := by
    refine ⟨hEelem, ?_⟩
    intro B hEB hBelem
    letI : IsElementaryAbelian p B := hBelem
    have hB_le_ΩR : B ≤ omega₁ (G := R) (p := p) := elementaryAbelian_le_omega₁
    have hB_le_C : B ≤ C := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro r₀ hr₀
      have hr₀E : r₀ ∈ E := by
        have hr₀C : r₀ ∈ C := by
          simpa [C, hcent] using (Subgroup.mem_sup_left hr₀ : r₀ ∈ R₀ ⊔ R₁)
        have hr₀Ω : (⟨r₀, hr₀C⟩ : C) ∈ omega₁ (G := C) (p := p) := by
          rw [omega₁, omega]
          refine Subgroup.subset_closure ?_
          have hr₀powR : r₀ ^ p = 1 := by
            haveI : Fact (IsPGroup p R₀) := ⟨IsPGroup.of_card (p := p) (G := R₀)
              (n := 1) (by simpa [pow_one] using hR₀card)⟩
            have hr₀pow : (⟨r₀, hr₀⟩ : R₀) ^ p = 1 := by
              simpa [hR₀card] using pow_card_eq_one' (x := (⟨r₀, hr₀⟩ : R₀))
            simpa using congrArg Subtype.val hr₀pow
          have hr₀powC : ((⟨r₀, hr₀C⟩ : C) ^ p) = 1 := by
            apply Subtype.ext
            simpa using hr₀powR
          simpa [pow_one] using hr₀powC
        exact Subgroup.mem_map.mpr ⟨⟨r₀, hr₀C⟩, hr₀Ω, rfl⟩
      have hr₀B : r₀ ∈ B := hEB hr₀E
      exact setLike_mul_comm (s := B) hr₀B hb
    have hB_le_E : B ≤ E := by
      intro b hb
      have hbpow : b ^ p = 1 := by
        have hbB : (⟨b, hb⟩ : B) ^ p = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p B) ⟨b, hb⟩
        simpa using congrArg Subtype.val hbB
      have hbC : b ∈ C := hB_le_C hb
      have hbΩC : (⟨b, hbC⟩ : C) ∈ omega₁ (G := C) (p := p) := by
        rw [omega₁, omega]
        refine Subgroup.subset_closure ?_
        have hbpowC : ((⟨b, hbC⟩ : C) ^ p) = 1 := by
          simpa using hbpow
        simpa [pow_one] using hbpowC
      exact Subgroup.mem_map.mpr ⟨⟨b, hbC⟩, hbΩC, rfl⟩
    exact le_antisymm hEB hB_le_E
  exact ⟨E, ⟨hEcard, hEelem⟩, hEmax⟩

public theorem CFSG.omega1Z_isElementaryAbelian
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] :
    IsElementaryAbelian p (Ω₁Z p R) := by
  let Ωc : Subgroup (Subgroup.center R) := omega₁ (G := Subgroup.center R) (p := p)
  have hΩcelem : IsElementaryAbelian p Ωc := by
    letI : IsMulCommutative (Subgroup.center R) := inferInstance
    simpa [Ωc] using omega1_isElementaryAbelian_of_commutative (p := p) (Subgroup.center R)
  letI : IsElementaryAbelian p Ωc := hΩcelem
  refine
    { toIsMulCommutative := by
        have hΩZ_le_center : Ω₁Z p R ≤ Subgroup.center R := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, _hy, hyx⟩
          rw [← hyx]
          exact y.property
        apply (Subgroup.le_centralizer_iff_isMulCommutative
          (K := Ω₁Z p R)).1
        exact hΩZ_le_center.trans
          (Subgroup.center_le_centralizer (Ω₁Z p R : Set R))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hyx⟩
  let yΩ : Ωc := ⟨y, hy⟩
  have hypow : yΩ ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p Ωc) yΩ
  have hx_eq : ((x : Ω₁Z p R) : R) = ((yΩ : Ωc) : Subgroup.center R) := by
    simpa [yΩ] using hyx.symm
  simpa [hx_eq] using congrArg (fun z : Ωc => (((z : Ωc) : Subgroup.center R) : R)) hypow

public theorem CFSG.omega1Z_le_center
    (p : ℕ) (R : Type*) [Group R] :
    Ω₁Z p R ≤ Subgroup.center R := by
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
  exact y.property

public theorem CFSG.omega1Z_normal
    (p : ℕ) (R : Type*) [Group R] :
    (Ω₁Z p R).Normal := by
  refine ⟨?_⟩
  intro z hz r
  have hzcent : z ∈ Subgroup.center R := (omega1Z_le_center p R) hz
  have hconj : r * z * r⁻¹ = z := by
    have hmul : r * z = z * r := (Subgroup.mem_center_iff.mp hzcent) r
    calc
      r * z * r⁻¹ = z * r * r⁻¹ := by rw [hmul]
      _ = z := by simp [mul_assoc]
  simpa [hconj] using hz

public theorem CFSG.omega1Z_le_of_rank_two_maximal
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] {E : Subgroup R}
    (hEelem : IsElementaryAbelian p E)
    (hEmax : E ∈ maximalElementaryAbelianSubgroups p R) :
    Ω₁Z p R ≤ E := by
  classical
  rcases hEmax with ⟨_hEelem', hEmax'⟩
  letI : IsElementaryAbelian p E := hEelem
  let Z : Subgroup R := Ω₁Z p R
  have hZelem : IsElementaryAbelian p Z := by
    simpa [Z] using omega1Z_isElementaryAbelian (p := p) (R := R)
  letI : IsElementaryAbelian p Z := hZelem
  have hZcentE : Z ≤ Subgroup.centralizer (E : Set R) := by
    exact (omega1Z_le_center p R).trans (Subgroup.center_le_centralizer (E : Set R))
  have hEcentZ : E ≤ Subgroup.centralizer (Z : Set R) := by
    exact (Subgroup.le_centralizer_iff).mp hZcentE
  have hZEelem : IsElementaryAbelian p ↥(Z ⊔ E : Subgroup R) := by
    exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := Z) (C := E) hEcentZ
  have hEZ_eq : E = Z ⊔ E := by
    exact hEmax' (Z ⊔ E : Subgroup R) le_sup_right hZEelem
  intro z hz
  have hzsup : z ∈ Z ⊔ E := Subgroup.mem_sup_left hz
  simpa [Z, ← hEZ_eq] using hzsup

public theorem CFSG.exists_order_p_subgroup_of_rank_two_maximal_not_le
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] [Finite R]
    {E T : Subgroup R} (hEcard : Nat.card E = p ^ 2) [IsElementaryAbelian p E]
    (hZcard : Nat.card (Ω₁Z p R) = p) (hZ_le_E : Ω₁Z p R ≤ E)
    (hZ_le_T : Ω₁Z p R ≤ T) (hE_not_le_T : ¬ E ≤ T) :
    ∃ S : Subgroup R, S ≤ E ∧ Nat.card S = p ∧ Disjoint (Ω₁Z p R) S ∧ ¬ S ≤ T ∧
      E = Ω₁Z p R ⊔ S := by
  classical
  have hnot : ∃ s, s ∈ E ∧ s ∉ T := by
    by_contra h
    apply hE_not_le_T
    intro s hsE
    by_contra hsT
    exact h ⟨s, hsE, hsT⟩
  obtain ⟨s, hsE, hsT⟩ := hnot
  let S : Subgroup R := Subgroup.zpowers s
  have hs_ne_one : s ≠ 1 := by
    intro hs1
    exact hsT (by simp [hs1])
  have hspow : s ^ p = 1 := by
    have hspowE : (⟨s, hsE⟩ : E) ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) ⟨s, hsE⟩
    simpa using congrArg Subtype.val hspowE
  have hScard : Nat.card S = p := by
    calc
      Nat.card S = orderOf s := by simp [S]
      _ = p := orderOf_eq_prime hspow hs_ne_one
  have hS_le_E : S ≤ E := by
    exact (Subgroup.zpowers_le).2 hsE
  have hS_not_le_T : ¬ S ≤ T := by
    intro hST
    exact hsT (hST (Subgroup.mem_zpowers s))
  have hdisj : Disjoint (Ω₁Z p R) S := by
    rw [Subgroup.disjoint_def]
    intro x hxZ hxS
    by_contra hx_ne_one
    have hZS : (Ω₁Z p R).subgroupOf S = ⊤ := by
      haveI : Fact (Nat.card S).Prime := ⟨by simpa [hScard] using (Fact.out : Nat.Prime p)⟩
      have hxsub_ne_bot : (Ω₁Z p R).subgroupOf S ≠ ⊥ := by
        intro hbot
        have hx_sub : (⟨x, hxS⟩ : S) ∈ (Ω₁Z p R).subgroupOf S := hxZ
        have hx_bot : (⟨x, hxS⟩ : S) ∈ (⊥ : Subgroup S) := by simpa [hbot] using hx_sub
        exact hx_ne_one (by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hx_bot))
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Ω₁Z p R).subgroupOf S) with hbot | htop
      · exact False.elim (hxsub_ne_bot hbot)
      · exact htop
    have hS_le_Z : S ≤ Ω₁Z p R := by
      intro y hyS
      have hy_top : (⟨y, hyS⟩ : S) ∈ (⊤ : Subgroup S) := by simp
      have hy_sub : (⟨y, hyS⟩ : S) ∈ (Ω₁Z p R).subgroupOf S := by
        rw [hZS]
        exact hy_top
      exact Subgroup.mem_subgroupOf.mp hy_sub
    exact hS_not_le_T (hS_le_Z.trans hZ_le_T)
  have hZ_normal : (Ω₁Z p R).Normal := by
    refine ⟨?_⟩
    intro z hz r
    have hzcent : z ∈ Subgroup.center R := (omega1Z_le_center p R) hz
    have hconj : r * z * r⁻¹ = z := by
      have hmul : r * z = z * r := (Subgroup.mem_center_iff.mp hzcent) r
      calc
        r * z * r⁻¹ = z * r * r⁻¹ := by rw [hmul]
        _ = z := by simp [mul_assoc]
    simpa [hconj] using hz
  have hcomp :
      ((Ω₁Z p R).subgroupOf (Ω₁Z p R ⊔ S)).IsComplement'
        (S.subgroupOf (Ω₁Z p R ⊔ S)) := by
    letI : (Ω₁Z p R).Normal := hZ_normal
    let ZS : Subgroup R := Ω₁Z p R ⊔ S
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxZ hxS
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hdisj hxZ hxS
    · rw [Set.eq_univ_iff_forall]
      intro x
      rcases (Subgroup.mem_sup_of_normal_left (x := (x : R)) (s := Ω₁Z p R) (t := S)).1 x.2 with
        ⟨z, hzZ, s, hsS, hmul⟩
      let zZS : (Ω₁Z p R).subgroupOf ZS :=
        ⟨⟨z, Subgroup.mem_sup_left hzZ⟩, hzZ⟩
      let sZS : S.subgroupOf ZS :=
        ⟨⟨s, Subgroup.mem_sup_right hsS⟩, hsS⟩
      refine ⟨(zZS : ZS), zZS.2, (sZS : ZS), sZS.2, ?_⟩
      apply Subtype.ext
      simpa using hmul
  have hsup_card : Nat.card (Ω₁Z p R ⊔ S : Subgroup R) = p ^ 2 := by
    have hmul := hcomp.card_mul
    rw [natCard_subgroupOf_eq (Ω₁Z p R) (Ω₁Z p R ⊔ S) le_sup_left,
      natCard_subgroupOf_eq S (Ω₁Z p R ⊔ S) le_sup_right, hZcard, hScard] at hmul
    simpa [pow_two] using hmul.symm
  have hsup_card_ge : Nat.card E ≤ Nat.card (Ω₁Z p R ⊔ S : Subgroup R) := by
    rw [hEcard, hsup_card]
  have hsup_eq : E = Ω₁Z p R ⊔ S :=
    (Subgroup.eq_of_le_of_card_ge (sup_le hZ_le_E hS_le_E) hsup_card_ge).symm
  exact ⟨S, hS_le_E, hScard, hdisj, hS_not_le_T, hsup_eq⟩

public theorem CFSG.groupRank_centralizer_le_two_of_rank_two_maximal
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R)
    {E S : Subgroup R} (hE : E ∈ elementaryAbelianSubgroupsOfRank p 2 R)
    (hEmax : E ∈ maximalElementaryAbelianSubgroups p R)
    (hE_eq : E = Ω₁Z p R ⊔ S) :
    groupRank (Subgroup.centralizer (S : Set R)) ≤ 2 := by
  classical
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  rcases hE with ⟨hEcard, hEelem⟩
  rcases hEmax with ⟨_hEelem', hEmax'⟩
  letI : IsElementaryAbelian p E := hEelem
  have hZ_le_E : Ω₁Z p R ≤ E :=
    omega1Z_le_of_rank_two_maximal hEelem ⟨hEelem, hEmax'⟩
  have hS_le_E : S ≤ E := by
    rw [hE_eq]
    exact le_sup_right
  have hZ_le_C : Ω₁Z p R ≤ C := by
    exact (omega1Z_le_center p R).trans (Subgroup.center_le_centralizer (S : Set R))
  have hS_le_C : S ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact setLike_mul_comm (s := E) (hS_le_E ht) (hS_le_E hs)
  have hE_le_C : E ≤ C := by
    rw [hE_eq]
    exact sup_le hZ_le_C hS_le_C
  by_contra hCgt
  have hC_rank : 3 ≤ groupRank C := by
    have hCgt' : 2 < groupRank (Subgroup.centralizer (S : Set R)) := not_le.mp hCgt
    have hC_rank' : 3 ≤ groupRank (Subgroup.centralizer (S : Set R)) := by omega
    simpa [C] using hC_rank'
  let Esub : Subgroup C := E.subgroupOf C
  have hEsub_card : Nat.card Esub = p ^ 2 := by
    rw [natCard_subgroupOf_eq E C hE_le_C, hEcard]
  have hEsub_elem : IsElementaryAbelian p Esub :=
    IsElementaryAbelian.subgroupOf (p := p) hE_le_C
  letI : IsElementaryAbelian p Esub := hEsub_elem
  have hZsub_norm : ((Ω₁Z p R).subgroupOf C).Normal := by
    letI : (Ω₁Z p R).Normal := omega1Z_normal p R
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZ_le_C]
    exact Subgroup.le_normalizer_of_normal (H := Ω₁Z p R)
  have hSsub_norm : (S.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_C]
    simpa [C] using (centralizer_le_normalizer (R := S))
  have hEsub_eq : Esub = (Ω₁Z p R).subgroupOf C ⊔ S.subgroupOf C := by
    change E.subgroupOf C = (Ω₁Z p R).subgroupOf C ⊔ S.subgroupOf C
    rw [hE_eq]
    exact Subgroup.subgroupOf_sup hZ_le_C hS_le_C
  have hEsub_norm : Esub.Normal := by
    letI : ((Ω₁Z p R).subgroupOf C).Normal := hZsub_norm
    letI : (S.subgroupOf C).Normal := hSsub_norm
    rw [hEsub_eq]
    infer_instance
  letI : Esub.Normal := hEsub_norm
  obtain ⟨B, _hBnorm, hBelem, hBcard, hEsub_le_B⟩ :=
    exists_normal_elementaryAbelian_card_p3_containing_rank_two_normal
      (p := p) hpodd (R := C) (hpR.to_subgroup C) hC_rank
      (hE := ⟨hEsub_card, hEsub_elem⟩)
  let BR : Subgroup R := B.map C.subtype
  have hBR_elem : IsElementaryAbelian p BR := by
    letI : IsElementaryAbelian p B := hBelem
    simpa [BR] using IsElementaryAbelian.map_subtype (p := p) (K := C) (H := B)
  have hBR_card : Nat.card BR = p ^ 3 := by
    calc
      Nat.card BR = Nat.card B := by
        symm
        exact Nat.card_congr
          (Subgroup.equivMapOfInjective (f := C.subtype) B C.subtype_injective).toEquiv
      _ = p ^ 3 := hBcard
  have hE_le_BR : E ≤ BR := by
    intro e he
    exact Subgroup.mem_map.mpr
      ⟨⟨e, hE_le_C he⟩, hEsub_le_B he, rfl⟩
  have hE_eq_BR : E = BR := hEmax' BR hE_le_BR hBR_elem
  have hpow_eq : p ^ 2 = p ^ 3 := by
    calc
      p ^ 2 = Nat.card E := hEcard.symm
      _ = Nat.card BR := by rw [hE_eq_BR]
      _ = p ^ 3 := hBR_card
  exact (ne_of_lt ((Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).2
    (by decide : 2 < 3))) hpow_eq

private theorem CFSG.rank_two_maximal_implies_narrow
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {E : Subgroup R} (hE : E ∈ elementaryAbelianSubgroupsOfRank p 2 R)
    (hEmax : E ∈ maximalElementaryAbelianSubgroups p R) :
    IsNarrowPGroup p R := by
  classical
  have hErank : E ∈ elementaryAbelianSubgroupsOfRank p 2 R := hE
  rcases hE with ⟨hEcard, hEelem⟩
  let T : Subgroup R := CΩ₁Z₂ p R
  obtain ⟨hZcard, _hWmem⟩ := lemma_5_2_b (p := p) hpodd (R := R) hpR hR hErank hEmax
  obtain ⟨hTchar, hTindex⟩ := lemma_5_2_c (p := p) hpodd (R := R) hpR hR hErank hEmax
  letI : T.Characteristic := hTchar
  letI : T.Normal := by infer_instance
  have hZ_le_E : Ω₁Z p R ≤ E := omega1Z_le_of_rank_two_maximal hEelem hEmax
  have hZ_le_T : Ω₁Z p R ≤ T := by
    exact (omega1Z_le_center p R).trans (Subgroup.center_le_centralizer (Ω₁Z₂ p R : Set R))
  have hE_not_le_T : ¬ E ≤ T := lemma_5_2_a (p := p) hpodd (R := R) hpR hR hErank hEmax
  obtain ⟨S, hS_le_E, hScard, hdisjZS, hS_not_le_T, hE_eq⟩ :=
    exists_order_p_subgroup_of_rank_two_maximal_not_le
      (p := p) (R := R) (E := E) (T := T) hEcard hZcard hZ_le_E hZ_le_T hE_not_le_T
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hC_rank_le_two : groupRank C ≤ 2 :=
    groupRank_centralizer_le_two_of_rank_two_maximal
      (p := p) hpodd (R := R) hpR hErank hEmax hE_eq
  have hTS_bot : T.subgroupOf S = ⊥ := by
    haveI : Fact (Nat.card S).Prime := ⟨by simpa [hScard] using (Fact.out : Nat.Prime p)⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (T.subgroupOf S) with hbot | htop
    · exact hbot
    · exact False.elim (hS_not_le_T ((Subgroup.subgroupOf_eq_top).1 htop))
  have hdisjST : Disjoint S T := by
    rw [Subgroup.disjoint_def]
    intro x hxS hxT
    have hxsub : (⟨x, hxS⟩ : S) ∈ T.subgroupOf S := hxT
    have hxbot : (⟨x, hxS⟩ : S) ∈ (⊥ : Subgroup S) := by simpa [hTS_bot] using hxsub
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
  have hquot_card : Nat.card (R ⧸ T) = p := by
    simpa [Subgroup.index_eq_card] using hTindex
  have hST_card : Nat.card S * Nat.card T = Nat.card R := by
    calc
      Nat.card S * Nat.card T = p * Nat.card T := by rw [hScard]
      _ = Nat.card (R ⧸ T) * Nat.card T := by rw [hquot_card]
      _ = Nat.card R := (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := T)).symm
  have hSTcomp : S.IsComplement' T :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hST_card hdisjST
  have hS_le_C : S ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact setLike_mul_comm (s := E) (hS_le_E ht) (hS_le_E hs)
  have hsup_le : S ⊔ subgroupCentralizerIn T S ≤ C := by
    refine sup_le hS_le_C ?_
    exact inf_le_right
  have hC_le_sup : C ≤ S ⊔ subgroupCentralizerIn T S := by
    intro x hxC
    have hxST : x ∈ S ⊔ T := by simp [hSTcomp.sup_eq_top]
    rcases (Subgroup.mem_sup_of_normal_right (s := S) (t := T)).1 hxST with
      ⟨s, hsS, t, htT, hst⟩
    have hsC : s ∈ C := hS_le_C hsS
    have htC : t ∈ C := by
      have hs_inv_mul_x : s⁻¹ * x ∈ C := C.mul_mem (C.inv_mem hsC) hxC
      have ht_eq : t = s⁻¹ * x := by
        calc
          t = s⁻¹ * (s * t) := by simp
          _ = s⁻¹ * x := by rw [hst]
      rw [ht_eq]
      exact hs_inv_mul_x
    have hs_sup : s ∈ S ⊔ subgroupCentralizerIn T S := Subgroup.mem_sup_left hsS
    have ht_sup : t ∈ S ⊔ subgroupCentralizerIn T S := Subgroup.mem_sup_right ⟨htT, htC⟩
    have hmul_sup : s * t ∈ S ⊔ subgroupCentralizerIn T S :=
      (S ⊔ subgroupCentralizerIn T S).mul_mem hs_sup ht_sup
    simpa [hst] using hmul_sup
  have hcent_eq : C = S ⊔ subgroupCentralizerIn T S := le_antisymm hC_le_sup hsup_le
  have hR1_cyclic : IsCyclic (subgroupCentralizerIn T S) := by
    by_contra hR1_ncyc
    let R₁ : Subgroup R := subgroupCentralizerIn T S
    letI : Fact (IsPGroup p R₁) := ⟨hpR.to_subgroup R₁⟩
    obtain ⟨U, _hUnorm, hUcard, hUelem⟩ := lemma_4_5_a (R := R₁) (p := p) hpodd hR1_ncyc
    let Umap : Subgroup R := U.map R₁.subtype
    have hUmap_elem : IsElementaryAbelian p Umap := by
      letI : IsElementaryAbelian p U := hUelem
      simpa [Umap] using IsElementaryAbelian.map_subtype (p := p) (K := R₁) (H := U)
    have hUmap_card : Nat.card Umap = p ^ 2 := by
      calc
        Nat.card Umap = Nat.card U := by
          symm
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective (f := R₁.subtype) U R₁.subtype_injective).toEquiv
        _ = p ^ 2 := hUcard
    have hUmap_le_T : Umap ≤ T := by
      exact (Subgroup.map_subtype_le U).trans inf_le_left
    have hUmap_le_C : Umap ≤ C := by
      exact (Subgroup.map_subtype_le U).trans inf_le_right
    have hdisjSU : Disjoint S Umap := hdisjST.mono_right hUmap_le_T
    have hSelem : IsElementaryAbelian p S := by
      letI : IsCyclic S := isCyclic_of_prime_card hScard
      exact isElementaryAbelian_of_prime_card_isCyclic (p := p) (G := S) hScard
    let D : Subgroup R := S ⊔ Umap
    have hDelem : IsElementaryAbelian p D := by
      letI : IsElementaryAbelian p S := hSelem
      letI : IsElementaryAbelian p Umap := hUmap_elem
      exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := S) (C := Umap) hUmap_le_C
    have hD_le_C : D ≤ C := sup_le hS_le_C hUmap_le_C
    have hDcard : Nat.card D = p ^ 3 := by
      letI : IsElementaryAbelian p D := hDelem
      letI : CommGroup D := IsMulCommutative.instCommGroup
      have hdisj_sub : Disjoint (S.subgroupOf D) (Umap.subgroupOf D) := by
        rw [Subgroup.disjoint_def]
        intro x hxS hxU
        apply Subtype.ext
        exact Subgroup.disjoint_def.mp hdisjSU hxS hxU
      have hsup_sub : S.subgroupOf D ⊔ Umap.subgroupOf D = ⊤ := by
        simpa [D] using
          (Subgroup.subgroupOf_sup (A := S) (A' := Umap) (B := D)
            le_sup_left le_sup_right).symm
      letI : (S.subgroupOf D).Normal := by infer_instance
      have hcompDU : (S.subgroupOf D).IsComplement' (Umap.subgroupOf D) :=
        isComplement'_of_disjoint_sup_eq_top_of_normal (S.subgroupOf D) (Umap.subgroupOf D)
          hdisj_sub hsup_sub
      have hmul := hcompDU.card_mul
      rw [natCard_subgroupOf_eq S D le_sup_left,
        natCard_subgroupOf_eq Umap D le_sup_right, hScard, hUmap_card] at hmul
      simpa [pow_succ', Nat.mul_assoc] using hmul.symm
    let Dsub : Subgroup C := D.subgroupOf C
    have hDsub_card : Nat.card Dsub = p ^ 3 := by
      rw [natCard_subgroupOf_eq D C hD_le_C, hDcard]
    have hDsub_elem : IsElementaryAbelian p Dsub :=
      IsElementaryAbelian.subgroupOf (p := p) hD_le_C
    letI : IsElementaryAbelian p Dsub := hDsub_elem
    have hC_rank_ge : 3 ≤ groupRank C :=
      groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
        (p := p) (G := C) (B := Dsub) hDsub_card
    exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hC_rank_ge hC_rank_le_two)
  exact ⟨hpR, Or.inr ⟨S, subgroupCentralizerIn T S, hScard, hR1_cyclic,
    hdisjST.mono_right inf_le_left, hcent_eq⟩⟩

public theorem CFSG.theorem_5_3
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R) :
    IsNarrowPGroup p R ↔ ∃ E : Subgroup R, E ∈ elementaryAbelianSubgroupsOfRank p 2 R ∧
      E ∈ maximalElementaryAbelianSubgroups p R := by
  constructor
  · intro hnarrow
    rcases hnarrow.2 with hsmall | ⟨R₀, R₁, hR₀card, hR₁cyc, hdisj, hcent⟩
    · exact False.elim ((by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hR hsmall))
    · exact narrow_forward_exists_rank_two_maximal (p := p) hpodd (R := R) hpR hR hR₀card hR₁cyc hdisj hcent
  · rintro ⟨E, hE, hEmax⟩
    exact rank_two_maximal_implies_narrow (p := p) hpodd (R := R) hpR hR hE hEmax
