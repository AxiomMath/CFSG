module

public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.GroupTheory.SteinbergBKClassTwoOddRankBound

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.Coprime
open scoped IsMulCommutative commutatorElement

universe u

theorem commutator_le_center_of_commutator_central {P : Type*} [Group P]
    (h : ∀ x y z : P, ⁅x, y⁆ * z = z * ⁅x, y⁆) : commutator P ≤ center P := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [mem_center_iff]
  intro z
  exact (h x y z).symm

theorem le_center_of_global_odd_rank {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (m : ℕ) (hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r K ≤ m) (C : Subgroup K) [C.Normal]
    (hCsolv : Group.IsSolvable C) (hCodd : Odd (Nat.card C)) (hsimple : IsSimpleGroup (K ⧸ C))
    (U : Subgroup (K ⧸ C)) (hU : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 2 ^ (m + 1))
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (R : Subgroup K) [R.Normal] (hR : IsPGroup r R) :
    R ≤ center K := by
  classical
  rcases subsingleton_or_nontrivial R with hRs | hRnt
  · intro x hx
    have hx1 : x = 1 := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : R) 1)
    rw [hx1]
    exact one_mem _
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hr2 hR
  set D' : Subgroup K := D.map R.subtype with hD'
  have hD'n : D'.Normal := inferInstance
  set K₀ := centralizer (D' : Set K) with hK₀
  have hK₀n : K₀.Normal := inferInstance
  have : (K₀.map (QuotientGroup.mk' C)).Normal :=
    hK₀n.map (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₀.map (QuotientGroup.mk' C)) with hbot | htop
  ·
    exfalso
    have hK₀C : K₀ ≤ C := by
      intro k hk
      have hmem : QuotientGroup.mk' C k ∈ K₀.map (QuotientGroup.mk' C) := ⟨k, hk, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff k).mp hmem
    obtain ⟨V, hV, hVcard, hVC⟩ := exists_elementary_two_lift C hCodd U hU hUcard
    have := hV
    have hD'exp : ∀ x : D', x ^ r = 1 := by
      intro x
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hxx, ← map_pow, hDexp x' hx', map_one, Subgroup.coe_one]
    have hD'cz : ∀ x y z : D', ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
      intro x y z
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp y.2
      obtain ⟨z', hz', hzz⟩ := Subgroup.mem_map.mp z.2
      have hc : ⁅x', y'⁆ ∈ centralizer (D : Set R) :=
        (hDcomm (Subgroup.commutator_mem_commutator hx' (mem_top y'))).2
      have hcz : z' * ⁅x', y'⁆ = ⁅x', y'⁆ * z' := mem_centralizer_iff.mp hc z' hz'
      have h1 := congrArg R.subtype hcz
      simp only [map_mul, commutatorElement_def, map_inv] at h1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv]
      rw [← hxx, ← hyy, ← hzz]
      exact h1.symm
    let act : MulDistribMulAction V D' :=
      MulDistribMulAction.compHom D' ((MulAut.conjNormal (H := D')).comp V.subtype)
    have hsmul : ∀ (v : V) (d : D'), ((v • d : D') : K) = (v : K) * d * (v : K)⁻¹ :=
      fun v d => MulAut.conjNormal_apply (v : K) d
    have hfaith : ∀ a : V, (∀ d : D', a • d = d) → a = 1 := by
      intro a hfix
      have hK₀mem : (a : K) ∈ K₀ := by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := congrArg Subtype.val (hfix ⟨x, hx⟩)
        rw [hsmul] at h1
        calc x * (a : K) = (a : K) * x * (a : K)⁻¹ * (a : K) := by rw [h1]
          _ = (a : K) * x := by group
      exact Subtype.ext (Subgroup.disjoint_def.mp hVC a.2 (hK₀C hK₀mem))
    have hcommV : ∀ a b : V, a * b = b * a := fun a b => mul_comm' a b
    have hsqV : ∀ a : V, a ^ 2 = 1 := fun a => Subtype.ext
      (by simpa using elemPow_eq_one_of_isElementaryAbelian (a : K) a.2)
    have hbound :=
      CFSG.RankThree.GroupTheory.SteinbergBK.elementary_two_action_class_two_global_odd_rank_bound
        hr.out hr2 hD'exp (commutator_le_center_of_commutator_central hD'cz) hcommV hsqV hfaith
    have hV2 : m + 1 ≤ CFSG.Assembly.pRank 2 (⊤ : Subgroup V) :=
      CFSG.SectionRank.le_pRank_of_injective (G := V) (p := 2) Nat.one_lt_two hcommV hsqV hVcard
        (MonoidHom.id V) Function.injective_id (H := ⊤) (by simp)
    have hDr : CFSG.Assembly.pRank r (⊤ : Subgroup D') ≤ m :=
      calc CFSG.Assembly.pRank r (⊤ : Subgroup D') = CFSG.Open.pRank r (⊤ : Subgroup D') := rfl
        _ ≤ CFSG.Open.pRank r (⊤ : Subgroup K) :=
            CFSG.SectionRank.pRank_top_le_of_injective hr.out.one_lt D'.subtype
              D'.subtype_injective
        _ = CFSG.pRank r K := (CFSG.SectionRank.pRank_eq_open_pRank_top r K).symm
        _ ≤ m := hrank r hr.out hr2
    omega
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' K₀).comp C.subtype) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective K₀ q
      have hk : QuotientGroup.mk' C k ∈ K₀.map (QuotientGroup.mk' C) := by
        rw [htop]
        exact mem_top _
      obtain ⟨k₀, hk₀, hkk⟩ := hk
      refine ⟨⟨k₀⁻¹ * k, QuotientGroup.eq.mp hkk⟩, ?_⟩
      change QuotientGroup.mk' K₀ (k₀⁻¹ * k) = QuotientGroup.mk' K₀ k
      have hk₀1 : QuotientGroup.mk' K₀ k₀ = 1 := (QuotientGroup.eq_one_iff k₀).mpr hk₀
      rw [map_mul, map_inv, hk₀1, inv_one, one_mul]
    have hKK₀ : ∀ k : K, k ∈ K₀ := by
      have : Group.IsSolvable (K ⧸ K₀) := Group.isSolvable_of_surjective hsurj
      have hsolv : Group.IsSolvable (QuotientGroup.mk' K₀).range := by
        rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective K₀)]
        infer_instance
      intro k
      exact (QuotientGroup.eq_one_iff k).mp (eq_one_of_isSolvable_range _ hsolv k)
    let g : K →* MulAut R := MulAut.conjNormal
    have hrange : g.range ≤ fixingSubgroup (MulAut R) (D : Set R) := by
      rintro _ ⟨k, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      change k * (d : K) * k⁻¹ = d
      have h1 := mem_centralizer_iff.mp (hKK₀ k) (d : K) ⟨d, hd, rfl⟩
      rw [← h1, mul_inv_cancel_right]
    have hgp : IsPGroup r g.range := hDfix.to_le hrange
    have hgs : Group.IsSolvable g.range := by
      have := hgp.isNilpotent
      infer_instance
    intro x hx
    rw [mem_center_iff]
    intro k
    have h1 := congrArg (fun φ : MulAut R => ((φ ⟨x, hx⟩ : R) : K))
      (eq_one_of_isSolvable_range g hgs k)
    simp only [g, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * x = k * x * k⁻¹ * k := by group
      _ = x * k := by rw [h1]

theorem global_odd_rank_simple_odd_kernel_centralization {K : Type*} [Group K] [Finite K] (m : ℕ)
    (hK : Group.IsPerfect K) (hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r K ≤ m)
    (C : Subgroup K) [C.Normal] (hCnil : Group.IsNilpotent C) (hCodd : Odd (Nat.card C))
    (hsimple : IsSimpleGroup (K ⧸ C))
    (hU : ∃ U : Subgroup (K ⧸ C), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 1)) :
    C ≤ center K := by
  obtain ⟨U, hUel, hUcard⟩ := hU
  have hCsolv : Group.IsSolvable C := by
    have := hCnil
    infer_instance
  have hC : C = (⨆ p ∈ (Nat.card C).primeFactors, ((default : Sylow p C) : Subgroup C)).map
      C.subtype := by
    rw [Sylow.iSup_sylow_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hC, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun p hp => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hCodd)
      (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  have : (pCore p K).Normal := pCore_normal
  exact (Sylow.map_le_pCore inferInstance hCnil p default).trans
    (le_center_of_global_odd_rank m hrank C hCsolv hCodd hsimple U hUel hUcard hp2 (pCore p K)
      pCore_isPGroup)

theorem even_center_section_global_rank_central_cover {G : Type u} [Group G] [Finite G] (m : ℕ)
    (he : CFSG.Assembly.evenRank G ≤ m) {M : Type*} [Group M] [Finite M] (hM : IsQuasisimple M)
    (hZ : Even (Nat.card (center M)))
    (hS : ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 1))
    (H : Subgroup G) (π : H →* M) (hπ : Function.Surjective π) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y) (_ : Group.IsPerfect Y)
      (φ : Y →* M ⧸ center M), Function.Surjective φ ∧ φ.ker ≤ center Y ∧
        ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r Y ≤ m := by
  classical
  obtain ⟨K, -, hKmin⟩ := Finite.exists_le_minimal (p := fun K : Subgroup H => K.map π = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective π hπ])
  set πK : K →* M := π.comp K.subtype with hπK
  have hπKs : Function.Surjective πK := by
    intro x
    have hx : x ∈ K.map π := by
      rw [hKmin.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin : ∀ Y : Subgroup K, Y ≠ ⊤ → Y.map πK ≠ ⊤ := by
    intro Y hY hYmap
    apply hY
    have h1 : (Y.map K.subtype).map π = ⊤ := by
      rw [Subgroup.map_map]
      exact hYmap
    have h2 := hKmin.le_of_le h1 (Subgroup.map_subtype_le Y)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  obtain ⟨hKperf, hCn, hCnil, hCsyl, -, -, -, -, -⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover (layer_eq_top_of_isQuasisimple hM) πK hπKs hmin
  set C : Subgroup K := (center M).comap πK with hC
  have hCZ : Function.Surjective ((πK.comp C.subtype).codRestrict (center M)
      (fun x => x.2)) := by
    intro z
    obtain ⟨k, hk⟩ := hπKs z
    exact ⟨⟨k, show πK k ∈ center M by rw [hk]; exact z.2⟩, Subtype.ext hk⟩
  have h2C : 2 ∣ Nat.card C :=
    (even_iff_two_dvd.mp hZ).trans (Subgroup.card_dvd_of_surjective hCZ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Sylow 2 C := default with hT
  set R : Subgroup K := (T : Subgroup C).map C.subtype with hR
  have hRn : R.Normal := hCsyl 2 T
  have hRp : IsPGroup 2 R := T.isPGroup'.map _
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  have hRne : R ≠ ⊥ := by
    rw [hR, Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact T.ne_bot_of_dvd_card h2C
  set ι : K →* G := H.subtype.comp K.subtype with hι
  have hιinj : Function.Injective ι := H.subtype_injective.comp K.subtype_injective
  set N := normalizer ((R.map ι : Subgroup G) : Set G) with hN
  have hloc : CFSG.Open.IsTwoLocal N := by
    refine ⟨R.map ι, ?_, hRp.map ι, rfl⟩
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hιinj]
    exact hRne
  have hKN : (⊤ : Subgroup K).map ι ≤ N := by
    rintro _ ⟨k, -, rfl⟩
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨k * x * k⁻¹, hRn.conj_mem x hx k, by simp [map_mul, map_inv]⟩
    · rintro ⟨x, hx, hxg⟩
      refine ⟨k⁻¹ * x * k, by simpa using hRn.conj_mem x hx k⁻¹, ?_⟩
      have h := congrArg (fun y => (ι k)⁻¹ * y * ι k) hxg
      simp only [map_mul, map_inv] at h ⊢
      rw [h]
      group
  have hKrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r K ≤ m := by
    intro r hr hr2
    calc CFSG.pRank r K = CFSG.Open.pRank r (⊤ : Subgroup K) :=
          CFSG.SectionRank.pRank_eq_open_pRank_top r K
      _ ≤ CFSG.Open.pRank r ((⊤ : Subgroup K).map ι) :=
          CFSG.SectionRank.pRank_le_map hr.one_lt ι hιinj ⊤
      _ ≤ CFSG.Open.pRank r N := CFSG.SectionRank.pRank_mono hr.one_lt hKN
      _ ≤ CFSG.Open.evenRank G :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 N hloc
      _ = CFSG.Assembly.evenRank G := rfl
      _ ≤ m := he
  have hRr : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card R := by
    intro r hr hr2 hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  have hYrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (K ⧸ R) ≤ m := fun r hr hr2 => by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr R
      (hRr r hr hr2)]
    exact hKrank r hr hr2
  have hRker : R ≤ ((QuotientGroup.mk' (center M)).comp πK).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hRC hx
  set φ : K ⧸ R →* M ⧸ center M :=
    QuotientGroup.lift R ((QuotientGroup.mk' (center M)).comp πK) hRker with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center M) q
    obtain ⟨k, rfl⟩ := hπKs x
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hφker : φ.ker = C.map (QuotientGroup.mk' R) := by
    rw [hφ, QuotientGroup.ker_lift, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  refine ⟨K ⧸ R, inferInstance, inferInstance, inferInstance, φ, hφs, ?_, hYrank⟩
  have hYperf : Group.IsPerfect (K ⧸ R) := inferInstance
  have hkernil : Group.IsNilpotent φ.ker := by
    rw [hφker]
    exact Group.nilpotent_of_surjective _ ((QuotientGroup.mk' R).subgroupMap_surjective C)
  have hkerodd : Odd (Nat.card φ.ker) := by
    rw [hφker, CFSG.natCard_map_mk'_eq]
    have hsub : R.subgroupOf C = (T : Subgroup C) := by
      rw [hR, subgroupOf, comap_map_eq_self_of_injective C.subtype_injective]
    rw [hsub, ← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp T.not_dvd_index)
  set iso := QuotientGroup.quotientKerEquivOfSurjective φ hφs with hiso
  have : IsSimpleGroup (M ⧸ center M) := hM.2.1
  have hsimple : IsSimpleGroup ((K ⧸ R) ⧸ φ.ker) := iso.isSimpleGroup
  obtain ⟨U, hU, hUcard⟩ := hS
  obtain ⟨hU', hUcard'⟩ := isElementaryAbelian_map_mulEquiv iso.symm hU
  exact global_odd_rank_simple_odd_kernel_centralization m hYperf hYrank φ.ker hkernil hkerodd
    hsimple ⟨_, hU', hUcard'.trans hUcard⟩

end CFSG.RankThree.PartOne
