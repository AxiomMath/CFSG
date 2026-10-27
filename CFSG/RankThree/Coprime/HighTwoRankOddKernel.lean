module

public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG
open scoped IsMulCommutative commutatorElement

theorem eq_one_of_isSolvable_range {K H : Type*} [Group K] [Group H] [Group.IsPerfect K]
    (f : K →* H) (hs : Group.IsSolvable f.range) (k : K) : f k = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases subsingleton_or_nontrivial f.range with h | h
  · exact congrArg Subtype.val (Subsingleton.elim (⟨f k, k, rfl⟩ : f.range) 1)
  · exact absurd hs (Group.IsPerfect.not_isSolvable f.range)

theorem lowerCentralSeries_two_eq_bot {P : Type*} [Group P]
    (h : ∀ x y z : P, ⁅x, y⁆ * z = z * ⁅x, y⁆) : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ := by
  have hle : commutator P ≤ center P := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [mem_center_iff]
    intro z
    exact (h x y z).symm
  have h2 : ⁅center P, (⊤ : Subgroup P)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one]
  exact le_bot_iff.mp (h2 ▸ Subgroup.commutator_mono hle le_rfl)

theorem exists_elementary_two_lift {K : Type*} [Group K] [Finite K] (C : Subgroup K) [C.Normal]
    (hCodd : Odd (Nat.card C)) (U : Subgroup (K ⧸ C)) (hU : IsElementaryAbelian 2 U) {n : ℕ}
    (hUcard : Nat.card U = 2 ^ n) :
    ∃ V : Subgroup K, IsElementaryAbelian 2 V ∧ Nat.card V = 2 ^ n ∧ Disjoint V C := by
  classical
  set W := U.comap (QuotientGroup.mk' C) with hW
  have hWcard : Nat.card W = 2 ^ n * Nat.card C := by
    have h1 := W.card_mul_index
    have h2 := U.card_mul_index
    have h3 : W.index = U.index :=
      Subgroup.index_comap_of_surjective U (QuotientGroup.mk'_surjective C)
    have h4 := C.card_eq_card_quotient_mul_card_subgroup
    have hi : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [h3] at h1
    rw [hUcard] at h2
    have h5 : Nat.card W * U.index = 2 ^ n * Nat.card C * U.index := by
      rw [h1, h4, ← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_right hi h5
  let S : Sylow 2 W := default
  set V : Subgroup K := (S : Subgroup W).map W.subtype with hV
  have hC2 : ¬ 2 ∣ Nat.card C := fun h => (Nat.not_even_iff_odd.mpr hCodd) (even_iff_two_dvd.mpr h)
  have hVcard : Nat.card V = 2 ^ n := by
    rw [hV, Subgroup.card_map_of_injective W.subtype_injective, S.card_eq_multiplicity, hWcard,
      Nat.factorization_mul (by positivity) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hC2, add_zero]
  have hdisj : Disjoint V C := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hVcard]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hCodd)
  have hVW : V ≤ W := Subgroup.map_subtype_le _
  have hmk : ∀ x ∈ V, ∀ y ∈ V, QuotientGroup.mk' C x = QuotientGroup.mk' C y → x = y := by
    intro x hx y hy hxy
    have h1 : y⁻¹ * x ∈ C := QuotientGroup.eq.mp hxy.symm
    have h2 : y⁻¹ * x ∈ V := V.mul_mem (V.inv_mem hy) hx
    exact (inv_mul_eq_one.mp (Subgroup.disjoint_def.mp hdisj h2 h1)).symm
  have := hU
  have hcomm : IsMulCommutative V := ⟨⟨fun a b => by
    apply Subtype.ext
    apply hmk _ (V.mul_mem a.2 b.2) _ (V.mul_mem b.2 a.2)
    have ha : QuotientGroup.mk' C a ∈ U := hVW a.2
    have hb : QuotientGroup.mk' C b ∈ U := hVW b.2
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : U) ⟨_, hb⟩)⟩⟩
  have hexp : Monoid.exponent V ∣ 2 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro a
    apply Subtype.ext
    apply hmk _ (V.pow_mem a.2 2) _ V.one_mem
    have ha : QuotientGroup.mk' C a ∈ U := hVW a.2
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (A := U) _ ha
  exact ⟨V, { toIsMulCommutative := hcomm, exponent_dvd_p := hexp }, hVcard, hdisj⟩


theorem le_center_of_high_two_rank {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (m : ℕ) (he : CFSG.Assembly.evenRank K ≤ m) (C : Subgroup K) [C.Normal]
    (hCsolv : Group.IsSolvable C) (hCodd : Odd (Nat.card C)) (hsimple : IsSimpleGroup (K ⧸ C))
    (U : Subgroup (K ⧸ C)) (hU : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 2 ^ (m + 2))
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
    have hD'p : IsPGroup r D' := hR.to_le (Subgroup.map_subtype_le D)
    have hD'exp : Monoid.exponent D' ∣ r := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hxx, ← map_pow, hDexp x' hx', map_one, Subgroup.coe_one]
    have hD'cl : (⊤ : Subgroup D').lowerCentralSeries 2 = ⊥ := by
      apply lowerCentralSeries_two_eq_bot
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
    have hfaith : FaithfulSMul V D' := by
      refine ⟨fun {v₁ v₂} h => ?_⟩
      have hfix : ∀ d : D', (v₂⁻¹ * v₁) • d = d := by
        intro d
        rw [mul_smul, h d, ← mul_smul, inv_mul_cancel, one_smul]
      have hK₀mem : ((v₂⁻¹ * v₁ : V) : K) ∈ K₀ := by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := congrArg Subtype.val (hfix ⟨x, hx⟩)
        rw [hsmul] at h1
        calc x * ((v₂⁻¹ * v₁ : V) : K) =
            ((v₂⁻¹ * v₁ : V) : K) * x * ((v₂⁻¹ * v₁ : V) : K)⁻¹ * ((v₂⁻¹ * v₁ : V) : K) := by
              rw [h1]
          _ = ((v₂⁻¹ * v₁ : V) : K) * x := by group
      have h1 := Subgroup.disjoint_def.mp hVC (v₂⁻¹ * v₁).2 (hK₀C hK₀mem)
      have h2 : v₂⁻¹ * v₁ = 1 := Subtype.ext h1
      exact (inv_mul_eq_one.mp h2).symm
    have hm : ∀ a : V, a ≠ 1 →
        pRank r (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D') ≤ m := by
      intro a ha
      set F := CFSG.fixedPointSubgroup (Subgroup.zpowers a) D' with hF
      let ι : F →* K := D'.subtype.comp F.subtype
      have hι : Function.Injective ι := D'.subtype_injective.comp F.subtype_injective
      set N := normalizer ((zpowers (a : K) : Subgroup K) : Set K) with hN
      have hιN : (⊤ : Subgroup F).map ι ≤ N := by
        rintro _ ⟨f, -, rfl⟩
        have hf : a • (f : D') = f := f.2 ⟨a, mem_zpowers a⟩
        have hf' : (a : K) * ι f * (a : K)⁻¹ = ι f := by
          have h1 := congrArg Subtype.val hf
          rw [hsmul] at h1
          exact h1
        have hc : ι f ∈ centralizer ((zpowers (a : K) : Subgroup K) : Set K) := by
          rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_iff]
          rintro _ rfl
          calc (a : K) * ι f = (a : K) * ι f * (a : K)⁻¹ * a := by group
            _ = ι f * a := by rw [hf']
        exact centralizer_le_normalizer _ hc
      have ha1 : (a : K) ≠ 1 := fun h => ha (Subtype.ext h)
      have ha2 : (a : K) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (a : K) a.2
      have hloc : CFSG.Open.IsTwoLocal N := by
        refine ⟨zpowers (a : K), ?_, ?_, rfl⟩
        · intro h
          apply ha1
          have hmem : (a : K) ∈ zpowers (a : K) := mem_zpowers _
          rwa [h, Subgroup.mem_bot] at hmem
        · exact IsPGroup.of_card (n := 1)
            (by rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1, pow_one])
      calc pRank r F = CFSG.Open.pRank r (⊤ : Subgroup F) :=
            CFSG.SectionRank.pRank_eq_open_pRank_top r F
        _ ≤ CFSG.Open.pRank r ((⊤ : Subgroup F).map ι) :=
            CFSG.SectionRank.pRank_le_map hr.out.one_lt ι hι ⊤
        _ ≤ CFSG.Open.pRank r N := CFSG.SectionRank.pRank_mono hr.out.one_lt hιN
        _ ≤ CFSG.Open.evenRank K :=
            CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr.out hr2 N hloc
        _ = CFSG.Assembly.evenRank K := rfl
        _ ≤ m := he
    have h := class_two_involution_fixed_rank_bound (A := V) (hr.out.odd_of_ne_two hr2) hD'p
      hD'exp hD'cl (m + 2) m hVcard hm
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

theorem high_two_rank_simple_odd_kernel_centralization {K : Type*} [Group K] [Finite K] (m : ℕ)
    (hK : Group.IsPerfect K) (he : CFSG.Assembly.evenRank K ≤ m) (C : Subgroup K) [C.Normal]
    (hCnil : Group.IsNilpotent C) (hCodd : Odd (Nat.card C)) (hsimple : IsSimpleGroup (K ⧸ C))
    (_hnonab : ∃ a b : K ⧸ C, a * b ≠ b * a)
    (hU : ∃ U : Subgroup (K ⧸ C), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 2)) :
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
    (le_center_of_high_two_rank m he C hCsolv hCodd hsimple U hUel hUcard hp2 (pCore p K)
      pCore_isPGroup)

end CFSG.RankThree.Coprime
