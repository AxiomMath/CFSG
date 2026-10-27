module

public import CFSG.RankThree.Coprime.HighTwoRankOddKernel

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG
open scoped IsMulCommutative commutatorElement

theorem eq_one_of_conjNormal_eq_self {K : Type*} [Group K] {C D' : Subgroup K} (V : Subgroup K)
    (hVC : Disjoint V C) (hK₀C : centralizer (D' : Set K) ≤ C) (v : V)
    (hv : ∀ d : D', (v : K) * (d : K) * (v : K)⁻¹ = (d : K)) : v = 1 := by
  have hK₀mem : (v : K) ∈ centralizer (D' : Set K) := by
    rw [mem_centralizer_iff]
    intro x hx
    calc x * (v : K) = (v : K) * x * (v : K)⁻¹ * (v : K) := by rw [hv ⟨x, hx⟩]
      _ = (v : K) * x := by group
  exact Subtype.ext (Subgroup.disjoint_def.mp hVC v.2 (hK₀C hK₀mem))

theorem pRank_fixedPointSubgroup_le {K : Type*} [Group K] [Finite K] {r m : ℕ} [hr : Fact r.Prime]
    (D' : Subgroup K) [D'.Normal] (V : Subgroup K) (hV : IsElementaryAbelian 2 V)
    (a : V) (ha : a ≠ 1)
    (he : ∀ N : Subgroup K, CFSG.Open.IsTwoLocal N → CFSG.Open.pRank r N ≤ m) :
    letI : MulDistribMulAction V D' :=
      MulDistribMulAction.compHom D' ((MulAut.conjNormal (H := D')).comp V.subtype)
    pRank r (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D') ≤ m := by
  letI : MulDistribMulAction V D' :=
    MulDistribMulAction.compHom D' ((MulAut.conjNormal (H := D')).comp V.subtype)
  have hsmul : ∀ (v : V) (d : D'), ((v • d : D') : K) = (v : K) * (d : K) * (v : K)⁻¹ :=
    fun v d => MulAut.conjNormal_apply (v : K) d
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
    _ ≤ m := he N hloc

theorem criticalSubgroup_image_isPGroup {K : Type*} [Group K] {r : ℕ} [hr : Fact r.Prime]
    (R : Subgroup K) (hR : IsPGroup r R) (D : Subgroup R)
    (hDexp : ∀ x ∈ D, x ^ r = 1)
    (hDcomm : ⁅D, (⊤ : Subgroup R)⁆ ≤ D ⊓ centralizer (D : Set R)) :
    IsPGroup r (D.map R.subtype) ∧ Monoid.exponent (D.map R.subtype) ∣ r ∧
      (⊤ : Subgroup (D.map R.subtype)).lowerCentralSeries 2 = ⊥ := by
  refine ⟨hR.to_le (Subgroup.map_subtype_le D), ?_, ?_⟩
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hxx, ← map_pow, hDexp x' hx', map_one, Subgroup.coe_one]
  · apply lowerCentralSeries_two_eq_bot
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

theorem false_of_centralizer_le {K : Type*} [Group K] [Finite K]
    (m : ℕ) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (he : ∀ N : Subgroup K, CFSG.Open.IsTwoLocal N → CFSG.Open.pRank r N ≤ m)
    (C : Subgroup K) [C.Normal] (hCodd : Odd (Nat.card C))
    (U : Subgroup (K ⧸ C)) (hU : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 2 ^ (m + 2))
    (D' : Subgroup K) [D'.Normal] (hD'p : IsPGroup r D') (hD'exp : Monoid.exponent D' ∣ r)
    (hD'cl : (⊤ : Subgroup D').lowerCentralSeries 2 = ⊥)
    (hK₀C : centralizer (D' : Set K) ≤ C) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV, hVcard, hVC⟩ := exists_elementary_two_lift C hCodd U hU hUcard
  let act : MulDistribMulAction V D' :=
    MulDistribMulAction.compHom D' ((MulAut.conjNormal (H := D')).comp V.subtype)
  have hsmul : ∀ (v : V) (d : D'), ((v • d : D') : K) = (v : K) * (d : K) * (v : K)⁻¹ :=
    fun v d => MulAut.conjNormal_apply (v : K) d
  have hfaith : FaithfulSMul V D' := by
    refine ⟨fun {v₁ v₂} h => ?_⟩
    have hfix : ∀ d : D', (v₂⁻¹ * v₁) • d = d := by
      intro d
      rw [mul_smul, h d, ← mul_smul, inv_mul_cancel, one_smul]
    have h1 : v₂⁻¹ * v₁ = 1 := by
      refine eq_one_of_conjNormal_eq_self V hVC hK₀C (v₂⁻¹ * v₁) ?_
      intro d
      have h2 := congrArg Subtype.val (hfix ⟨d, d.2⟩)
      rwa [hsmul] at h2
    exact (inv_mul_eq_one.mp h1).symm
  have hm : ∀ a : V, a ≠ 1 →
      pRank r (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D') ≤ m :=
    fun a ha => pRank_fixedPointSubgroup_le D' V hV a ha he
  have h := class_two_involution_fixed_rank_bound (A := V) (hr.out.odd_of_ne_two hr2) hD'p
    hD'exp hD'cl (m + 2) m hVcard hm
  omega

theorem le_center_of_centralizer_map_eq_top {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    {r : ℕ} [hr : Fact r.Prime] (R : Subgroup K) [R.Normal]
    (D : Subgroup R) (hDfix : IsPGroup r (fixingSubgroup (MulAut R) (D : Set R)))
    (C K₀ : Subgroup K) [C.Normal] [K₀.Normal] (hCsolv : Group.IsSolvable C)
    (hK₀def : K₀ = centralizer ((D.map R.subtype : Subgroup K) : Set K))
    (htop : K₀.map (QuotientGroup.mk' C) = ⊤) : R ≤ center K := by
  classical
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
    have hk : k ∈ centralizer ((D.map R.subtype : Subgroup K) : Set K) := by
      rw [← hK₀def]
      exact hKK₀ k
    have h1 := mem_centralizer_iff.mp hk (d : K) ⟨d, hd, rfl⟩
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

theorem le_center_of_high_two_rank_of_local {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (m : ℕ) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (he : ∀ N : Subgroup K, CFSG.Open.IsTwoLocal N → CFSG.Open.pRank r N ≤ m)
    (C : Subgroup K) [C.Normal]
    (hCsolv : Group.IsSolvable C) (hCodd : Odd (Nat.card C)) (hsimple : IsSimpleGroup (K ⧸ C))
    (U : Subgroup (K ⧸ C)) (hU : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 2 ^ (m + 2))
    (R : Subgroup K) [R.Normal] (hR : IsPGroup r R) :
    R ≤ center K := by
  classical
  rcases subsingleton_or_nontrivial R with hRs | hRnt
  · intro x hx
    have hx1 : x = 1 := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : R) 1)
    rw [hx1]
    exact one_mem _
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hr2 hR
  obtain ⟨hD'p, hD'exp, hD'cl⟩ := criticalSubgroup_image_isPGroup R hR D hDexp hDcomm
  let D' : Subgroup K := D.map R.subtype
  have hD'n : D'.Normal := inferInstance
  let K₀ : Subgroup K := centralizer (D' : Set K)
  have hK₀n : K₀.Normal := inferInstance
  have : (K₀.map (QuotientGroup.mk' C)).Normal :=
    hK₀n.map (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₀.map (QuotientGroup.mk' C)) with hbot | htop
  · exfalso
    have hK₀C : K₀ ≤ C := by
      intro k hk
      have hmem : QuotientGroup.mk' C k ∈ K₀.map (QuotientGroup.mk' C) := ⟨k, hk, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff k).mp hmem
    exact false_of_centralizer_le m hr2 he C hCodd U hU hUcard D' hD'p hD'exp hD'cl hK₀C
  · exact le_center_of_centralizer_map_eq_top R D hDfix C K₀ hCsolv rfl htop

end CFSG.RankThree.Coprime
