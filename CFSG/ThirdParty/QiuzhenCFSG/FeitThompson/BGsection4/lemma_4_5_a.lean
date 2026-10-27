module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_3_b

namespace CFSG
end CFSG
open CFSG

/-! # Infrastructure for BG Section 4, Lemma 4.5 -/

section Main

public theorem CFSG.isElementaryAbelian_of_card_eq_p_sq_of_forall_pow_eq_one
    {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card S = p ^ 2) (hpow : ∀ x : S, x ^ p = 1) :
    IsElementaryAbelian p S := by
  have hcyc : IsCyclic (S ⧸ Subgroup.center S) :=
    IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq (p := p) (G := S) hcard
  letI : IsMulCommutative S := lemma_4_1 (G := S) hcyc
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := ?_
  }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hpow

public theorem CFSG.exists_nontrivial_center_mem_normal_local
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal] [Nontrivial N]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] :
    ∃ x : N, x ≠ 1 ∧ (x : G) ∈ Subgroup.center G := by
  let hGconj : IsPGroup p (ConjAct G) :=
    (Fact.out : IsPGroup p G).of_equiv ConjAct.toConjAct
  have hN_p : IsPGroup p N := (Fact.out : IsPGroup p G).to_subgroup N
  obtain ⟨n, hn_pos, hcardN⟩ := hN_p.nontrivial_iff_card.mp (by infer_instance : Nontrivial N)
  have hdvd : p ∣ Nat.card N := by
    rw [hcardN]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn_pos)
  have hone_fixed : ((1 : N) : N) ∈ MulAction.fixedPoints (ConjAct G) N := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨x, hxfix, hxne⟩ :=
    hGconj.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := N) hdvd hone_fixed
  refine ⟨x, (fun h => hxne h.symm), ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hxg : (ConjAct.toConjAct g) • x = x :=
    (MulAction.mem_fixedPoints.mp hxfix) (ConjAct.toConjAct g)
  have hxg' : (ConjAct.toConjAct g) • (x : G) = x := by
    exact Subtype.ext_iff.mp hxg
  have hconj : g * (x : G) * g⁻¹ = x := by
    simpa [ConjAct.smul_def] using hxg'
  have hmul : g * (x : G) = x * g := by
    simpa [mul_assoc] using congrArg (fun t => t * g) hconj
  simpa [eq_comm] using hmul

public theorem CFSG.normal_subgroup_card_eq_prime_le_center
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)]
    (N : Subgroup G) [N.Normal] (hNcard : Nat.card N = p) :
    N ≤ Subgroup.center G := by
  letI : Nontrivial N :=
    Finite.one_lt_card_iff_nontrivial.mp (hNcard ▸ (Fact.out : Nat.Prime p).one_lt)
  obtain ⟨x, hx_ne, hx_center⟩ :=
    exists_nontrivial_center_mem_normal_local (N := N) (p := p)
  intro y hy
  have hy_zpow : (⟨y, hy⟩ : N) ∈ Subgroup.zpowers x :=
    mem_zpowers_of_prime_card (G := N) (p := p) (h := hNcard) (g := x) (g' := ⟨y, hy⟩) hx_ne
  rcases Subgroup.mem_zpowers_iff.mp hy_zpow with ⟨n, hn⟩
  have hy_eq : y = (((x : N) ^ n : N) : G) := by
    simpa using congrArg Subtype.val hn.symm
  rw [hy_eq]
  simpa using (Subgroup.center G).zpow_mem hx_center n

public theorem CFSG.exists_central_normal_subgroup_card_eq_prime_of_nontrivial_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)]
    (N : Subgroup G) [N.Normal] (hN_ne_bot : N ≠ ⊥) :
    ∃ Z : Subgroup G, Z.Normal ∧ Z ≤ N ∧ Nat.card Z = p ∧ Z ≤ Subgroup.center G := by
  have hNp : IsPGroup p N := (Fact.out : IsPGroup p G).to_subgroup N
  letI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hN_ne_bot
  obtain ⟨n, hn_pos, hNcard_pow⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := N) hNp).mp inferInstance
  obtain ⟨Z, hZ_normal, hZ_le_N, hZ_card_pow⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := G) (p := p) (N := N) inferInstance
      hNcard_pow 1 (Nat.succ_le_of_lt hn_pos)
  have hZ_card : Nat.card Z = p := by
    simpa using hZ_card_pow
  refine ⟨Z, hZ_normal, hZ_le_N, hZ_card, ?_⟩
  letI : Z.Normal := hZ_normal
  exact normal_subgroup_card_eq_prime_le_center (G := G) (p := p) (N := Z) hZ_card


end Main

section Main

private theorem CFSG.lemma_4_5_a_preimage_case {R : Type*} [Group R] [Finite R] {p : ℕ}
    [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)] (Z : Subgroup R) [Z.Normal]
    (hZ_le_center : Z ≤ Subgroup.center R) (hZcard : Nat.card Z = p ^ 1)
    (Sbar : Subgroup (R ⧸ Z)) [Sbar.Normal] (hSbar_card : Nat.card Sbar = p ^ 2)
    (hSbar_elem : IsElementaryAbelian p Sbar) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  let q : R →* R ⧸ Z := QuotientGroup.mk' Z
  let T : Subgroup R := Sbar.comap q
  have hT_normal : T.Normal := by
    simpa [T, q] using (inferInstance : (Sbar.comap (QuotientGroup.mk' Z)).Normal)
  letI : T.Normal := hT_normal
  have hker_le_T : q.ker ≤ T := by
    simpa [T] using (Subgroup.ker_le_comap (f := q) (H := Sbar))
  let ZT : Subgroup T := q.ker.subgroupOf T
  have hZT_card : Nat.card ZT = p ^ 1 := by
    calc
      Nat.card ZT = Nat.card q.ker := by
        exact natCard_subgroupOf_eq _ _ hker_le_T
      _ = Nat.card Z := by simp [q, QuotientGroup.ker_mk']
      _ = p ^ 1 := hZcard
  have hT_card : Nat.card T = p ^ 3 := by
    have hquot_card : Nat.card (T ⧸ ZT) = p ^ 2 := by
      simpa [T, ZT, q] using
        (card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective Z)
          (H := Sbar)).trans hSbar_card
    calc
      Nat.card T = Nat.card (T ⧸ ZT) * Nat.card ZT := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := ZT))
      _ = p ^ 2 * p ^ 1 := by rw [hquot_card, hZT_card]
      _ = p ^ 3 := by ring_nf
  have hTmap_eq : T.map q = Sbar := by
    simpa [T] using (Subgroup.map_comap_eq_self_of_surjective (f := q)
      (h := QuotientGroup.mk'_surjective Z) Sbar)
  let qT : T →* T.map q := q.subgroupMap T
  have hTmap_comm : IsMulCommutative (T.map q) := by
    rw [hTmap_eq]
    exact hSbar_elem.toIsMulCommutative
  have hder_le_ZT : _root_.commutator T ≤ ZT := by
    letI : IsMulCommutative (T.map q) := hTmap_comm
    letI : CommGroup ↥qT.range := IsMulCommutative.instCommGroup
    have hquot_comm : IsMulCommutative (T ⧸ qT.ker) := by
      let e : T ⧸ qT.ker ≃* qT.range := QuotientGroup.quotientKerEquivRange qT
      letI : CommGroup (T ⧸ qT.ker) := e.toMonoidHom.commGroupOfInjective e.injective
      infer_instance
    have hder_le_ker : _root_.commutator T ≤ qT.ker := by
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := qT.ker)).1 hquot_comm
    simpa [qT, ZT, Subgroup.ker_subgroupMap] using hder_le_ker
  have hZT_le_centerT : ZT ≤ Subgroup.center T := by
    intro z hz
    have hzZ : ((z : T) : R) ∈ Z := by
      simpa [ZT, q, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] using hz
    have hzcenter : ((z : T) : R) ∈ Subgroup.center R := hZ_le_center hzZ
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hzcenter) (t : R)
  have hclassT : NilpotencyClassLe 2 T := by
    have hcomm_sub : _root_.commutator T ≤ Subgroup.center T := hder_le_ZT.trans hZT_le_centerT
    have hL1_le_center : (⊤ : Subgroup T).lowerCentralSeries 1 ≤ Subgroup.center T := by
      simpa only [Subgroup.top_lowerCentralSeries_one] using hcomm_sub
    have hL2_bot : (⊤ : Subgroup T).lowerCentralSeries 2 = ⊥ := by
      simpa [Nat.succ_eq_add_one] using
        (Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup T) (n := 1) hL1_le_center)
    have hnil : Group.IsNilpotent T :=
      (Subgroup.nilpotent_iff_lowerCentralSeries (G := T)).2 ⟨2, hL2_bot⟩
    letI : Group.IsNilpotent T := hnil
    have hclass : Group.nilpotencyClass T ≤ 2 :=
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := T)).1 hL2_bot
    unfold NilpotencyClassLe
    exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := T)).2 hclass
  let ΩT : Subgroup T := omega₁ (G := T) (p := p)
  have hZT_le_omega : ZT ≤ ΩT := by
    intro z hz
    refine Subgroup.subset_closure ?_
    have hz_pow : (z : T) ^ p = 1 := by
      have : (⟨z, hz⟩ : ZT) ^ Nat.card ZT = 1 := by
        simp
      simpa [hZT_card] using congrArg Subtype.val this
    simpa [omega₁, omega, pow_one] using hz_pow
  have hder_le_omega : _root_.commutator T ≤ ΩT := hder_le_ZT.trans hZT_le_omega
  haveI : Fact (IsPGroup p T) := ⟨(Fact.out : IsPGroup p R).to_subgroup T⟩
  obtain ⟨φ, hφ⟩ := proposition_4_3_b (R := T) (p := p) hpodd (Or.inl hclassT) hder_le_omega
  have hOmega_eq_ker : ΩT = φ.ker := by
    apply le_antisymm
    · intro x hx
      change φ x = 1
      refine Subgroup.closure_induction (k := {z : T | z ^ (p ^ 1) = 1}) (x := x) ?_ ?_ ?_ ?_ hx
      · intro z hz
        simpa [hφ z, pow_one] using hz
      · simp
      · intro a b _ _ ha hb
        simp [MonoidHom.map_mul, ha, hb]
      · intro a _ ha
        simp [MonoidHom.map_inv, ha]
    · intro x hx
      refine Subgroup.subset_closure ?_
      have hxpow : x ^ p = 1 := by
        simpa [hφ x, MonoidHom.mem_ker] using hx
      simpa [omega₁, omega, pow_one] using hxpow
  have hOmegaT_card_eq_ker : Nat.card ΩT = Nat.card φ.ker := by
    simp [hOmega_eq_ker]
  have hphi_range_le_ZT : φ.range ≤ ZT := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have hxpow_one : (qT x) ^ p = 1 := by
      let xbar : Sbar := ⟨q x, x.2⟩
      have hxbar_pow : xbar ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p Sbar) xbar
      apply Subtype.ext
      simpa [qT] using congrArg Subtype.val hxbar_pow
    have hxker : x ^ p ∈ qT.ker := by
      rw [MonoidHom.mem_ker]
      simpa [MonoidHom.map_pow] using hxpow_one
    simpa [hφ x, qT, ZT, Subgroup.ker_subgroupMap] using hxker
  have hphi_range_le_p : Nat.card φ.range ≤ p ^ 1 := by
    exact (Subgroup.card_le_of_le hphi_range_le_ZT).trans_eq hZT_card
  have hT_card_expr : Nat.card T = Nat.card φ.range * Nat.card φ.ker := by
    have hquot_card : Nat.card (T ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    calc
      Nat.card T = Nat.card (T ⧸ φ.ker) * Nat.card φ.ker := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker))
      _ = Nat.card φ.range * Nat.card φ.ker := by rw [hquot_card]
  have hOmegaT_big : p ^ 2 ≤ Nat.card ΩT := by
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hmul : p ^ 3 ≤ p ^ 1 * Nat.card φ.ker := by
      calc
        p ^ 3 = Nat.card φ.range * Nat.card φ.ker := by rw [← hT_card, hT_card_expr]
        _ ≤ p ^ 1 * Nat.card φ.ker := Nat.mul_le_mul_right _ hphi_range_le_p
    have hcancel : p ^ 2 ≤ Nat.card φ.ker := by
      have hmul' : p * p ^ 2 ≤ p * Nat.card φ.ker := by
        simpa [pow_succ, pow_one, mul_assoc] using hmul
      exact Nat.le_of_mul_le_mul_left hmul' hp_pos
    simpa [hOmegaT_card_eq_ker] using hcancel
  let Ω : Subgroup R := ΩT.map T.subtype
  have hΩ_normal : Ω.Normal := by
    letI : ΩT.Characteristic := omega₁_characteristic T
    simpa [Ω] using (inferInstance : (ΩT.map T.subtype).Normal)
  letI : Ω.Normal := hΩ_normal
  have hΩ_card_eq : Nat.card Ω = Nat.card ΩT := by
    exact Subgroup.card_map_of_injective (f := T.subtype) Subtype.coe_injective
  have hΩ_p : IsPGroup p Ω := (Fact.out : IsPGroup p R).to_subgroup Ω
  obtain ⟨m, hmΩ⟩ := IsPGroup.iff_card.mp hΩ_p
  have hm_ge_two : 2 ≤ m := by
    have hΩ_big : p ^ 2 ≤ Nat.card Ω := by simpa [hΩ_card_eq] using hOmegaT_big
    have hpow : p ^ 2 ≤ p ^ m := by simpa [hmΩ] using hΩ_big
    exact (Nat.pow_le_pow_iff_right (show 1 < p from (Fact.out : Nat.Prime p).one_lt)).1 hpow
  obtain ⟨K, hK_normal, hK_le_Ω, hKcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p) Ω inferInstance hmΩ 2 hm_ge_two
  letI : K.Normal := hK_normal
  have hOmegaT_pow : ∀ x : ΩT, ((x : T) : R) ^ p = 1 := by
    intro x
    have hxker : (x : T) ∈ φ.ker := by simpa [hOmega_eq_ker] using x.2
    have hxpowT : (x : T) ^ p = 1 := by
      simpa [hφ (x : T), MonoidHom.mem_ker] using hxker
    simpa using congrArg Subtype.val hxpowT
  have hKpow : ∀ y : K, y ^ p = 1 := by
    intro y
    apply Subtype.ext
    change ((y : R) ^ p = 1)
    have hyΩ : (y : R) ∈ Ω := hK_le_Ω y.2
    rcases Subgroup.mem_map.mp hyΩ with ⟨x, hxΩT, hxy⟩
    simpa [← hxy] using hOmegaT_pow ⟨x, hxΩT⟩
  have hKcyc : IsCyclic (K ⧸ Subgroup.center K) :=
    IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq (p := p) (G := K) hKcard
  letI : IsMulCommutative K := lemma_4_1 (G := K) hKcyc
  refine ⟨K, hK_normal, hKcard, ?_⟩
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := ?_
  }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hKpow

private theorem CFSG.lemma_4_5_a_cyclic_case {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (Z : Subgroup R) [Z.Normal] (hZ_le_center : Z ≤ Subgroup.center R)
    (hZcard : Nat.card Z = p ^ 1) (hQcyc : IsCyclic (R ⧸ Z)) (hncyc : ¬ IsCyclic R) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  obtain ⟨q0, hq0⟩ := (isCyclic_iff_exists_zpowers_eq_top).1 hQcyc
  obtain ⟨x, hxq0⟩ := Quotient.exists_rep q0
  let q : R →* R ⧸ Z := QuotientGroup.mk' Z
  let C : Subgroup R := Subgroup.zpowers x
  have hxq0' : q x = q0 := by simpa [q] using hxq0
  have hq0x : Subgroup.zpowers (q x) = ⊤ := by
    rw [hxq0']
    exact hq0
  have hCmap_top : C.map q = ⊤ := by
    calc
      C.map q = Subgroup.zpowers (q x) := by
        simp [C, q]
      _ = ⊤ := hq0x
  have hCZ_top : C ⊔ Z = ⊤ := by
    apply (Subgroup.eq_top_iff' (H := C ⊔ Z)).2
    intro r
    have hqr : q r ∈ C.map q := by simp [hCmap_top]
    rcases Subgroup.mem_map.mp hqr with ⟨c, hcC, hqc⟩
    have hker : c⁻¹ * r ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) (x := c⁻¹ * r)).1
      have : (q c)⁻¹ * q r = 1 := by
        simpa using congrArg (fun t => t⁻¹ * q r) hqc
      simpa [q, MonoidHom.map_mul] using this
    exact (Subgroup.mem_sup_of_normal_right).2 ⟨c, hcC, c⁻¹ * r, hker, by simp⟩
  have hZ_not_le_C : ¬ Z ≤ C := by
    intro hZleC
    have hC_top : C = ⊤ := by
      simpa [sup_eq_left.mpr hZleC] using hCZ_top
    exact hncyc <|
      (isCyclic_iff_exists_zpowers_eq_top).2 ⟨x, by simpa [C] using hC_top⟩
  let π : R ⧸ Z →* R ⧸ Subgroup.center R :=
    QuotientGroup.map Z (Subgroup.center R) (MonoidHom.id R) hZ_le_center
  have hπ_surj : Function.Surjective π := by
    intro y
    refine Quotient.inductionOn y ?_
    intro r
    exact ⟨QuotientGroup.mk' Z r, rfl⟩
  have hQcenter_cyc : IsCyclic (R ⧸ Subgroup.center R) :=
    isCyclic_of_surjective π hπ_surj
  letI : IsMulCommutative R := lemma_4_1 (G := R) hQcenter_cyc
  let C' : Subgroup R := C
  letI : C'.Normal := Subgroup.normal_of_isMulCommutative C'
  have hx_ne : x ≠ 1 := by
    intro hx1
    have hCbot : C' = ⊥ := by simp [C', C, hx1]
    have hZ_top : Z = ⊤ := by
      have hCbot' : C = ⊥ := by simpa [C'] using hCbot
      simpa [hCbot'] using hCZ_top
    have hR_card : Nat.card R = p := by simpa [hZ_top] using hZcard
    exact hncyc (isCyclic_of_prime_card (α := R) hR_card)
  have hC_nontriv : Nontrivial C' := by
    have hxC : x ∈ C := Subgroup.mem_zpowers x
    refine ⟨⟨1, ⟨⟨x, by simpa [C'] using hxC⟩, ?_⟩⟩⟩
    intro hEq
    exact hx_ne (Subtype.ext_iff.mp hEq).symm
  have hCp : IsPGroup p C' := (Fact.out : IsPGroup p R).to_subgroup C'
  obtain ⟨mC, hmC⟩ := IsPGroup.iff_card.mp hCp
  have hmC_pos : 0 < mC := by
    by_contra hmC0
    have hmC_eq_zero : mC = 0 := Nat.eq_zero_of_not_pos hmC0
    have hC_card_one : Nat.card C' = 1 := by simpa [hmC_eq_zero] using hmC
    have hC_sub : Subsingleton C' := (Nat.card_eq_one_iff_unique.mp hC_card_one).1
    exact (not_subsingleton_iff_nontrivial.mpr hC_nontriv) hC_sub
  obtain ⟨U, hU_normal, hU_le_C, hUcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p)
      (N := C') inferInstance hmC 1 (Nat.succ_le_of_lt hmC_pos)
  letI : U.Normal := hU_normal
  have hU_ne_Z : U ≠ Z := by
    intro hUZ
    exact hZ_not_le_C (hUZ ▸ hU_le_C)
  let Ω : Subgroup R := U ⊔ Z
  letI : Ω.Normal := Subgroup.normal_of_isMulCommutative Ω
  have hOmega_pow : ∀ y : Ω, y ^ p = 1 := by
    intro y
    rcases (Subgroup.mem_sup_of_normal_right).1 y.2 with ⟨u, huU, z, hzZ, huz⟩
    have hu_pow : u ^ p = 1 := by
      have : (⟨u, huU⟩ : U) ^ Nat.card U = 1 := by
        simp
      simpa [hUcard] using congrArg Subtype.val this
    have hz_pow : z ^ p = 1 := by
      have : (⟨z, hzZ⟩ : Z) ^ Nat.card Z = 1 := by
        simp
      simpa [hZcard] using congrArg Subtype.val this
    apply Subtype.ext
    change ((y : R) ^ p = 1)
    calc
      (y : R) ^ p = (u * z) ^ p := congrArg (· ^ p) huz.symm
      _ = u ^ p * z ^ p := Commute.mul_pow (mul_comm' u z) p
      _ = 1 := by rw [hu_pow, hz_pow, one_mul]
  have hU_le_Ω : U ≤ Ω := le_sup_left
  have hZ_le_Ω : Z ≤ Ω := le_sup_right
  have hΩ_p : IsPGroup p Ω := (Fact.out : IsPGroup p R).to_subgroup Ω
  obtain ⟨m, hmΩ⟩ := IsPGroup.iff_card.mp hΩ_p
  have hΩ_card_ne_p : Nat.card Ω ≠ p := by
    intro hΩp
    have hU_eq_Ω : U = Ω :=
      Subgroup.eq_of_le_of_card_ge hU_le_Ω (by simp [hUcard, hΩp])
    have hZ_eq_Ω : Z = Ω :=
      Subgroup.eq_of_le_of_card_ge hZ_le_Ω (by simp [hZcard, hΩp])
    exact hU_ne_Z (hU_eq_Ω.trans hZ_eq_Ω.symm)
  have hm_ge_two : 2 ≤ m := by
    have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
    by_contra hm_lt
    have hm_lt_two : m < 2 := lt_of_not_ge hm_lt
    cases m with
    | zero =>
        have hΩ_card_one : Nat.card Ω = 1 := by simpa using hmΩ
        have hp_le_one : p ≤ 1 := by
          have := Subgroup.card_le_of_le hZ_le_Ω
          simpa [hZcard, hΩ_card_one] using this
        exact (not_le_of_gt hp_one_lt) hp_le_one
    | succ m' =>
        cases m' with
        | zero =>
            exact hΩ_card_ne_p (by simpa using hmΩ)
        | succ m'' =>
            exact False.elim (by omega)
  obtain ⟨K, hK_normal, hK_le_Ω, hKcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p) Ω inferInstance hmΩ 2 hm_ge_two
  letI : K.Normal := hK_normal
  have hKpow : ∀ y : K, y ^ p = 1 := by
    intro y
    apply Subtype.ext
    simpa using hOmega_pow ⟨(y : R), hK_le_Ω y.2⟩
  have hKcyc : IsCyclic (K ⧸ Subgroup.center K) :=
    IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq (p := p) (G := K) hKcard
  letI : IsMulCommutative K := lemma_4_1 (G := K) hKcyc
  refine ⟨K, hK_normal, hKcard, ?_⟩
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := ?_
  }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hKpow

universe u

public theorem CFSG.lemma_4_5_a {R : Type u} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)] (hncyc : ¬ IsCyclic R) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  let rec aux {S : Type u} [Group S] [Finite S] [Fact (IsPGroup p S)]
      (hSncyc : ¬ IsCyclic S) :
      ∃ A : Subgroup S, A.Normal ∧ Nat.card A = p ^ 2 ∧ IsElementaryAbelian p A := by
    have hS_nontriv : Nontrivial S := Nontrivial.of_not_isCyclic hSncyc
    have hSp : IsPGroup p S := Fact.out
    obtain ⟨nS, hSpow⟩ := IsPGroup.iff_card.mp hSp
    have hnS_pos : 0 < nS := by
      by_contra hnS
      have hnS0 : nS = 0 := Nat.eq_zero_of_not_pos hnS
      have hS_card_one : Nat.card S = 1 := by simpa [hnS0] using hSpow
      letI : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hS_card_one).1
      exact hSncyc (isCyclic_of_subsingleton (α := S))
    obtain ⟨k, hk_pos, hcenter_card⟩ :=
      IsPGroup.card_center_eq_prime_pow (G := S) (p := p) hSpow hnS_pos
    obtain ⟨Z, hZ_normal, hZ_le_center, hZcard⟩ :=
      exists_normal_subgroup_card_pow_of_normal (G := S) (p := p)
        (N := Subgroup.center S) inferInstance hcenter_card 1 (Nat.succ_le_of_lt hk_pos)
    letI : Z.Normal := hZ_normal
    by_cases hQcyc : IsCyclic (S ⧸ Z)
    · exact lemma_4_5_a_cyclic_case (p := p) Z hZ_le_center hZcard hQcyc hSncyc
    · have hQ_card : Nat.card S = Nat.card (S ⧸ Z) * p := by
        calc
          Nat.card S = Nat.card (S ⧸ Z) * Nat.card Z := by
            simpa using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := S) (s := Z))
          _ = Nat.card (S ⧸ Z) * p := by simp [hZcard]
      have hQ_lt : Nat.card (S ⧸ Z) < Nat.card S := by
        rw [hQ_card]
        simpa [one_mul] using
          (Nat.mul_lt_mul_of_pos_left ((Fact.out : Nat.Prime p).one_lt)
            (Nat.card_pos (α := S ⧸ Z)))
      have hQp : IsPGroup p (S ⧸ Z) := (Fact.out : IsPGroup p S).to_quotient Z
      letI : Fact (IsPGroup p (S ⧸ Z)) := ⟨hQp⟩
      obtain ⟨Sbar, hSbar_normal, hSbar_card, hSbar_elem⟩ :=
        aux (S := S ⧸ Z) hQcyc
      letI : Sbar.Normal := hSbar_normal
      exact
        lemma_4_5_a_preimage_case (R := S) (p := p) hpodd Z hZ_le_center hZcard
          Sbar hSbar_card hSbar_elem
  termination_by Nat.card S
  decreasing_by
    exact hQ_lt
  exact aux (S := R) hncyc


end Main
