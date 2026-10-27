module

public import CFSG.Timmesfeld.Bridge.RootStructR2KOneClass
public import CFSG.Timmesfeld.Bridge.RootStructR2Tori
public import CFSG.Timmesfeld.Bridge.RootClosureThree

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity RootClosure CFSG.GH74.Uniqueness.Bender

namespace RootKOne

section Bender

variable {K : Type} [Group K] [Finite K] {n i e : ℕ}

omit [Finite K] in
theorem orderOf_eq_two_of_mul_self {u : K} (hu1 : u ≠ 1) (hu2 : u * u = 1) : orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact hu2) hu1

theorem mem_rootCenter_of_commute (hBT : BenderType K n i e) (S : Sylow 2 K) {u v : K}
    (huS : u ∈ (S : Subgroup K)) (hu1 : u ≠ 1) (hu2 : u * u = 1) (hv1 : v ≠ 1) (hv2 : v * v = 1)
    (huv : Commute u v) : v ∈ rootCenter (S : Subgroup K) := by
  obtain ⟨t, hc⟩ := hBT.exists_benderCore S
  have hL := hBT.lemma_3_2 S hc.sq_eq_one hc.not_mem
  obtain ⟨hle, -⟩ := hBT.lemma_3_4_b S hc.sq_eq_one hc.not_mem
    ⟨le_borel _ huS, orderOf_eq_two_of_mul_self hu1 hu2⟩
  have hvB : v ∈ borel (S : Subgroup K) :=
    hle (Subgroup.mem_centralizer_singleton_iff.2 huv.eq.symm)
  exact ((hL.involutions_iff v).1 ⟨hvB, orderOf_eq_two_of_mul_self hv1 hv2⟩).1

theorem mem_rootCenter_of_mem (hBT : BenderType K n i e) (S : Sylow 2 K) {u : K}
    (huS : u ∈ (S : Subgroup K)) (hu1 : u ≠ 1) (hu2 : u * u = 1) :
    u ∈ rootCenter (S : Subgroup K) := by
  obtain ⟨t, hc⟩ := hBT.exists_benderCore S
  have hL := hBT.lemma_3_2 S hc.sq_eq_one hc.not_mem
  exact ((hL.involutions_iff u).1 ⟨le_borel _ huS, orderOf_eq_two_of_mul_self hu1 hu2⟩).1

theorem mul_self_eq_one_of_mem_rootCenter (hBT : BenderType K n i e) (S : Sylow 2 K) {z : K}
    (hz : z ∈ rootCenter (S : Subgroup K)) : z * z = 1 := by
  by_cases hz1 : z = 1
  · rw [hz1, one_mul]
  obtain ⟨t, hc⟩ := hBT.exists_benderCore S
  have hL := hBT.lemma_3_2 S hc.sq_eq_one hc.not_mem
  have h2 := ((hL.involutions_iff z).2 ⟨hz, hz1⟩).2
  rw [← sq, ← h2, pow_orderOf_eq_one]

omit [Finite K] in
theorem mem_smul_sylow_iff {P : Sylow 2 K} {k z : K} :
    z ∈ ((k • P : Sylow 2 K) : Subgroup K) ↔ k⁻¹ * z * k ∈ (P : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem exists_eq_smul_sylow (hBT : BenderType K n i e) (S : Sylow 2 K) {t : K}
    (ht : t * t = 1) (htS : t ∉ borel (S : Subgroup K)) {P : Sylow 2 K} (hPS : P ≠ S) :
    ∃ p ∈ (S : Subgroup K), P = (p * t) • S := by
  have hL := hBT.lemma_3_2 S ht htS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S P
  have hgB : g ∉ borel (S : Subgroup K) := fun hgN =>
    hPS (by rw [← hg]; exact Sylow.smul_eq_iff_mem_normalizer.mpr hgN)
  obtain ⟨p, hpS, m₀, hm₀, rfl⟩ := hL.bruhat g hgB
  refine ⟨p, hpS, ?_⟩
  rw [← hg, mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr hm₀]

end Bender

namespace KOneConf

variable {G : Type} [Group G] {D : Set G} {q : ℕ} {a x y h : G} {T₁ T₂ : Subgroup G}
  (K1 : KOneConf G D q a x y h T₁ T₂)
include K1

theorem mem_classIn_of_mem_rootSet_of_mem_classIn {f t : G}
    (hf : f ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a)
    (ht : t ∈ rootSet D f) : t ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a := by
  obtain ⟨g, hgU, rfl⟩ := hf
  rw [rootSet_conj K1.isClass] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  exact conj_mem_classIn (K1.mem_classIn_of_mem_rootSet ht') hgU

omit K1 in
theorem mem_U_of_mem_rootSet_a {t : G} (ht : t ∈ rootSet D a) :
    t ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a ht))

theorem mk_ne_one {w : ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)} (hw : (w : G) ∈ D) :
    QuotientGroup.mk' (zStar ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)) w ≠ 1 :=
  fun h1 => K1.not_mem_zStar hw ((QuotientGroup.eq_one_iff _).1 h1)

theorem mk_mul_self {w : ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)} (hw : (w : G) ∈ D) :
    QuotientGroup.mk' (zStar ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)) w *
      QuotientGroup.mk' (zStar ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)) w = 1 := by
  rw [← map_mul, show w * w = 1 from Subtype.ext (by simpa using K1.root.mul_self_eq_one hw),
    map_one]

theorem isPGroup_zpowers_mk {U : Subgroup G}
    (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U) {f : U} (hf : f ∈ subClass U a) :
    IsPGroup 2 (Subgroup.zpowers (QuotientGroup.mk' (zStar U) f)) := by
  subst hU
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_two_of_mul_self (K1.mk_ne_one (K1.mem_D_of_mem_classIn hf))
    (K1.mk_mul_self (K1.mem_D_of_mem_classIn hf))

theorem commute_of_mk_mem_sylow {U : Subgroup G}
    (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U) {n i e : ℕ}
    (hBT : BenderType (U ⧸ zStar U) n i e) (P : Sylow 2 (U ⧸ zStar U)) {f f' : U}
    (hf : f ∈ subClass U a) (hf' : f' ∈ subClass U a)
    (hfP : QuotientGroup.mk' (zStar U) f ∈ (P : Subgroup (U ⧸ zStar U)))
    (hf'P : QuotientGroup.mk' (zStar U) f' ∈ (P : Subgroup (U ⧸ zStar U))) :
    Commute (f : G) f' := by
  subst hU
  have := K1.finite
  have hZ := mem_rootCenter_of_mem hBT P hf'P (K1.mk_ne_one (K1.mem_D_of_mem_classIn hf'))
    (K1.mk_mul_self (K1.mem_D_of_mem_classIn hf'))
  have hc : Commute (QuotientGroup.mk' (zStar _) f) (QuotientGroup.mk' (zStar _) f') :=
    (mem_rootCenter_iff.1 hZ).2 _ hfP
  exact ((OddLocal.commute_iff_mod_zStar K1.isOddTransp_subClass hf hf').1 hc).map
    (Subgroup.subtype _)

theorem mk_mem_rootCenter {U : Subgroup G}
    (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U) {n i e : ℕ}
    (hBT : BenderType (U ⧸ zStar U) n i e) (S : Sylow 2 (U ⧸ zStar U)) {f t : U}
    (hf : f ∈ subClass U a) (hfS : QuotientGroup.mk' (zStar U) f ∈ (S : Subgroup (U ⧸ zStar U)))
    (ht : (t : G) ∈ rootSet D f) :
    QuotientGroup.mk' (zStar U) t ∈ rootCenter (S : Subgroup (U ⧸ zStar U)) := by
  subst hU
  have := K1.finite
  have hfD := K1.mem_D_of_mem_classIn hf
  refine mem_rootCenter_of_commute hBT S hfS (K1.mk_ne_one hfD) (K1.mk_mul_self hfD)
    (K1.mk_ne_one ht.1) (K1.mk_mul_self ht.1) ?_
  have hft : Commute f t := Subtype.ext ((ht.2 f hfD).2 (Commute.refl _)).symm.eq
  exact hft.map _

theorem exists_mk_eq_of_mem_rootCenter {U : Subgroup G}
    (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U) {n i e : ℕ}
    (hBT : BenderType (U ⧸ zStar U) n i e) (S : Sylow 2 (U ⧸ zStar U)) {f : U}
    (hf : f ∈ subClass U a) (hfS : QuotientGroup.mk' (zStar U) f ∈ (S : Subgroup (U ⧸ zStar U)))
    {z : U ⧸ zStar U}
    (hz : z ∈ rootCenter (S : Subgroup (U ⧸ zStar U))) (hz1 : z ≠ 1) :
    ∃ t : U, (t : G) ∈ rootSet D f ∧ QuotientGroup.mk' (zStar U) t = z := by
  subst hU
  have := K1.finite
  have hfD := K1.mem_D_of_mem_classIn hf
  obtain ⟨c, hc⟩ := isConj_iff.1 (hBT.lemma_3_4_a (K1.mk_mul_self hfD) (K1.mk_ne_one hfD)
    (mul_self_eq_one_of_mem_rootCenter hBT S hz) hz1)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ c
  have hk : k * f * k⁻¹ ∈ subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a :=
    isNormalSet_subClass k f hf
  have himg : QuotientGroup.mk' (zStar _) (k * f * k⁻¹) = z := by
    rw [map_mul, map_mul, map_inv, hc]
  have hcomm : Commute f (k * f * k⁻¹) := by
    refine (OddLocal.commute_iff_mod_zStar K1.isOddTransp_subClass hf hk).1 ?_
    rw [himg]
    exact (mem_rootCenter_iff.1 hz).2 _ hfS
  exact ⟨_, K1.mem_rootSet_of_mem_classIn hf (K1.mem_D_of_mem_classIn hk) (k * f * k⁻¹).2
    (hcomm.map (Subgroup.subtype _)), himg⟩

theorem card_rootGroup_eq_card_rootCenter {U : Subgroup G}
    (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U) {n i e : ℕ}
    (hBT : BenderType (U ⧸ zStar U) n i e) (S : Sylow 2 (U ⧸ zStar U)) {f : U}
    (hfa : (f : G) = a) (hfS : QuotientGroup.mk' (zStar U) f ∈ (S : Subgroup (U ⧸ zStar U))) :
    Nat.card (rootGroup D a) = Nat.card (rootCenter (S : Subgroup (U ⧸ zStar U))) := by
  subst hU
  have := K1.finite
  have hD := K1.root
  have hle : rootGroup D a ≤ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y :=
    le_sup_left.trans le_sup_left
  obtain ⟨φ, hφ⟩ : ∃ φ : rootGroup D a →* ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) ⧸
      zStar ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y),
      φ = (QuotientGroup.mk' _).comp (Subgroup.inclusion hle) := ⟨_, rfl⟩
  have hφs : ∀ s, φ s = QuotientGroup.mk' _ (Subgroup.inclusion hle s) := fun s => by
    rw [hφ]
    rfl
  have hf : f ∈ subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a := by
    show (f : G) ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a
    rw [hfa]
    exact mem_classIn_self _ a
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    by_contra hs1
    have hsT : (s : G) ∈ rootSet D a := mem_rootSet_of_mem_rootGroup_of_ne_one hD
      K1.counter.closure K1.ha s.2 fun h' => hs1 (Subtype.ext h')
    exact K1.mk_ne_one (w := Subgroup.inclusion hle s) hsT.1 (by rw [← hφs]; exact hs)
  have hrange : φ.range = rootCenter (S : Subgroup _) := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      by_cases hs1 : (s : G) = 1
      · have hs : s = 1 := Subtype.ext hs1
        rw [hs, map_one]
        exact (rootCenter _).one_mem
      · have hsT : (s : G) ∈ rootSet D a :=
          mem_rootSet_of_mem_rootGroup_of_ne_one hD K1.counter.closure K1.ha s.2 hs1
        rw [hφs]
        exact K1.mk_mem_rootCenter rfl hBT S (t := Subgroup.inclusion hle s) hf hfS
          (by rw [hfa]; exact hsT)
    · intro hz
      by_cases hz1 : z = 1
      · rw [hz1]
        exact φ.range.one_mem
      · obtain ⟨t, htT, hπt⟩ := K1.exists_mk_eq_of_mem_rootCenter rfl hBT S hf hfS hz hz1
        rw [hfa] at htT
        exact ⟨⟨t, rootSet_subset_rootGroup D a htT⟩, by rw [hφs, ← hπt]; rfl⟩
  rw [← hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv

omit K1 in
theorem commute_of_forall_rootSet {g : G} {c : G} (hg : ∀ t ∈ rootSet D c, Commute g t) {u : G}
    (hu : u ∈ rootGroup D c) : Commute g u := by
  have hle : rootGroup D c ≤ Subgroup.centralizer {g} :=
    (Subgroup.closure_le _).2 fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2 (hg t ht).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm

theorem rootGroup_le_closure : rootGroup D a ≤ Subgroup.closure {c | c ∈ D ∧ Commute a c} :=
  Subgroup.closure_mono fun _ hc => ⟨hc.1, ((hc.2 a K1.ha).2 (Commute.refl a)).symm⟩

theorem mem_gatedLines_x : T₁ ∈ gatedLines D a x := by
  rw [K1.gated_x]
  rfl

theorem map_conj_T₁_eq {g : G} (hga : ∀ s ∈ rootGroup D a, Commute g s)
    (hgx : ∀ s ∈ rootGroup D x, Commute g s) :
    T₁.map (MulAut.conj g).toMonoidHom = T₁ := by
  have hD := K1.root
  have hgxx : g * x * g⁻¹ = x := by
    rw [(hgx x (rootSet_subset_rootGroup D x (mem_rootSet_self K1.hx))).eq, mul_inv_cancel_right]
  obtain ⟨hT₁, p, hp, hpT₁, h4⟩ := K1.mem_gatedLines_x
  have hgA : (rootGroup D a).map (MulAut.conj g).toMonoidHom = rootGroup D a :=
    map_conj_eq_of_forall_commute hga
  have hmem : T₁.map (MulAut.conj g).toMonoidHom ∈ gatedLines D a x := by
    refine ⟨map_conj_mem_rootLines_of_map_eq K1.counter.hyp K1.counter.closure K1.counter.special
      K1.ha hgA hT₁, g * p * g⁻¹, K1.conj_mem g hp, ⟨p, hpT₁, rfl⟩, ?_⟩
    rw [show x * (g * p * g⁻¹) = g * (x * p) * g⁻¹ by
      conv_lhs => rw [← hgxx]
      group, orderOf_conj_eq]
    exact h4
  rw [K1.gated_x] at hmem
  exact Set.mem_singleton_iff.1 hmem

theorem false_of_suzuki {U : Subgroup G} (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U)
    {m : ℕ} (hm : 1 ≤ m) (e : U ⧸ zStar U ≃* CFSG.Theory.Comparator.SzModel m) : False := by
  subst hU
  have := K1.finite
  set U := rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y with hUdef
  obtain ⟨a', ha', h3⟩ := exists_orderOf_mul_eq_three_of_oneOpposite K1.counter.hyp
    K1.counter.closure K1.counter.special K1.lineSetting.commLambda K1.ha K1.hx
    (fun h' => K1.hax h'.symm) (by rw [orderOf_mul_comm_eq]; exact K1.hoddax) K1.hx1
  have ha'U : a' ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y := mem_U_of_mem_rootSet_a ha'
  set x₀ : U := ⟨x, K1.x_mem_U⟩ with hx₀
  set a₀ : U := ⟨a', ha'U⟩ with ha₀
  have hg3 : orderOf (QuotientGroup.mk' (zStar U) (x₀ * a₀)) = 3 := by
    have hdvd : orderOf (QuotientGroup.mk' (zStar U) (x₀ * a₀)) ∣ 3 := by
      have hU3 : orderOf (x₀ * a₀) = 3 := by
        rw [← Subgroup.orderOf_coe]
        exact h3
      rw [← hU3]
      exact orderOf_map_dvd _ _
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      rw [orderOf_eq_one_iff, map_mul] at h1
      have heq : QuotientGroup.mk' (zStar U) x₀ = QuotientGroup.mk' (zStar U) a₀ := by
        calc QuotientGroup.mk' (zStar U) x₀
            = QuotientGroup.mk' (zStar U) x₀ *
              (QuotientGroup.mk' (zStar U) a₀ * QuotientGroup.mk' (zStar U) a₀) := by
              rw [K1.mk_mul_self (w := a₀) ha'.1, mul_one]
          _ = (QuotientGroup.mk' (zStar U) x₀ * QuotientGroup.mk' (zStar U) a₀) *
              QuotientGroup.mk' (zStar U) a₀ := by rw [mul_assoc]
          _ = QuotientGroup.mk' (zStar U) a₀ := by rw [h1, one_mul]
      have hxa : x = a' :=
        congrArg Subtype.val (K1.eq_of_mk_eq (e := x₀) (f := a₀) K1.x_mem_classIn
          (K1.mem_classIn_of_mem_rootSet ha') heq)
      have hxT : x ∈ rootSet D a := by rw [hxa]; exact ha'
      exact K1.hax ((hxT.2 a K1.ha).2 (Commute.refl a)).symm
    · exact h1
  have h3K : 3 ∣ Nat.card (U ⧸ zStar U) := hg3 ▸ orderOf_dvd_natCard _
  rw [Nat.card_congr e.toEquiv] at h3K
  exact not_three_dvd_card_szModel hm h3K

theorem false_of_psl2 {U : Subgroup G} (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U)
    {m : ℕ} (hm : 2 ≤ m) (e : U ⧸ zStar U ≃* CFSG.Theory.Comparator.PSL2Model m) : False := by
  subst hU
  have := K1.finite
  have hD := K1.root
  set U := rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y with hUdef
  set π := QuotientGroup.mk' (zStar U) with hπ
  have hBT : BenderType (U ⧸ zStar U) m 1 1 := .linear m hm e
  set a₀ : U := ⟨a, K1.a_mem_U⟩ with ha₀
  set x₀ : U := ⟨x, K1.x_mem_U⟩ with hx₀
  set y₀ : U := ⟨y, K1.y_mem_U⟩ with hy₀
  have ha₀E : a₀ ∈ subClass U a := mem_classIn_self _ a
  have hx₀E : x₀ ∈ subClass U a := K1.x_mem_classIn
  have hy₀E : y₀ ∈ subClass U a := K1.y_mem_classIn
  obtain ⟨S, hS⟩ := (K1.isPGroup_zpowers_mk rfl ha₀E).exists_le_sylow
  obtain ⟨Sx, hSx⟩ := (K1.isPGroup_zpowers_mk rfl hx₀E).exists_le_sylow
  obtain ⟨Sy, hSy⟩ := (K1.isPGroup_zpowers_mk rfl hy₀E).exists_le_sylow
  have haS : π a₀ ∈ (S : Subgroup (U ⧸ zStar U)) := hS (Subgroup.mem_zpowers _)
  have hxS : π x₀ ∈ (Sx : Subgroup (U ⧸ zStar U)) := hSx (Subgroup.mem_zpowers _)
  have hyS : π y₀ ∈ (Sy : Subgroup (U ⧸ zStar U)) := hSy (Subgroup.mem_zpowers _)
  have hZ : ∀ P : Sylow 2 (U ⧸ zStar U), rootCenter (P : Subgroup (U ⧸ zStar U)) = P := by
    intro P
    obtain ⟨t, hc⟩ := hBT.exists_benderCore P
    have hL := hBT.lemma_3_2 P hc.sq_eq_one hc.not_mem
    exact Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (by rw [hL.card_center, hL.card_sylow, pow_one])
  have hSxS : Sx ≠ S := fun h' =>
    K1.hax (K1.commute_of_mk_mem_sylow rfl hBT S ha₀E hx₀E haS (h' ▸ hxS))
  have hSyS : Sy ≠ S := fun h' =>
    K1.hay (K1.commute_of_mk_mem_sylow rfl hBT S ha₀E hy₀E haS (h' ▸ hyS))
  obtain ⟨t, hc⟩ := hBT.exists_benderCore S
  obtain ⟨p₁, hp₁, hSx'⟩ := exists_eq_smul_sylow hBT S hc.sq_eq_one hc.not_mem hSxS
  obtain ⟨p₂, hp₂, hSy'⟩ := exists_eq_smul_sylow hBT S hc.sq_eq_one hc.not_mem hSyS
  have hSyx : Sy = (p₂ * p₁⁻¹) • Sx := by
    rw [hSy', hSx', ← mul_smul]
    congr 1
    group
  have hk : p₂ * p₁⁻¹ ∈ (S : Subgroup (U ⧸ zStar U)) := S.mul_mem hp₂ (S.inv_mem hp₁)
  obtain ⟨n₀, hn₀A, hn₀⟩ : ∃ n₀ : U, (n₀ : G) ∈ rootGroup D a ∧ π n₀ = p₂ * p₁⁻¹ := by
    by_cases hk1 : p₂ * p₁⁻¹ = 1
    · exact ⟨1, (rootGroup D a).one_mem, by rw [map_one, hk1]⟩
    · have hkZ : p₂ * p₁⁻¹ ∈ rootCenter (S : Subgroup (U ⧸ zStar U)) := by rw [hZ S]; exact hk
      obtain ⟨t', ht', hπt'⟩ := K1.exists_mk_eq_of_mem_rootCenter rfl hBT S ha₀E haS hkZ hk1
      exact ⟨t', rootSet_subset_rootGroup D a ht', hπt'⟩
  set w : U := n₀ * x₀ * n₀⁻¹ with hw
  have hwE : w ∈ subClass U a := isNormalSet_subClass n₀ x₀ hx₀E
  have hwS : π w ∈ (Sy : Subgroup (U ⧸ zStar U)) := by
    rw [hSyx, mem_smul_sylow_iff, hw, map_mul, map_mul, map_inv, hn₀]
    rw [show (p₂ * p₁⁻¹)⁻¹ * (p₂ * p₁⁻¹ * π x₀ * (p₂ * p₁⁻¹)⁻¹) * (p₂ * p₁⁻¹) = π x₀ by group]
    exact hxS
  have hwZ : π w ∈ rootCenter (Sy : Subgroup (U ⧸ zStar U)) := by rw [hZ Sy]; exact hwS
  obtain ⟨t', ht', hπt'⟩ := K1.exists_mk_eq_of_mem_rootCenter rfl hBT Sy hy₀E hyS hwZ
    (K1.mk_ne_one (K1.mem_D_of_mem_classIn hwE))
  have ht'E : t' ∈ subClass U a := K1.mem_classIn_of_mem_rootSet_of_mem_classIn hy₀E ht'
  have hwT : (w : G) ∈ rootSet D y := by
    rw [← K1.eq_of_mk_eq ht'E hwE hπt']
    exact ht'
  set n := (n₀ : G) with hn
  have hwG : (w : G) = n * x * n⁻¹ := rfl
  obtain ⟨hT₁, p, hp, hpT₁, h4⟩ := K1.mem_gatedLines_x
  have hnT : T₁.map (MulAut.conj n).toMonoidHom = T₁ :=
    K1.lineSetting.map_conj_eq_of_mem_closure K1.ha (K1.rootGroup_le_closure hn₀A) hT₁
  have hpT₁' : n * p * n⁻¹ ∈ T₁ := by
    rw [← hnT]
    exact ⟨p, hpT₁, rfl⟩
  have hp' : n * p * n⁻¹ ∈ D := K1.conj_mem n hp
  have h4' : orderOf (n * x * n⁻¹ * (n * p * n⁻¹)) = 4 := by
    rw [show n * x * n⁻¹ * (n * p * n⁻¹) = n * (x * p) * n⁻¹ by group, orderOf_conj_eq]
    exact h4
  rw [← hwG] at h4'
  have hy4 : orderOf (y * (n * p * n⁻¹)) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD (K1.mem_D_of_mem_classIn hwE) hp'
      (mem_rootSet_comm K1.hy hwT) (mem_rootSet_self hp') h4'
  have hmem : T₁ ∈ gatedLines D a y := ⟨hT₁, _, hp', hpT₁', hy4⟩
  rw [K1.gated_y] at hmem
  exact K1.ne (Set.mem_singleton_iff.1 hmem)

theorem false_of_centralizing {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card (rootGroup D a) - 1) (hpq' : ¬ p ∣ Nat.card (rootGroup D a)) {g : G}
    (hgo : orderOf g = p) (hga : ∀ s ∈ rootGroup D a, Commute g s)
    (hgx : ∀ s ∈ rootGroup D x, Commute g s) : False := by
  have := K1.finite
  have hp := (Fact.out : p.Prime)
  have hgT₁ := K1.map_conj_T₁_eq hga hgx
  have hgA : (rootGroup D a).map (MulAut.conj g).toMonoidHom = rootGroup D a :=
    map_conj_eq_of_forall_commute hga
  have hT₁L : T₁ ∈ rootLines D a := K1.mem_gatedLines_x.1
  have hP : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgo, pow_one])
  have hS : ∀ g' ∈ Subgroup.zpowers g, ∀ H ∈ rootLines D a \ {T₁},
      H.map (MulAut.conj g').toMonoidHom ∈ rootLines D a \ {T₁} := by
    intro g' hg' H hH
    obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers hg'
    obtain ⟨hHL, hHne⟩ := hH
    refine ⟨map_conj_mem_rootLines_of_map_eq K1.counter.hyp K1.counter.closure
      K1.counter.special K1.ha (map_conj_pow_eq hgA j) hHL, fun h' => hHne ?_⟩
    rw [Set.mem_singleton_iff] at h' ⊢
    exact Subgroup.map_injective (f := (MulAut.conj (g ^ j)).toMonoidHom)
      (MulAut.conj (g ^ j)).injective (h'.trans (map_conj_pow_eq hgT₁ j).symm)
  have hpS : ¬ p ∣ (rootLines D a \ {T₁}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hT₁L, K1.count.ncard_rootLines a K1.ha, pow_one,
      ← K1.count.card_rootGroup a K1.ha, Nat.add_sub_cancel]
    exact hpq'
  obtain ⟨T', ⟨hT'L, hT'ne⟩, hT'fix⟩ := exists_map_conj_eq_of_isPGroup hP hS hpS
  have hgT' : ∀ v ∈ T', Commute g v := fun v hv =>
    K1.lineSetting.commute_of_orderOf_eq_prime K1.counter.allTI hp2 K1.ha hpq hT'L hgo hga
      (hT'fix g (Subgroup.mem_zpowers g)) hv
  obtain ⟨c, hcD, hac, hacD, hcT, rfl⟩ := hT'L
  have hnogate : ∀ p' ∈ D, p' ∈ rootGroup D a ⊔ rootGroup D c → orderOf (x * p') ≠ 4 := by
    intro p' hp' hp'L h4
    have hmem : rootGroup D a ⊔ rootGroup D c ∈ gatedLines D a x :=
      ⟨⟨c, hcD, hac, hacD, hcT, rfl⟩, p', hp', hp'L, h4⟩
    rw [K1.gated_x] at hmem
    exact hT'ne hmem
  have htop := K1.counter.gen a K1.ha c hcD x K1.hx hac hacD hcT K1.hax K1.hoddax K1.hx1 hnogate
  have hcen : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun w => by
    have hw : w ∈ rootGroup D a ⊔ rootGroup D c ⊔ rootGroup D x := by
      rw [htop]
      exact Subgroup.mem_top w
    exact (commute_of_mem_sup hgT' hgx hw).eq.symm
  rw [Hyp.center_eq_bot K1.counter.hyp, Subgroup.mem_bot] at hcen
  rw [hcen, orderOf_one] at hgo
  exact hp.ne_one hgo.symm

theorem commute_of_mk_commute {U : Subgroup G}
    (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U) {g₀ : U} {f : G}
    (hf : f ∈ classIn U a) (hc : ∀ t : U, (t : G) ∈ rootSet D f →
      Commute (QuotientGroup.mk' (zStar U) g₀) (QuotientGroup.mk' (zStar U) t)) (k : ℕ) :
    ∀ s ∈ rootGroup D f, Commute ((g₀ ^ k : U) : G) s := by
  subst hU
  intro s hs
  refine commute_of_forall_rootSet (fun t ht => ?_) hs
  have htE := K1.mem_classIn_of_mem_rootSet_of_mem_classIn hf ht
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y), (t₀ : G) = t :=
    ⟨⟨t, K1.mem_U_of_mem_classIn htE⟩, rfl⟩
  have ht₀E : t₀ ∈ subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a := by
    show (t₀ : G) ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a
    rw [ht₀]
    exact htE
  have hconj : g₀ ^ k * t₀ * (g₀ ^ k)⁻¹ = t₀ := by
    refine K1.eq_of_mk_eq (isNormalSet_subClass _ t₀ ht₀E) ht₀E ?_
    have hc' := hc t₀ (by rw [ht₀]; exact ht)
    rw [map_mul, map_mul, map_inv, map_pow, (hc'.pow_left k).eq, mul_inv_cancel_right]
  obtain ⟨g, hg⟩ : ∃ g : G, g = ((g₀ ^ k : ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)) :
      G) := ⟨_, rfl⟩
  rw [← hg]
  have h1 : g * t * g⁻¹ = t := by
    rw [← ht₀, hg]
    exact congrArg Subtype.val hconj
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [h1]

theorem exists_centralizing_of_psu3 {U : Subgroup G}
    (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U) {m : ℕ} (hm : 2 ≤ m)
    (e : U ⧸ zStar U ≃* CFSG.Theory.Comparator.PSU3Model m) :
    Nat.card (rootGroup D a) = 2 ^ m ∧ ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ m + 1 ∧
      ∃ g : G, orderOf g = p ∧ (∀ s ∈ rootGroup D a, Commute g s) ∧
        ∀ s ∈ rootGroup D x, Commute g s := by
  have := K1.finite
  have hBT : BenderType (U ⧸ zStar U) m 3 ((2 ^ m + 1) / Nat.gcd 3 (2 ^ m + 1)) :=
    .unitary m hm e
  have haU : a ∈ U := hU ▸ K1.a_mem_U
  have hxU : x ∈ U := hU ▸ K1.x_mem_U
  have ha₀E : (⟨a, haU⟩ : U) ∈ subClass U a := mem_classIn_self _ a
  have hx₀E : (⟨x, hxU⟩ : U) ∈ subClass U a := hU ▸ K1.x_mem_classIn
  obtain ⟨S, hS⟩ := (K1.isPGroup_zpowers_mk hU ha₀E).exists_le_sylow
  obtain ⟨Sx, hSx⟩ := (K1.isPGroup_zpowers_mk hU hx₀E).exists_le_sylow
  have haS := hS (Subgroup.mem_zpowers _)
  have hxS := hSx (Subgroup.mem_zpowers _)
  have hSSx : S ≠ Sx := fun h' =>
    K1.hax (K1.commute_of_mk_mem_sylow hU hBT S ha₀E hx₀E haS (h' ▸ hxS))
  have hq : Nat.card (rootGroup D a) = 2 ^ m := by
    rw [K1.card_rootGroup_eq_card_rootCenter hU hBT S (f := ⟨a, haU⟩) rfl haS]
    obtain ⟨t, hc⟩ := hBT.exists_benderCore S
    exact (hBT.lemma_3_2 S hc.sq_eq_one hc.not_mem).card_center
  refine ⟨hq, ?_⟩
  obtain ⟨g₁, hg₁o, hg₁S, hg₁Sx⟩ := Tori.psu3_exists_centralizing hm e hSSx
  have he₀ := unitary_e_gt_one m hm
  obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd
    (show (2 ^ m + 1) / Nat.gcd 3 (2 ^ m + 1) ≠ 1 by omega)
  refine ⟨p, hp, hpe.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 _)), ?_⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (zStar U) g₁
  have hpg : p ∣ orderOf (QuotientGroup.mk' (zStar U) g₀) := by
    rw [hg₁o]
    exact hpe
  have hpg₀ : p ∣ orderOf g₀ := hpg.trans (orderOf_map_dvd _ _)
  have hcomm : ∀ {f : U} {P : Sylow 2 (U ⧸ zStar U)}, f ∈ subClass U a →
      QuotientGroup.mk' (zStar U) f ∈ (P : Subgroup (U ⧸ zStar U)) →
      (∀ z ∈ P, (∀ s ∈ P, Commute s z) → Commute (QuotientGroup.mk' (zStar U) g₀) z) →
      ∀ t : U, (t : G) ∈ rootSet D f →
        Commute (QuotientGroup.mk' (zStar U) g₀) (QuotientGroup.mk' (zStar U) t) := by
    intro f P hf hfP hgP t ht
    obtain ⟨htP, htc⟩ := mem_rootCenter_iff.1 (K1.mk_mem_rootCenter hU hBT P hf hfP ht)
    exact hgP _ htP fun s hs => htc s hs
  refine ⟨_, ?_, K1.commute_of_mk_commute hU ha₀E (hcomm ha₀E haS hg₁S) (orderOf g₀ / p),
    K1.commute_of_mk_commute hU hx₀E (hcomm hx₀E hxS hg₁Sx) (orderOf g₀ / p)⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (orderOf_pos g₀).ne' hpg₀

theorem false_of_psu3 {U : Subgroup G} (hU : rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y = U)
    {m : ℕ} (hm : 2 ≤ m) (e : U ⧸ zStar U ≃* CFSG.Theory.Comparator.PSU3Model m) : False := by
  obtain ⟨hq, p, hp, hpq1, g, hgo, hga, hgx⟩ := K1.exists_centralizing_of_psu3 hU hm e
  have : Fact p.Prime := ⟨hp⟩
  have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  refine K1.false_of_centralizing hp2 ?_ ?_ hgo hga hgx
  · rw [hq]
    intro hdvd
    have h1 : p ∣ (2 ^ m + 1) - (2 ^ m - 1) := Nat.dvd_sub hpq1 hdvd
    have h2 : (2 ^ m + 1) - (2 ^ m - 1) = 2 := by
      have := Nat.one_le_two_pow (n := m)
      omega
    rw [h2] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  · rw [hq]
    exact not_dvd_two_pow hp hp2 m

end KOneConf

end RootKOne

end CFSG.Timmesfeld.Bridge
