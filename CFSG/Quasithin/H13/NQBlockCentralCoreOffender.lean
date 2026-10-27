module

public import CFSG.Quasithin.H13.NQBlockEscapingComponent
public import CFSG.Quasithin.SteinbergBTMaximalElementaryBestWeight
public import CFSG.Quasithin.SteinbergBQThompsonSeedBaumannCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedGeneral
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup
open CFSG.Quasithin.BlueprintB2 (centerTorsion mem_centerTorsion_iff)
open scoped Pointwise

theorem elemThompson_ne_bot_of_isPGroup {R : Type*} [Group R] [Finite R] [Nontrivial R] {p : ℕ}
    [hp : Fact p.Prime] (hR : IsPGroup p R) : CFSG.elemThompson R p ≠ ⊥ := by
  classical
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p
    (hR.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne')
  have hBcard : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hB : CFSG.IsElementaryAbelian p (zpowers x) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
        rw [← hBcard]
        exact pow_card_eq_one' }
  have h1 := CFSG.Quasithin.BlueprintB2.card_le_pow_pRank hB
  obtain ⟨A, hA, hAcard⟩ := CFSG.Quasithin.BlueprintB2.exists_card_eq_pow_pRank R p
  have hAJ := CFSG.Quasithin.BlueprintB2.le_elemThompson (A := A) ⟨hA, hAcard⟩
  intro hJ
  rw [hJ, le_bot_iff] at hAJ
  rw [hAJ, card_bot] at hAcard
  rw [hBcard, ← hAcard] at h1
  have := hp.out.two_le
  omega

theorem not_dvd_card_of_normal_nilpotent {E : Type*} [Group E] [Finite E] {p : ℕ}
    [hp : Fact p.Prime] (hO : CFSG.pCore p E = ⊥) {N : Subgroup E} (hN : N.Normal)
    (hnil : Group.IsNilpotent N) : ¬ p ∣ Nat.card N := by
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hdvd
  have hU : IsPGroup p (zpowers (x : E)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])
  have hle := CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore (zpowers (x : E)) N p
    hp.out hU hN hnil
  rw [hO, le_bot_iff] at hle
  have hmem : (x : E) ∈ zpowers (x : E) ⊓ N := ⟨mem_zpowers _, x.2⟩
  rw [hle, mem_bot] at hmem
  have hx1 : x = 1 := Subtype.ext hmem
  rw [hx1, orderOf_one] at hx
  exact hp.out.one_lt.ne hx

theorem mem_of_pow_prime_pow_mem {E : Type*} [Group E] {p : ℕ} (hp : p.Prime) {K : Subgroup E}
    {x : E} (hx : ¬ p ∣ orderOf x) {k : ℕ} (hk : x ^ p ^ k ∈ K) : x ∈ K := by
  have hcop : Nat.Coprime (p ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hx)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hk m

theorem not_dvd_orderOf_of_mem {E : Type*} [Group E] [Finite E] {p : ℕ} {K : Subgroup E}
    (hK : ¬ p ∣ Nat.card K) {x : E} (hx : x ∈ K) : ¬ p ∣ orderOf x := by
  intro h
  apply hK
  rw [show orderOf x = orderOf (⟨x, hx⟩ : K) from Subgroup.orderOf_coe ⟨x, hx⟩] at h
  exact h.trans (orderOf_dvd_natCard _)

theorem exists_pow_mem_of_mul_eq_univ {G : Type*} [Group G] {p : ℕ} {L S : Subgroup G}
    [L.Normal] (hS : IsPGroup p S) (h : (L : Set G) * (S : Set G) = Set.univ) (g : G) :
    ∃ k : ℕ, g ^ p ^ k ∈ L := by
  have hg : g ∈ (L : Set G) * (S : Set G) := h ▸ Set.mem_univ g
  rw [Set.mem_mul] at hg
  obtain ⟨l, hl, s, hs, rfl⟩ := hg
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hs1 : s ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff l).mpr hl, one_mul, ← QuotientGroup.mk_pow, hs1,
    QuotientGroup.mk_one]

theorem center_map_le_centralizer {E : Type*} [Group E] (Lb : Subgroup E) :
    (center Lb).map Lb.subtype ≤ centralizer (Lb : Set E) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_centralizer_iff]
  intro l hl
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)

theorem inf_le_center_of_normal {E : Type*} [Group E] {Lb N : Subgroup E}
    (hq : CFSG.IsQuasisimple Lb) (hN : N.Normal) (hNL : ¬ Lb ≤ N) :
    N ⊓ Lb ≤ (center Lb).map Lb.subtype := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (N := N.subgroupOf Lb) inferInstance
    with h | h
  · exact absurd (subgroupOf_eq_top.mp h) hNL
  · rw [← subgroupOf_map_subtype]
    exact map_mono h

theorem commutator_eq_bot_of_le_center {E : Type*} [Group E] {Lb X : Subgroup E}
    (hP : Group.IsPerfect Lb) (h : ⁅Lb, X⁆ ≤ (center Lb).map Lb.subtype) : ⁅Lb, X⁆ = ⊥ := by
  refine CFSG.LocalCores.perfect_double_commutator hP ?_
  exact le_bot_iff.mp ((commutator_mono h le_rfl).trans
    (commutator_eq_bot_iff_le_centralizer.mpr (center_map_le_centralizer Lb)).le)

theorem le_center_of_normal_of_not_le {E : Type*} [Group E] {Lb X : Subgroup E} [Lb.Normal]
    (hq : CFSG.IsQuasisimple Lb) (hcent : centralizer (Lb : Set E) ≤ (center Lb).map Lb.subtype)
    (hX : X.Normal) (hXL : ¬ Lb ≤ X) : X ≤ (center Lb).map Lb.subtype := by
  have h1 := inf_le_center_of_normal hq hX hXL
  have h2 : ⁅Lb, X⁆ ≤ (center Lb).map Lb.subtype := by
    refine (commutator_le_inf Lb X).trans ?_
    rw [inf_comm]
    exact h1
  have h3 := commutator_eq_bot_of_le_center hq.1 h2
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h3)).trans hcent

theorem not_isPGroup_quotient_center {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hq : CFSG.IsQuasisimple Q) : ¬ IsPGroup p (Q ⧸ center Q) := by
  intro hP
  obtain ⟨-, hs, a, b, hab⟩ := hq
  have hnil := hP.isNilpotent
  have hc : center (Q ⧸ center Q) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left
      (Group.IsNilpotent.center_ne_bot _)
  have ha : a ∈ center (Q ⧸ center Q) := hc ▸ mem_top a
  exact hab (mem_center_iff.mp ha b).symm

theorem isPGroup_quotient_center_of_pow_mem {E : Type*} [Group E] {p : ℕ} {Lb : Subgroup E}
    (h : ∀ l ∈ Lb, ∃ k : ℕ, l ^ p ^ k ∈ (center Lb).map Lb.subtype) :
    IsPGroup p (Lb ⧸ center Lb) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H l =>
    obtain ⟨k, z, hz, hzl⟩ := h l l.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have hzl' : z = l ^ p ^ k := Subtype.ext (by rw [Subgroup.coe_pow]; exact hzl)
    rw [← hzl']
    exact hz

theorem not_dvd_card_center_and_centralizer_le {E : Type*} [Group E] [Finite E] {p : ℕ}
    [hp : Fact p.Prime] (hO : CFSG.pCore p E = ⊥) {Lb : Subgroup E} [Lb.Normal]
    (hpow : ∀ g : E, ∃ k : ℕ, g ^ p ^ k ∈ Lb) :
    ¬ p ∣ Nat.card (center Lb) ∧ centralizer (Lb : Set E) ≤ (center Lb).map Lb.subtype := by
  have hZn : ((center Lb).map Lb.subtype).Normal := inferInstance
  have hZc : IsMulCommutative ((center Lb).map Lb.subtype) :=
    ⟨⟨fun a b => Subtype.ext (by
      obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      show (x : E) * y = y * x
      exact congrArg Subtype.val (mem_center_iff.mp hy x))⟩⟩
  have hZ := not_dvd_card_of_normal_nilpotent hO hZn CommGroup.isNilpotent
  rw [card_map_of_injective Lb.subtype_injective] at hZ
  refine ⟨hZ, ?_⟩
  have hE'n : (centralizer (Lb : Set E)).Normal := inferInstance
  have hcen : ∀ e ∈ centralizer (Lb : Set E), ∃ k : ℕ, e ^ p ^ k ∈ Lb ∧
      ∀ y ∈ centralizer (Lb : Set E), y * e ^ p ^ k = e ^ p ^ k * y := by
    intro e _
    obtain ⟨k, hk⟩ := hpow e
    exact ⟨k, hk, fun y hy => ((mem_centralizer_iff.mp hy) _ hk).symm⟩
  have hnil : Group.IsNilpotent (centralizer (Lb : Set E)) := by
    refine Group.of_quotient_center_nilpotent (IsPGroup.isNilpotent (p := p) ?_)
    intro x
    induction x using QuotientGroup.induction_on with
    | H e =>
      obtain ⟨k, -, hc⟩ := hcen e e.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_iff]
      intro y
      exact Subtype.ext (by simp only [coe_mul, coe_pow]; exact hc y y.2)
  have hE' := not_dvd_card_of_normal_nilpotent hO hE'n hnil
  intro e he
  obtain ⟨k, hk⟩ := hpow e
  have heL : e ∈ Lb := mem_of_pow_prime_pow_mem hp.out (not_dvd_orderOf_of_mem hE' he) hk
  exact ⟨⟨e, heL⟩, mem_center_iff.mpr fun l => Subtype.ext ((mem_centralizer_iff.mp he) l l.2),
    rfl⟩

theorem quotient_core_facts {E : Type*} [Group E] [Finite E] {p : ℕ} [hp : Fact p.Prime]
    (hO : CFSG.pCore p E = ⊥) {Lb : Subgroup E} [Lb.Normal] (hq : CFSG.IsQuasisimple Lb)
    (hpow : ∀ g : E, ∃ k : ℕ, g ^ p ^ k ∈ Lb) {Cb : Subgroup E} (hCn : Cb.Normal)
    (hCL : ¬ Lb ≤ Cb) :
    ¬ p ∣ Nat.card (center Lb) ∧ Cb ≤ (center Lb).map Lb.subtype ∧
      ∀ X : Subgroup E, X.Normal → (∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ Cb) → X ≤ Cb := by
  obtain ⟨hZ, hcent⟩ := not_dvd_card_center_and_centralizer_le hO hpow
  have hCZ := le_center_of_normal_of_not_le hq hcent hCn hCL
  refine ⟨hZ, hCZ, fun X hX hXp => ?_⟩
  have hZ' : ¬ p ∣ Nat.card ((center Lb).map Lb.subtype) := by
    rwa [card_map_of_injective Lb.subtype_injective]
  have hXL : ¬ Lb ≤ X := by
    intro hle
    refine not_isPGroup_quotient_center (p := p) hq (isPGroup_quotient_center_of_pow_mem ?_)
    intro l hl
    obtain ⟨k, hk⟩ := hXp l (hle hl)
    exact ⟨k, hCZ hk⟩
  have hXZ := le_center_of_normal_of_not_le hq hcent hX hXL
  intro x hx
  obtain ⟨k, hk⟩ := hXp x hx
  exact mem_of_pow_prime_pow_mem hp.out (not_dvd_orderOf_of_mem hZ' (hXZ hx)) hk

theorem centerTorsion_top_characteristic {R : Type*} [Group R] (p : ℕ) :
    (centerTorsion p (⊤ : Subgroup R)).Characteristic := by
  rw [characteristic_iff_le_comap]
  intro φ z hz
  obtain ⟨-, hc, hzp⟩ := mem_centerTorsion_iff.mp hz
  rw [mem_comap, mem_centerTorsion_iff]
  refine ⟨mem_top _, fun k _ => ?_, ?_⟩
  · have h := congrArg φ (hc (φ.symm k) (mem_top _))
    simpa using h
  · rw [← map_pow, hzp, map_one]

theorem central_core_centralizer_le {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hchar : CFSG.IsCharacteristicP p G) {S : Subgroup G} (hSp : IsPGroup p S)
    (hQS : CFSG.pCore p G ≤ S) (hSnt : S ≠ ⊥) {M : Subgroup G}
    (hM : ∀ D : Subgroup S, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map S.subtype : Subgroup G) : Set G) ≤ M) :
    centralizer (centerTorsion p (CFSG.pCore p G) : Set G) ≤ M := by
  classical
  have : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hSnt
  have hZc : (centerTorsion p (⊤ : Subgroup S)).Characteristic :=
    centerTorsion_top_characteristic p
  have hZne : centerTorsion p (⊤ : Subgroup S) ≠ ⊥ := by
    have := hSp.center_nontrivial
    have hdvd : p ∣ Nat.card (center S) :=
      ((hSp.to_subgroup (center S)).card_eq_or_dvd).resolve_left Finite.one_lt_card.ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) p hdvd
    have hz1 : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
    have hzZ : (z : S) ∈ centerTorsion p (⊤ : Subgroup S) :=
      mem_centerTorsion_iff.mpr ⟨mem_top _, fun k _ => mem_center_iff.mp z.2 k,
        by rw [← Subgroup.coe_pow, hz1, Subgroup.coe_one]⟩
    intro hbot
    rw [hbot, mem_bot] at hzZ
    have hz' : z = 1 := Subtype.ext hzZ
    rw [hz', orderOf_one] at hz
    exact hp.out.one_lt.ne hz
  have hZV : (centerTorsion p (⊤ : Subgroup S)).map S.subtype ≤
      centerTorsion p (CFSG.pCore p G) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨-, hzc, hzp⟩ := mem_centerTorsion_iff.mp hz
    have hzQ : (z : G) ∈ CFSG.pCore p G := hchar (mem_centralizer_iff.mpr fun q hq =>
      congrArg Subtype.val (hzc ⟨q, hQS hq⟩ (mem_top _)))
    refine mem_centerTorsion_iff.mpr ⟨hzQ, fun q hq => ?_, ?_⟩
    · exact congrArg Subtype.val (hzc ⟨q, hQS hq⟩ (mem_top _))
    · simpa using congrArg Subtype.val hzp
  calc centralizer (centerTorsion p (CFSG.pCore p G) : Set G)
      ≤ centralizer (((centerTorsion p (⊤ : Subgroup S)).map S.subtype : Subgroup G) : Set G) :=
        centralizer_le hZV
    _ ≤ normalizer (((centerTorsion p (⊤ : Subgroup S)).map S.subtype : Subgroup G) : Set G) :=
        centralizer_le_normalizer _
    _ ≤ M := hM _ hZc hZne

theorem card_fixed_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (D : Subgroup (MulAut X)) :
    Nat.card {y : Y // ∀ d ∈ D.map (MulAut.congr e).toMonoidHom, d y = y} =
      Nat.card {x : X // ∀ d ∈ D, d x = x} := by
  refine Nat.card_congr
    { toFun := fun y => ⟨e.symm y.1, fun d hd => ?_⟩
      invFun := fun x => ⟨e x.1, fun d hd => ?_⟩
      left_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      right_inv := fun x => Subtype.ext (e.symm_apply_apply x.1) }
  · have h : e (d (e.symm y.1)) = y.1 := y.2 _ ⟨d, hd, rfl⟩
    simpa using congrArg e.symm h
  · obtain ⟨d, hd, rfl⟩ := hd
    change e (d (e.symm (e x.1))) = e x.1
    rw [e.symm_apply_apply, x.2 d hd]

open CFSG.Quasithin.SteinbergBT (conjActOn maximal_elementary_subgroup_original_best_weight) in
theorem best_weight_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S V : Subgroup G} [V.Normal] (hVS : V ≤ S) (hV : CFSG.IsElementaryAbelian p V)
    (ρ : G →* MulAut V) (hρ : ∀ (g : G) (v : V), (ρ g v : G) = g * v * g⁻¹)
    (A : Subgroup S) (hA : CFSG.IsElementaryAbelian p A)
    (hmax : ∀ E : Subgroup S, CFSG.IsElementaryAbelian p E → Nat.card E ≤ Nat.card A)
    (D : Subgroup (MulAut V)) (hD : D ≤ (A.map S.subtype).map ρ) :
    Nat.card D * Nat.card {v : V // ∀ d ∈ D, d v = v} ≤
      Nat.card ((A.map S.subtype).map ρ) *
        Nat.card {v : V // ∀ d ∈ (A.map S.subtype).map ρ, d v = v} := by
  have hV' : CFSG.IsElementaryAbelian p (V.subgroupOf S) := CFSG.IsElementaryAbelian.subgroupOf hVS
  obtain ⟨-, -, -, hbest, -, -, -⟩ :=
    maximal_elementary_subgroup_original_best_weight (V.subgroupOf S) hV' A hA hmax
  set e : V.subgroupOf S ≃* V := subgroupOfEquivOfLe hVS with he
  have hkey : ∀ a : A, MulAut.congr e (conjActOn (V.subgroupOf S) A a) = ρ ((a : S) : G) := by
    intro a
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [hρ]
    rfl
  have hB : (A.map S.subtype).map ρ =
      (conjActOn (V.subgroupOf S) A).range.map (MulAut.congr e).toMonoidHom := by
    ext β
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, hkey ⟨a, ha⟩⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, a.2, rfl⟩, (hkey a).symm⟩
  have hD' : D.map (MulAut.congr e).symm.toMonoidHom ≤ (conjActOn (V.subgroupOf S) A).range := by
    rintro _ ⟨d, hd, rfl⟩
    have h := hD hd
    rw [hB] at h
    obtain ⟨r, hr, rfl⟩ := h
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, SetLike.mem_coe] using hr
  have hDD : (D.map (MulAut.congr e).symm.toMonoidHom).map (MulAut.congr e).toMonoidHom = D := by
    ext d
    constructor
    · rintro ⟨_, ⟨d', hd', rfl⟩, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, SetLike.mem_coe] using hd'
    · intro hd
      exact ⟨_, ⟨d, hd, rfl⟩, by simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩
  have h1 := hbest _ hD'
  rw [card_map_of_injective (f := (MulAut.congr e).symm.toMonoidHom)
    (MulAut.congr e).symm.injective, ← card_fixed_congr e, hDD, ← card_fixed_congr e, ← hB] at h1
  rw [hB, card_map_of_injective (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective,
    ← hB]
  exact h1

open CFSG.QuasithinUnique.Setup (normal_centerTorsion_pCore isElementaryAbelian_centerTorsion) in
theorem characteristic_normalizer_control_produces_central_core_best_offender
    {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hchar : CFSG.IsCharacteristicP p G) {S : Subgroup G} (hSp : IsPGroup p S)
    (hQS : CFSG.pCore p G ≤ S) {L : Subgroup G} (hLn : L.Normal)
    (hLS : (L : Set G) * (S : Set G) = Set.univ)
    (hLq : CFSG.IsQuasisimple (L ⧸ (CFSG.pCore p G).subgroupOf L)) {M : Subgroup G}
    (hLM : ¬ L ≤ M)
    (hM : ∀ D : Subgroup S, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map S.subtype : Subgroup G) : Set G) ≤ M)
    {V : Subgroup G} (hV : V = centerTorsion p (CFSG.pCore p G))
    (ρ : G →* MulAut V) (hρ : ∀ (g : G) (v : V), (ρ g v : G) = g * v * g⁻¹) :
    CFSG.Quasithin.IsPrimeReduced p V ∧ ⁅V, L⁆ ≠ ⊥ ∧
      CFSG.pCore p G ≤ centralizer (V : Set G) ∧
      (centralizer (V : Set G)).map (QuotientGroup.mk' (CFSG.pCore p G)) ≤
        (center (L.map (QuotientGroup.mk' (CFSG.pCore p G)))).map
          (L.map (QuotientGroup.mk' (CFSG.pCore p G))).subtype ∧
      Nat.Coprime (Nat.card (center (L.map (QuotientGroup.mk' (CFSG.pCore p G))))) p ∧
      S ⊓ centralizer (V : Set G) = CFSG.pCore p G ∧
      ¬ (CFSG.elemThompson S p).map S.subtype ≤ CFSG.pCore p G ∧
      ⁅V, (CFSG.elemThompson S p).map S.subtype⁆ ≠ ⊥ ∧
      ∃ A ∈ CFSG.elemThompsonFamily S p, (A.map S.subtype).map ρ ≠ ⊥ ∧
        CFSG.IsElementaryAbelian p ((A.map S.subtype).map ρ) ∧
        ∀ D : Subgroup (MulAut V), D ≤ (A.map S.subtype).map ρ →
          Nat.card D * Nat.card {v : V // ∀ d ∈ D, d v = v} ≤
            Nat.card ((A.map S.subtype).map ρ) *
              Nat.card {v : V // ∀ d ∈ (A.map S.subtype).map ρ, d v = v} := by
  classical
  have hVn : V.Normal := by rw [hV]; exact normal_centerTorsion_pCore p
  have hVe : CFSG.IsElementaryAbelian p V := by
    rw [hV]; exact isElementaryAbelian_centerTorsion p _
  have hVS : V ≤ S := by rw [hV]; exact (CFSG.Quasithin.BlueprintB2.centerTorsion_le p _).trans hQS
  have hQC : CFSG.pCore p G ≤ centralizer (V : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro v hv
    rw [SetLike.mem_coe, hV] at hv
    exact ((mem_centerTorsion_iff.mp hv).2.1 q hq).symm
  have hQnt : CFSG.pCore p G ≠ ⊥ := by
    intro hQ
    have hall : ∀ g : G, g = 1 := fun g => by
      have hg : g ∈ centralizer ((CFSG.pCore p G : Subgroup G) : Set G) := by
        rw [mem_centralizer_iff]
        intro h hh
        rw [SetLike.mem_coe, hQ, mem_bot] at hh
        rw [hh, one_mul, mul_one]
      have := hchar hg
      rwa [hQ, mem_bot] at this
    have : Subsingleton L := ⟨fun a b => Subtype.ext (by rw [hall a, hall b])⟩
    obtain ⟨x, y, hxy⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hLq).exists_pair_ne
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y => exact hxy (by rw [Subsingleton.elim x y])
  have hSnt : S ≠ ⊥ := fun h => hQnt (le_bot_iff.mp (h ▸ hQS))
  have hCM : centralizer (V : Set G) ≤ M := by
    rw [hV]; exact central_core_centralizer_le hchar hSp hQS hSnt hM
  have hVL : ⁅V, L⁆ ≠ ⊥ := fun h =>
    hLM ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)).trans hCM)
  have hO : CFSG.pCore p (G ⧸ CFSG.pCore p G) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hsurj := QuotientGroup.mk'_surjective (CFSG.pCore p G)
  have hLbn : (L.map (QuotientGroup.mk' (CFSG.pCore p G))).Normal := hLn.map _ hsurj
  obtain ⟨eL⟩ := nonempty_quotient_mulEquiv (QuotientGroup.mk' (CFSG.pCore p G)) (K := L) rfl
    ((CFSG.pCore p G).subgroupOf L)
    (by rw [subgroupOf_map_subtype, QuotientGroup.ker_mk', inf_comm])
  have hLbq := CFSG.LocalCores.isQuasisimple_of_mulEquiv eL hLq
  have hpow : ∀ g : G ⧸ CFSG.pCore p G, ∃ k : ℕ,
      g ^ p ^ k ∈ L.map (QuotientGroup.mk' (CFSG.pCore p G)) := by
    intro g
    obtain ⟨g, rfl⟩ := hsurj g
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mul_eq_univ (L := L) hSp hLS g
    exact ⟨k, ⟨g ^ p ^ k, hk, map_pow _ _ _⟩⟩
  have hCbn : ((centralizer (V : Set G)).map (QuotientGroup.mk' (CFSG.pCore p G))).Normal :=
    (inferInstance : (centralizer (V : Set G)).Normal).map _ hsurj
  have hCQ : ((centralizer (V : Set G)).map (QuotientGroup.mk' (CFSG.pCore p G))).comap
      (QuotientGroup.mk' (CFSG.pCore p G)) = centralizer (V : Set G) := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hQC]
  have hCL : ¬ L.map (QuotientGroup.mk' (CFSG.pCore p G)) ≤
      (centralizer (V : Set G)).map (QuotientGroup.mk' (CFSG.pCore p G)) := by
    intro hle
    have h := map_le_iff_le_comap.mp hle
    rw [hCQ] at h
    exact hLM (h.trans hCM)
  obtain ⟨hZ, hCZ, hred⟩ := quotient_core_facts hO hLbq hpow hCbn hCL
  have hRed : CFSG.Quasithin.IsPrimeReduced p V := by
    refine (CFSG.Quasithin.isPrimeReduced_iff_forall p).mpr ⟨hVn, hVe, fun D hD hDp => ?_⟩
    have hDb := hred (D.map (QuotientGroup.mk' (CFSG.pCore p G))) (hD.map _ hsurj) (by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨k, hk⟩ := hDp d hd
      exact ⟨k, ⟨d ^ p ^ k, hk, map_pow _ _ _⟩⟩)
    have h := map_le_iff_le_comap.mp hDb
    rwa [hCQ] at h
  have hSC : S ⊓ centralizer (V : Set G) = CFSG.pCore p G := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQS hQC)
    have hxZ := hCZ ⟨x, hx.2, rfl⟩
    have hZ' : ¬ p ∣ Nat.card ((center (L.map (QuotientGroup.mk' (CFSG.pCore p G)))).map
        (L.map (QuotientGroup.mk' (CFSG.pCore p G))).subtype) := by
      rwa [card_map_of_injective (subtype_injective _)]
    obtain ⟨k, hk⟩ := hSp ⟨x, hx.1⟩
    have hx1 : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hk' : (QuotientGroup.mk' (CFSG.pCore p G) x) ^ p ^ k ∈
        (⊥ : Subgroup (G ⧸ CFSG.pCore p G)) := by
      rw [← map_pow, hx1, map_one]
      exact one_mem _
    have h := mem_of_pow_prime_pow_mem hp.out (not_dvd_orderOf_of_mem hZ' hxZ) hk'
    rwa [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hJQ : ¬ (CFSG.elemThompson S p).map S.subtype ≤ CFSG.pCore p G := by
    intro hJ
    have hEq := CFSG.Quasithin.SteinbergBQ.map_elemThompson_subtype_eq_of_le hQS hJ
    have hchJ : (CFSG.elemThompson (CFSG.pCore p G) p).Characteristic :=
      CFSG.Quasithin.BlueprintB2.elemThompson_characteristic _ p
    have hJn : ((CFSG.elemThompson S p).map S.subtype).Normal := by
      rw [← hEq]
      infer_instance
    have : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hSnt
    have hN := hM _ (CFSG.Quasithin.BlueprintB2.elemThompson_characteristic S p)
      (elemThompson_ne_bot_of_isPGroup hSp)
    rw [normalizer_eq_top_iff.mpr hJn] at hN
    exact hLM (le_top.trans hN)
  have hJC : ¬ (CFSG.elemThompson S p).map S.subtype ≤ centralizer (V : Set G) := fun h =>
    hJQ ((le_inf (map_subtype_le _) h).trans hSC.le)
  refine ⟨hRed, hVL, hQC, hCZ, ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hZ).symm, hSC, hJQ,
    fun h => hJC (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)), ?_⟩
  obtain ⟨A, hA, hAV⟩ : ∃ A ∈ CFSG.elemThompsonFamily S p,
      ¬ A.map S.subtype ≤ centralizer (V : Set G) := by
    by_contra hall
    push Not at hall
    apply hJC
    rw [map_le_iff_le_comap]
    exact sSup_le fun A hA => map_le_iff_le_comap.mp (hall A hA)
  have hAe : CFSG.IsElementaryAbelian p (A.map S.subtype) :=
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_map hA.1 S.subtype
  refine ⟨A, hA, fun hB => hAV fun a ha => ?_,
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_map hAe ρ,
    best_weight_of_le hVS hVe ρ hρ A hA.1 fun E hE =>
      (CFSG.Quasithin.BlueprintB2.card_le_pow_pRank hE).trans hA.2.ge⟩
  have h1 : ρ a = 1 := by
    have : ρ a ∈ (A.map S.subtype).map ρ := mem_map_of_mem ρ ha
    rwa [hB, mem_bot] at this
  rw [mem_centralizer_iff]
  intro v hv
  have h2 := hρ a ⟨v, hv⟩
  rw [h1, MulAut.one_apply] at h2
  have h3 : v = a * v * a⁻¹ := h2
  calc v * a = (a * v * a⁻¹) * a := by rw [← h3]
    _ = a * v := by group

end CFSG.Quasithin.H13.NQBlock
