module

public import CFSG.RankThree.OddKernel.CriticalFixedSpaces
public import CFSG.RankThree.OddKernel.RankTwoActionsVanish
public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.Assembly.LowTwoRank

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Assembly.RankThreeEven
open scoped commutatorElement

universe u

theorem isPerfect_of_isSimpleGroup' {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hc : ⁅a, b⁆ ∈ commutator S :=
      Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem even_card_of_isQuasisimple {K : Type*} [Group K] [Finite K] (hK : IsQuasisimple K) :
    Even (Nat.card K) := by
  obtain ⟨-, hs, hnab⟩ := hK
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (center K)
  rw [hk]
  exact heven.mul_right k

theorem isSimpleGroup_of_isQuasisimple {K : Type*} [Group K] (hK : IsQuasisimple K)
    (hZ : center K = ⊥) : IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hK
  let e : K ⧸ center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem center_eq_bot_of_isComponent {S : Type*} [Group S] [Finite S] (hE : layer S = ⊤)
    (hZ : center S = ⊥) {K : Subgroup S} (hK : IsComponent K) : center K = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzc := CFSG.LocalCores.center_component_le_centralizer_layer hK
    (mem_map_of_mem K.subtype hz)
  rw [hE, coe_top, centralizer_univ, hZ] at hzc
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp hzc))

theorem exists_four_group_of_isSimpleGroup {K : Type u} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) :
    ∃ V : Subgroup K, (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x ^ 2 = 1) ∧
      Nat.card V = 4 := by
  classical
  let f : Shrink.{0} K ≃* K := Shrink.mulEquiv
  have : Finite (Shrink.{0} K) := Finite.of_equiv K f.symm.toEquiv
  have : IsSimpleGroup (Shrink.{0} K) := f.isSimpleGroup
  have hnab' : ∃ a b : Shrink.{0} K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨f.symm a, f.symm b, fun h => hab ?_⟩
    have := congrArg f h
    simpa using this
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab').1
  have h2 : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (Shrink.{0} K)) :=
    CFSG.Assembly.LowTwoRank.two_le_twoRank (Shrink.{0} K) hnab' heven
  obtain ⟨E, -, hE, hEcard⟩ :=
    SectionRank.exists_pRank (G := Shrink.{0} K) (p := 2) one_lt_two ⊤
  obtain ⟨E', hE'4, -, hE'E⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := ⊥) (L := E) (n := 2) (by rw [card_bot]; exact one_dvd _)
    (by rw [hEcard]; exact pow_dvd_pow 2 h2) bot_le
  refine ⟨E'.map f.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have := hE.1.is_comm.comm (⟨x, hE'E hx⟩ : E) ⟨y, hE'E hy⟩
    exact congrArg Subtype.val this
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x (hE'E hx), map_one]
  · rw [Subgroup.card_map_of_injective f.injective, hE'4]
    norm_num

theorem exists_elementary_sixteen {S : Type*} [Group S] {V₁ V₂ : Subgroup S}
    (h₁c : ∀ x ∈ V₁, ∀ y ∈ V₁, x * y = y * x) (h₂c : ∀ x ∈ V₂, ∀ y ∈ V₂, x * y = y * x)
    (h₁2 : ∀ x ∈ V₁, x ^ 2 = 1) (h₂2 : ∀ x ∈ V₂, x ^ 2 = 1) (h₁4 : Nat.card V₁ = 4)
    (h₂4 : Nat.card V₂ = 4) (h12 : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x) (hinf : V₁ ⊓ V₂ = ⊥) :
    ∃ V : Subgroup S, (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x ^ 2 = 1) ∧
      Nat.card V = 16 := by
  have hcomm : ∀ (a : V₁) (b : V₂), Commute (V₁.subtype a) (V₂.subtype b) :=
    fun a b => h12 a a.2 b b.2
  set f : V₁ × V₂ →* S := V₁.subtype.noncommCoprod V₂.subtype hcomm with hf
  have hfapp : ∀ x : V₁ × V₂, f x = (x.1 : S) * (x.2 : S) := fun x => rfl
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hx
    rw [MonoidHom.mem_ker, hfapp] at hx
    have ha : (a : S) = (b : S)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hab : (a : S) ∈ V₁ ⊓ V₂ := ⟨a.2, ha ▸ V₂.inv_mem b.2⟩
    rw [hinf, mem_bot] at hab
    have hb : (b : S) = 1 := by rw [hab] at ha; exact inv_eq_one.mp ha.symm
    exact mem_bot.mpr (Prod.ext (Subtype.ext hab) (Subtype.ext hb))
  have hfc : ∀ x y : V₁ × V₂, f x * f y = f y * f x := by
    intro x y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (Subtype.ext (h₁c _ x.1.2 _ y.1.2)) (Subtype.ext (h₂c _ x.2.2 _ y.2.2))
  refine ⟨f.range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hfc x y
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Prod.ext (Subtype.ext (h₁2 _ x.1.2)) (Subtype.ext (h₂2 _ x.2.2))
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, h₁4, h₂4]

theorem pRank_le_of_injective {p : ℕ} (hp : 1 < p) {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Injective f) : pRank p G ≤ pRank p H := by
  rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
  exact pRank_top_le_of_injective hp f hf

section Kernel

variable {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
  {P : Subgroup Y} [P.Normal] {D : Subgroup P} [D.Characteristic]

omit [Finite Y] [Group.IsPerfect Y] in
theorem frattiniAction_conj_eq (y : Y) :
    (frattiniAction D).comp (MulAut.conjNormal (H := P)) y =
      autQuotient (frattini D) ((MulAut.characteristic D).comp (MulAut.conjNormal (H := P)) y) :=
  rfl

theorem odd_card_ker_frattiniAction_conj (hp2 : p ≠ 2) (hP : IsPGroup p P)
    (hE : layer (Y ⧸ P) = ⊤) (hZ : center (Y ⧸ P) = ⊥)
    (hR : ((frattiniAction D).comp (MulAut.conjNormal (H := P))).range ≠ ⊥)
    (hfix : ∀ t : Y, orderOf t = 2 →
      pRank p (D.map P.subtype ⊓ centralizer {t} : Subgroup Y) ≤ 2) :
    Odd (Nat.card ((frattiniAction D).comp (MulAut.conjNormal (H := P))).ker) := by
  classical
  set α := (frattiniAction D).comp (MulAut.conjNormal (H := P)) with hα
  set β : Y →* MulAut D := (MulAut.characteristic D).comp (MulAut.conjNormal (H := P)) with hβ
  have hDp : IsPGroup p D := hP.to_subgroup D
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := α.ker) 2 (even_iff_two_dvd.mp hodd)
  have ht2 : orderOf (t : Y) = 2 := by
    rw [← ht]
    exact (orderOf_injective α.ker.subtype Subtype.val_injective t)
  have hβt : β t = 1 := by
    have hmem : β t ∈ (autQuotient (frattini D)).ker := by
      rw [MonoidHom.mem_ker, ← frattiniAction_conj_eq]
      exact t.2
    have hpg := isPGroup_ker_autQuotient_frattini hDp
    obtain ⟨k, hk⟩ := hpg ⟨β t, hmem⟩
    have hsq : (β t) ^ 2 = 1 := by rw [← map_pow, ← ht2, pow_orderOf_eq_one, map_one]
    have hk' : (β t) ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
    have hord : orderOf (β t) ∣ Nat.gcd 2 (p ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hk')
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hord
  set s : Y := (t : Y) with hs
  have hcent : D.map P.subtype ⊓ centralizer {s} = D.map P.subtype := by
    refine inf_eq_left.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := congrArg (fun σ : MulAut D => (((σ ⟨d, hd⟩ : D) : P) : Y)) hβt
    simp only [hβ, MonoidHom.comp_apply, MulAut.characteristic_apply_apply_coe,
      MulAut.conjNormal_apply, MulAut.one_apply] at this
    change (d : Y) * s = s * d
    calc (d : Y) * s = s * d * s⁻¹ * s := by rw [this]
      _ = s * d := by group
  have hrankD : pRank p D ≤ 2 := by
    have h := hfix t ht2
    rw [hcent] at h
    refine le_trans (le_of_eq ?_) h
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_eq_of_mulEquiv hp.out.one_lt
      (D.equivMapOfInjective P.subtype P.subtype_injective)
  have hβ1 := centerless_semisimple_prime_quotient_rank_two_actions_vanish hp.out hp2 P hP hE hZ
    hDp hrankD β
  apply hR
  rw [eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  rw [mem_bot, frattiniAction_conj_eq, ← hβ, hβ1, MonoidHom.one_apply, map_one]

omit [Group.IsPerfect Y] in
theorem le_of_odd_card_normal (hE : layer (Y ⧸ P) = ⊤) (hZ : center (Y ⧸ P) = ⊥)
    {N : Subgroup Y} [N.Normal] (hN : Odd (Nat.card N)) : N ≤ P := by
  set π := QuotientGroup.mk' P
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective P)
  have hNodd : Odd (Nat.card (N.map π)) := Odd.of_dvd_nat hN (Subgroup.card_map_dvd N π)
  have hcomm : ∀ C : Subgroup (Y ⧸ P), IsComponent C → C ≤ centralizer (N.map π : Set (Y ⧸ P)) := by
    intro C hC
    rcases CFSG.LocalCores.component_normal_subgroup hC hNn with h | h
    · exfalso
      have hdvd := Subgroup.card_dvd_of_le h
      exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hNodd hdvd)) (even_card_of_isQuasisimple hC.1)
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 h
  have hlayer : layer (Y ⧸ P) ≤ centralizer (N.map π : Set (Y ⧸ P)) :=
    sSup_le fun C hC => hcomm C hC
  rw [hE, ← le_centralizer_iff, coe_top, centralizer_univ, hZ] at hlayer
  intro x hx
  have := hlayer (mem_map_of_mem π hx)
  rw [mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).mp this

omit [Group.IsPerfect Y] in
theorem false_of_elementary_sixteen (hp2 : p ≠ 2) (hP : IsPGroup p P)
    (hexp : Monoid.exponent D = p) (hclass : D.lowerCentralSeries 2 = ⊥)
    (hfix : ∀ t : Y, orderOf t = 2 →
      pRank p (D.map P.subtype ⊓ centralizer {t} : Subgroup Y) ≤ 2)
    (A : Subgroup Y) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hA16 : Nat.card A = 16)
    (hAfaith : ∀ a ∈ A, (∀ d ∈ D, a * ((d : P) : Y) * a⁻¹ = d) → a = 1) : False := by
  classical
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun x y => Subtype.ext (hAc _ x.2 _ y.2) }
  let _ : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, ofMul_eq_zero]
    exact Subtype.ext (hA2 _ (Additive.toMul x).2)
  set β : A →* MulAut D :=
    (MulAut.characteristic D).comp ((MulAut.conjNormal (H := P)).comp A.subtype) with hβ
  let _ : MulDistribMulAction A D := MulDistribMulAction.compHom D β
  have hβapp : ∀ (a : A) (d : D), ((β a d : D) : Y) = (a : Y) * ((d : P) : Y) * (a : Y)⁻¹ :=
    fun _ _ => rfl
  have hβ1 : ∀ a : A, β a = 1 → a = 1 := by
    intro a ha
    refine Subtype.ext (hAfaith a a.2 fun d hd => ?_)
    have := congrArg (fun σ : MulAut D => (((σ ⟨d, hd⟩ : D) : P) : Y)) ha
    simpa only [hβapp, MulAut.one_apply] using this
  have : FaithfulSMul A D := ⟨fun {a₁ a₂} h => by
    have hβeq : β a₁ = β a₂ := MulEquiv.ext h
    have : β (a₁ * a₂⁻¹) = 1 := by rw [map_mul, map_inv, hβeq, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hβ1 _ this)⟩
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hclass' : (⊤ : Subgroup D).lowerCentralSeries 2 = ⊥ := by
    have h := Subgroup.top_subtype_lowerCentralSeries D 2
    rw [hclass, Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective] at h
    exact h
  have hm : ∀ a : A, a ≠ 1 →
      pRank p (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D) ≤ 2 := by
    intro a ha
    have ha2 : orderOf (a : Y) = 2 :=
      orderOf_eq_prime (hA2 _ a.2) fun h => ha (Subtype.ext h)
    set F := CFSG.fixedPointSubgroup (Subgroup.zpowers a) D
    let g : F →* Y := P.subtype.comp (D.subtype.comp F.subtype)
    have hg : ∀ x : F, g x ∈ D.map P.subtype ⊓ centralizer {(a : Y)} := by
      intro x
      refine ⟨⟨(x : D), (x : D).2, rfl⟩, ?_⟩
      show g x ∈ centralizer {(a : Y)}
      rw [mem_centralizer_singleton_iff]
      have hx : β a (x : D) = (x : D) := x.2 ⟨a, mem_zpowers a⟩
      have := congrArg (fun d : D => ((d : P) : Y)) hx
      simp only [hβapp] at this
      change ((x : D) : Y) * a = a * ((x : D) : Y)
      calc ((x : D) : Y) * a = a * ((x : D) : Y) * (a : Y)⁻¹ * a := by rw [this]
        _ = a * ((x : D) : Y) := by group
    have hginj : Function.Injective (g.codRestrict _ hg) := by
      intro x y hxy
      have h1 : (g.codRestrict _ hg x : Y) = (g.codRestrict _ hg y : Y) := by rw [hxy]
      change g x = g y at h1
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    exact (pRank_le_of_injective hp.out.one_lt _ hginj).trans (hfix a ha2)
  have hbound := (CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound
    (hp.out.odd_of_ne_two hp2) hDp (hexp ▸ dvd_rfl) hclass' 4 2 (by rw [hA16]; norm_num) hm).1
  omega

end Kernel

theorem props_of_injective_map {G H : Type*} [Group G] [Group H] (π : G →* H) {A : Subgroup G}
    (hinj : Function.Injective (π.comp A.subtype)) {V : Subgroup H} (hAV : A.map π = V)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x ^ 2 = 1) :
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ (∀ x ∈ A, x ^ 2 = 1) ∧ Nat.card A = Nat.card V := by
  have hmem : ∀ x ∈ A, π x ∈ V := fun x hx => hAV ▸ mem_map_of_mem π hx
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, ?_⟩
  · have h1 : π (x * y) = π (y * x) := by rw [map_mul, map_mul, hVc _ (hmem x hx) _ (hmem y hy)]
    exact congrArg Subtype.val (@hinj ⟨x * y, mul_mem hx hy⟩ ⟨y * x, mul_mem hy hx⟩ h1)
  · have h1 : π (x ^ 2) = π 1 := by rw [map_pow, map_one, hV2 _ (hmem x hx)]
    exact congrArg Subtype.val (@hinj ⟨x ^ 2, pow_mem hx 2⟩ ⟨1, one_mem _⟩ h1)
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp, range_subtype,
      hAV]

section Components

variable {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
  {P : Subgroup Y} [P.Normal] {D : Subgroup P} [D.Characteristic]

theorem eq_of_isComponent (hp2 : p ≠ 2) (hP : IsPGroup p P) (hE : layer (Y ⧸ P) = ⊤)
    (hZ : center (Y ⧸ P) = ⊥) (hexp : Monoid.exponent D = p)
    (hclass : D.lowerCentralSeries 2 = ⊥)
    (hfix : ∀ t : Y, orderOf t = 2 →
      pRank p (D.map P.subtype ⊓ centralizer {t} : Subgroup Y) ≤ 2)
    (hKP : ((frattiniAction D).comp (MulAut.conjNormal (H := P))).ker ≤ P)
    {C₁ C₂ : Subgroup (Y ⧸ P)} (h₁ : IsComponent C₁) (h₂ : IsComponent C₂) : C₁ = C₂ := by
  classical
  by_contra hne
  have hcomm : ⁅C₁, C₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left hne
  have hZ₁ := center_eq_bot_of_isComponent hE hZ h₁
  have hZ₂ := center_eq_bot_of_isComponent hE hZ h₂
  obtain ⟨hs₁, hnab₁⟩ := isSimpleGroup_of_isQuasisimple h₁.1 hZ₁
  obtain ⟨hs₂, hnab₂⟩ := isSimpleGroup_of_isQuasisimple h₂.1 hZ₂
  obtain ⟨V₁, hV₁c, hV₁2, hV₁4⟩ := exists_four_group_of_isSimpleGroup hnab₁
  obtain ⟨V₂, hV₂c, hV₂2, hV₂4⟩ := exists_four_group_of_isSimpleGroup hnab₂
  have h12 : C₁ ≤ centralizer (C₂ : Set (Y ⧸ P)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
  obtain ⟨V, hVc, hV2, hV16⟩ := exists_elementary_sixteen (V₁ := V₁.map C₁.subtype)
    (V₂ := V₂.map C₂.subtype)
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact congrArg Subtype.val (hV₁c x hx y hy))
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact congrArg Subtype.val (hV₂c x hx y hy))
    (by rintro _ ⟨x, hx, rfl⟩; exact congrArg Subtype.val (hV₁2 x hx))
    (by rintro _ ⟨x, hx, rfl⟩; exact congrArg Subtype.val (hV₂2 x hx))
    (by rw [Subgroup.card_map_of_injective C₁.subtype_injective, hV₁4])
    (by rw [Subgroup.card_map_of_injective C₂.subtype_injective, hV₂4])
    (by
      rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
      exact (mem_centralizer_iff.1 (h12 x.2) y y.2).symm)
    (by
      rw [eq_bot_iff]
      rintro _ ⟨⟨x, -, rfl⟩, ⟨y, -, hxy⟩⟩
      have hx1 : x ∈ center C₁ := by
        rw [mem_center_iff]
        intro c
        apply Subtype.ext
        have hyc := mem_centralizer_iff.1 (h12 c.2) y y.2
        rw [show ((y : C₂) : Y ⧸ P) = (x : Y ⧸ P) from hxy] at hyc
        exact hyc.symm
      rw [hZ₁, mem_bot] at hx1
      rw [mem_bot, hx1]
      rfl)
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact (hp.out.odd_of_ne_two hp2).pow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2p : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hV16]; norm_num)
  obtain ⟨A, hA2p, hAV, hAinj⟩ := exists_two_subgroup_map_eq (QuotientGroup.mk' P)
    (QuotientGroup.mk'_surjective P) (by rw [QuotientGroup.ker_mk']; exact hPodd) V hV2p
  obtain ⟨hAc, hA2, hAcard⟩ := props_of_injective_map _ hAinj hAV hVc hV2
  refine false_of_elementary_sixteen hp2 hP hexp hclass hfix A hAc hA2 (hAcard.trans hV16)
    fun a ha hcent => ?_
  have hβ : (MulAut.characteristic D).comp (MulAut.conjNormal (H := P)) a = 1 := by
    ext d
    simp only [MonoidHom.comp_apply, MulAut.characteristic_apply_apply_coe,
      MulAut.conjNormal_apply, MulAut.one_apply]
    exact hcent d d.2
  have hK : a ∈ ((frattiniAction D).comp (MulAut.conjNormal (H := P))).ker := by
    rw [MonoidHom.mem_ker, frattiniAction_conj_eq, hβ, map_one]
  have haP : a ∈ A ⊓ P := ⟨ha, hKP hK⟩
  rw [inf_eq_bot_of_odd hA2p hPodd, mem_bot] at haP
  exact haP

end Components

noncomputable abbrev frattiniConjAction {Y : Type*} [Group Y] (P : Subgroup Y) [P.Normal]
    (D : Subgroup P) [D.Characteristic] : Y →* MulAut (D ⧸ frattini D) :=
  (frattiniAction D).comp (MulAut.conjNormal (H := P))

theorem frattiniConjAction_mk {Y : Type*} [Group Y] (P : Subgroup Y) [P.Normal]
    (D : Subgroup P) [D.Characteristic] (y : Y) (d : D) :
    frattiniConjAction P D y (d : D ⧸ frattini D) =
      ((MulAut.characteristic D (MulAut.conjNormal y) d : D) : D ⧸ frattini D) ∧
    (((MulAut.characteristic D (MulAut.conjNormal (H := P) y) d : D) : P) : Y) =
      y * ((d : P) : Y) * y⁻¹ :=
  ⟨rfl, rfl⟩

theorem exists_quotient_mulEquiv {R S : Type*} [Group R] [Group S] (ψ : R →* S)
    (hψ : Function.Surjective ψ) {B : Subgroup R} (hB : ψ.ker = B) :
    ∃ _ : B.Normal, ∃ e : (R ⧸ B) ≃* S, ∀ r, e (QuotientGroup.mk r) = ψ r := by
  subst hB
  exact ⟨inferInstance, QuotientGroup.quotientKerEquivOfSurjective ψ hψ, fun _ => rfl⟩

theorem exists_isComponent {S : Type*} [Group S] [Nontrivial S] (hE : layer S = ⊤) :
    ∃ C : Subgroup S, IsComponent C := by
  by_contra hnone
  push Not at hnone
  have hbot : layer S = ⊥ := sSup_eq_bot.2 fun C hC => absurd hC (hnone C)
  rw [hE] at hbot
  exact top_ne_bot hbot

theorem exists_range_hom_quotient {Y H : Type*} [Group Y] [Group H] (α : Y →* H)
    {P : Subgroup Y} [P.Normal] (hKP : α.ker ≤ P) :
    ∃ ψ : α.range →* Y ⧸ P, Function.Surjective ψ ∧ ψ.ker = P.map α.rangeRestrict ∧
      ∀ y : Y, ψ (α.rangeRestrict y) = y := by
  have hK' : α.ker ≤ (QuotientGroup.mk' P).ker := by rw [QuotientGroup.ker_mk']; exact hKP
  let ψ : α.range →* Y ⧸ P :=
    (QuotientGroup.lift α.ker (QuotientGroup.mk' P) hK').comp
      (QuotientGroup.quotientKerEquivRange α).symm.toMonoidHom
  have hψapp : ∀ y : Y, ψ (α.rangeRestrict y) = y := by
    intro y
    have h1 : (QuotientGroup.quotientKerEquivRange α).symm (α.rangeRestrict y) =
        (y : Y ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift α.ker (QuotientGroup.mk' P) hK'
      ((QuotientGroup.quotientKerEquivRange α).symm (α.rangeRestrict y)) = _
    rw [h1]
    rfl
  refine ⟨ψ, fun s => ?_, ?_, hψapp⟩
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨_, hψapp y⟩
  · ext r
    obtain ⟨y, rfl⟩ := α.rangeRestrict_surjective r
    rw [MonoidHom.mem_ker, hψapp, QuotientGroup.eq_one_iff]
    constructor
    · intro hy
      exact mem_map_of_mem _ hy
    · rintro ⟨x, hx, hxy⟩
      have h1 : α (x⁻¹ * y) = 1 := by
        have := congrArg Subtype.val hxy
        simp only [MonoidHom.coe_rangeRestrict] at this
        rw [map_mul, map_inv, this, inv_mul_cancel]
      have hy : y = x * (x⁻¹ * y) := by group
      rw [hy]
      exact P.mul_mem hx (hKP (MonoidHom.mem_ker.2 h1))

theorem le_pCore {p : ℕ} {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (hNp : IsPGroup p N) : N ≤ CFSG.pCore p G :=
  le_sSup ⟨hN, hNp⟩

theorem eq_pCore_of_simple_quotient {p : ℕ} {R S : Type*} [Group R] [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (φ : R →* S)
    (hφ : Function.Surjective φ) [Fact p.Prime] (hBp : IsPGroup p φ.ker) :
    φ.ker = CFSG.pCore p R := by
  refine le_antisymm (le_pCore inferInstance hBp) ?_
  have hOn : (CFSG.pCore p R).Normal := CFSG.pCore_normal
  have hOp : IsPGroup p (CFSG.pCore p R) := CFSG.pCore_isPGroup
  have := hOn.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore p R).map φ) with hbot | htop
  · rwa [Subgroup.map_eq_bot_iff] at hbot
  · exfalso
    have hSp : IsPGroup p S := by
      have h := hOp.map φ
      rw [htop] at h
      exact h.of_equiv Subgroup.topEquiv
    have : Group.IsPerfect S := isPerfect_of_isSimpleGroup' hnab
    obtain ⟨a, b, hab⟩ := hnab
    have : Nontrivial S := ⟨⟨a * b, b * a, hab⟩⟩
    exact Group.IsPerfect.not_isNilpotent S hSp.isNilpotent

theorem noncentral_odd_prime_kernel_simple_quotient {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y) [P.Normal]
    (hP : IsPGroup p P) (hP1 : P ≠ ⊥) (hE : layer (Y ⧸ P) = ⊤) (hZ : center (Y ⧸ P) = ⊥)
    (hYP : ⁅(⊤ : Subgroup Y), P⁆ ≠ ⊥) (hloc : localRank p Y ≤ 2) :
    ∃ D : Subgroup P, ∃ _ : D.Characteristic, D ≠ ⊥ ∧ Monoid.exponent D = p ∧
      ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P) ∧
      IsPGroup p (frattiniAction D).ker ∧ D.lowerCentralSeries 2 = ⊥ ∧
      (frattiniConjAction P D).range ≠ ⊥ ∧ Group.IsPerfect (frattiniConjAction P D).range ∧
      (∀ (n : ℕ) (e : D ⧸ frattini D ≃* Multiplicative (Fin n → ZMod p)),
        ∀ r ∈ (frattiniConjAction P D).range,
          Matrix.GeneralLinearGroup.det (elemAutEquivGL e r) = 1) ∧
      (∀ t : Y, orderOf t = 2 →
        pRank p (D.map P.subtype ⊓ centralizer {t} : Subgroup Y) ≤ 2 ∧
          Nat.card {w : D ⧸ frattini D // frattiniConjAction P D t w = w} ≤ p ^ 2) ∧
      IsSimpleGroup (Y ⧸ P) ∧ (∃ a b : Y ⧸ P, a * b ≠ b * a) ∧
      (frattiniConjAction P D).ker ≤ P ∧
      P.map (frattiniConjAction P D).rangeRestrict =
        CFSG.pCore p (frattiniConjAction P D).range ∧
      (∃ ψ : (frattiniConjAction P D).range →* Y ⧸ P, Function.Surjective ψ ∧
        ψ.ker = P.map (frattiniConjAction P D).rangeRestrict ∧
        ∀ y : Y, ψ ((frattiniConjAction P D).rangeRestrict y) = y) ∧
      (∃ _ : (P.map (frattiniConjAction P D).rangeRestrict).Normal,
        ∃ e : ((frattiniConjAction P D).range ⧸ P.map (frattiniConjAction P D).rangeRestrict) ≃*
          (Y ⧸ P), ∀ y : Y,
            e (QuotientGroup.mk ((frattiniConjAction P D).rangeRestrict y)) = QuotientGroup.mk y) ∧
      ∀ A : Subgroup Y, IsPGroup 2 A →
        Function.Injective ((frattiniConjAction P D).comp A.subtype) := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨D, hDc, hD1, hexp, hDZ, hker, hclass, hR, hRperf, hdet, hfixall⟩ :=
    odd_prime_kernel_critical_involution_fixed_spaces hp3 P hP hP1 hYP hloc
  refine ⟨D, hDc, hD1, hexp, hDZ, hker, hclass, hR, hRperf, hdet, hfixall, ?_⟩
  set α := frattiniConjAction P D with hα
  have hfix : ∀ t : Y, orderOf t = 2 →
      pRank p (D.map P.subtype ⊓ centralizer {t} : Subgroup Y) ≤ 2 := fun t ht => (hfixall t ht).1
  have hKodd : Odd (Nat.card α.ker) := odd_card_ker_frattiniAction_conj hp2 hP hE hZ hR hfix
  have hKP : α.ker ≤ P := le_of_odd_card_normal hE hZ hKodd
  have hSnt : Nontrivial (Y ⧸ P) := by
    by_contra hS
    rw [not_nontrivial_iff_subsingleton] at hS
    apply hR
    have hPtop : P = ⊤ := by
      rw [eq_top_iff]
      intro y _
      exact (QuotientGroup.eq_one_iff y).1 (Subsingleton.elim _ _)
    have hpg : IsPGroup p α.range := by
      rw [MonoidHom.range_eq_map, ← hPtop]
      exact hP.map α
    by_contra hne
    have : Nontrivial α.range := (nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent α.range hpg.isNilpotent
  have hCex : ∃ C : Subgroup (Y ⧸ P), IsComponent C := exists_isComponent hE
  obtain ⟨C, hC⟩ := hCex
  have huniq : ∀ C' : Subgroup (Y ⧸ P), IsComponent C' → C' = C := fun C' hC' =>
    eq_of_isComponent hp2 hP hE hZ hexp hclass hfix hKP hC' hC
  have hCtop : C = ⊤ := by
    rw [← hE, layer]
    exact le_antisymm (le_sSup hC) (sSup_le fun C' hC' => (huniq C' hC').le)
  rw [hCtop] at hC
  have hSq : IsQuasisimple (Y ⧸ P) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hC.1
  have hSsn : IsSimpleGroup (Y ⧸ P) ∧ ∃ a b : Y ⧸ P, a * b ≠ b * a :=
    isSimpleGroup_of_isQuasisimple hSq hZ
  obtain ⟨hSs, hSnab⟩ := hSsn
  have hψex := exists_range_hom_quotient α hKP
  obtain ⟨ψ, hψs, hψker, hψapp⟩ := hψex
  have hBp : IsPGroup p ψ.ker := hψker ▸ hP.map _
  refine ⟨hSs, hSnab, hKP, ?_, ⟨ψ, hψs, hψker, hψapp⟩, ?_,
    fun A hA => injective_restrict_of_odd α hKodd hA⟩
  · rw [← hψker]
    exact eq_pCore_of_simple_quotient hSnab ψ hψs hBp
  · have hiso := exists_quotient_mulEquiv ψ hψs hψker
    obtain ⟨hBn, e, he⟩ := hiso
    exact ⟨hBn, e, fun y => (he _).trans (hψapp y)⟩

end CFSG.RankThree.OddKernel
