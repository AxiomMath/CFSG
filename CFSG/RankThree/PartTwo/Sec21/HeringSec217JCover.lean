module

import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
public import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217JBasic
public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofON

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

namespace Item2113Res3Proof

theorem j217_exists_conj_of_sq {X Y : Type*} [Group X] [Finite X] [Group.IsPerfect X] [Group Y]
    (e : X ⧸ Subgroup.center X ≃* Y) (hY : Nat.card (Outer Y) ≤ 2) (σ : MulAut X) :
    ∃ k : X, σ ^ 2 = MulAut.conj k := by
  have hN : ∀ τ : MulAut X, Subgroup.map (τ : X →* X) (Subgroup.center X) =
      Subgroup.center X := fun τ => Subgroup.map_center_eq τ
  have hout : Nat.card (Outer (X ⧸ Subgroup.center X)) ≤ 2 := by
    rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  have := KFacts.OutFixCentralThree.finite_outer (X ⧸ Subgroup.center X)
  set σ' := KFacts.OutFixCentralThree.quotientAut (Subgroup.center X) hN σ with hσ'
  have hq1 : (σ' : Outer (X ⧸ Subgroup.center X)) ^ 2 = 1 := by
    have hc := pow_card_eq_one' (x := (σ' : Outer (X ⧸ Subgroup.center X)))
    have hpos : 0 < Nat.card (Outer (X ⧸ Subgroup.center X)) := Nat.card_pos
    obtain h | h : Nat.card (Outer (X ⧸ Subgroup.center X)) = 1 ∨
        Nat.card (Outer (X ⧸ Subgroup.center X)) = 2 := by omega
    · rw [h, pow_one] at hc
      rw [hc, one_pow]
    · rw [h] at hc
      exact hc
  have hmem : σ' ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (X ⧸ Subgroup.center X) := (QuotientGroup.eq_one_iff (σ' ^ 2)).mp (by
    rw [QuotientGroup.mk_pow]
    exact hq1)
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨k, ?_⟩
  have h1 : KFacts.OutFixCentralThree.quotientAut (Subgroup.center X) hN
      ((MulAut.conj k)⁻¹ * σ ^ 2) = 1 := by
    rw [map_mul, map_inv, KFacts.OutFixCentralThree.quotientAut_conj, hy, map_pow, ← hσ',
      inv_mul_cancel]
  exact (inv_mul_eq_one.mp
    (KFacts.OutFixCentralThree.eq_one_of_quotientAut_eq_one le_rfl hN h1)).symm

theorem j217_le_and_center_le_cover
    (hKA : KS217J3CoverPreimage)
    {G : Type} [Group G] [Finite G] {A J : Subgroup G} {d : G}
    (hAe : IsElemAbelian 3 A) (hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A)
    (hAN : A ≤ Subgroup.normalizer (J : Set G)) (hq : IsQuasisimple (lBar J))
    (hcov : Sec4.IsTripleCover (lBar J) NativeSporadic.J3) (h81 : Nat.card A = 3 ^ 4)
    (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hCA : A ⊓ Sec4.thetaQuotCentralizer J = Subgroup.zpowers d) :
    A ≤ J ∧ Subgroup.center (lBar J) ≤
      (A.subgroupOf J).map (QuotientGroup.mk' (aschbacherSolvableCore 3 J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (lBar J) := hq.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hcube : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  set ρ : A →* MulAut (lBar J) := (Item211Res2Proof.barAct J).comp (Subgroup.inclusion hAN)
  obtain ⟨e⟩ := hcov.2
  have hinner : ∀ a : A, ∃ k : lBar J, ρ a = MulAut.conj k := fun a =>
    exists_conj_of_pow_three e Sec4.card_outer_J3 (by rw [← map_pow, hcube a, map_one])
  have hker : ρ.ker = (Subgroup.zpowers d).subgroupOf A := by
    ext ⟨a, ha⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hCA]
    change Item211Res2Proof.barAct J ⟨a, hAN ha⟩ = 1 ↔ a ∈ A ⊓ Sec4.thetaQuotCentralizer J
    constructor
    · intro h
      refine ⟨ha, ⟨a, hAN ha⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      exact h
    · rintro ⟨-, n, hn, hna⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hn
      have hn' : n = ⟨a, hAN ha⟩ := Subtype.ext hna
      rw [← hn']
      exact hn
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have hker3 : Nat.card ρ.ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzA).toEquiv,
      Sec13.card_zpowers_of_pow_three hd3 hd1]
  have h81' : Nat.card A = 81 := by rw [h81]; norm_num
  have hrange : Nat.card ρ.range = 27 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hker3, h81'] at h
    omega
  set K : Subgroup (lBar J) := ρ.range.comap (MulAut.conj : lBar J →* MulAut (lBar J))
  have hmemK : ∀ k : lBar J, k ∈ K ↔ MulAut.conj k ∈ ρ.range := fun k => Iff.rfl
  have hZK : Subgroup.center (lBar J) ≤ K := fun z hz => by
    rw [hmemK, conj_eq_one_iff_mem_center.mpr hz]
    exact ρ.range.one_mem
  set κ : K →* MulAut (lBar J) := (MulAut.conj : lBar J →* MulAut (lBar J)).comp K.subtype
  have hκker : κ.ker = (Subgroup.center (lBar J)).subgroupOf K := by
    ext ⟨k, hk⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact conj_eq_one_iff_mem_center (k := k)
  have hκrange : κ.range = ρ.range := by
    ext σ
    constructor
    · intro hσ
      obtain ⟨⟨k, hk⟩, rfl⟩ := MonoidHom.mem_range.mp hσ
      exact (hmemK k).mp hk
    · intro hσ
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
      obtain ⟨k, hk⟩ := hinner a
      have hkK : k ∈ K := by rw [hmemK, ← hk]; exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨⟨k, hkK⟩, hk.symm⟩
  have hK81 : Nat.card K = 3 ^ 4 := by
    have h := Subgroup.card_ker_mul_card_range κ
    rw [hκker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hcov.1, hκrange,
      hrange] at h
    calc Nat.card K = 3 * 27 := h.symm
      _ = 3 ^ 4 := by norm_num
  have hρcomm : ∀ σ ∈ ρ.range, ∀ τ ∈ ρ.range, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hτ
    rw [← map_mul, ← map_mul, hAe.1.is_comm.comm a b]
  have hρcube : ∀ σ ∈ ρ.range, σ ^ 3 = 1 := by
    intro σ hσ
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
    rw [← map_pow, hcube a, map_one]
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (lBar J) := by
    intro x hx y hy
    rw [← conj_eq_one_iff_mem_center, map_mul, map_mul, map_mul, map_inv, map_inv,
      hρcomm _ ((hmemK x).mp hx) _ ((hmemK y).mp hy), mul_inv_cancel_right, mul_inv_cancel]
  have hKcube : ∀ x ∈ K, x ^ 3 ∈ Subgroup.center (lBar J) := by
    intro x hx
    rw [← conj_eq_one_iff_mem_center, map_pow]
    exact hρcube _ ((hmemK x).mp hx)
  have hKe : IsElemAbelian 3 K := hKA (lBar J) hq hcov K hZK hK81 hKcomm hKcube
  have hfix : ∀ x ∈ K, ∀ a (ha : a ∈ A), Item211Res2Proof.barAct J ⟨a, hAN ha⟩ x = x := by
    intro x hx a ha
    obtain ⟨k, hk⟩ := hinner ⟨a, ha⟩
    have hkK : k ∈ K := by rw [hmemK, ← hk]; exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
    have e1 : Item211Res2Proof.barAct J ⟨a, hAN ha⟩ = MulAut.conj k := hk
    have hkx : k * x = x * k := congrArg Subtype.val (hKe.1.is_comm.comm ⟨k, hkK⟩ ⟨x, hx⟩)
    rw [e1, MulAut.conj_apply, hkx, mul_inv_cancel_right]
  have hlift : K ≤ (A.subgroupOf J).map (QuotientGroup.mk' (aschbacherSolvableCore 3 J)) := by
    intro x hx
    obtain ⟨y, hy3, hyA, hyx⟩ :=
      Item211Res3Proof.exists_lift_of_fixed hAe hAN (hKe.2 x hx) (hfix x hx)
    have hyA' : (y : G) ∈ A := Item211Res3Proof.mem_of_commute_of_maximal hAe hmax hy3 hyA
    have hxy : x ∈ Subgroup.zpowers ((y : J) : lBar J) := hyx ▸ Subgroup.mem_zpowers x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxy
    refine ⟨y ^ m, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [Subgroup.coe_zpow]
      exact zpow_mem hyA' m
    · rw [map_zpow]
      exact hm
  have hP3 : IsPGroup 3 (A.subgroupOf J) := hA3.comap_subtype
  have hcardmap := Item211Res3Proof.card_map_of_injOn _ _
    (CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hP3)
  have hle := Subgroup.card_le_of_le hlift
  rw [hcardmap, hK81] at hle
  have hcardinf : Nat.card (A ⊓ J : Subgroup G) = Nat.card (A.subgroupOf J) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
  have heq : A ⊓ J = A :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardinf, h81]; exact hle)
  exact ⟨inf_eq_left.mp heq, hZK.trans hlift⟩

set_option maxRecDepth 20000 in
theorem j217_false_of_cover
    (hKA : KS217J3CoverPreimage)
    (hKB : KS217J3CoverNoTransvection) {G : Type} [Group G] [Finite G] {A J : Subgroup G}
    {d t : G} (hAe : IsElemAbelian 3 A)
    (hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A)
    (hAN : A ≤ Subgroup.normalizer (J : Set G)) (hq : IsQuasisimple (lBar J))
    (hcov : Sec4.IsTripleCover (lBar J) NativeSporadic.J3) (h81 : Nat.card A = 3 ^ 4)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hCA : A ⊓ Sec4.thetaQuotCentralizer J = Subgroup.zpowers d)
    (htA : t ∈ Subgroup.normalizer (A : Set G)) (htJ : t ∈ Subgroup.normalizer (J : Set G))
    (htr : IsTransvectionOn (A.normalizerMonoidHom ⟨t, htA⟩)) : False := by
  obtain ⟨hAJ', hZF⟩ := j217_le_and_center_le_cover hKA hAe hmax hAN hq hcov h81 hdA hd1 hCA
  have : Group.IsPerfect (lBar J) := hq.1
  obtain ⟨e⟩ := hcov.2
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 J) with hπ
  set F := (A.subgroupOf J).map π with hF
  have hinj : Set.InjOn π (A.subgroupOf J : Set J) :=
    CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hA3.comap_subtype
  have hFe : IsElemAbelian 3 F :=
    Sec4.Item462Proof.isElemAbelian_map' π (Item211Res3Proof.isElemAbelian_subgroupOf J hAe)
  have hF81 : Nat.card F = 3 ^ 4 := by
    rw [hF, Item211Res3Proof.card_map_of_injOn π _ hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ').toEquiv, h81]
  set j : A →* F := (π.comp (Subgroup.inclusion hAJ')).codRestrict F
    (fun a => ⟨⟨(a : G), hAJ' a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩) with hjdef
  have hjb : Function.Bijective j := by
    refine ⟨fun a b hab => ?_, fun z => ?_⟩
    · have h1 : π ⟨(a : G), hAJ' a.2⟩ = π ⟨(b : G), hAJ' b.2⟩ := congrArg Subtype.val hab
      have ha' : (⟨(a : G), hAJ' a.2⟩ : J) ∈ (A.subgroupOf J : Set J) :=
        Subgroup.mem_subgroupOf.mpr a.2
      have hb' : (⟨(b : G), hAJ' b.2⟩ : J) ∈ (A.subgroupOf J : Set J) :=
        Subgroup.mem_subgroupOf.mpr b.2
      have h2 : (⟨(a : G), hAJ' a.2⟩ : J) = ⟨(b : G), hAJ' b.2⟩ := hinj ha' hb' h1
      exact Subtype.ext (Subtype.mk.inj h2)
    · obtain ⟨l, hl, hlz⟩ := Subgroup.mem_map.mp z.2
      exact ⟨⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩, Subtype.ext hlz⟩
  set φ := A.normalizerMonoidHom ⟨t, htA⟩ with hφ
  set σ := Item211Res2Proof.barAct J ⟨t, htJ⟩ with hσ
  obtain ⟨k, hk⟩ := j217_exists_conj_of_sq e Sec4.card_outer_J3 σ
  have hσa : ∀ a : A, σ (π (Subgroup.inclusion hAJ' a)) =
      π (Subgroup.inclusion hAJ' (φ a)) := by
    intro a
    have h1 : σ (π (Subgroup.inclusion hAJ' a)) =
        π (J.normalizerMonoidHom ⟨t, htJ⟩ (Subgroup.inclusion hAJ' a)) :=
      Sec4.thetaQuotMulAut_mk _ _
    rw [h1]
    congr 1
  have hkact : ∀ a : A, k * π (Subgroup.inclusion hAJ' a) * k⁻¹ =
      π (Subgroup.inclusion hAJ' ((φ ^ 2) a)) := by
    intro a
    have h1 := congrArg (fun τ : MulAut (lBar J) => τ (π (Subgroup.inclusion hAJ' a))) hk
    simp only [MulAut.conj_apply] at h1
    rw [← h1, pow_two, MulAut.mul_apply, pow_two, MulAut.mul_apply, hσa, hσa]
  have hkF : ∀ z ∈ F, k * z * k⁻¹ ∈ F := by
    rintro _ ⟨x, hx, rfl⟩
    have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    have h1 := hkact ⟨x, hxA⟩
    change k * π x * k⁻¹ = _ at h1
    rw [h1]
    exact ⟨Subgroup.inclusion hAJ' ((φ ^ 2) ⟨x, hxA⟩),
      Subgroup.mem_subgroupOf.mpr ((φ ^ 2) ⟨x, hxA⟩).2, rfl⟩
  have hkN : k ∈ Subgroup.normalizer (F : Set (lBar J)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨z, hz, rfl⟩
      exact hkF z hz
    · exact (Subgroup.card_map_of_injective (MulAut.conj k).injective).ge
  have hint : ∀ a : A, F.normalizerMonoidHom ⟨k, hkN⟩ (j a) = j ((φ ^ 2) a) := by
    intro a
    apply Subtype.ext
    exact hkact a
  have hφ2 : IsTransvectionOn (φ ^ 2) := by
    rw [pow_two]
    exact j217_isTransvectionOn_sq htr
  exact hKB (lBar J) hq hcov F hFe hZF hF81 k hkN (isTransvectionOn_of_bijective j hjb hint hφ2)

end Item2113Res3Proof

end CFSG.RankThree.PartTwo.Sec21
