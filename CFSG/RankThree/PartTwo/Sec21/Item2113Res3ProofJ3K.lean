module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofJ3
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofON
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
import CFSG.RankThree.PartTwo.Sec4.Item462ProofCent
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def KS217J3CoverPreimage : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    Sec4.IsTripleCover X NativeSporadic.J3 →
    ∀ K : Subgroup X, Subgroup.center X ≤ K → Nat.card K = 3 ^ 4 →
      (∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center X) →
      (∀ x ∈ K, x ^ 3 ∈ Subgroup.center X) → IsElemAbelian 3 K

@[expose] def KS217J3CoverNoTransvection : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    Sec4.IsTripleCover X NativeSporadic.J3 →
    ∀ F : Subgroup X, IsElemAbelian 3 F → Subgroup.center X ≤ F → Nat.card F = 3 ^ 4 →
      ∀ (y : X) (hy : y ∈ Subgroup.normalizer (F : Set X)),
        ¬ IsTransvectionOn (F.normalizerMonoidHom ⟨y, hy⟩)

namespace Item2113Res3Proof

theorem conj_eq_one_iff_mem_center {X : Type*} [Group X] {k : X} :
    MulAut.conj k = 1 ↔ k ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h1 : k * g * k⁻¹ = g := by
      have := congrArg (fun σ : MulAut X => σ g) h
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc g * k = k * g * k⁻¹ * k := by rw [h1]
      _ = k * g := by group
  · intro h
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← h g, mul_inv_cancel_right]

theorem exists_conj_of_pow_three {X Y : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [Group Y] (e : X ⧸ Subgroup.center X ≃* Y) (hY : Nat.card (Outer Y) ≤ 2) {σ : MulAut X}
    (hσ : σ ^ 3 = 1) : ∃ k : X, σ = MulAut.conj k := by
  have hN : ∀ τ : MulAut X, Subgroup.map (τ : X →* X) (Subgroup.center X) =
      Subgroup.center X := fun τ => Subgroup.map_center_eq τ
  have hout : Nat.card (Outer (X ⧸ Subgroup.center X)) ≤ 2 := by
    rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  have := KFacts.OutFixCentralThree.finite_outer (X ⧸ Subgroup.center X)
  set σ' := KFacts.OutFixCentralThree.quotientAut (Subgroup.center X) hN σ with hσ'
  have hq3 : (σ' : Outer (X ⧸ Subgroup.center X)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hσ', ← map_pow, hσ, map_one, QuotientGroup.mk_one]
  have hq1 : (σ' : Outer (X ⧸ Subgroup.center X)) = 1 := by
    have hc := pow_card_eq_one' (x := (σ' : Outer (X ⧸ Subgroup.center X)))
    have hpos : 0 < Nat.card (Outer (X ⧸ Subgroup.center X)) := Nat.card_pos
    obtain h | h : Nat.card (Outer (X ⧸ Subgroup.center X)) = 1 ∨
        Nat.card (Outer (X ⧸ Subgroup.center X)) = 2 := by omega
    · rwa [h, pow_one] at hc
    · rw [h] at hc
      calc (σ' : Outer (X ⧸ Subgroup.center X))
          = (σ' : Outer (X ⧸ Subgroup.center X)) ^ 3 *
              ((σ' : Outer (X ⧸ Subgroup.center X)) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hq3, hc, inv_one, one_mul]
  have hmem : σ' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (X ⧸ Subgroup.center X) := (QuotientGroup.eq_one_iff σ').mp hq1
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨k, ?_⟩
  have h1 : KFacts.OutFixCentralThree.quotientAut (Subgroup.center X) hN
      ((MulAut.conj k)⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, KFacts.OutFixCentralThree.quotientAut_conj, hy, ← hσ', inv_mul_cancel]
  exact (inv_mul_eq_one.mp
    (KFacts.OutFixCentralThree.eq_one_of_quotientAut_eq_one le_rfl hN h1)).symm

theorem isTransvectionOn_of_bijective {P Q : Type*} [Group P] [Group Q] (j : P →* Q)
    (hj : Function.Bijective j) {φ : MulAut P} {ψ : MulAut Q} (h : ∀ a, ψ (j a) = j (φ a))
    (hφ : IsTransvectionOn φ) : IsTransvectionOn ψ := by
  have hcomm : commOf ψ = (commOf φ).map j := by
    simp only [commOf, MonoidHom.map_closure]
    congr 1
    ext q
    constructor
    · rintro ⟨q', rfl⟩
      obtain ⟨a, rfl⟩ := hj.2 q'
      exact ⟨a⁻¹ * φ a, ⟨a, rfl⟩, by simp only [map_mul, map_inv, h]⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨j a, by simp only [map_mul, map_inv, h]⟩
  obtain ⟨hcard, hfix⟩ := hφ
  refine ⟨by rw [hcomm, Subgroup.card_map_of_injective hj.1, hcard], ?_⟩
  rw [hcomm]
  rintro _ ⟨p, hp, rfl⟩
  have hp' : φ p = p := (mem_fixedSubgroupOf φ p).mp (hfix hp)
  rw [mem_fixedSubgroupOf, h, hp']

theorem le_and_center_le_of_j3
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hKA : KS217J3CoverPreimage) {G : Type} [Group G] [Finite G]
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hcov : Sec4.IsTripleCover (lBar L) NativeSporadic.J3) (h81 : Nat.card A = 3 ^ 4) :
    A ≤ L ∧ Subgroup.center (lBar L) ≤
      (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hcE, -⟩, hc1, hLs, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hmax := hpair.mem_S.1.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have : Group.IsPerfect (lBar L) := hq.1
  have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
  rw [Sec13.sectionCentralizer_eq_inf hAN] at hsc
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := SetLike.coe_injective hsc
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hcube : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  set ρ : A →* MulAut (lBar L) := (Item211Res2Proof.barAct L).comp (Subgroup.inclusion hAN)
  obtain ⟨e⟩ := hcov.2
  have hinner : ∀ a : A, ∃ k : lBar L, ρ a = MulAut.conj k := fun a =>
    exists_conj_of_pow_three e Sec4.card_outer_J3 (by rw [← map_pow, hcube a, map_one])
  have hker : ρ.ker = (Subgroup.zpowers c).subgroupOf A := by
    ext ⟨a, ha⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hCA]
    change Item211Res2Proof.barAct L ⟨a, hAN ha⟩ = 1 ↔ a ∈ A ⊓ Sec4.thetaQuotCentralizer L
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
  have hzA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  have hker3 : Nat.card ρ.ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzA).toEquiv,
      Sec13.card_zpowers_of_pow_three hc3 hc1]
  have h81' : Nat.card A = 81 := by rw [h81]; norm_num
  have hrange : Nat.card ρ.range = 27 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hker3, h81'] at h
    omega
  set K : Subgroup (lBar L) := ρ.range.comap (MulAut.conj : lBar L →* MulAut (lBar L))
  have hmemK : ∀ k : lBar L, k ∈ K ↔ MulAut.conj k ∈ ρ.range := fun k => Iff.rfl
  have hZK : Subgroup.center (lBar L) ≤ K := fun z hz => by
    rw [hmemK, conj_eq_one_iff_mem_center.mpr hz]
    exact ρ.range.one_mem
  set κ : K →* MulAut (lBar L) := (MulAut.conj : lBar L →* MulAut (lBar L)).comp K.subtype
  have hκker : κ.ker = (Subgroup.center (lBar L)).subgroupOf K := by
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
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (lBar L) := by
    intro x hx y hy
    rw [← conj_eq_one_iff_mem_center, map_mul, map_mul, map_mul, map_inv, map_inv,
      hρcomm _ ((hmemK x).mp hx) _ ((hmemK y).mp hy), mul_inv_cancel_right, mul_inv_cancel]
  have hKcube : ∀ x ∈ K, x ^ 3 ∈ Subgroup.center (lBar L) := by
    intro x hx
    rw [← conj_eq_one_iff_mem_center, map_pow]
    exact hρcube _ ((hmemK x).mp hx)
  have hKe : IsElemAbelian 3 K := hKA (lBar L) hq hcov K hZK hK81 hKcomm hKcube
  have hfix : ∀ x ∈ K, ∀ a (ha : a ∈ A), Item211Res2Proof.barAct L ⟨a, hAN ha⟩ x = x := by
    intro x hx a ha
    obtain ⟨k, hk⟩ := hinner ⟨a, ha⟩
    have hkK : k ∈ K := by rw [hmemK, ← hk]; exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
    have e1 : Item211Res2Proof.barAct L ⟨a, hAN ha⟩ = MulAut.conj k := hk
    have hkx : k * x = x * k := congrArg Subtype.val (hKe.1.is_comm.comm ⟨k, hkK⟩ ⟨x, hx⟩)
    rw [e1, MulAut.conj_apply, hkx, mul_inv_cancel_right]
  have hlift : K ≤ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
    intro x hx
    obtain ⟨y, hy3, hyA, hyx⟩ :=
      Item211Res3Proof.exists_lift_of_fixed hAe hAN (hKe.2 x hx) (hfix x hx)
    have hyA' : (y : G) ∈ A := Item211Res3Proof.mem_of_commute_of_maximal hAe hmax hy3 hyA
    have hxy : x ∈ Subgroup.zpowers ((y : L) : lBar L) := hyx ▸ Subgroup.mem_zpowers x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxy
    refine ⟨y ^ m, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [Subgroup.coe_zpow]
      exact zpow_mem hyA' m
    · rw [map_zpow]
      exact hm
  have hP3 : IsPGroup 3 (A.subgroupOf L) := hA3.comap_subtype
  have hcardmap := Item211Res3Proof.card_map_of_injOn _ _
    (CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hP3)
  have hle := Subgroup.card_le_of_le hlift
  rw [hcardmap, hK81] at hle
  have hcardinf : Nat.card (A ⊓ L : Subgroup G) = Nat.card (A.subgroupOf L) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
  have heq : A ⊓ L = A :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardinf, h81]; exact hle)
  exact ⟨inf_eq_left.mp heq, hZK.trans hlift⟩

theorem item217InLNoTransCover_of
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hKA : KS217J3CoverPreimage) (hKB : KS217J3CoverNoTransvection) :
    Item217InLNoTransCover := by
  intro G _ _ A E U c L hpair _ _ hcov h81 _ x hx htr
  obtain ⟨hAL, hZF⟩ := le_and_center_le_of_j3 h45 h66 hKA hpair hcov h81
  obtain ⟨-, -, hLs, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  set F := (A.subgroupOf L).map π with hF
  have hinj : Set.InjOn π (A.subgroupOf L : Set L) :=
    CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hA3.comap_subtype
  have hFe : IsElemAbelian 3 F :=
    Sec4.Item462Proof.isElemAbelian_map' π (Item211Res3Proof.isElemAbelian_subgroupOf L hAe)
  have hF81 : Nat.card F = 3 ^ 4 := by
    rw [hF, Item211Res3Proof.card_map_of_injOn π _ hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, h81]
  obtain ⟨n, hnL, rfl⟩ := hx
  set n' : L := ⟨(n : G), Subgroup.mem_subgroupOf.mp hnL⟩
  have hn'N : n' ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp n.2 (h : G)
  have hyF : π n' ∈ Subgroup.normalizer (F : Set (lBar L)) :=
    Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hn'N)
  set j : A →* F := (π.comp (Subgroup.inclusion hAL)).codRestrict F
    (fun a => ⟨⟨(a : G), hAL a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩)
  have hjb : Function.Bijective j := by
    refine ⟨fun a b hab => ?_, fun z => ?_⟩
    · have h1 : π ⟨(a : G), hAL a.2⟩ = π ⟨(b : G), hAL b.2⟩ := congrArg Subtype.val hab
      have ha' : (⟨(a : G), hAL a.2⟩ : L) ∈ (A.subgroupOf L : Set L) :=
        Subgroup.mem_subgroupOf.mpr a.2
      have hb' : (⟨(b : G), hAL b.2⟩ : L) ∈ (A.subgroupOf L : Set L) :=
        Subgroup.mem_subgroupOf.mpr b.2
      have h2 : (⟨(a : G), hAL a.2⟩ : L) = ⟨(b : G), hAL b.2⟩ := hinj ha' hb' h1
      exact Subtype.ext (Subtype.mk.inj h2)
    · obtain ⟨l, hl, hlz⟩ := Subgroup.mem_map.mp z.2
      exact ⟨⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩, Subtype.ext hlz⟩
  have hint : ∀ a : A, F.normalizerMonoidHom ⟨π n', hyF⟩ (j a) =
      j (A.normalizerMonoidHom n a) := by
    intro a
    apply Subtype.ext
    change π n' * π ⟨(a : G), hAL a.2⟩ * (π n')⁻¹ = π (n' * ⟨(a : G), hAL a.2⟩ * n'⁻¹)
    rw [map_mul, map_mul, map_inv]
  exact hKB (lBar L) hq hcov F hFe hZF hF81 (π n') hyF
    (isTransvectionOn_of_bijective j hjb hint htr)

theorem item217InLNoTrans_of_kfacts
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hKA : KS217J3CoverPreimage) (hKB : KS217J3CoverNoTransvection) :
    Item217InLNoTrans :=
  item217InLNoTrans_of (item217InLNoTransCover_of h45 h66 hKA hKB)

end Item2113Res3Proof

end CFSG.RankThree.PartTwo.Sec21
