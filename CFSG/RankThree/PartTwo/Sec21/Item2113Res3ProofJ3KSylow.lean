module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofJ3K
import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofON
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
import CFSG.RankThree.PartTwo.Sec4.Item462ProofCent
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def KS217J3CoverSylowFix : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    Sec4.IsTripleCover X NativeSporadic.J3 →
    ∀ F : Subgroup X, IsElemAbelian 3 F → Subgroup.center X ≤ F → Nat.card F = 3 ^ 4 →
      ∀ f ∈ F, (∀ (y : X) (hy : y ∈ Subgroup.normalizer (F : Set X)),
        (∃ k : ℕ, F.normalizerMonoidHom ⟨y, hy⟩ ^ 3 ^ k = 1) → y * f * y⁻¹ = f) →
        f ∈ Subgroup.center X

namespace Item2113Res3Proof

theorem exists_conj_of_pow_three_pow {X Y : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [Group Y] (e : X ⧸ Subgroup.center X ≃* Y) (hY : Nat.card (Outer Y) ≤ 2) {σ : MulAut X}
    {k : ℕ} (hσ : σ ^ 3 ^ k = 1) : ∃ x : X, σ = MulAut.conj x := by
  have hN : ∀ τ : MulAut X, Subgroup.map (τ : X →* X) (Subgroup.center X) =
      Subgroup.center X := fun τ => Subgroup.map_center_eq τ
  have hout : Nat.card (Outer (X ⧸ Subgroup.center X)) ≤ 2 := by
    rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  have := KFacts.OutFixCentralThree.finite_outer (X ⧸ Subgroup.center X)
  set σ' := KFacts.OutFixCentralThree.quotientAut (Subgroup.center X) hN σ with hσ'
  have hq3 : (σ' : Outer (X ⧸ Subgroup.center X)) ^ 3 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hσ', ← map_pow, hσ, map_one, QuotientGroup.mk_one]
  have hq1 : (σ' : Outer (X ⧸ Subgroup.center X)) = 1 := by
    have hc := pow_card_eq_one' (x := (σ' : Outer (X ⧸ Subgroup.center X)))
    have hpos : 0 < Nat.card (Outer (X ⧸ Subgroup.center X)) := Nat.card_pos
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    obtain h | h : Nat.card (Outer (X ⧸ Subgroup.center X)) = 1 ∨
        Nat.card (Outer (X ⧸ Subgroup.center X)) = 2 := by omega
    · rwa [h, pow_one] at hc
    · rw [h] at hc
      rw [hm, pow_succ, pow_mul, hc, one_pow, one_mul] at hq3
      exact hq3
  have hmem : σ' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (X ⧸ Subgroup.center X) := (QuotientGroup.eq_one_iff σ').mp hq1
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x, ?_⟩
  have h1 : KFacts.OutFixCentralThree.quotientAut (Subgroup.center X) hN
      ((MulAut.conj x)⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, KFacts.OutFixCentralThree.quotientAut_conj, hy, ← hσ', inv_mul_cancel]
  exact (inv_mul_eq_one.mp
    (KFacts.OutFixCentralThree.eq_one_of_quotientAut_eq_one le_rfl hN h1)).symm

theorem exists_fixed_of_isPGroup {G : Type} [Group G] [Finite G] {A R : Subgroup G}
    (hR : IsPGroup 3 R) (hRN : R ≤ Subgroup.normalizer (A : Set G)) (hA : 3 ∣ Nat.card A) :
    ∃ b ∈ A, b ≠ 1 ∧ ∀ r ∈ R, r * b * r⁻¹ = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : MulAction ↥R ↥A :=
    MulAction.compHom ↥A (A.normalizerMonoidHom.comp (Subgroup.inclusion hRN))
  have h1 : (1 : A) ∈ MulAction.fixedPoints ↥R ↥A := fun r => by
    show A.normalizerMonoidHom (Subgroup.inclusion hRN r) 1 = 1
    exact map_one _
  obtain ⟨b, hb, hb1⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := A) hA h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun r hr => ?_⟩
  exact congrArg Subtype.val (hb ⟨r, hr⟩)

theorem exists_lift_normalizer {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    (hAL : A ≤ L) (hA3 : IsPGroup 3 A) {x : lBar L}
    (hx : x ∈ Subgroup.normalizer
      ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) : Set (lBar L))) :
    ∃ l : L, (l : G) ∈ Subgroup.normalizer (A : Set G) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) l = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥(A.subgroupOf L)) := ⟨hA3.comap_subtype⟩
  have hcop : Nat.Coprime 3 (Nat.card (aschbacherSolvableCore 3 L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore
  have h : Subgroup.normalizer
      ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) : Set (lBar L)) =
      (Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L)).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :=
    CFSG.normalizer_map_quotient_eq_map_normalizer 3 (A.subgroupOf L)
      (aschbacherSolvableCore 3 L) inferInstance hcop
  rw [h] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l, ?_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff.mp hl ⟨g, hAL hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg))
  · intro hg
    have hgL : g ∈ L := by
      have e : g = (l : G)⁻¹ * ((l : G) * g * (l : G)⁻¹) * l := by group
      rw [e]
      exact L.mul_mem (L.mul_mem (L.inv_mem l.2) (hAL hg)) l.2
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff.mp hl ⟨g, hgL⟩).mpr (Subgroup.mem_subgroupOf.mpr hg))

theorem conj_eq_of_mk_conj_eq {G : Type} [Group G] [Finite G] {A L : Subgroup G} (hAL : A ≤ L)
    (hA3 : IsPGroup 3 A) {u : L} (huN : (u : G) ∈ Subgroup.normalizer (A : Set G)) {a : G}
    (ha : a ∈ A)
    (h : QuotientGroup.mk' (aschbacherSolvableCore 3 L) u *
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨a, hAL ha⟩ *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) u)⁻¹ =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨a, hAL ha⟩) :
    (u : G) * a * (u : G)⁻¹ = a := by
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
    (hA3.comap_subtype (K := L))
  have h1 : (u * ⟨a, hAL ha⟩ * u⁻¹ : L) ∈ (A.subgroupOf L : Set L) :=
    Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp huN a).mp ha)
  have h2 : (⟨a, hAL ha⟩ : L) ∈ (A.subgroupOf L : Set L) := Subgroup.mem_subgroupOf.mpr ha
  have h3 := hinj h1 h2 (by rw [map_mul, map_mul, map_inv]; exact h)
  exact congrArg Subtype.val h3

theorem mem_zpowers_of_mk_mem_center {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}
    (hAL : A ≤ L) (hA3 : IsPGroup 3 A) (hcA : c ∈ A) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hLC : L ≤ Subgroup.centralizer ({c} : Set G))
    (hZ3 : Nat.card (Subgroup.center (lBar L)) = 3) {a : G} (ha : a ∈ A)
    (haZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨a, hAL ha⟩ ∈
      Subgroup.center (lBar L)) : a ∈ Subgroup.zpowers c := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three (hA3.comap_subtype (K := L))
  set c' : L := ⟨c, hAL hcA⟩ with hc'
  have hcZ : π c' ∈ Subgroup.center (lBar L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC l.2))
  have hc'3 : π c' ^ 3 = 1 := by
    rw [← map_pow]
    have : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'] using hc3)
    rw [this, map_one]
  have hc'1 : π c' ≠ 1 := by
    intro h
    have h2 : c' = 1 :=
      hinj (Subgroup.mem_subgroupOf.mpr hcA) (Subgroup.one_mem _) (by rw [h, map_one])
    exact hc1 (congrArg Subtype.val h2)
  have hZ : Subgroup.zpowers (π c') = Subgroup.center (lBar L) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcZ)
      (by rw [hZ3, Sec13.card_zpowers_of_pow_three hc'3 hc'1])
  rw [← hZ] at haZ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp haZ
  have h1 : (c' ^ n : L) ∈ (A.subgroupOf L : Set L) :=
    Subgroup.zpow_mem _ (Subgroup.mem_subgroupOf.mpr hcA) n
  have h2 : (⟨a, hAL ha⟩ : L) ∈ (A.subgroupOf L : Set L) := Subgroup.mem_subgroupOf.mpr ha
  have h3 := hinj h1 h2 (by rw [map_zpow]; exact hn)
  have h4 : c ^ n = a := by
    have := congrArg Subtype.val h3
    rwa [Subgroup.coe_zpow] at this
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, h4⟩

theorem item217InLSylowCover_of
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hKA : KS217J3CoverPreimage) (hKC : KS217J3CoverSylowFix) :
    Item217InLSylowCover := by
  intro G _ _ A E U c L hpair _ _ hcov h81 hext
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAL, hZF⟩ := le_and_center_le_of_j3 h45 h66 hKA hpair hcov h81
  obtain ⟨⟨hcE, -⟩, hc1, hLs, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have : Group.IsPerfect (lBar L) := hq.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  obtain ⟨e⟩ := hcov.2
  set W := Subgroup.normalizer (A : Set G) with hW
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set F := (A.subgroupOf L).map π with hF
  have hinj : Set.InjOn π (A.subgroupOf L : Set L) :=
    CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hA3.comap_subtype
  have hFe : IsElemAbelian 3 F :=
    Sec4.Item462Proof.isElemAbelian_map' π (Item211Res3Proof.isElemAbelian_subgroupOf L hAe)
  have hF81 : Nat.card F = 3 ^ 4 := by
    rw [hF, Item211Res3Proof.card_map_of_injOn π _ hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, h81]
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := hext
  have hK9 : Nat.card K = 3 ^ 2 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_prod, ZMod.card]
    norm_num
  have hQ8 : Nat.card (starOf A L ⧸ K) = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have h3K : ∀ (x : starOf A L) (k : ℕ), x ^ 3 ^ k = 1 → x ∈ K := by
    intro x k hx
    have h1 : (x : starOf A L ⧸ K) ^ 3 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
    have h2 : (x : starOf A L ⧸ K) ^ 8 = 1 := by
      rw [← hQ8]
      exact pow_card_eq_one'
    have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by decide)), pow_one] at h3
    exact (QuotientGroup.eq_one_iff x).mp h3
  have hLW : starOf A L ≤ wStar A := starOf_le_wStar A L
  have hK3 : IsPGroup 3 K := IsPGroup.of_card hK9
  obtain ⟨P, hKP⟩ := (hK3.map (Subgroup.inclusion hLW)).exists_le_sylow
  have hψs : Function.Surjective A.normalizerMonoidHom.rangeRestrict :=
    A.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨R, hR⟩ := Sylow.mapSurjective_surjective hψs 3 P
  have hPR : ∀ x ∈ (P : Subgroup (wStar A)), ∃ r ∈ (R : Subgroup W),
      A.normalizerMonoidHom r = (x : MulAut A) := by
    intro x hx
    rw [← hR, Sylow.coe_mapSurjective] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨r, hr, rfl⟩
  set RG : Subgroup G := (R : Subgroup W).map W.subtype with hRG
  have hRGp : IsPGroup 3 RG := R.isPGroup'.map W.subtype
  have hRGN : RG ≤ W := Subgroup.map_subtype_le _
  obtain ⟨b, hbA, hb1, hbR⟩ := exists_fixed_of_isPGroup hRGp hRGN (by rw [h81]; norm_num)
  have hbF : π ⟨b, hAL hbA⟩ ∈ F :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbA)
  have hbZ : π ⟨b, hAL hbA⟩ ∈ Subgroup.center (lBar L) := by
    refine hKC (lBar L) hq hcov F hFe hZF hF81 _ hbF ?_
    rintro x hx ⟨k, hk⟩
    obtain ⟨y, hyN, rfl⟩ := exists_lift_normalizer hAL hA3 hx
    have hw3 : A.normalizerMonoidHom ⟨(y : G), hyN⟩ ^ 3 ^ k = 1 := by
      rw [← map_pow] at hk ⊢
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      have huN : ((y ^ 3 ^ k : L) : G) ∈ W := by
        rw [Subgroup.coe_pow]
        exact pow_mem hyN _
      have haF : π ⟨a, hAL a.2⟩ ∈ F :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr a.2)
      have h1 : ((F.normalizerMonoidHom (⟨π y, hx⟩ ^ 3 ^ k) ⟨π ⟨a, hAL a.2⟩, haF⟩ : F) :
          lBar L) = π ⟨a, hAL a.2⟩ := by
        rw [hk]
        rfl
      have h2 : π (y ^ 3 ^ k) * π ⟨a, hAL a.2⟩ * (π (y ^ 3 ^ k))⁻¹ = π ⟨a, hAL a.2⟩ := h1
      have h3 := conj_eq_of_mk_conj_eq hAL hA3 huN a.2 h2
      rw [Subgroup.coe_pow] at h3
      exact h3
    have hwL : A.normalizerMonoidHom ⟨(y : G), hyN⟩ ∈ starOf A L :=
      ⟨⟨(y : G), hyN⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    have hwK : (⟨A.normalizerMonoidHom ⟨(y : G), hyN⟩, hwL⟩ : starOf A L) ∈ K :=
      h3K _ k (Subtype.ext hw3)
    obtain ⟨r, hr, hrw⟩ := hPR _ (hKP (Subgroup.mem_map_of_mem _ hwK))
    have h1 : (r : G) * b * (r : G)⁻¹ = (y : G) * b * (y : G)⁻¹ :=
      congrArg (fun σ : MulAut A => ((σ ⟨b, hbA⟩ : A) : G)) hrw
    have h2 : (y : G) * b * (y : G)⁻¹ = b := by
      rw [← h1]
      exact hbR _ (Subgroup.mem_map_of_mem W.subtype hr)
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext h2)
  have hbc : b ∈ Subgroup.zpowers c :=
    mem_zpowers_of_mk_mem_center hAL hA3 hcA hc3 hc1 hLC hcov.1 hbA hbZ
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hcb : c ∈ Subgroup.zpowers b := by
    have heq : Subgroup.zpowers b = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbc)
        (by rw [Sec13.card_zpowers_of_pow_three hc3 hc1, Sec13.card_zpowers_of_pow_three hb3 hb1])
    rw [heq]
    exact Subgroup.mem_zpowers c
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcb
  have hRC : RG ≤ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * c * g⁻¹ = c := by rw [← hm, ← conj_zpow, hbR g hg]
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [h1]
  have hRL : RG ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hpair.standing.toTheoremFourHyp hc3
      hc1 hRGp hRC L hLc
  have hRstar : ∀ r ∈ (R : Subgroup W), A.normalizerMonoidHom r ∈ starOf A L := by
    intro r hr
    have hrNL : (r : G) ∈ Subgroup.normalizer (L : Set G) :=
      hRL (Subgroup.mem_map_of_mem W.subtype hr)
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨r, hr⟩
    have hk' : (r : G) ^ 3 ^ k = 1 := by
      have := congrArg (fun x : (R : Subgroup W) => ((x : W) : G)) hk
      simpa using this
    set σ := Item211Res2Proof.barAct L ⟨r, hrNL⟩ with hσdef
    have hσ3 : σ ^ 3 ^ k = 1 := by
      rw [hσdef, ← map_pow]
      have : (⟨r, hrNL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using hk')
      rw [this, map_one]
    obtain ⟨x, hx⟩ := exists_conj_of_pow_three_pow e Sec4.card_outer_J3 hσ3
    have hxF : x ∈ Subgroup.normalizer (F : Set (lBar L)) := by
      have hle : F.map (MulAut.conj x).toMonoidHom ≤ F := by
        rintro _ ⟨f, hf, rfl⟩
        obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hf
        have e1 : (MulAut.conj x).toMonoidHom (π l) =
            π (L.normalizerMonoidHom ⟨r, hrNL⟩ l) := by
          show MulAut.conj x (π l) = _
          rw [← hx]
          rfl
        rw [e1]
        refine Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ?_)
        exact (Subgroup.mem_normalizer_iff.mp r.2 l).mp (Subgroup.mem_subgroupOf.mp hl)
      have heq : F.map (MulAut.conj x).toMonoidHom = F :=
        Subgroup.eq_of_le_of_card_ge hle
          (by rw [Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
            (MulAut.conj x).injective])
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    obtain ⟨ℓ, hℓN, hℓ⟩ := exists_lift_normalizer hAL hA3 hxF
    refine ⟨⟨(ℓ : G), hℓN⟩, Subgroup.mem_subgroupOf.mpr ℓ.2, ?_⟩
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change (ℓ : G) * a * (ℓ : G)⁻¹ = (r : G) * a * (r : G)⁻¹
    have h1 : (ℓ * ⟨a, hAL a.2⟩ * ℓ⁻¹ : L) ∈ (A.subgroupOf L : Set L) :=
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hℓN a).mp a.2)
    have h2 : (L.normalizerMonoidHom ⟨r, hrNL⟩ ⟨a, hAL a.2⟩ : L) ∈ (A.subgroupOf L : Set L) :=
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp r.2 a).mp a.2)
    have h3 : π (ℓ * ⟨a, hAL a.2⟩ * ℓ⁻¹) =
        π (L.normalizerMonoidHom ⟨r, hrNL⟩ ⟨a, hAL a.2⟩) := by
      rw [map_mul, map_mul, map_inv, hℓ]
      change MulAut.conj x (π ⟨a, hAL a.2⟩) = σ (π ⟨a, hAL a.2⟩)
      rw [hx]
    exact congrArg Subtype.val (hinj h1 h2 h3)
  refine ⟨P, fun x hx => ?_⟩
  obtain ⟨r, hr, hrx⟩ := hPR x hx
  rw [← hrx]
  exact hRstar r hr

theorem item217InLSylow_of_kfacts
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hKA : KS217J3CoverPreimage) (hKC : KS217J3CoverSylowFix) :
    Item217InLSylow :=
  item217InLSylow_of (item217InLSylowCover_of h45 h66 hKA hKC)

end Item2113Res3Proof

end CFSG.RankThree.PartTwo.Sec21
