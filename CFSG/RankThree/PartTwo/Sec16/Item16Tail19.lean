module

import CFSG.RankThree.PartTwo.Sec11.Item1116Proof
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec13.Item13Theta
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec16.Item16Statements
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def Step1619Sz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Item167 A (lB A) c L → ∀ Y ∈ scriptY1 A (lB A), ¬ Group.IsSolvable ↥Y →
      ∃ (K : Subgroup G) (n : ℕ), K ≤ Y ∧ A ≤ Subgroup.normalizer (K : Set G) ∧
        generalizedFitting ↥K = CFSG.pCore 2 ↥K ∧
        CFSG.Blueprint.SuzukiModel (↥K ⧸ CFSG.pCore 2 ↥K) 2 n

@[expose] noncomputable def KS1619SzFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (c : G) (n : ℕ),
    c ∈ Subgroup.normalizer (K : Set G) → c ^ 3 = 1 → ¬ 3 ∣ Nat.card K →
    CFSG.Blueprint.SuzukiModel (↥K ⧸ CFSG.pCore 2 ↥K) 2 n → 3 < n →
      2 ∣ Nat.card (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)))

@[expose] noncomputable def KS1619LCen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J : Subgroup G) (n : ℕ), IsSimpleGroup ↥L → 1 ≤ n →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n →
    J ≤ Subgroup.normalizer (L : Set G) → Group.IsPerfect J → ¬ 3 ∣ Nat.card J →
      J ≤ Subgroup.centralizer (L : Set G)

@[expose] noncomputable def KS1619Sec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q X : Subgroup G) (c : G), IsPGroup 2 Q →
    Nat.card X = 13 → X ≤ Subgroup.normalizer (Q : Set G) →
    c ∈ Subgroup.normalizer (Q : Set G) → c ∈ Subgroup.normalizer (X : Set G) → c ^ 3 = 1 →
    (∀ x ∈ X, c * x * c⁻¹ = x → x = 1) → X ⊓ Subgroup.centralizer (Q : Set G) = ⊥ →
      ∃ E N : Subgroup G, N ≤ E ∧ E ≤ Q ⊓ Subgroup.centralizer ({c} : Set G) ∧
        ∃ _ : (N.subgroupOf E).Normal,
          IsElementaryAbelian 2 (↥E ⧸ N.subgroupOf E) ∧ Nat.card (↥E ⧸ N.subgroupOf E) = 2 ^ 4

@[expose] noncomputable def Step1619CU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → IsSimpleGroup ↥L → ∀ n : ℕ, IsZ3LThreeTwo A c L n →
    ∀ U : Subgroup G, IsPGroup 2 U → U ≤ Subgroup.centralizer ({c} : Set G) →
      A ≤ Subgroup.normalizer (U : Set G) →
      (∃ E N : Subgroup G, N ≤ E ∧ E ≤ U ∧ ∃ _ : (N.subgroupOf E).Normal,
          IsElementaryAbelian 2 (↥E ⧸ N.subgroupOf E) ∧
            Nat.card (↥E ⧸ N.subgroupOf E) = 2 ^ 4) →
        U ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Proof1619

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_of_prod {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : Multiplicative (ZMod 3) × X ≃* Multiplicative (ZMod 3) × Y)
    (hY : _root_.commutator Y = ⊤) : Nonempty (X ≃* Y) := by
  have hcard : Nat.card X = Nat.card Y := by
    have h := Nat.card_congr e.toEquiv
    rw [Nat.card_prod, Nat.card_prod] at h
    have h3 : Nat.card (Multiplicative (ZMod 3)) ≠ 0 := by simp
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h3) h
  have hec : (_root_.commutator (Multiplicative (ZMod 3) × X)).map e.toMonoidHom =
      _root_.commutator (Multiplicative (ZMod 3) × Y) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective, commutator_def]
  have e3 : _root_.commutator (Multiplicative (ZMod 3) × X) ≃*
      _root_.commutator (Multiplicative (ZMod 3) × Y) :=
    ((_root_.commutator (Multiplicative (ZMod 3) × X)).equivMapOfInjective e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hec)
  obtain ⟨eX⟩ := Sec11.Item1116Proof.nonempty_commutator_prod_equiv X
  obtain ⟨eY⟩ := Sec11.Item1116Proof.nonempty_commutator_prod_equiv Y
  have eXY : _root_.commutator X ≃* _root_.commutator Y := eX.symm.trans (e3.trans eY)
  have hXc : _root_.commutator X = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_congr eXY.toEquiv, hY, Subgroup.card_top, hcard]
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hXc.symm)).trans
    (eXY.trans ((MulEquiv.subgroupCongr hY).trans Subgroup.topEquiv))⟩

theorem simple_of_steps {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (h1612 : Concl1612 A c L)
    (h34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)))
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    IsSimpleGroup ↥L ∧
      ∀ T ∈ invariantPiSubgroups (Subgroup.centralizer (L : Set G)) A (piOf 2), T = ⊥ := by
  rcases h1612 with h1 | he1
  · exact h1
  · exfalso
    obtain ⟨e1⟩ := he1
    obtain ⟨e2⟩ := hprod
    obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_lA.1
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
    have : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hq.1
    have hperf : _root_.commutator (Sec12.lBar c L) = ⊤ :=
      (Group.IsPerfect.ofSurjective (f := η.toMonoidHom) η.surjective).commutator_eq_top
    have hfin : Finite (projSL 3 (GaloisField 2 2)) := by
      have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 2)
      rw [GaloisField.card 2 2 (by norm_num)] at hc
      norm_num at hc
      exact Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨f⟩ := nonempty_mulEquiv_of_prod (e1.symm.trans e2) hperf
    exact h34.false (η.trans f.symm)

noncomputable def conjQuot (K : Subgroup G) {c : G} (hc : c ∈ Subgroup.normalizer (K : Set G)) :
    MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K) (K.normalizerMonoidHom ⟨c, hc⟩)
    (by rw [← MulEquiv.toMonoidHom_eq_coe]; exact CFSG.pCore_map_iso 2 _)

omit [Finite G] in
theorem conjQuot_mk (K : Subgroup G) {c : G} (hc : c ∈ Subgroup.normalizer (K : Set G))
    (k : K) : conjQuot K hc (k : ↥K ⧸ CFSG.pCore 2 ↥K) =
      ((⟨c * k * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc k).mp k.2⟩ : K) :
        ↥K ⧸ CFSG.pCore 2 ↥K) := by
  rw [conjQuot, QuotientGroup.congr_mk]
  rfl

omit [Finite G] in
theorem conjQuot_pow_three (K : Subgroup G) {c : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : c ^ 3 = 1) : conjQuot K hc ^ 3 = 1 := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H k =>
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, conjQuot_mk, conjQuot_mk, conjQuot_mk,
      MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp only
    have hc3' : c * c * c = 1 := by rw [← pow_three', hc3]
    calc c * (c * (c * (k : G) * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * k * (c * c * c)⁻¹ := by
          group
      _ = k := by rw [hc3']; group

omit [Finite G] in
theorem derivedSeries_eq_top_of_isPerfect {X : Type*} [Group X] [Group.IsPerfect X] (m : ℕ) :
    derivedSeries X m = ⊤ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [derivedSeries_succ, ih, ← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem isPerfect_and_two_dvd_of_suzukiModel {H : Type} [Group H]
    {n : ℕ} (hSz : CFSG.Blueprint.SuzukiModel H 2 n) : Group.IsPerfect H ∧ 2 ∣ Nat.card H := by
  refine ⟨?_, ?_⟩
  · obtain ⟨-, a, ha, F, _, _, rfl, hF, ⟨e⟩⟩ := hSz
    have : Group.IsPerfect (CFSG.Blueprint.suzukiGroup a F) :=
      (CFSG.LieType.Ree.suzuki_perfect ha hF).2
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have : Finite H := by
      obtain ⟨-, a, ha, F, _, _, rfl, hF, ⟨e⟩⟩ := hSz
      have : Finite (CFSG.Blueprint.suzukiGroup a F) :=
        KFacts.KP7.finite_of_suzukiModel ⟨rfl, a, ha, F, inferInstance, inferInstance, rfl, hF,
          ⟨MulEquiv.refl _⟩⟩
      exact Finite.of_equiv _ e.symm.toEquiv
    obtain ⟨t, ht, -⟩ := KFacts.KP7.exists_involution_fixed_of_suzukiModel hSz
      (1 : H →* MulAut H) (E := ⊥) (fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow])
    exact ht ▸ orderOf_dvd_natCard t

theorem two_dvd_of_conjQuot_eq_one {K : Subgroup G} {c : G}
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hc : orderOf c = 3) {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ CFSG.pCore 2 ↥K) 2 n)
    (hα : conjQuot K hcK = 1) :
    2 ∣ Nat.card (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 ↥K with hN
  set π := QuotientGroup.mk' N with hπ
  have hfix : ∀ k : K,
      π ⟨c * k * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcK k).mp k.2⟩ = π k := by
    intro k
    have h1 : conjQuot K hcK (k : ↥K ⧸ N) = (1 : MulAut (↥K ⧸ N)) (k : ↥K ⧸ N) := by rw [hα]
    rw [conjQuot_mk, MulAut.one_apply] at h1
    exact h1
  have hpow : ∀ (j : ℕ) (k : K) (hj : c ^ j * k * (c ^ j)⁻¹ ∈ K),
      π ⟨c ^ j * k * (c ^ j)⁻¹, hj⟩ = π k := by
    intro j
    induction j with
    | zero =>
      intro k hj
      congr 1
      apply Subtype.ext
      simp
    | succ j ih =>
      intro k hj
      have hj' : c ^ j * k * (c ^ j)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (pow_mem hcK j) k).mp k.2
      have heq : (⟨c ^ (j + 1) * k * (c ^ (j + 1))⁻¹, hj⟩ : K) =
          ⟨c * (⟨c ^ j * k * (c ^ j)⁻¹, hj'⟩ : K) * c⁻¹,
            (Subgroup.mem_normalizer_iff.mp hcK _).mp hj'⟩ := by
        apply Subtype.ext
        simp only
        rw [pow_succ']
        group
      rw [heq, hfix, ih]
  have hcP : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hzK : Subgroup.zpowers c ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hcK
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have htriv : ∀ (member : Subgroup.zpowers c) (element : K),
      π ⟨member * element * (member : G)⁻¹,
        Subgroup.le_normalizer_iff.mp hzK member member.property element element.property⟩ =
          π element := by
    rintro ⟨y, hy⟩ element
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    exact hpow j element _
  set X := K ⊓ Subgroup.centralizer ({c} : Set G) with hX
  set f : ↥X →* ↥K ⧸ N := π.comp (Subgroup.inclusion inf_le_left) with hf
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N z
    obtain ⟨k', hk'C, hk'⟩ := exists_centralizer_with_same_image_of_trivial_quotient_action
      3 Nat.prime_three (Subgroup.zpowers c) K hcP hzK π hker htriv k
    have hk'c : (k' : G) ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)) hk'C
    refine ⟨⟨k', k'.2, hk'c⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply]
    exact hk'
  obtain ⟨hperf, h2⟩ := isPerfect_and_two_dvd_of_suzukiModel hSz
  obtain ⟨m, hm, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥X)
  have hmap : (perfectResidual ↥X).map f = ⊤ := by
    rw [hm, map_derivedSeries_eq hfsurj m, derivedSeries_eq_top_of_isPerfect]
  have hdvd : Nat.card (↥K ⧸ N) ∣ Nat.card (perfectResidual ↥X) := by
    have := Subgroup.card_map_dvd (H := perfectResidual ↥X) f
    rwa [hmap, Subgroup.card_top] at this
  rw [inSubgroup, Subgroup.card_map_of_injective X.subtype_injective]
  exact h2.trans hdvd

omit [Finite G] in
theorem eq_one_of_mem_of_mem {H : Type*} [Group H] {P Q : Subgroup H} {p q : ℕ}
    (hpq : Nat.Coprime p q) (hP : IsPGroup p P) (hQ : IsPGroup q Q) {x : H} (hxP : x ∈ P)
    (hxQ : x ∈ Q) : x = 1 := by
  obtain ⟨i, hi⟩ := hP ⟨x, hxP⟩
  obtain ⟨j, hj⟩ := hQ ⟨x, hxQ⟩
  have hi' : x ^ p ^ i = 1 := by simpa using congrArg Subtype.val hi
  have hj' : x ^ q ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow i j hpq)
    (orderOf_dvd_of_pow_eq_one hi') (orderOf_dvd_of_pow_eq_one hj')
  exact orderOf_eq_one_iff.mp h1

theorem exists_thirteen_of_conjQuot_ne_one {K : Subgroup G} {c : G}
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hc : orderOf c = 3) (hK3 : ¬ 3 ∣ Nat.card K)
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ CFSG.pCore 2 ↥K) 2 3) (hα : conjQuot K hcK ≠ 1) :
    ∃ X : Subgroup G, X ≤ K ∧ Nat.card X = 13 ∧ c ∈ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, c * x * c⁻¹ = x → x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set N := CFSG.pCore 2 ↥K with hN
  set π := QuotientGroup.mk' N with hπ
  set α := conjQuot K hcK with hαdef
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  have hα3 : orderOf α = 3 := by
    have hdvd : orderOf α ∣ 3 := orderOf_dvd_of_pow_eq_one (conjQuot_pow_three K hcK hc3)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hα
    · exact h3
  obtain ⟨Xb, hXb13, hXbinv, hXbfree⟩ :=
    KFacts.KP7.exists_thirteen_fixedPointFree_of_suzukiModel hSz α hα3
  set Yt : Subgroup G := (Xb.comap π).map K.subtype with hYt
  have hYtK : Yt ≤ K := Subgroup.map_subtype_le _
  have hmemYt : ∀ x ∈ Yt, ∀ hxK : x ∈ K, π ⟨x, hxK⟩ ∈ Xb := by
    rintro x ⟨k, hk, hkx⟩ hxK
    have : (⟨x, hxK⟩ : K) = k := Subtype.ext hkx.symm
    rw [this]
    exact hk
  have hcYt : c ∈ Subgroup.normalizer (Yt : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨k, hk, rfl⟩ := hy
    refine ⟨⟨c * k * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcK k).mp k.2⟩, ?_, rfl⟩
    have h1 := hXbinv (π k) hk
    rw [hαdef, hπ, QuotientGroup.mk'_apply, conjQuot_mk] at h1
    exact h1
  have h13 : 13 ∣ Nat.card Yt := by
    have hsurj : (Xb.comap π).map π = Xb :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Xb
    have h1 := Subgroup.card_map_dvd (H := Xb.comap π) π
    rw [hsurj, hXb13] at h1
    rw [hYt, Subgroup.card_map_of_injective K.subtype_injective]
    exact h1
  have hcop : Nat.Coprime 3 (Nat.card Yt) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
      hK3 (h.trans (Subgroup.card_dvd_of_le hYtK))
  have hcP : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨S, hS, hS1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 13
      Nat.prime_three (by norm_num) (Subgroup.zpowers c) Yt hcP
      (Subgroup.zpowers_le.mpr hcYt) hcop h13
  set X := (S : Subgroup ↥Yt).map Yt.subtype with hX
  have hXYt : X ≤ Yt := Subgroup.map_subtype_le _
  have hXK : X ≤ K := hXYt.trans hYtK
  have hX13p : IsPGroup 13 X := S.isPGroup'.map _
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup (p := 2) (G := ↥K)
  have hXN : ∀ k : K, (k : G) ∈ X → k ∈ N → k = 1 := by
    intro k hkX hkN
    have hXk : IsPGroup 13 (X.subgroupOf K) := hX13p.comap_subtype
    exact eq_one_of_mem_of_mem (by norm_num : Nat.Coprime 13 2) hXk hN2
      (Subgroup.mem_subgroupOf.mpr hkX) hkN
  have hcardX : Nat.card X = 13 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX13p
    let ψ : X → Xb := fun x => ⟨π ⟨x, hXK x.2⟩, hmemYt x (hXYt x.2) (hXK x.2)⟩
    have hψ : Function.Injective ψ := by
      intro x y hxy
      have h1 : π ⟨x, hXK x.2⟩ = π ⟨y, hXK y.2⟩ := congrArg Subtype.val hxy
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have h2 := hXN _ (by simpa using X.mul_mem (X.inv_mem x.2) y.2) h1
      have h3 : (x : G)⁻¹ * y = 1 := by simpa using congrArg Subtype.val h2
      exact Subtype.ext (by rw [← mul_inv_cancel_left (x : G) y, h3, mul_one])
    have hle := Nat.card_le_card_of_injective ψ hψ
    rw [hXb13, hk] at hle
    have hk1 : k ≠ 0 := by
      intro h0
      apply hS1
      rw [← Subgroup.card_eq_one, hX, hk, h0, pow_zero]
    have hk2 : k ≤ 1 := by
      by_contra hk2
      have := Nat.pow_le_pow_right (show 1 ≤ 13 by norm_num) (show 2 ≤ k by omega)
      omega
    rw [hk, show k = 1 by omega, pow_one]
  refine ⟨X, hXK, hcardX, hS (Subgroup.mem_zpowers c), fun x hx hfix => ?_⟩
  have hxK : x ∈ K := hXK hx
  have hαx : α (π ⟨x, hxK⟩) = π ⟨x, hxK⟩ := by
    rw [hαdef, hπ, QuotientGroup.mk'_apply, conjQuot_mk]
    congr 1
    exact Subtype.ext hfix
  have hx1 := hXbfree (π ⟨x, hxK⟩) (hmemYt x (hXYt hx) hxK) hαx
  have hxN : (⟨x, hxK⟩ : K) ∈ N := by
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  have := hXN ⟨x, hxK⟩ hx hxN
  simpa using congrArg Subtype.val this

end CFSG.RankThree.PartTwo.Sec16.Proof1619

