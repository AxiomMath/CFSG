module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofHJList
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item163Proof
import CFSG.RankThree.PartTwo.Sec16.Item163ProofY4
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1515Res

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oRes3_le_of_forall {Y N : Subgroup G}
    (h : ∀ y ∈ Y, ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ N) : oPrimeResidualOf 3 Y ≤ N := by
  rw [oPrimeResidualOf, oPrimeResidual, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro x ⟨k, hk⟩
  exact h x x.2 k (by simpa using congrArg Subtype.val hk)

omit [Finite G] in
theorem mem_oRes3_of_pow {Y : Subgroup G} {y : G} (hy : y ∈ Y) {k : ℕ} (hk : y ^ 3 ^ k = 1) :
    y ∈ oPrimeResidualOf 3 Y :=
  ⟨⟨y, hy⟩, Subgroup.subset_closure ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩

omit [Finite G] in
theorem oRes3_idem (Y : Subgroup G) :
    oPrimeResidualOf 3 (oPrimeResidualOf 3 Y) = oPrimeResidualOf 3 Y :=
  le_antisymm (Subgroup.map_subtype_le _) (oRes3_le_of_forall fun _ hy _ hk =>
    mem_oRes3_of_pow (mem_oRes3_of_pow hy hk) hk)

omit [Finite G] in
theorem le_normalizer_oRes3 {H Y : Subgroup G} (hHY : H ≤ Subgroup.normalizer (Y : Set G)) :
    H ≤ Subgroup.normalizer (oPrimeResidualOf 3 Y : Set G) := by
  have key : ∀ g ∈ H, ∀ y ∈ oPrimeResidualOf 3 Y, g * y * g⁻¹ ∈ oPrimeResidualOf 3 Y := by
    intro g hg
    have hle : oPrimeResidualOf 3 Y ≤
        (oPrimeResidualOf 3 Y).comap (MulAut.conj g).toMonoidHom := by
      refine oRes3_le_of_forall fun y hy k hk => ?_
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine mem_oRes3_of_pow ((Subgroup.mem_normalizer_iff.mp (hHY hg) y).mp hy) (k := k) ?_
      rw [conj_pow, hk, mul_one, mul_inv_cancel]
    intro y hy
    have := hle hy
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨key g hg y, fun hy => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hy
  rwa [inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1

omit [Finite G] in
theorem le_oRes3_sup [Finite G] {Y M O : Subgroup G} (hY3 : Y = oPrimeResidualOf 3 Y)
    (hMY : M ≤ Y) (hOY : O ≤ Y) (hYO : Y ≤ Subgroup.normalizer (O : Set G))
    (hY : Y ≤ M ⊔ O) : Y ≤ oPrimeResidualOf 3 M ⊔ O := by
  have hON : (O.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).mpr hYO
  refine hY3.le.trans (oRes3_le_of_forall fun y hy k hk => ?_)
  have hy' : y ∈ ((M ⊔ O : Subgroup G) : Set G) := hY hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right M O (hMY.trans hYO)] at hy'
  obtain ⟨m, hm, o, ho, rfl⟩ := hy'
  beta_reduce at hy hk ⊢
  obtain ⟨e, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos m).ne' 3 (by norm_num)
  have hmr : (m ^ r) ^ 3 ^ e = 1 := by
    rw [← pow_mul, mul_comm, ← hor, pow_orderOf_eq_one]
  have hmrZ : m ^ r ∈ oPrimeResidualOf 3 M := mem_oRes3_of_pow (pow_mem hm r) hmr
  have hcop : Nat.Coprime r (3 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr3).symm
  by_cases hk0 : k = 0
  · subst hk0
    rw [pow_zero, pow_one] at hk
    rw [hk]
    exact one_mem _
  have hk1 : 1 < 3 ^ k := Nat.one_lt_pow hk0 (by norm_num)
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hk1
  have hmY : m ∈ Y := hMY hm
  have hoY : o ∈ Y := hOY ho
  set yY : ↥Y := ⟨m * o, mul_mem hmY hoY⟩ with hyY
  set mY : ↥Y := ⟨m, hmY⟩ with hmYdef
  have h1 : (yY : ↥Y ⧸ O.subgroupOf Y) = (mY : ↥Y ⧸ O.subgroupOf Y) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((yY⁻¹ * mY : ↥Y) : G) = o⁻¹ := by
      simp only [hyY, hmYdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact inv_mem ho
  have hyk : yY ^ 3 ^ k = 1 := Subtype.ext (by simpa [hyY] using hk)
  have hpow : ∀ x : ↥Y ⧸ O.subgroupOf Y, x ^ 3 ^ k = 1 → x ^ (r * s) = x := by
    intro x hx
    have he : r * s = 3 ^ k * (r * s / 3 ^ k) + 1 := by
      have := Nat.div_add_mod (r * s) (3 ^ k)
      omega
    rw [he, pow_succ, pow_mul, hx, one_pow, one_mul]
  have h2 : (yY : ↥Y ⧸ O.subgroupOf Y) = ((mY ^ (r * s) : ↥Y) : ↥Y ⧸ O.subgroupOf Y) := by
    rw [QuotientGroup.mk_pow, ← h1]
    exact (hpow _ (by rw [← QuotientGroup.mk_pow, hyk, QuotientGroup.mk_one])).symm
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
  have hmrs : ((mY ^ (r * s) : ↥Y) : G) ∈ oPrimeResidualOf 3 M := by
    rw [Subgroup.coe_pow, pow_mul]
    exact pow_mem hmrZ s
  have e2 : m * o = ((mY ^ (r * s) : ↥Y) : G) * (((yY⁻¹ * mY ^ (r * s) : ↥Y) : G))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyY]
    group
  rw [e2]
  exact mul_mem (Subgroup.mem_sup_left hmrs) (Subgroup.mem_sup_right (inv_mem h2))

theorem eq_delta_of_le_cover {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y Z : Subgroup G}
    (hY : Y ∈ scriptY4 A LB) (hZY : Z ≤ Y) (hcov : Y ≤ Z ⊔ CFSG.Open.pCoreOf 2 Y)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hmem : ∀ R : Subgroup G, R ≤ Z → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ∈ scriptQ A LB) :
    Z = delta A LB Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set D := delta A LB Z with hDdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hY.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hmem' : ∀ R : Subgroup G, R ≤ Z → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ≤ D := fun R hRZ hR3 hAR =>
    le_delta (hmem R hRZ hR3 hAR) hRZ
  have hDZ : D ≤ Z := delta_le Z
  have hQ : ∀ Q ∈ collectionIn (scriptQ A LB) Y, Q ≤ D ⊔ O := by
    rintro Q ⟨hQ, hQY⟩
    have hQO : IsPiSubgroup (piCompl 3) (Q ⊔ O) := isPiSubgroup_piCompl_sup hQ.1.2.1
      ((isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3) (hQY.trans hYO)
    have hR : (Q ⊔ O) ⊓ Z ≤ D := hmem' _ inf_le_right
      (fun h3 => (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hQO
        (h3.trans (Subgroup.card_dvd_of_le inf_le_left)))
      ((le_inf (le_normalizer_sup hQ.1.2.2 hAO) hAZ).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
    intro q hq
    have hqY : q ∈ ((Z ⊔ O : Subgroup G) : Set G) := hcov (hQY hq)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Z O (hZY.trans hYO)] at hqY
    obtain ⟨l, hl, o, ho, rfl⟩ := hqY
    have hlR : l ∈ (Q ⊔ O) ⊓ Z := by
      refine Subgroup.mem_inf.mpr ⟨?_, hl⟩
      have hlo : l = (l * o) * o⁻¹ := by group
      rw [hlo]
      exact mul_mem (Subgroup.mem_sup_left hq) (inv_mem (Subgroup.mem_sup_right ho))
    exact mul_mem (Subgroup.mem_sup_left (hR hlR)) (Subgroup.mem_sup_right ho)
  have hYle : Y ≤ D ⊔ O :=
    hY.2.2.1.le.trans (show delta A LB Y ≤ D ⊔ O from sSup_le hQ)
  have hZO : Z ⊓ O ≤ D := hmem' _ inf_le_left
    (fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right)))
    ((le_inf hAZ hAO).trans Subgroup.inf_normalizer_le_normalizer_inf)
  refine le_antisymm (fun l hl => ?_) hDZ
  have hl' : l ∈ ((D ⊔ O : Subgroup G) : Set G) := hYle (hZY hl)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D O (hDZ.trans (hZY.trans hYO))] at hl'
  obtain ⟨d, hd, o, ho, rfl⟩ := hl'
  have hoZ : o ∈ Z := by
    have := mul_mem (inv_mem (hDZ hd)) hl
    rwa [inv_mul_cancel_left] at this
  exact mul_mem hd (hZO ⟨hoZ, ho⟩)

theorem three_dvd_card_of_le_cover {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y Z : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hZY : Z ≤ Y)
    (hcov : Y ≤ Z ⊔ CFSG.Open.pCoreOf 2 Y) : 3 ∣ Nat.card Z := by
  set P := CFSG.pCore 2 ↥Y with hP
  set f : ↥Z →* ↥Y ⧸ P := (QuotientGroup.mk' P).comp (Subgroup.inclusion hZY) with hf
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P q
    have hy : (y : G) ∈ ((Z ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := hcov y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Z _
      (hZY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hy
    obtain ⟨l, hl, o, ho, hlo⟩ := hy
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.mp
      (show o ∈ (CFSG.Open.pCore 2 ↥Y).map Y.subtype from ho)
    have ho'P : o' ∈ P := by rwa [hP]
    have hy' : y = Subgroup.inclusion hZY ⟨l, hl⟩ * o' := Subtype.ext hlo.symm
    have h1 : QuotientGroup.mk' P o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'P
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hy', hf, MonoidHom.comp_apply, map_mul, h1, mul_one]
  have hcard : Nat.card (↥Y ⧸ P) = Nat.card (↥Z ⧸ f.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv).symm
  exact (Proof1515.three_dvd_card_of_mem_scriptY4 hY).trans
    (hcard ▸ Subgroup.card_quotient_dvd_card _)

theorem mem_scriptY4_of_le_cover {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y Z : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hZY : Z ≤ Y)
    (hcov : Y ≤ Z ⊔ CFSG.Open.pCoreOf 2 Y) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hZ3 : Z = oPrimeResidualOf 3 Z)
    (hmem : ∀ R : Subgroup G, R ≤ Z → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ∈ scriptQ A LB) :
    Z ∈ scriptY4 A LB :=
  ⟨⟨fun hZ => hY.1.1 (top_le_iff.mp (hZ ▸ hZY)), hAZ⟩, hZ3,
    eq_delta_of_le_cover hY hZY hcov hAZ hmem,
    Sec16.isQuasisimple_of_cover hY hZY hcov (three_dvd_card_of_le_cover hY hZY hcov)⟩

theorem meetsY4_of_cover {A : Subgroup G} (h142 : Concl142 A (lB A)) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' Y : Subgroup G}
    (hL'c : L' ≤ Subgroup.centralizer ({c'} : Set G))
    (hAL' : A ≤ Subgroup.normalizer (L' : Set G)) (hY : Y ∈ scriptY4 A (lB A))
    (hcov : Y = (Y ⊓ L') ⊔ CFSG.Open.pCoreOf 2 Y) : MeetsY4 A (lB A) L' Y := by
  set M := Y ⊓ L' with hM
  set Z := oPrimeResidualOf 3 M with hZ
  have hZM : Z ≤ M := Subgroup.map_subtype_le _
  have hZY : Z ≤ Y := hZM.trans inf_le_left
  have hcovZ : Y ≤ Z ⊔ CFSG.Open.pCoreOf 2 Y :=
    le_oRes3_sup hY.2.1 inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y) hcov.le
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_oRes3 (Late.le_normalizer_inf hY.1.2 hAL')
  have hmem : ∀ R : Subgroup G, R ≤ Z → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ∈ scriptQ A (lB A) := fun R hRZ hR3 hAR =>
    Sec16.mem_scriptQ_of_concl142 h142 hc'
      ⟨(hRZ.trans (hZM.trans (inf_le_right.trans hL'c))).trans
        (centralizer_singleton_le_normalizer_zpowers c'),
        (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
  exact ⟨Z, mem_scriptY4_of_le_cover hY hZY hcovZ hAZ (oRes3_idem M).symm hmem,
    le_inf (hZM.trans inf_le_right) hZY⟩

end Proof1515Res

open Proof1515 Proof1515Res

theorem step1515HJListCover_of
    (h142 : Item142R) (h134 : Item134) (h48 : Sec4.Item4_8) (h135 : Item135Simple)
    (hHJ : Step1515HJ) : Step1515HJListCover := by
  intro G _ _ A c L h hJ Y hY _ hYJ _ c' hc' hcc hdec
  exfalso
  obtain ⟨φY⟩ := hYJ
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  obtain ⟨L', hL', ⟨φL'⟩⟩ := allPointsHJ_of_j2 h134 h48 h.toSec14Std hJ c' hc'
  have h' : Sec15R G A c' L' := { h with zpowers_mem_omegaA := hc', mem_lA := hL' }
  have hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := KFacts.KS14.card_nativeJ2
  have h3J : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by rw [hJc]; norm_num
  have h3L' : 3 ∣ Nat.card L' := three_dvd_card_of_mulEquiv φL' h3J
  have hL'J : Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 604800 := by
    rw [Nat.card_congr φL'.toEquiv, hJc]
  have hnot34 : IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    refine ⟨fun ψ => ?_⟩
    have h1 := Nat.card_congr ψ.toEquiv
    rw [hL'J, KFacts.KS14.card_projSL_three_four] at h1
    omega
  have hfac := eq_inf_sup_pPrimeCoreOf_of_item142 h' (h142 G A c' L' h') h3L' hnot34 hY4 hdec
  have hs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := isSimpleGroup_of_mulEquiv_J2 φY
  have hO : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    pPrimeCore_three_eq_pCore_two (pPrimeCore_three_eq_bot_of_isSimpleGroup hs
      (by rw [Nat.card_congr φY.toEquiv, hJc]; norm_num))
  rw [pPrimeCoreOf_eq_pCoreOf_two hO] at hfac
  have : Nontrivial CFSG.Blueprint.NativeSporadic.J2 := nontrivial_J2
  have hθ' : aschbacherSolvableCore 3 ↥L' = CFSG.pCore 2 ↥L' :=
    theta_eq_pCore_two_of_multFree (h135 G A c' L' h'.toSec13Data (Or.inr (Or.inr ⟨φL'⟩)))
      ⟨φL'⟩ multFree_J2
  have hθO' : (aschbacherSolvableCore 3 ↥L').map L'.subtype = CFSG.Open.pCoreOf 2 L' := by
    rw [hθ']
    rfl
  have hLY' : L' = (L' ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L' := by
    have hLK := eq_sup_theta_of_cover inf_le_right inf_le_left hfac hs hY4.2.2.2.1
      (by rw [hL'J, Nat.card_congr φY.toEquiv, hJc])
    rw [hθO', inf_comm] at hLK
    exact hLK
  have hmeet : MeetsY4 A (lB A) L' Y :=
    meetsY4_of_cover (concl142_of_j2 h134 h48 h.toSec14Std hJ) hc'
      (le_centralizer_of_mem_thetaComponentsAt hL'.1) hL'.2.1 hY4 hfac
  have hΩ := hHJ G A c' L' h' ⟨φL'⟩ Y hY hmeet hfac hLY'
  have hc : Subgroup.zpowers c ∈ omegaA A := h.zpowers_mem_omegaA
  rw [hΩ, Set.mem_singleton_iff] at hc
  exact hcc hc.symm

end CFSG.RankThree.PartTwo.Sec15
