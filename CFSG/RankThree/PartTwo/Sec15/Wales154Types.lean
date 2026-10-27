module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Stage
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofList
import CFSG.RankThree.PartTwo.Sec14.Ronan148KPoint
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec15.Wales154J2Branch
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofInner
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofA6
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Embed
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.RankThree.PartTwo.Sec15.Wales154Tools
public import CFSG.RankThree.PartTwo.Sec15.Wales154When
public import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem exists_card_imgX_eq {X Y : Subgroup G} (hXY : X ≤ Y) :
    ∃ k : ℕ, Nat.card (imgX X Y) = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := CFSG.Open.pCoreOf 2 Y with hD
  set P := CFSG.Open.pCoreOf 2 X with hP
  have hYD : Y ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hD2 : IsPGroup 2 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hXDP : D ⊓ X ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (Late.le_normalizer_inf (hXY.trans hYD) Subgroup.le_normalizer) (hD2.to_le inf_le_left)
  have h1 := Subgroup.relIndex_mul_card D X
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  have hcP : Nat.card (CFSG.pCore 2 ↥X) = Nat.card P := by
    rw [hP, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  rw [hcP] at h2
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hD2.to_le (inf_le_left : D ⊓ X ≤ D))
  have hdvd : Nat.card (D ⊓ X : Subgroup G) ∣ Nat.card P := Subgroup.card_dvd_of_le hXDP
  rw [hj, hm] at hdvd
  have hjm : j ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  refine ⟨m - j, ?_⟩
  rw [card_imgX hXY]
  have e : D.relIndex X * 2 ^ j = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * 2 ^ m := by
    rw [← hj, h1, h2, hm]
  refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ j) ?_
  rw [e, mul_assoc, ← pow_add, Nat.sub_add_cancel hjm]

theorem not_nine_dvd_card_imgX {X Y : Subgroup G} (hXY : X ≤ Y)
    (h9 : ¬ 9 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X)) : ¬ 9 ∣ Nat.card (imgX X Y) := by
  obtain ⟨k, hk⟩ := exists_card_imgX_eq hXY
  rw [hk]
  intro h
  exact h9 ((Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h)

omit [Finite G] in
theorem actQ_mem_imgX {X Y : Subgroup G} {m : Subgroup.normalizer (Y : Set G)}
    (hmX : (m : G) ∈ Subgroup.normalizer (X : Set G)) {k : ↥Y ⧸ CFSG.pCore 2 ↥Y}
    (hk : k ∈ imgX X Y) : Sec17.Proof17Res6.actQ Y m k ∈ imgX X Y := by
  obtain ⟨y, hy, rfl⟩ := hk
  rw [Sec17.Proof17Res6.actQ_mk]
  refine ⟨Y.normalizerMonoidHom m y, ?_, rfl⟩
  show Y.normalizerMonoidHom m y ∈ X.subgroupOf Y
  rw [Subgroup.mem_subgroupOf]
  have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
  show (m : G) * y * (m : G)⁻¹ ∈ X
  exact (Subgroup.mem_normalizer_iff.mp hmX y).mp hyX

@[expose] noncomputable def abar (A Y : Subgroup G) : Subgroup (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
  (A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (Sec17.Proof17Res6.actQ Y)

omit [Finite G] in
theorem abar_mem_imgX {A X Y : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ∀ e ∈ abar A Y, ∀ k ∈ imgX X Y, e k ∈ imgX X Y := by
  rintro _ ⟨m, hm, rfl⟩ k hk
  exact actQ_mem_imgX (hAX (Subgroup.mem_subgroupOf.mp hm)) hk

omit [Finite G] in
theorem abar_le_normalizer_barR {A Y R : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    abar A Y ≤ Subgroup.normalizer (barR Y R : Set _) := by
  rintro _ ⟨m, hm, rfl⟩
  exact actQ_mem_normalizer_barR m.2 (hAR (Subgroup.mem_subgroupOf.mp hm))

theorem isPGroup_abar {A Y : Subgroup G} (hA : IsPGroup 3 A) : IsPGroup 3 (abar A Y) := by
  have h : IsPGroup 3 (A.subgroupOf (Subgroup.normalizer (Y : Set G))) := by
    intro g
    obtain ⟨k, hk⟩ :=
      hA ⟨((g : Subgroup.normalizer (Y : Set G)) : G), Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  exact h.map _

theorem card_spec_of_isLThreeEpsAt {Q : Type} [Group Q] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : IsLThreeEpsAt Q p f) : ∃ q, 2 ≤ q ∧
      (Nat.card Q * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∨
        (2 < q ∧ Nat.card Q * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))) := by
  have hp : p.Prime := Fact.out
  have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  rcases h with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · refine ⟨p ^ f, hq2, Or.inl ?_⟩
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p f)
    rw [GaloisField.card p f (by omega)] at hc
    rw [Nat.card_congr φ.toEquiv]
    exact hc
  · refine ⟨p ^ f, hq2, Or.inr ⟨hq, ?_⟩⟩
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_projSU_three_mul_gcd p f hf

theorem prop_of_isLThreeEpsAt {Q : Type} [Group Q] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : IsLThreeEpsAt Q p f) {N B : ℕ} (hN : 0 < N) (hB : 3 * N < B ^ 3) {P : ℕ → Prop}
    (hdvd : Nat.card Q ∣ N)
    (hSL : ∀ q < B, 2 ≤ q →
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) ∣ N →
        P (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)))
    (hSU : ∀ q < B, 2 < q →
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) ∣ N →
        P (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1))) :
    P (Nat.card Q) := by
  obtain ⟨q, hq2, hSL' | ⟨hq, hSU'⟩⟩ := card_spec_of_isLThreeEpsAt hf h
  · have hg : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hg3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hM : Nat.card Q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) :=
      (Nat.div_eq_of_eq_mul_left hg hSL'.symm).symm
    have hQle : Nat.card Q ≤ N := Nat.le_of_dvd hN hdvd
    have hqB : q < B := by
      by_contra hqB
      push Not at hqB
      have h1 : B ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hqB 3
      have h2 : q ^ 3 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
        have : 1 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := by
          have a : 1 ≤ q ^ 2 - 1 := by
            have : 4 ≤ q ^ 2 := by nlinarith
            omega
          have b : 1 ≤ q ^ 3 - 1 := by
            have : 8 ≤ q ^ 3 := by
              calc 8 = 2 ^ 3 := by norm_num
                _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
            omega
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        exact Nat.le_mul_of_pos_right _ this
      have h3 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 3 * N := by
        rw [← hSL']
        calc Nat.card Q * Nat.gcd 3 (q - 1) ≤ N * 3 := Nat.mul_le_mul hQle hg3
          _ = 3 * N := by ring
      omega
    rw [hM] at hdvd ⊢
    exact hSL q hqB hq2 hdvd
  · have hg : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hg3 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hM : Nat.card Q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) :=
      (Nat.div_eq_of_eq_mul_left hg hSU'.symm).symm
    have hQle : Nat.card Q ≤ N := Nat.le_of_dvd hN hdvd
    have hqB : q < B := by
      by_contra hqB
      push Not at hqB
      have h1 : B ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hqB 3
      have h2 : q ^ 3 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
        have : 1 ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := by
          have a : 1 ≤ q ^ 2 - 1 := by
            have : 4 ≤ q ^ 2 := by nlinarith
            omega
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        exact Nat.le_mul_of_pos_right _ this
      have h3 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ≤ 3 * N := by
        rw [← hSU']
        calc Nat.card Q * Nat.gcd 3 (q + 1) ≤ N * 3 := Nat.mul_le_mul hQle hg3
          _ = 3 * N := by ring
      omega
    rw [hM] at hdvd ⊢
    exact hSU q hqB hq hdvd

theorem factorization_two_pow_mul_27 (m : ℕ) : (2 ^ m * 27).factorization 3 = 3 := by
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), smul_zero, zero_add,
    show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same]

theorem eq_one_of_trivial_of_E27_of {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {J U : Subgroup G} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hJU : J ≤ Subgroup.normalizer (U : Set G))
    (hZ : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥) {b : G} (hbA : b ∈ A)
    (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (hbtriv : ∀ y ∈ J, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 J)
    {E : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) : b = 1 := by
  classical
  by_contra hb1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.toSec13Data.partTwoS_eq).1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hAe.2 b hbA) hb1
  set B := Subgroup.zpowers b with hB
  have hB3 : IsPGroup 3 B := h.isE27.isPGroup.to_le (Subgroup.zpowers_le.mpr hbA)
  set P := CFSG.pCore 2 ↥J with hP
  set π := QuotientGroup.mk' P with hπ
  set O := CFSG.Open.pCoreOf 2 J with hOdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J
  have hJO : J ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hBtriv : ∀ x ∈ B, ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ O := by
    have hS : B ≤ centralizerSection J O := Subgroup.zpowers_le.mpr
      (mem_centralizerSection_of_trivial hbJ hbtriv)
    exact fun x hx => trivial_of_mem_centralizerSection (hS hx)
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := Subgroup.zpowers_le.mpr hbJ
  set Ê : Subgroup G := (E.comap π).map J.subtype with hÊ
  have hÊJ : Ê ≤ J := Subgroup.map_subtype_le _
  have hπconj : ∀ x ∈ B, ∀ y : ↥J, ∀ hxy : x * (y : G) * x⁻¹ ∈ J,
      π ⟨x * (y : G) * x⁻¹, hxy⟩ = π y := by
    intro x hx y hxy
    have h1 : ((⟨x * (y : G) * x⁻¹, hxy⟩ * y⁻¹ : ↥J) : G) ∈ O := by
      simpa using hBtriv x hx y y.2
    have h2 := (Proof156Res4.mem_pCoreOf_iff_mk_eq_one _).mp h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h2
    exact h2
  have hBÊ : B ≤ Subgroup.normalizer (Ê : Set G) := by
    intro x hx
    have hx3 : x ^ 3 = 1 := hAe.2 x ((Subgroup.zpowers_le.mpr hbA) hx)
    refine Proof156Res4.mem_normalizer_of_conj_le hx3 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hxy : x * (y : G) * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hBJ hx) y).mp y.2
    refine ⟨⟨_, hxy⟩, ?_, rfl⟩
    show π ⟨_, hxy⟩ ∈ E
    rw [hπconj x hx y hxy]
    exact hy
  obtain ⟨F₀, hF₀, hF₀N⟩ := Proof156Res4.exists_invariant_sylowOf' hBÊ hB3
  have hF₀Ê : F₀ ≤ Ê := hF₀.le
  have hÊcard : Nat.card Ê = Nat.card P * 27 := by
    rw [hÊ, Subgroup.card_map_of_injective J.subtype_injective]
    have h1 := QuotientGroup.card_preimage_mk P (E : Set (↥J ⧸ P))
    rw [SetLike.coe_sort_coe, hE27] at h1
    exact h1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 P)
  have hF₀27 : Nat.card F₀ = 27 := by
    rw [hF₀.card_eq, hÊcard, hm, factorization_two_pow_mul_27]
    norm_num
  have hdisj : F₀ ⊓ O = ⊥ := by
    have hd : Disjoint F₀ O := Subgroup.disjoint_of_coprime_natCard (by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
      rw [hF₀27, hn]
      exact Nat.Coprime.pow_right _ (by norm_num))
    exact hd.eq_bot
  have hmemO : ∀ x ∈ F₀, x ∈ O → x = 1 := fun x hx hxO => by
    have : x ∈ F₀ ⊓ O := ⟨hx, hxO⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  have hbC : ∀ f ∈ F₀, f * b = b * f := by
    intro f hf
    have hbB : b ∈ B := Subgroup.mem_zpowers b
    have h1 : b * f * b⁻¹ ∈ F₀ := (Subgroup.mem_normalizer_iff.mp (hF₀N hbB) f).mp hf
    have h2 : b * f * b⁻¹ * f⁻¹ ∈ O := hBtriv b hbB f (hÊJ (hF₀Ê hf))
    have h3 : b * f * b⁻¹ * f⁻¹ = 1 := hmemO _ (mul_mem h1 (inv_mem hf)) h2
    calc f * b = b * f * b⁻¹ * f⁻¹ * (f * b) := by rw [h3, one_mul]
      _ = b * f := by group
  have hπE : ∀ e ∈ Ê, ∃ y : ↥J, (y : G) = e ∧ π y ∈ E := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, rfl, hy⟩
  have hF₀c : ∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl, hx'⟩ := hπE x (hF₀Ê hx)
    obtain ⟨y', rfl, hy'⟩ := hπE y (hF₀Ê hy)
    have hO' : ((x' * y' * x'⁻¹ * y'⁻¹ : ↥J) : G) ∈ O := by
      rw [Proof156Res4.mem_pCoreOf_iff_mk_eq_one, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      have hc : (x' : ↥J ⧸ P) * (y' : ↥J ⧸ P) = (y' : ↥J ⧸ P) * (x' : ↥J ⧸ P) :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
      rw [hc, mul_inv_cancel_right, mul_inv_cancel]
    have h1 := hmemO _ (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inv]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) hO'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv] at h1
    calc (x' : G) * y' = (x' : G) * y' * (x' : G)⁻¹ * (y' : G)⁻¹ * (y' * x') := by group
      _ = y' * x' := by rw [h1, one_mul]
  have hF₀e : ∀ x ∈ F₀, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨x', rfl, hx'⟩ := hπE x (hF₀Ê hx)
    refine hmemO _ (pow_mem hx 3) ?_
    rw [← Subgroup.coe_pow, Proof156Res4.mem_pCoreOf_iff_mk_eq_one, QuotientGroup.mk_pow]
    exact hE.2 _ hx'
  have hF₀comm : IsMulCommutative F₀ := ⟨⟨fun x y => Subtype.ext (hF₀c x x.2 y y.2)⟩⟩
  have hDab : CFSG.Assembly.IsElemAbelian 3 F₀ := ⟨hF₀comm, hF₀e⟩
  have hbF : b ∉ F₀ := by
    intro hbF
    have hbJ' : b ∈ J := hÊJ (hF₀Ê hbF)
    set bJ : ↥J := ⟨b, hbJ'⟩ with hbJdef
    have hZb : QuotientGroup.mk' P bJ ∈ Subgroup.center (↥J ⧸ P) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P z
      have h1 : ((bJ * y * bJ⁻¹ * y⁻¹ : ↥J) : G) ∈ O := by
        simpa [hbJdef] using hbtriv y y.2
      have h2 := (Proof156Res4.mem_pCoreOf_iff_mk_eq_one _).mp h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h2
      show (y : ↥J ⧸ P) * (bJ : ↥J ⧸ P) = (bJ : ↥J ⧸ P) * (y : ↥J ⧸ P)
      calc (y : ↥J ⧸ P) * (bJ : ↥J ⧸ P) =
          (bJ : ↥J ⧸ P) * (y : ↥J ⧸ P) * (bJ : ↥J ⧸ P)⁻¹ * (y : ↥J ⧸ P)⁻¹ *
            ((y : ↥J ⧸ P) * (bJ : ↥J ⧸ P)) := by
            rw [h2, one_mul]
        _ = (bJ : ↥J ⧸ P) * (y : ↥J ⧸ P) := by group
    rw [hZ, Subgroup.mem_bot] at hZb
    have hbO : b ∈ O := (Proof156Res4.mem_pCoreOf_iff_mk_eq_one bJ).mpr hZb
    exact hb1 (hmemO b hbF hbO)
  have hbD : b ∈ Subgroup.centralizer (F₀ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun f hf => hbC f hf
  have hDU : F₀ ≤ Subgroup.normalizer (U : Set G) := (hF₀Ê.trans hÊJ).trans hJU
  exact Sec12.false_of_le_E81 hFE hDab hF₀27 hU hU2 hDU hbD hb3 hbF

theorem eq_one_of_trivial_of_E27 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {J : Subgroup G} (hO : CFSG.Open.pCoreOf 2 J ≠ ⊥)
    (hZ : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥) {b : G} (hbA : b ∈ A)
    (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (hbtriv : ∀ y ∈ J, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 J)
    {E : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) : b = 1 :=
  eq_one_of_trivial_of_E27_of h hO (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J) hZ hbA hbJ hbtriv hE hE27

theorem card_abar_of_E27 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {J : Subgroup G} (hO : CFSG.Open.pCoreOf 2 J ≠ ⊥)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hZ : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥)
    {E : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) : Nat.card (abar A J) = 27 := by
  set N := Subgroup.normalizer (J : Set G) with hNdef
  set A' := A.subgroupOf N with hA'
  set f := Sec17.Proof17Res6.actQ J with hf
  have hA'27 : Nat.card A' = 27 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv, h.isE27.2]
  have h27 : f.ker.relIndex A' * Nat.card (f.ker ⊓ A' : Subgroup N) = 27 :=
    (Subgroup.relIndex_mul_card f.ker A').trans hA'27
  rw [Subgroup.relIndex_ker] at h27
  have hbot : f.ker ⊓ A' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2
    have hx1 : f x = 1 := (Subgroup.mem_inf.mp hx).1
    have htriv := Proof155w3.commutator_mem_of_actQ_eq_one (J := J) (m := x) hx1
    have := eq_one_of_trivial_of_E27 h hO hZ hxA x.2 htriv hE hE27
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  rw [hbot, Subgroup.card_bot, mul_one] at h27
  exact h27

theorem eTwentySevenF_inj : ∀ i j k i' j' k' : Fin 3,
    KFacts.KP2.eTwentySevenF i j k = KFacts.KP2.eTwentySevenF i' j' k' →
      i = i' ∧ j = j' ∧ k = k' := by
  decide +kernel

theorem card_eTwentySeven : Nat.card KFacts.KP2.eTwentySeven = 27 := by
  have hb : Function.Bijective (fun t : Fin 3 × Fin 3 × Fin 3 =>
      (⟨KFacts.KP2.eTwentySevenF t.1 t.2.1 t.2.2, t.1, t.2.1, t.2.2, rfl⟩ :
        KFacts.KP2.eTwentySeven)) := by
    refine ⟨fun t t' h => ?_, fun ⟨x, i, j, k, hx⟩ => ⟨(i, j, k), Subtype.ext hx.symm⟩⟩
    obtain ⟨h1, h2, h3⟩ := eTwentySevenF_inj _ _ _ _ _ _ (congrArg Subtype.val h)
    exact Prod.ext h1 (Prod.ext h2 h3)
  rw [← Nat.card_congr (Equiv.ofBijective _ hb)]
  simp

theorem exists_E27_of_A10 {Q : Type*} [Group Q] (φ : Q ≃* alternatingGroup (Fin 10)) :
    ∃ E : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  set E₀ := KFacts.KP2.eTwentySeven.subgroupOf (alternatingGroup (Fin 10)) with hE₀
  refine ⟨E₀.map φ.symm.toMonoidHom,
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf
      Sec16.Step163Alt.isElemAbelian_eTwentySeven _) _, ?_⟩
  rw [Subgroup.card_map_of_injective φ.symm.injective, hE₀,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      KFacts.KP2.eTwentySeven_le_alternatingGroup).toEquiv, card_eTwentySeven]

section Types


theorem type154_hj (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) {A : Subgroup G}
    {c : G} {L : Subgroup G} (hR : Sec15R G A c L) (hHJ : AllPointsHJ A) {Z : Subgroup G}
    (hZ : Z ∈ scriptY4 A (lB A)) :
    Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Sec4.IsTripleCover (↥Z ⧸ CFSG.pCore 2 ↥Z) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥Z ⧸ CFSG.pCore 2 ↥Z) CFSG.Blueprint.NativeSporadic.ON ∨
      Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) := by
  have hq : CFSG.IsQuasisimple (↥Z ⧸ CFSG.pCore 2 ↥Z) := hZ.2.2.2
  have hperf : Group.IsPerfect (↥Z ⧸ CFSG.pCore 2 ↥Z) := hq.1
  have hnt : Nontrivial (↥Z ⧸ CFSG.pCore 2 ↥Z) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hZ
  have key : ∀ {S : Type} [Group S], Proof1515.MultFree S →
      Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* S) → Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* S) :=
    fun hm hS => Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hZ hS hm
  rcases read154_hj h148 h134 h48 hR hHJ hZ with ⟨-, -, -, hJ⟩ | h6 | ⟨⟨φ⟩⟩ | hON | ⟨⟨φ⟩⟩ |
      ⟨hp7, ⟨φ⟩⟩
  · exact Or.inl (key Proof1515.multFree_J2 hJ)
  · have hc : Nat.card (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) = 1080 := by
      rw [card_of_isTripleCover h6, card_alternatingGroup_six]
    have heq : CFSG.pPrimeCore 3 ↥Z = CFSG.pCore 2 ↥Z :=
      Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hq hne fun p hp hp6 => by
        rw [hc]
        exact Proof1515.not_sq_dvd_small (Or.inr rfl) hp hp6
    exact Or.inr (Or.inl
      (Proof1515.isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) h6))
  · have hc : Nat.card (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) = 60 := by
      rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
    have heq : CFSG.pPrimeCore 3 ↥Z = CFSG.pCore 2 ↥Z :=
      Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hq hne fun p hp hp6 => by
        rw [hc]
        exact Proof1515.not_sq_dvd_small (Or.inl rfl) hp hp6
    exact Or.inr (Or.inr (Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans φ⟩))
  · have heq : CFSG.pPrimeCore 3 ↥Z = CFSG.pCore 2 ↥Z :=
      Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun W _ hWc hcop ⟨ψ⟩ =>
        ks1515ONMult _ W hperf hWc hcop (Proof1515.isTripleCover_congr ψ.symm hON)
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (Proof1515.isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) hON))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key Proof1515.multFree_alternatingGroup_seven ⟨φ⟩)))))
  · have heq : CFSG.pPrimeCore 3 ↥Z = CFSG.pCore 2 ↥Z :=
      Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun W _ hWc hcop ⟨ψ⟩ =>
        Proof1511Steps.eq_bot_of_isLThreeEpsAt _ W hperf hWc hcop le_rfl
          (IsLThreeEpsAt.of_mulEquiv ψ.symm (Or.inl ⟨φ⟩))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hp7, ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans φ⟩⟩))))

theorem type154_nhj (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) {A : Subgroup G}
    {c : G} {L : Subgroup G} (hR : Sec15R G A c L) (hNHJ : ¬ AllPointsHJ A) {Z : Subgroup G}
    (hZ : Z ∈ scriptY4 A (lB A)) :
    (∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧ IsLThreeEpsAt (↥Z ⧸ CFSG.pCore 2 ↥Z) p f) ∨
      Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* alternatingGroup (Fin 10)) := by
  have hq : CFSG.IsQuasisimple (↥Z ⧸ CFSG.pCore 2 ↥Z) := hZ.2.2.2
  have hperf : Group.IsPerfect (↥Z ⧸ CFSG.pCore 2 ↥Z) := hq.1
  have hnt : Nontrivial (↥Z ⧸ CFSG.pCore 2 ↥Z) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hZ
  have key : ∀ {S : Type} [Group S], Proof1515.MultFree S →
      Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* S) → Nonempty (↥Z ⧸ CFSG.pCore 2 ↥Z ≃* S) :=
    fun hm hS => Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hZ hS hm
  have hL3eps : ∀ {p f : ℕ} [Fact p.Prime], 1 ≤ f → p ≠ 3 →
      IsLThreeEpsAt (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) p f →
        ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧
          IsLThreeEpsAt (↥Z ⧸ CFSG.pCore 2 ↥Z) p f := by
    intro p f hp hf hp3 hε
    have heq : CFSG.pPrimeCore 3 ↥Z = CFSG.pCore 2 ↥Z :=
      Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun W _ hWc hcop ⟨φ⟩ =>
        Proof1511Steps.eq_bot_of_isLThreeEpsAt _ W hperf hWc hcop hf
          (IsLThreeEpsAt.of_mulEquiv φ.symm hε)
    exact ⟨p, f, hp, hf, hp3,
      IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heq) hε⟩
  have hL3pi : ∀ {p e : ℕ} [Fact p.Prime], 1 ≤ e →
      Sec4.IsoLThreePi (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) p e →
        ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧
          IsLThreeEpsAt (↥Z ⧸ CFSG.pCore 2 ↥Z) p f := by
    intro p e hp he hiso
    obtain ⟨φ⟩ := key (Proof1515.multFree_of_isLThreePi ⟨p, e, hp, he, hiso⟩)
      (⟨MulEquiv.refl _⟩ : Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* ↥Z ⧸ CFSG.pPrimeCore 3 ↥Z))
    exact ⟨p, e, hp, he, Sec14.Ronan148K.ne_three_of_isoLThreePi he hiso,
      Sec14.isLThreeEpsAt_of_isoLThreePi148 (Proof1515.isoLThreePi_congr φ.symm hiso)⟩
  rcases read154_nhj h148 h134 h48 hR hNHJ hZ with
    ⟨c', hc', -, L', hL', ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e₀, hp, hf, he₀, hiso, hε⟩⟩ | hA10 |
      ⟨-, -, n, m, -, -, hn, -, hiso, -⟩
  · rcases (hR.chosen136.2 c' hc' L' hL').1 with ⟨⟨φJ⟩⟩ | ⟨p, e₀, hp, he, hiso⟩ | ⟨⟨φ7⟩⟩ |
        ⟨⟨φM⟩⟩ | ⟨⟨φM⟩⟩
    · exact (hNHJ (allPointsHJ_of_point h134 h48 hR.toSec14Std hc' hL' ⟨φJ⟩)).elim
    · exact Or.inl (hL3pi he (Proof1515.isoLThreePi_congr φ.symm hiso))
    · exact Or.inr (Or.inl (key Proof1515.multFree_alternatingGroup_seven ⟨φ.trans φ7⟩))
    · exact Or.inr (Or.inr (Or.inl (key Proof1515.multFree_M22 ⟨φ.trans φM⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (key Proof1515.multFree_M12 ⟨φ.trans φM⟩))))
  · exact Or.inr (Or.inl (key Proof1515.multFree_alternatingGroup_seven ⟨φ⟩))
  · have hf' : 1 ≤ f * e₀ := Nat.mul_pos hf he₀
    exact Or.inl (hL3eps hf (Sec14.Ronan148K.ne_three_of_isoLThreePi hf' hiso) hε)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (key Proof1515.multFree_alternatingGroup_ten hA10))))
  · exact Or.inl (hL3pi (p := 2) (by omega) hiso)

theorem card_of_type154_hj (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L) (hHJ : AllPointsHJ A)
    {Z : Subgroup G} (hZ : Z ∈ scriptY4 A (lB A)) :
    Nat.card (↥Z ⧸ CFSG.pCore 2 ↥Z) ∈
      ({604800, 1080, 60, 1382446517760, 2520, 1876896} : Finset ℕ) := by
  rcases type154_hj h148 h134 h48 hR hHJ hZ with ⟨⟨φ⟩⟩ | h6 | ⟨⟨φ⟩⟩ | hON | ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
    decide
  · rw [card_of_isTripleCover h6, card_alternatingGroup_six]
    decide
  · rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
    decide
  · rw [card_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON]
    decide
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    decide
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
    rw [GaloisField.card 7 1 (by norm_num)] at hc
    have h7 : Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) = 1876896 := by
      norm_num at hc
      omega
    rw [Nat.card_congr φ.toEquiv, h7]
    decide

end Types

theorem item154ProperWhen_five :
    Item154ProperWhen fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 5)) := by
  intro G _ _ A c L hR Y hY X hX hXY hYX ⟨φ⟩ R hRm
  exfalso
  have hle := two_mul_card_quot_le hXY hYX
  rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five] at hle
  have hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) := hX.2.2.2
  have : Group.IsPerfect (↥X ⧸ CFSG.pCore 2 ↥X) := hq.1
  have : Nontrivial (↥X ⧸ CFSG.pCore 2 ↥X) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable _
    (CFSG.GroupTheory.groups_order_below_sixty_solvable (G := ↥X ⧸ CFSG.pCore 2 ↥X)
      (by omega))

section Branches


theorem item154ProperWhen_M12 (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) :
    Item154ProperWhen fun Q _ => Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  intro G _ _ A c L hR Y hY X hX hXY hYX ⟨φ⟩ R hRm
  exfalso
  have hN : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 95040 := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
  have hdvd := card_quot_dvd hXY
  have hle := two_mul_card_quot_le hXY hYX
  rw [hN] at hdvd hle
  by_cases hHJ : AllPointsHJ A
  · have h := card_of_type154_hj h148 h134 h48 hR hHJ hY.1
    rw [hN] at h
    revert h
    decide
  · rcases type154_nhj h148 h134 h48 hR hHJ hX with ⟨p, f, hp, hf, -, hε⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ |
        ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
    · exact prop_of_isLThreeEpsAt hf hε (N := 95040) (B := 66)
        (P := fun M => ¬ 2 * M ≤ 95040) (by norm_num) (by norm_num) hdvd
        (by decide +kernel) (by decide +kernel) hle
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at hdvd
      norm_num at hdvd
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM22] at hle
      norm_num at hle
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM12] at hle
      norm_num at hle
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at hle
      norm_num at hle

theorem item154ProperWhen_A7 (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hK1 : KS154A7E9) (hK2 : KS154A7Seven) :
    Item154ProperWhen fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 7)) := by
  intro G _ _ A c L hR Y hY X hX hXY hYX ⟨φ⟩ R hRm
  have hN : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  have hdvd := card_quot_dvd hXY
  have hle := two_mul_card_quot_le hXY hYX
  rw [hN] at hdvd hle
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := (le_sup_right : X ≤ A ⊔ X).trans hRm.2.2
  by_cases hHJ : AllPointsHJ A
  · exfalso
    have h60 : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 60 := by
      rcases type154_hj h148 h134 h48 hR hHJ hX with ⟨⟨ψ⟩⟩ | h6 | ⟨⟨ψ⟩⟩ | hON | ⟨⟨ψ⟩⟩ |
          ⟨hp7, ⟨ψ⟩⟩
      · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeJ2] at hle
        norm_num at hle
      · rw [card_of_isTripleCover h6, card_alternatingGroup_six] at hdvd
        norm_num at hdvd
      · rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_five]
      · rw [card_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON] at hle
        norm_num at hle
      · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at hle
        norm_num at hle
      · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
        rw [GaloisField.card 7 1 (by norm_num), ← Nat.card_congr ψ.toEquiv] at hc
        norm_num at hc
        omega
    have h5 : 5 ∣ Nat.card (imgX X Y) :=
      (show 5 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) by rw [h60]; norm_num).trans
        (card_quot_dvd_card_imgX hXY)
    have h9 : ¬ 9 ∣ Nat.card (imgX X Y) := not_nine_dvd_card_imgX hXY (by rw [h60]; norm_num)
    have hZ := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
      (by norm_num) φ
    obtain ⟨E, hE, hE9⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_nine φ
    have h9A : 9 ≤ Nat.card (abar A Y) :=
      Proof155w3.nine_le_card_map_actQ hR.toSec14Std hY.2.2 hY.1.1.2 hZ hE hE9
    exact hK1 _ ⟨φ⟩ (imgX X Y) h5 h9 (abar A Y) (isPGroup_abar hR.toSec14Std.isE27.isPGroup) h9A
      (abar_mem_imgX hX.1.2)
  · have h7 : 7 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
      rcases type154_nhj h148 h134 h48 hR hHJ hX with ⟨p, f, hp, hf, -, hε⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ |
          ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
      · exact prop_of_isLThreeEpsAt hf hε (N := 2520) (B := 20)
          (P := fun M => 2 * M ≤ 2520 → 7 ∣ M) (by norm_num) (by norm_num) hdvd
          (by decide +kernel) (by decide +kernel) hle
      · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at hle
        norm_num at hle
      · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM22] at hle
        norm_num at hle
      · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM12] at hle
        norm_num at hle
      · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at hle
        norm_num at hle
    have hbot := hK2 _ ⟨φ⟩ (imgX X Y) (h7.trans (card_quot_dvd_card_imgX hXY)) (barR Y R)
      (isPGroup_barR hRm.1 hR2) (conj_mem_normalizer_barR hXY hXR)
    exact Or.inl (commutator_le_pCoreOf_of_barR_eq_bot hRm.1 hbot)

theorem item154ProperWhen_A10 (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hK : KS154A10Aut) :
    Item154ProperWhen fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 10)) := by
  intro G _ _ A c L hR Y hY X hX hXY hYX ⟨φ⟩ R hRm
  have hN : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 1814400 := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2]
  have hdvd := card_quot_dvd hXY
  have hle := two_mul_card_quot_le hXY hYX
  rw [hN] at hdvd hle
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := (le_sup_left : A ≤ A ⊔ X).trans hRm.2.2
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := (le_sup_right : X ≤ A ⊔ X).trans hRm.2.2
  have hHJ : ¬ AllPointsHJ A := fun hHJ => by
    have h := card_of_type154_hj h148 h134 h48 hR hHJ hY.1
    rw [hN] at h
    revert h
    decide
  have h7 : 7 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rcases type154_nhj h148 h134 h48 hR hHJ hX with ⟨p, f, hp, hf, -, hε⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ |
        ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
    · exact prop_of_isLThreeEpsAt hf hε (N := 1814400) (B := 176)
        (P := fun M => 2 * M ≤ 1814400 → 7 ∣ M) (by norm_num) (by norm_num) hdvd
        (by decide +kernel) (by decide +kernel) hle
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
      norm_num
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM22] at hdvd
      norm_num at hdvd
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM12] at hdvd
      norm_num at hdvd
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at hle
      norm_num at hle
  have hZ := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
    (by norm_num) φ
  obtain ⟨E, hE, hE27⟩ := exists_E27_of_A10 φ
  have h27 := card_abar_of_E27 hR.toSec14Std hY.2.2 hY.1.1.2 hZ hE hE27
  have hbot := hK _ ⟨φ⟩ (imgX X Y) (h7.trans (card_quot_dvd_card_imgX hXY)) (abar A Y)
    (isPGroup_abar hR.toSec14Std.isE27.isPGroup) h27.ge (abar_mem_imgX hX.1.2) (barR Y R)
    (isPGroup_barR hRm.1 hR2) (conj_mem_normalizer_barR hXY hXR) (abar_le_normalizer_barR hAR)
  exact Or.inl (commutator_le_pCoreOf_of_barR_eq_bot hRm.1 hbot)

end Branches

end CFSG.RankThree.PartTwo.Sec15.Wales154
