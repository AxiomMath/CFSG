module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofM22S
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofInner
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofA6
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Proof155w3

theorem factorization_two_pow_mul_nine (m : ℕ) : (2 ^ m * 9).factorization 3 = 2 := by
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), smul_zero, zero_add,
    show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same]

theorem false_of_le_E9_of_trivial {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {J : Subgroup G} (hO : CFSG.Open.pCoreOf 2 J ≠ ⊥)
    {B : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hBtriv : ∀ b ∈ B, ∀ y ∈ J, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 J)
    (hBJ1 : B ⊓ J = ⊥)
    {E : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.toSec13Data.partTwoS_eq).1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  set P := CFSG.pCore 2 ↥J with hP
  set π := QuotientGroup.mk' P with hπ
  set O := CFSG.Open.pCoreOf 2 J with hOdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J
  have hJO : J ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hNO : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J
  set Ê : Subgroup G := (E.comap π).map J.subtype with hÊ
  have hÊJ : Ê ≤ J := Subgroup.map_subtype_le _
  have hπconj : ∀ b ∈ B, ∀ y : ↥J, ∀ hby : b * (y : G) * b⁻¹ ∈ J,
      π ⟨b * (y : G) * b⁻¹, hby⟩ = π y := by
    intro b hb y hby
    have h1 : ((⟨b * (y : G) * b⁻¹, hby⟩ * y⁻¹ : ↥J) : G) ∈ O := by
      simpa using hBtriv b hb y y.2
    have h2 := (Proof156Res4.mem_pCoreOf_iff_mk_eq_one _).mp h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h2
    exact h2
  have hBÊ : B ≤ Subgroup.normalizer (Ê : Set G) := by
    intro b hb
    refine Proof156Res4.mem_normalizer_of_conj_le (hAe.2 b (hBA hb)) ?_
    rintro _ ⟨y, hy, rfl⟩
    have hby : b * (y : G) * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hBJ hb) y).mp y.2
    refine ⟨⟨_, hby⟩, ?_, rfl⟩
    show π ⟨_, hby⟩ ∈ E
    rw [hπconj b hb y hby]
    exact hy
  obtain ⟨F₀, hF₀, hF₀N⟩ := Proof156Res4.exists_invariant_sylowOf' hBÊ (hA3.to_le hBA)
  have hF₀Ê : F₀ ≤ Ê := hF₀.le
  have hÊcard : Nat.card Ê = Nat.card P * 9 := by
    rw [hÊ, Subgroup.card_map_of_injective J.subtype_injective]
    have h1 := QuotientGroup.card_preimage_mk P (E : Set (↥J ⧸ P))
    rw [SetLike.coe_sort_coe, hE9] at h1
    exact h1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 P)
  have hF₀9 : Nat.card F₀ = 9 := by
    rw [hF₀.card_eq, hÊcard, hm, factorization_two_pow_mul_nine]
    norm_num
  have hdisj : F₀ ⊓ O = ⊥ := by
    have hd : Disjoint F₀ O := Subgroup.disjoint_of_coprime_natCard (by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
      rw [hF₀9, hn]
      exact Nat.Coprime.pow_right _ (by norm_num))
    exact hd.eq_bot
  have hmemO : ∀ x ∈ F₀, x ∈ O → x = 1 := fun x hx hxO => by
    have : x ∈ F₀ ⊓ O := ⟨hx, hxO⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  have hBC : ∀ b ∈ B, ∀ f ∈ F₀, f * b = b * f := by
    intro b hb f hf
    have h1 : b * f * b⁻¹ ∈ F₀ := (Subgroup.mem_normalizer_iff.mp (hF₀N hb) f).mp hf
    have h2 : b * f * b⁻¹ * f⁻¹ ∈ O := hBtriv b hb f (hÊJ (hF₀Ê hf))
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
  have hBbot : B ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hB9
    norm_num at hB9
  obtain ⟨⟨b₁, hb₁B⟩, hb₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBbot
  have hb₁1' : b₁ ≠ 1 := fun h1 => hb₁1 (Subtype.ext h1)
  have hb₁3 : orderOf b₁ = 3 := orderOf_eq_prime (hAe.2 b₁ (hBA hb₁B)) hb₁1'
  have hzle : Subgroup.zpowers b₁ ≤ B := Subgroup.zpowers_le.mpr hb₁B
  have hzne : Subgroup.zpowers b₁ ≠ B := by
    intro he
    have h1 := Nat.card_zpowers b₁
    rw [he, hB9, hb₁3] at h1
    norm_num at h1
  obtain ⟨b₂, hb₂B, hb₂z⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hzle hzne)
  have hb₂1 : b₂ ≠ 1 := fun h1 => hb₂z (h1 ▸ one_mem _)
  have hb₂3 : orderOf b₂ = 3 := orderOf_eq_prime (hAe.2 b₂ (hBA hb₂B)) hb₂1
  have hBF : ∀ b ∈ B, b ∈ F₀ → b = 1 := by
    intro b hb hbF
    have : b ∈ B ⊓ J := ⟨hb, hÊJ (hF₀Ê hbF)⟩
    rwa [hBJ1, Subgroup.mem_bot] at this
  have hb₁F : b₁ ∉ F₀ := fun h1 => hb₁1' (hBF b₁ hb₁B h1)
  have hb₁C : b₁ ∈ Subgroup.centralizer (F₀ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun f hf => hBC b₁ hb₁B f hf
  obtain ⟨hDcard, hDc, hDe⟩ := CFSG.RankThree.card_sup_zpowers_of_disjoint hb₁C hF₀comm hF₀e
    hb₁3 (Sec12.inf_zpowers_eq_bot_of_not_mem hb₁3 hb₁F)
  set D := F₀ ⊔ Subgroup.zpowers b₁ with hD
  have hD27 : Nat.card D = 27 := by rw [hDcard, hF₀9]
  have hDab : CFSG.Assembly.IsElemAbelian 3 D := ⟨hDc, hDe⟩
  have hb₂D : b₂ ∈ Subgroup.centralizer (D : Set G) := by
    have hle : D ≤ Subgroup.centralizer ({b₂} : Set G) := by
      refine sup_le (fun f hf => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hBC b₂ hb₂B f hf
      · rw [Subgroup.mem_centralizer_singleton_iff]
        simpa using congrArg Subtype.val (hAe.1.is_comm.comm ⟨b₁, hBA hb₁B⟩ ⟨b₂, hBA hb₂B⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 := hle hd
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact h1
  have hb₂notD : b₂ ∉ D := by
    intro hb₂D'
    have hzN : Subgroup.zpowers b₁ ≤ Subgroup.normalizer (F₀ : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hb₁C)
    have hmem : b₂ ∈ ((F₀ : Set G) * (Subgroup.zpowers b₁ : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left F₀ _ hzN]
      exact hb₂D'
    obtain ⟨f, hf, z, hz, hfz⟩ := hmem
    have hfB : f ∈ B := by
      have e : f = b₂ * z⁻¹ := by rw [← hfz]; group
      rw [e]
      exact mul_mem hb₂B (inv_mem (hzle hz))
    have hf1 := hBF f hfB hf
    have hzb : z = b₂ := by simpa [hf1] using hfz
    exact hb₂z (hzb ▸ hz)
  have hDO : D ≤ Subgroup.normalizer (O : Set G) :=
    sup_le ((hF₀Ê.trans hÊJ).trans hJO) (Subgroup.zpowers_le.mpr (hNO (hBJ hb₁B)))
  exact Sec12.false_of_le_E81 hFE hDab hD27 hO hO2 hDO hb₂D hb₂3 hb₂notD

omit [Finite G] in
theorem commutator_mem_of_actQ_eq_one {J : Subgroup G} {m : Subgroup.normalizer (J : Set G)}
    (hm : Sec17.Proof17Res6.actQ J m = 1) :
    ∀ y ∈ J, (m : G) * y * (m : G)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 J := by
  have h1 := Sec17.Proof17Res6.mem_cQuot_of_actQ_eq_one hm
  rw [← SetLike.mem_coe, Sec17.coe_cQuot] at h1
  exact h1.2

theorem nine_le_card_map_actQ_of_forall {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {J : Subgroup G} (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hno : ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 →
      (∀ b ∈ B, ∀ y ∈ J, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 J) → False) :
    9 ≤ Nat.card ((A.subgroupOf (Subgroup.normalizer (J : Set G))).map
      (Sec17.Proof17Res6.actQ J)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA27 : Nat.card A = 27 := h.isE27.2
  set N := Subgroup.normalizer (J : Set G) with hN
  set f : ↥A →* MulAut (↥J ⧸ CFSG.pCore 2 ↥J) :=
    (Sec17.Proof17Res6.actQ J).comp (Subgroup.inclusion hAJ) with hf
  have hrange : f.range = (A.subgroupOf N).map (Sec17.Proof17Res6.actQ J) := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [← hrange]
  by_contra hlt
  push Not at hlt
  have hcard : Nat.card A = Nat.card f.ker * Nat.card f.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hr27 : Nat.card f.range ∣ 27 := by
    rw [← hA27, hcard]
    exact Dvd.intro_left _ rfl
  have hr3 : Nat.card f.range ∣ 3 := by
    have hdivs : Nat.card f.range ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hr27, by norm_num⟩
    have key : ∀ d ∈ Nat.divisors 27, d < 9 → d ∣ 3 := by decide
    exact key _ hdivs hlt
  have hk9 : 3 ^ 2 ∣ Nat.card f.ker := by
    obtain ⟨t, ht⟩ := hr3
    have h27 : Nat.card f.ker * Nat.card f.range = 27 := by rw [← hcard, hA27]
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    refine ⟨t, ?_⟩
    have : Nat.card f.ker * Nat.card f.range * t = 27 * t := by rw [h27]
    rw [mul_assoc, ← ht] at this
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hk9
  set B : Subgroup G := (K.map f.ker.subtype).map A.subtype with hBdef
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hB9 : Nat.card B = 9 := by
    rw [hBdef, Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.card_map_of_injective f.ker.subtype_injective, hK]
    norm_num
  have hBker : ∀ b ∈ B, ∃ hbA : b ∈ A, f ⟨b, hbA⟩ = 1 := by
    rintro _ ⟨_, ⟨k, -, rfl⟩, rfl⟩
    exact ⟨(k : ↥A).2, MonoidHom.mem_ker.mp k.2⟩
  refine hno B hBA hB9 fun b hb y hy => ?_
  obtain ⟨hbA, hfb⟩ := hBker b hb
  exact commutator_mem_of_actQ_eq_one (m := ⟨b, hAJ hbA⟩) hfb y hy

theorem nine_le_card_map_actQ {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {J : Subgroup G} (hO : CFSG.Open.pCoreOf 2 J ≠ ⊥)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hZ : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥)
    {E : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) :
    9 ≤ Nat.card ((A.subgroupOf (Subgroup.normalizer (J : Set G))).map
      (Sec17.Proof17Res6.actQ J)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  refine nine_le_card_map_actQ_of_forall h hAJ fun B hBA hB9 hBtriv => ?_
  have hBJ1 : B ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro b ⟨hbB, hbJ⟩
    have hb3 : b ^ 3 = 1 := hAe.2 b (hBA hbB)
    set bJ : ↥J := ⟨b, hbJ⟩ with hbJdef
    have hZb : QuotientGroup.mk' (CFSG.pCore 2 ↥J) bJ ∈
        Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) z
      have h1 : ((bJ * y * bJ⁻¹ * y⁻¹ : ↥J) : G) ∈ CFSG.Open.pCoreOf 2 J := by
        simpa [hbJdef] using hBtriv b hbB y y.2
      have h2 := (Proof156Res4.mem_pCoreOf_iff_mk_eq_one _).mp h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h2
      show (y : ↥J ⧸ CFSG.pCore 2 ↥J) * (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) =
        (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) * (y : ↥J ⧸ CFSG.pCore 2 ↥J)
      calc (y : ↥J ⧸ CFSG.pCore 2 ↥J) * (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) =
          (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) * (y : ↥J ⧸ CFSG.pCore 2 ↥J) *
            (bJ : ↥J ⧸ CFSG.pCore 2 ↥J)⁻¹ * (y : ↥J ⧸ CFSG.pCore 2 ↥J)⁻¹ *
            ((y : ↥J ⧸ CFSG.pCore 2 ↥J) * (bJ : ↥J ⧸ CFSG.pCore 2 ↥J)) := by
            rw [h2, one_mul]
        _ = (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) * (y : ↥J ⧸ CFSG.pCore 2 ↥J) := by group
    rw [hZ, Subgroup.mem_bot] at hZb
    have hbO : b ∈ CFSG.Open.pCoreOf 2 J :=
      (Proof156Res4.mem_pCoreOf_iff_mk_eq_one bJ).mpr hZb
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J) ⟨b, hbO⟩
    have hb2 : b ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hco : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
    have h1 := (pow_gcd_eq_one (a := b)).mpr ⟨hb2, hb3⟩
    rw [hco.gcd_eq_one, pow_one] at h1
    exact Subgroup.mem_bot.mpr h1
  exact false_of_le_E9_of_trivial h hO hBA hB9 (hBA.trans hAJ) hBtriv hBJ1 hE hE9

end Proof155w3

end CFSG.RankThree.PartTwo.Sec15
