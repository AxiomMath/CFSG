module

public import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2Tools
public import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.RankThree.PartTwo.Late.Uniqueness
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.RankThree.PartTwo.KFacts.AutKinds
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

namespace Step1918Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_of_inv_mul_mem {R : Subgroup G} {a b l : G} (hab : a⁻¹ * b ∈ R)
    (ha : a ∈ Subgroup.normalizer (R : Set G)) (hl : l ∈ Subgroup.normalizer (R : Set G))
    (hb : b * l * b⁻¹ * l⁻¹ ∈ R) : a * l * a⁻¹ * l⁻¹ ∈ R := by
  set o := a⁻¹ * b with ho
  have hbo : b = a * o := by rw [ho]; group
  have h1 : o * (l * o⁻¹ * l⁻¹) ∈ R := R.mul_mem hab
    ((Subgroup.mem_normalizer_iff.mp hl _).mp (R.inv_mem hab))
  have h2 : a * (o * (l * o⁻¹ * l⁻¹)) * a⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp ha _).mp h1
  have h3 := R.mul_mem (R.inv_mem h2) hb
  have e : (a * (o * (l * o⁻¹ * l⁻¹)) * a⁻¹)⁻¹ * (b * l * b⁻¹ * l⁻¹) =
      a * l * a⁻¹ * l⁻¹ := by
    rw [hbo]
    group
  rwa [e] at h3

theorem four_le_localRank_of_pair {Y Q R F₁ F₂ : Subgroup G} (hQ : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q)
    (hYQ : Y ≤ Subgroup.normalizer (Q : Set G)) (hRY : R ≤ Y) (hR2 : IsPGroup 2 R)
    (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hF₁ : CFSG.Assembly.IsElemAbelian 3 F₁) (hF₁9 : Nat.card F₁ = 9) (hF₁Y : F₁ ≤ Y)
    (hF₂ : CFSG.Assembly.IsElemAbelian 3 F₂) (hF₂9 : Nat.card F₂ = 9) (hF₂Y : F₂ ≤ Y)
    (hcomm : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b * a⁻¹ * b⁻¹ ∈ R)
    (hdisj : ∀ a ∈ F₁, ∀ b ∈ F₂, a⁻¹ * b ∈ R → a = 1) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := R.subgroupOf Y with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).mpr hYR
  set π := QuotientGroup.mk' N with hπ
  have hN2 : IsPGroup 2 N := hR2.comap_subtype
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hπ1 : ∀ y : Y, π y = 1 ↔ (y : G) ∈ R := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
  set W₁ := (F₁.subgroupOf Y).map π with hW₁
  set W₂ := (F₂.subgroupOf Y).map π with hW₂
  have hF₁3 : IsPGroup 3 (F₁.subgroupOf Y) := by
    refine IsPGroup.comap_subtype ?_
    exact fun f => ⟨1, Subtype.ext (by simpa using hF₁.2 f f.2)⟩
  have hF₂3 : IsPGroup 3 (F₂.subgroupOf Y) := by
    refine IsPGroup.comap_subtype ?_
    exact fun f => ⟨1, Subtype.ext (by simpa using hF₂.2 f f.2)⟩
  have hW₁card : Nat.card W₁ = 9 := by
    rw [hW₁, Step198DProof.card_map_of_injOn π (Sec12.injOn_mk_of_coprime N hN3 hF₁3),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₁Y).toEquiv, hF₁9]
  have hW₂card : Nat.card W₂ = 9 := by
    rw [hW₂, Step198DProof.card_map_of_injOn π (Sec12.injOn_mk_of_coprime N hN3 hF₂3),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₂Y).toEquiv, hF₂9]
  have hW₁₂ : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    apply Step1910O2Proof.mul_comm_of_commutator_eq_one
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hπ1]
    exact hcomm _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)
  have hW₁c : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (a : G) * b = b * a
    exact congrArg Subtype.val (hF₁.1.is_comm.comm
      ⟨_, Subgroup.mem_subgroupOf.mp ha⟩ ⟨_, Subgroup.mem_subgroupOf.mp hb⟩)
  have hW₂c : ∀ x ∈ W₂, ∀ y ∈ W₂, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (a : G) * b = b * a
    exact congrArg Subtype.val (hF₂.1.is_comm.comm
      ⟨_, Subgroup.mem_subgroupOf.mp ha⟩ ⟨_, Subgroup.mem_subgroupOf.mp hb⟩)
  have hW₁e : ∀ x ∈ W₁, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hπ1]
    have := hF₁.2 _ (Subgroup.mem_subgroupOf.mp ha)
    rw [Subgroup.coe_pow, this]
    exact R.one_mem
  have hW₂e : ∀ x ∈ W₂, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hπ1]
    have := hF₂.2 _ (Subgroup.mem_subgroupOf.mp ha)
    rw [Subgroup.coe_pow, this]
    exact R.one_mem
  have hinf : W₁ ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have h1 : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    rw [hπ1] at h1
    have h2 := hdisj _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)
      (by simpa using h1)
    have h3 : a = 1 := Subtype.ext h2
    rw [h3, map_one]
    exact Subgroup.one_mem _
  have hW₁N : W₁ ≤ Subgroup.normalizer (W₂ : Set (Y ⧸ N)) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun y => by
      constructor
      · intro hy
        rw [hW₁₂ x hx y hy, mul_inv_cancel_right]
        exact hy
      · intro hy
        have h := hW₁₂ x⁻¹ (W₁.inv_mem hx) _ hy
        have e : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
        rw [e, h, mul_inv_cancel_right]
        exact hy
  set W := W₁ ⊔ W₂ with hW
  have hWcard : Nat.card W = 81 := by
    have h := Sec6.card_sup_mul_card_inf hW₁N
    rw [hinf, Subgroup.card_bot, mul_one, hW₁card, hW₂card] at h
    exact h
  have hWmem : ∀ w ∈ W, ∃ x ∈ W₁, ∃ y ∈ W₂, w = x * y := by
    intro w hw
    have hw' : w ∈ ((W₁ ⊔ W₂ : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) := hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right W₁ W₂ hW₁N] at hw'
    obtain ⟨x, hx, y, hy, rfl⟩ := hw'
    exact ⟨x, hx, y, hy, rfl⟩
  have hWc : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u := by
    intro u hu v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := hWmem u hu
    obtain ⟨x', hx', y', hy', rfl⟩ := hWmem v hv
    calc x * y * (x' * y') = x * (y * x') * y' := by group
      _ = x * (x' * y) * y' := by rw [hW₁₂ x' hx' y hy]
      _ = (x * x') * (y * y') := by group
      _ = (x' * x) * (y' * y) := by rw [hW₁c x hx x' hx', hW₂c y hy y' hy']
      _ = x' * (x * y') * y := by group
      _ = x' * (y' * x) * y := by rw [hW₁₂ x hx y' hy']
      _ = x' * y' * (x * y) := by group
  have hWe : ∀ u ∈ W, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := hWmem u hu
    rw [(Commute.mul_pow (hW₁₂ x hx y hy) 3), hW₁e x hx, hW₂e y hy, one_mul]
  have hW3 : IsPGroup 3 W := fun w => ⟨1, Subtype.ext (by simpa using hWe w w.2)⟩
  have hker : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  obtain ⟨S, -, ⟨eS⟩⟩ := RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
    Nat.prime_three π (QuotientGroup.mk'_surjective _) hker W hW3
  set S' := S.map Y.subtype with hS'
  have hS'card : Nat.card S' = 3 ^ 4 := by
    rw [hS', Subgroup.card_map_of_injective Y.subtype_injective, Nat.card_congr eS.toEquiv,
      hWcard]
    norm_num
  have hSmem : ∀ s ∈ S', ∃ t : S, ((t : Y) : G) = s := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hS'c : IsMulCommutative S' := ⟨⟨fun a b => Subtype.ext (by
    obtain ⟨a', ha'⟩ := hSmem a a.2
    obtain ⟨b', hb'⟩ := hSmem b b.2
    change (a : G) * b = b * a
    rw [← ha', ← hb']
    have h : a' * b' = b' * a' := eS.injective (by
      rw [map_mul, map_mul]
      exact Subtype.ext (hWc _ (eS a').2 _ (eS b').2))
    exact congrArg (fun t : S => ((t : Y) : G)) h)⟩⟩
  have hS'e : ∀ s ∈ S', s ^ 3 = 1 := by
    intro s hs
    obtain ⟨t, rfl⟩ := hSmem s hs
    have h : t ^ 3 = 1 := eS.injective (by
      rw [map_pow, map_one]
      exact Subtype.ext (hWe _ (eS t).2))
    exact congrArg (fun t : S => ((t : Y) : G)) h
  have hS'N : S' ≤ Subgroup.normalizer (Q : Set G) := (Subgroup.map_subtype_le _).trans hYQ
  exact Theta.le_localRank_of_le_normalizer (by norm_num) hQ hQ2 hS'c hS'e hS'card hS'N

omit [Finite G] in
theorem eq_one_of_mem_pCore_two {J : Type*} [Group J] [Finite J] {x : J}
    (hx : x ∈ CFSG.pCore 2 J) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := J)).exists_card_eq
  have h2 : orderOf x ∣ 2 ^ n := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : CFSG.pCore 2 J)
    rwa [Subgroup.orderOf_mk, hn] at this
  have h3 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ n) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)

theorem exists_lift {J X : Subgroup G} (hX3 : IsPGroup 3 X)
    (hXJ : X ≤ Subgroup.normalizer (J : Set G)) {x : J ⧸ CFSG.pCore 2 J}
    (hfix : ∀ a (ha : a ∈ X), Step199Proof.pCoreAct J ⟨a, hXJ ha⟩ x = x) (hx3 : x ^ 3 = 1) :
    ∃ y : J, (y : J ⧸ CFSG.pCore 2 J) = x ∧ (y : G) ^ 3 = 1 ∧ ∀ a ∈ X, a * y = (y : G) * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  set O := CFSG.Open.pCoreOf 2 J with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨n, hn⟩ := hO2.exists_card_eq
    rw [hn]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    hXJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hk : ∀ a ∈ X, (k : G)⁻¹ * (a * k * a⁻¹) ∈ O := by
    intro a ha
    have hmem : a * (k : G) * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hXJ ha) _).mp k.2
    have h1 := hfix a ha
    rw [Step199Proof.pCoreAct_mk ⟨a, hXJ ha⟩ k ⟨_, hmem⟩ rfl] at h1
    have h2 : k⁻¹ * ⟨_, hmem⟩ ∈ CFSG.pCore 2 J := QuotientGroup.eq.mp h1.symm
    rw [Step1911EndProof.mem_pCore_iff] at h2
    simpa using h2
  obtain ⟨y₀, hy₀, hy₀X⟩ := Step199Proof.exists_fixed_mem_coset hX3 hO3 hXO hk
  have hy₀J : y₀ ∈ J := by
    have := J.mul_mem k.2 ((CFSG.LieType.BorelTits.pCoreOf_le 2 J) hy₀)
    simpa using this
  set y₁ : J := ⟨y₀, hy₀J⟩ with hy₁def
  have hy₁ : (y₁ : J ⧸ CFSG.pCore 2 J) = (k : J ⧸ CFSG.pCore 2 J) := by
    apply QuotientGroup.eq.mpr
    rw [Step1911EndProof.mem_pCore_iff]
    have := O.inv_mem hy₀
    simpa [hy₁def] using this
  obtain ⟨a, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₁).ne' 3 (by norm_num)
  set w : J := y₁ ^ (m ^ 2) with hw
  have hwa : w ^ (3 ^ a) = 1 := by
    rw [hw, ← pow_mul, show m ^ 2 * 3 ^ a = (3 ^ a * m) * m by ring, pow_mul, ← hord,
      pow_orderOf_eq_one, one_pow]
  have hm2 : m ^ 2 % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have hwx : (w : J ⧸ CFSG.pCore 2 J) = (k : J ⧸ CFSG.pCore 2 J) := by
    rw [hw, QuotientGroup.mk_pow, hy₁, ← Nat.div_add_mod (m ^ 2) 3, hm2, pow_add, pow_mul,
      hx3, one_pow, one_mul, pow_one]
  have hw3 : w ^ 3 = 1 := by
    have h1 : w ^ 3 ∈ CFSG.pCore 2 J := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hwx, hx3]
    refine eq_one_of_mem_pCore_two h1 (k := a) ?_
    rw [← pow_mul, mul_comm, pow_mul, hwa, one_pow]
  refine ⟨w, hwx, by simpa using congrArg Subtype.val hw3, fun b hb => ?_⟩
  rw [hw, Subgroup.coe_pow]
  exact (Commute.pow_right (hy₀X b hb) (m ^ 2))

theorem exists_mem_of_conj_mem_range (hst : PartTwoStanding G) (hS : partTwoS G = ∅)
    {X J : Subgroup G} (hX : X ∈ partTwoE G) (hXJ : X ≤ Subgroup.normalizer (J : Set G))
    (hZ : Subgroup.center (J ⧸ CFSG.pCore 2 J) = ⊥) {x : J ⧸ CFSG.pCore 2 J}
    (hx : MulAut.conj x ∈ ((Step199Proof.pCoreAct J).comp (Subgroup.inclusion hXJ)).range) :
    ∃ y : J, (y : G) ∈ X ∧ (y : J ⧸ CFSG.pCore 2 J) = x := by
  have hXe := isE27_of_mem_partTwoE hX
  set ρ := (Step199Proof.pCoreAct J).comp (Subgroup.inclusion hXJ) with hρ
  have hconj := Step1914TriProof.conj_injective_of_center_eq_bot' hZ
  obtain ⟨a₀, ha₀⟩ := hx
  have hfix : ∀ a (ha : a ∈ X), Step199Proof.pCoreAct J ⟨a, hXJ ha⟩ x = x := by
    intro a ha
    have hcomm : ρ ⟨a, ha⟩ * ρ a₀ = ρ a₀ * ρ ⟨a, ha⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (congrArg Subtype.val (hXe.1.1.is_comm.comm ⟨a, ha⟩ ⟨a₀, a₀.2⟩))
    apply hconj
    rw [← KFacts.mul_mulAutConj_mul_inv]
    change ρ ⟨a, ha⟩ * MulAut.conj x * (ρ ⟨a, ha⟩)⁻¹ = MulAut.conj x
    rw [← ha₀, hcomm, mul_inv_cancel_right]
  have hx3 : x ^ 3 = 1 := by
    apply hconj
    rw [map_pow, ← ha₀, ← map_pow, map_one]
    have : a₀ ^ 3 = 1 := Subtype.ext (by simpa using hXe.1.2 _ a₀.2)
    rw [this, map_one]
  obtain ⟨y, hyx, hy3, hyX⟩ := exists_lift hXe.isPGroup hXJ hfix hx3
  refine ⟨y, mem_of_le_centralizer hst hS hX hy3 fun a ha => ?_, hyx⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hyX a ha)

theorem pCoreOf_le_pCoreOf_of_eq_sup {K L : Subgroup G} (hLK : L ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) :
    CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set OL := CFSG.Open.pCoreOf 2 L with hOL
  set OK := CFSG.Open.pCoreOf 2 K with hOK
  have hOLL : OL ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hOKK : OK ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKOK : K ≤ Subgroup.normalizer (OK : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hLOL : L ≤ Subgroup.normalizer (OL : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  set P := OL ⊔ OK with hP
  have hP2 : IsPGroup 2 P := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_sup_of_normal_right'
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) (hOLL.trans (hLK.trans hKOK))
  have hPK : P ≤ K := sup_le (hOLL.trans hLK) hOKK
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := by
    apply Sec6.le_normalizer_sup_of_conj
    · intro a ha x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hLOL ha) x).mp hx)
    · intro a ha x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hKOK (hLK ha)) x).mp hx)
  have hOP : OK ≤ Subgroup.normalizer (P : Set G) := by
    apply Sec6.le_normalizer_sup_of_conj
    · intro a ha x hx
      have hxK : x ∈ K := hLK (hOLL hx)
      have h1 : a * x * a⁻¹ * x⁻¹ ∈ OK := by
        have h2 : x * a⁻¹ * x⁻¹ ∈ OK :=
          (Subgroup.mem_normalizer_iff.mp (hKOK hxK) _).mp (OK.inv_mem ha)
        have h3 := OK.mul_mem ha h2
        rwa [show a * (x * a⁻¹ * x⁻¹) = a * x * a⁻¹ * x⁻¹ by group] at h3
      rw [show a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x by group, sup_comm]
      exact Subgroup.mul_mem_sup h1 hx
    · intro a ha x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hKOK (hOKK ha)) x).mp hx)
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := by
    rw [hKL]
    exact sup_le hLP hOP
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPK hKP hP2)

theorem exists_quotientEquiv {K L : Subgroup G} (hLK : L ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) :
    ∃ ι : (L ⧸ CFSG.pCore 2 L) ≃* (K ⧸ CFSG.pCore 2 K),
      ∀ l : L, ι (l : L ⧸ CFSG.pCore 2 L) =
        ((Subgroup.inclusion hLK l : K) : K ⧸ CFSG.pCore 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := Step1911EndProof.phiL hLK with hφ
  have hsurj := Step1911EndProof.phiL_surjective hLK hKL
  have hker : φ.ker = CFSG.pCore 2 L := by
    ext l
    rw [MonoidHom.mem_ker, Step1911EndProof.phiL_eq_one_iff, Step1911EndProof.mem_pCore_iff]
    constructor
    · intro h
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun _j hj => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj,
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (hLK hj)⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_right) ⟨l.2, h⟩
    · intro h
      exact pCoreOf_le_pCoreOf_of_eq_sup hLK hKL h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj), fun l => rfl⟩

theorem exists_elemAbelian_nine
    {A L E M : Subgroup G} {c : G} (h1913 : Step1913) (hctx : Ctx1912 G A c L E M) :
    ∃ F : Subgroup G, F ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθ, -, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hctx.mem_lA.1
  set ι : L ⧸ aschbacherSolvableCore 3 L ≃* L ⧸ CFSG.pCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq hθ with hι
  rcases h1913 G A c L E M hctx with ⟨p, e, hp, he, hiso⟩ | hM12
  ·
    set X := L ⧸ aschbacherSolvableCore 3 L with hX
    have hXq : CFSG.IsQuasisimple X := Sec12.isQuasisimple_thetaQuot_of_mem hctx.mem_lA.1
    have hisoT : Sec4.IsoLThreePi (⊤ : Subgroup X) p e := by
      rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
      · exact Or.inl ⟨hq, ⟨(Subgroup.topEquiv.trans ι).trans φ⟩⟩
      · exact Or.inr ⟨hq, ⟨(Subgroup.topEquiv.trans ι).trans φ⟩⟩
    have hTq : CFSG.IsQuasisimple (⊤ : Subgroup X) :=
      LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hXq
    obtain ⟨π, K, _, hK, hq, -, ⟨ψ⟩⟩ := Sec4.exists_pslPi_model he hisoT hTq
    obtain ⟨D, hD, hD9⟩ := Sec13.exists_elemAbelian_nine_projImage_slPi hK hq
    set ψ' : CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ e) K) ≃* X :=
      ψ.symm.trans Subgroup.topEquiv with hψ'
    have hDb := Sec13.isElemAbelian_map hD ψ'.toMonoidHom
    have hDb9 : Nat.card (D.map ψ'.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective ψ'.injective, hD9]
    obtain ⟨S, -, hS, hS9, -⟩ := Sec13.exists_elemAbelian_map_eq (H := L) (M := ⊤) hDb
      (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
    refine ⟨S.map L.subtype, Subgroup.map_subtype_le _, Sec13.isElemAbelian_map hS _, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective, hS9, hDb9]
  ·
    obtain ⟨-, hZ, hinn, -⟩ := KFacts.ks18M12 _ hM12
    have hA := isE27_of_mem_partTwoE hctx.mem_partTwoE
    have hAL : A ≤ Subgroup.normalizer (L : Set G) := hctx.mem_lA.2.1
    set ρ := (Step199Proof.pCoreAct L).comp (Subgroup.inclusion hAL) with hρ
    have hconj := Step1914TriProof.conj_injective_of_center_eq_bot' hZ
    have hrange : ρ.range ≤ (MulAut.conj : L ⧸ CFSG.pCore 2 L →* MulAut _).range := by
      rintro _ ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := hinn (ρ a) ⟨1, by
        have : a ^ 3 = 1 := Subtype.ext (by simpa using hA.1.2 _ a.2)
        rw [pow_one, ← map_pow, this, map_one]⟩
      exact ⟨x, hx.symm⟩
    have hker : Nat.card ρ.ker ≤ 3 := by
      have hle : ρ.ker.map A.subtype ≤ Subgroup.zpowers c := by
        rintro _ ⟨a, ha, rfl⟩
        have hsc : (a : G) ∈ Late.sectionCentralizer A L
            ((aschbacherSolvableCore 3 L).map L.subtype) := by
          refine ⟨a.2, fun l hl => ?_⟩
          have h1 := congrArg (fun σ : MulAut (L ⧸ CFSG.pCore 2 L) =>
            σ ((⟨l, hl⟩ : L) : L ⧸ CFSG.pCore 2 L)) (MonoidHom.mem_ker.mp ha)
          have hmem : (a : G) * l * (a : G)⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.mp (hAL a.2) l).mp hl
          simp only [hρ, MonoidHom.comp_apply, MulAut.one_apply] at h1
          rw [Step199Proof.pCoreAct_mk _ ⟨l, hl⟩ ⟨_, hmem⟩ rfl] at h1
          have h2 : (⟨l, hl⟩ : L)⁻¹ * ⟨_, hmem⟩ ∈ CFSG.pCore 2 L := QuotientGroup.eq.mp h1.symm
          rw [← hθ] at h2
          have h3 : (⟨l, hl⟩ : L) * ((⟨l, hl⟩ : L)⁻¹ * ⟨_, hmem⟩) * (⟨l, hl⟩ : L)⁻¹ ∈
              aschbacherSolvableCore 3 L :=
            (aschbacherSolvableCore_normal 3 L).conj_mem _ h2 _
          refine ⟨_, h3, ?_⟩
          simp
        have := hctx.mem_lA.2.2.1
        rw [this] at hsc
        exact hsc
      calc Nat.card ρ.ker = Nat.card (ρ.ker.map A.subtype) :=
            (Subgroup.card_map_of_injective A.subtype_injective).symm
        _ ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hle
        _ = 3 := hctx.zpowers_mem_omegaA.2.1
    have hcard : Nat.card ρ.range * Nat.card ρ.ker = 27 := by
      rw [← Subgroup.index_ker, mul_comm, Subgroup.card_mul_index, hA.2]
    have hρ9 : 9 ≤ Nat.card ρ.range := by
      have hpos : 0 < Nat.card ρ.ker := Nat.card_pos
      nlinarith
    set V := ρ.range.comap (MulAut.conj : L ⧸ CFSG.pCore 2 L →* MulAut _) with hV
    have hVcard : Nat.card V = Nat.card ρ.range := by
      rw [← Subgroup.map_comap_eq_self hrange, Subgroup.card_map_of_injective hconj]
    have hVle : V ≤ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) := by
      intro x hx
      obtain ⟨y, hyA, hyx⟩ := exists_mem_of_conj_mem_range hctx.toPartTwoStanding
        hctx.partTwoS_eq hctx.mem_partTwoE hAL hZ hx
      exact ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hyA, y.2⟩, hyx⟩
    have h9 : 9 ≤ Nat.card (A ⊓ L : Subgroup G) :=
      calc 9 ≤ Nat.card V := hVcard ▸ hρ9
        _ ≤ Nat.card (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L))) :=
          Subgroup.card_le_of_le hVle
        _ ≤ Nat.card ((A ⊓ L).subgroupOf L) := Nat.le_of_dvd Nat.card_pos
          (Subgroup.card_map_dvd _ _)
        _ = Nat.card (A ⊓ L : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    refine ⟨A ⊓ L, inf_le_right, isElemAbelian_of_le hA.1 inf_le_left, ?_⟩
    interval_cases k
    · rw [hk] at h9; norm_num at h9
    · rw [hk] at h9; norm_num at h9
    · rw [hk]; norm_num
    · exfalso
      have heq : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hA.2]; norm_num)
      have hcA := Step1916Proof2.mem_A hctx
      rw [← heq] at hcA
      exact Step1916Proof2.not_mem_L hctx hcA.2

end Step1918Proof

end CFSG.RankThree.PartTwo.Sec19
