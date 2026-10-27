module

public import CFSG.RankThree.PartTwo.Late.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Sec8.Standing
import CFSG.RankThree.CentralCover.FourGroupWitness

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

private theorem centralQ_le_of_isSylowOf {Q R : Subgroup G} (hQ : IsSylowOf 3 Q R) :
    Q ≤ R := by
  obtain ⟨P, rfl⟩ := hQ
  exact Subgroup.map_subtype_le _

private theorem centralQ_isPGroup_of_isSylowOf {Q R : Subgroup G} (hQ : IsSylowOf 3 Q R) :
    IsPGroup 3 Q := by
  obtain ⟨P, rfl⟩ := hQ
  exact P.isPGroup'.map R.subtype

private theorem centralQ_mem_iff {U : Subgroup G} {x : G} :
    x ∈ sectionCentralizer U L (CFSG.Open.pCoreOf 2 L) ↔
      x ∈ U ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
  Iff.rfl

private theorem centralQ_mem_zpowers_of_isCyclic {K : Subgroup G} (hK : IsCyclic K) {c : G}
    (hcK : c ∈ K) (hc3 : orderOf c = 3) {x : G} (hxK : x ∈ K) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.zpowers c := by
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hc'3 : orderOf (⟨c, hcK⟩ : K) = 3 := by
    rw [Subgroup.orderOf_mk c hcK, hc3]
  have hx'3 : orderOf (⟨x, hxK⟩ : K) = 3 := by
    rw [Subgroup.orderOf_mk x hxK, hxo]
  have heq : Subgroup.zpowers (⟨c, hcK⟩ : K) = Subgroup.zpowers (⟨x, hxK⟩ : K) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hc'3, hx'3])
  have hx'mem : (⟨x, hxK⟩ : K) ∈ Subgroup.zpowers (⟨c, hcK⟩ : K) := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'mem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem Hyp1921.isCyclic_sectionCentralizer_of (h : Hyp1921 G A M N L)
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hZ : ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      x ∈ CFSG.Open.pCoreOf 2 L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N)
    (hQL9 : Nat.card (Q ⊓ L : Subgroup G) = 9)
    (hQLE : CFSG.Open.IsElemAbelian 3 (Q ⊓ L : Subgroup G))
    (hQL2 : (Q ⊓ L : Subgroup G) ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    {K : Subgroup G} (hK : (K : Set G) = sectionCentralizer Q L (CFSG.Open.pCoreOf 2 L)) :
    IsCyclic K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQle : Q ≤ N := centralQ_le_of_isSylowOf hQ
  have hQp : IsPGroup 3 Q := centralQ_isPGroup_of_isSylowOf hQ
  have hmemK : ∀ x, x ∈ K ↔ x ∈ sectionCentralizer Q L (CFSG.Open.pCoreOf 2 L) :=
    fun x => Set.ext_iff.mp hK x
  have hKQ : K ≤ Q := fun x hx => (centralQ_mem_iff.mp ((hmemK x).mp hx)).1
  have hK3 : IsPGroup 3 K := hQp.to_le hKQ
  refine isCyclic_of_forall_elemAbelian_card_le_three hK3 fun F hFK hF => ?_
  by_contra hF3
  have hF3' : IsPGroup 3 F := hK3.to_le hFK
  obtain ⟨j, hj⟩ := hF3'.exists_card_eq
  have hj2 : 2 ≤ j := by
    by_contra hlt
    apply hF3
    rw [hj]
    calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := by norm_num
  obtain ⟨F₀, hF₀F, hF₀e, hF₀9⟩ : ∃ F₀ : Subgroup G, F₀ ≤ F ∧
      CFSG.Open.IsElemAbelian 3 F₀ ∧ Nat.card F₀ = 9 := by
    obtain ⟨F₀', hF₀'⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) 3 (n := 2)
      (by rw [hj]; exact pow_dvd_pow 3 hj2)
    refine ⟨F₀'.map F.subtype, Subgroup.map_subtype_le F₀',
      isElemAbelian_of_le hF (Subgroup.map_subtype_le F₀'), ?_⟩
    calc Nat.card (F₀'.map F.subtype : Subgroup G) = Nat.card F₀' :=
          Subgroup.card_map_of_injective F.subtype_injective
      _ = 3 ^ 2 := hF₀'
      _ = 9 := by norm_num
  set B : Subgroup G := Q ⊓ L with hBdef
  have hBmem : ∀ b, b ∈ B ↔ b ∈ Q ∧ b ∈ L := fun b => Subgroup.mem_inf
  have hBQ : B ≤ Q := fun b hb => ((hBmem b).mp hb).1
  have hBe : CFSG.Open.IsElemAbelian 3 B := hQLE
  have hB9 : Nat.card B = 9 := hQL9
  have hBL2 : B ⊓ CFSG.Open.pCoreOf 2 L = ⊥ := hQL2
  have hF₀K : F₀ ≤ K := hF₀F.trans hFK
  have hF₀Q : F₀ ≤ Q := hF₀K.trans hKQ
  have hcomm : ∀ f ∈ F₀, ∀ b ∈ B, f * b = b * f := by
    intro f hf b hb
    have hfQ : f ∈ Q := hF₀Q hf
    have hfN : f ∈ Subgroup.normalizer (L : Set G) := hNL (hQle hfQ)
    obtain ⟨hbQ, hbL⟩ := (hBmem b).mp hb
    have hfc : f * b * f⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
      (centralQ_mem_iff.mp ((hmemK f).mp (hF₀K hf))).2 b hbL
    have h1 : f * b * f⁻¹ * b⁻¹ ∈ B := by
      refine (hBmem _).mpr ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hfQ hbQ) (Q.inv_mem hfQ))
        (Q.inv_mem hbQ), ?_⟩
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hfN b).mp hbL) (L.inv_mem hbL)
    have h2 : f * b * f⁻¹ * b⁻¹ = 1 := by
      have h3 : f * b * f⁻¹ * b⁻¹ ∈ B ⊓ CFSG.Open.pCoreOf 2 L :=
        Subgroup.mem_inf.mpr ⟨h1, hfc⟩
      rw [hBL2, Subgroup.mem_bot] at h3
      exact h3
    calc f * b = (f * b * f⁻¹ * b⁻¹)⁻¹⁻¹ * (b * f) := by group
      _ = b * f := by rw [h2, inv_one, inv_one, one_mul]
  have hdisj : F₀ ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbF, hbB⟩ := Subgroup.mem_inf.mp hb
    have hbO : b ∈ CFSG.Open.pCoreOf 2 L :=
      hZ b ((hBmem b).mp hbB).2 (centralQ_mem_iff.mp ((hmemK b).mp (hF₀K hbF))).2
    have h3 : b ∈ B ⊓ CFSG.Open.pCoreOf 2 L := Subgroup.mem_inf.mpr ⟨hbB, hbO⟩
    rw [hBL2, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr h3
  have hBcent : B ≤ Subgroup.centralizer (F₀ : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun f hf => hcomm f hf b hb
  have hBnorm : B ≤ Subgroup.normalizer (F₀ : Set G) :=
    hBcent.trans (Subgroup.centralizer_le_normalizer _)
  have hEcard : Nat.card (F₀ ⊔ B : Subgroup G) = 81 := by
    have hc := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hBnorm hdisj
    rw [hF₀9, hB9] at hc
    omega
  have hEab : CFSG.Open.IsElemAbelian 3 (F₀ ⊔ B : Subgroup G) := by
    have hFF : F₀ ≤ Subgroup.centralizer (F₀ : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hF₀e.1
    have hBB : B ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hBe.1
    refine ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp ?_, ?_⟩
    · refine sup_le ?_ ?_
      · exact Subgroup.le_centralizer_iff.mpr (sup_le hFF hBcent)
      · exact Subgroup.le_centralizer_iff.mpr
          (sup_le (Subgroup.le_centralizer_iff.mpr hBcent) hBB)
    · intro x hx
      have hx' : x ∈ (F₀ : Set G) * (B : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left F₀ B hBnorm]
        exact hx
      obtain ⟨f, hf, b, hb, rfl⟩ := hx'
      have hc : Commute f b := hcomm f hf b hb
      rw [hc.mul_pow, hF₀e.2 f hf, hBe.2 b hb, one_mul]
  have hEN : (F₀ ⊔ B : Subgroup G) ≤ N := sup_le (hF₀Q.trans hQle) (hBQ.trans hQle)
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).exists_card_eq
  have hX3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 N) := by
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hodd := Sec8.odd_card_of_le_normalizer (h.toTheoremFourHyp.localRank_three).le hEab
    hEcard hX3 (hEN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : CFSG.Open.pCoreOf 2 N = ⊥ :=
      Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
    exact pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM_N.1 h1
  rw [hk] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)

theorem Hyp1921.mul_comm_of_mem_of (h : Hyp1921 G A M N L)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {Q : Subgroup G} (hQ : IsSylowOf 3 Q N)
    (hAQ : A ≤ Q) {K : Subgroup G}
    (hK : (K : Set G) = sectionCentralizer Q L (CFSG.Open.pCoreOf 2 L)) (hKc : IsCyclic K)
    {c : G} (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G))
    (hc3 : orderOf c = 3) :
    ∀ q ∈ Q, q * c = c * q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQle : Q ≤ N := centralQ_le_of_isSylowOf hQ
  have hQp : IsPGroup 3 Q := centralQ_isPGroup_of_isSylowOf hQ
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := hQle.trans hNL
  have hmemK : ∀ x, x ∈ K ↔ x ∈ sectionCentralizer Q L (CFSG.Open.pCoreOf 2 L) :=
    fun x => Set.ext_iff.mp hK x
  have hcmem : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hc]
    exact Subgroup.mem_zpowers c
  obtain ⟨hcA, hcL⟩ := centralQ_mem_iff.mp hcmem
  have hcQ : c ∈ Q := hAQ hcA
  have hcK : c ∈ K := (hmemK c).mpr (centralQ_mem_iff.mpr ⟨hcQ, hcL⟩)
  have hKnorm : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K := by
    intro q hq k hk
    obtain ⟨hkQ, hkL⟩ := centralQ_mem_iff.mp ((hmemK k).mp hk)
    refine (hmemK _).mpr (centralQ_mem_iff.mpr ⟨Q.mul_mem (Q.mul_mem hq hkQ) (Q.inv_mem hq),
      fun x hx => ?_⟩)
    have hqN : q ∈ Subgroup.normalizer (L : Set G) := hQN hq
    have hx' : q⁻¹ * x * q ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hqN) x).mp hx
      simpa using this
    have h1 := hkL _ hx'
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hqN) _).mp h1
    have e : q * (k * (q⁻¹ * x * q) * k⁻¹ * (q⁻¹ * x * q)⁻¹) * q⁻¹ =
        q * k * q⁻¹ * x * (q * k * q⁻¹)⁻¹ * x⁻¹ := by
      group
    rw [e] at h2
    exact h2
  have hc3' : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  have hcn : ∀ q ∈ Q, q * c * q⁻¹ ∈ Subgroup.zpowers c := by
    intro q hq
    refine centralQ_mem_zpowers_of_isCyclic hKc hcK hc3 (hKnorm q hq c hcK) ?_
    rw [conj_pow, hc3', mul_one, mul_inv_cancel]
  have hnorm : Q ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro q hq
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have e : q * c ^ i * q⁻¹ = (q * c * q⁻¹) ^ i := by
      rw [conj_zpow]
    rw [e]
    exact Subgroup.zpow_mem _ (hcn q hq) i
  have hle : Subgroup.zpowers c ≤ Q := Subgroup.zpowers_le.mpr hcQ
  have hHn : ((Subgroup.zpowers c).subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm
  have hQnil : Group.IsNilpotent Q := hQp.isNilpotent
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc3
    norm_num at hc3
  have hHne : (Subgroup.zpowers c).subgroupOf Q ≠ ⊥ := by
    intro hbot
    have hmem : (⟨c, hcQ⟩ : Q) ∈ (Subgroup.zpowers c).subgroupOf Q :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hc1 (congrArg Subtype.val hmem)
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
  have hzH : ((z : Q) : G) ∈ Subgroup.zpowers c :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
  have hzC : (z : Q) ∈ Subgroup.center Q := (Subgroup.mem_inf.mp z.2).2
  have hz1 : ((z : Q) : G) ≠ 1 := fun h1 => hz (Subtype.ext (Subtype.ext h1))
  have hord : orderOf ((z : Q) : G) = 3 := by
    have hdvd := orderOf_dvd_of_mem_zpowers hzH
    rw [hc3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h1
  have hzgen : Subgroup.zpowers ((z : Q) : G) = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzH)
      (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hord]))
  have hcz : c ∈ Subgroup.zpowers ((z : Q) : G) := by
    rw [hzgen]
    exact Subgroup.mem_zpowers c
  intro q hq
  have hcomm : Commute q ((z : Q) : G) := by
    have hzc := Subgroup.mem_center_iff.mp hzC ⟨q, hq⟩
    exact congrArg Subtype.val hzc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
  rw [← hk]
  exact (hcomm.zpow_right k).eq

end CFSG.RankThree.PartTwo.Late
