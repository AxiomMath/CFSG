module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowSpor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429

theorem isElementaryAbelian_of_isElemAbelian {L : Type} [Group L] {p : ℕ} {B : Subgroup L}
    (h : CFSG.Assembly.IsElemAbelian p B) : CFSG.IsElementaryAbelian p B :=
  CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.2
    ⟨fun a ha b hb => congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩), h.2⟩

theorem exists_move_of_automizer {S : Type} [Group S] [Finite S] {B : Subgroup S}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hA : Nonempty (CFSG.RankThree.Asc83Table.Automizer B ≃* CFSG.RankThree.Asc83Table.GL23))
    {s : S} (hs : s ∈ B) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (B : Set S), n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hs3 : s ^ 3 = 1 := hB.2 s hs
  have hord : Nat.card (Subgroup.zpowers s) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hs3 hs1]
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ B, t ∉ Subgroup.zpowers s := by
    by_contra h
    push Not at h
    have hle : B ≤ Subgroup.zpowers s := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hgen : B ≤ Subgroup.closure ({s, t} : Set S) := by
    have hHB : Subgroup.closure ({s, t} : Set S) ≤ B := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with h | h
      · rw [h]; exact hs
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact ht
    have hsH : Subgroup.zpowers s ≤ Subgroup.closure ({s, t} : Set S) :=
      Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
    have htH : t ∈ Subgroup.closure ({s, t} : Set S) := Subgroup.subset_closure (by simp)
    have hd1 : Nat.card (Subgroup.closure ({s, t} : Set S)) ∣ 9 := by
      have := Subgroup.card_dvd_of_le hHB
      rwa [hB9] at this
    have hd3 : 3 ∣ Nat.card (Subgroup.closure ({s, t} : Set S)) := by
      have := Subgroup.card_dvd_of_le hsH
      rwa [hord] at this
    have hne3 : Nat.card (Subgroup.closure ({s, t} : Set S)) ≠ 3 := by
      intro h3
      apply htn
      have heq : Subgroup.zpowers s = Subgroup.closure ({s, t} : Set S) :=
        Subgroup.eq_of_le_of_card_ge hsH (by rw [h3, hord])
      rw [heq]
      exact htH
    have hH9 : Nat.card (Subgroup.closure ({s, t} : Set S)) = 9 := by
      generalize Nat.card (Subgroup.closure ({s, t} : Set S)) = n at hd1 hd3 hne3 ⊢
      have hn : n ≤ 9 := Nat.le_of_dvd (by norm_num) hd1
      interval_cases n <;> omega
    exact (Subgroup.eq_of_le_of_card_ge hHB (by omega)).symm.le
  obtain ⟨φ⟩ := hA
  set ψ : Subgroup.normalizer (B : Set S) →* MulAut B := Subgroup.normalizerMonoidHom B with hψ
  have hkerψ : ψ.ker =
      (Subgroup.centralizer (B : Set S)).subgroupOf (Subgroup.normalizer (B : Set S)) :=
    Subgroup.normalizerMonoidHom_ker B
  have h48 : Nat.card ψ.range = 48 := by
    have e1 : CFSG.RankThree.Asc83Table.Automizer B ≃* ψ.range :=
      (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
    rw [← Nat.card_congr e1.toEquiv, Nat.card_congr φ.toEquiv,
      CFSG.RankThree.Asc83Table.card_GL23]
  have hψapp : ∀ (n : Subgroup.normalizer (B : Set S)) (b : B),
      ((ψ n b : B) : S) = (n : S) * (b : S) * (n : S)⁻¹ :=
    fun n b => rfl
  have hmemS : ∀ n : Subgroup.normalizer (B : Set S),
      ((ψ n ⟨s, hs⟩ : B) : S) ∈ Subgroup.zpowers s := by
    intro n
    have h1 : (n : S) ∈ Subgroup.normalizer (Subgroup.zpowers s : Set S) := hcon (n : S) n.2
    exact (Subgroup.mem_normalizer_iff.mp h1 s).mp (Subgroup.mem_zpowers s)
  have hφmem : ∀ φ' : ψ.range, ((φ'.1 ⟨s, hs⟩ : B) : S) ∈ Subgroup.zpowers s := by
    rintro ⟨φ', hφ'⟩
    obtain ⟨n, rfl⟩ := hφ'
    exact hmemS n
  let F : ψ.range → ↥(Subgroup.zpowers s) × ↥B := fun φ' =>
    (⟨((φ'.1 ⟨s, hs⟩ : B) : S), hφmem φ'⟩, φ'.1 ⟨t, ht⟩)
  have hkey : ∀ n m : Subgroup.normalizer (B : Set S),
      (n : S) * s * (n : S)⁻¹ = (m : S) * s * (m : S)⁻¹ →
      (n : S) * t * (n : S)⁻¹ = (m : S) * t * (m : S)⁻¹ → ψ n = ψ m := by
    intro n m h1 h2
    have hdN : (m : S)⁻¹ * (n : S) ∈ Subgroup.normalizer (B : Set S) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ m.2) n.2
    have hds : ((m : S)⁻¹ * (n : S)) * s = s * ((m : S)⁻¹ * (n : S)) := by
      calc ((m : S)⁻¹ * (n : S)) * s = (m : S)⁻¹ * ((n : S) * s * (n : S)⁻¹) * (n : S) := by
            group
        _ = (m : S)⁻¹ * ((m : S) * s * (m : S)⁻¹) * (n : S) := by rw [h1]
        _ = s * ((m : S)⁻¹ * (n : S)) := by group
    have hdt : ((m : S)⁻¹ * (n : S)) * t = t * ((m : S)⁻¹ * (n : S)) := by
      calc ((m : S)⁻¹ * (n : S)) * t = (m : S)⁻¹ * ((n : S) * t * (n : S)⁻¹) * (n : S) := by
            group
        _ = (m : S)⁻¹ * ((m : S) * t * (m : S)⁻¹) * (n : S) := by rw [h2]
        _ = t * ((m : S)⁻¹ * (n : S)) := by group
    have hclos : Subgroup.closure ({s, t} : Set S) ≤
        Subgroup.centralizer ({(m : S)⁻¹ * (n : S)} : Set S) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      rcases hy with h | h
      · rw [h]; exact hds
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact hdt
    have hdC : (m : S)⁻¹ * (n : S) ∈ Subgroup.centralizer (B : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' := hclos (hgen hx)
      rw [Subgroup.mem_centralizer_iff] at hx'
      exact (hx' _ (Set.mem_singleton _)).symm
    have hker1 : (⟨(m : S)⁻¹ * (n : S), hdN⟩ : Subgroup.normalizer (B : Set S)) ∈ ψ.ker := by
      rw [hkerψ, Subgroup.mem_subgroupOf]
      exact hdC
    have hone : ψ ⟨(m : S)⁻¹ * (n : S), hdN⟩ = 1 := MonoidHom.mem_ker.mp hker1
    have hnm : n = m * ⟨(m : S)⁻¹ * (n : S), hdN⟩ := Subtype.ext (by simp)
    calc ψ n = ψ (m * ⟨(m : S)⁻¹ * (n : S), hdN⟩) := congrArg ψ hnm
      _ = ψ m := by rw [map_mul, hone, mul_one]
  have hF : Function.Injective F := by
    rintro ⟨φ', hφ'⟩ ⟨φ'', hφ''⟩ h
    obtain ⟨n, rfl⟩ := hφ'
    obtain ⟨m, rfl⟩ := hφ''
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : (n : S) * s * (n : S)⁻¹ = (m : S) * s * (m : S)⁻¹ :=
      ((hψapp n ⟨s, hs⟩).symm.trans h1).trans (hψapp m ⟨s, hs⟩)
    have h2' : (n : S) * t * (n : S)⁻¹ = (m : S) * t * (m : S)⁻¹ :=
      ((hψapp n ⟨t, ht⟩).symm.trans (congrArg Subtype.val h2)).trans (hψapp m ⟨t, ht⟩)
    exact Subtype.ext (hkey n m h1' h2')
  have hcardle : Nat.card ψ.range ≤ Nat.card (↥(Subgroup.zpowers s) × ↥B) :=
    Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, hord, hB9, h48] at hcardle
  norm_num at hcardle

theorem RankTwoData.of_mulEquiv {S X : Type} [Group S] [Group X] (e : S ≃* X)
    (h : RankTwoData X) : RankTwoData S where
  cubeInner := cubeInner_of_mulEquiv e h.cubeInner
  card_le E hE := by
    have := h.card_le (E.map e.toMonoidHom) (isElemAbelian_map _ hE)
    rwa [Subgroup.card_map_of_injective e.injective] at this
  exists_e9 := by
    obtain ⟨E, hE, hE9⟩ := h.exists_e9
    exact ⟨E.map e.symm.toMonoidHom, isElemAbelian_map _ hE,
      by rw [Subgroup.card_map_of_injective e.symm.injective, hE9]⟩

theorem exists_e9_of_pRank_eq_two {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card G, fun j hj => ?_⟩
    obtain ⟨F, -, -, hF⟩ := hj
    have h1 : 3 ^ j ≤ Nat.card G := hF ▸ Subgroup.card_le_card_group F
    have h2 : j < 3 ^ j := Nat.lt_pow_self (by norm_num)
    omega
  have hne : Set.Nonempty {k : ℕ | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := by
    refine ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subtype.ext (by
      have ha := Subgroup.mem_bot.mp a.2
      have hb := Subgroup.mem_bot.mp b.2
      simp [ha, hb])⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩, ?_⟩
    rw [Subgroup.card_bot, pow_zero]
  have hmem := Nat.sSup_mem hne hbdd
  have hp : sSup {k : ℕ | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} = 2 := h
  rw [hp] at hmem
  obtain ⟨E, -, hE, hE9⟩ := hmem
  exact ⟨E, hE, by rw [hE9]; norm_num⟩

theorem ru_automizer_all
    {L : Type} [Group L] (hL : Blueprint.NativeSporadic.IsSporadic L .Ru) :
    ∀ B : Subgroup L, CFSG.IsElementaryAbelian 3 B → Nat.card B = 9 →
      Nonempty (CFSG.RankThree.Asc83Table.Automizer B ≃* CFSG.RankThree.Asc83Table.GL23) := by
  obtain ⟨e⟩ := hL
  obtain ⟨-, -, h₃⟩ := CFSG.RankThree.Asc83Table.ex27_transport
    (CFSG.RankThree.Asc83Table.Ru.facts.x_cube (CFSG.SectionRank.spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    (CFSG.RankThree.Asc83Table.Ru.facts.y_cube (CFSG.SectionRank.spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    (CFSG.RankThree.Asc83Table.Ru.facts.z_x (CFSG.SectionRank.spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    (CFSG.RankThree.Asc83Table.Ru.facts.z_y (CFSG.SectionRank.spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    (CFSG.RankThree.Asc83Table.Ru.facts.z_ne (CFSG.SectionRank.spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    CFSG.RankThree.Asc83Table.Ru.factorization_card (e : L ≃* Blueprint.NativeSporadic.Ru)
  intro B _ hB9
  obtain ⟨i, ⟨f⟩⟩ := h₃ B hB9
  obtain ⟨q⟩ := CFSG.RankThree.Asc83Table.Ru.automizer_B i
  exact ⟨f.trans q⟩

theorem j4_automizer_all
    {L : Type} [Group L] (hL : Blueprint.NativeSporadic.IsSporadic L .J4) :
    ∀ B : Subgroup L, CFSG.IsElementaryAbelian 3 B → Nat.card B = 9 →
      Nonempty (CFSG.RankThree.Asc83Table.Automizer B ≃* CFSG.RankThree.Asc83Table.GL23) := by
  obtain ⟨e⟩ := hL
  obtain ⟨-, -, h₃⟩ := CFSG.RankThree.Asc83Table.ex27_transport
    (CFSG.RankThree.Asc83Table.J4.facts.x_cube (CFSG.SectionRank.spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    (CFSG.RankThree.Asc83Table.J4.facts.y_cube (CFSG.SectionRank.spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    (CFSG.RankThree.Asc83Table.J4.facts.z_x (CFSG.SectionRank.spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    (CFSG.RankThree.Asc83Table.J4.facts.z_y (CFSG.SectionRank.spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    (CFSG.RankThree.Asc83Table.J4.facts.z_ne (CFSG.SectionRank.spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    CFSG.RankThree.Asc83Table.J4.factorization_card (e : L ≃* Blueprint.NativeSporadic.J4)
  intro B _ hB9
  obtain ⟨i, ⟨f⟩⟩ := h₃ B hB9
  obtain ⟨q⟩ := CFSG.RankThree.Asc83Table.J4.automizer_B i
  exact ⟨f.trans q⟩

theorem orderChecks_of_bound {N B : ℕ} (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hsmall : ∀ q, q < B → 2 ≤ q → q ^ 3 ∣ N →
      N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∧
        N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    (∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
      (∀ q, 2 ≤ q → q ^ 3 ∣ N →
        N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) := by
  have hmono : ∀ q, B ≤ q →
      B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := fun q hq =>
    Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
  have hmono' : ∀ q : ℕ, q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    fun q => Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (by omega))
  refine ⟨fun q hq hdvd heq => ?_, fun q hq hdvd heq => ?_⟩
  · rcases Nat.lt_or_ge q B with hlt | hge
    · exact (hsmall q hlt hq hdvd).1 heq
    · have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      have h3 : N * Nat.gcd 3 (q - 1) ≤ 3 * N := by
        calc N * Nat.gcd 3 (q - 1) ≤ N * 3 := Nat.mul_le_mul le_rfl hg
          _ = 3 * N := Nat.mul_comm _ _
      have h4 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 3 * N := by rw [← heq]; exact h3
      exact lt_irrefl _ (lt_of_lt_of_le hB ((hmono q hge).trans h4))
  · rcases Nat.lt_or_ge q B with hlt | hge
    · exact (hsmall q hlt hq hdvd).2 heq
    · have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      have h3 : N * Nat.gcd 3 (q + 1) ≤ 3 * N := by
        calc N * Nat.gcd 3 (q + 1) ≤ N * 3 := Nat.mul_le_mul le_rfl hg
          _ = 3 * N := Nat.mul_comm _ _
      have h4 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ≤ 3 * N := by rw [← heq]; exact h3
      exact lt_irrefl _ (lt_of_lt_of_le hB ((hmono q hge).trans ((hmono' q).trans h4)))

theorem ru_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 145926144000 →
      145926144000 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 145926144000 →
      145926144000 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 30) (by norm_num) (by decide +kernel)

theorem j4_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 86775571046077562880 →
      86775571046077562880 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 86775571046077562880 →
      86775571046077562880 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 360) (by norm_num) (by decide +kernel)

section Rows

theorem rankTwo_spor_ru
    : RankTwoData (Spor .Ru) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .Ru ≃* Spor .Ru := b
  have hcard : Nat.card (Spor .Ru) = 145926144000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Ru.card_Ru]
  have : Finite (Spor .Ru) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank : CFSG.pRank 3 (Spor .Ru) = 2 :=
    (CFSG.RankThree.Asc83Table.Ru.table (L := Spor .Ru) ⟨b'.symm⟩).2.1
  refine ⟨cubeInner_of_not_three_dvd_card_outer (spor_ru).1, fun E hE => ?_, ?_⟩
  · have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (Spor .Ru)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .Ru)]
      exact hrank.le
    exact (card_le_of_pRank_le h2 hE).trans (by norm_num)
  · exact exists_e9_of_pRank_eq_two ((CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .Ru)).symm.trans
      hrank)

theorem rankTwo_spor_j4
    : RankTwoData (Spor .J4) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (Spor .J4) = 86775571046077562880 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.J4.card_J4]
  have : Finite (Spor .J4) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank : CFSG.pRank 3 (Spor .J4) = 2 :=
    (CFSG.RankThree.Asc83Table.J4.table (L := Spor .J4) ⟨b'.symm⟩).2.1
  refine ⟨cubeInner_of_not_three_dvd_card_outer (spor_j4).1, fun E hE => ?_, ?_⟩
  · have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (Spor .J4)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .J4)]
      exact hrank.le
    exact (card_le_of_pRank_le h2 hE).trans (by norm_num)
  · exact exists_e9_of_pRank_eq_two ((CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .J4)).symm.trans
      hrank)

theorem e9Move_of_ru
    {S : Type} [Group S] [Finite S]
    (hS : Blueprint.NativeSporadic.IsSporadic S .Ru) : E9Move S := by
  intro E hE hE9 s hs hs1
  exact exists_move_of_automizer hE hE9
    (ru_automizer_all hS E (isElementaryAbelian_of_isElemAbelian hE) hE9) hs hs1

theorem e9Move_of_j4
    {S : Type} [Group S] [Finite S]
    (hS : Blueprint.NativeSporadic.IsSporadic S .J4) : E9Move S := by
  intro E hE hE9 s hs hs1
  exact exists_move_of_automizer hE hE9
    (j4_automizer_all hS E (isElementaryAbelian_of_isElemAbelian hE) hE9) hs hs1

theorem rowOf425_ru
    : RowOf425 (Spor .Ru) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .Ru ≃* Spor .Ru := b
  have hcard : Nat.card (Spor .Ru) = 145926144000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Ru.card_Ru]
  have hScard : Nat.card S = 145926144000 := (Nat.card_congr e.toEquiv).trans hcard
  refine row425_of_e9Move ?_ (RankTwoData.of_mulEquiv e rankTwo_spor_ru)
    (e9Move_of_ru ⟨e.trans b'.symm⟩)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hScard)
    ru_orderChecks.1 ru_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem rowOf425_j4
    : RowOf425 (Spor .J4) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (Spor .J4) = 86775571046077562880 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.J4.card_J4]
  have hScard : Nat.card S = 86775571046077562880 := (Nat.card_congr e.toEquiv).trans hcard
  refine row425_of_e9Move ?_ (RankTwoData.of_mulEquiv e rankTwo_spor_j4)
    (e9Move_of_j4 ⟨e.trans b'.symm⟩)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hScard)
    j4_orderChecks.1 j4_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
