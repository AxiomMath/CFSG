module

public import CFSG.RankThree.PartOne.FIVES.Transport
public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.RankThree.PartOne.S12.ReflectionFacts
public import CFSG.RankThree.PartOne.S13K.ThetaFixed
public import CFSG.RankThree.PartOne.S15K.SL2Model
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne.FIVES

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open scoped commutatorElement

@[expose] def PairEx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∃ f : ℕ, 2 ≤ f ∧ (∀ t ∈ reflectionSet p E, KFAt p E f t) ∧
      ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → KFPair p E f s t

theorem exists_involution_of_dvd {G : Type} [Group G] [Finite G] {k : G} (h : 2 ∣ orderOf k) :
    ∃ z ∈ Subgroup.zpowers k, z ≠ 1 ∧ z * z = 1 := by
  obtain ⟨m, hm⟩ := h
  have hpos : 0 < orderOf k := orderOf_pos k
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  refine ⟨k ^ m, Subgroup.pow_mem _ (Subgroup.mem_zpowers k) m,
    pow_ne_one_of_lt_orderOf hm0 (by omega), ?_⟩
  rw [← pow_add, ← two_mul, ← hm]
  exact pow_orderOf_eq_one k

theorem simple_perfect_of_model {K : Type} [Group K] {f : ℕ} (hK : StatedClassicalModel K .PSL 2 2 f) :
    IsSimpleGroup K ∧ Group.IsPerfect K := by
  have hq := S15K.isQuasisimple_of_model hK
  have hc := S15K.center_eq_bot_of_model hK
  refine ⟨?_, hq.1⟩
  have e : K ≃* K ⧸ Subgroup.center K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot |>.symm
  have := hq.2.1
  exact e.isSimpleGroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem exists_fixed_not_fixed (h : Sec12Hyp G p A c L E) {t s : MulAut E}
    (ht : t ∈ reflectionSet p E) (hs : s ∈ reflectionSet p E) (hord : orderOf (t * s) = 3) :
    ∃ e ∈ autFixedInG E t, e ∉ autFixedInG E s := by
  have hp := h.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  have hd : RefFacts.ElemData p E := RefFacts.ElemData.of_isElementaryAbelian hp (by omega) h.E_elem
  by_contra hcon
  push Not at hcon
  have hle : autFixed E t ≤ autFixed E s := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcon (x : G) ⟨x, hx, rfl⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have h1 : (autFixed E t).relIndex ⊤ = p := by
    have := RefFacts.relIndex_inf_fixed hd ht.1 (B := ⊤) le_top
    rwa [top_inf_eq] at this
  have h2 : (autFixed E s).relIndex ⊤ = p := by
    have := RefFacts.relIndex_inf_fixed hd hs.1 (B := ⊤) le_top
    rwa [top_inf_eq] at this
  rw [Subgroup.relIndex_top_right] at h1 h2
  have heq : autFixed E t = autFixed E s := by
    have h3 := Subgroup.relIndex_mul_index hle
    rw [h1, h2] at h3
    have h4 : (autFixed E t).relIndex (autFixed E s) = 1 := by
      have hpos : 0 < p := hp.pos
      exact Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact h3)
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h4)
  have hpow := RefFacts.pow_prime_fixes_of_same_fixed hd ht.1 hs.1 (B := ⊤) le_top le_top
    (by rw [top_inf_eq, top_inf_eq]; exact heq)
  have hp1 : (t * s) ^ p = 1 := MulEquiv.ext fun b => hpow b (Subgroup.mem_top b)
  have h5 := orderOf_dvd_of_pow_eq_one hp1
  rw [hord] at h5
  have h6 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h5
  omega

theorem E_le_normalizer_sup (h : Sec12Hyp G p A c L E) (t s : MulAut E) :
    E ≤ Subgroup.normalizer ((kZero p E t ⊔ kZero p E s : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨S13K.E_le_normalizer_kZero h.E_elem t hg, S13K.E_le_normalizer_kZero h.E_elem s hg⟩

theorem kf158FiveS_of_pair (hPair : PairEx) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
      ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, orderOf (t * s) = 3 →
        ∃ S : Subgroup G, S ≤ kZero p E t ⊔ kZero p E s ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
          autFixedInG E t ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, autFixedInG E t⁆ := by
  intro G _ _ p A c L E h15 hF hout t ht s hs hord
  have h := h15.h12
  have hp := h.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  obtain ⟨f, hf2, hAt, hPairs⟩ := hPair G p A c L E h15 hF hout
  have hne : t ≠ s := by
    rintro rfl
    rw [RefFacts.mul_self_eq_one ht.1, orderOf_one] at hord
    omega
  obtain ⟨-, hmodelt, hcentt, -, kt, hkt, hktK, hktt⟩ := hAt t ht
  obtain ⟨-, hmodels, hcents, -⟩ := hAt s hs
  have hU : CentrallyUThree f ↥(kZero p E t ⊔ kZero p E s) := (hPairs t ht s hs hne).2 hord
  obtain ⟨hKs, hKp⟩ := simple_perfect_of_model hmodelt
  obtain ⟨-, hK'p⟩ := simple_perfect_of_model hmodels
  have hordt : orderOf t = 2 := ht.1.1
  have hdvd : 2 ∣ orderOf kt := by
    have h1 := orderOf_map_dvd (E.normalizerMonoidHom) (⟨kt, hkt⟩ : ↥(Subgroup.normalizer (E : Set G)))
    rw [hktt, hordt] at h1
    have h2 : orderOf (⟨kt, hkt⟩ : ↥(Subgroup.normalizer (E : Set G))) = orderOf kt :=
      Subgroup.orderOf_mk _ _
    rwa [h2] at h1
  obtain ⟨z, hzmem, hz1, hz2⟩ := exists_involution_of_dvd hdvd
  have hzK : z ∈ kZero p E t := (Subgroup.zpowers_le.mpr hktK) hzmem
  have hAE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hAcentK : ∀ a ∈ autFixedInG E t, ∀ k ∈ kZero p E t, a * k * a⁻¹ = k := by
    intro a ha k hk
    have : a ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) := by rw [hcentt]; exact ha
    have h1 := (Subgroup.mem_centralizer_iff.mp this.2) k hk
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  obtain ⟨e, he, hes⟩ := exists_fixed_not_fixed h ht hs hord
  have hAnotK' : ∃ a ∈ autFixedInG E t, ∃ y ∈ kZero p E s, a * y * a⁻¹ ≠ y := by
    refine ⟨e, he, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hes
    rw [← hcents]
    refine ⟨hAE he, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have := hcon y hy
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  obtain ⟨U, hUJ, hU2, hUn, a₀, ha₀, u₀, hu₀, hmove⟩ :=
    exists_invariant_two_subgroup_of_subgroups hf2 le_sup_left le_sup_right hU hKs hKp hK'p hzK hz1
      hz2 (fun a ha => E_le_normalizer_sup h t s (hAE ha)) hAcentK hAnotK'
  have hApg : IsPGroup p ↥(autFixedInG E t) := S13K.isPGroup_of_le_elementaryAbelian h.E_elem hAE
  have hSU : ⁅U, autFixedInG E t⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hUn
  refine ⟨⁅U, autFixedInG E t⁆, hSU.trans hUJ, ?_, hU2.to_le hSU, ?_, ?_⟩
  · intro hbot
    apply hmove
    have hcomm : ⁅u₀, a₀⁆ ∈ ⁅U, autFixedInG E t⁆ := Subgroup.commutator_mem_commutator hu₀ ha₀
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hcomm
    have h1 : u₀ * a₀ * u₀⁻¹ = a₀ := mul_inv_eq_one.mp hcomm
    have h2 : u₀ * a₀ = a₀ * u₀ := mul_inv_eq_iff_eq_mul.mp h1
    exact mul_inv_eq_iff_eq_mul.mpr h2.symm
  · exact Subgroup.normalizer_commutator_ge_right U (autFixedInG E t)
  · obtain ⟨n, hn⟩ := hU2.exists_card_eq
    have hcop : ¬ p ∣ Nat.card U := by
      rw [hn]
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
      omega
    exact (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp
      (autFixedInG E t) U hApg hcop hUn).symm

end CFSG.RankThree.PartOne.FIVES
