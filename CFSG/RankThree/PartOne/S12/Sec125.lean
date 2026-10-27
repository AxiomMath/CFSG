module

public import CFSG.RankThree.PartOne.S12.Sec125Moved
public import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.RankThree.PartOne.S12.Skeleton
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Torsion37
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace Sec125

variable {G : Type} [Group G] [Finite G]

theorem pow_three_le_card_E {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) : p ^ 3 ≤ Nat.card E :=
  Nat.le_of_dvd Nat.card_pos h.pow_three_dvd_card_E

theorem not_pow_three_le {p n : ℕ} (hp : p.Prime) (hn : n ≤ p * p) : ¬ p ^ 3 ≤ n := by
  intro h
  have h2 := hp.two_le
  nlinarith [Nat.mul_pos hp.pos hp.pos]

omit [Finite G] in
theorem zpowers_comm {a b : G} (hab : a * b = b * a) :
    ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers b, u * v = v * u := by
  intro u hu v hv
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  exact ((show Commute a b from hab).zpow_zpow i j).eq

theorem mem_sectionTenTwo (h124 : Node124) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hW : torusNormalizer E ≤ cNormalizer c) {K : Subgroup G}
    (hKzs : K ∈ sectionTenZeroStar p A) (hK0 : K ≠ ⊥) (hKc : ⁅K, Subgroup.zpowers c⁆ = K) :
    K ∈ sectionTenTwo p A := by
  by_contra hK2
  have hKF : K ∈ thetaComponentFamily p A := hKzs.1.1
  have hK1 : K ∈ sectionTenOne p A := by
    by_contra hK1
    exact hK2 ⟨hKF, hK1⟩
  obtain ⟨a₀, ha₀A, ha₀1, hKa₀⟩ := mem_thetaComponentFamily_iff.mp hKF
  have hK' : Sec12Hyp G p A a₀ K E :=
    ⟨h.setup, ha₀A, ha₀1, ⟨⟨hKzs, hK1⟩, hKa₀⟩, h.E_elem, h.E_le, h.E_max⟩
  obtain ⟨hinv, hdecomp⟩ := h124 G p A a₀ K E hK'
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcord : orderOf c = p := Sec12Three.orderOf_c h
  have ha₀ord : orderOf a₀ = p :=
    orderOf_eq_prime (Sec12Three.pow_eq_one_of_mem_A h ha₀A) ha₀1
  have hle : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.2 (h.A_le_E h.c_mem)
  have hinvc : torusInvariant E K (Subgroup.zpowers c) := fun w hw b hb =>
    (Subgroup.mem_normalizer_iff.mp (hW (Subgroup.mem_inf.mp hw).2) b).mp hb
  have hne : Subgroup.zpowers c ≠ ⊥ := fun hb => h.c_ne_one (Subgroup.zpowers_eq_bot.1 hb)
  have hneE : Subgroup.zpowers c ≠ E := by
    intro hE
    have h3 := pow_three_le_card_E h
    rw [← hE, Nat.card_zpowers, hcord] at h3
    exact not_pow_three_le hp (Nat.le_mul_self p) h3
  rcases hinv (Subgroup.zpowers c) hle hinvc hne hneE with h1 | h1
  · have hzeq : thetaComponentsAt p a₀ = thetaComponentsAt p c :=
      thetaComponentsAt_eq_of_zpowers_eq p h1.symm
    have hKC : K ≤ Subgroup.centralizer ({c} : Set G) :=
      (mem_thetaComponentsAt_iff.mp (hzeq ▸ hKa₀)).1
    have hcomm : ⁅K, Subgroup.zpowers c⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro k hk z hz
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hkc : k * c = c * k := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
      rw [Subgroup.mem_bot]
      exact Commute.commutator_eq (Commute.zpow_right (show Commute k c from hkc) i)
    exact hK0 (hKc.symm.trans hcomm)
  · rcases hdecomp with ⟨hEsup, hdisj⟩ | ⟨-, hEeq⟩
    · rw [← h1] at hEsup hdisj
      have hcard : Nat.card E =
          Nat.card (Subgroup.zpowers a₀) * Nat.card (Subgroup.zpowers c) := by
        have := card_sup_of_commute_disjoint (zpowers_comm
          (Sec12Three.mul_comm_of_mem_A h ha₀A h.c_mem)) (disjoint_iff.mpr hdisj)
        rwa [← hEsup] at this
      rw [Nat.card_zpowers, Nat.card_zpowers, ha₀ord, hcord] at hcard
      exact not_pow_three_le hp hcard.le (pow_three_le_card_E h)
    · exact hneE (h1.trans hEeq)

omit [Finite G] in
theorem autMoved_one (F : Subgroup G) : autMoved F (1 : MulAut F) = ⊥ := by
  unfold autMoved
  rw [eq_bot_iff, Subgroup.closure_le]
  rintro _ ⟨f, rfl⟩
  simp

omit [Finite G] in
theorem pow_eq_one_of_isAutTransvection {p : ℕ} {E : Subgroup G} (hE : IsElementaryAbelian p E)
    {φ : MulAut E} (hφ : IsAutTransvection p E φ) : φ ^ p = 1 := by
  refine MulEquiv.ext fun e => ?_
  obtain ⟨n, hn⟩ : ∃ n : E, n = φ e * e⁻¹ := ⟨_, rfl⟩
  have hnfix : φ n = n := hφ.2.2 (hn ▸ Subgroup.subset_closure ⟨e, rfl⟩)
  have hφe : φ e = n * e := by simp [hn]
  have hpow : ∀ k : ℕ, (φ ^ k) e = n ^ k * e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hnfix, hφe, pow_succ, mul_assoc]
  have hnp : n ^ p = 1 := by
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (n : G) n.2
    exact Subtype.ext (by simpa using h1)
  rw [hpow p, hnp, one_mul]
  rfl

theorem exists_pElement_transvection {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) {y₀ : G} (hy₀ : y₀ ∈ Subgroup.normalizer (E : Set G))
    (hφ : IsAutTransvection p E (E.normalizerMonoidHom ⟨y₀, hy₀⟩)) :
    ∃ n : ℕ, (∃ k : ℕ, orderOf (y₀ ^ n) = p ^ k) ∧
      ∃ hy : y₀ ^ n ∈ Subgroup.normalizer (E : Set G),
        E.normalizerMonoidHom ⟨y₀ ^ n, hy⟩ = E.normalizerMonoidHom ⟨y₀, hy₀⟩ := by
  have hφp := pow_eq_one_of_isAutTransvection hE hφ
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₀).ne' p hp.ne_one
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm hp.one_lt
  have hy : y₀ ^ (m * j) ∈ Subgroup.normalizer (E : Set G) := Subgroup.pow_mem _ hy₀ _
  refine ⟨m * j, ?_, hy, ?_⟩
  · have hpow : (y₀ ^ (m * j)) ^ (p ^ a) = 1 := by
      rw [← pow_mul, show m * j * p ^ a = orderOf y₀ * j by rw [hN]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hpow)
    exact ⟨k, hk⟩
  · have h1 : (⟨y₀ ^ (m * j), hy⟩ : Subgroup.normalizer (E : Set G)) = ⟨y₀, hy₀⟩ ^ (m * j) :=
      Subtype.ext (by simp)
    rw [h1, map_pow]
    have h2 : m * j = p * (m * j / p) + 1 := by
      have := Nat.div_add_mod (m * j) p
      omega
    rw [h2, pow_add, pow_mul, hφp, one_pow, one_mul, pow_one]

theorem commute_of_transvection {p : ℕ} (hp : p.Prime) {E : Subgroup G} {c y : G}
    (hcE : c ∈ E) (hc : orderOf c = p) (hyE : y ∈ Subgroup.normalizer (E : Set G))
    (hyc : y ∈ cNormalizer c)
    (hφ : IsAutTransvection p E (E.normalizerMonoidHom ⟨y, hyE⟩)) : y * c = c * y := by
  set φ := E.normalizerMonoidHom ⟨y, hyE⟩ with hφdef
  obtain ⟨n, hn⟩ : ∃ n : E, n = φ ⟨c, hcE⟩ * (⟨c, hcE⟩ : E)⁻¹ := ⟨_, rfl⟩
  have hfix : φ n = n := hφ.2.2 (hn ▸ Subgroup.subset_closure ⟨⟨c, hcE⟩, rfl⟩)
  have hnG : (n : G) = y * c * y⁻¹ * c⁻¹ := by rw [hn]; rfl
  have hnz : (n : G) ∈ Subgroup.zpowers c := by
    rw [hnG]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hyc c).mp (Subgroup.mem_zpowers c))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
  have hyn : y * (n : G) * y⁻¹ = n := congrArg Subtype.val hfix
  by_cases hn1 : (n : G) = 1
  · rw [hnG] at hn1
    have h1 : y * c * y⁻¹ = c := mul_inv_eq_one.1 hn1
    calc y * c = y * c * y⁻¹ * y := by group
      _ = c * y := by rw [h1]
  · exfalso
    have hz : Subgroup.zpowers (n : G) = Subgroup.zpowers c :=
      zpowers_eq_of_mem_of_ne_one hp hc hnz hn1
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      (hz ▸ Subgroup.mem_zpowers c : c ∈ Subgroup.zpowers (n : G))
    have h2 : y * c * y⁻¹ = c := by
      rw [← hi, ← _root_.conj_zpow, hyn]
    apply hn1
    rw [hnG, h2]
    simp

omit [Finite G] in
theorem isAutTransvection_restrict {p : ℕ} (hp : p.Prime) {c y : G} {L E F : Subgroup G}
    (R : Sec12Three.Restr c L E F) (hyc : y * c = c * y)
    (hyE : y ∈ Subgroup.normalizer (E : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G))
    (hφ : IsAutTransvection p E (E.normalizerMonoidHom ⟨y, hyE⟩)) :
    IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hyF⟩) := by
  obtain ⟨-, hcard, hfix⟩ := hφ
  have hmoved := R.autMovedInG_eq hyc hyE hyF
  have hcardF : Nat.card (autMoved F (F.normalizerMonoidHom ⟨y, hyF⟩)) = p := by
    rw [← Sec12Three.natCard_autMovedInG, ← hmoved, Sec12Three.natCard_autMovedInG, hcard]
  refine ⟨fun h1 => ?_, hcardF, fun f hf => ?_⟩
  · rw [h1, autMoved_one] at hcardF
    exact hp.one_lt.ne (by simpa using hcardF)
  · have hfG : (f : G) ∈ autMovedInG E (E.normalizerMonoidHom ⟨y, hyE⟩) := by
      rw [hmoved]
      exact Subgroup.mem_map.2 ⟨f, hf, rfl⟩
    obtain ⟨e, he, hef⟩ := Subgroup.mem_map.1 hfG
    have h1 : (E.normalizerMonoidHom ⟨y, hyE⟩) e = e := hfix he
    have h2 : y * (e : G) * y⁻¹ = e := congrArg Subtype.val h1
    show F.normalizerMonoidHom ⟨y, hyF⟩ f = f
    apply Subtype.ext
    show y * (f : G) * y⁻¹ = f
    rw [← hef]
    exact h2

end Sec125

theorem Sec12Hyp.pElement_normalizes_thetaComponentsAt {G : Type} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hnorm : SelectedPrimeElementsNormalizeThetaComponents) {y : G} (hyc : y * c = c * y)
    (hord : ∃ k : ℕ, orderOf y = p ^ k) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p c) :
    y ∈ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsAt_iff.mp hY
  have hyC : y ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyc
  have hH : evenRank (Subgroup.centralizer ({c} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  have hord' : ∃ k : ℕ, orderOf (⟨y, hyC⟩ : Subgroup.centralizer ({c} : Set G)) = p ^ k := by
    obtain ⟨k, hk⟩ := hord
    exact ⟨k, by rw [← hk, ← Subgroup.orderOf_coe]⟩
  have hmem := hnorm.1 (Subgroup.centralizer ({c} : Set G)) hH p h.prime h.three_lt _ hord' _ hY'
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ Subgroup.centralizer ({c} : Set G)
  · have := Subgroup.mem_normalizer_iff.mp hmem ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgY
      exact absurd (hYC hgY) hg
    · intro hygY
      have h1 : y * g * y⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := hYC hygY
      refine absurd ?_ hg
      have h2 := mul_mem (mul_mem (inv_mem hyC) h1) hyC
      simpa [mul_assoc] using h2

theorem node125_of_inputs (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h81 : SelectedPrimeElementsNormalizeThetaComponents)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple)
    (h107 : InSec10Seven) (h109 : InSec10Nine)
    (hTrans : SectionTenComponentSupplementTransitivity)
    (hSupp : SectionTenTrivialActorComponentSupplement)
    (hUp : SectionTenMovingTwoStratumUpwardClosure) (h105 : InSec10FivePlus)
    (h122 : Node122) (h124 : Node124) (h128 : Node128) (hNT : KF123NoTransvection) :
    Node125 := by
  intro G _ _ p A c L E h hW
  have hp := h.prime
  obtain ⟨K, hKzs, hK0, hKc⟩ :=
    Sec125.exists_moved_component hSchreier hTwoAction h81 h106 hTrans hSupp hUp h105 h
  have hK2 := Sec125.mem_sectionTenTwo h124 h hW hKzs hK0 hKc
  obtain ⟨φ, hφW, hφ⟩ := h128 G p A c L E h ⟨K, hKzs, hK2⟩
  obtain ⟨⟨y₀, hy₀⟩, rfl⟩ := MonoidHom.mem_range.mp hφW
  have hcord : orderOf c = p := Sec12Three.orderOf_c h
  have hy₀c : y₀ * c = c * y₀ :=
    Sec125.commute_of_transvection hp (h.A_le_E h.c_mem) hcord hy₀ (hW hy₀) hφ
  obtain ⟨n, hyord, hyE, hyφ⟩ := Sec125.exists_pElement_transvection hp h.E_elem hy₀ hφ
  have hyc : y₀ ^ n * c = c * y₀ ^ n := (Commute.pow_left (show Commute y₀ c from hy₀c) n).eq
  have hyL : y₀ ^ n ∈ Subgroup.normalizer (L : Set G) :=
    h.pElement_normalizes_thetaComponentsAt h81 hyc hyord h.L_mem.2
  have hφy : IsAutTransvection p E (E.normalizerMonoidHom ⟨y₀ ^ n, hyE⟩) := hyφ ▸ hφ
  rcases Sec12Hyp.table123_hyp h107 h109 h122 h with ⟨hG, hgen⟩ | ⟨-, hsu⟩
  · have hyF : y₀ ^ n ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
      Sec12Three.mem_normalizer_inf hyL hyE
    exact hNT G p L (A ⊓ L) (E ⊓ L) (Or.inl hgen) (y₀ ^ n) hyL hyF
      (Sec125.isAutTransvection_restrict hp (h.restr_of_generic hG) hyc hyE hyF hφy)
  · exact hNT G p L A E (Or.inr hsu) (y₀ ^ n) hyL hyE hφy

end CFSG.RankThree.PartOne
