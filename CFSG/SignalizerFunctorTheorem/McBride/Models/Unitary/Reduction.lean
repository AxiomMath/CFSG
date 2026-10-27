module

public import CFSG.GroupTheory.PCore.Defs
import CFSG.CharacterTheory.Wreathed.OriginalStationarityCoverageCriterion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

variable {G : Type*} [Group G]

theorem orderOf_conj_eq (g t : G) : orderOf (g * t * g⁻¹) = orderOf t := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t
  simpa [MulAut.conj_apply] using this

theorem exists_conj_eq_of_mul_mem {K : Subgroup G} (hK : Odd (Nat.card K)) {t u : G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (huk : u * t ∈ K) :
    ∃ m ∈ K, u = m * t * m⁻¹ := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have hinv : ∀ {v : G}, orderOf v = 2 → v⁻¹ = v := fun {v} hv => by
    have hv2 : v * v = 1 := by rw [← pow_two, ← hv]; exact pow_orderOf_eq_one v
    exact inv_eq_of_mul_eq_one_right hv2
  have ht' : t⁻¹ = t := hinv ht
  have hu' : u⁻¹ = u := hinv hu
  obtain ⟨a, ha⟩ : Odd (orderOf (u * t)) :=
    hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K huk)
  set k := u * t with hk
  set m := k ^ (a + 1) with hm
  have hmK : m ∈ K := K.pow_mem huk _
  have hmm : m * m = k := by
    rw [hm, ← pow_add]
    have : a + 1 + (a + 1) = orderOf k + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have htkt : t * k * t⁻¹ = k⁻¹ := by
    rw [hk, mul_inv_rev, ht', hu']
    calc t * (u * t) * t = (t * u) * (t * t) := by group
      _ = t * u := by rw [ht2, mul_one]
  have htmt : t * m * t⁻¹ = m⁻¹ := by
    rw [hm, ← conj_pow, htkt, inv_pow]
  refine ⟨m, hmK, ?_⟩
  calc u = k * t := by rw [hk, mul_assoc, ht2, mul_one]
    _ = (m * m) * t := by rw [hmm]
    _ = m * (t * m * t⁻¹)⁻¹ * t := by rw [htmt, inv_inv]
    _ = m * t * m⁻¹ := by group

variable [Finite G]

theorem exists_involution_mul_centralizer (heven : 2 ∣ Nat.card G)
    (hS : ∀ S : Sylow 2 G, IsCyclic S ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup G) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∃ t : G, orderOf t = 2 ∧
      ∀ g : G, ∃ m ∈ CFSG.oddCore G, ∃ c : G, c * t = t * c ∧ g = m * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (S : Subgroup G)) 2
    (S.dvd_card_of_dvd_card heven)
  have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  refine ⟨t, ht2, fun g => ?_⟩
  rcases hS S with hcyc | ⟨r, hr, hquat⟩
  · have hfact :=
      CFSG.Wreathed.OriginalStationarityCoverageCriterion.cyclic_Sylow_two_oddCore_factorization
        S hcyc
    have hg : g ∈ CFSG.oddCore G ⊔ (S : Subgroup G) := by
      rw [hfact]
      exact Subgroup.mem_top g
    obtain ⟨m, hm, s, hs, hms⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨m, hm, s, ?_, hms.symm⟩
    exact congrArg Subtype.val ((IsCyclic.isMulCommutative (α := S)).is_comm.comm
      ⟨s, hs⟩ ⟨t, t.2⟩)
  · have hcentral := CFSG.BrauerSuzuki.brauer_suzuki r hr S hquat (t : G) t.2 ht2
    have hKodd : Odd (Nat.card (CFSG.oddCore G)) := CFSG.ComponentClassification.OddCore.odd_card G
    have hu : orderOf (g * (t : G) * g⁻¹) = 2 := by rw [orderOf_conj_eq, ht2]
    have hmk : ((g * (t : G) * g⁻¹ : G) : G ⧸ CFSG.oddCore G) = ((t : G) : G ⧸ CFSG.oddCore G) := by
      have := Subgroup.mem_center_iff.mp hcentral (g : G ⧸ CFSG.oddCore G)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have huk : (g * (t : G) * g⁻¹) * (t : G) ∈ CFSG.oddCore G := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hmk, ← QuotientGroup.mk_mul]
      have : (t : G) * (t : G) = 1 := by
        have h1 := pow_orderOf_eq_one (t : G)
        rwa [ht2, pow_two] at h1
      rw [this, QuotientGroup.mk_one]
    obtain ⟨m, hm, hum⟩ := exists_conj_eq_of_mul_mem hKodd ht2 hu huk
    refine ⟨m, hm, m⁻¹ * g, ?_, by group⟩
    have h1 : g * (t : G) * g⁻¹ = m * (t : G) * m⁻¹ := hum
    calc m⁻¹ * g * (t : G) = m⁻¹ * (g * (t : G) * g⁻¹) * g := by group
      _ = m⁻¹ * (m * (t : G) * m⁻¹) * g := by rw [h1]
      _ = (t : G) * (m⁻¹ * g) := by group


theorem eq_one_of_dvd_nine {n : ℕ} (h9 : n ∣ 9) (h3 : ¬ 3 ∣ n) : n = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show n ∣ 3 ^ 2 by simpa using h9)
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simpa using hi
  · exact absurd (hi ▸ dvd_pow_self 3 hpos.ne') h3

theorem eq_top_of_sylow_two_cyclic_or_quaternion (C : Subgroup G) (P : Sylow 3 G)
    (hC : Nat.card C = 72) (hPC : (P : Subgroup G) ≤ C) (hP : Nat.card P = 9)
    (hNP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ C)
    (hA : ∀ x t : G, orderOf t = 2 → x * t = t * x → ¬ 3 ∣ orderOf x)
    (hN : ∀ N : Subgroup G, N ≠ ⊥ → Nat.Coprime (Nat.card N) 6 →
      ¬ C ≤ Subgroup.normalizer (N : Set G))
    (hS : ∀ S : Sylow 2 G, IsCyclic S ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup G) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    C = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have heven : 2 ∣ Nat.card G :=
    (show 2 ∣ 72 by norm_num).trans (hC ▸ Subgroup.card_subgroup_dvd_card C)
  obtain ⟨t, ht, hdecomp⟩ := exists_involution_mul_centralizer heven hS
  set K := CFSG.oddCore G with hK
  have hKodd : Odd (Nat.card K) := CFSG.ComponentClassification.OddCore.odd_card G
  have hPK : (P : Subgroup G) ≤ K := by
    intro x hx
    obtain ⟨m, hm, c, hc, rfl⟩ := hdecomp x
    have hdvdP : orderOf (m * c) ∣ 9 := hP ▸ Subgroup.orderOf_dvd_natCard _ hx
    let q := QuotientGroup.mk' K
    have hqm : q m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    have hq : q (m * c) = q c := by rw [map_mul, hqm, one_mul]
    have h1 : orderOf (q c) ∣ 9 := by
      rw [← hq]
      exact (orderOf_map_dvd q _).trans hdvdP
    have h3 : ¬ 3 ∣ orderOf (q c) := fun h3 =>
      hA c t ht hc (h3.trans (orderOf_map_dvd q c))
    have hqc : q c = 1 := orderOf_eq_one_iff.mp (eq_one_of_dvd_nine h1 h3)
    exact (QuotientGroup.eq_one_iff _).mp (hq.trans hqc)
  have hfr : Subgroup.normalizer ((P : Subgroup G) : Set G) ⊔ K = ⊤ :=
    Sylow.normalizer_sup_eq_top' P hPK
  have hGCK : ∀ g : G, ∃ n ∈ C, ∃ k ∈ K, g = n * k := by
    intro g
    have hg : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ⊔ K := by
      rw [hfr]
      exact Subgroup.mem_top g
    obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    exact ⟨n, hNP hn, k, hk, hnk.symm⟩
  have hKC : (K ⊓ C : Subgroup G) = P := by
    have hle : (P : Subgroup G) ≤ K ⊓ C := le_inf hPK hPC
    have hodd : Odd (Nat.card ↥(K ⊓ C)) :=
      hKodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hdvd72 : Nat.card ↥(K ⊓ C) ∣ 72 := hC ▸ Subgroup.card_dvd_of_le inf_le_right
    have h9 : 9 ∣ Nat.card ↥(K ⊓ C) := hP ▸ Subgroup.card_dvd_of_le hle
    have hcard : Nat.card ↥(K ⊓ C) = 9 := by
      have hmem : Nat.card ↥(K ⊓ C) ∈ Nat.divisors 72 :=
        Nat.mem_divisors.mpr ⟨hdvd72, by norm_num⟩
      have h72 : Nat.divisors 72 = {1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72} := by decide
      rw [h72] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      obtain ⟨j, hj⟩ := hodd
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hP])).symm
  let Pk : Sylow 3 K := P.subtype hPK
  have hPkcard : Nat.card Pk = 9 := by
    have : Nat.card ((P : Subgroup G).subgroupOf K) = Nat.card (P : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
    exact this.trans hP
  have hPkcomm : IsMulCommutative (Pk : Subgroup K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hPkcard]; norm_num)
  have hnorm : Subgroup.normalizer ((Pk : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((Pk : Subgroup K) : Set K) := by
    intro y hy
    have hy' : y ∈ (Subgroup.normalizer ((P : Subgroup G) : Set G)).subgroupOf K := by
      rw [Subgroup.subgroupOf_normalizer_eq hPK]
      exact hy
    have hyKC : (y : G) ∈ K ⊓ C := ⟨y.2, hNP hy'⟩
    rw [hKC] at hyKC
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (hPkcomm.is_comm.comm ⟨z, hz⟩ ⟨y, hyKC⟩)
  have hcompl := MonoidHom.ker_transferSylow_isComplement' Pk hnorm
  set τ := MonoidHom.transferSylow Pk hnorm with hτ
  have hker3 : ¬ 3 ∣ Nat.card τ.ker := MonoidHom.not_dvd_card_ker_transferSylow Pk hnorm
  have hmulcard : Nat.card τ.ker * Nat.card Pk = Nat.card K := hcompl.card_mul_card
  set K₃ : Subgroup G := τ.ker.map K.subtype with hK₃
  have hK₃card : Nat.card K₃ = Nat.card τ.ker :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hK₃odd : Odd (Nat.card K₃) := by
    rw [hK₃card]
    exact hKodd.of_dvd_nat (Dvd.intro _ hmulcard)
  have hK₃3 : ¬ 3 ∣ Nat.card K₃ := by
    rw [hK₃card]
    exact hker3
  have hcop : Nat.Coprime (Nat.card K₃) 6 := by
    have h2 : Nat.Coprime (Nat.card K₃) 2 := Nat.coprime_two_right.mpr hK₃odd
    have h3 : Nat.Coprime (Nat.card K₃) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK₃3).symm
    simpa using Nat.Coprime.mul_right h2 h3
  have hK₃char : ∀ y : G, y ∈ K → ¬ 3 ∣ orderOf y → y ∈ K₃ := by
    intro y hy h3
    set y' : K := ⟨y, hy⟩ with hy'
    have hdvd9 : orderOf (τ y') ∣ 9 := hPkcard ▸ orderOf_dvd_natCard (τ y')
    have hd : orderOf (τ y') ∣ orderOf y' := orderOf_map_dvd τ y'
    have hy'ord : orderOf y' = orderOf y := Subgroup.orderOf_mk y hy
    have h1 : orderOf (τ y') = 1 :=
      eq_one_of_dvd_nine hdvd9 (fun h => h3 (hy'ord ▸ h.trans hd))
    exact ⟨y', orderOf_eq_one_iff.mp h1, rfl⟩
  have hK₃conj : ∀ c ∈ C, ∀ x ∈ K₃, c * x * c⁻¹ ∈ K₃ := by
    intro c hc x hx
    have hxK : x ∈ K := Subgroup.map_subtype_le _ hx
    have hxdvd : orderOf x ∣ Nat.card K₃ := Subgroup.orderOf_dvd_natCard K₃ hx
    refine hK₃char _ ((inferInstance : K.Normal).conj_mem x hxK c) ?_
    rw [orderOf_conj_eq]
    exact fun h => hK₃3 (h.trans hxdvd)
  have hCnorm : C ≤ Subgroup.normalizer (K₃ : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hK₃conj c hc x hx, fun hx => ?_⟩
    have := hK₃conj c⁻¹ (C.inv_mem hc) _ hx
    simpa [mul_assoc] using this
  have hK₃bot : K₃ = ⊥ := by
    by_contra hne
    exact hN K₃ hne hcop hCnorm
  have hker1 : Nat.card τ.ker = 1 := by
    rw [← hK₃card, hK₃bot, Subgroup.card_bot]
  have hKcard9 : Nat.card K = 9 := by
    rw [← hmulcard, hker1, hPkcard]
  have hKP : (P : Subgroup G) = K :=
    Subgroup.eq_of_le_of_card_ge hPK (by rw [hKcard9, hP])
  rw [eq_top_iff]
  intro g _
  obtain ⟨n, hn, k, hk, rfl⟩ := hGCK g
  have hkP : k ∈ (P : Subgroup G) := hKP ▸ hk
  exact C.mul_mem hn (hPC hkP)

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
