module

public import CFSG.RankThree.PartTwo.Sec12.Item125Basic
public import CFSG.RankThree.PartTwo.Sec6.Item612Core
public import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1117Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_isPGroup_two_not_le_centralizer (hchar : CFSG.Assembly.IsCharTwoType G)
    {A U₀ : Subgroup G} (hU₀ : U₀ ≠ ⊥) (hU₀2 : IsPGroup 2 U₀)
    (hAU₀ : A ≤ Subgroup.normalizer (U₀ : Set G)) {d : G} (hdA : d ∈ A) (hd : orderOf d = 3) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      ¬ S ≤ Subgroup.centralizer ({d} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hU₀S, hSmax⟩ := Finite.exists_le_maximal
    (p := fun S : Subgroup G => IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G))
    ⟨hU₀2, hAU₀⟩
  refine ⟨S, hSmax.1.1, hSmax.1.2, fun hSd => ?_⟩
  have hS1 : S ≠ ⊥ := fun h => hU₀ (eq_bot_iff.mpr (h ▸ hU₀S))
  set M := Subgroup.normalizer (S : Set G) with hM
  set O := inSubgroup (CFSG.pCore 2) M with hO
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup.map _
  have hSO : S ≤ O := by
    rw [hO, ← Sec6.pCoreOf_two_eq_inSubgroup]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      hSmax.1.1
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := fun a ha =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 M)
      (Subgroup.le_normalizer (hSmax.1.2 ha))
  have hOS : O ≤ S := hSmax.2 ⟨hO2, hAO⟩ hSO
  have hch := hchar M ⟨S, hS1, hSmax.1.1, rfl⟩
  rw [Sec6.pCoreOf_two_eq_inSubgroup] at hch
  have hdC : d ∈ Subgroup.centralizer (O : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSd (hOS hy))
  have hdO : d ∈ O := hch ⟨hSmax.1.2 hdA, hdC⟩
  obtain ⟨k, hk⟩ := hO2 ⟨d, hdO⟩
  have hdk : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 := orderOf_dvd_of_pow_eq_one hdk
  rw [hd] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

omit [Finite G] in
theorem le_of_commutator_eq {Y U : Subgroup G} {d e : G} (hdY : d ∈ Y)
    (hdC : d ∈ Subgroup.centralizer ({e} : Set G)) (hd3 : d ^ 3 = 1)
    (hN : ∀ t ∈ Subgroup.centralizer ({e} : Set G), (∃ k : ℕ, t ^ 3 ^ k = 1) →
      t ∈ Subgroup.normalizer (Y : Set G))
    (hUC : U ≤ Subgroup.centralizer ({e} : Set G)) (hUd : ⁅U, Subgroup.zpowers d⁆ = U) :
    U ≤ Y := by
  have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.zpowers_le.mpr hdY).trans Subgroup.le_normalizer
  have hpow : ∀ t ∈ Subgroup.zpowers d, t ^ 3 ^ 1 = 1 := fun t ht => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have hUN : U ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← hUd, Subgroup.commutator_le]
    intro u hu t ht
    have htC : t ∈ Subgroup.centralizer ({e} : Set G) :=
      (Subgroup.zpowers_le.mpr hdC) ht
    have hconj : u * t * u⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
      refine hN _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hUC hu) htC)
        (Subgroup.inv_mem _ (hUC hu))) ⟨1, ?_⟩
      rw [conj_pow, hpow t ht, mul_one, mul_inv_cancel]
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ (hdN ht))
  rw [← hUd, Subgroup.commutator_le]
  intro u hu t ht
  have htY : t ∈ Y := (Subgroup.zpowers_le.mpr hdY) ht
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hUN hu) t).mp htY)
    (Subgroup.inv_mem _ htY)

theorem eq_one_of_mem_theta {Y : Subgroup G} {y : G}
    (hy : y ∈ inSubgroup (aschbacherSolvableCore 3) Y) {k : ℕ} (hk : y ^ 3 ^ k = 1) : y = 1 := by
  obtain ⟨t, ht, rfl⟩ := hy
  set t' : aschbacherSolvableCore 3 Y := ⟨t, ht⟩
  have hk' : t' ^ 3 ^ k = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hk
  have hdvd : orderOf t' ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf t') 3 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard t')
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        three_not_dvd_card_aschbacherSolvableCore).symm
  have h1 : orderOf t' = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd
  rw [orderOf_eq_one_iff] at h1
  have : t = 1 := congrArg Subtype.val h1
  simp [this]

theorem eq_one_of_mem_thetaQuotCentralizer {Y : Subgroup G}
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥) {y : G} (hyY : y ∈ Y)
    (hyC : y ∈ Sec4.thetaQuotCentralizer Y) {k : ℕ} (hk : y ^ 3 ^ k = 1) : y = 1 := by
  have h1 := Sec12.mk_mem_center_of_mem_thetaQuotCentralizer (x := ⟨y, hyY⟩) hyC
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact eq_one_of_mem_theta ⟨_, h1, rfl⟩ hk

theorem commute_of_mem_thetaQuotCentralizer {Y : Subgroup G} {v y : G}
    (hv : v ∈ Sec4.thetaQuotCentralizer Y) (hyY : y ∈ Y) {k : ℕ}
    (hk : (y⁻¹ * (v * y * v⁻¹)) ^ 3 ^ k = 1) : v * y = y * v := by
  have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hv).2 y hyY
  have h2 := eq_one_of_mem_theta h1 hk
  calc v * y = (y * (y⁻¹ * (v * y * v⁻¹))) * v := by group
    _ = y * v := by rw [h2, mul_one]

omit [Finite G] in
theorem mem_zpowers_of_mem_zpowers {d z : G} (hd3 : d ^ 3 = 1) (hz : z ∈ Subgroup.zpowers d)
    (hz1 : z ≠ 1) : d ∈ Subgroup.zpowers z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hd3' : d ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3]
  have hk : k % 3 ≠ 0 := by
    intro h0
    apply hz1
    rw [zpow_eq_zpow_emod _ hd3', h0, zpow_zero]
  have hkk : (k * k) % 3 = 1 := by
    have : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h | h <;> rw [Int.mul_emod, h] <;> norm_num
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← zpow_mul, zpow_eq_zpow_emod _ hd3', hkk, zpow_one]

omit [Finite G] in
theorem conj_pow_eq_mul_pow {x e δ : G} (hxe : x * e * x⁻¹ = e * δ) (hxδ : x * δ = δ * x) :
    ∀ j : ℕ, x ^ j * e * (x ^ j)⁻¹ = e * δ ^ j
  | 0 => by simp
  | j + 1 => by
    have ih := conj_pow_eq_mul_pow hxe hxδ j
    have hc : Commute x δ := hxδ
    calc x ^ (j + 1) * e * (x ^ (j + 1))⁻¹ = x * (x ^ j * e * (x ^ j)⁻¹) * x⁻¹ := by
          rw [pow_succ', mul_inv_rev]; group
      _ = x * e * x⁻¹ * (x * δ ^ j * x⁻¹) := by rw [ih]; group
      _ = e * δ * δ ^ j := by rw [hxe, (hc.pow_right j).eq, mul_inv_cancel_right]
      _ = e * δ ^ (j + 1) := by rw [pow_succ', mul_assoc]

theorem exists_inf_centralizer_not_le {S : Subgroup G} {e d x δ : G} (hde : d * e = e * d)
    (he3 : e ^ 3 = 1) (hd3 : orderOf d = 3) (hed : e ∉ Subgroup.zpowers d)
    (hxd : x * d = d * x) (hδ : δ ∈ Subgroup.zpowers d) (hδ1 : δ ≠ 1)
    (hxe : x * e * x⁻¹ = e * δ) (hS2 : IsPGroup 2 S) (hdS : d ∈ Subgroup.normalizer (S : Set G))
    (heS : e ∈ Subgroup.normalizer (S : Set G))
    (hSd : ¬ S ≤ Subgroup.centralizer ({d} : Set G)) :
    ∃ S' : Subgroup G, IsPGroup 2 S' ∧ d ∈ Subgroup.normalizer (S' : Set G) ∧
      ¬ S' ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer ({d} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hno
  push Not at hno
  apply hSd
  have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have he3o : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hxδ : x * δ = δ * x := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    exact ((Commute.zpow_right (show Commute x d from hxd) k)).eq
  have hconj := conj_pow_eq_mul_pow hxe hxδ
  have hdδ : d ∈ Subgroup.zpowers δ := mem_zpowers_of_mem_zpowers hd3' hδ hδ1
  have hδ3 : δ ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3', one_zpow]
  set B := Subgroup.zpowers d ⊔ Subgroup.zpowers e with hB
  have hdz : ∀ w ∈ Subgroup.zpowers d, w ^ 3 = 1 := fun w hw => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3', one_zpow]
  have heC : e ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (show Commute d e from hde) k)).eq
  obtain ⟨hBcard, hBc, hBe⟩ := card_sup_zpowers_of_disjoint heC inferInstance hdz he3o
    (Sec12.inf_zpowers_eq_bot_of_not_mem he3o hed)
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := ⟨hBc, hBe⟩
  have hB9 : 3 ^ 2 ≤ Nat.card B := by
    rw [hB, hBcard, Nat.card_zpowers, hd3]
    norm_num
  have hBS : B ≤ Subgroup.normalizer (S : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hdS) (Subgroup.zpowers_le.mpr heS)
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hBab hB9 hBS hcop ?_
  intro b hb hb1 y hy
  have hb' : b ∈ Subgroup.closure ({d, e} : Set G) := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
    exact hb
  obtain ⟨m, n, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hde hb'
  have hyb : y * (d ^ m * e ^ n) = (d ^ m * e ^ n) * y :=
    Subgroup.mem_centralizer_singleton_iff.mp hy.2
  have hcomm : Commute y (d ^ m * e ^ n) := hyb
  have he3' : e ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, he3]
  have hd3z : d ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3']
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hn : n % 3 = 0
  ·
    have hen : e ^ n = 1 := by rw [zpow_eq_zpow_emod _ he3', hn, zpow_zero]
    rw [hen, mul_one] at hb1 hcomm
    have hdm : d ∈ Subgroup.zpowers (d ^ m) :=
      mem_zpowers_of_mem_zpowers hd3' (Subgroup.zpow_mem_zpowers d m) hb1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdm
    rw [← hk]
    exact (hcomm.zpow_right k).eq
  ·
    set n' := n % 3 with hn'
    have hnn : (n * n') % 3 = 1 := by
      have : n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases this with h | h <;> rw [hn', Int.mul_emod, h] <;> norm_num
    have hpow : (d ^ m * e ^ n) ^ n' = d ^ (m * n') * e := by
      rw [(Commute.zpow_zpow (show Commute d e from hde) m n).mul_zpow, ← zpow_mul, ← zpow_mul,
        zpow_eq_zpow_emod (n * n') he3', hnn, zpow_one]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.zpowers_le.mpr hdδ) (Subgroup.zpow_mem_zpowers d (m * n')))
    have hδ3' : δ ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hδ3]
    set j := (i % 3).toNat with hj
    have hjeq : δ ^ i = δ ^ j := by
      rw [zpow_eq_zpow_emod _ hδ3', ← zpow_natCast, hj,
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    have hbe : (d ^ m * e ^ n) ^ n' = x ^ j * e * (x ^ j)⁻¹ := by
      rw [hpow, hconj j, ← hi, hjeq]
      exact (Commute.pow_left (show Commute δ e from by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
        exact Commute.zpow_left (show Commute d e from hde) k) j).eq
    have hcomm' : y * (x ^ j * e * (x ^ j)⁻¹) = (x ^ j * e * (x ^ j)⁻¹) * y := by
      rw [← hbe]
      exact (hcomm.zpow_right n').eq
    set S' := S.map (MulAut.conj (x ^ j)⁻¹).toMonoidHom with hS'
    have hS'2 : IsPGroup 2 S' := hS2.map _
    have hxjd : x ^ j * d = d * x ^ j := (Commute.pow_left (show Commute x d from hxd) j).eq
    have hdS' : d ∈ Subgroup.normalizer (S' : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨t, ht, rfl⟩ := hz
      have ht' := (Subgroup.mem_normalizer_iff.mp hdS t).mp ht
      refine ⟨_, ht', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc (x ^ j)⁻¹ * (d * t * d⁻¹) * x ^ j
          = (x ^ j)⁻¹ * ((x ^ j * d * (x ^ j)⁻¹) * t * (x ^ j * d * (x ^ j)⁻¹)⁻¹) * x ^ j := by
            rw [hxjd, mul_inv_cancel_right]
        _ = d * ((x ^ j)⁻¹ * t * x ^ j) * d⁻¹ := by group
    have hye : (x ^ j)⁻¹ * y * x ^ j * e = e * ((x ^ j)⁻¹ * y * x ^ j) := by
      calc (x ^ j)⁻¹ * y * x ^ j * e
          = (x ^ j)⁻¹ * (y * (x ^ j * e * (x ^ j)⁻¹)) * x ^ j := by group
        _ = (x ^ j)⁻¹ * ((x ^ j * e * (x ^ j)⁻¹) * y) * x ^ j := by rw [hcomm']
        _ = e * ((x ^ j)⁻¹ * y * x ^ j) := by group
    have hyS' : (x ^ j)⁻¹ * y * x ^ j ∈ S' :=
      ⟨y, hy.1, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have hy' : (x ^ j)⁻¹ * y * x ^ j ∈ S' ⊓ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyS', Subgroup.mem_centralizer_singleton_iff.mpr hye⟩
    have hyd := Subgroup.mem_centralizer_singleton_iff.mp (hno S' hS'2 hdS' hy')
    calc y * d = x ^ j * (((x ^ j)⁻¹ * y * x ^ j) * d) * (x ^ j)⁻¹ := by
          rw [show x ^ j * (((x ^ j)⁻¹ * y * x ^ j) * d) * (x ^ j)⁻¹ =
            y * (x ^ j * d * (x ^ j)⁻¹) by group, hxjd, mul_inv_cancel_right]
      _ = x ^ j * (d * ((x ^ j)⁻¹ * y * x ^ j)) * (x ^ j)⁻¹ := by rw [hyd]
      _ = (x ^ j * d * (x ^ j)⁻¹) * y := by group
      _ = d * y := by rw [hxjd, mul_inv_cancel_right]

theorem exists_commute_not_mem_zpowers {S E : Subgroup G} (hS : IsPGroup 3 S) (hES : E ≤ S)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {d : G} (hdS : d ∈ S)
    (hd3 : orderOf d = 3) :
    ∃ w ∈ S, orderOf w = 3 ∧ w ∉ Subgroup.zpowers d ∧ w * d = d * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 : d ≠ 1 := fun h => by rw [h, orderOf_one] at hd3; norm_num at hd3
  have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  have hEd : ¬ E ≤ Subgroup.zpowers d := fun h => by
    have := Subgroup.card_le_of_le h
    rw [hE9, Nat.card_zpowers, hd3] at this
    norm_num at this
  obtain ⟨w₀, hw₀E, hw₀d⟩ := Set.not_subset.mp hEd
  have hw₀3 : orderOf w₀ = 3 :=
    orderOf_eq_prime (hE.2 w₀ hw₀E) (fun h => hw₀d (h ▸ Subgroup.one_mem _))
  have : Nontrivial S := ⟨⟨⟨d, hdS⟩, 1, fun h => hd1 (congrArg Subtype.val h)⟩⟩
  have hZ : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hZ3 : IsPGroup 3 (Subgroup.center S) := hS.to_subgroup _
  obtain ⟨k, hk⟩ := hZ3.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 3
    (by rw [hk]; exact dvd_pow_self 3 hk0)
  have hzc : ∀ t ∈ S, t * ((z : S) : G) = ((z : S) : G) * t := fun t ht =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨t, ht⟩)
  have hz3 : orderOf ((z : S) : G) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  by_cases hzd : ((z : S) : G) ∈ Subgroup.zpowers d
  ·
    have hz1 : ((z : S) : G) ≠ 1 := fun h => by rw [h, orderOf_one] at hz3; norm_num at hz3
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_mem_zpowers hd3' hzd hz1)
    refine ⟨w₀, hES hw₀E, hw₀3, hw₀d, ?_⟩
    rw [← hi]
    exact (Commute.zpow_right (show Commute w₀ ((z : S) : G) from hzc w₀ (hES hw₀E)) i).eq
  · exact ⟨_, (z : S).2, hz3, hzd, (hzc d hdS).symm⟩

omit [Finite G] in
theorem isPGroup_zpowers_of_pow {y : G} {k : ℕ} (hy : y ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers y) := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

@[expose] noncomputable def thetaHull (L U : Subgroup G) : Subgroup G :=
  (((U.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).comap
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map L.subtype

omit [Finite G] in
theorem le_thetaHull {L U : Subgroup G} (hUL : U ≤ L) : U ≤ thetaHull L U := fun u hu =>
  ⟨⟨u, hUL hu⟩, ⟨⟨u, hUL hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩, rfl⟩

theorem mem_normalizer_thetaHull_of_mem_thetaQuotCentralizer {L U : Subgroup G} {v : G}
    (hv : v ∈ Sec4.thetaQuotCentralizer L) :
    v ∈ Subgroup.normalizer (thetaHull L U : Set G) := by
  obtain ⟨hvN, hvθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hv
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨m, hm, rfl⟩ := hz
  have hmL : v * (m : G) * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hvN _).mp m.2
  refine ⟨⟨_, hmL⟩, ?_, rfl⟩
  obtain ⟨t, ht, hte⟩ := hvθ m m.2
  have hm' : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (⟨v * (m : G) * v⁻¹, hmL⟩ : L) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) m := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (⟨v * (m : G) * v⁻¹, hmL⟩ : L)⁻¹ * m = t⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((t : L) : G) = (m : G)⁻¹ * (v * m * v⁻¹) from hte]
      group
    rw [this]
    exact Subgroup.inv_mem _ ht
  have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 L) m ∈
      (U.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := hm
  exact Subgroup.mem_comap.mpr (hm'.symm ▸ hmem)

theorem mem_normalizer_thetaHull_of_mem {L U : Subgroup G} {y : G} (hyL : y ∈ L)
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) :
    y ∈ Subgroup.normalizer (thetaHull L U : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨m, hm, rfl⟩ := hz
  obtain ⟨u, hu, hum⟩ := hm
  set y₀ : L := ⟨y, hyL⟩
  refine ⟨y₀ * m * y₀⁻¹, ?_, rfl⟩
  have hu' : ((y₀ * u * y₀⁻¹ : L) : G) ∈ U := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hyU _).mp (Subgroup.mem_subgroupOf.mp hu)
  refine ⟨y₀ * u * y₀⁻¹, Subgroup.mem_subgroupOf.mpr hu', ?_⟩
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hum]

theorem exists_two_subgroup_of_thetaHull {L U X : Subgroup G} (hUL : U ≤ L) (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hX : IsPGroup 3 X)
    (hXN : X ≤ Subgroup.normalizer (thetaHull L U : Set G)) :
    ∃ U' : Subgroup G, U' ≠ ⊥ ∧ IsPGroup 2 U' ∧ X ≤ Subgroup.normalizer (U' : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := aschbacherSolvableCore 3 L with hN
  set B := (U.subgroupOf L).map (QuotientGroup.mk' N) with hB
  have hB2 : IsPGroup 2 B :=
    (hU2.comap_of_injective L.subtype L.subtype_injective).map _
  have hcard : Nat.card (thetaHull L U) = Nat.card N * Nat.card B := by
    rw [thetaHull, Subgroup.card_map_of_injective L.subtype_injective]
    exact QuotientGroup.card_preimage_mk N (B : Set (L ⧸ N))
  obtain ⟨k, hk⟩ := hB2.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card (thetaHull L U)) := by
    rw [hcard, hk]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      three_not_dvd_card_aschbacherSolvableCore) (Nat.Coprime.pow_right k (by norm_num))
  have h2 : 2 ∣ Nat.card (thetaHull L U) := by
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hU1 (Subgroup.eq_bot_of_card_eq U hn)
    exact (dvd_pow_self 2 hn0).trans (hn ▸ Subgroup.card_dvd_of_le (le_thetaHull hUL))
  obtain ⟨S, hSD, hS0⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two X _ hX hXN hcop h2
  exact ⟨_, hS0, S.isPGroup'.map _, hSD⟩

theorem isSylowOf_inf_of_le_normalizer {Q C Y : Subgroup G} (hQ : IsSylowOf 3 Q C)
    (hQY : Q ≤ Subgroup.normalizer (Y : Set G)) (hYC : Y ≤ C) : IsSylowOf 3 (Q ⊓ Y) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : IsSylowOf 3 Q (Q ⊔ Y) := hQ.of_le le_sup_left (sup_le hQ.le hYC)
  exact hK.inf_of_le_normalizer le_sup_right (sup_le hQY Subgroup.le_normalizer)

theorem exists_elemAbelian_le_of_isSylowOf {T Y S : Subgroup G} (hT : IsSylowOf 3 T Y)
    (hSY : S ≤ Y) (hS : CFSG.Assembly.IsElemAbelian 3 S) (hS9 : Nat.card S = 9) :
    ∃ E : Subgroup G, E ≤ T ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS3 : IsPGroup 3 S := fun s => ⟨1, Subtype.ext (by simpa using hS.2 s s.2)⟩
  obtain ⟨P, hP⟩ := (hS3.comap_subtype (K := Y)).exists_le_sylow
  have hPY : IsSylowOf 3 ((P : Subgroup Y).map Y.subtype) Y := ⟨P, rfl⟩
  obtain ⟨k, -, hk⟩ := hT.exists_mem_conj hPY
  refine ⟨S.map (MulAut.conj k⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hsP : s ∈ (P : Subgroup Y).map Y.subtype :=
      ⟨⟨s, hSY hs⟩, hP (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
    have := (hk s).mp hsP
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  · obtain ⟨hc, he⟩ := hS
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, he x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hS9]

theorem exists_two_subgroup_le (hchar : CFSG.Assembly.IsCharTwoType G) {A Y U₀ : Subgroup G}
    (hU₀ : U₀ ≠ ⊥) (hU₀2 : IsPGroup 2 U₀) (hAU₀ : A ≤ Subgroup.normalizer (U₀ : Set G))
    {e d x δ : G} (heA : e ∈ A) (hdA : d ∈ A) (hde : d * e = e * d) (he3 : e ^ 3 = 1)
    (hd3 : orderOf d = 3) (hed : e ∉ Subgroup.zpowers d) (hxd : x * d = d * x)
    (hδ : δ ∈ Subgroup.zpowers d) (hδ1 : δ ≠ 1) (hxe : x * e * x⁻¹ = e * δ) (hdY : d ∈ Y)
    (hN : ∀ t ∈ Subgroup.centralizer ({e} : Set G), (∃ k : ℕ, t ^ 3 ^ k = 1) →
      t ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ Y ∧ d ∈ Subgroup.normalizer (U : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  obtain ⟨S, hS2, hAS, hSd⟩ := exists_isPGroup_two_not_le_centralizer hchar hU₀ hU₀2 hAU₀ hdA hd3
  obtain ⟨S', hS'2, hdS', hS'e⟩ := exists_inf_centralizer_not_le hde he3 hd3 hed hxd hδ hδ1 hxe
    hS2 (hAS hdA) (hAS heA) hSd
  set X := S' ⊓ Subgroup.centralizer ({e} : Set G) with hX
  have hdC : d ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hde
  have hdX : d ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hdS', Subgroup.le_normalizer hdC⟩
  set Z := Subgroup.zpowers d with hZ
  have hZX : Z ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr hdX
  have hZ3 : IsPGroup 3 Z := isPGroup_zpowers_of_pow (k := 1) (by rw [pow_one]; exact hd3')
  have hX2 : IsPGroup 2 X := hS'2.to_le inf_le_left
  have hX3 : ¬ 3 ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  set U := ⁅X, Z⁆ with hU
  have hUX : U ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hZX
  have hUd : ⁅U, Z⁆ = U :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three Z X
      hZ3 hX3 hZX
  have hU1 : U ≠ ⊥ := by
    intro hbot
    apply hS'e
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : ⁅y, d⁆ ∈ U := Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers d)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  have hdU : d ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hU, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hdX,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (Subgroup.mem_zpowers d))]
  exact ⟨U, hU1, hX2.to_le hUX, le_of_commutator_eq hdY hdC hd3' hN (hUX.trans inf_le_right) hUd,
    hdU⟩

end CFSG.RankThree.PartTwo.Sec11.Item1117Res7Proof
