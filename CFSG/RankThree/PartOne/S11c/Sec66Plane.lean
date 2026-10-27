module

public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartOne.PlaneInner

open Subgroup CFSG CFSG.Assembly

variable {H : Type} [Group H] [Finite H]

theorem false_of_commuting_extension_of_localRank {p : ℕ}
    (he : CFSG.Assembly.RankThreeEven.localRank p H ≤ 3) (hp : p.Prime)
    {A : Subgroup H} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ p = 1)
    (hAcard : Nat.card A = p ^ 3) {S : Subgroup H} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hAS : A ≤ Subgroup.normalizer (S : Set H)) {t : H} (htA : t ∉ A) (htp : t ^ p = 1)
    (htc : ∀ x ∈ A, x * t = t * x) (htS : t ∈ Subgroup.normalizer (S : Set H)) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ (m : A) (n : Subgroup.zpowers t),
      Commute (A.subtype m) ((Subgroup.zpowers t).subtype n) := by
    intro m n
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp n.2
    have h1 : Commute (m : H) t := htc m m.2
    show Commute (m : H) (n : H)
    rw [← hk]
    exact h1.zpow_right k
  let φ : A × Subgroup.zpowers t →* H := A.subtype.noncommCoprod (Subgroup.zpowers t).subtype hcomm
  have ht1 : t ≠ 1 := fun h => htA (h ▸ A.one_mem)
  have htord : orderOf t = p := orderOf_eq_prime htp ht1
  have hdisj : Disjoint A (Subgroup.zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxA hxt
    by_contra hx1
    have hxord : orderOf x = p := orderOf_eq_prime (hAp x hxA) hx1
    have hzx : Subgroup.zpowers x ≤ Subgroup.zpowers t := (Subgroup.zpowers_le).mpr hxt
    have hcard : Nat.card (Subgroup.zpowers t) ≤ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, htord]
    have heq := Subgroup.eq_of_le_of_card_ge hzx hcard
    exact htA ((Subgroup.zpowers_le).mpr hxA (heq ▸ Subgroup.mem_zpowers t))
  have hinj : Function.Injective φ := by
    refine (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
      ⟨A.subtype_injective, (Subgroup.zpowers t).subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact hdisj
  have hcardD : Nat.card φ.range = p ^ 4 := by
    have h1 : Nat.card (A × Subgroup.zpowers t) = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← h1, Nat.card_prod, hAcard, Nat.card_zpowers, htord]
    ring
  have hpow : ∀ x ∈ φ.range, x ^ p = 1 := by
    rintro _ ⟨⟨m, n⟩, rfl⟩
    rw [← map_pow]
    have hm : m ^ p = 1 := Subtype.ext (hAp m m.2)
    have hn : n ^ p = 1 := by
      apply Subtype.ext
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp n.2
      show (n : H) ^ p = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, htp, one_zpow]
    have hmn : ((m, n) : A × Subgroup.zpowers t) ^ p = 1 :=
      Prod.ext (by simpa using hm) (by simpa using hn)
    rw [hmn]
    exact map_one φ
  have hcommD : IsMulCommutative φ.range := by
    refine ⟨⟨?_⟩⟩
    rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
    apply Subtype.ext
    show φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hAc _ x.1.2 _ y.1.2
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2.2
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp y.2.2
      show (x.2 : H) * (y.2 : H) = (y.2 : H) * (x.2 : H)
      rw [← hk, ← hl]
      exact (Commute.zpow_zpow_self t k l).eq
  have hnorm : φ.range ≤ Subgroup.normalizer (S : Set H) := by
    rintro _ ⟨⟨m, n⟩, rfl⟩
    show (m : H) * (n : H) ∈ _
    exact mul_mem (hAS m.2) ((Subgroup.zpowers_le).mpr htS n.2)
  have h4 := CFSG.RankThree.PartOne.Sec9Excl.le_localRank_of_normalizes hp.one_lt hS1 hS2 hcommD
    hpow hcardD hnorm
  omega

theorem false_of_commuting_extension (he : evenRank H ≤ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup H} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ p = 1)
    (hAcard : Nat.card A = p ^ 3) {S : Subgroup H} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hAS : A ≤ Subgroup.normalizer (S : Set H)) {t : H} (htA : t ∉ A) (htp : t ^ p = 1)
    (htc : ∀ x ∈ A, x * t = t * x) (htS : t ∈ Subgroup.normalizer (S : Set H)) : False :=
  false_of_commuting_extension_of_localRank
    ((CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans he) hp hAc hAp hAcard hS1 hS2
    hAS htA htp htc htS

omit [Finite H] in
theorem exists_mul_of_mem_sup_centralizer {J : Subgroup H} {x : H}
    (hx : x ∈ J ⊔ Subgroup.centralizer (J : Set H)) :
    ∃ j ∈ J, ∃ z ∈ Subgroup.centralizer (J : Set H), x = j * z := by
  have hle : J ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set H) : Set H) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.le_centralizer_iff.mpr le_rfl
  have h := Subgroup.coe_mul_of_left_le_normalizer_right J (Subgroup.centralizer (J : Set H)) hle
  have hx' : x ∈ ((J ⊔ Subgroup.centralizer (J : Set H) : Subgroup H) : Set H) := hx
  rw [h] at hx'
  obtain ⟨j, hj, z, hz, rfl⟩ := hx'
  exact ⟨j, hj, z, hz, rfl⟩

omit [Finite H] in
theorem orderOf_dvd_card_center {J : Subgroup H} {ζ : H} (hJ : ζ ∈ J)
    (hC : ζ ∈ Subgroup.centralizer (J : Set H)) :
    orderOf ζ ∣ Nat.card (Subgroup.center J) := by
  have hζ : (⟨ζ, hJ⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hC) g g.2
  have h1 := orderOf_dvd_natCard (⟨(⟨ζ, hJ⟩ : J), hζ⟩ : Subgroup.center J)
  have h2 : orderOf ζ = orderOf (⟨(⟨ζ, hJ⟩ : J), hζ⟩ : Subgroup.center J) :=
    (Subgroup.orderOf_coe (⟨ζ, hJ⟩ : J)).trans
      (Subgroup.orderOf_coe (⟨(⟨ζ, hJ⟩ : J), hζ⟩ : Subgroup.center J))
  rw [h2]
  exact h1

omit [Finite H] in
theorem eq_one_of_pow_eq_one {p : ℕ} (hp : p.Prime) {J : Subgroup H}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {ζ : H} (hJ : ζ ∈ J)
    (hC : ζ ∈ Subgroup.centralizer (J : Set H)) (hζp : ζ ^ p = 1) : ζ = 1 := by
  have h1 := orderOf_dvd_card_center hJ hC
  have h2 : orderOf ζ ∣ p := orderOf_dvd_of_pow_eq_one hζp
  rcases (Nat.dvd_prime hp).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h1
    exact absurd h1 hZ

omit [Finite H] in
theorem exists_split {p : ℕ} (hp : p.Prime) {J : Subgroup H}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {x : H}
    (hx : x ∈ J ⊔ Subgroup.centralizer (J : Set H)) (hxp : x ^ p = 1) :
    ∃ t ∈ J, ∃ y ∈ Subgroup.centralizer (J : Set H), x = t * y ∧ t ^ p = 1 ∧ y ^ p = 1 := by
  obtain ⟨j, hj, z, hz, rfl⟩ := exists_mul_of_mem_sup_centralizer hx
  have hjz : Commute j z := (Subgroup.mem_centralizer_iff.mp hz) j hj
  have hxp' : j ^ p * z ^ p = 1 := by rw [← hjz.mul_pow]; exact hxp
  have hzp : z ^ p = (j ^ p)⁻¹ := eq_inv_of_mul_eq_one_right hxp'
  have hζJ : j ^ p ∈ J := J.pow_mem hj p
  have hζC : j ^ p ∈ Subgroup.centralizer (J : Set H) := by
    have : j ^ p = (z ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hxp'
    rw [this]
    exact inv_mem (Subgroup.pow_mem _ hz p)
  have hn : Nat.Coprime p (orderOf (j ^ p)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => hZ ?_
    exact hdvd.trans (orderOf_dvd_card_center hζJ hζC)
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (orderOf (j ^ p) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hn
  have hu : (j ^ p) ^ (u * (p : ℤ)) = j ^ p := by
    have h1 : (j ^ p) ^ (u * (p : ℤ) + v * (orderOf (j ^ p) : ℤ)) = j ^ p := by
      rw [huv, zpow_one]
    rw [zpow_add, zpow_mul' (j ^ p) v (orderOf (j ^ p) : ℤ), zpow_natCast, pow_orderOf_eq_one,
      one_zpow, mul_one] at h1
    exact h1
  have hζup : ((j ^ p) ^ u) ^ p = j ^ p := by
    rw [← zpow_natCast, ← zpow_mul]
    exact hu
  have hζuJ : (j ^ p) ^ u ∈ J := J.zpow_mem hζJ u
  have hζuC : (j ^ p) ^ u ∈ Subgroup.centralizer (J : Set H) := Subgroup.zpow_mem _ hζC u
  refine ⟨j * ((j ^ p) ^ u)⁻¹, J.mul_mem hj (J.inv_mem hζuJ), (j ^ p) ^ u * z,
    (Subgroup.centralizer (J : Set H)).mul_mem hζuC hz, ?_, ?_, ?_⟩
  · group
  · have hc : Commute j ((j ^ p) ^ u)⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp (inv_mem hζuC)) j hj
    rw [hc.mul_pow, inv_pow, hζup]
    exact mul_inv_cancel _
  · have hc : Commute ((j ^ p) ^ u) z := (Subgroup.mem_centralizer_iff.mp hz) _ hζuJ
    rw [hc.mul_pow, hζup, hzp]
    exact mul_inv_cancel _

omit [Finite H] in
theorem commute_of_split {p : ℕ} (hp : p.Prime) {J A : Subgroup H}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hAN : A ≤ Subgroup.normalizer (J : Set H))
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x t y : H} (hxA : x ∈ A) (htJ : t ∈ J)
    (hyC : y ∈ Subgroup.centralizer (J : Set H)) (hxty : x = t * y) (htp : t ^ p = 1) :
    ∀ a ∈ A, a * t = t * a := by
  intro a ha
  have haN : ∀ j ∈ J, a * j * a⁻¹ ∈ J := fun j hj =>
    (Subgroup.mem_normalizer_iff.mp (hAN ha) j).mp hj
  have haN' : ∀ j ∈ J, a⁻¹ * j * a ∈ J := fun j hj => by
    have := (Subgroup.mem_normalizer_iff.mp (hAN (A.inv_mem ha)) j).mp hj
    simpa using this
  have hayC : a * y * a⁻¹ ∈ Subgroup.centralizer (J : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h1 := (Subgroup.mem_centralizer_iff.mp hyC) (a⁻¹ * j * a) (haN' j hj)
    calc j * (a * y * a⁻¹) = a * ((a⁻¹ * j * a) * y) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * j * a)) * a⁻¹ := by rw [h1]
      _ = (a * y * a⁻¹) * j := by group
  have hax : a * x * a⁻¹ = x := by
    rw [hAc a ha x hxA]
    group
  have h3 : t * y = (a * t * a⁻¹) * (a * y * a⁻¹) := by
    have h1 : a * x * a⁻¹ = (a * t * a⁻¹) * (a * y * a⁻¹) := by rw [hxty]; group
    rw [← hxty, ← hax]
    exact h1
  have h2 : t⁻¹ * (a * t * a⁻¹) = y * (a * y * a⁻¹)⁻¹ := by
    calc t⁻¹ * (a * t * a⁻¹)
        = t⁻¹ * ((a * t * a⁻¹) * (a * y * a⁻¹)) * (a * y * a⁻¹)⁻¹ := by group
      _ = t⁻¹ * (t * y) * (a * y * a⁻¹)⁻¹ := by rw [← h3]
      _ = y * (a * y * a⁻¹)⁻¹ := by group
  have hζJ : t⁻¹ * (a * t * a⁻¹) ∈ J := J.mul_mem (J.inv_mem htJ) (haN t htJ)
  have hζC : t⁻¹ * (a * t * a⁻¹) ∈ Subgroup.centralizer (J : Set H) := by
    rw [h2]
    exact (Subgroup.centralizer (J : Set H)).mul_mem hyC
      ((Subgroup.centralizer (J : Set H)).inv_mem hayC)
  have hζp : (t⁻¹ * (a * t * a⁻¹)) ^ p = 1 := by
    have hc : Commute t (t⁻¹ * (a * t * a⁻¹)) := (Subgroup.mem_centralizer_iff.mp hζC) t htJ
    have h4 : (a * t * a⁻¹) ^ p = 1 := by rw [conj_pow, htp]; group
    have h5 : t * (t⁻¹ * (a * t * a⁻¹)) = a * t * a⁻¹ := by group
    rw [← h5, hc.mul_pow, htp, one_mul] at h4
    exact h4
  have hζ1 := eq_one_of_pow_eq_one hp hZ hζJ hζC hζp
  have h6 : a * t * a⁻¹ = t := (inv_mul_eq_one.mp hζ1).symm
  calc a * t = a * t * a⁻¹ * a := by group
    _ = t * a := by rw [h6]

theorem exists_inner_part (he : evenRank H ≤ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J A : Subgroup H} (hZ : ¬ p ∣ Nat.card (Subgroup.center J))
    (hAN : A ≤ Subgroup.normalizer (J : Set H)) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAp : ∀ x ∈ A, x ^ p = 1) (hAcard : Nat.card A = p ^ 3) {c : H}
    (hCA : ∀ x ∈ A, x ∈ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c)
    {S : Subgroup H} (hSJ : S ≤ J) (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hAS : A ≤ Subgroup.normalizer (S : Set H)) {x : H} (hxA : x ∈ A)
    (hxJ : x ∈ J ⊔ Subgroup.centralizer (J : Set H)) (hxc : x ∉ Subgroup.zpowers c) :
    ∃ d ∈ A, d ∈ J ∧ d ≠ 1 ∧ d ^ p = 1 := by
  obtain ⟨t, htJ, y, hyC, hxty, htp, hyp⟩ := exists_split hp hZ hxJ (hAp x hxA)
  have htc := commute_of_split hp hZ hAN hAc hxA htJ hyC hxty htp
  have hyS : y ∈ Subgroup.normalizer (S : Set H) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSJ) hyC)
  have htS : t ∈ Subgroup.normalizer (S : Set H) := by
    have : t = x * y⁻¹ := by rw [hxty]; group
    rw [this]
    exact mul_mem (hAS hxA) (inv_mem hyS)
  have htA : t ∈ A := by
    by_contra htA
    exact false_of_commuting_extension he hp hp2 hAc hAp hAcard hS1 hS2 hAS htA htp htc htS
  refine ⟨t, htA, htJ, ?_, htp⟩
  rintro rfl
  apply hxc
  rw [one_mul] at hxty
  rw [hxty]
  exact hCA y (hxty ▸ hxA) hyC

theorem card_mul_le_of_lt {p : ℕ} (hp : p.Prime) {A K K' : Subgroup H}
    (hAcard : Nat.card A = p ^ 3) (hK : K ≤ K') (hK' : K' ≤ A) (hne : K ≠ K') :
    p * Nat.card K ≤ Nat.card K' := by
  have h1 : Nat.card K ∣ Nat.card K' := Subgroup.card_dvd_of_le hK
  have h2 : Nat.card K' ∣ p ^ 3 := hAcard ▸ Subgroup.card_dvd_of_le hK'
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 h2
  have h3 : Nat.card K ∣ p ^ j := hj' ▸ h1
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 h3
  have hij : i ≠ j := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hK (by rw [hi', hj']))
  have hlt : i < j := lt_of_le_of_ne hi hij
  rw [hi', hj', ← pow_succ']
  exact Nat.pow_le_pow_right hp.pos hlt

theorem decomposition {p : ℕ} (hp : p.Prime) {J A : Subgroup H}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hAp : ∀ x ∈ A, x ^ p = 1)
    (hAcard : Nat.card A = p ^ 3) {c d a : H} (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hcC : c ∈ Subgroup.centralizer (J : Set H)) (hdA : d ∈ A) (hdJ : d ∈ J) (hd1 : d ≠ 1)
    (haA : a ∈ A) (haJ : a ∉ J ⊔ Subgroup.centralizer (J : Set H)) :
    A = Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers d ∧
      Subgroup.zpowers d = A ⊓ J := by
  have : Fact p.Prime := ⟨hp⟩
  have hcord : orderOf c = p := orderOf_eq_prime (hAp c hcA) hc1
  have hdord : orderOf d = p := orderOf_eq_prime (hAp d hdA) hd1
  have hdpow : d ^ p = 1 := hAp d hdA
  have hcpow : c ^ p = 1 := hAp c hcA
  have hdc : d ∉ Subgroup.zpowers c := fun h => hd1
    (eq_one_of_pow_eq_one hp hZ hdJ ((Subgroup.zpowers_le).mpr hcC h) hdpow)
  have hK2le : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤
      J ⊔ Subgroup.centralizer (J : Set H) :=
    sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_right hcC))
      ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_left hdJ))
  have hac : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := fun h => haJ (hK2le h)
  obtain ⟨K1, hK1⟩ : ∃ K : Subgroup H, K = Subgroup.zpowers c := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K : Subgroup H, K = K1 ⊔ Subgroup.zpowers d := ⟨_, rfl⟩
  obtain ⟨K3, hK3⟩ : ∃ K : Subgroup H, K = K2 ⊔ Subgroup.zpowers a := ⟨_, rfl⟩
  have hK1A : K1 ≤ A := hK1 ▸ (Subgroup.zpowers_le).mpr hcA
  have hK2A : K2 ≤ A := hK2 ▸ sup_le hK1A ((Subgroup.zpowers_le).mpr hdA)
  have hK3A : K3 ≤ A := hK3 ▸ sup_le hK2A ((Subgroup.zpowers_le).mpr haA)
  have hdK2 : d ∈ K2 := hK2 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have haK3 : a ∈ K3 := hK3 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hdK1 : d ∉ K1 := hK1 ▸ hdc
  have haK2 : a ∉ K2 := by rw [hK2, hK1]; exact hac
  have h12 : p * Nat.card K1 ≤ Nat.card K2 :=
    card_mul_le_of_lt hp hAcard (hK2 ▸ le_sup_left) hK2A fun h => hdK1 (h ▸ hdK2)
  have h23 : p * Nat.card K2 ≤ Nat.card K3 :=
    card_mul_le_of_lt hp hAcard (hK3 ▸ le_sup_left) hK3A fun h => haK2 (h ▸ haK3)
  have hK1card : Nat.card K1 = p := by rw [hK1, Nat.card_zpowers, hcord]
  rw [hK1card] at h12
  have hK3A' : K3 = A := by
    refine Subgroup.eq_of_le_of_card_ge hK3A ?_
    rw [hAcard]
    calc p ^ 3 = p * (p * p) := by ring
      _ ≤ p * Nat.card K2 := Nat.mul_le_mul_left p h12
      _ ≤ _ := h23
  refine ⟨?_, ?_⟩
  · rw [← hK3A', hK3, hK2, hK1]
    ac_rfl
  · obtain ⟨N, hN⟩ : ∃ N : Subgroup H, N = A ⊓ J := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Subgroup H, B = A ⊓ (J ⊔ Subgroup.centralizer (J : Set H)) :=
      ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M : Subgroup H, M = N ⊔ Subgroup.zpowers c := ⟨_, rfl⟩
    have hdN : Subgroup.zpowers d ≤ N :=
      hN ▸ le_inf ((Subgroup.zpowers_le).mpr hdA) ((Subgroup.zpowers_le).mpr hdJ)
    have hNA : N ≤ A := hN ▸ inf_le_left
    have hNJ : ∀ x ∈ N, x ∈ J := fun x hx => (hN ▸ hx : x ∈ A ⊓ J).2
    by_contra hne
    have h1 : p * Nat.card (Subgroup.zpowers d) ≤ Nat.card N :=
      card_mul_le_of_lt hp hAcard hdN hNA (hN ▸ hne)
    rw [Nat.card_zpowers, hdord] at h1
    have hcN : c ∉ N := fun h => hc1 (eq_one_of_pow_eq_one hp hZ (hNJ c h) hcC hcpow)
    have hMA : M ≤ A := hM ▸ sup_le hNA ((Subgroup.zpowers_le).mpr hcA)
    have hcM : c ∈ M := hM ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    have h2 : p * Nat.card N ≤ Nat.card M :=
      card_mul_le_of_lt hp hAcard (hM ▸ le_sup_left) hMA fun h => hcN (h ▸ hcM)
    have hMB : M ≤ B := by
      rw [hM, hB, hN]
      exact sup_le (inf_le_inf_left A le_sup_left)
        (le_inf ((Subgroup.zpowers_le).mpr hcA)
          ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_right hcC)))
    have hBA : B ≠ A := fun h => by
      have haB : a ∈ B := h ▸ haA
      rw [hB] at haB
      exact haJ haB.2
    have h3 : p * Nat.card B ≤ Nat.card A :=
      card_mul_le_of_lt hp hAcard (hB ▸ inf_le_left) le_rfl hBA
    have h4 : Nat.card M ≤ Nat.card B := Subgroup.card_le_of_le hMB
    rw [hAcard] at h3
    have h5 : p * (p * p) ≤ Nat.card B := calc
      p * (p * p) ≤ p * Nat.card N := Nat.mul_le_mul_left p h1
      _ ≤ Nat.card M := h2
      _ ≤ Nat.card B := h4
    have h6 : p * (p * (p * p)) ≤ p ^ 3 := (Nat.mul_le_mul_left p h5).trans h3
    have h8 : p ^ 3 * 1 < p ^ 3 * p := Nat.mul_lt_mul_of_pos_left hp.one_lt (pow_pos hp.pos 3)
    nlinarith [h6, h8]

end CFSG.RankThree.PartOne.PlaneInner
