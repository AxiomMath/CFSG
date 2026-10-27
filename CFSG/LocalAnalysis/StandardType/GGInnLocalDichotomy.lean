module

public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubExistAdmissible

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Elementary

variable {G : Type} [Group G]

theorem eq_one_of_conj_eq_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {b t z : G} (hbp : b ^ p = 1)
    (hbt : b * t * b⁻¹ = t * z) (hbz : b * z = z * b) {k : ℕ} (hz : z ^ 2 ^ k = 1) : z = 1 := by
  have hpow : ∀ n : ℕ, b ^ n * t * (b ^ n)⁻¹ = t * z ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hbz' : b * z ^ n = z ^ n * b := ((Commute.pow_right hbz n)).eq
      calc b ^ (n + 1) * t * (b ^ (n + 1))⁻¹ = b * (b ^ n * t * (b ^ n)⁻¹) * b⁻¹ := by group
        _ = b * (t * z ^ n) * b⁻¹ := by rw [ih]
        _ = (b * t * b⁻¹) * (b * z ^ n * b⁻¹) := by group
        _ = t * z * (z ^ n * b * b⁻¹) := by rw [hbt, hbz']
        _ = t * z ^ (n + 1) := by group
  have h1 := hpow p
  rw [hbp, one_mul, inv_one, mul_one] at h1
  have hzp : z ^ p = 1 := (mul_left_cancel ((mul_one t).trans h1)).symm
  have hd : orderOf z ∣ Nat.gcd p (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp) (orderOf_dvd_of_pow_eq_one hz)
  have hcop : Nat.gcd p (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

variable [Finite G]

theorem mem_centralizer_of_inner_of_not_dvd {p : ℕ} (hp : p.Prime) {L T : Subgroup G}
    {x b l : G} (hlL : l ∈ L) (hbl : ∀ m ∈ L, b * m * b⁻¹ = l * m * l⁻¹) (hbp : b ^ p = 1)
    (hx : x ^ p = 1) (hx1 : x ≠ 1) (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (hbx : b * x = x * b)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hTL : T ≤ Subgroup.centralizer (L : Set G)) (hTx : T ≤ Subgroup.centralizer ({x} : Set G))
    (hnd : ¬ p ∣ orderOf (l ^ p)) :
    b ∈ Subgroup.centralizer (T : Set G) := by
  have := Fact.mk hp
  have hLT : L ≤ Subgroup.centralizer (T : Set G) := Subgroup.le_centralizer_iff.mp hTL
  have hxT : x ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTx ht)
  set y := l⁻¹ * b with hy
  have hbl' : b * l = l * b := by
    have h := hbl l hlL
    calc b * l = b * l * b⁻¹ * b := by group
      _ = l * l * l⁻¹ * b := by rw [h]
      _ = l * b := by group
  have hyC : y ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h := hbl m hm
    calc m * (l⁻¹ * b) = l⁻¹ * (l * m * l⁻¹) * b := by group
      _ = l⁻¹ * (b * m * b⁻¹) * b := by rw [h]
      _ = l⁻¹ * b * m := by group
  have hlx : l * x = x * l := Subgroup.mem_centralizer_iff.mp hxC l hlL
  have hyx : y * x = x * y := by
    calc l⁻¹ * b * x = l⁻¹ * (x * l) * l⁻¹ * b := by rw [mul_assoc l⁻¹ b x, hbx]; group
      _ = l⁻¹ * (l * x) * l⁻¹ * b := by rw [hlx]
      _ = x * (l⁻¹ * b) := by group
  have hc : Commute l⁻¹ b := by
    show l⁻¹ * b = b * l⁻¹
    calc l⁻¹ * b = l⁻¹ * (b * l) * l⁻¹ := by group
      _ = l⁻¹ * (l * b) * l⁻¹ := by rw [hbl']
      _ = b * l⁻¹ := by group
  have hyp_eq : y ^ p = (l ^ p)⁻¹ := by
    rw [hy, hc.mul_pow, hbp, mul_one, inv_pow]
  have hyp : y ^ p ∈ L := by
    rw [hyp_eq]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hlL _)
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  have ha : a ≤ 1 := by
    by_contra ha
    push Not at ha
    apply hnd
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    have hpd : p ∣ orderOf y := by
      rw [hn]
      exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) m
    have h1 : orderOf (y ^ p) = orderOf y / p := orderOf_pow_of_dvd hp.ne_zero hpd
    rw [hyp_eq, orderOf_inv] at h1
    have h2 : orderOf y / p = p * (p ^ a' * m) := by
      rw [hn]
      exact Nat.div_eq_of_eq_mul_left hp.pos (by ring)
    rw [h1, h2]
    exact dvd_mul_right p _
  set y₁ := y ^ m with hy₁
  have hy₁p : y₁ ^ p = 1 := by
    rw [hy₁, ← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hn]
    calc p ^ a * m ∣ p ^ 1 * m := Nat.mul_dvd_mul_right (Nat.pow_dvd_pow p ha) m
      _ = m * p := by ring
  have hP1 := isPGroup_zpowers_of_pow hp (k := 1) (by rw [pow_one]; exact hy₁p)
  have hP2 := isPGroup_zpowers_of_pow hp (k := 1) (by rw [pow_one]; exact hx)
  have hcomm : ∀ c ∈ Subgroup.zpowers x, c * y₁ = y₁ * c := by
    intro c hc'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    exact ((Commute.pow_left hyx m).zpow_right i).symm.eq
  have hN : Subgroup.zpowers y₁ ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro c hc'
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    exact (Commute.zpow_right (show Commute d y₁ from hcomm d hd) i).eq
  have hPp : IsPGroup p (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers x : Subgroup G) :=
    hP1.to_sup_of_normal_right' hP2 hN
  have hPC : (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers x : Subgroup G) ≤
      Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hyC m)) (Subgroup.zpowers_le.mpr hxC)
  have hy₁x : y₁ ∈ Subgroup.zpowers x :=
    mem_zpowers_of_isCyclic hp (hcyc _ hPC hPp) (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)) hx hx1 hy₁p
  have hy₂ : y ^ p ^ a ∈ L := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0
      rw [pow_zero, pow_one]
      have hcop : p.Coprime (orderOf y) := by
        rw [hn, pow_zero, one_mul]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
      obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
      rw [← hk]
      exact Subgroup.pow_mem _ hyp k
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [pow_succ', pow_mul]
      exact Subgroup.pow_mem _ hyp _
  have hcop : Nat.Coprime (p ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hyeq : y = (y ^ p ^ a) ^ u * (y ^ m) ^ v := by
    rw [← zpow_natCast y (p ^ a), ← zpow_natCast y m, ← zpow_mul, ← zpow_mul, ← zpow_add]
    rw [show ((p ^ a : ℕ) : ℤ) * u + (m : ℤ) * v = 1 by linear_combination huv, zpow_one]
  have hyT : y ∈ Subgroup.centralizer (T : Set G) := by
    rw [hyeq]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (hLT hy₂) _)
      (Subgroup.zpow_mem _ (Subgroup.zpowers_le.mpr hxT hy₁x) _)
  have hb : b = l * y := by rw [hy]; group
  rw [hb]
  exact Subgroup.mul_mem _ (hLT hlL) hyT

end Elementary

section Inner

variable {G : Type} [Group G] (L : Subgroup G) {R : Type} [Group R]
  (θ : L ⧸ Subgroup.center L ≃* R)

theorem ggLAut_le_normalizer_eq_conj (l : L) :
    ggLAut L θ ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
      MulAut.conj (θ (l : L ⧸ Subgroup.center L)) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H m =>
    rw [ggLAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl

end Inner

section Cases

variable {G : Type} [Group G] [Finite G]

theorem exists_two_subgroup_of_inn {L : Subgroup G} (hL : commutator L = ⊤) {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) {Θ : Subgroup (MulAut R)} (hΘ1 : Θ ≠ ⊥)
    (hΘ2 : IsPGroup 2 Θ) (hΘinn : Θ ≤ (MulAut.conj : R →* MulAut R).range)
    (hΘB : ∀ b (hb : b ∈ B), ∀ φ ∈ Θ,
      ggLAut L θ ⟨b, hBN hb⟩ * φ * (ggLAut L θ ⟨b, hBN hb⟩)⁻¹ ∈ Θ) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f₀ : L →* MulAut R := (ggLAut L θ).comp (Subgroup.inclusion Subgroup.le_normalizer)
    with hf₀
  have hf₀l : ∀ l : L, f₀ l = MulAut.conj (θ (l : L ⧸ Subgroup.center L)) := fun l =>
    ggLAut_le_normalizer_eq_conj L θ l
  set W : Subgroup L := Θ.comap f₀ with hW
  set f : W →* MulAut R := f₀.comp W.subtype with hf
  have hfr : f.range ≤ Θ := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  have hker : f.ker ≤ Subgroup.center W := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw
    have hc := mem_centralizer_of_ggLAut_eq_one L θ hL
      (g := ⟨((w : L) : G), Subgroup.le_normalizer (w : L).2⟩) hw
    rw [Subgroup.mem_center_iff]
    intro v
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc _ (v : L).2
  have hrange2 : IsPGroup 2 f.range := hΘ2.to_le hfr
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have : Group.IsNilpotent f.range := hrange2.isNilpotent
  have : Group.IsNilpotent W :=
    Subgroup.isNilpotent_of_ker_le_center f.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 W))
  have hPn : (P : Subgroup W).Normal := inferInstance
  have := Sylow.unique_of_normal P hPn
  have hγW : ∀ b (hb : b ∈ B) (w : W), ggGamma L hBN ⟨b, hb⟩ (w : L) ∈ W := by
    intro b hb w
    show f₀ _ ∈ Θ
    have h1 : f₀ (ggGamma L hBN ⟨b, hb⟩ (w : L)) =
        ggLAut L θ ⟨b, hBN hb⟩ * f₀ w * (ggLAut L θ ⟨b, hBN hb⟩)⁻¹ := by
      have h2 : Subgroup.inclusion Subgroup.le_normalizer (ggGamma L hBN ⟨b, hb⟩ (w : L)) =
          (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G)) *
            Subgroup.inclusion Subgroup.le_normalizer (w : L) * ⟨b, hBN hb⟩⁻¹ :=
        Subtype.ext rfl
      rw [hf₀, MonoidHom.comp_apply, MonoidHom.comp_apply, h2, map_mul, map_mul, map_inv]
    rw [h1]
    exact hΘB b hb _ w.2
  have hPB : ∀ b (hb : b ∈ B) (w : W), w ∈ (P : Subgroup W) →
      (⟨ggGamma L hBN ⟨b, hb⟩ (w : L), hγW b hb w⟩ : W) ∈ (P : Subgroup W) := by
    intro b hb w hw
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨w, hw⟩
    have hw' : w ^ 2 ^ k = 1 := by
      have h1 := pow_orderOf_eq_one (⟨w, hw⟩ : (P : Subgroup W))
      rw [hk] at h1
      have h3 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h3
    have hv : (⟨ggGamma L hBN ⟨b, hb⟩ (w : L), hγW b hb w⟩ : W) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show (ggGamma L hBN ⟨b, hb⟩ (w : L)) ^ 2 ^ k = 1
      rw [← map_pow, ← Subgroup.coe_pow, hw', Subgroup.coe_one, map_one]
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (isPGroup_zpowers_of_pow Nat.prime_two hv)
    rw [Subsingleton.elim Q P] at hQ
    exact hQ (Subgroup.mem_zpowers _)
  have hP1 : (P : Subgroup W) ≠ ⊥ := by
    intro hPbot
    obtain ⟨⟨φ, hφΘ⟩, hφ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hΘ1
    have hφ1' : φ ≠ 1 := fun h => hφ1 (Subtype.ext h)
    obtain ⟨r, hr⟩ := hΘinn hφΘ
    obtain ⟨q, rfl⟩ := θ.surjective r
    induction q using QuotientGroup.induction_on with
    | H l =>
      have hlW : l ∈ W := by
        show f₀ l ∈ Θ
        rw [hf₀l, hr]
        exact hφΘ
      have hfw : f ⟨l, hlW⟩ = φ := by
        show f₀ l = φ
        rw [hf₀l, hr]
      obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hΘ2 ⟨φ, hφΘ⟩
      rw [Subgroup.orderOf_mk] at hj
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hj
        exact hφ1' hj
      have hdvd : 2 ∣ Nat.card W := by
        have h1 : orderOf φ ∣ orderOf (⟨l, hlW⟩ : W) := by
          rw [← hfw]
          exact orderOf_map_dvd f _
        rw [hj] at h1
        exact (dvd_pow_self 2 hj0).trans (h1.trans (orderOf_dvd_natCard _))
      exact P.ne_bot_of_dvd_card hdvd hPbot
  refine ⟨((P : Subgroup W).map W.subtype).map L.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective]
    exact hP1
  · exact (P.isPGroup'.map _).map _
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, hPB b hb w hw, rfl⟩, ggGamma_coe L hBN ⟨b, hb⟩ (w : L)⟩

omit [Finite G] in
theorem commutator_inf_centralizer_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup G} (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)} {B : Subgroup G}
    (hB : ∀ b ∈ B, b ^ p = 1) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {D : Subgroup (MulAut R)} (hDn : D.Normal) (hID : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ D)
    (hodd : Odd ((MulAut.conj : R →* MulAut R).range.relIndex D)) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (L : Set G))
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTB : (⁅T, B⁆ : Subgroup G) ≠ ⊥)
    (hΘ : ((ggLAut L θ).comp (Subgroup.inclusion hTN)).range ⊓
      (MulAut.conj : R →* MulAut R).range = ⊥) :
    (⁅T ⊓ Subgroup.centralizer (L : Set G), B⁆ : Subgroup G) ≠ ⊥ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hT0
  apply hTB
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hT0 ⊢
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  set z := t⁻¹ * (b * t * b⁻¹) with hz
  have hbtb : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht
  have hzT : z ∈ T := Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hbtb
  set lt := ggLAut L θ ⟨t, hTN ht⟩ with hlt
  set lb := ggLAut L θ ⟨b, hBN hb⟩ with hlb
  have hlz : ggLAut L θ ⟨z, hTN hzT⟩ = lt⁻¹ * (lb * lt * lb⁻¹) := by
    have h1 : (⟨z, hTN hzT⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨t, hTN ht⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
          (⟨b, hBN hb⟩ * ⟨t, hTN ht⟩ * (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G))⁻¹) :=
      Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hlbD : lb ∈ D := by
    refine hID _ (ggLAut_mem_of_induces L θ hBN h3 hb) ?_
    have h1 : (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB b hb)
    rw [hlb, ← map_pow, h1, map_one]
  have hzD : ggLAut L θ ⟨z, hTN hzT⟩ ∈ D := by
    rw [hlz]
    have h1 : lt⁻¹ * lb * lt⁻¹⁻¹ ∈ D := hDn.conj_mem _ hlbD _
    rw [inv_inv] at h1
    have h4 : lt⁻¹ * (lb * lt * lb⁻¹) = (lt⁻¹ * lb * lt) * lb⁻¹ := by group
    rw [h4]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hlbD)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT2 ⟨z, hzT⟩
  rw [Subgroup.orderOf_mk] at hk
  have hz2 : z ^ 2 ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one z
  have hlz2 : ggLAut L θ ⟨z, hTN hzT⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have h1 : (⟨z, hTN hzT⟩ : Subgroup.normalizer (L : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hz2)
    rw [h1, map_one]
  have hinn := mem_range_conj_of_pow_two_pow hodd hzD hlz2
  have hlz1 : ggLAut L θ ⟨z, hTN hzT⟩ = 1 := by
    have h1 : ggLAut L θ ⟨z, hTN hzT⟩ ∈ ((ggLAut L θ).comp (Subgroup.inclusion hTN)).range ⊓
        (MulAut.conj : R →* MulAut R).range := ⟨⟨⟨z, hzT⟩, rfl⟩, hinn⟩
    rw [hΘ] at h1
    exact h1
  have hzC := mem_centralizer_of_ggLAut_eq_one L θ hL hlz1
  have hbz : b * z = z * b := Subgroup.mem_centralizer_iff.mp (hT0 ⟨hzT, hzC⟩) b hb
  have hbt : b * t * b⁻¹ = t * z := by rw [hz]; group
  have hz1 := eq_one_of_conj_eq_mul hp hp2 (hB b hb) hbt hbz hz2
  rw [hz1, mul_one] at hbt
  calc b * t = b * t * b⁻¹ * b := by group
    _ = t * b := by rw [hbt]

theorem ggInnLocal_or_delta {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I)
    (h4 : ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) :
    (∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G)) ∨
      ∃ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) ∧
        T₀ ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T₀ ∧
        B ≤ Subgroup.normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨D, hDn, hID, hodd⟩ := hOD
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := h4
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := fun t ht =>
    mem_normalizer_of_sstar hS hnc (hTx ht)
  set lamT := ((ggLAut L θ).comp (Subgroup.inclusion hTN)).range with hlamT
  have hlamT2 : IsPGroup 2 lamT :=
    hT2.of_surjective ((ggLAut L θ).comp (Subgroup.inclusion hTN)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  by_cases hΘ1 : lamT ⊓ (MulAut.conj : R →* MulAut R).range = ⊥
  · right
    refine ⟨T ⊓ Subgroup.centralizer (L : Set G), inf_le_right, inf_le_left.trans hTx,
      hT2.to_le inf_le_left, ?_,
      commutator_inf_centralizer_ne_bot hp hp2 hL θ (fun b hb => hS.1.1.2 b hb) hBN h3 hDn hID
        hodd hT2 hTN hBT hTB hΘ1⟩
    rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : b⁻¹ * l * b ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hBN (Subgroup.inv_mem _ hb)) l).mp hl
      rwa [inv_inv] at h1
    have hc := Subgroup.mem_centralizer_iff.mp ht.2 _ hl'
    calc l * (b * t * b⁻¹) = b * ((b⁻¹ * l * b) * t) * b⁻¹ := by group
      _ = b * (t * (b⁻¹ * l * b)) * b⁻¹ := by rw [hc]
      _ = b * t * b⁻¹ * l := by group
  · left
    refine exists_two_subgroup_of_inn hL θ hBN hΘ1 (hlamT2.to_le inf_le_left) inf_le_right ?_
    intro b hb φ hφ
    obtain ⟨⟨t, rfl⟩, hφi⟩ := hφ
    have hbtb : b * (t : G) * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp t.2
    refine ⟨⟨⟨b * t * b⁻¹, hbtb⟩, ?_⟩, (ggInnNormal R).conj_mem _ hφi _⟩
    have h1 : Subgroup.inclusion hTN ⟨b * t * b⁻¹, hbtb⟩ =
        (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G)) * Subgroup.inclusion hTN t *
          (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G))⁻¹ :=
      Subtype.ext rfl
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_mul, map_mul, map_inv]

theorem ggDeltaAdm_of_delta {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar p B x L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hδ : ∃ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) ∧
      T₀ ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T₀ ∧
      B ≤ Subgroup.normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥) :
    GGDeltaAdm p L (ggGamma L hBN).range := by
  have := Fact.mk hp
  obtain ⟨T, hTL, hTx, hT2, hBT, hTB⟩ := hδ
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    exact hTB (Subgroup.commutator_bot_left B)
  have hN2 : IsTwoLocal (Subgroup.normalizer (T : Set G)) := ⟨T, hT1, hT2, rfl⟩
  have hLN : L ≤ Subgroup.normalizer (T : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.mp hTL hl)
  have hcB := card_range_ggGamma_mul L hBN hp hS
  have hbound : ∀ E : Subgroup G, E ≤ Subgroup.normalizer (T : Set G) → IsElemAbelian p E →
      Nat.card E ≤ Nat.card B := fun E hEN hE => by
    rw [hS.1.2.1]
    exact card_le_of_twoLocal hp hN2 hEN hE
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_le_centralizer hS.2.2.2.1.1
  have hx : x ^ p = 1 := hS.1.1.2 x hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcardE : ∀ E : Subgroup L, Nat.card (E.map L.subtype) = Nat.card E := fun E =>
    (Nat.card_congr (E.equivMapOfInjective _ L.subtype_injective).toEquiv).symm
  have hmove : ∃ b ∈ B, b ∉ Subgroup.centralizer (T : Set G) := by
    by_contra hall
    push Not at hall
    apply hTB
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact hall
  have hinner : ∀ b (hb : b ∈ B) (l : L), MulAut.conj l = ggGamma L hBN ⟨b, hb⟩ →
      ∀ m ∈ L, b * m * b⁻¹ = (l : G) * m * (l : G)⁻¹ := by
    intro b hb l hl m hm
    have h2 := congrArg (fun φ : MulAut L => ((φ ⟨m, hm⟩ : L) : G)) hl
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h2, ggGamma_coe]
  refine ⟨?_, ?_⟩
  · intro e he hfix
    have hcomm : ∀ b ∈ B, ∀ c ∈ Subgroup.zpowers (e : G), b * c = c * b := by
      intro b hb c hc
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have h1 := congrArg Subtype.val (hfix _ ⟨⟨b, hb⟩, rfl⟩)
      rw [ggGamma_coe] at h1
      have h2 : b * (e : G) = (e : G) * b := by
        calc b * (e : G) = b * e * b⁻¹ * b := by group
          _ = e * b := by rw [h1]
      exact (Commute.zpow_right (show Commute b (e : G) from h2) i).eq
    have hep : (e : G) ^ p = 1 := by
      have h1 := congrArg Subtype.val he
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
    have hEab := isElemAbelian_sup hS.1.1 (isElemAbelian_zpowers hep) hcomm
    have hle : B ≤ B ⊔ Subgroup.zpowers (e : G) := le_sup_left
    have hEN : B ⊔ Subgroup.zpowers (e : G) ≤ Subgroup.normalizer (T : Set G) :=
      sup_le hBT (Subgroup.zpowers_le.mpr (hLN e.2))
    have heq := Subgroup.eq_of_le_of_card_ge hle (hbound _ hEN hEab)
    have heB : (e : G) ∈ B := by
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    refine ⟨⟨e, heB⟩, ?_⟩
    ext m
    simp only [ggGamma_coe, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  · by_cases hxL : x ∈ L
    · right
      refine ⟨?_, fun E hE => ?_, ?_⟩
      · have hxZ : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
          rw [Subgroup.mem_center_iff]
          intro m
          exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC m m.2)
        have hord : orderOf (⟨⟨x, hxL⟩, hxZ⟩ : Subgroup.center L) = p := by
          rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, orderOf_eq_prime hx hx1]
        rw [← hord]
        exact orderOf_dvd_natCard _
      · have h1 := hbound (E.map L.subtype) ((Subgroup.map_subtype_le E).trans hLN)
          (isElemAbelian_map hE L.subtype)
        rw [hcardE, ← hcB] at h1
        linarith [mul_comm (Nat.card (ggGamma L hBN).range) p]
      · obtain ⟨b, hb, hbT⟩ := hmove
        refine ⟨ggGamma L hBN ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, ?_⟩
        by_cases hinn : ggGamma L hBN ⟨b, hb⟩ ∈ (MulAut.conj : L →* MulAut L).range
        · right
          intro l hl
          by_contra hnd
          apply hbT
          have hnd' : ¬ p ∣ orderOf ((l : G) ^ p) := by
            rwa [← Subgroup.coe_pow, Subgroup.orderOf_coe]
          exact mem_centralizer_of_inner_of_not_dvd hp l.2 (hinner b hb l hl) (hS.1.1.2 b hb)
            hx hx1 hxC (IsElemAbelian.comm hS.1.1 hb hS.2.1) hS.2.2.2.2 hTL hTx hnd'
        · exact Or.inl hinn
    · left
      refine ⟨?_, fun E hE => ?_⟩
      · obtain ⟨b, hb, hbT⟩ := hmove
        refine ⟨ggGamma L hBN ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, ?_⟩
        rintro ⟨l, hl⟩
        apply hbT
        exact mem_centralizer_of_inner hp l.2 (hinner b hb l hl) (hS.1.1.2 b hb) hxL hx hx1 hxC
          (IsElemAbelian.comm hS.1.1 hb hS.2.1) hS.2.2.2.2 hTL hTx
      · set E' := E.map L.subtype with hE'
        have hEL : E' ≤ L := Subgroup.map_subtype_le E
        have hcomm : ∀ e ∈ E', ∀ c ∈ Subgroup.zpowers x, e * c = c * e := by
          intro e he c hc
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
          exact (Commute.zpow_right (show Commute e x from
            Subgroup.mem_centralizer_iff.mp hxC e (hEL he)) i).eq
        have hEab := isElemAbelian_sup (isElemAbelian_map hE L.subtype)
          (isElemAbelian_zpowers hx) hcomm
        have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (E' : Set G) := by
          intro c hc
          apply Subgroup.centralizer_le_normalizer
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          exact hcomm e he c hc
        have hdisj : Disjoint E' (Subgroup.zpowers x) := by
          rw [Subgroup.disjoint_def]
          intro g hgE hgx
          by_contra hg1
          exact hxL (mem_of_mem_zpowers_of_ne_one hp hx hx1 hgx (hEL hgE) hg1)
        have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
          hnorm hdisj
        rw [Nat.card_zpowers, orderOf_eq_prime hx hx1, hcardE] at hcard
        have h1 := hbound _ (sup_le (hEL.trans hLN)
          (Subgroup.zpowers_le.mpr (hBT hS.2.1))) hEab
        rw [hcard, ← hcB] at h1
        exact Nat.le_of_mul_le_mul_right h1 hp.pos

end Cases

end CFSG.StandardType
