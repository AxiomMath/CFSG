module

public import CFSG.Walter.Cited.HuppertBasic
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

namespace Lem22

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem frattini_map_le (P : Subgroup G) : (frattini ↥P).map P.subtype ≤ P := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit [Finite G] in
theorem conj_mem_frattini {P : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G))
    {f : G} (hf : f ∈ (frattini ↥P).map P.subtype) : g * f * g⁻¹ ∈ (frattini ↥P).map P.subtype := by
  have hmem : ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hmem' : ∀ x ∈ P, g⁻¹ * x * g ∈ P := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    rwa [inv_inv] at this
  let φ : ↥P ≃* ↥P :=
    { toFun := fun x => ⟨g * x * g⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  have hmap := Subgroup.characteristic_iff_map_eq.mp
    (inferInstance : (frattini ↥P).Characteristic) φ
  have h1 : φ f₀ ∈ frattini ↥P := by
    rw [← hmap]
    exact ⟨f₀, hf₀, rfl⟩
  exact ⟨φ f₀, h1, rfl⟩

variable {Q H P : Subgroup G}

theorem le_normalizer_frattini_sup (hPH : P ≤ H) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hQH : Q ≤ H) (hfr : ∀ g ∈ H, ∃ q ∈ Q, q * g ∈ Subgroup.normalizer (P : Set G)) :
    H ≤ Subgroup.normalizer
      (((frattini ↥P).map P.subtype ⊔ Q : Subgroup G) : Set G) := by
  intro g hg
  obtain ⟨q, hq, hqg⟩ := hfr g hg
  have hconjQ : ∀ x ∈ H, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHQ hx) y).mp hy
  refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
  have hΦQ : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (Q : Set G) :=
    (frattini_map_le P).trans (hPH.trans hHQ)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hΦQ] at hy
  obtain ⟨f, hf, o, ho, rfl⟩ := hy
  set m := q * g with hm
  have hgm : g = q⁻¹ * m := by rw [hm]; group
  have hmH : m ∈ H := H.mul_mem (hQH hq) hg
  have hmf : m * f * m⁻¹ ∈ (frattini ↥P).map P.subtype := conj_mem_frattini hqg hf
  have hmo : m * o * m⁻¹ ∈ Q := hconjQ m hmH o ho
  have hf' := hmf
  obtain ⟨f₁, -, hf₁⟩ := hf'
  have hf₁P : m * f * m⁻¹ ∈ P := hf₁ ▸ f₁.2
  have e : g * (f * o) * g⁻¹ =
      (m * f * m⁻¹) * ((m * f * m⁻¹)⁻¹ * q⁻¹ * (m * f * m⁻¹) * q) *
        (q⁻¹ * (m * o * m⁻¹) * q) := by
    rw [hgm]
    group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hmf)
    (Subgroup.mem_sup_right ?_)) (Subgroup.mem_sup_right ?_)
  · have h1 : (m * f * m⁻¹)⁻¹ * q⁻¹ * (m * f * m⁻¹) ∈ Q := by
      have := hconjQ (m * f * m⁻¹)⁻¹ (H.inv_mem (hPH hf₁P)) q⁻¹ (Q.inv_mem hq)
      simpa using this
    exact Q.mul_mem h1 hq
  · have := hconjQ q⁻¹ (H.inv_mem (hQH hq)) _ hmo
    simpa using this

omit [Finite G] in
theorem mem_of_mem_frattini_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) {x : G}
    (hx : x ∈ (frattini ↥P).map P.subtype ⊔ Q) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x ∈ Q := by
  have hΦQ : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (Q : Set G) :=
    (frattini_map_le P).trans hPQ
  rw [← SetLike.mem_coe, sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hΦQ] at hx
  obtain ⟨o, ho, f, hf, rfl⟩ := hx
  have hfP : f ∈ P := frattini_map_le P hf
  obtain ⟨j, hj⟩ := hPp ⟨f, hfP⟩
  have hj' : f ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨o', ho', he⟩ := A4.exists_pow_mul_eq ho (hΦQ hf) (p ^ j)
  have hpow : (o * f) ^ p ^ j ∈ Q := by
    rw [he, hj', mul_one]
    exact ho'
  have hcop : Nat.Coprime (orderOf (o * f)) (p ^ j) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxk)
      (Nat.coprime_pow_primes k j Nat.prime_two hp (Ne.symm hp2))
  exact B6.mem_of_pow_mem_of_coprime hpow hcop

omit [Finite G] in
theorem comm_mem_of_le_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P)
    (hPH : P ≤ H) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hHΦ : H ≤ Subgroup.normalizer (((frattini ↥P).map P.subtype ⊔ Q : Subgroup G) : Set G))
    {R : Subgroup G} (hR : IsPGroup 2 ↥R) (hRH : R ≤ H)
    (hΦR : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (R : Set G)) {r f : G}
    (hr : r ∈ R) (hf : f ∈ (frattini ↥P).map P.subtype) : r * f * r⁻¹ * f⁻¹ ∈ Q := by
  have hfr : f * r * f⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hΦR hf) r).mp hr
  have hy : f * r * f⁻¹ * r⁻¹ ∈ R := R.mul_mem hfr (R.inv_mem hr)
  obtain ⟨k, hk⟩ := hR ⟨_, hy⟩
  have hk' : (f * r * f⁻¹ * r⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hyΦ : f * r * f⁻¹ * r⁻¹ ∈ (frattini ↥P).map P.subtype ⊔ Q := by
    have h1 : r * f⁻¹ * r⁻¹ ∈ (frattini ↥P).map P.subtype ⊔ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHΦ (hRH hr)) f⁻¹).mp
        (Subgroup.mem_sup_left (Subgroup.inv_mem _ hf))
    have e : f * r * f⁻¹ * r⁻¹ = f * (r * f⁻¹ * r⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hf) h1
  have hyQ := mem_of_mem_frattini_sup hp hp2 hPp (hPH.trans hHQ) hyΦ hk'
  have e : r * f * r⁻¹ * f⁻¹ = (f * r * f⁻¹ * r⁻¹)⁻¹ := by group
  rw [e]
  exact Q.inv_mem hyQ

theorem comm_mem_of_mem' {K : Type*} [Group K] {O : Subgroup K} [O.Normal] {n t s x' o' : K}
    (h1 : t * n * t⁻¹ * n⁻¹ ∈ O) (h2 : s * n * s⁻¹ * n⁻¹ ∈ O) (h3 : t * s * t⁻¹ = x' * o')
    (ho' : o' ∈ O) : n * x' * n⁻¹ * x'⁻¹ ∈ O := by
  set φ := QuotientGroup.mk' O with hφ
  have hφ1 : ∀ y : K, φ y = 1 ↔ y ∈ O := fun y => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← hφ1]
  have e1 := (hφ1 _).mpr h1
  have e2 := (hφ1 _).mpr h2
  have e3 := (hφ1 _).mpr ho'
  have e4 := congrArg φ h3
  simp only [map_mul, map_inv] at e1 e2 e4 ⊢
  rw [e3, mul_one] at e4
  set N := φ n
  set A := φ t
  set B := φ s
  have htn : A * N = N * A := by
    calc A * N = (A * N * A⁻¹ * N⁻¹) * N * A := by group
      _ = N * A := by rw [e1, one_mul]
  have hsn : B * N = N * B := by
    calc B * N = (B * N * B⁻¹ * N⁻¹) * N * B := by group
      _ = N * B := by rw [e2, one_mul]
  have hAi : N * A⁻¹ = A⁻¹ * N := by
    calc N * A⁻¹ = A⁻¹ * (A * N) * A⁻¹ := by group
      _ = A⁻¹ * (N * A) * A⁻¹ := by rw [htn]
      _ = A⁻¹ * N := by group
  have hX : N * (A * B * A⁻¹) = (A * B * A⁻¹) * N := by
    calc N * (A * B * A⁻¹) = (N * A) * B * A⁻¹ := by group
      _ = (A * N) * B * A⁻¹ := by rw [htn]
      _ = A * (N * B) * A⁻¹ := by group
      _ = A * (B * N) * A⁻¹ := by rw [hsn]
      _ = A * B * (N * A⁻¹) := by group
      _ = A * B * (A⁻¹ * N) := by rw [hAi]
      _ = (A * B * A⁻¹) * N := by group
  rw [← e4, hX]
  group

variable {T L V : Subgroup G} {p : ℕ}

theorem eq_of_le_normalizer_of_not_le (h331 : Stmt3_3_1) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hp : p.Prime) (hp2 : p ≠ 2)
    (hPp : IsPGroup p ↥P) (hPH : P ≤ H) {S : Subgroup G} (hSP : S ≤ P)
    (hSM : ¬ S ≤ Subgroup.normalizer (L : Set G))
    (hTS : T ≤ Subgroup.normalizer ((S ⊔ pCoreOf 2 H : Subgroup G) : Set G)) : S = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  set N₂ := S ⊔ pCoreOf 2 H with hN₂
  have hN₂H : N₂ ≤ H := sup_le (hSP.trans hPH) (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hK : N₂ ⊔ T = H := by
    refine hmin.eq_of_not_le le_sup_right (sup_le hN₂H hTH) fun hle => hSM ?_
    intro x hx
    exact (hle (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))).2
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left N₂ T hTS
  have hSQ : S ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (hSP.trans hPH).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hset2 := Subgroup.coe_mul_of_left_le_normalizer_right S (pCoreOf 2 H) hSQ
  refine le_antisymm hSP fun x hx => ?_
  have hxK : x ∈ ((N₂ ⊔ T : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, hK]
    exact hPH hx
  rw [hset] at hxK
  obtain ⟨n, hn, t, ht, hnt⟩ := hxK
  have hnt' : n * t = x := hnt
  obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨n', hn', hpow⟩ := A4.exists_pow_mul_eq hn (hTS ht) (p ^ k)
  have htN : t ^ p ^ k ∈ N₂ := by
    have e : t ^ p ^ k = n'⁻¹ := by
      rw [hnt', hk'] at hpow
      exact (eq_inv_of_mul_eq_one_right hpow.symm)
    rw [e]
    exact N₂.inv_mem hn'
  obtain ⟨j, hj⟩ := hT2 ⟨t, ht⟩
  have hj' : t ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (orderOf t) (p ^ k) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hj')
      (Nat.coprime_pow_primes j k Nat.prime_two hp (Ne.symm hp2))
  have htN₂ : t ∈ N₂ := B6.mem_of_pow_mem_of_coprime htN hcop
  have hxN : x ∈ ((S ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    rw [← hnt']
    exact N₂.mul_mem hn htN₂
  rw [hset2] at hxN
  obtain ⟨s, hs, q, hq, hsq⟩ := hxN
  have hsq' : s * q = x := hsq
  have hqP : q ∈ P := by
    have e : q = s⁻¹ * x := by rw [← hsq']; group
    rw [e]
    exact P.mul_mem (P.inv_mem (hSP hs)) hx
  have hq1 : q = 1 :=
    eq_one_of_mem_of_mem hp hp2 hPp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hqP hq
  rw [← hsq', hq1, mul_one]
  exact hs

theorem le_pCoreOf_L (hyp : Hyp1223 G T L V) (hVT : V ≤ T) (hV2 : ∀ x ∈ V, x ^ 2 = 1) :
    V ≤ pCoreOf 2 L := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVL : V ≤ L := by
    have h1 : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
    rw [← h1, Subgroup.commutator_le]
    intro a ha b hb
    have hab : a * b * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hyp.normalizes (hVT ha)) b).mp hb
    rw [commutatorElement_def]
    exact L.mul_mem hab (L.inv_mem hb)
  have hVp : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hV2 x x.2)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLV hVp

theorem exists_inv_conj_frattini (h331 : Stmt3_3_1) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hsol : Group.IsSolvable ↥H)
    (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hPH : P ≤ H)
    (hPi : ¬ p ∣ P.relIndex H) (hHPT : H = P ⊔ T)
    (hPΦ : P ⊓ Subgroup.normalizer (L : Set G) = (frattini ↥P).map P.subtype)
    (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hVL : V ≤ pCoreOf 2 L)
    (hidx : (V ⊓ pCoreOf 2 H).relIndex V = 2) (hP1 : P ≠ ⊥) {v : G} (hvV : v ∈ V)
    (hv2 : v ^ 2 = 1) (hvO : v ∉ pCoreOf 2 H) :
    ∃ n : G, n * v⁻¹ ∈ pCoreOf 2 H ∧ n ∈ Subgroup.normalizer (P : Set G) ∧
      (∀ f ∈ (frattini ↥P).map P.subtype, n * f = f * n) ∧
      ∀ x ∈ P, n * x * n⁻¹ * x ∈ (frattini ↥P).map P.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p ↥P) := ⟨hPp⟩
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hvH : v ∈ H := hTH (hVT hvV)
  have hO2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hOH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hconjO : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHO hg) y).mp hy
  have hPO : ∀ y ∈ P, y ∈ Q → y = 1 := fun y hyP hyO =>
    eq_one_of_mem_of_mem hp hp2 hPp hO2 hyP hyO
  have hΦP : Φ ≤ P := frattini_map_le P
  have hΦL : Φ ≤ Subgroup.normalizer (L : Set G) := by
    show Φ ≤ _
    rw [← hPΦ]
    exact inf_le_right
  have hfr : ∀ g ∈ H, ∃ q ∈ Q, q * g ∈ Subgroup.normalizer (P : Set G) := fun g hg =>
    exists_mul_mem_normalizer h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hg
  have hHΦ := le_normalizer_frattini_sup hPH hHO hOH hfr
  have hPΦQ : ∀ w ∈ P, w ∈ Φ ⊔ Q → w ∈ Φ := by
    intro w hwP hw
    have hΦQ : Φ ≤ Subgroup.normalizer (Q : Set G) := hΦP.trans (hPH.trans hHO)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hΦQ] at hw
    obtain ⟨f, hf, o, ho, hfo⟩ := hw
    have hfo' : f * o = w := hfo
    have hoP : o ∈ P := by
      have e : o = f⁻¹ * w := by rw [← hfo']; group
      rw [e]
      exact P.mul_mem (P.inv_mem (hΦP hf)) hwP
    rw [← hfo', hPO o hoP ho, mul_one]
    exact hf
  obtain ⟨q, hq, hqv⟩ := hfr v hvH
  obtain ⟨n, hn⟩ : ∃ n : G, n = q * v := ⟨_, rfl⟩
  rw [← hn] at hqv
  have hqH : q ∈ H := hOH hq
  have hnH : n ∈ H := hn ▸ H.mul_mem hqH hvH
  have hnP : ∀ x ∈ P, n * x * n⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hqv x).mp hx
  have hn2O : n * n ∈ Q := by
    have e : n * n = q * (v * q * v⁻¹) * (v * v) := by rw [hn]; group
    rw [e, ← pow_two v, hv2, mul_one]
    exact Subgroup.mul_mem _ hq (hconjO v hvH q hq)
  have hn2c : ∀ x ∈ P, (n * n) * x * (n * n)⁻¹ = x := by
    intro x hx
    have h1 : (n * n) * x * (n * n)⁻¹ * x⁻¹ ∈ P := by
      have e : (n * n) * x * (n * n)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := by group
      rw [e]
      exact P.mul_mem (hnP _ (hnP x hx)) (P.inv_mem hx)
    have h2 : (n * n) * x * (n * n)⁻¹ * x⁻¹ ∈ Q := by
      have e : (n * n) * x * (n * n)⁻¹ * x⁻¹ = (n * n) * (x * (n * n)⁻¹ * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hn2O (hconjO x (hPH hx) _ (Subgroup.inv_mem _ hn2O))
    exact mul_inv_eq_one.mp (hPO _ h1 h2)
  have htn : ∀ t ∈ T, t * n * t⁻¹ * n⁻¹ ∈ Q := by
    intro t ht
    have htv : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV ht) v).mp hvV
    have htvO : t * v * t⁻¹ ∉ Q := fun h0 => hvO (by
      have := hconjO t⁻¹ (H.inv_mem (hTH ht)) _ h0
      simpa [mul_assoc] using this)
    have hmul : t * v * t⁻¹ * v⁻¹ ∈ Q := by
      have h1 : (⟨t * v * t⁻¹, htv⟩ : ↥V) * ⟨v⁻¹, V.inv_mem hvV⟩ ∈
          (V ⊓ pCoreOf 2 H).subgroupOf V := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        refine iff_of_false (fun h0 => htvO (Subgroup.mem_subgroupOf.mp h0).2) fun h0 => hvO ?_
        have := Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp h0).2
        simpa using this
      exact (Subgroup.mem_subgroupOf.mp h1).2
    have e : t * n * t⁻¹ * n⁻¹ = (t * q * t⁻¹) * (t * v * t⁻¹ * v⁻¹) * q⁻¹ := by
      rw [hn]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hconjO t (hTH ht) q hq) hmul)
      (Subgroup.inv_mem _ hq)
  set R := pCoreOf 2 L ⊓ H with hR
  have hR2 : IsPGroup 2 ↥R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left
  have hΦR : Φ ≤ Subgroup.normalizer (R : Set G) := fun f hf =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hΦL hf),
        Subgroup.le_normalizer (hPH (hΦP hf))⟩
  have hcomm : ∀ f ∈ Φ, n * f = f * n := by
    intro f hf
    have h1 : v * f * v⁻¹ * f⁻¹ ∈ Q :=
      comm_mem_of_le_normalizer hp hp2 hPp hPH hHO hHΦ hR2 inf_le_right hΦR ⟨hVL hvV, hvH⟩ hf
    have h2 : n * f * n⁻¹ * f⁻¹ ∈ Q := by
      have e : n * f * n⁻¹ * f⁻¹ = q * (v * f * v⁻¹ * f⁻¹) * (f * q⁻¹ * f⁻¹) := by
        rw [hn]; group
      rw [e]
      exact Q.mul_mem (Q.mul_mem hq h1) (hconjO f (hPH (hΦP hf)) _ (Q.inv_mem hq))
    have h3 : n * f * n⁻¹ * f⁻¹ ∈ P := P.mul_mem (hnP f (hΦP hf)) (P.inv_mem (hΦP hf))
    have h4 := hPO _ h3 h2
    calc n * f = (n * f * n⁻¹ * f⁻¹) * f * n := by group
      _ = f * n := by rw [h4, one_mul]
  let S : Subgroup G :=
    { carrier := {x | x ∈ P ∧ n * x * n⁻¹ * x⁻¹ ∈ Φ}
      one_mem' := ⟨P.one_mem, by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨P.mul_mem hx.1 hy.1, by
        have e : n * (x * y) * n⁻¹ * (x * y)⁻¹ =
            (n * x * n⁻¹ * x⁻¹) * (x * (n * y * n⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact Φ.mul_mem hx.2 (conj_mem_frattini (Subgroup.le_normalizer hx.1) hy.2)⟩
      inv_mem' := fun {x} hx => ⟨P.inv_mem hx.1, by
        have e : n * x⁻¹ * n⁻¹ * x⁻¹⁻¹ =
            (n * x⁻¹ * n⁻¹) * (n * x * n⁻¹ * x⁻¹)⁻¹ * (n * x⁻¹ * n⁻¹)⁻¹ := by group
        rw [e]
        exact conj_mem_frattini (Subgroup.le_normalizer (hnP _ (P.inv_mem hx.1)))
          (Φ.inv_mem hx.2)⟩ }
  have hSP : S ≤ P := fun x hx => hx.1
  have hΦS : Φ ≤ S := fun f hf => ⟨hΦP hf, by
    have : n * f * n⁻¹ * f⁻¹ = 1 := by rw [hcomm f hf]; group
    rw [this]
    exact Φ.one_mem⟩
  have hOn : (((Φ ⊔ Q : Subgroup G)).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (sup_le (hΦP.trans hPH) hOH)).mpr hHΦ
  have hTS : T ≤ Subgroup.normalizer ((S ⊔ Q : Subgroup G) : Set G) := by
    intro t ht
    have htH := hTH ht
    refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
    have hSQ : S ≤ Subgroup.normalizer (Q : Set G) := (hSP.trans hPH).trans hHO
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right S Q hSQ
    rw [← SetLike.mem_coe, hset] at hy
    obtain ⟨s, hs, o, ho, hso⟩ := hy
    have hso' : s * o = y := hso
    have hts : t * s * t⁻¹ ∈ P ⊔ Q :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_sup h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 htH) s).mp
        (Subgroup.mem_sup_left hs.1)
    have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hPH.trans hHO
    have hset2 := Subgroup.coe_mul_of_left_le_normalizer_right P Q hPQ
    rw [← SetLike.mem_coe, hset2] at hts
    obtain ⟨x', hx', o', ho', hxo⟩ := hts
    have hxo' : x' * o' = t * s * t⁻¹ := hxo
    have hx'S : x' ∈ S := by
      refine ⟨hx', ?_⟩
      have hsH := hPH hs.1
      have hx'H := hPH hx'
      have hsn : s * n * s⁻¹ * n⁻¹ ∈ Φ ⊔ Q := by
        have e : s * n * s⁻¹ * n⁻¹ = (n * s * n⁻¹ * s⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.mem_sup_left (Φ.inv_mem hs.2)
      have hw : (⟨n, hnH⟩ : ↥H) * ⟨x', hx'H⟩ * (⟨n, hnH⟩ : ↥H)⁻¹ * (⟨x', hx'H⟩ : ↥H)⁻¹ ∈
          (Φ ⊔ Q).subgroupOf H :=
        comm_mem_of_mem' (O := (Φ ⊔ Q).subgroupOf H) (o' := ⟨o', hOH ho'⟩)
          (t := ⟨t, htH⟩) (s := ⟨s, hsH⟩)
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (htn t ht)))
          (Subgroup.mem_subgroupOf.mpr hsn) (Subtype.ext hxo'.symm)
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ho'))
      have hwO : n * x' * n⁻¹ * x'⁻¹ ∈ Φ ⊔ Q := Subgroup.mem_subgroupOf.mp hw
      exact hPΦQ _ (P.mul_mem (hnP x' hx') (P.inv_mem hx')) hwO
    have e : t * y * t⁻¹ = (t * s * t⁻¹) * (t * o * t⁻¹) := by
      rw [← hso']
      group
    rw [e, ← hxo', mul_assoc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx'S)
      (Subgroup.mem_sup_right (Subgroup.mul_mem _ ho' (hconjO t htH o ho)))
  have hSΦ : S ≤ Φ := by
    by_contra hne
    have hSM : ¬ S ≤ Subgroup.normalizer (L : Set G) := fun hle => hne fun x hx => by
      show x ∈ Φ
      rw [← hPΦ]
      exact ⟨hx.1, hle hx⟩
    have hSPeq := eq_of_le_normalizer_of_not_le h331 hyp hHs hp hp2 hPp hPH hSP hSM hTS
    have hinvP : ∀ x ∈ P, n⁻¹ * x * n ∈ P := fun x hx => by
      have h1 : (n * n)⁻¹ * x * (n * n) = x := by
        have h2 := hn2c x hx
        calc (n * n)⁻¹ * x * (n * n) = (n * n)⁻¹ * ((n * n) * x * (n * n)⁻¹) * (n * n) := by
              rw [h2]
          _ = x := by group
      have e : n⁻¹ * x * n = n * ((n * n)⁻¹ * x * (n * n)) * n⁻¹ := by group
      rw [e, h1]
      exact hnP x hx
    let τ : MulAut ↥P :=
      { toFun := fun x => ⟨n * x * n⁻¹, hnP x x.2⟩
        invFun := fun x => ⟨n⁻¹ * x * n, hinvP x x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          group) }
    have hτ : ∀ x : ↥P, ((τ x : ↥P) : G) = n * x * n⁻¹ := fun _ => rfl
    have hτ2 : τ ^ 2 = 1 := by
      ext x
      rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
      show n * (n * (x : G) * n⁻¹) * n⁻¹ = x
      have := hn2c x x.2
      calc n * (n * (x : G) * n⁻¹) * n⁻¹ = (n * n) * x * (n * n)⁻¹ := by group
        _ = x := this
    have hcop : Nat.Coprime p (orderOf τ) := by
      have hdvd : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one hτ2
      exact Nat.Coprime.coprime_dvd_right hdvd
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hfrat : CFSG.Walter.Huppert.frattiniAut ↥P τ = 1 := by
      ext y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [CFSG.Walter.Huppert.frattiniAut_mk, MulAut.one_apply, QuotientGroup.eq]
      have hxS : (x : G) ∈ S := by rw [hSPeq]; exact x.2
      obtain ⟨f₀, hf₀, hf₀e⟩ := hxS.2
      have hmem : (τ x)⁻¹ * x ∈ frattini ↥P := by
        have e : (τ x)⁻¹ * x = (x : ↥P)⁻¹ * f₀⁻¹ * x := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ]
          rw [show ((f₀ : ↥P) : G) = n * x * n⁻¹ * (x : G)⁻¹ from hf₀e]
          group
        rw [e]
        have := (inferInstance : (frattini ↥P).Normal).conj_mem _ (Subgroup.inv_mem _ hf₀)
          (x : ↥P)⁻¹
        simpa [mul_assoc] using this
      exact hmem
    have hτ1 := CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one hPp hcop hfrat
    have hxn : ∀ x ∈ P, x * n = n * x := by
      intro x hx
      have := congrArg (fun σ : MulAut ↥P => ((σ ⟨x, hx⟩ : ↥P) : G)) hτ1
      simp only [MulAut.one_apply, hτ] at this
      calc x * n = (n * x * n⁻¹) * n := by rw [this]
        _ = n * x := by group
    have hxv : ∀ x ∈ P, x * v * x⁻¹ * v⁻¹ ∈ Q := by
      intro x hx
      have hv : v = q⁻¹ * n := by rw [hn]; group
      have e : x * v * x⁻¹ * v⁻¹ = (x * q⁻¹ * x⁻¹) * q := by
        rw [hv]
        calc x * (q⁻¹ * n) * x⁻¹ * (q⁻¹ * n)⁻¹ = x * q⁻¹ * x⁻¹ * (x * n) * x⁻¹ * n⁻¹ * q := by
              group
          _ = x * q⁻¹ * x⁻¹ * (n * x) * x⁻¹ * n⁻¹ * q := by rw [hxn x hx]
          _ = (x * q⁻¹ * x⁻¹) * q := by group
      rw [e]
      exact Subgroup.mul_mem _ (hconjO x (hPH hx) _ (Subgroup.inv_mem _ hq)) hq
    set Y := Q ⊔ V with hY
    have hYT : Y ≤ T := sup_le (pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow) hVT
    have hYp : IsPGroup 2 ↥Y := hmin.isSylow.2.1.to_le hYT
    have hYH : Y ≤ H := hYT.trans hTH
    have hPY : P ≤ Subgroup.normalizer (Y : Set G) := by
      intro x hx
      have hxH := hPH hx
      have hmapY : Y.map (MulAut.conj x).toMonoidHom ≤ Y := by
        rw [hY, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨w, hw, rfl⟩
          exact Subgroup.mem_sup_left (hconjO x hxH w hw)
        · rintro _ ⟨w, hw, rfl⟩
          show x * w * x⁻¹ ∈ Y
          by_cases hwO : w ∈ Q
          · exact Subgroup.mem_sup_left (hconjO x hxH w hwO)
          · have h1 : (⟨w, hw⟩ : ↥V) * ⟨v⁻¹, V.inv_mem hvV⟩ ∈
                (V ⊓ pCoreOf 2 H).subgroupOf V := by
              rw [Subgroup.mul_mem_iff_of_index_two hidx]
              refine iff_of_false (fun h0 => hwO (Subgroup.mem_subgroupOf.mp h0).2)
                fun h0 => hvO ?_
              have := Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp h0).2
              simpa using this
            have hwv : w * v⁻¹ ∈ Q := (Subgroup.mem_subgroupOf.mp h1).2
            have e : x * w * x⁻¹ = (x * (w * v⁻¹) * x⁻¹) * (x * v * x⁻¹ * v⁻¹) * v := by
              group
            rw [e]
            exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
              (hconjO x hxH _ hwv) (hxv x hx))) (Subgroup.mem_sup_right hvV)
      exact Sec121Swap.mem_normalizer_of_conj_mem fun y hy => hmapY ⟨y, hy, rfl⟩
    have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
      Lem21Post.mem_normalizer_sup (hHO (hTH ht)) (hTV ht)
    have hHY : H ≤ Subgroup.normalizer (Y : Set G) := by
      rw [hHPT]
      exact sup_le hPY hTY
    have hYO : Y ≤ Q :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYH hHY hYp
    exact hvO (hYO (Subgroup.mem_sup_right hvV))
  refine ⟨n, by rw [hn, mul_inv_cancel_right]; exact hq, hqv, hcomm, fun x hx => ?_⟩
  have hnx := hnP x hx
  have hyS : x * (n * x * n⁻¹) ∈ S := by
    refine ⟨P.mul_mem hx hnx, ?_⟩
    have e : n * (x * (n * x * n⁻¹)) * n⁻¹ * (x * (n * x * n⁻¹))⁻¹ =
        (n * x * n⁻¹) * x * (n * x * n⁻¹)⁻¹ * x⁻¹ := by
      calc n * (x * (n * x * n⁻¹)) * n⁻¹ * (x * (n * x * n⁻¹))⁻¹
          = (n * x * n⁻¹) * ((n * n) * x * (n * n)⁻¹) * (x * (n * x * n⁻¹))⁻¹ := by group
        _ = (n * x * n⁻¹) * x * (x * (n * x * n⁻¹))⁻¹ := by rw [hn2c x hx]
        _ = (n * x * n⁻¹) * x * (n * x * n⁻¹)⁻¹ * x⁻¹ := by group
    rw [e]
    have hc : ⁅(⟨n * x * n⁻¹, hnx⟩ : ↥P), (⟨x, hx⟩ : ↥P)⁆ ∈ frattini ↥P :=
      CFSG.commutator_le_frattini_of_isPGroup (p := p)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    refine ⟨_, hc, ?_⟩
    simp [commutatorElement_def]
  have hyΦ := hSΦ hyS
  have e : n * x * n⁻¹ * x = x⁻¹ * (x * (n * x * n⁻¹)) * x⁻¹⁻¹ := by group
  rw [e]
  exact conj_mem_frattini (Subgroup.le_normalizer (P.inv_mem hx)) hyΦ

end Lem22

end CFSG.Quasithin.H13
