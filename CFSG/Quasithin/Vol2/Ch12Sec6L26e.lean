module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26d
public import CFSG.Goldschmidt.Steps.AxB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open CFSG.Blueprint CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F Equiv
open scoped IsMulCommutative

namespace S126L26

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_inverted {H X Q : Subgroup G} (hQH : H ≤ Subgroup.normalizer (Q : Set G))
    (hXH : H ≤ Subgroup.normalizer (X : Set G)) {r : ℕ} (hXr : ∀ x ∈ X, ∃ n : ℕ, x ^ r ^ n ∈ Q)
    {v c : G} (hvH : v ∈ H) (hv2 : v * v = 1) (hcX : c ∈ X) (hcH : c ∈ H)
    (hvc : v * c * v⁻¹ * c⁻¹ ∉ Q) :
    ∃ k : ℕ, v * (c⁻¹ * v * c * v⁻¹) ^ r ^ k * v⁻¹ = ((c⁻¹ * v * c * v⁻¹) ^ r ^ k)⁻¹ ∧
      (c⁻¹ * v * c * v⁻¹) ^ r ^ k ∉ Q ∧ ((c⁻¹ * v * c * v⁻¹) ^ r ^ k) ^ r ∈ Q := by
  classical
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hd0X : c⁻¹ * v * c * v⁻¹ ∈ X := by
    have h1 : v * c * v⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXH hvH) c).mp hcX
    have e : c⁻¹ * v * c * v⁻¹ = c⁻¹ * (v * c * v⁻¹) := by group
    rw [e]
    exact X.mul_mem (X.inv_mem hcX) h1
  generalize hd0 : c⁻¹ * v * c * v⁻¹ = d₀ at hd0X ⊢
  have hinv0 : v * d₀ * v⁻¹ = d₀⁻¹ := by
    rw [← hd0, hvinv]
    calc v * (c⁻¹ * v * c * v) * v = v * c⁻¹ * v * c * (v * v) := by group
      _ = v * c⁻¹ * v * c := by rw [hv2, mul_one]
      _ = (c⁻¹ * v * c * v)⁻¹ := by simp only [mul_inv_rev, inv_inv, hvinv, mul_assoc]
  have hd0Q : d₀ ∉ Q := by
    intro hd
    apply hvc
    have h1 : c * d₀ * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQH hcH) d₀).mp hd
    have e : v * c * v⁻¹ * c⁻¹ = c * d₀ * c⁻¹ := by rw [← hd0]; group
    rw [e]
    exact h1
  obtain ⟨n, hn⟩ := hXr d₀ hd0X
  have hex : ∃ n : ℕ, d₀ ^ r ^ n ∈ Q := ⟨n, hn⟩
  set n₀ := Nat.find hex with hn₀
  have hn₀Q : d₀ ^ r ^ n₀ ∈ Q := Nat.find_spec hex
  have hn₀pos : n₀ ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hn₀Q
    exact hd0Q hn₀Q
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn₀pos
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [← conj_pow, hinv0, inv_pow]
  · intro hk'
    have := Nat.find_min hex (show k < n₀ by omega)
    exact this hk'
  · rw [← pow_mul, ← pow_succ, show k + 1 = n₀ by omega]
    exact hn₀Q

theorem exists_comm_P {H X P V : Subgroup G} (hXH : X ≤ H)
    (hXn : H ≤ Subgroup.normalizer (X : Set G)) (hX3 : ∀ x ∈ X, ∃ n : ℕ, x ^ 3 ^ n ∈ pCoreOf 2 H)
    (hPH : P ≤ H) (hP3 : IsPGroup 3 ↥P) (hVH : V ≤ H) (hV2 : IsPGroup 2 ↥V)
    (hVP : ∀ v ∈ V, ∀ a ∈ P, v * a * v⁻¹ * a⁻¹ ∈ pCoreOf 2 H)
    (hne : ∃ v ∈ V, ∃ x ∈ X, v * x * v⁻¹ * x⁻¹ ∉ pCoreOf 2 H) :
    ∃ v ∈ V, ∃ c ∈ X, (∀ a ∈ P, c * a * c⁻¹ * a⁻¹ ∈ pCoreOf 2 H) ∧
      v * c * v⁻¹ * c⁻¹ ∉ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := pCoreOf 2 H with hQdef
  have hQH : Q ≤ H := pCoreOf_le 2 H
  let N : Subgroup ↥H := Q.subgroupOf H
  have hNn : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr (le_normalizer_pCoreOf 2 H)
  let π : ↥H →* ↥H ⧸ N := QuotientGroup.mk' N
  have hπ1 : ∀ y : ↥H, π y = 1 ↔ (y : G) ∈ Q := fun y =>
    (QuotientGroup.eq_one_iff y).trans Subgroup.mem_subgroupOf
  have hπc : ∀ a b : ↥H, π a * π b = π b * π a ↔
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ Q := by
    intro a b
    have e : ((a * b * a⁻¹ * b⁻¹ : ↥H) : G) = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ := rfl
    rw [← e, ← hπ1, map_mul, map_mul, map_mul, map_inv, map_inv]
    constructor
    · intro e
      rw [e]
      group
    · intro e
      calc π a * π b = π a * π b * (π a)⁻¹ * (π b)⁻¹ * (π b * π a) := by group
        _ = π b * π a := by rw [e, one_mul]
  set Pb := (X.subgroupOf H).map π with hPb
  set Rb := (V.subgroupOf H).map π with hRb
  set Bb := (P.subgroupOf H).map π with hBb
  have hPb3 : IsPGroup 3 ↥Pb := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    obtain ⟨n, hn⟩ := hX3 x hx
    refine ⟨n, Subtype.ext ?_⟩
    show π x ^ 3 ^ n = 1
    rw [← map_pow, hπ1]
    exact hn
  have hRb2 : Nat.Coprime (Nat.card ↥Rb) 3 := by
    have h2 : IsPGroup 2 ↥(V.subgroupOf H) :=
      hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
    obtain ⟨k, hk⟩ := (h2.map π).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (by norm_num)
  have hBb3 : IsPGroup 3 ↥Bb := by
    have h3 : IsPGroup 3 ↥(P.subgroupOf H) :=
      hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
    exact h3.map π
  have hnorm : ∀ y ∈ (⊤ : Subgroup ↥H).map π, y ∈ Subgroup.normalizer (Pb : Set (↥H ⧸ N)) := by
    rintro _ ⟨y, -, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨y * x * y⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp (hXn y.2) x).mp hx
    · rintro ⟨x, hx, hxe⟩
      refine ⟨y⁻¹ * x * y, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hXn (H.inv_mem y.2)) x).mp hx
        refine Subgroup.mem_subgroupOf.mpr ?_
        simpa [mul_assoc] using this
      · have : π x = π y * w * (π y)⁻¹ := hxe
        simp only [map_mul, map_inv, this]
        group
  have hRbN : Rb ≤ Subgroup.normalizer (Pb : Set (↥H ⧸ N)) := fun y hy =>
    hnorm y (Subgroup.map_mono le_top hy)
  have hBbN : Bb ≤ Subgroup.normalizer (Pb : Set (↥H ⧸ N)) := fun y hy =>
    hnorm y (Subgroup.map_mono le_top hy)
  have hRB : ⁅Rb, Bb⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact ((hπc a v).2 (by
      have := (pCoreOf 2 H).inv_mem (hVP v hv a ha)
      convert this using 1
      group))
  by_contra hcon
  push Not at hcon
  have key := CFSG.Goldschmidt.N10 (↥H ⧸ N) Pb Rb Bb hPb3 hRb2 hBb3 hRbN hBbN hRB (by
    rintro y ⟨⟨c, hc, rfl⟩, hcB⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have hcP : ∀ a ∈ P, (c : G) * a * (c : G)⁻¹ * a⁻¹ ∈ pCoreOf 2 H := by
      intro a ha
      have h1 := Subgroup.mem_centralizer_iff.mp hcB (π ⟨a, hPH ha⟩) ⟨⟨a, hPH ha⟩, ha, rfl⟩
      have h2 := (hπc ⟨a, hPH ha⟩ c).1 h1
      have := (pCoreOf 2 H).inv_mem h2
      convert this using 1
      group
    exact (hπc v c).2 (hcon (v : G) hv (c : G) hc hcP))
  obtain ⟨v, hv, x, hx, hvx⟩ := hne
  have hxP : π ⟨x, hXH hx⟩ ∈ Pb := ⟨⟨x, hXH hx⟩, hx, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.mp (key hxP) (π ⟨v, hVH hv⟩) ⟨⟨v, hVH hv⟩, hv, rfl⟩
  exact hvx ((hπc ⟨v, hVH hv⟩ ⟨x, hXH hx⟩).1 h1)

omit [Finite G] in
theorem mem_of_pow_mem {Q : Subgroup G} {d : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : d ^ a ∈ Q) (hb : d ^ b ∈ Q) : d ∈ Q := by
  have h1 : d = d ^ ((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b) := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hab]
    simp
  rw [h1, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  exact Q.mul_mem (Q.zpow_mem ha _) (Q.zpow_mem hb _)

section Frame

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem V_le_K (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) :
    V ≤ centralizerMod (pCoreOf 2 H) H (Li L F.V1) := by
  obtain ⟨h, hidx, -, -, -⟩ := setup126 h1224 F hH hZ hHz
  obtain ⟨-, hXV, -, hXV5⟩ := S126L24.sup_le_normalizers h1222 F hH
  have hVpQ : F.V5 ≤ pCoreOf 2 H := h.Vp_le_pCoreOf_and_commutator_le.1
  exact fun v hv => ⟨h.V_le_H hv, le_normalizer_pCoreOf 2 H (h.V_le_H hv),
    fun l hl => hVpQ (comm_mem_Vp hidx hv (hXV (Subgroup.mem_sup_left hl))
      (hXV5 (Subgroup.mem_sup_left hl)))⟩

theorem centralizes_of_ne_five (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {X : Subgroup G} (hXH : X ≤ H)
    (hXn : H ≤ Subgroup.normalizer (X : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr5 : r ≠ 5) (hXr : ∀ x ∈ X, ∃ n : ℕ, x ^ r ^ n ∈ pCoreOf 2 H) :
    ∀ v ∈ V, ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀, x₀, hx₀, hvx₀⟩ := hcon
  obtain ⟨h, hidx, hyp5, hcard, hC⟩ := setup126 h1224 F hH hZ hHz
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hv2 : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact isElemAbelian_pow_eq_one h.elemAbelian hv
  have hnotQ : ∀ {v x : G}, x ∈ H → v * x * v⁻¹ * x⁻¹ ∉ pCoreOf 2 H → v ∉ pCoreOf 2 H := by
    intro v x hx hvx hvQ
    apply hvx
    have h1 : x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hQn hx) _).mp ((pCoreOf 2 H).inv_mem hvQ)
    have e : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hvQ h1
  have hv₀Q : v₀ ∉ pCoreOf 2 H := hnotQ (hXH hx₀) hvx₀
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hv₀Q (hle hv₀)
  by_cases hr3 : r = 3
  · subst hr3
    have hL1H : Li L F.V1 ≤ H := le_sup_left.trans h.L₁T_le_H
    have hVK := V_le_K h1222 h1224 F hH hZ hHz
    obtain ⟨P, hPL1, hP, hcP⟩ := exists_E9 h1222 F hH
    have hVP : ∀ v ∈ V, ∀ a ∈ P, v * a * v⁻¹ * a⁻¹ ∈ pCoreOf 2 H := fun v hv a ha =>
      (hVK hv).2.2 a (hPL1 ha)
    obtain ⟨v, hv, c, hcX, hcP', hvc⟩ := exists_comm_P hXH hXn hXr (hPL1.trans hL1H)
      (isPGroup_of_isElemAbelian hP) h.V_le_H h.isPGroup_V hVP ⟨v₀, hv₀, x₀, hx₀, hvx₀⟩
    obtain ⟨k, hinv, hdQ, hd3⟩ := exists_inverted hQn hXn hXr (h.V_le_H hv) (hv2 v hv) hcX
      (hXH hcX) hvc
    have hcS : c ∈ centralizerMod (pCoreOf 2 H) H P := ⟨hXH hcX, hQn (hXH hcX), hcP'⟩
    have hvS : v ∈ centralizerMod (pCoreOf 2 H) H P :=
      ⟨h.V_le_H hv, hQn (h.V_le_H hv), hVP v hv⟩
    have hdS : (c⁻¹ * v * c * v⁻¹) ^ 3 ^ k ∈ centralizerMod (pCoreOf 2 H) H P :=
      Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ hcS) hvS) hcS) (Subgroup.inv_mem _ hvS)) _
    have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple
      hH.hyp.nonabelian hHz.1.2
    refine false_of_e27 hSQ (hPL1.trans hL1H) hP hcP hdS.1 (h.V_le_H hv) hd3 hdQ hdS.2.2
      (hVP v hv) ?_
    rw [hinv, inv_mul_cancel]
    exact (pCoreOf 2 H).one_mem
  · obtain ⟨k, hinv, hdQ, hdr⟩ := exists_inverted hQn hXn hXr (h.V_le_H hv₀) (hv2 v₀ hv₀) hx₀
      (hXH hx₀) hvx₀
    generalize hd : (x₀⁻¹ * v₀ * x₀ * v₀⁻¹) ^ r ^ k = d at hinv hdQ hdr
    have hdH : d ∈ H := by
      rw [← hd]
      exact H.pow_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem (hXH hx₀)) (h.V_le_H hv₀))
        (hXH hx₀)) (H.inv_mem (h.V_le_H hv₀))) _
    obtain ⟨m, hm⟩ := hr.odd_of_ne_two hr2
    have hodd : d ^ (2 * m + 1) ∈ pCoreOf 2 H := by rw [← hm]; exact hdr
    have hvd : v₀ * d * v₀⁻¹ * d ∈ pCoreOf 2 H := by
      rw [hinv, inv_mul_cancel]
      exact (pCoreOf 2 H).one_mem
    rcases inverted_pow_mem h hidx hyp5 hcard hC hv₀ hv₀Q hdH hvd hodd with h3 | h5
    · exact hdQ (mem_of_pow_mem ((Nat.coprime_primes Nat.prime_three hr).mpr (Ne.symm hr3))
        h3 hdr)
    · exact hdQ (mem_of_pow_mem ((Nat.coprime_primes (by norm_num) hr).mpr (Ne.symm hr5))
        h5 hdr)

end Frame

end S126L26

end CFSG.Quasithin.H13
