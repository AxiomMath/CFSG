module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zf

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  (s : Set714 G T L V t z)
include s

theorem exists_x
    (h1222 : Stmt12_2_2) :
    ∃ x : G, x ∈ L ∧ x ^ 3 = 1 ∧ x ∈ Subgroup.normalizer (V1 T L V : Set G) ∧
      x ∉ Subgroup.centralizer (V1 T L V : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := s.setting.hyp
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  obtain ⟨-, hset, -, -⟩ := S127.Mod.lemma12_7_2_five h1222 h
  have hXmem : XOf L ∈ {I : Subgroup G | I ≤ P1 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
      oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} := by
    rw [hset]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨-, -, -, hX3⟩ := hXmem
  have h3X : 3 ∣ Nat.card (XOf L) := by
    rw [← hX3]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card (H := pCoreOf 2 (XOf L)) (K := XOf L))
  obtain ⟨⟨x, hxX⟩, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3X
  rw [Subgroup.orderOf_mk] at hx3
  have hxL : x ∈ L := XOf_le L hxX
  have hxV : x ∉ Subgroup.centralizer (V : Set G) := by
    intro hc
    have hxO : x ∈ pCoreOf 2 L := by
      rw [← S127.inf_centralizer_eq_of_1222 h1222 h]
      exact ⟨hxL, hc⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨x, hxO⟩
    have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hn)
    rw [hx3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hpt := (S127.Mod.lemma12_7_2_two h1222 h).1
  refine ⟨x, hxL, by rw [← hx3]; exact pow_orderOf_eq_one x, hpt.1.2 hxX, fun hc => ?_⟩
  have hz := Subgroup.mem_centralizer_iff.mp hc z s.mem
  exact s.ne_one (S127.fpf_of_mem_XOf h1222 h hxX hxV s.z_mem_V (by
    rw [← hz, mul_inv_cancel_right]))

omit s in
theorem mem_normalizer_C {x : G} (hx : x ∈ Subgroup.normalizer (V1 T L V : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (V1 T L V : Set G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun c hc => ?_
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : x⁻¹ * v * x ∈ V1 T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) v).mp hv
    simpa using this
  have h1 := hc _ hv'
  calc v * (x * c * x⁻¹) = x * ((x⁻¹ * v * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * v * x)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * v := by group

omit [Finite G] s in
abbrev Nx (T L V : Subgroup G) (x : G) : Subgroup G :=
  Subgroup.centralizer (V1 T L V : Set G) ⊔ Subgroup.zpowers x

omit [Finite G] s in
theorem Nx_le_N {x : G} (hx : x ∈ Subgroup.normalizer (V1 T L V : Set G)) :
    Nx T L V x ≤ Subgroup.normalizer (V1 T L V : Set G) :=
  sup_le (Subgroup.centralizer_le_normalizer _) (Subgroup.zpowers_le_of_mem hx)

omit s in
theorem Nx_le_normalizer_C {x : G} (hx : x ∈ Subgroup.normalizer (V1 T L V : Set G)) :
    Nx T L V x ≤ Subgroup.normalizer (Subgroup.centralizer (V1 T L V : Set G) : Set G) :=
  sup_le Subgroup.le_normalizer (Subgroup.zpowers_le_of_mem (mem_normalizer_C hx))

omit s in
theorem mem_Nx {x : G} (hx : x ∈ Subgroup.normalizer (V1 T L V : Set G)) {n : G}
    (hn : n ∈ Nx T L V x) :
    ∃ c ∈ Subgroup.centralizer (V1 T L V : Set G), ∃ y ∈ Subgroup.zpowers x, c * y = n := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left
    (Subgroup.centralizer (V1 T L V : Set G)) (Subgroup.zpowers x)
    (Subgroup.zpowers_le_of_mem (mem_normalizer_C hx))
  have hn' : n ∈ (↑(Nx T L V x) : Set G) := hn
  rw [h] at hn'
  obtain ⟨c, hc, y, hy, rfl⟩ := Set.mem_mul.mp hn'
  exact ⟨c, hc, y, hy, rfl⟩

omit s in
theorem mem_C_of_two_pow {x : G} (hx3 : x ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (V1 T L V : Set G))
    (hxC : x ∉ Subgroup.centralizer (V1 T L V : Set G)) {g : G} (hg : g ∈ Nx T L V x) {m : ℕ}
    (hm' : g ^ 2 ^ m = 1) : g ∈ Subgroup.centralizer (V1 T L V : Set G) := by
  obtain ⟨c, hc, y, hy, rfl⟩ := mem_Nx hxN hg
  have hyN : y ∈ Subgroup.normalizer (V1 T L V : Set G) := Subgroup.zpowers_le_of_mem hxN hy
  have hact : ∀ n : ℕ, ∀ v ∈ V1 T L V,
      (c * y) ^ n * v * ((c * y) ^ n)⁻¹ = y ^ n * v * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro v _; simp
    | succ n ih =>
      intro v hv
      have hyn : y ^ n * v * (y ^ n)⁻¹ ∈ V1 T L V :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyN n) v).mp hv
      have hyv : y * (y ^ n * v * (y ^ n)⁻¹) * y⁻¹ ∈ V1 T L V :=
        (Subgroup.mem_normalizer_iff.mp hyN _).mp hyn
      calc (c * y) ^ (n + 1) * v * ((c * y) ^ (n + 1))⁻¹
          = c * (y * ((c * y) ^ n * v * ((c * y) ^ n)⁻¹) * y⁻¹) * c⁻¹ := by
            rw [pow_succ', mul_inv_rev, mul_inv_rev]
            simp only [mul_assoc]
        _ = c * (y * (y ^ n * v * (y ^ n)⁻¹) * y⁻¹) * c⁻¹ := by rw [ih v hv]
        _ = y * (y ^ n * v * (y ^ n)⁻¹) * y⁻¹ := by
            rw [(Subgroup.mem_centralizer_iff.mp hc _ hyv).symm, mul_inv_cancel_right]
        _ = y ^ (n + 1) * v * (y ^ (n + 1))⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
  have hyC : y ^ 2 ^ m ∈ Subgroup.centralizer (V1 T L V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := hact (2 ^ m) v hv
    rw [hm', one_mul, inv_one, mul_one] at this
    calc v * y ^ 2 ^ m = (y ^ 2 ^ m * v * (y ^ 2 ^ m)⁻¹) * y ^ 2 ^ m := by rw [← this]
      _ = y ^ 2 ^ m * v := by group
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  by_cases hk : (3 : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hk
    rw [zpow_mul, hx3', one_zpow, mul_one]
    exact hc
  · exfalso
    apply hxC
    have hpow : (x ^ k) ^ 2 ^ m = x ^ (k * 2 ^ m) := by
      rw [← zpow_natCast, ← zpow_mul]
      push_cast
      ring_nf
    rw [hpow] at hyC
    have hmod : x ^ (k * 2 ^ m) = x ^ ((k * 2 ^ m) % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv (k * 2 ^ m) 3]
      rw [zpow_add, zpow_mul, hx3', one_zpow, mul_one]
    have h3 : ¬ (3 : ℤ) ∣ k * 2 ^ m := by
      intro h
      rcases (Int.prime_three.dvd_mul).mp h with h | h
      · exact hk h
      · have : (3 : ℤ) ∣ 2 := Int.Prime.dvd_pow' (by norm_num) h
        norm_num at this
    have hr : (k * 2 ^ m) % 3 = 1 ∨ (k * 2 ^ m) % 3 = 2 := by omega
    rw [hmod] at hyC
    rcases hr with hr | hr
    · rw [hr, zpow_one] at hyC
      exact hyC
    · rw [hr] at hyC
      have : x = (x ^ (2 : ℤ)) ^ (2 : ℤ) * x ^ (-(3 : ℤ)) := by
        rw [← zpow_mul, ← zpow_add]
        norm_num
      rw [this, zpow_neg, hx3', inv_one, mul_one]
      exact Subgroup.zpow_mem _ hyC 2

omit s in
theorem pCoreOf_Nx_le {x : G} (hx3 : x ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (V1 T L V : Set G))
    (hxC : x ∉ Subgroup.centralizer (V1 T L V : Set G)) :
    pCoreOf 2 (Nx T L V x) ≤ Subgroup.centralizer (V1 T L V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ⟨g, hg⟩
  exact mem_C_of_two_pow hx3 hxN hxC ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) hg) (m := m)
    (by simpa using congrArg Subtype.val hm)

theorem V1_le_pCoreOf_Nx
    (h1222 : Stmt12_2_2) {x : G} (hxN : x ∈ Subgroup.normalizer (V1 T L V : Set G)) :
    V1 T L V ≤ pCoreOf 2 (Nx T L V x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := s.V1_le_pCoreOf_C h1222
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((h1.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans le_sup_left) (Nx_le_N hxN)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le h1)

theorem pCoreOf_Nx_ne_bot
    (h1222 : Stmt12_2_2) {x : G} (hxN : x ∈ Subgroup.normalizer (V1 T L V : Set G)) :
    pCoreOf 2 (Nx T L V x) ≠ ⊥ := fun hb =>
  s.ne_one (by
    have := s.V1_le_pCoreOf_Nx h1222 hxN s.mem
    rwa [hb, Subgroup.mem_bot] at this)

end CFSG.Quasithin.H13.S127.L715.Set714
