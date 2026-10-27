module

public import CFSG.RankThree.PartOne.S12.Sec1514Defs
public import CFSG.RankThree.PartOne.S12.Sec15FA

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

open scoped Pointwise

namespace Sec1512

variable {G : Type} [Group G]

theorem false_of_normal_in_twoLocal [Finite G] (hchar : IsCharacteristicPType G 2) {R X : Subgroup G}
    (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hXM : X ≤ Subgroup.normalizer (R : Set G))
    (hMX : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (X : Set G)) (hX1 : X ≠ ⊥)
    (hX2 : ∀ Q : Subgroup G, Q ≤ X → X ≤ Subgroup.normalizer (Q : Set G) → IsPGroup 2 Q → Q = ⊥) :
    False := by
  classical
  have hMloc : IsPLocal 2 (Subgroup.normalizer (R : Set G)) := ⟨R, hR1, hR2, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = Subgroup.normalizer (R : Set G) := ⟨_, rfl⟩
  rw [← hM] at hMloc hXM hMX
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup G, Q = inSubgroup (CFSG.pCore 2) M := ⟨_, rfl⟩
  have hQ2 : IsPGroup 2 Q := hQ ▸ IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := M)) M.subtype
  have hQM : Q ≤ M := hQ ▸ Subgroup.map_subtype_le _
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := hQ ▸
    (Subgroup.le_normalizer.trans
      (Sec15Final.normalizer_le_normalizer_map_subtype_of_characteristic inferInstance))
  have h1 : X ⊓ Q = ⊥ := by
    refine hX2 _ inf_le_left (fun x hx => ?_) (hQ2.to_le inf_le_right)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hX' := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hx) y
    have hQ' := Subgroup.mem_normalizer_iff.1 (hMQ (hXM hx)) y
    simp only [Subgroup.mem_inf]
    rw [hX', hQ']
  have h2 : ∀ x ∈ X, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    have hxM : x ∈ M := hXM hx
    have hyM : y ∈ M := hQM hy
    have hcX : x * y * x⁻¹ * y⁻¹ ∈ X := by
      have : y * x⁻¹ * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hMX hyM) _).1 (X.inv_mem hx)
      have := X.mul_mem hx this
      simpa [mul_assoc] using this
    have hcQ : x * y * x⁻¹ * y⁻¹ ∈ Q := by
      have : x * y * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hMQ hxM) y).1 hy
      exact Q.mul_mem this (Q.inv_mem hy)
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Q := ⟨hcX, hcQ⟩
    rw [h1, Subgroup.mem_bot] at h3
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  have h3 : X ≤ Q := by
    intro x hx
    have hxM : x ∈ M := hXM hx
    have hcent : (⟨x, hxM⟩ : ↥M) ∈ Subgroup.centralizer ((CFSG.pCore 2 ↥M : Subgroup ↥M) : Set ↥M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzQ : (z : G) ∈ Q := hQ ▸ ⟨z, hz, rfl⟩
      exact Subtype.ext (h2 x hx z hzQ).symm
    have hxcore : (⟨x, hxM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := hchar M hMloc hcent
    exact hQ ▸ ⟨⟨x, hxM⟩, hxcore, rfl⟩
  exact hX1 (hX2 X le_rfl Subgroup.le_normalizer (hQ2.to_le h3))

theorem normal_two_eq_bot_of_simple [Finite G] {I : Subgroup G} (hI : IsSimpleGroup ↥I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card ↥I) :
    ∀ Q : Subgroup G, Q ≤ I → I ≤ Subgroup.normalizer (Q : Set G) → IsPGroup 2 Q → Q = ⊥ := by
  intro Q hQI hIQ hQ2
  have hnorm : (Q.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQI).2 hIQ
  have := hnorm
  rcases hI.eq_bot_or_eq_top_of_normal (Q.subgroupOf I) with h | h
  · rw [eq_bot_iff]
    intro q hq
    have h1 : (⟨q, hQI hq⟩ : ↥I) ∈ Q.subgroupOf I := hq
    rw [h, Subgroup.mem_bot] at h1
    have h2 : q = 1 := congrArg Subtype.val h1
    rw [h2]
    exact (⊥ : Subgroup G).one_mem
  · exfalso
    have hIQ' : I ≤ Q := fun x hx => by
      have h1 : (⟨x, hx⟩ : ↥I) ∈ Q.subgroupOf I := by rw [h]; trivial
      exact h1
    have hI2 : IsPGroup 2 ↥I := hQ2.to_le hIQ'
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hI2
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

theorem inf_centralizer_eq_bot_of_simple [Finite G] {I : Subgroup G} (hI : IsSimpleGroup ↥I) {p : ℕ}
    (hp : p.Prime) (hdvd : p ^ 3 ∣ Nat.card ↥I) : I ⊓ Subgroup.centralizer (I : Set G) = ⊥ := by
  have hZ : (I ⊓ Subgroup.centralizer (I : Set G)).subgroupOf I = Subgroup.center ↥I := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_center_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, h⟩ y
      exact Subtype.ext (h y y.2)
    · intro h
      exact ⟨x.2, fun y hy => congrArg Subtype.val (h ⟨y, hy⟩)⟩
  rcases hI.eq_bot_or_eq_top_of_normal (Subgroup.center ↥I) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx.1⟩ : ↥I) ∈ (I ⊓ Subgroup.centralizer (I : Set G)).subgroupOf I := hx
    rw [hZ, h, Subgroup.mem_bot] at h1
    have h2 : x = 1 := congrArg Subtype.val h1
    rw [h2]
    exact Subgroup.one_mem _
  · exfalso
    have hcomm : ∀ x y : ↥I, x * y = y * x := fun x y => by
      have hx : x ∈ Subgroup.center ↥I := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.1 hx) y).symm
    let _ : CommGroup ↥I := { (inferInstance : Group ↥I) with mul_comm := hcomm }
    have hprime : (Nat.card ↥I).Prime := IsSimpleGroup.prime_card (α := ↥I)
    obtain ⟨k, hk⟩ := hdvd
    have h3 : p ∣ Nat.card ↥I := ⟨p ^ 2 * k, by rw [hk]; ring⟩
    have h4 : p = Nat.card ↥I := (Nat.prime_dvd_prime_iff_eq hp hprime).1 h3
    have h5 : Nat.card ↥I = p ^ 3 * k := hk
    have h6 : 1 < p := hp.one_lt
    have h7 : 0 < k := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at h5; exact hprime.ne_zero h5)
    have h8 : p ^ 3 ≤ Nat.card ↥I := by rw [h5]; exact Nat.le_mul_of_pos_right _ h7
    have h9 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right h6 (by norm_num)
    omega

variable [Finite G]

theorem faithful_sup {I T : Subgroup G} (hTN : T ≤ Subgroup.normalizer (I : Set G))
    (hTS : IsSylowOf 2 T (I ⊔ T)) (hTC : T ⊓ Subgroup.centralizer (I : Set G) = ⊥)
    (hIC : I ⊓ Subgroup.centralizer (I : Set G) = ⊥) :
    (I ⊔ T) ⊓ Subgroup.centralizer (I : Set G) = ⊥ := by
  classical
  have hT2 : IsPGroup 2 T := hTS.2.1
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = (I ⊔ T) ⊓ Subgroup.centralizer (I : Set G) := ⟨_, rfl⟩
  rw [← hK]
  have hKC : ∀ k ∈ K, ∀ y ∈ I, y * k = k * y := fun k hk y hy =>
    Subgroup.mem_centralizer_iff.1 (hK ▸ hk : k ∈ (I ⊔ T) ⊓ Subgroup.centralizer (I : Set G)).2 y hy
  have hKH : ∀ k ∈ K, k ∈ I ⊔ T := fun k hk => (hK ▸ hk :
    k ∈ (I ⊔ T) ⊓ Subgroup.centralizer (I : Set G)).1
  have hK2 : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    have hmem : k ∈ (I : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left I T hTN]
      exact hKH k hk
    obtain ⟨i, hi, t, ht, hkit⟩ := hmem
    have hkit' : k = i * t := hkit.symm
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have hta : t ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
    have hcomm : i * t = t * i := by
      have h1 := hKC k hk i hi
      rw [hkit'] at h1
      have h2 : i * (i * t) = i * (t * i) := by simpa [mul_assoc] using h1
      exact mul_left_cancel h2
    have hc : Commute i t := hcomm
    refine ⟨a, Subtype.ext ?_⟩
    have h3 : k ^ (2 ^ a) = i ^ (2 ^ a) := by
      rw [hkit', hc.mul_pow, hta, mul_one]
    have h4 : i ^ (2 ^ a) ∈ I ⊓ Subgroup.centralizer (I : Set G) := by
      have hkK : k ^ (2 ^ a) ∈ K := K.pow_mem hk _
      rw [h3] at hkK
      exact ⟨I.pow_mem hi _, Subgroup.mem_centralizer_iff.2 fun y hy => hKC _ hkK y hy⟩
    rw [hIC, Subgroup.mem_bot] at h4
    have h5 : k ^ (2 ^ a) = 1 := by rw [h3, h4]
    simpa using h5
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := by
    have hconj : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
      intro t ht k hk
      have hT' : t⁻¹ ∈ T := T.inv_mem ht
      have htH : t ∈ I ⊔ T := Subgroup.mem_sup_right ht
      rw [hK]
      refine ⟨(I ⊔ T).mul_mem ((I ⊔ T).mul_mem htH (hKH k hk)) ((I ⊔ T).inv_mem htH), ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      have hy' : t⁻¹ * y * t ∈ I := by
        have := (Subgroup.mem_normalizer_iff.1 (hTN hT') y).1 hy
        simpa using this
      have := hKC k hk _ hy'
      calc y * (t * k * t⁻¹) = t * ((t⁻¹ * y * t) * k) * t⁻¹ := by group
        _ = t * (k * (t⁻¹ * y * t)) * t⁻¹ := by rw [this]
        _ = t * k * t⁻¹ * y := by group
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro k
    exact ⟨fun hk => hconj t ht k hk, fun hk => by
      have := hconj t⁻¹ (T.inv_mem ht) _ hk
      simpa [mul_assoc] using this⟩
  have hKT : K ≤ T := by
    have hR : IsPGroup 2 (T ⊔ K : Subgroup G) := hT2.to_sup_of_normal_right' hK2 hTK
    have hle : T ⊔ K ≤ T := Sec15FA.le_of_isSylowOf_of_isPGroup hTS hR le_sup_left
      (sup_le le_sup_right (fun k hk => hKH k hk))
    exact le_sup_right.trans hle
  rw [eq_bot_iff]
  intro k hk
  have hkT : k ∈ T := hKT hk
  have hkC : k ∈ Subgroup.centralizer (I : Set G) := (hK ▸ hk :
    k ∈ (I ⊔ T) ⊓ Subgroup.centralizer (I : Set G)).2
  have : k ∈ T ⊓ Subgroup.centralizer (I : Set G) := ⟨hkT, hkC⟩
  rw [hTC] at this
  exact this

theorem config_of_inputs {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {I T A : Subgroup G}
    (hT : IsSylowOf 2 T (Subgroup.normalizer (I : Set G)))
    (hTC : T ⊓ Subgroup.centralizer (I : Set G) = ⊥)
    (hIC : I ⊓ Subgroup.centralizer (I : Set G) = ⊥) (hAI : A ≤ I)
    (hAe : IsElementaryAbelian p ↥A) (hAcard : Nat.card ↥A = p ^ 3) :
    Config1514 p I (I ⊔ T) T A := by
  have hTH : T ≤ I ⊔ T := le_sup_right
  have hHN : I ⊔ T ≤ Subgroup.normalizer (I : Set G) := sup_le Subgroup.le_normalizer hT.1
  have hTS : IsSylowOf 2 T (I ⊔ T) := by
    refine ⟨hTH, hT.2.1, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex T (I ⊔ T) (Subgroup.normalizer (I : Set G)) hTH hHN
    intro hdvd
    exact hT.2.2 (h1 ▸ dvd_mul_of_dvd_left hdvd _)
  exact ⟨hp, h5, le_sup_left, hHN, faithful_sup hT.1 hTS hTC hIC, hTS, hAI, hAe, hAcard⟩

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers {t : G} :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact hx

omit [Finite G] in
theorem mem_centralizer_of_mem_normalizer_zpowers {t m : G} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hm : m ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G)) : m * t = t * m := by
  have h1 : m * t * m⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.1 hm t).1 (Subgroup.mem_zpowers t)
  have ht : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  have h2 : (m * t * m⁻¹) ^ 2 = 1 := by
    have : m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
    rw [pow_two, this, ← pow_two, ht2]; group
  have hne : m * t * m⁻¹ ≠ 1 := by
    intro h
    apply ht1
    have : t = m⁻¹ * (m * t * m⁻¹) * m := by group
    rw [this, h]; group
  have h3 : m * t * m⁻¹ = t := by
    rw [← hk]
    have hk' : (k % 2 : ℤ) = 0 ∨ (k % 2 : ℤ) = 1 := by omega
    have hkk : t ^ k = t ^ (k % 2) := by
      have : t ^ k = t ^ (2 * (k / 2) + k % 2) := by rw [Int.mul_ediv_add_emod]
      rw [this, zpow_add, zpow_mul, zpow_two, ← pow_two, ht2, one_zpow, one_mul]
    rcases hk' with h0 | h0
    · exfalso
      apply hne
      rw [← hk, hkk, h0]; simp
    · rw [hkk, h0]; simp
  calc m * t = (m * t * m⁻¹) * m := by group
    _ = t * m := by rw [h3]

end Sec1512

end CFSG.RankThree.PartOne
