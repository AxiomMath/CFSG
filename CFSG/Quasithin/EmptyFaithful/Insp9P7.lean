module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.B5Irr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Insp9

theorem prime_le_seven_of_dvd {r a b c d : ℕ} (hr : r.Prime) (h : r ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    r ≤ 7 := by
  rcases (Nat.Prime.dvd_mul hr).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h); omega

theorem prime_le_seven_of_eq {r n a b c d : ℕ} (hr : r.Prime) (hn : n = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d)
    (h : r ∣ n) : r ≤ 7 := prime_le_seven_of_dvd hr (hn ▸ h)

theorem prime_le_seven_of_dvd_numeral {r n : ℕ} (hr : r.Prime) (h : r ∣ n)
    (hn : n = 6 ∨ n = 60 ∨ n = 504 ∨ n = 168 ∨ n = 360 ∨ n = 2520 ∨ n = 1080 ∨ n = 120 ∨
      n = 40320 ∨ n = 12096 ∨ n = 1) : r ≤ 7 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_le_seven_of_eq (a := 1) (b := 1) (c := 0) (d := 0) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 2) (b := 1) (c := 1) (d := 0) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 3) (b := 2) (c := 0) (d := 1) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 3) (b := 1) (c := 0) (d := 1) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 3) (b := 2) (c := 1) (d := 0) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 3) (b := 2) (c := 1) (d := 1) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 3) (b := 3) (c := 1) (d := 0) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 3) (b := 1) (c := 1) (d := 0) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 7) (b := 2) (c := 1) (d := 1) hr (by norm_num) h
  · exact prime_le_seven_of_eq (a := 6) (b := 3) (c := 0) (d := 1) hr (by norm_num) h
  · have := Nat.le_of_dvd (by norm_num) h; omega

theorem prime_le_seven_of_dvd_dvd {r n : ℕ} (hr : r.Prime) (h : r ∣ n)
    (hn : n ∣ 40320 ∨ n ∣ 12096) : r ≤ 7 := by
  rcases hn with hn | hn
  · exact prime_le_seven_of_eq (a := 7) (b := 2) (c := 1) (d := 1) hr (by norm_num) (h.trans hn)
  · exact prime_le_seven_of_eq (a := 6) (b := 3) (c := 0) (d := 1) hr (by norm_num) (h.trans hn)


theorem b56QL_primes_le7 {X : Type} [Group X] [Finite X] (h : B56QuasisimpleList X)
    (h4 : ¬ 2 ^ 4 ∣ Nat.card X) : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → r ≤ 7 := by
  intro r hr hrX
  have hpos : 0 < Nat.card X := Nat.card_pos
  rcases h with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
    ⟨n, K, _, _, hK, ⟨e⟩⟩ | he | he | hhat | ⟨K, _, _, hK, ⟨e⟩⟩ | he | he
  ·
    have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    have hn : n ≤ 3 := by
      by_contra hn
      exact h4 (by rw [hX]; exact (Nat.pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ rfl))
    interval_cases n
    · simp at hX hpos; omega
    · exact prime_le_seven_of_dvd_numeral hr hrX (by simp at hX; omega)
    · exact prime_le_seven_of_dvd_numeral hr hrX (by simp at hX; omega)
    · exact prime_le_seven_of_dvd_numeral hr hrX (by simp at hX; omega)
  ·
    have hX : Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    have hn : n ≤ 1 := by
      by_contra hn
      refine h4 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 4 ≤ n * 3)).trans (Dvd.intro _ rfl))
    interval_cases n
    · simp at hX hpos; omega
    · exact prime_le_seven_of_dvd_numeral hr hrX (by simp at hX; omega)
  ·
    have hX : Nat.card X = (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
      have hI : Finset.Icc 1 2 = {1, 2} := by decide
      rw [hI, Finset.prod_pair (by norm_num)]
    by_cases hn0 : n = 0
    · subst hn0; simp at hX hpos; omega
    · exfalso
      refine h4 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 4 ≤ n * 2 ^ 2)).trans (Dvd.intro _ rfl))
  ·
    have hX : Nat.card X = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK]
    by_cases hn0 : n = 0
    · subst hn0; simp at hX hpos; omega
    · exfalso
      refine h4 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 4 ≤ n * 6)).trans (Dvd.intro _ rfl))
  ·
    obtain ⟨e⟩ := he
    have : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
      simp [Nat.factorial]
    exact prime_le_seven_of_dvd_numeral hr hrX (by omega)
  ·
    obtain ⟨e⟩ := he
    have : Nat.card X = 2520 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
      simp [Nat.factorial]
    exact prime_le_seven_of_dvd_numeral hr hrX (by omega)
  ·
    have hA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      simp [Nat.factorial]
    have : Nat.card X = 1080 := card_of_isHat1527d hhat hA
    exact prime_le_seven_of_dvd_numeral hr hrX (by omega)
  ·
    have h2 : Nat.card K = 2 ^ 1 := by simpa using hK
    have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact (quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
          ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb)
    have h3 := Subgroup.card_dvd_of_le hle
    rw [card_quasithinG2_1527d h2, hK] at h3
    rw [Nat.card_congr e.toEquiv] at hrX
    exact prime_le_seven_of_dvd_dvd hr hrX (Or.inr (by simpa using h3))
  ·
    obtain ⟨e⟩ := he
    exfalso
    apply h4
    rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
    norm_num
  ·
    obtain ⟨e⟩ := he
    exfalso
    apply h4
    rw [Nat.card_congr e.toEquiv, card_statedSL_five_zmod1527d]
    norm_num

theorem b56FL_even {X : Type} [Group X] (h : B56FactorList X) : 2 ∣ Nat.card X := by
  rcases h with ⟨n, K, _, _, hn, hK, ⟨e⟩⟩ | ⟨e⟩ | ⟨m, K, _, _, hm, -, hK, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · obtain ⟨e⟩ := ‹Nonempty (X ≃* Equiv.Perm (Fin 5))›
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  · rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    exact Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _

theorem b56FL_primes_le7 {X : Type} [Group X] [Finite X] (h : B56FactorList X)
    (h8 : ¬ 2 ^ 3 ∣ Nat.card X) : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → r ≤ 7 := by
  intro r hr hrX
  have hpos : 0 < Nat.card X := Nat.card_pos
  rcases h with ⟨n, K, _, _, hn, hK, ⟨e⟩⟩ | he | ⟨m, K, _, _, hm, -, hK, ⟨e⟩⟩
  · have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    have hn' : n ≤ 2 := by
      by_contra hn'
      exact h8 (by rw [hX]; exact (Nat.pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ rfl))
    interval_cases n
    · exact prime_le_seven_of_dvd_numeral hr hrX (by simp at hX; omega)
    · exact prime_le_seven_of_dvd_numeral hr hrX (by simp at hX; omega)
  · exfalso
    obtain ⟨e⟩ := he
    apply h8
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  · exfalso
    apply h8
    rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK, ← pow_mul]
    exact (Nat.pow_dvd_pow 2 (by omega : 3 ≤ m * 3)).trans (Dvd.intro _ rfl)

theorem card_sup_eq_mul {Ω : Type*} [Group Ω] {A B : Subgroup Ω}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := fun a b => hc a a.2 b b.2
  let φ : ↥A × ↥B →* Ω := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker] at hab
    have h1 : (a : Ω) * (b : Ω) = 1 := hab
    have h2 : (a : Ω) = (b : Ω)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (a : Ω) ∈ A ⊓ B := ⟨a.2, by rw [h2]; exact B.inv_mem b.2⟩
    rw [hAB, Subgroup.mem_bot] at h3
    have h4 : (b : Ω) = 1 := by rw [h3, one_mul] at h1; exact h1
    simp only [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext h3, Subtype.ext h4⟩
  have hrange : φ.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range]
    simp
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem sq_centralizes_of_card_three {Ω : Type*} [Group Ω] {A : Subgroup Ω} (hA : Nat.card A = 3)
    {t : Ω} (ht : t ∈ Subgroup.normalizer (A : Set Ω)) (hnc : ¬ ∀ y ∈ A, t * y * t⁻¹ = y) :
    ∀ y ∈ A, t * t * y * (t * t)⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥A := isCyclic_of_prime_card hA
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  set x : Ω := (g : Ω) with hxdef
  have hx3 : x ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥A) (x := g)
    rw [hA] at this
    simpa using congrArg Subtype.val this
  have hxA : x ∈ A := g.2
  have hpow : ∀ y ∈ A, ∃ k : ℤ, x ^ k = y := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hconjG : ∀ (u z : Ω) (k : ℤ), u * z ^ k * u⁻¹ = (u * z * u⁻¹) ^ k := fun u z k =>
    map_zpow (MulAut.conj u) z k
  have hconj : ∀ (z : Ω) (k : ℤ), t * z ^ k * t⁻¹ = (t * z * t⁻¹) ^ k := fun z k => hconjG t z k
  have hcA : t * x * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp ht x).mp hxA
  have hcx : t * x * t⁻¹ ≠ x := by
    intro hcx
    apply hnc
    intro y hy
    obtain ⟨k, rfl⟩ := hpow y hy
    rw [hconj, hcx]
  obtain ⟨m, hm⟩ := hpow _ hcA
  have hxm : ∀ n : ℤ, x ^ n = x ^ (n % 3) := by
    intro n
    have h3 : x ^ (3 : ℤ) = 1 := by simpa using hx3
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3, zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hcx
    have : t * x * t⁻¹ = 1 := by rw [hx1]; simp
    rw [this, hx1]
  have hc2 : t * x * t⁻¹ = x ^ (2 : ℤ) := by
    rcases hm3 with h0 | h1 | h2
    · exfalso
      apply hx1
      have : t * x * t⁻¹ = 1 := by rw [← hm, hxm, h0]; simp
      have h' : t * x * t⁻¹ = 1 := this
      calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
        _ = 1 := by rw [h']; simp
    · exfalso
      apply hcx
      rw [← hm, hxm, h1]; simp
    · rw [← hm, hxm, h2]
  have hsq : t * t * x * (t * t)⁻¹ = x := by
    have e1 : t * t * x * (t * t)⁻¹ = t * (t * x * t⁻¹) * t⁻¹ := by group
    rw [e1, hc2, hconj, hc2]
    have : (x ^ (2 : ℤ)) ^ (2 : ℤ) = x ^ ((2 : ℤ) * 2) := (zpow_mul x 2 2).symm
    rw [this, hxm]
    norm_num
  intro y hy
  obtain ⟨k, rfl⟩ := hpow y hy
  have hconj2 : ∀ (z : Ω) (k : ℤ), t * t * z ^ k * (t * t)⁻¹ = (t * t * z * (t * t)⁻¹) ^ k :=
    fun z k => hconjG (t * t) z k
  rw [hconj2, hsq]

section TypeFour

variable {W : Type} [CommGroup W]

theorem case4_two_pow_four_dvd {G : Subgroup (MulAut W)} (h : B56Case4 G) :
    2 ^ 4 ∣ Nat.card ↥G := by
  obtain ⟨G₁, G₂, t, hG, hinf, hcomm, ⟨e⟩, hcard₂, -, -, -, -, -, ht₁, ht₂, -, hout₂⟩ := h
  have hG1card : Nat.card ↥G₁ = 360 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
    simp [Nat.factorial]
  set C : Subgroup (MulAut W) := G₁ ⊔ G₂ with hC
  have hCcard : Nat.card ↥C = 360 * 3 := by
    rw [hC, card_sup_eq_mul hcomm hinf, hG1card, hcard₂]
  have hCG : C ≤ G := hG ▸ le_sup_left
  have htG : t ∈ G := hG ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hnormC : G ≤ Subgroup.normalizer (C : Set (MulAut W)) := by
    rw [hG]
    refine sup_le Subgroup.le_normalizer ?_
    refine Subgroup.zpowers_le.mpr ?_
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) (fun x hx => ?_)
    · have h1 : (C : Subgroup (MulAut W)) ≤ (C).comap (MulAut.conj t).toMonoidHom := by
        refine sup_le (fun a ha => ?_) (fun b hb => ?_)
        · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp ht₁ a).mp ha)
        · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp ht₂ b).mp hb)
      exact h1 hx
    · have h1 : (C : Subgroup (MulAut W)) ≤ (C).comap (MulAut.conj t⁻¹).toMonoidHom := by
        have ht₁' := Subgroup.inv_mem _ ht₁
        have ht₂' := Subgroup.inv_mem _ ht₂
        refine sup_le (fun a ha => ?_) (fun b hb => ?_)
        · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp ht₁' a).mp ha)
        · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp ht₂' b).mp hb)
      have := h1 hx
      simpa using this
  have hN : (C.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCG).mpr hnormC
  have hmul : Nat.card ↥C * (C.subgroupOf G).index = Nat.card ↥G := by
    have h1 := Subgroup.card_mul_index (C.subgroupOf G)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCG).toEquiv] at h1
  have heven : 2 ∣ (C.subgroupOf G).index := by
    by_contra hodd
    have hodd' : Odd (C.subgroupOf G).index := Nat.odd_iff.mpr (by omega)
    set k := (C.subgroupOf G).index with hk
    have htk : t ^ k ∈ C := by
      have := Subgroup.pow_index_mem (C.subgroupOf G) (⟨t, htG⟩ : ↥G)
      exact this
    have hcent : ∀ c ∈ C, ∀ y ∈ G₂, c * y = y * c := by
      have hle : C ≤ Subgroup.centralizer (G₂ : Set (MulAut W)) := by
        refine sup_le (fun a ha => ?_) (fun b hb => ?_)
        · exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm a ha y hy).symm
        · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
          have hcyc : IsCyclic ↥G₂ := isCyclic_of_prime_card hcard₂
          let _ : CommGroup ↥G₂ := IsCyclic.commGroup
          refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
          have := mul_comm (⟨y, hy⟩ : ↥G₂) (⟨b, hb⟩ : ↥G₂)
          exact congrArg Subtype.val this
      intro c hc y hy
      exact (Subgroup.mem_centralizer_iff.mp (hle hc) y hy).symm
    have hnc : ¬ ∀ y ∈ G₂, t * y * t⁻¹ = y := by
      intro hc
      exact hout₂ ⟨1, G₂.one_mem, fun x hx => by simpa using hc x hx⟩
    have hsq := sq_centralizes_of_card_three hcard₂ ht₂ hnc
    apply hnc
    intro y hy
    obtain ⟨j, hj⟩ : ∃ j : ℤ, 1 = (k : ℤ) + 2 * j := by
      obtain ⟨a, ha⟩ := hodd'
      exact ⟨-a, by omega⟩
    have htt : t = t ^ k * (t * t) ^ j := by
      rw [← sq, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_add]
      simp [← hj]
    have hu : (t ^ k) * y = y * (t ^ k) := hcent _ htk y hy
    have hv : Commute ((t * t) ^ j) y := by
      refine Commute.zpow_left ?_ j
      have := hsq y hy
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have hty : t * y = y * t := by
      conv_lhs => rw [htt]
      calc t ^ k * (t * t) ^ j * y = t ^ k * (y * (t * t) ^ j) := by rw [mul_assoc, hv.eq]
        _ = (t ^ k * y) * (t * t) ^ j := by rw [mul_assoc]
        _ = y * t ^ k * (t * t) ^ j := by rw [hu]
        _ = y * (t ^ k * (t * t) ^ j) := by rw [mul_assoc]
        _ = y * t := by rw [← htt]
    rw [hty]; group
  have h2160 : 2 ^ 4 ∣ 360 * 3 * (C.subgroupOf G).index := by
    obtain ⟨m, hm⟩ := heven
    rw [hm]
    exact ⟨135 * m, by ring⟩
  rw [← hmul, hCcard]
  exact h2160

theorem case5_two_pow_four_dvd {G : Subgroup (MulAut W)} (h : B56Case5 G) :
    2 ^ 4 ∣ Nat.card ↥G := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, -, ⟨e⟩, -, -, hG₂⟩ := h
  have h1 : Nat.card ↥G₁ = 168 := by
    rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
    norm_num
  have hprod := card_sup_eq_mul hcomm hinf
  rw [hsup, h1] at hprod
  have h2 : 2 ∣ Nat.card ↥G₂ := by
    rcases hG₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, K, _, _, hK, π, hπ⟩
    · rw [Nat.card_congr e₂.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
      norm_num
    · rw [card_eq_of_nat_realizes1527d hπ, card_statedSL_two1527d, hK]
      have hn : 1 ≤ n := by
        by_contra hn
        have hn0 : n = 0 := by omega
        have := Finite.one_lt_card (α := K)
        rw [hK, hn0] at this
        simp at this
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  rw [hprod]
  obtain ⟨m, hm⟩ := h2
  rw [hm]
  exact ⟨21 * m, by ring⟩

end TypeFour

section Case1

variable {W : Type} [CommGroup W] [Finite W]

theorem b56Case1_cases {G : Subgroup (MulAut W)} (h : B56Case1 G) :
    (G = quasithinGenFitting G ∧ B56QuasisimpleList ↥G) ∨ Nat.card ↥G ∣ 40320 ∨
      Nat.card ↥G ∣ 12096 := by
  obtain ⟨hLq, hconcl, hlist⟩ := h
  obtain ⟨-, hcases⟩ := hconcl.1
  have key : G = quasithinGenFitting G → (G = quasithinGenFitting G ∧ B56QuasisimpleList ↥G) ∨
      Nat.card ↥G ∣ 40320 ∨ Nat.card ↥G ∣ 12096 := by
    intro hGL
    refine Or.inl ⟨hGL, ?_⟩
    rw [← hGL] at hlist
    exact hlist
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨S, hS⟩ := B5.exists_isSylowTwoOf G
    rcases hi.2.2 S hS with hGL | ⟨-, hnat⟩
    · exact key hGL
    · rcases hnat with ⟨n, hn5, hn8, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
      · right; left
        have h1 := Subgroup.card_dvd_of_surjective hπ.1
        have h2 : Nat.card (Equiv.Perm (Fin n)) ∣ 40320 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
          exact Nat.factorial_dvd_factorial hn8 |>.trans (by norm_num [Nat.factorial])
        exact h1.trans h2
      · right; right
        have h1 := Subgroup.card_dvd_of_surjective hπ.1
        have h3 := card_quasithinG2_1527d hK
        rw [hK] at h3
        exact h1.trans (show Nat.card ↥(quasithinG2 K) ∣ 12096 by rw [h3]; norm_num)
  · exact key hii.1
  · exact key hiii.1
  · exact key hiv.1

end Case1

section Assembly

variable {W : Type} [CommGroup W] [Finite W]

theorem b56_primes_le_seven {G : Subgroup (MulAut W)}
    (h : B56Case1 G ∨ B56Case2 G ∨ B56Case3 G ∨ B56Case4 G ∨ B56Case5 G)
    (h4 : ¬ 2 ^ 4 ∣ Nat.card ↥G) : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥G → r ≤ 7 := by
  intro r hr hrG
  rcases h with h1 | h2 | h3 | h4' | h5
  · rcases b56Case1_cases h1 with ⟨-, hlist⟩ | hd | hd
    · exact b56QL_primes_le7 hlist h4 r hr hrG
    · exact prime_le_seven_of_dvd_dvd hr hrG (Or.inl hd)
    · exact prime_le_seven_of_dvd_dvd hr hrG (Or.inr hd)
  · obtain ⟨e⟩ := h2.1
    have : Nat.card ↥G = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    exact prime_le_seven_of_dvd_numeral hr hrG (by omega)
  · obtain ⟨G₁, G₂, hsup, hinf, hcomm, hF₁, hF₂, -⟩ := h3
    have hprod := card_sup_eq_mul hcomm hinf
    rw [hsup] at hprod
    have e₁ := b56FL_even hF₁
    have e₂ := b56FL_even hF₂
    rw [hprod] at hrG
    rcases (Nat.Prime.dvd_mul hr).mp hrG with hr₁ | hr₂
    · refine b56FL_primes_le7 hF₁ (fun h8 => h4 ?_) r hr hr₁
      rw [hprod]
      exact Dvd.dvd.trans (by norm_num : (2:ℕ) ^ 4 ∣ 2 ^ 3 * 2) (Nat.mul_dvd_mul h8 e₂)
    · refine b56FL_primes_le7 hF₂ (fun h8 => h4 ?_) r hr hr₂
      rw [hprod]
      exact Dvd.dvd.trans (by norm_num : (2:ℕ) ^ 4 ∣ 2 * 2 ^ 3) (Nat.mul_dvd_mul e₁ h8)
  · exact absurd (case4_two_pow_four_dvd h4') h4
  · exact absurd (case5_two_pow_four_dvd h5) h4

end Assembly

end Insp9

end CFSG.Quasithin
