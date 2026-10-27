module

public import CFSG.Quasithin.Vol2.Ch10SecKRSf
public import CFSG.Quasithin.Vol2.Ch10SecQ9H26

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_zpow_mul {K : Subgroup G} {d : G} (hdK : d ∈ Subgroup.normalizer (K : Set G))
    {g : G} (hg : g ∈ Subgroup.zpowers d ⊔ K) : ∃ n : ℤ, ∃ k ∈ K, g = d ^ n * k := by
  have hset : ((Subgroup.zpowers d ⊔ K : Subgroup G) : Set G) =
      (Subgroup.zpowers d : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr hdK)
  have hg' : g ∈ ((Subgroup.zpowers d ⊔ K : Subgroup G) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_mul.mp hg'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ⟨n, k, hk, rfl⟩

theorem mem_zpowers_of_pow_three [Finite G] {g y : G} (hg : g ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers g) (hy1 : y ≠ 1) : g ∈ Subgroup.zpowers y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hg1 : g ≠ 1 := fun h => hy1 (by rw [h, one_zpow])
  have hog : orderOf g = 3 := orderOf_eq_prime hg hg1
  have hy3 : (g ^ n) ^ 3 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hg, one_zpow]
  have hoy : orderOf (g ^ n) = 3 := orderOf_eq_prime hy3 hy1
  have heq : Subgroup.zpowers (g ^ n) = Subgroup.zpowers g :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hog, hoy])
  rw [heq]
  exact Subgroup.mem_zpowers g

theorem eq_one_of_two_three {g : G} {m n : ℕ} (h2 : g ^ 2 ^ m = 1) (h3 : g ^ 3 ^ n = 1) :
    g = 1 := by
  have h1 : orderOf g ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2
  have h1' : orderOf g ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h3
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow m n (by norm_num)) h1 h1')

theorem exists_E9 [Finite G] {K H : Subgroup G} {d d' u w : G} (hK2 : IsPGroup 2 K)
    (hdH : d ∈ H) (hd'H : d' ∈ H) (hd3 : d ^ 3 = 1) (hd'3 : d' ^ 3 = 1)
    (hdK : d ∈ Subgroup.normalizer (K : Set G)) (hd'K : d' ∈ Subgroup.normalizer (K : Set G))
    (hcomm : d * d' * d⁻¹ * d'⁻¹ ∈ K) (hKu : K ≤ Subgroup.centralizer ({u} : Set G))
    (hKw : K ≤ Subgroup.centralizer ({w} : Set G)) (hdw : d ∈ Subgroup.centralizer ({w} : Set G))
    (hd'u : d' ∈ Subgroup.centralizer ({u} : Set G))
    (hdu : d ∉ Subgroup.centralizer ({u} : Set G))
    (hd'w : d' ∉ Subgroup.centralizer ({w} : Set G)) :
    ∃ P : Subgroup G, P ≤ H ∧ (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) ∧ (∀ a ∈ P, a ^ 3 = 1) ∧
      9 ≤ Nat.card P ∧ ∀ g ∈ P, g ∈ Subgroup.centralizer ({u} : Set G) →
        g ∈ Subgroup.centralizer ({w} : Set G) → g = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K' := K ⊓ H with hK'
  have hK'2 : IsPGroup 2 K' := hK2.to_le inf_le_left
  have hHN : ∀ {x : G}, x ∈ H → x ∈ Subgroup.normalizer (H : Set G) := fun hx =>
    Subgroup.le_normalizer hx
  have hdK' : d ∈ Subgroup.normalizer (K' : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hdK ⊢
    intro k
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hdK k,
      (Subgroup.mem_normalizer_iff.mp (hHN hdH) k)]
  have hd'K' : d' ∈ Subgroup.normalizer (K' : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hd'K ⊢
    intro k
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hd'K k,
      (Subgroup.mem_normalizer_iff.mp (hHN hd'H) k)]
  set D := Subgroup.zpowers d ⊔ K' with hD
  have hDH : D ≤ H := sup_le (Subgroup.zpowers_le.mpr hdH) inf_le_right
  have hDw : D ≤ Subgroup.centralizer ({w} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hdw) (inf_le_left.trans hKw)
  have hdD : d ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hc' : d' * d * d'⁻¹ * d⁻¹ ∈ K' := by
    refine ⟨?_, ?_⟩
    · have := K.inv_mem hcomm
      simpa [mul_assoc] using this
    · exact H.mul_mem (H.mul_mem (H.mul_mem hd'H hdH) (H.inv_mem hd'H)) (H.inv_mem hdH)
  have hd'D : d' ∈ Subgroup.normalizer (D : Set G) := by
    have hgen : ∀ g ∈ D, d' * g * d'⁻¹ ∈ D := by
      intro g hg
      obtain ⟨n, k, hk, rfl⟩ := exists_zpow_mul hdK' hg
      have h1 : d' * (d ^ n * k) * d'⁻¹ = (d' * d * d'⁻¹) ^ n * (d' * k * d'⁻¹) := by
        rw [conj_zpow]; group
      rw [h1]
      refine D.mul_mem (D.zpow_mem ?_ n) (Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp hd'K' k).mp hk))
      have h2 : d' * d * d'⁻¹ = (d' * d * d'⁻¹ * d⁻¹) * d := by group
      rw [h2]
      exact D.mul_mem (Subgroup.mem_sup_right hc') hdD
    have hgen2 : ∀ g ∈ D, (d' * d') * g * (d' * d')⁻¹ ∈ D := fun g hg => by
      have := hgen _ (hgen g hg)
      simpa [mul_assoc] using this
    refine C10P4F.le_normalizer_of_conj (U := Subgroup.zpowers d') (fun x hx z hz => ?_)
      (Subgroup.mem_zpowers d')
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [zpow_eq_zpow_emod' m hd'3]
    have hm : m % ((3 : ℕ) : ℤ) = 0 ∨ m % ((3 : ℕ) : ℤ) = 1 ∨ m % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases hm with h | h | h <;> rw [h]
    · simpa using hz
    · simpa using hgen z hz
    · have h2 : d' ^ ((2 : ℤ)) * z * (d' ^ ((2 : ℤ)))⁻¹ = (d' * d') * z * (d' * d')⁻¹ := by
        rw [zpow_two]
      rw [h2]
      exact hgen2 z hz
  have hd'3p : IsPGroup 3 (Subgroup.zpowers d') := IsPGroup.of_card (by
    have hd'1 : d' ≠ 1 := fun h => hd'w (h ▸ Subgroup.one_mem _)
    rw [Nat.card_zpowers, orderOf_eq_prime hd'3 hd'1, pow_one])
  obtain ⟨Q, hQD, hQ3, hQdvd, hQN, -⟩ := CFSG.RankThree.Coprime.exists_sylow_normalized D
    (Subgroup.zpowers d') hd'3p (Subgroup.zpowers_le.mpr hd'D)
  have hd1 : d ≠ 1 := fun h => hdu (h ▸ Subgroup.one_mem _)
  have h3D : 3 ∣ Nat.card D := by
    have := orderOf_dvd_natCard (⟨d, hdD⟩ : ↥D)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hd3 hd1] at this
  have h3Q : 3 ∣ Nat.card Q := hQdvd 1 (by simpa using h3D)
  have hQK : ∀ q ∈ Q, q ∈ K' → q = 1 := fun q hq hqK => by
    obtain ⟨m, hm⟩ := hK'2 ⟨q, hqK⟩
    obtain ⟨n, hn⟩ := hQ3 ⟨q, hq⟩
    exact eq_one_of_two_three (m := m) (n := n) (congrArg Subtype.val hm)
      (congrArg Subtype.val hn)
  have hQle : Nat.card Q ≤ 3 := by
    classical
    choose n k hk hnk using fun q : ↥Q => exists_zpow_mul hdK' (hQD q.2)
    let F : ↥Q → ZMod 3 := fun q => ((n q : ℤ) : ZMod 3)
    have hF : Function.Injective F := by
      intro q₁ q₂ h
      have h' : n q₁ % ((3 : ℕ) : ℤ) = n q₂ % ((3 : ℕ) : ℤ) :=
        (ZMod.intCast_eq_intCast_iff' _ _ 3).mp h
      have hd : d ^ n q₁ = d ^ n q₂ := by
        rw [zpow_eq_zpow_emod' (n q₁) hd3, zpow_eq_zpow_emod' (n q₂) hd3, h']
      have hmem : (q₁ : G)⁻¹ * q₂ ∈ K' := by
        rw [hnk q₁, hnk q₂, hd, mul_inv_rev, show (k q₁)⁻¹ * (d ^ n q₂)⁻¹ * (d ^ n q₂ * k q₂) =
          (k q₁)⁻¹ * k q₂ by group]
        exact K'.mul_mem (K'.inv_mem (hk q₁)) (hk q₂)
      have h1 := hQK _ (Q.mul_mem (Q.inv_mem q₁.2) q₂.2) hmem
      exact Subtype.ext (inv_mul_eq_one.mp h1)
    calc Nat.card Q ≤ Nat.card (ZMod 3) := Nat.card_le_card_of_injective F hF
      _ = 3 := Nat.card_zmod 3
  have hQ3c : Nat.card Q = 3 := le_antisymm hQle (Nat.le_of_dvd Nat.card_pos h3Q)
  obtain ⟨⟨x, hxQ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Q)).mp (by
    intro h
    rw [h, Subgroup.card_bot] at hQ3c
    norm_num at hQ3c)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx3 : x ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Q) (x := ⟨x, hxQ⟩)
    rw [hQ3c] at this
    exact congrArg Subtype.val this
  have hxd' : d' * x = x * d' :=
    commute_of_card_three hQ3c hd'3 (hQN (Subgroup.mem_zpowers d')) hxQ
  have hxw : x ∈ Subgroup.centralizer ({w} : Set G) := hDw (hQD hxQ)
  have hxu : ∀ y ∈ Subgroup.zpowers x, y ∈ Subgroup.centralizer ({u} : Set G) → y = 1 := by
    intro y hy hyu
    by_contra hy1
    have hyQ : y ∈ Q := (Subgroup.zpowers_le.mpr hxQ) hy
    obtain ⟨n, k, hk, hnk⟩ := exists_zpow_mul hdK' (hQD hyQ)
    have hdn : d ^ n ≠ 1 := fun h => hy1 (hQK y hyQ (by rw [hnk, h, one_mul]; exact hk))
    have hku : k ∈ Subgroup.centralizer ({u} : Set G) := hKu hk.1
    have hdnu : d ^ n ∈ Subgroup.centralizer ({u} : Set G) := by
      have : d ^ n = y * k⁻¹ := by rw [hnk]; group
      rw [this]
      exact Subgroup.mul_mem _ hyu (Subgroup.inv_mem _ hku)
    exact hdu ((Subgroup.zpowers_le.mpr hdnu)
      (mem_zpowers_of_pow_three hd3 (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩) hdn))
  have hd'w' : ∀ y ∈ Subgroup.zpowers d', y ∈ Subgroup.centralizer ({w} : Set G) → y = 1 := by
    intro y hy hyw
    by_contra hy1
    exact hd'w ((Subgroup.zpowers_le.mpr hyw) (mem_zpowers_of_pow_three hd'3 hy hy1))
  have hxC : x ∈ Subgroup.centralizer ((Subgroup.zpowers d' : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (show Commute d' x from hxd') m).eq
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers d' : Subgroup G) :
      Set G) := Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hxC)
  set P := Subgroup.zpowers x ⊔ Subgroup.zpowers d' with hP
  have hPset : (P : Set G) = (Subgroup.zpowers x : Set G) * (Subgroup.zpowers d' : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hxN
  have hmemP : ∀ g ∈ P, ∃ a ∈ Subgroup.zpowers x, ∃ b ∈ Subgroup.zpowers d', g = a * b :=
    fun g hg => by
      have hg' : g ∈ (P : Set G) := hg
      rw [hPset] at hg'
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg'
      exact ⟨a, ha, b, hb, rfl⟩
  have hcom : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers d', a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_zpow (show Commute x d' from hxd'.symm) i j))
  have hPH : P ≤ H := sup_le (Subgroup.zpowers_le.mpr (hDH (hQD hxQ)))
    (Subgroup.zpowers_le.mpr hd'H)
  have hpow3 : ∀ {y : G}, y ^ 3 = 1 → ∀ a ∈ Subgroup.zpowers y, a ^ 3 = 1 := by
    intro y hy a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hP3 : ∀ a ∈ P, a ^ 3 = 1 := fun g hg => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hmemP g hg
    have hc : Commute a b := hcom a ha b hb
    rw [hc.mul_pow, hpow3 hx3 a ha, hpow3 hd'3 b hb, one_mul]
  refine ⟨P, hPH, ?_, hP3, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hmemP a ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hmemP b hb
    have hab : a₁ * b₁ = b₁ * a₁ := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₁
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb₁
      exact (Commute.zpow_zpow_self x i j).eq
    have hab' : a₂ * b₂ = b₂ * a₂ := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₂
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb₂
      exact (Commute.zpow_zpow_self d' i j).eq
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [← hcom _ hb₁ _ ha₂]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
      _ = (b₁ * a₁) * (b₂ * a₂) := by rw [hab, hab']
      _ = b₁ * (a₁ * b₂) * a₂ := by group
      _ = b₁ * (b₂ * a₁) * a₂ := by rw [hcom _ ha₁ _ hb₂]
      _ = b₁ * b₂ * (a₁ * a₂) := by group
  · have hPp : IsPGroup 3 P := fun g => ⟨1, Subtype.ext (by simpa using hP3 g g.2)⟩
    obtain ⟨m, hm⟩ := hPp.exists_card_eq
    have hlt : Subgroup.zpowers x < P := by
      refine lt_of_le_of_ne le_sup_left fun h => hd'w ?_
      have : d' ∈ Subgroup.zpowers x := h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers d')
      exact (Subgroup.zpowers_le.mpr hxw) this
    have hcard := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1', hm] at hcard
    have hm2 : 2 ≤ m := by
      by_contra h
      have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hm]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  · intro g hg hgu hgw
    obtain ⟨a, ha, b, hb, rfl⟩ := hmemP g hg
    have hbu : b ∈ Subgroup.centralizer ({u} : Set G) :=
      (Subgroup.zpowers_le.mpr hd'u) hb
    have hau : a ∈ Subgroup.centralizer ({u} : Set G) := by
      have : a = a * b * b⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hgu (Subgroup.inv_mem _ hbu)
    have ha1 := hxu a ha hau
    rw [ha1, one_mul] at hgw ⊢
    exact hd'w' b hb hgw

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
