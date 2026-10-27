module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.GGL48TW.Cent

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem dvd_sub_one_of_pow_prime {p a k : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (h1 : p ∣ k - 1) (hpow : p ^ a ∣ k ^ p - 1) : p ^ (a - 1) ∣ k - 1 := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk1
  · simp
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hpk : ¬ p ∣ k := by
    intro hd
    have h2 : p ∣ (k - 1) + 1 := by rwa [Nat.sub_add_cancel hk]
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h2))
  have hlte := padicValNat.pow_sub_pow hodd hk1 (by simpa using h1) hpk hp.out.ne_zero
  rw [one_pow, padicValNat_self] at hlte
  have hne : k ^ p - 1 ≠ 0 := by
    have : 1 < k ^ p := Nat.one_lt_pow hp.out.ne_zero hk1
    omega
  have hne' : k - 1 ≠ 0 := by omega
  have ha : a ≤ padicValNat p (k ^ p - 1) := (padicValNat_dvd_iff_le hne).mp hpow
  exact (padicValNat_dvd_iff_le hne').mpr (by omega)

theorem dvd_pow_sub_one_of_dvd {p a k : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (ha : 1 ≤ a) (h1 : p ∣ k - 1) : p ^ a ∣ k ^ p ^ (a - 1) - 1 := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk1
  · simp
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hpk : ¬ p ∣ k := by
    intro hd
    have h2 : p ∣ (k - 1) + 1 := by rwa [Nat.sub_add_cancel hk]
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h2))
  have hn0 : p ^ (a - 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hlte := padicValNat.pow_sub_pow hodd hk1 (by simpa using h1) hpk hn0
  rw [one_pow, padicValNat.prime_pow] at hlte
  have hne : k ^ p ^ (a - 1) - 1 ≠ 0 := by
    have : 1 < k ^ p ^ (a - 1) := Nat.one_lt_pow hn0 hk1
    omega
  have hne' : k - 1 ≠ 0 := by omega
  have hv : 1 ≤ padicValNat p (k - 1) := one_le_padicValNat_of_dvd hne' h1
  exact (padicValNat_dvd_iff_le hne).mpr (by omega)

theorem conj_pow_iter {g w : G} {k : ℕ} (h : g * w * g⁻¹ = w ^ k) (j : ℕ) :
    g ^ j * w * (g ^ j)⁻¹ = w ^ (k ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc g ^ (j + 1) * w * (g ^ (j + 1))⁻¹ = g * (g ^ j * w * (g ^ j)⁻¹) * g⁻¹ := by group
      _ = g * w ^ (k ^ j) * g⁻¹ := by rw [ih]
      _ = (g * w * g⁻¹) ^ (k ^ j) := by rw [conj_pow]
      _ = w ^ (k ^ (j + 1)) := by rw [h, ← pow_mul, pow_succ, mul_comm (k ^ j) k]

theorem pow_eq_self_of_dvd {w : G} {m : ℕ} (hm : 1 ≤ m) (h : orderOf w ∣ m - 1) : w ^ m = w := by
  have : w ^ (m - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  calc w ^ m = w ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel hm]
    _ = w := by rw [pow_succ, this, one_mul]

theorem one_le_and_dvd_sub_one [Finite G] {p : ℕ} {g w z : G} {k : ℕ}
    (hk : g * w * g⁻¹ = w ^ k) (hz : z ∈ zpowers w) (hz1 : z ≠ 1) (hzp : orderOf z = p)
    (hgz : g * z * g⁻¹ = z) : 1 ≤ k ∧ p ∣ k - 1 := by
  obtain ⟨e, rfl⟩ := (mem_powers_iff_mem_zpowers).mpr hz
  have hzk : (w ^ e) ^ k = w ^ e := by
    calc (w ^ e) ^ k = (w ^ k) ^ e := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (g * w * g⁻¹) ^ e := by rw [hk]
      _ = g * w ^ e * g⁻¹ := conj_pow
      _ = w ^ e := hgz
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (by simpa using hzk.symm) hz1
    · exact h
  refine ⟨hk1, ?_⟩
  rw [← hzp]
  apply orderOf_dvd_of_pow_eq_one
  have : (w ^ e) ^ (k - 1) * w ^ e = w ^ e := by
    rw [← pow_succ, Nat.sub_add_cancel hk1, hzk]
  simpa using this

theorem mem_of_pow_mem_of_coprime {K : Subgroup G} {n : G} {i j : ℕ} (hi : n ^ i ∈ K)
    (hj : n ^ j ∈ K) (hij : Nat.Coprime i j) : n ∈ K := by
  have h := Nat.gcd_eq_gcd_ab i j
  rw [hij] at h
  have e : n = (n ^ i) ^ (Nat.gcdA i j) * (n ^ j) ^ (Nat.gcdB i j) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h]
    simp
  rw [e]
  exact K.mul_mem (K.zpow_mem hi _) (K.zpow_mem hj _)

theorem exists_eq_zpowers {S : Subgroup G} (h : IsCyclic S) : ∃ w ∈ S, S = zpowers w := by
  obtain ⟨⟨w, hw⟩, hgen⟩ := h.exists_generator
  refine ⟨w, hw, le_antisymm (fun s hs => ?_) ((zpowers_le).mpr hw)⟩
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hgen ⟨s, hs⟩)
  exact mem_zpowers_iff.mpr ⟨i, by simpa using congrArg Subtype.val hi⟩


theorem mem_normalizer_of_conj_mem {H : Subgroup G} [Finite H] {g : G}
    (key : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key y, fun hy => ?_⟩
  let f : H → H := fun z => ⟨g * z * g⁻¹, key z z.2⟩
  have hf : Function.Injective f := fun z z' hzz' => Subtype.ext (by
    have := congrArg Subtype.val hzz'
    simpa [f] using this)
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hf) ⟨g * y * g⁻¹, hy⟩
  have : (z : G) = y := by
    have := congrArg Subtype.val hz
    simpa [f] using this
  exact this ▸ z.2

theorem commutator_sup_le_of_le_normalizer {A N : Subgroup G} (h : A ≤ normalizer (N : Set G)) :
    ⁅A ⊔ N, A ⊔ N⁆ ≤ ⁅A, A⁆ ⊔ N := by
  have hAN : A ⊔ N ≤ normalizer (N : Set G) := sup_le h (le_normalizer)
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have e₁ : g₁ ∈ (A : Set G) * N := by
    rw [← coe_mul_of_left_le_normalizer_right A N h]; exact hg₁
  have e₂ : g₂ ∈ (A : Set G) * N := by
    rw [← coe_mul_of_left_le_normalizer_right A N h]; exact hg₂
  obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := e₁
  obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := e₂
  have e : ⁅a₁ * n₁, a₂ * n₂⁆ =
      (a₁ * ⁅n₁, a₂ * n₂⁆ * a₁⁻¹) * ⁅a₁, a₂⁆ * (a₂ * ⁅a₁, n₂⁆ * a₂⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hc1 : ⁅n₁, a₂ * n₂⁆ ∈ N := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine N.mul_mem hn₁ ?_
    rw [← mul_assoc]
    exact (mem_normalizer_iff.mp (hAN hg₂) _).mp (N.inv_mem hn₁)
  have hc2 : ⁅a₁, n₂⁆ ∈ N := by
    rw [commutatorElement_def]
    exact N.mul_mem ((mem_normalizer_iff.mp (h ha₁) _).mp hn₂) (N.inv_mem hn₂)
  refine (⁅A, A⁆ ⊔ N).mul_mem ((⁅A, A⁆ ⊔ N).mul_mem (mem_sup_right ?_)
    (mem_sup_left (commutator_mem_commutator ha₁ ha₂))) (mem_sup_right ?_)
  · exact (mem_normalizer_iff.mp (h ha₁) _).mp hc1
  · exact (mem_normalizer_iff.mp (h ha₂) _).mp hc2

theorem mul_pow_mul_inv_mem {W F : Subgroup G} (hFW : F ≤ normalizer (W : Set G)) {v n : G}
    (hv : v ∈ W) (hn : n ∈ F) (m : ℕ) : (v * n) ^ m * (n ^ m)⁻¹ ∈ W := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (v * n) ^ (m + 1) * (n ^ (m + 1))⁻¹ =
        ((v * n) ^ m * (n ^ m)⁻¹) * (n ^ m * v * (n ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]; group
    rw [e]
    exact W.mul_mem ih ((mem_normalizer_iff.mp (hFW (F.pow_mem hn m)) v).mp hv)

theorem normalizer_le_centralizer_of_isCyclic {T : Type*} [Group T] [Finite T] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (S : Sylow p T) (hS : IsCyclic (S : Subgroup T)) {z : T}
    (hzS : z ∈ (S : Subgroup T)) (hz1 : z ≠ 1) (hzp : z ^ p = 1) (hzc : ∀ t : T, t * z = z * t) :
    normalizer ((S : Subgroup T) : Set T) ≤ centralizer ((S : Subgroup T) : Set T) := by
  obtain ⟨w, hwS, hSw⟩ := exists_eq_zpowers hS
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨w, hwS⟩
  have ha' : orderOf w = p ^ a := (Subgroup.orderOf_coe (⟨w, hwS⟩ : (S : Subgroup T))).trans ha
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzw : z ∈ zpowers w := hSw ▸ hzS
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at ha'
      rw [ha', zpowers_one_eq_bot] at hzw
      exact hz1 (mem_bot.mp hzw)
    · exact h
  intro n hn
  have hnw : n * w * n⁻¹ ∈ zpowers w := hSw ▸ (mem_normalizer_iff.mp hn w).mp hwS
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr hnw
  have hnz : n * z * n⁻¹ = z := by rw [hzc n, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨hk1, hkp⟩ := one_le_and_dvd_sub_one hk.symm hzw hz1 hzo hnz
  have hNT := dvd_pow_sub_one_of_dvd hp2 hk1 ha1 hkp
  have h1 : n ^ (p ^ (a - 1)) ∈ centralizer ({w} : Set T) := by
    rw [mem_centralizer_singleton_iff]
    have h := conj_pow_iter hk.symm (p ^ (a - 1))
    rw [pow_eq_self_of_dvd (Nat.one_le_pow _ _ hk1) (ha' ▸ hNT)] at h
    calc n ^ p ^ (a - 1) * w = n ^ p ^ (a - 1) * w * (n ^ p ^ (a - 1))⁻¹ * n ^ p ^ (a - 1) := by
          group
      _ = w * n ^ p ^ (a - 1) := by rw [h]
  obtain ⟨e, m, hm, ho⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' p hp.out.one_lt.ne'
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have h2 : n ^ m ∈ (S : Subgroup T) := by
    have hPp : IsPGroup p (zpowers (n ^ m)) := by
      apply IsPGroup.of_card (n := e)
      rw [Nat.card_zpowers, orderOf_pow_of_dvd hm0 (Dvd.intro_left _ ho.symm), ho,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    have hmem : n ^ m ∈ zpowers (n ^ m) ⊓ normalizer (S : Set T) :=
      ⟨mem_zpowers _, pow_mem hn m⟩
    rw [hPp.inf_normalizer_sylow S] at hmem
    exact hmem.2
  have h2' : n ^ m ∈ centralizer ({w} : Set T) := by
    rw [mem_centralizer_singleton_iff]
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hSw ▸ h2)
    rw [← hi]
    exact ((Commute.refl w).zpow_left i).eq
  have hcop : Nat.Coprime (p ^ (a - 1)) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
  have hn' : n * w = w * n :=
    mem_centralizer_singleton_iff.mp (mem_of_pow_mem_of_coprime h1 h2' hcop)
  rw [mem_centralizer_iff]
  intro s hs
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hSw ▸ hs)
  exact ((Commute.zpow_right hn' i).eq).symm

theorem exists_normal_complement {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (S : Sylow p T)
    (hN : normalizer ((S : Subgroup T) : Set T) ≤ centralizer ((S : Subgroup T) : Set T)) :
    ∃ O : Subgroup T, (∀ t : T, t ∈ O ↔ (orderOf t).Coprime p) ∧
      ∀ t : T, ∃ o ∈ O, ∃ s ∈ (S : Subgroup T), t = o * s := by
  refine ⟨(MonoidHom.transferSylow S hN).ker, fun t => ⟨fun ht => ?_, fun ht => ?_⟩, fun t => ?_⟩
  · have hd := MonoidHom.not_dvd_card_ker_transferSylow S hN
    have hot : orderOf t ∣ Nat.card (MonoidHom.transferSylow S hN).ker :=
      Subgroup.orderOf_dvd_natCard _ ht
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr (fun h => hd (h.trans hot)))
  · rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') (MonoidHom.transferSylow S hN t)
    have hdvd : p ^ k ∣ orderOf t := hk ▸ orderOf_map_dvd _ t
    have hk0 : k = 0 := by
      by_contra h0
      have : p ∣ orderOf t := (dvd_pow_self p h0).trans hdvd
      exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd ht.symm this)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · obtain ⟨⟨⟨o, ho⟩, ⟨s, hs⟩⟩, h, -⟩ :=
      (MonoidHom.ker_transferSylow_isComplement' S hN).existsUnique t
    exact ⟨o, ho, s, hs, h.symm⟩

theorem le_zpowers_of_isCyclic [Finite G] {p : ℕ} (hp : p.Prime) {T : Subgroup G}
    (hT : IsCyclic T) (hexp : ∀ t ∈ T, t ^ p = 1) {x : G} (hxT : x ∈ T) (hx1 : x ≠ 1) :
    T ≤ zpowers x := by
  haveI := Fact.mk hp
  obtain ⟨w, hwT, hTw⟩ := exists_eq_zpowers hT
  have hxo : orderOf x = p := orderOf_eq_prime (hexp x hxT) hx1
  have hwo : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one (hexp w hwT)
  have heq : zpowers x = T := by
    apply Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hxT)
    rw [hTw, Nat.card_zpowers, Nat.card_zpowers, hxo]
    exact Nat.le_of_dvd hp.pos hwo
  exact heq.ge

theorem eq_one_of_mem_zpowers [Finite G] {p : ℕ} (hp : p.Prime) {B₁ : Subgroup G} {x c : G}
    (hxo : orderOf x = p) (hxB : x ∉ B₁) (hc : c ∈ zpowers x) (hcB : c ∈ B₁) : c = 1 := by
  by_contra hc1
  have hco : orderOf c = p := by
    have hd : orderOf c ∣ p := hxo ▸ orderOf_dvd_of_mem_zpowers hc
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have heq : zpowers c = zpowers x := Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hc)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hco, hxo])
  have hx : x ∈ zpowers c := heq ▸ mem_zpowers x
  exact hxB ((zpowers_le.mpr hcB) hx)

theorem commute_of_cyclic_invariant [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {Bs B₁ : Subgroup G} {x w : G}
    (hBsp : ∀ b ∈ Bs, b ^ p = 1)
    (hBsC : ∀ g ∈ centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBs : Bs = B₁ ⊔ zpowers x) (hNB : normalizer (Bs : Set G) ≤ normalizer (B₁ : Set G))
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxw : x ∈ zpowers w)
    (hBx : ∀ b ∈ B₁, b * x = x * b)
    (hinv : ∀ b ∈ B₁, b * w * b⁻¹ ∈ zpowers w)
    (htriv : ∀ c ∈ B₁, c ∈ zpowers w → c = 1) {a : ℕ} (ha : orderOf w = p ^ a) :
    ∀ b ∈ B₁, b * w = w * b := by
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hB₁Bs : B₁ ≤ Bs := hBs ▸ le_sup_left
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at ha
      rw [ha, zpowers_one_eq_bot] at hxw
      exact hx1 (mem_bot.mp hxw)
    · exact h
  have hkb : ∀ b ∈ B₁, ∃ k : ℕ, b * w * b⁻¹ = w ^ k ∧ 1 ≤ k ∧ p ∣ k - 1 := by
    intro b hb
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr (hinv b hb)
    have hbx : b * x * b⁻¹ = x := by rw [hBx b hb, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨h1, h2⟩ := one_le_and_dvd_sub_one hk.symm hxw hx1 hxo hbx
    exact ⟨k, hk.symm, h1, h2⟩
  have hxwc : x * w = w * x := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hxw
    exact ((Commute.refl w).zpow_left i).eq
  have key : ∀ b ∈ B₁, ∃ c ∈ Bs, c ∈ zpowers w ∧ b * w * b⁻¹ = c * w := by
    intro b hb
    obtain ⟨k, hk, hk1, hkp⟩ := hkb b hb
    have hkpow : p ^ a ∣ k ^ p - 1 := by
      rw [← ha]
      apply orderOf_dvd_of_pow_eq_one
      have h := conj_pow_iter hk p
      rw [hBsp b (hB₁Bs hb), one_mul, inv_one, mul_one] at h
      have h' : w ^ (k ^ p - 1) * w = w := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hk1), ← h]
      simpa using h'
    have hkp1 : p ^ (a - 1) ∣ k - 1 := dvd_sub_one_of_pow_prime hp2 hk1 hkp hkpow
    have hcp : (w ^ (k - 1)) ^ p = 1 := by
      rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [ha]
      calc p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel ha1]
        _ ∣ (k - 1) * p := Nat.mul_dvd_mul_right hkp1 p
    have hcB : ∀ b' ∈ B₁, b' * w ^ (k - 1) = w ^ (k - 1) * b' := by
      intro b' hb'
      obtain ⟨k', hk', hk'1, hk'p⟩ := hkb b' hb'
      have h1 : b' * w ^ (k - 1) * b'⁻¹ = (w ^ (k - 1)) ^ k' := by
        rw [← conj_pow, hk', ← pow_mul, ← pow_mul, mul_comm]
      have h2 : (w ^ (k - 1)) ^ k' = w ^ (k - 1) :=
        pow_eq_self_of_dvd hk'1 ((orderOf_dvd_of_pow_eq_one hcp).trans hk'p)
      calc b' * w ^ (k - 1) = b' * w ^ (k - 1) * b'⁻¹ * b' := by group
        _ = w ^ (k - 1) * b' := by rw [h1, h2]
    have hcx : x * w ^ (k - 1) = w ^ (k - 1) * x := (Commute.pow_right hxwc (k - 1)).eq
    have hcBs : w ^ (k - 1) ∈ Bs := by
      apply hBsC _ _ hcp
      have hle : Bs ≤ centralizer ({w ^ (k - 1)} : Set G) := by
        rw [hBs]
        exact sup_le (fun b' hb' => mem_centralizer_singleton_iff.mpr (hcB b' hb'))
          ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr hcx))
      rw [mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_singleton_iff.mp (hle hh)
    refine ⟨w ^ (k - 1), hcBs, pow_mem (mem_zpowers w) _, ?_⟩
    rw [hk, ← pow_succ, Nat.sub_add_cancel hk1]
  have hconj : ∀ b ∈ B₁, ∀ c : G, b * w * b⁻¹ = c * w → w * b * w⁻¹ = c⁻¹ * b := by
    intro b _ c hc
    calc w * b * w⁻¹ = c⁻¹ * (c * w * b * w⁻¹) := by group
      _ = c⁻¹ * (b * w * b⁻¹ * b * w⁻¹) := by rw [← hc]
      _ = c⁻¹ * b := by group
  have hwN : w ∈ normalizer (Bs : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro g hg
    have hle : B₁ ⊔ zpowers x ≤ Bs.comap (MulAut.conj w).toMonoidHom := by
      refine sup_le (fun b hb => ?_) ((zpowers_le).mpr ?_)
      · obtain ⟨c, hcBs, -, hc⟩ := key b hb
        rw [mem_comap]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hconj b hb c hc]
        exact Bs.mul_mem (Bs.inv_mem hcBs) (hB₁Bs hb)
      · rw [mem_comap]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← hxwc, mul_assoc, mul_inv_cancel, mul_one]
        rw [hBs]; exact mem_sup_right (mem_zpowers x)
    rw [hBs] at hg
    have := hle hg
    rw [mem_comap] at this
    simpa [MulAut.conj_apply] using this
  have hwN₁ := hNB hwN
  intro b hb
  obtain ⟨c, -, hcw, hc⟩ := key b hb
  have hwb : w * b * w⁻¹ ∈ B₁ := (mem_normalizer_iff.mp hwN₁ b).mp hb
  rw [hconj b hb c hc] at hwb
  have hcB : c ∈ B₁ := by
    have : c⁻¹ ∈ B₁ := by
      have := B₁.mul_mem hwb (B₁.inv_mem hb)
      simpa using this
    simpa using B₁.inv_mem this
  have hc1 : c = 1 := htriv c hcB hcw
  rw [hc1, one_mul] at hc
  calc b * w = b * w * b⁻¹ * b := by group
    _ = w * b := by rw [hc]

theorem exists_invariant_cyclic_complement [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {Y B₁ : Subgroup G} {z : G}
    (hB₁N : B₁ ≤ normalizer (Y : Set G)) (hB₁p : IsPGroup p B₁)
    (hcyc : ∀ S : Subgroup G, S ≤ Y → IsPGroup p S → IsCyclic S)
    (hzY : z ∈ Y) (hz1 : z ≠ 1) (hzp : z ^ p = 1) (hzc : ∀ y ∈ Y, y * z = z * y) :
    ∃ (w : G) (O : Subgroup G) (a : ℕ), w ∈ Y ∧ z ∈ zpowers w ∧ orderOf w = p ^ a ∧
      (∀ b ∈ B₁, b * w * b⁻¹ ∈ zpowers w) ∧
      (∀ g : G, g ∈ O ↔ g ∈ Y ∧ (orderOf g).Coprime p) ∧
      ∀ g ∈ Y, ∃ o ∈ O, ∃ s ∈ zpowers w, g = o * s := by
  let φ : B₁ →* MulAut Y := (Y.normalizerMonoidHom).comp (Subgroup.inclusion hB₁N)
  letI : MulDistribMulAction B₁ Y := MulDistribMulAction.compHom Y φ
  have hsmul : ∀ (b : B₁) (t : Y), ((b • t : Y) : G) = (b : G) * t * (b : G)⁻¹ := by
    intro b t
    show ((Y.normalizerMonoidHom (Subgroup.inclusion hB₁N b)) t : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hcard : ¬ p ∣ Nat.card (Sylow p Y) := by
    have h := card_sylow_modEq_one p Y
    intro hd
    have h0 : Nat.card (Sylow p Y) % p = 0 := Nat.mod_eq_zero_of_dvd hd
    have h1 : Nat.card (Sylow p Y) % p = 1 := by
      rw [h]; exact Nat.mod_eq_of_lt hp.out.one_lt
    omega
  obtain ⟨S, hS⟩ := hB₁p.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p Y) hcard
  have hSfix : ∀ b : B₁, b • S = S := fun b => hS b
  have hinvS : ∀ b : B₁, ∀ t ∈ (S : Subgroup Y), b • t ∈ (S : Subgroup Y) := by
    intro b t ht
    have h : b • t ∈ ((b • S : Sylow p Y) : Subgroup Y) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul t b _ ht
    rwa [hSfix b] at h
  set S' : Subgroup G := (S : Subgroup Y).map Y.subtype with hS'
  have hS'Y : S' ≤ Y := by
    rintro g ⟨t, -, rfl⟩; exact t.2
  have hS'p : IsPGroup p S' := S.isPGroup'.map _
  have hS'c : IsCyclic S' := hcyc S' hS'Y hS'p
  obtain ⟨w, hwS', hS'w⟩ := exists_eq_zpowers hS'c
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hS'p) ⟨w, hwS'⟩
  have ha' : orderOf w = p ^ a := (Subgroup.orderOf_coe (⟨w, hwS'⟩ : S')).trans ha
  have hSc : IsCyclic (S : Subgroup Y) := by
    let e := (S : Subgroup Y).equivMapOfInjective Y.subtype Y.subtype_injective
    haveI := hS'c
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  set z' : Y := ⟨z, hzY⟩ with hz'
  have hz'c : ∀ t : Y, t * z' = z' * t := fun t => Subtype.ext (hzc t t.2)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'p : z' ^ p = 1 := Subtype.ext (by simpa using hzp)
  have hz'S : z' ∈ (S : Subgroup Y) := by
    have hPp : IsPGroup p (zpowers z') := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, orderOf_eq_prime hz'p hz'1, pow_one]
    have hzN : z' ∈ normalizer ((S : Subgroup Y) : Set Y) := by
      rw [mem_normalizer_iff]
      intro h
      rw [← hz'c h, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : z' ∈ zpowers z' ⊓ normalizer (S : Set Y) := ⟨mem_zpowers _, hzN⟩
    rw [hPp.inf_normalizer_sylow S] at hmem
    exact hmem.2
  have hNC := normalizer_le_centralizer_of_isCyclic hp2 S hSc hz'S hz'1 hz'p hz'c
  obtain ⟨O₀, hO₀, hdec⟩ := exists_normal_complement S hNC
  refine ⟨w, O₀.map Y.subtype, a, hS'Y hwS', ?_, ha', ?_, ?_, ?_⟩
  · rw [← hS'w]; exact ⟨z', hz'S, rfl⟩
  · intro b hb
    rw [← hS'w]
    rw [hS'] at hwS'
    obtain ⟨t, ht, rfl⟩ := hwS'
    refine ⟨(⟨b, hb⟩ : B₁) • t, hinvS ⟨b, hb⟩ t ht, ?_⟩
    rw [Subgroup.coe_subtype, hsmul]
  · intro g
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t.2, ?_⟩
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact (hO₀ t).mp ht
    · rintro ⟨hgY, hg⟩
      refine ⟨⟨g, hgY⟩, (hO₀ _).mpr ?_, rfl⟩
      rwa [Subgroup.orderOf_mk]
  · intro g hg
    obtain ⟨o, ho, s, hs, hos⟩ := hdec ⟨g, hg⟩
    refine ⟨o, ⟨o, ho, rfl⟩, s, ?_, ?_⟩
    · rw [← hS'w]; exact ⟨s, hs, rfl⟩
    · have := congrArg Subtype.val hos
      simpa using this


end CFSG.StandardType.GGL48TW.Cent
