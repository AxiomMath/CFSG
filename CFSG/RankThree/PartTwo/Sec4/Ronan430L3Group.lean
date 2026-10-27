module

public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan430L3

open CFSG

variable {G : Type*} [Group G]

theorem eq_one_or_eq_or_eq_sq_of_mem_zpowers [Finite G] {c x : G} (hc : orderOf c = 3)
    (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c ∨ x = c ^ 2 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hc] at hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range] at hj
  interval_cases j <;> simp

theorem eq_one_or_eq_or_eq_inv_of_pow_three {K : Type*} [Field K] {u v : K} (hu : u ^ 3 = 1)
    (hv : v ^ 3 = 1) (hv1 : v ≠ 1) : u = 1 ∨ u = v ∨ u = v⁻¹ := by
  have hs : v ^ 2 + v + 1 = 0 := by
    have h : (v - 1) * (v ^ 2 + v + 1) = 0 := by linear_combination hv
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hv1)
  have hvinv : v⁻¹ = v ^ 2 := inv_eq_of_mul_eq_one_right (by linear_combination hv)
  have h : (u - 1) * (u - v) * (u - v ^ 2) = 0 := by
    linear_combination hu - hv - (u ^ 2 - u * v) * hs
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (by rw [hvinv]; exact sub_eq_zero.mp h))

theorem exists_mul_of_mem_sup [Finite G] {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = g := by
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H K hc
  have hg' : g ∈ ((H ⊔ K : Subgroup G) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨h, hh, k, hk, hhk⟩ := Set.mem_mul.mp hg'
  exact ⟨h, hh, k, hk, hhk⟩

theorem card_sup_le_of_commute [Finite G] {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    Nat.card (H ⊔ K : Subgroup G) ≤ Nat.card H * Nat.card K := by
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H K hc
  rw [← hcard]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem false_of_transitive [Finite G] {A L : Subgroup G} {a c : G}
    (hA : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (haA : a ∈ A)
    (haC : a ∈ Subgroup.centralizer (L : Set G))
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hcA : c ∈ A)
    (hca : c ∉ Subgroup.zpowers a)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hsup : A ⊔ L = Subgroup.zpowers a ⊔ L)
    (htrans : ∀ x ∈ A ⊓ L, x ≠ 1 → ∀ y ∈ A ⊓ L, y ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G), n * x * n⁻¹ = y) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.2
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hzaA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  have hzaC : Subgroup.zpowers a ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr haC
  have haL : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hzaC hx) y hy).symm
  have hdec : ∀ x ∈ A, ∃ h ∈ Subgroup.zpowers a, ∃ l ∈ A ⊓ L, h * l = x := by
    intro x hx
    have hx' : x ∈ Subgroup.zpowers a ⊔ L := hsup ▸ Subgroup.mem_sup_left hx
    obtain ⟨h, hh, l, hl, rfl⟩ := exists_mul_of_mem_sup haL hx'
    refine ⟨h, hh, l, ⟨?_, hl⟩, rfl⟩
    have : l = h⁻¹ * (h * l) := by group
    rw [this]
    exact A.mul_mem (A.inv_mem (hzaA hh)) hx
  have hzaL : ∀ h ∈ Subgroup.zpowers a, h ∈ L → h = 1 := fun h hh hhL => by
    have hmem : h ∈ L ⊓ Subgroup.centralizer (L : Set G) := ⟨hhL, hzaC hh⟩
    rw [hLC, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨h₀, hh₀, l₀, hl₀, rfl⟩ := hdec c hcA
  have hl₀1 : l₀ ≠ 1 := fun h => hca (by rw [h, mul_one]; exact hh₀)
  have hl₀A : l₀ ∈ A := (Subgroup.mem_inf.mp hl₀).1
  have hl₀L : l₀ ∈ L := (Subgroup.mem_inf.mp hl₀).2
  have hco : orderOf (h₀ * l₀) = 3 :=
    orderOf_eq_prime (hA3 _ hcA) fun h => hca (h ▸ Subgroup.one_mem _)
  have hconjA : ∀ m ∈ L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G), ∀ x ∈ A,
      m * x * m⁻¹ ∈ A := by
    intro m hm x hx
    obtain ⟨hmL, hmN⟩ := Subgroup.mem_inf.mp hm
    obtain ⟨h, hh, l, hl, rfl⟩ := hdec x hx
    have hl' : m * l * m⁻¹ ∈ A ⊓ L := (Subgroup.mem_normalizer_iff.mp hmN l).mp hl
    have hmh : m * h * m⁻¹ = h := by rw [(haL h hh m hmL).symm, mul_inv_cancel_right]
    have : m * (h * l) * m⁻¹ = (m * h * m⁻¹) * (m * l * m⁻¹) := by group
    rw [this, hmh]
    exact A.mul_mem (hzaA hh) (Subgroup.mem_inf.mp hl').1
  have hn : ∀ n ∈ L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G),
      n * l₀ * n⁻¹ ∈ Subgroup.zpowers l₀ := by
    intro n hn
    obtain ⟨hnL, -⟩ := Subgroup.mem_inf.mp hn
    have hnh : ∀ h ∈ Subgroup.zpowers a, n * h * n⁻¹ = h := fun h hh => by
      rw [(haL h hh n hnL).symm, mul_inv_cancel_right]
    have hnA : n ∈ Subgroup.normalizer (A : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hconjA n hn x, fun hx => ?_⟩
      have := hconjA n⁻¹ (inv_mem hn) _ hx
      simpa [mul_assoc] using this
    have hnc := (Subgroup.mem_normalizer_iff.mp (hW hnA) (h₀ * l₀)).mp
      (Subgroup.mem_zpowers _)
    have hnl : n * l₀ * n⁻¹ ∈ L := L.mul_mem (L.mul_mem hnL hl₀L) (L.inv_mem hnL)
    have e0 : n * (h₀ * l₀) * n⁻¹ = h₀ * (n * l₀ * n⁻¹) := by
      have : n * (h₀ * l₀) * n⁻¹ = (n * h₀ * n⁻¹) * (n * l₀ * n⁻¹) := by group
      rw [this, hnh h₀ hh₀]
    rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers hco hnc with h | h | h
    · exfalso
      apply hca
      have : h₀ * l₀ = n⁻¹ * (n * (h₀ * l₀) * n⁻¹) * n := by group
      rw [this, h]
      simp
    · rw [e0] at h
      have : n * l₀ * n⁻¹ = l₀ := mul_left_cancel h
      rw [this]
      exact Subgroup.mem_zpowers l₀
    · rw [e0] at h
      have hcomm₀ : h₀ * l₀ = l₀ * h₀ := hcomm _ (hzaA hh₀) _ hl₀A
      have e1 : (h₀ * l₀) ^ 2 = h₀ ^ 2 * l₀ ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        calc h₀ * l₀ * (h₀ * l₀) = h₀ * (l₀ * h₀) * l₀ := by group
          _ = h₀ * (h₀ * l₀) * l₀ := by rw [hcomm₀]
          _ = h₀ * h₀ * (l₀ * l₀) := by group
      rw [e1] at h
      have e2 : n * l₀ * n⁻¹ = h₀ * l₀ ^ 2 := by
        have : n * l₀ * n⁻¹ = h₀⁻¹ * (h₀ * (n * l₀ * n⁻¹)) := by group
        rw [this, h]
        group
      have hh₀L : h₀ ∈ L := by
        have : h₀ = (n * l₀ * n⁻¹) * (l₀ ^ 2)⁻¹ := by rw [e2]; group
        rw [this]
        exact L.mul_mem hnl (L.inv_mem (L.pow_mem hl₀L 2))
      rw [e2, hzaL h₀ hh₀ hh₀L, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers l₀) 2
  have hle : A ⊓ L ≤ Subgroup.zpowers l₀ := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Subgroup.one_mem _
    obtain ⟨n, hn', rfl⟩ := htrans l₀ hl₀ hl₀1 y hy hy1
    exact hn n hn'
  have hAle : A ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers l₀ := by
    intro x hx
    obtain ⟨h, hh, l, hl, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right (hle hl))
  have hc' : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers l₀, x * y = y * x :=
    fun x hx y hy => hcomm x (hzaA hx) y (Subgroup.zpowers_le.mpr hl₀A hy)
  have h1 := Subgroup.card_le_of_le hAle
  have h2 := card_sup_le_of_commute hc'
  rw [Nat.card_zpowers, Nat.card_zpowers] at h2
  have ha3 := orderOf_le_of_pow_eq_one (by norm_num) (hA3 a haA)
  have hl3 := orderOf_le_of_pow_eq_one (by norm_num) (hA3 l₀ hl₀A)
  have : orderOf a * orderOf l₀ ≤ 3 * 3 := Nat.mul_le_mul ha3 hl3
  omega

theorem false_of_gen [Finite G] {A L R H : Subgroup G} {c x₀ : G}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hHA : H ≤ A) (hcH : c ∈ H) (hc1 : c ≠ 1)
    (hx₀A : x₀ ∈ A) (hx₀H : x₀ ∉ H)
    (hinv : ∀ y ∈ A, y ∉ H → ∀ t ∈ L, t * t = 1 → y * t = t * y → t = 1)
    (hRL : R ≤ L) (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRc : ⁅R, Subgroup.zpowers c⁆ = R) (hR1 : R ≠ ⊥) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcA := hHA hcH
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.2
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hco : orderOf c = 3 := orderOf_eq_prime (hA3 c hcA) hc1
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀H (h ▸ H.one_mem)
  have hx₀o : orderOf x₀ = 3 := orderOf_eq_prime (hA3 x₀ hx₀A) hx₀1
  set F : Subgroup G := Subgroup.zpowers x₀ ⊔ Subgroup.zpowers c with hF
  have hzx : Subgroup.zpowers x₀ ≤ A := Subgroup.zpowers_le.mpr hx₀A
  have hzc : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  have hFA : F ≤ A := sup_le hzx hzc
  have hFel : CFSG.Open.IsElemAbelian 3 F :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 3 hA hFA
  have hFp : IsPGroup 3 F := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 3 F hFel
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hFp
  have h3dvd : 3 ∣ Nat.card F := by
    have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers c ≤ F)
    rwa [Nat.card_zpowers, hco] at this
  have hne3 : Nat.card F ≠ 3 := by
    intro h3
    have heq : Subgroup.zpowers c = F :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3, Nat.card_zpowers, hco])
    apply hx₀H
    have : x₀ ∈ F := Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀)
    rw [← heq] at this
    exact Subgroup.zpowers_le.mpr hcH this
  have hF9 : 3 ^ 2 ≤ Nat.card F := by
    rw [hk] at h3dvd hne3 ⊢
    rcases k with _ | _ | k
    · norm_num at h3dvd
    · norm_num at hne3
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR2
    rw [hm]
    exact Nat.Coprime.pow_right m (by norm_num)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_inf_centralizer Nat.prime_three hFel hF9
    (hFA.trans hAR) hcop
  have hxc : ∀ x ∈ Subgroup.zpowers x₀, ∀ y ∈ Subgroup.zpowers c, x * y = y * x :=
    fun x hx y hy => hcomm x (hzx hx) y (hzc hy)
  have hout : ∀ b ∈ F, b ∉ Subgroup.zpowers c → b ∉ H := by
    intro b hb hbc hbH
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hxc hb
    have hxH : x ∈ H := by
      have : x = (x * y) * y⁻¹ := by group
      rw [this]
      exact H.mul_mem hbH (H.inv_mem (Subgroup.zpowers_le.mpr hcH hy))
    rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers hx₀o hx with h | h | h
    · exact hbc (by rw [h, one_mul]; exact hy)
    · exact hx₀H (h ▸ hxH)
    · apply hx₀H
      have : x₀ = x * x := by
        rw [h, ← pow_add]
        calc x₀ = x₀ ^ 3 * x₀ := by rw [hA3 x₀ hx₀A, one_mul]
          _ = x₀ ^ (2 + 2) := by group
      rw [this]
      exact H.mul_mem hxH hxH
  have hRcen : R ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [← hgen]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    by_cases hbc : b ∈ Subgroup.zpowers c
    ·
      have hbo : orderOf b = 3 := orderOf_eq_prime (hA3 b (hFA hb)) hb1
      have heq : Subgroup.zpowers b = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbc)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hbo, hco])
      have hcb : c ∈ Subgroup.zpowers b := heq ▸ Subgroup.mem_zpowers c
      intro x hx
      obtain ⟨-, hxb⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hxb ⊢
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcb
      rw [← hm]
      exact (Commute.zpow_right (show Commute x b from hxb) m).eq
    ·
      have hbH := hout b hb hbc
      have hbot : R ⊓ Subgroup.centralizer ({b} : Set G) = ⊥ := by
        by_contra hne
        have h2' : IsPGroup 2 (R ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) :=
          hR2.to_le inf_le_left
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2'
        have hm0 : m ≠ 0 := by
          rintro rfl
          exact hne (Subgroup.eq_bot_of_card_eq _ (by simpa using hm))
        obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hm]; exact dvd_pow_self 2 hm0)
        have htR : (t : G) ∈ R := (Subgroup.mem_inf.mp t.2).1
        have htb : (t : G) * b = b * t :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp t.2).2
        have ht2 : (t : G) * t = 1 := by
          have h := pow_orderOf_eq_one t
          rw [ht, pow_two] at h
          exact congrArg Subtype.val h
        have h1 := hinv b (hFA hb) hbH t (hRL htR) ht2 htb.symm
        have : t = 1 := Subtype.ext h1
        rw [this, orderOf_one] at ht
        omega
      rw [hbot]
      exact bot_le
  have hbot : ⁅R, Subgroup.zpowers c⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (hRcen hx)
    exact ((Commute.zpow_left (Commute.symm hxc) m)).eq
  rw [hRc] at hbot
  exact hR1 hbot

theorem le_normalizer_of_isComponent [Finite G] {A L R : Subgroup G} (hL : IsComponent L)
    (hZ : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1) (hRL : R ≤ L) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR1 : R ≠ ⊥) :
    A ≤ Subgroup.normalizer (L : Set G) := by
  intro x hxA
  set L' : Subgroup G := L.map (MulAut.conj x).toMonoidHom with hL'def
  have hL' : IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hL
  have hmem : ∀ h ∈ L, x * h * x⁻¹ ∈ L' := fun h hh => ⟨h, hh, rfl⟩
  rcases CFSG.LocalCores.distinct_components_commute hL' hL with heq | hc
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hmem h hh
      rwa [heq] at this
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', he⟩ := hh
      have : h' = h := by
        have he' : x * h' * x⁻¹ = x * h * x⁻¹ := he
        have := congrArg (fun g => x⁻¹ * g * x) he'
        simpa [mul_assoc] using this
      exact this ▸ hh'
  · exfalso
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have hrL : r ∈ L := hRL hr
    have hr' : x⁻¹ * r * x⁻¹⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hAR (A.inv_mem hxA)) r).mp hr
    have hrL' : r ∈ L' := by
      have := hmem _ (hRL hr')
      simpa [mul_assoc] using this
    have hcent : L' ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    have hrc : ∀ l ∈ L, r * l = l * r := fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hcent hrL') l hl).symm
    have hr3 : r ^ 3 = 1 := hZ r hrL hrc
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    have hk' : r ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h1 : orderOf r ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hr3) (orderOf_dvd_of_pow_eq_one hk')
    rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    rw [Subgroup.mem_bot]
    exact h1

end CFSG.RankThree.PartTwo.Sec4.Ronan430L3
