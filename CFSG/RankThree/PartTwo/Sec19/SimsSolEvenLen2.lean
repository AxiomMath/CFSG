module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4b
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.CGT.PushingUpLit.SolK.SwapVec
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

namespace H2

section Stab

variable {G : Type} [Group G]

theorem conj_eq_of_mem_zpowers {x a z : G} (hax : a * x * a⁻¹ = x)
    (hz : z ∈ Subgroup.zpowers x) : a * z * a⁻¹ = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [← conj_zpow, hax]

@[expose] def stabSub (K P : Subgroup G) (x : G) (hxK : ∀ k ∈ K, k * x * k⁻¹ = x) : Subgroup G where
  carrier := {a | a ∈ K ∧ ∀ p ∈ P, a * p * a⁻¹ * p⁻¹ ∈ Subgroup.zpowers x}
  mul_mem' := by
    rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
    refine ⟨K.mul_mem haK hbK, fun p hp => ?_⟩
    have e : a * b * p * (a * b)⁻¹ * p⁻¹ =
        a * (b * p * b⁻¹ * p⁻¹) * a⁻¹ * (a * p * a⁻¹ * p⁻¹) := by group
    rw [e, conj_eq_of_mem_zpowers (hxK a haK) (hb p hp)]
    exact Subgroup.mul_mem _ (hb p hp) (ha p hp)
  one_mem' := ⟨K.one_mem, fun p _ => by simpa using Subgroup.one_mem _⟩
  inv_mem' := by
    rintro a ⟨haK, ha⟩
    refine ⟨K.inv_mem haK, fun p hp => ?_⟩
    have e : a⁻¹ * p * a⁻¹⁻¹ * p⁻¹ = a⁻¹ * (a * p * a⁻¹ * p⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e, conj_eq_of_mem_zpowers (hxK a⁻¹ (K.inv_mem haK))
      (Subgroup.inv_mem _ (ha p hp))]
    exact Subgroup.inv_mem _ (ha p hp)

variable [Finite G]

theorem stabSub_le_pCoreOf {K : Subgroup G} {x : G} (hxK : ∀ k ∈ K, k * x * k⁻¹ = x)
    (hx2 : ∃ j : ℕ, x ^ (2 ^ j) = 1)
    (hcons : ∀ k ∈ K, (∀ p ∈ CFSG.Open.pCoreOf 2 K, p * k = k * p) →
      k ∈ CFSG.Open.pCoreOf 2 K) :
    stabSub K (CFSG.Open.pCoreOf 2 K) x hxK ≤ CFSG.Open.pCoreOf 2 K := by
  classical
  obtain ⟨j₀, hj₀⟩ := hx2
  set P := CFSG.Open.pCoreOf 2 K with hP
  set S := stabSub K P x hxK with hS
  have hSK : S ≤ K := fun a ha => ha.1
  have hnorm : ∀ k ∈ K, ∀ a ∈ S, k * a * k⁻¹ ∈ S := by
    rintro k hk a ⟨haK, ha⟩
    refine ⟨K.mul_mem (K.mul_mem hk haK) (K.inv_mem hk), fun p hp => ?_⟩
    have hp' : k⁻¹ * p * k ∈ P := by
      have := pCoreOf_normalized K (K.inv_mem hk) hp
      simpa using this
    have e : k * a * k⁻¹ * p * (k * a * k⁻¹)⁻¹ * p⁻¹ =
        k * (a * (k⁻¹ * p * k) * a⁻¹ * (k⁻¹ * p * k)⁻¹) * k⁻¹ := by group
    rw [e, conj_eq_of_mem_zpowers (hxK k hk) (ha _ hp')]
    exact ha _ hp'
  have h2 : ∀ b ∈ S, ∃ j : ℕ, b ^ (2 ^ j) = 1 := by
    intro b hb
    obtain ⟨e, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos b).ne'
    refine ⟨e, ?_⟩
    set u : G := b ^ (2 ^ e) with hu
    have huS : u ∈ S := S.pow_mem hb _
    have hum : u ^ m = 1 := by
      rw [hu, ← pow_mul, ← hbm]
      exact pow_orderOf_eq_one b
    have hcomm : ∀ p ∈ P, p * u = u * p := by
      intro p hp
      obtain ⟨z, hz⟩ : ∃ z : G, z = u * p * u⁻¹ * p⁻¹ := ⟨_, rfl⟩
      have hzx : z ∈ Subgroup.zpowers x := hz ▸ huS.2 p hp
      have hpow : ∀ k : ℕ, u ^ k * p * (u ^ k)⁻¹ = z ^ k * p := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hz1 : u * z ^ k * u⁻¹ = z ^ k :=
            conj_eq_of_mem_zpowers (hxK u huS.1) (Subgroup.pow_mem _ hzx k)
          have hz2 : u * p * u⁻¹ = z * p := by rw [hz]; group
          calc u ^ (k + 1) * p * (u ^ (k + 1))⁻¹
              = u * (u ^ k * p * (u ^ k)⁻¹) * u⁻¹ := by group
            _ = u * (z ^ k * p) * u⁻¹ := by rw [ih]
            _ = (u * z ^ k * u⁻¹) * (u * p * u⁻¹) := by group
            _ = z ^ (k + 1) * p := by rw [hz1, hz2, pow_succ, mul_assoc]
      have hzm : z ^ m = 1 := by
        have h1 := hpow m
        rw [hum] at h1
        have h3 : z ^ m * p = 1 * p := by rw [← h1]; group
        exact mul_right_cancel h3
      have hz2 : z ^ (2 ^ j₀) = 1 := by
        obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 hzx
        rw [← hl, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hj₀, one_zpow]
      have hz1 : z = 1 := eq_one_of_pow_odd hm hzm hz2
      have : u * p * u⁻¹ = p := by
        have h4 : u * p * u⁻¹ * p⁻¹ = 1 := by rw [← hz]; exact hz1
        exact mul_inv_eq_one.1 h4
      calc p * u = (u * p * u⁻¹) * u := by rw [this]
        _ = u * p := by group
    have huK : u ∈ K := huS.1
    have huP : u ∈ P := hcons u huK hcomm
    obtain ⟨j, hj⟩ := exists_two_pow_of_mem_pCoreOf K huP
    exact eq_one_of_pow_odd hm hum hj
  have hS2 : IsPGroup 2 S := isPGroup_two_of_forall h2
  exact le_pCoreOf_of_normalized hSK hnorm hS2

end Stab

section Count

variable {A B : Type*} [Group A] [Group B] [Finite A]

theorem card_subtype_le_mul [Finite B] (f : A →* B) (S : Set B) (n : ℕ)
    (hker : Nat.card f.ker ≤ n) : Nat.card {a : A // f a ∈ S} ≤ Nat.card S * n := by
  classical
  let s : B → A := fun b => if h : ∃ a, f a = b then h.choose else 1
  have hs : ∀ a, f (s (f a)) = f a := by
    intro a
    have h : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [s, dif_pos h]
    exact h.choose_spec
  let φ : {a : A // f a ∈ S} → S × f.ker := fun a =>
    (⟨f a.1, a.2⟩, ⟨(s (f a.1))⁻¹ * a.1, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs]
      exact inv_mul_cancel _⟩)
  have hφ : Function.Injective φ := by
    intro a b h
    have h1 : f a.1 = f b.1 := congrArg (fun p => (p.1 : B)) h
    have h2 : (s (f a.1))⁻¹ * a.1 = (s (f b.1))⁻¹ * b.1 := congrArg (fun p => (p.2 : A)) h
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod] at this
  exact this.trans (Nat.mul_le_mul_left _ hker)

theorem card_range_le_two (H : Subgroup B) (y : B) (h : ∀ b ∈ H, b = 1 ∨ b = y) :
    Nat.card H ≤ 2 := by
  have hsub : (H : Set B) ⊆ {1, y} := fun b hb => by
    rcases h b hb with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have h1 : Nat.card H ≤ Nat.card ({1, y} : Set B) := Nat.card_mono (Set.toFinite _) hsub
  rw [Nat.card_coe_set_eq] at h1
  have h2 : ({1, y} : Set B).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  omega

theorem card_le_ker_mul (π : A →* B) (c : A →* A) (y : B) (hc : ∀ a, π (c a) = 1 ∨ π (c a) = y) :
    Nat.card A ≤ Nat.card c.ker * (2 * Nat.card π.ker) := by
  classical
  have h1 := Subgroup.card_ker_mul_card_range c
  let π' : c.range →* B := π.comp c.range.subtype
  have h2 := Subgroup.card_ker_mul_card_range π'
  have h3 : Nat.card π'.ker ≤ Nat.card π.ker := by
    refine Nat.card_le_card_of_injective
      (fun a : π'.ker => (⟨((a : c.range) : A), a.2⟩ : π.ker)) ?_
    intro a b hab
    have := congrArg (fun p : π.ker => (p : A)) hab
    exact Subtype.ext (Subtype.ext this)
  have h4 : Nat.card π'.range ≤ 2 := by
    refine card_range_le_two π'.range y ?_
    rintro _ ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
    exact hc a
  have h5 : Nat.card c.range ≤ 2 * Nat.card π.ker := by
    calc Nat.card c.range = Nat.card π'.ker * Nat.card π'.range := h2.symm
      _ ≤ Nat.card π.ker * 2 := Nat.mul_le_mul h3 h4
      _ = 2 * Nat.card π.ker := mul_comm _ _
  calc Nat.card A = Nat.card c.ker * Nat.card c.range := h1.symm
    _ ≤ Nat.card c.ker * (2 * Nat.card π.ker) := Nat.mul_le_mul_left _ h5

theorem card_le_two_mul_ker (π : A →* B) (c : A →* A) (y : B)
    (hc : ∀ a, π (c a) = 1 ∨ π (c a) = y) (x : A) (hxy : π x = y) (hxc : x ∉ c.range)
    (hy : ∃ a, π (c a) = y) (hker : Nat.card π.ker ≤ 2) :
    Nat.card A ≤ 2 * Nat.card c.ker := by
  classical
  have h1 := Subgroup.card_ker_mul_card_range c
  let π' : c.range →* B := π.comp c.range.subtype
  have hinj : Function.Injective π' := by
    rw [injective_iff_map_eq_one]
    intro h hh
    by_contra hne
    obtain ⟨a, ha⟩ := hy
    have he : c a ∈ c.range := ⟨a, rfl⟩
    have hkx : x⁻¹ * c a ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, ha]
      exact inv_mul_cancel _
    have hkh : (h : A) ∈ π.ker := hh
    have hxne : x⁻¹ * c a ≠ 1 := by
      intro h1
      apply hxc
      have : c a = x := by simpa [inv_mul_eq_one] using (inv_mul_eq_one.1 h1).symm
      exact this ▸ he
    have hhne : (h : A) ≠ 1 := fun h' => hne (Subtype.ext h')
    have heq := eq_of_card_le_two hker (a := (⟨x⁻¹ * c a, hkx⟩ : π.ker)) (b := ⟨(h : A), hkh⟩)
      (fun h' => hxne (congrArg Subtype.val h')) (fun h' => hhne (congrArg Subtype.val h'))
    have heq' : x⁻¹ * c a = (h : A) := congrArg Subtype.val heq
    apply hxc
    have : x = c a * (h : A)⁻¹ := by rw [← heq']; group
    rw [this]
    exact c.range.mul_mem he (c.range.inv_mem h.2)
  have h4 : Nat.card c.range ≤ 2 := by
    have h5 : Nat.card c.range = Nat.card π'.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h5]
    refine card_range_le_two π'.range y ?_
    rintro _ ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
    exact hc a
  calc Nat.card A = Nat.card c.ker * Nat.card c.range := h1.symm
    _ ≤ Nat.card c.ker * 2 := Nat.mul_le_mul_left _ h4
    _ = 2 * Nat.card c.ker := mul_comm _ _

end Count

section CommMap

variable {G : Type} [Group G]

@[expose] def commMap (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (t : G)
    (ht : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : ↥A →* ↥A :=
  MonoidHom.mk' (fun a => ⟨t * a * t⁻¹ * a⁻¹, A.mul_mem (ht a a.2) (A.inv_mem a.2)⟩) (fun a b => by
    apply Subtype.ext
    show t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹ =
      (t * a * t⁻¹ * (a : G)⁻¹) * (t * b * t⁻¹ * (b : G)⁻¹)
    have hu : (t * (b : G) * t⁻¹ * (b : G)⁻¹) ∈ A := A.mul_mem (ht b b.2) (A.inv_mem b.2)
    have hc : (a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹) =
        (t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ := hA _ (A.inv_mem a.2) _ hu
    calc t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹
        = (t * a * t⁻¹) * ((t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (t * a * t⁻¹) * ((a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹)) := by rw [← hc]
      _ = (t * a * t⁻¹ * (a : G)⁻¹) * (t * b * t⁻¹ * (b : G)⁻¹) := by group)

theorem mem_ker_commMap (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (t : G)
    (ht : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (a : ↥A) :
    a ∈ (commMap A hA t ht).ker ↔ (a : G) * t = t * (a : G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : t * (a : G) * t⁻¹ * (a : G)⁻¹ = 1 := congrArg Subtype.val h
    have h2 : t * (a : G) * t⁻¹ = (a : G) := mul_inv_eq_one.1 h1
    calc (a : G) * t = (t * (a : G) * t⁻¹) * t := by rw [h2]
      _ = t * (a : G) := by group
  · intro h
    apply Subtype.ext
    show t * (a : G) * t⁻¹ * (a : G)⁻¹ = 1
    calc t * (a : G) * t⁻¹ * (a : G)⁻¹ = ((a : G) * t) * t⁻¹ * (a : G)⁻¹ := by rw [← h]
      _ = 1 := by group

theorem comm_mul_comm {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {t₀ q q' : G}
    (ht₀ : ∀ a ∈ A, t₀ * a * t₀⁻¹ ∈ A) (hq : q ∈ A) (hq' : q' ∈ A) :
    q * (q' * t₀) * q⁻¹ * (q' * t₀)⁻¹ = q * t₀ * q⁻¹ * t₀⁻¹ := by
  have hw : q * t₀ * q⁻¹ * t₀⁻¹ ∈ A := by
    have e : q * t₀ * q⁻¹ * t₀⁻¹ = q * (t₀ * q⁻¹ * t₀⁻¹) := by group
    rw [e]
    exact A.mul_mem hq (ht₀ _ (A.inv_mem hq))
  have h1 : q * q' = q' * q := hA _ hq _ hq'
  have h2 : q' * (q * t₀ * q⁻¹ * t₀⁻¹) = (q * t₀ * q⁻¹ * t₀⁻¹) * q' := hA _ hq' _ hw
  calc q * (q' * t₀) * q⁻¹ * (q' * t₀)⁻¹ = (q * q') * t₀ * q⁻¹ * t₀⁻¹ * q'⁻¹ := by group
    _ = (q' * q) * t₀ * q⁻¹ * t₀⁻¹ * q'⁻¹ := by rw [h1]
    _ = q' * (q * t₀ * q⁻¹ * t₀⁻¹) * q'⁻¹ := by group
    _ = ((q * t₀ * q⁻¹ * t₀⁻¹) * q') * q'⁻¹ := by rw [h2]
    _ = q * t₀ * q⁻¹ * t₀⁻¹ := by group

end CommMap

section Central

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_centralizer {K E Qq : Subgroup G}
    (hKE : ∀ k ∈ K, ∀ e ∈ E, k * e * k⁻¹ ∈ E) (hQK : Qq ≤ K) (hQ2 : IsPGroup 2 Qq)
    (hQE : Qq ≤ Subgroup.centralizer (E : Set G))
    (hCQ : ∀ c ∈ Subgroup.centralizer (E : Set G), ∀ q ∈ Qq, c * q * c⁻¹ ∈ Qq) :
    Qq ≤ CFSG.Open.pCoreOf 2 K := by
  classical
  have hQP : Qq ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (E : Set G)) :=
    le_pCoreOf_of_normalized hQE hCQ hQ2
  have hCEN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hP2 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (E : Set G)) ≤
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer (E : Set G)) := by
    refine le_pCoreOf_of_normalized ((pCoreOf_le_self _).trans hCEN) (fun n hn y hy => ?_)
      (isPGroup_pCoreOf' _)
    exact pCoreOf_normalized_of_normal (fun n hn k hk => centralizer_normalized hn hk) hn hy
  have hKN : K ≤ Subgroup.normalizer (E : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hKE k hk e he, fun he => ?_⟩
    have := hKE k⁻¹ (K.inv_mem hk) _ he
    simpa [mul_assoc] using this
  have hfin : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (E : Set G)) ⊓ K ≤
      CFSG.Open.pCoreOf 2 K := by
    refine le_pCoreOf_of_normalized inf_le_right (fun k hk y hy => ?_)
      (isPGroup_of_le (isPGroup_pCoreOf' _) inf_le_left)
    exact ⟨pCoreOf_normalized _ (hKN hk) hy.1, K.mul_mem (K.mul_mem hk hy.2) (K.inv_mem hk)⟩
  intro q hq
  exact hfin ⟨hP2 (hQP hq), hQK hq⟩

end Central

section Bar

variable {n : ℕ}

theorem barLen_zero : barLen (0 : permBar n) = 0 := by
  have : (0 : permBar n) = (((0 : Fin n → ZMod 2)) : permBar n) := rfl
  rw [this, barLen_mk]
  simp [vecWt]

theorem zmod_two_sub_eq_add : ∀ a b : ZMod 2, a - b = a + b := by decide

theorem barAct_swap_sub {i j : Fin n} (v : permBar n) :
    barAct (swap i j) v - v = 0 ∨ barAct (swap i j) v - v = barInd ({i, j} : Finset (Fin n)) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [barAct_mk, ← QuotientAddGroup.mk_sub]
  by_cases hij : i = j
  · subst hij
    left
    have : vecPerm (swap i i) a - a = 0 := by
      funext k
      simp [vecPerm_apply]
    rw [this]
    rfl
  have key : vecPerm (swap i j) a - a =
      fun k => (a i + a j) * indVec ({i, j} : Finset (Fin n)) k := by
    funext k
    simp only [Pi.sub_apply, vecPerm_apply, Equiv.swap_inv]
    by_cases hki : k = i
    · subst hki
      simp only [swap_apply_left, indVec, Finset.mem_insert, Finset.mem_singleton, true_or, if_true,
        mul_one]
      rw [zmod_two_sub_eq_add, add_comm]
    by_cases hkj : k = j
    · subst hkj
      simp only [swap_apply_right, indVec, Finset.mem_insert, Finset.mem_singleton, or_true,
        if_true, mul_one]
      rw [zmod_two_sub_eq_add]
    · rw [swap_apply_of_ne_of_ne hki hkj]
      simp [indVec, hki, hkj]
  rcases zmod_two_cases' (a i + a j) with h | h
  · left
    rw [key, h]
    have : (fun k => (0 : ZMod 2) * indVec ({i, j} : Finset (Fin n)) k) = 0 := by
      funext k; simp
    rw [this]
    rfl
  · right
    rw [key, h]
    unfold barInd
    congr 1
    funext k
    simp

end Bar

section CommQ

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10}

@[expose] noncomputable def commQ (C : Cfg G M X 10) (hR : Nat.card ↥(Rc X) ≤ 2) {t : G}
    (htM : t ∈ M) : ↥(CFSG.Open.pCoreOf 2 M) →* ↥(CFSG.Open.pCoreOf 2 M) :=
  H2.commMap (CFSG.Open.pCoreOf 2 M) (C.Q_comm hR) t (fun a ha => pCoreOf_normalized M htM ha)

theorem mem_ker_commQ (C : Cfg G M X 10) (hR : Nat.card ↥(Rc X) ≤ 2) {t : G} (htM : t ∈ M)
    (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    q ∈ (H2.commQ C hR htM).ker ↔ (q : G) * t = t * (q : G) :=
  H2.mem_ker_commMap _ _ _ _ _

theorem card_ker_commQ (C : Cfg G M X 10) (hR : Nat.card ↥(Rc X) ≤ 2) {t : G} (htM : t ∈ M) :
    Nat.card (H2.commQ C hR htM).ker =
      Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun q => ⟨((q : ↥(CFSG.Open.pCoreOf 2 M)) : G), q.1.2,
        Subgroup.mem_centralizer_singleton_iff.2 ((H2.mem_ker_commQ C hR htM q.1).1 q.2)⟩
      invFun := fun r => ⟨⟨(r : G), r.2.1⟩,
        (H2.mem_ker_commQ C hR htM _).2 (Subgroup.mem_centralizer_singleton_iff.1 r.2.2)⟩
      left_inv := fun q => rfl
      right_inv := fun r => rfl }

end CommQ

section Counting

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10} (D : C.PiData)

theorem card_ker_piQ : Nat.card D.piQ.ker = Nat.card ↥(Rc X) := by
  have hRQ : Rc X ≤ CFSG.Open.pCoreOf 2 M := by
    rw [C.S.R_eq_inf]
    exact inf_le_left
  refine Nat.card_congr
    { toFun := fun q => ⟨((q : ↥(CFSG.Open.pCoreOf 2 M)) : G), (D.piQ_eq_one_iff _).1 q.2⟩
      invFun := fun r => ⟨⟨(r : G), hRQ r.2⟩, (D.piQ_eq_one_iff _).2 r.2⟩
      left_inv := fun q => rfl
      right_inv := fun r => rfl }

include D in
theorem card_qB_ge (hR : Nat.card ↥(Rc X) ≤ 2) :
    2 ^ 8 * Nat.card ↥(Rc X) ≤ Nat.card ↥C.qB := by
  have hQ := C.Q_comm hR
  have h := D.card_qB hR hQ
  have hU : 2 ^ 8 ≤ Nat.card ↥((C.qB.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ) := by
    have h1 : Nat.card (altHeart 10) = 2 ^ 8 :=
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_altHeart_even (by norm_num) (by decide)
    rw [← h1]
    refine Nat.card_le_card_of_injective
      (fun u : altHeart 10 => (⟨Multiplicative.ofAdd (heartToBar u), D.heart_mem_piQ_qB hQ u⟩ :
        ↥((C.qB.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ))) ?_
    intro u v huv
    have := congrArg (fun p : ↥((C.qB.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ) =>
      Multiplicative.toAdd (p : Multiplicative (permBar 10))) huv
    exact heartToBar_injective this
  rw [h, mul_comm]
  exact Nat.mul_le_mul_left _ hU

include D in
theorem card_Q_ge (hR : Nat.card ↥(Rc X) ≤ 2) :
    2 ^ 8 * Nat.card ↥(Rc X) ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 M) :=
  (H2.card_qB_ge D hR).trans (Subgroup.card_le_of_le C.qB_le_Q)

theorem ncard_len_two_fixed_le {i j : Fin 10} (hij : i ≠ j) :
    Set.ncard {q : ↥(CFSG.Open.pCoreOf 2 M) | barLen (Multiplicative.toAdd (D.piQ q)) = 2 ∧
      barAct (swap i j) (Multiplicative.toAdd (D.piQ q)) = Multiplicative.toAdd (D.piQ q)} ≤
      29 * Nat.card ↥(Rc X) := by
  classical
  let S : Set (Multiplicative (permBar 10)) :=
    {v | barLen (Multiplicative.toAdd v) = 2 ∧
      barAct (swap i j) (Multiplicative.toAdd v) = Multiplicative.toAdd v}
  have hS : Nat.card ↥S = 29 := by
    rw [← card_len_two_fixed_swap i j hij]
    exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun v => Iff.rfl))
  have h := H2.card_subtype_le_mul D.piQ S (Nat.card ↥(Rc X)) (H2.card_ker_piQ D).le
  rw [hS] at h
  rw [← Nat.card_coe_set_eq]
  exact h

theorem card_le_of_conj {i j : Fin 10} (hij : i ≠ j) {D' : Subgroup G}
    (hD'Q : D' ≤ CFSG.Open.pCoreOf 2 M) {g : G}
    (hgQ : ∀ z ∈ D', g * z * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hfix : ∀ z : ↥(CFSG.Open.pCoreOf 2 M), (z : G) ∈ D' →
      barAct (swap i j) (Multiplicative.toAdd (D.piQ z)) = Multiplicative.toAdd (D.piQ z))
    (hfix' : ∀ z z' : ↥(CFSG.Open.pCoreOf 2 M), (z : G) ∈ D' → (z' : G) = g * z * g⁻¹ →
      barAct (swap i j) (Multiplicative.toAdd (D.piQ z')) = Multiplicative.toAdd (D.piQ z'))
    (hlen : ∀ z z' : ↥(CFSG.Open.pCoreOf 2 M), (z : G) ∈ D' → (z : G) ≠ 1 →
      (z' : G) = g * z * g⁻¹ →
      barLen (Multiplicative.toAdd (D.piQ z)) = 2 ∨ barLen (Multiplicative.toAdd (D.piQ z')) = 2) :
    Nat.card ↥D' ≤ 1 + 2 * (29 * Nat.card ↥(Rc X)) := by
  classical
  set Qs : Subgroup G := CFSG.Open.pCoreOf 2 M with hQs
  let E : Set ↥Qs := {z | (z : G) ∈ D'}
  have hE : Nat.card ↥D' = E.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      ⟨fun z => ⟨⟨z, hD'Q z.2⟩, z.2⟩, fun z => ⟨z.1, z.2⟩, fun _ => rfl, fun _ => rfl⟩
  let φ : ↥Qs → ↥Qs := fun z => if h : g * (z : G) * g⁻¹ ∈ Qs then ⟨g * z * g⁻¹, h⟩ else 1
  have hφ : ∀ z ∈ E, ((φ z : ↥Qs) : G) = g * z * g⁻¹ := by
    intro z hz
    simp only [φ, dif_pos (hgQ z hz)]
  let F : Set ↥Qs := {q | barLen (Multiplicative.toAdd (D.piQ q)) = 2 ∧
    barAct (swap i j) (Multiplicative.toAdd (D.piQ q)) = Multiplicative.toAdd (D.piQ q)}
  have hF : F.ncard ≤ 29 * Nat.card ↥(Rc X) := H2.ncard_len_two_fixed_le D hij
  set A : Set ↥Qs := {z | z ∈ E ∧ barLen (Multiplicative.toAdd (D.piQ z)) = 2} with hA
  set B : Set ↥Qs := {z | z ∈ E ∧ barLen (Multiplicative.toAdd (D.piQ (φ z))) = 2} with hB
  have hsub : E ⊆ {1} ∪ (A ∪ B) := by
    intro z hz
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    · right
      have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
      rcases hlen z (φ z) hz hz1' (hφ z hz) with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hAF : A.ncard ≤ F.ncard :=
    Set.ncard_le_ncard (fun z hz => ⟨hz.2, hfix z hz.1⟩) (Set.toFinite _)
  have hBF : B.ncard ≤ F.ncard := by
    refine Set.ncard_le_ncard_of_injOn φ (fun z hz => ⟨hz.2, hfix' z (φ z) hz.1 (hφ z hz.1)⟩)
      ?_ (Set.toFinite _)
    intro z hz w hw hzw
    have h1 := hφ z hz.1
    have h2 := hφ w hw.1
    rw [hzw] at h1
    have h3 : g * (z : G) * g⁻¹ = g * (w : G) * g⁻¹ := h1.symm.trans h2
    exact Subtype.ext (by simpa using h3)
  have h1 : E.ncard ≤ ({1} ∪ (A ∪ B)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1} ∪ (A ∪ B)).ncard ≤ ({1} : Set ↥Qs).ncard + (A ∪ B).ncard := Set.ncard_union_le _ _
  have h3 : (A ∪ B).ncard ≤ A.ncard + B.ncard := Set.ncard_union_le _ _
  rw [Set.ncard_singleton] at h2
  omega

@[expose] def ConjLen : Prop :=
  ∀ z z' : ↥(CFSG.Open.pCoreOf 2 M), (z : G) ≠ 1 → ∀ g : G, (z' : G) = g * z * g⁻¹ → g ∉ M →
    barLen (Multiplicative.toAdd (D.piQ z)) = 2 ∨ barLen (Multiplicative.toAdd (D.piQ z')) = 2

theorem conjLen_of (hR : Nat.card ↥(Rc X) ≤ 2)
    (hlen4 : ∀ x : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ x)) = 4 →
      ∀ g : G, g * (x : G) * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M → g ∈ M) : H2.ConjLen D := by
  intro z z' hz1 g hg hgM
  by_contra hcon
  push Not at hcon
  obtain ⟨h2z, h2z'⟩ := hcon
  have hz'1 : (z' : G) ≠ 1 := by
    intro h
    apply hz1
    have : g * (z : G) * g⁻¹ = 1 := by rw [← hg]; exact h
    have := congrArg (fun t => g⁻¹ * t * g) this
    simpa [mul_assoc] using this
  by_cases h4 : barLen (Multiplicative.toAdd (D.piQ z)) = 4
  · exact hgM (hlen4 z h4 g (hg ▸ z'.2))
  by_cases h4' : barLen (Multiplicative.toAdd (D.piQ z')) = 4
  · have hz : g⁻¹ * (z' : G) * g⁻¹⁻¹ = (z : G) := by rw [hg]; group
    have := hlen4 z' h4' g⁻¹ (by rw [hz]; exact z.2)
    exact hgM (by simpa using M.inv_mem this)
  · exact hgM (D.mem_of_conj_of_len hR hz1 hz'1 ⟨h2z, h4⟩ ⟨h2z', h4'⟩ hg)

end Counting

section Normalizer

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10}

theorem mem_Q_of_theta_eq_one (C : Cfg G M X 10) (hR : Nat.card ↥(Rc X) ≤ 2) {s : G}
    (hsM : s ∈ M) (h : C.θ ⟨s, hsM⟩ = 1) : s ∈ CFSG.Open.pCoreOf 2 M := by
  have : s ∈ C.K := C.mem_K.2 ⟨hsM, h⟩
  rwa [C.K_eq_Q hR] at this

variable (D : C.PiData)

section Basic

variable (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)

include D hR hx in
theorem Q_le_CGOf : CFSG.Open.pCoreOf 2 M ≤ CGOf x := fun q hq =>
  mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 (C.Q_comm hR q hq x hx))

end Basic

section Len2

variable (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 10}
  (hij : i ≠ j) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd ({i, j} : Finset (Fin 10)))

include hij hπ in
theorem x_ne_one : x ≠ 1 := by
  intro h
  have h1 : D.piQ ⟨x, hx⟩ = 1 := by
    have : (⟨x, hx⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 := Subtype.ext h
    rw [this, map_one]
  have h2 : barInd ({i, j} : Finset (Fin 10)) = 0 := by
    rw [← hπ, h1]
    rfl
  have h3 : barLen (barInd ({i, j} : Finset (Fin 10))) = 2 := by
    rw [barLen_barInd, Finset.card_pair hij]
    norm_num
  rw [h2, H2.barLen_zero] at h3
  omega

include hij hπ in
theorem theta_TOf_cases {s : G} (hs : s ∈ TOf M x) (hsM : s ∈ M) :
    C.θ ⟨s, hsM⟩ = 1 ∨ C.θ ⟨s, hsM⟩ = swap i j := by
  have hI : 2 * ({i, j} : Finset (Fin 10)).card < 10 := by
    rw [Finset.card_pair hij]
    norm_num
  have hmem : C.θ ⟨s, hsM⟩ ∈ C.thetaN x := C.mem_thetaN.2 ⟨⟨s, hsM⟩, hs, rfl⟩
  have hstab := D.thetaN_le_setStab hx hI hπ hmem
  have hfix := D.thetaN_fix_compl hx hI hπ _ hmem
  exact eq_one_or_swap hij hstab (fun y hyi hyj => hfix y (by simp [hyi, hyj]))

include hR hij hπ in
theorem theta_eq_swap {t : G} (ht : t ∈ TOf M x) (htM : t ∈ M)
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) : C.θ ⟨t, htM⟩ = swap i j :=
  (H2.theta_TOf_cases D hx hij hπ ht htM).resolve_left fun h =>
    htQ (H2.mem_Q_of_theta_eq_one C hR htM h)

include hR hij hπ in
theorem mem_Q_or_mul_inv_mem_Q {t s : G} (ht : t ∈ TOf M x) (htQ : t ∉ CFSG.Open.pCoreOf 2 M)
    (hs : s ∈ TOf M x) : s ∈ CFSG.Open.pCoreOf 2 M ∨ s * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  have htM := TOf_le_M M x ht
  have hsM := TOf_le_M M x hs
  have hθt := H2.theta_eq_swap D hR hx hij hπ ht htM htQ
  rcases H2.theta_TOf_cases D hx hij hπ hs hsM with h | h
  · exact Or.inl (H2.mem_Q_of_theta_eq_one C hR hsM h)
  · right
    have hM' : s * t⁻¹ ∈ M := M.mul_mem hsM (M.inv_mem htM)
    refine H2.mem_Q_of_theta_eq_one C hR hM' ?_
    have : (⟨s * t⁻¹, hM'⟩ : ↥M) = ⟨s, hsM⟩ * ⟨t, htM⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, h, hθt, mul_inv_cancel]

include hR hij hπ in
theorem piQ_commQ_cases {t : G} (htM : t ∈ M) (hθ : C.θ ⟨t, htM⟩ = swap i j)
    (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    D.piQ (H2.commQ C hR htM q) = 1 ∨ D.piQ (H2.commQ C hR htM q) = D.piQ ⟨x, hx⟩ := by
  have h1 : H2.commQ C hR htM q =
      (⟨t * q * t⁻¹, pCoreOf_normalized M htM q.2⟩ : ↥(CFSG.Open.pCoreOf 2 M)) * q⁻¹ := rfl
  have hq' := D.piQ_conj ⟨t, htM⟩ q ⟨t * q * t⁻¹, pCoreOf_normalized M htM q.2⟩ rfl
  rw [hθ] at hq'
  rw [h1, map_mul, map_inv]
  rcases H2.barAct_swap_sub (i := i) (j := j) (Multiplicative.toAdd (D.piQ q)) with h | h
  · left
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, hq', ← sub_eq_add_neg, h]
    rfl
  · right
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, hq', ← sub_eq_add_neg, h, hπ]

include hR hij hπ in
theorem normalizer_TOf_le_M (hS : H2.ConjLen D) {t : G} (ht : t ∈ TOf M x)
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) :
    Subgroup.normalizer ((TOf M x : Subgroup G) : Set G) ≤ M := by
  classical
  intro g hg
  by_contra hgM
  have hQab := C.Q_comm hR
  have htM : t ∈ M := TOf_le_M M x ht
  have hθt := H2.theta_eq_swap D hR hx hij hπ ht htM htQ
  have hQT : CFSG.Open.pCoreOf 2 M ≤ TOf M x := Q_le_TOf hQab hx
  set Z : Subgroup G := TOf M x ⊓ Subgroup.centralizer ((TOf M x : Subgroup G) : Set G) with hZ
  have hZQ : Z ≤ CFSG.Open.pCoreOf 2 M := by
    intro z hz
    have hzM : z ∈ M := TOf_le_M M x hz.1
    have hK : z ∈ C.K := C.mem_K_of_comm_W hzM (fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hz.2 w (hQT (C.S.W_le_Q hw))).symm)
    rwa [C.K_eq_Q hR] at hK
  have hconjZ : ∀ h ∈ Z, g * h * g⁻¹ ∈ Z := by
    intro h hh
    have hmemT : g * h * g⁻¹ ∈ TOf M x := (Subgroup.mem_normalizer_iff.1 hg h).1 hh.1
    refine ⟨hmemT, Subgroup.mem_centralizer_iff.2 fun τ hτ => ?_⟩
    have hτ' : g⁻¹ * τ * g ∈ TOf M x := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hg) τ).1 hτ
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hh.2 _ hτ'
    calc τ * (g * h * g⁻¹) = g * ((g⁻¹ * τ * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * τ * g)) * g⁻¹ := by rw [h1]
      _ = (g * h * g⁻¹) * τ := by group
  have hCt : CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G) ≤ Z := by
    intro q hq
    have hqt : q * t = t * q := Subgroup.mem_centralizer_singleton_iff.1 hq.2
    refine ⟨hQT hq.1, Subgroup.mem_centralizer_iff.2 fun τ hτ => ?_⟩
    rcases H2.mem_Q_or_mul_inv_mem_Q D hR hx hij hπ ht htQ hτ with h | h
    · exact hQab _ h q hq.1
    · have h1 : (τ * t⁻¹) * q = q * (τ * t⁻¹) := hQab _ h q hq.1
      calc τ * q = (τ * t⁻¹) * (t * q) := by group
        _ = (τ * t⁻¹) * (q * t) := by rw [hqt]
        _ = ((τ * t⁻¹) * q) * t := by group
        _ = (q * (τ * t⁻¹)) * t := by rw [h1]
        _ = q * τ := by group
  have hfixQ : ∀ z : ↥(CFSG.Open.pCoreOf 2 M), (z : G) * t = t * (z : G) →
      barAct (swap i j) (Multiplicative.toAdd (D.piQ z)) = Multiplicative.toAdd (D.piQ z) := by
    intro z hzt
    have h := D.piQ_conj ⟨t, htM⟩ z z (by
      show (z : G) = t * (z : G) * t⁻¹
      rw [← hzt]
      group)
    rw [hθt] at h
    exact h.symm
  have hcard := H2.card_le_of_conj D hij (D' := CFSG.Open.pCoreOf 2 M ⊓
      Subgroup.centralizer ({t} : Set G)) inf_le_left (g := g)
    (fun z hz => hZQ (hconjZ z (hCt hz)))
    (fun z hz => hfixQ z (Subgroup.mem_centralizer_singleton_iff.1 hz.2))
    (fun z z' hz hz' => hfixQ z' (by
      have hz'Z : (z' : G) ∈ Z := hz' ▸ hconjZ _ (hCt hz)
      exact (Subgroup.mem_centralizer_iff.1 hz'Z.2 t ht).symm))
    (fun z z' _ hz1 hz' => hS z z' hz1 g hz' hgM)
  have hlow := H2.card_le_ker_mul D.piQ (H2.commQ C hR htM) (D.piQ ⟨x, hx⟩)
    (H2.piQ_commQ_cases D hR hx hij hπ htM hθt)
  rw [H2.card_ker_piQ D, H2.card_ker_commQ C hR htM] at hlow
  have hQge := H2.card_Q_ge D hR
  have hRpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
  interval_cases hrr : Nat.card ↥(Rc X) <;> omega

end Len2

end Normalizer

section Cent

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10} (D : C.PiData)

section Basic2

variable (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)

include D hR hx in
theorem Q_le_normalizer_P : CFSG.Open.pCoreOf 2 M ≤
    Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (CGOf x) : Subgroup G) : Set G) := by
  intro q hq
  have hqK : q ∈ CGOf x := H2.Q_le_CGOf D hR hx hq
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => pCoreOf_normalized _ hqK hp, fun hp => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hqK) hp
  simpa [mul_assoc] using this

include D hR hx in
theorem isPGroup_sup :
    IsPGroup 2 (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) :=
  (isPGroup_pCoreOf' (CGOf x)).to_sup_of_normal_left' (isPGroup_pCoreOf' M)
    (H2.Q_le_normalizer_P D hR hx)

include D hR hx in
theorem sup_inf_le_TOf :
    (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M ≤ TOf M x := by
  have hT2 := H2.isPGroup_sup D hR hx
  have hTK : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M ≤ CGOf x :=
    sup_le (pCoreOf_le_self _) (H2.Q_le_CGOf D hR hx)
  refine le_pCoreOf_of_normalized (fun t ht => ⟨ht.2, hTK ht.1⟩) (fun k hk z hz => ?_)
    (isPGroup_of_le hT2 inf_le_left)
  exact Subgroup.mem_inf.2 ⟨sup_norm hk hz.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.1
    hz.2) (M.inv_mem hk.1)⟩

end Basic2

section Len2

variable (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 10}
  (hij : i ≠ j) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd ({i, j} : Finset (Fin 10)))

include hR hij hπ in
theorem not_P_le_Q (hKM : ¬ CGOf x ≤ M) :
    ¬ CFSG.Open.pCoreOf 2 (CGOf x) ≤ CFSG.Open.pCoreOf 2 M := by
  intro hPQ
  apply hKM
  have hQab := C.Q_comm hR
  have hQK : CFSG.Open.pCoreOf 2 M ≤ CGOf x := H2.Q_le_CGOf D hR hx
  have hx1 := H2.x_ne_one D hx hij hπ
  have hB : Subgroup.zpowers x ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers x) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hx)
  have hcons := centralizer_two_constrained C.S.charTwo hB hB2
  have hQP : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
    intro q hq
    apply hcons
    refine Subgroup.mem_inf.2 ⟨hQK hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact hQab p (hPQ hp) q hq
  have hPeq : CFSG.Open.pCoreOf 2 (CGOf x) = CFSG.Open.pCoreOf 2 M := le_antisymm hPQ hQP
  intro k hk
  rw [← C.S.normalizer_Q_eq, Subgroup.mem_normalizer_iff]
  intro q
  rw [← hPeq]
  refine ⟨fun hq => pCoreOf_normalized _ hk hq, fun hq => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hk) hq
  simpa [mul_assoc] using this

include hR hij hπ in
theorem sup_eq_TOf (hS : H2.ConjLen D) (hKM : ¬ CGOf x ≤ M) {t : G} (ht : t ∈ TOf M x)
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) :
    CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x := by
  classical
  have hH2 := H2.isPGroup_sup D hR hx
  have hUT := H2.sup_inf_le_TOf D hR hx
  have hPQ := H2.not_P_le_Q D hR hx hij hπ hKM
  have hQH : CFSG.Open.pCoreOf 2 M ≠ CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M :=
    fun h' => hPQ (by rw [h']; exact le_sup_left)
  obtain ⟨u, huH, huQ, huN⟩ := exists_mem_normalizer_of_lt hH2 le_sup_right hQH
  have huM : u ∈ M := by rw [← C.S.normalizer_Q_eq]; exact huN
  have huU : u ∈ (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M := ⟨huH, huM⟩
  have huT : u ∈ TOf M x := hUT huU
  have hTU : TOf M x ≤ (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M := by
    intro s hs
    rcases H2.mem_Q_or_mul_inv_mem_Q D hR hx hij hπ huT huQ hs with h | h
    · exact ⟨Subgroup.mem_sup_right h, pCoreOf_le_self M h⟩
    · have e : s = (s * u⁻¹) * u := by group
      rw [e]
      exact Subgroup.mul_mem _ ⟨Subgroup.mem_sup_right h, pCoreOf_le_self M h⟩ huU
  have hTH : TOf M x ≤ CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M :=
    hTU.trans inf_le_left
  by_contra hne'
  obtain ⟨h, hhH, hhT, hhN⟩ := exists_mem_normalizer_of_lt hH2 hTH (Ne.symm hne')
  have hhM : h ∈ M := H2.normalizer_TOf_le_M D hR hx hij hπ hS ht htQ hhN
  exact hhT (hUT ⟨hhH, hhM⟩)

include hR hij hπ in
theorem not_Q_le_P (hS : H2.ConjLen D) (hKM : ¬ CGOf x ≤ M) {t : G} (ht : t ∈ TOf M x)
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) :
    ¬ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
  intro hQP
  have hsup := H2.sup_eq_TOf D hR hx hij hπ hS hKM ht htQ
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) = TOf M x := (sup_eq_left.2 hQP).symm.trans hsup
  apply hKM
  intro k hk
  apply H2.normalizer_TOf_le_M D hR hx hij hπ hS ht htQ
  rw [Subgroup.mem_normalizer_iff]
  intro s
  rw [← hPT]
  refine ⟨fun hs => pCoreOf_normalized _ hk hs, fun hs => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hk) hs
  simpa [mul_assoc] using this

include hij hπ in
theorem cons_P {k : G} (hk : k ∈ CGOf x)
    (hkc : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * k = k * p) :
    k ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
  have hx1 := H2.x_ne_one D hx hij hπ
  have hB : Subgroup.zpowers x ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers x) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hx)
  exact centralizer_two_constrained C.S.charTwo hB hB2
    (Subgroup.mem_inf.2 ⟨hk, Subgroup.mem_centralizer_iff.2 hkc⟩)

include hij hπ in
theorem stab_mem_P {a : G} (haK : a ∈ CGOf x)
    (ha : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), a * p * a⁻¹ * p⁻¹ ∈ Subgroup.zpowers x) :
    a ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
  H2.stabSub_le_pCoreOf (fun k hk => mem_centralizer_zpowers_iff.1 hk)
    (exists_two_pow_of_mem_pCoreOf M hx) (fun k hk hkc => H2.cons_P D hx hij hπ hk hkc) ⟨haK, ha⟩

include hR hij hπ in
theorem exists_ne_one_mem_Rc (hS : H2.ConjLen D) (hKM : ¬ CGOf x ≤ M) {t : G} (ht : t ∈ TOf M x)
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) : ∃ r ∈ Rc X, r ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hQab := C.Q_comm hR
  have htM : t ∈ M := TOf_le_M M x ht
  have hθt := H2.theta_eq_swap D hR hx hij hπ ht htM htQ
  have hc : ∀ q ∈ CFSG.Open.pCoreOf 2 M, t * q * t⁻¹ * q⁻¹ ∈ Subgroup.zpowers x := by
    intro q hq
    rcases H2.piQ_commQ_cases D hR hx hij hπ htM hθt ⟨q, hq⟩ with h | h
    · have h2 : t * q * t⁻¹ * q⁻¹ = 1 := hcon _ ((D.piQ_eq_one_iff _).1 h)
      rw [h2]
      exact Subgroup.one_mem _
    · have h1 : D.piQ (H2.commQ C hR htM ⟨q, hq⟩ * (⟨x, hx⟩ : ↥(CFSG.Open.pCoreOf 2 M))⁻¹) = 1 := by
        rw [map_mul, map_inv, h, mul_inv_cancel]
      have h3 : t * q * t⁻¹ * q⁻¹ * x⁻¹ = 1 := hcon _ ((D.piQ_eq_one_iff _).1 h1)
      have h4 : t * q * t⁻¹ * q⁻¹ = x := mul_inv_eq_one.1 h3
      rw [h4]
      exact Subgroup.mem_zpowers x
  have hxK : ∀ k ∈ CGOf x, k * x * k⁻¹ = x := fun k hk => mem_centralizer_zpowers_iff.1 hk
  have hsup := H2.sup_eq_TOf D hR hx hij hπ hS hKM ht htQ
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := le_sup_left.trans hsup.le
  have hSP : H2.stabSub (CGOf x) (CFSG.Open.pCoreOf 2 (CGOf x)) x hxK ≤
      CFSG.Open.pCoreOf 2 (CGOf x) :=
    H2.stabSub_le_pCoreOf hxK (exists_two_pow_of_mem_pCoreOf M hx)
      (fun k hk hkc => H2.cons_P D hx hij hπ hk hkc)
  have hQnorm : ∀ a ∈ CFSG.Open.pCoreOf 2 M, t * a * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    fun a ha => pCoreOf_normalized M htM ha
  have hQS : CFSG.Open.pCoreOf 2 M ≤
      H2.stabSub (CGOf x) (CFSG.Open.pCoreOf 2 (CGOf x)) x hxK := by
    intro q hq
    refine ⟨H2.Q_le_CGOf D hR hx hq, fun p hp => ?_⟩
    rcases H2.mem_Q_or_mul_inv_mem_Q D hR hx hij hπ ht htQ (hPT hp) with h | h
    · have e : q * p * q⁻¹ * p⁻¹ = 1 := by rw [hQab q hq p h]; group
      rw [e]
      exact Subgroup.one_mem _
    · have e : p = (p * t⁻¹) * t := by group
      rw [e, H2.comm_mul_comm hQab hQnorm hq h]
      have e2 : q * t * q⁻¹ * t⁻¹ = (t * q * t⁻¹ * q⁻¹)⁻¹ := by group
      rw [e2]
      exact Subgroup.inv_mem _ (hc q hq)
  have htS : t ∈ H2.stabSub (CGOf x) (CFSG.Open.pCoreOf 2 (CGOf x)) x hxK := by
    refine ⟨(TOf_le_C M x ht).2, fun p hp => ?_⟩
    rcases H2.mem_Q_or_mul_inv_mem_Q D hR hx hij hπ ht htQ (hPT hp) with h | h
    · exact hc p h
    · have e2 : t * p * t⁻¹ * p⁻¹ = t * (p * t⁻¹) * t⁻¹ * (p * t⁻¹)⁻¹ := by group
      rw [e2]
      exact hc _ h
  have hTS : TOf M x ≤ H2.stabSub (CGOf x) (CFSG.Open.pCoreOf 2 (CGOf x)) x hxK := by
    intro s hs
    rcases H2.mem_Q_or_mul_inv_mem_Q D hR hx hij hπ ht htQ hs with h | h
    · exact hQS h
    · have e : s = (s * t⁻¹) * t := by group
      rw [e]
      exact Subgroup.mul_mem _ (hQS h) htS
  have hQP : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (CGOf x) := fun q hq =>
    hSP (hTS (Q_le_TOf hQab hx hq))
  exact H2.not_Q_le_P D hR hx hij hπ hS hKM ht htQ hQP

end Len2

section Len2

variable (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 10}
  (hij : i ≠ j) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd ({i, j} : Finset (Fin 10)))

include hR hij hπ in
theorem exists_central_not_Q (hS : H2.ConjLen D) (hKM : ¬ CGOf x ≤ M) {t : G} (ht : t ∈ TOf M x)
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) :
    ∃ t' ∈ CFSG.Open.pCoreOf 2 (CGOf x), t' ∉ CFSG.Open.pCoreOf 2 M ∧
      ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * t' = t' * p := by
  by_contra hcon
  push Not at hcon
  have hQab := C.Q_comm hR
  obtain ⟨r, hrR, hr1⟩ := H2.exists_ne_one_mem_Rc D hR hx hij hπ hS hKM ht htQ
  have hsup := H2.sup_eq_TOf D hR hx hij hπ hS hKM ht htQ
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := le_sup_left.trans hsup.le
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT.trans (TOf_le_M M x)
  set P : Subgroup G := CFSG.Open.pCoreOf 2 (CGOf x) with hP
  set E : Subgroup G := P ⊓ Subgroup.centralizer (P : Set G) with hE
  have hEQ : E ≤ CFSG.Open.pCoreOf 2 M := by
    intro e he
    by_contra heQ
    obtain ⟨p, hp, hne⟩ := hcon e he.1 heQ
    exact hne (Subgroup.mem_centralizer_iff.1 he.2 p hp)
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    have := hrR
    rw [C.S.R_eq_inf] at this
    exact (Subgroup.mem_inf.1 this).1
  have hrK : r ∈ CGOf x :=
    mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 (hQab r hrQ x hx))
  have hrc : ∀ p ∈ P, p * r = r * p := fun p hp =>
    mul_inv_eq_iff_eq_mul.1 (C.S.R_central hR (hPM hp) hrR)
  have hrP : r ∈ P := H2.cons_P D hx hij hπ hrK hrc
  have hrE : r ∈ E := ⟨hrP, Subgroup.mem_centralizer_iff.2 hrc⟩
  have hCE : ∀ c ∈ Subgroup.centralizer (E : Set G), c ∈ M := fun c hc =>
    C.S.centralizer_le_of_mem_R hrR hr1
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hrE) hc)
  have hKE : ∀ k ∈ CGOf x, ∀ e ∈ E, k * e * k⁻¹ ∈ E := by
    intro k hk e he
    refine ⟨pCoreOf_normalized _ hk he.1, Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩
    have hp' : k⁻¹ * p * k ∈ P := by
      simpa using pCoreOf_normalized _ ((CGOf x).inv_mem hk) hp
    have h1 := Subgroup.mem_centralizer_iff.1 he.2 _ hp'
    calc p * (k * e * k⁻¹) = k * ((k⁻¹ * p * k) * e) * k⁻¹ := by group
      _ = k * (e * (k⁻¹ * p * k)) * k⁻¹ := by rw [h1]
      _ = (k * e * k⁻¹) * p := by group
  have hQP : CFSG.Open.pCoreOf 2 M ≤ P :=
    H2.le_pCoreOf_of_centralizer hKE (H2.Q_le_CGOf D hR hx) (isPGroup_pCoreOf' M)
      (fun q hq => Subgroup.mem_centralizer_iff.2 fun e he => hQab e (hEQ he) q hq)
      (fun c hc q hq => pCoreOf_normalized M (hCE c hc) hq)
  exact H2.not_Q_le_P D hR hx hij hπ hS hKM ht htQ hQP

include hR hij hπ in
theorem exists_piQ_commQ_eq {t : G} (htM : t ∈ M) (hθ : C.θ ⟨t, htM⟩ = swap i j) :
    ∃ q : ↥(CFSG.Open.pCoreOf 2 M), D.piQ (H2.commQ C hR htM q) = D.piQ ⟨x, hx⟩ := by
  classical
  have hQab := C.Q_comm hR
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 10, k ≠ i ∧ k ≠ j := by
    have : ∀ i j : Fin 10, ∃ k : Fin 10, k ≠ i ∧ k ≠ j := by decide
    exact this i j
  have hsum : ∑ m, indVec ({i, k} : Finset (Fin 10)) m = 0 := by
    have h1 : ∀ m : Fin 10, indVec ({i, k} : Finset (Fin 10)) m =
        if m ∈ ({i, k} : Finset (Fin 10)) then 1 else 0 := fun m => rfl
    simp only [h1, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_pair hki.symm]
    decide
  obtain ⟨u, hu⟩ : (barInd ({i, k} : Finset (Fin 10)) : permBar 10) ∈
      Set.range (heartToBar (n := 10)) := mk_mem_range_heartToBar hsum
  obtain ⟨q, -, hq⟩ := Subgroup.mem_map.1 (D.heart_mem_piQ_qB hQab u)
  have hqk : Multiplicative.toAdd (D.piQ q) = barInd ({i, k} : Finset (Fin 10)) := by
    rw [hq, toAdd_ofAdd]
    exact hu
  have hq' := D.piQ_conj ⟨t, htM⟩ q ⟨t * q * t⁻¹, pCoreOf_normalized M htM q.2⟩ rfl
  have himg : barAct (swap i j) (barInd ({i, k} : Finset (Fin 10))) = barInd {j, k} := by
    rw [barAct_barInd]
    congr 1
    simp [Finset.image_insert, swap_apply_left, swap_apply_of_ne_of_ne hki hkj]
  rw [hθ, hqk, himg] at hq'
  have hne : barInd ({j, k} : Finset (Fin 10)) ≠ barInd ({i, k} : Finset (Fin 10)) := by
    unfold barInd
    refine bar_mk_ne_of_coords (i := i) (j := k) ?_ ?_
    · simp [indVec, hij, hki.symm, Ne.symm hki]
    · simp [indVec]
  refine ⟨q, ?_⟩
  rcases H2.piQ_commQ_cases D hR hx hij hπ htM hθ q with h | h
  · exfalso
    have h1 : D.piQ (⟨t * q * t⁻¹, pCoreOf_normalized M htM q.2⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
        D.piQ q := by
      have h2 : H2.commQ C hR htM q = (⟨t * q * t⁻¹, pCoreOf_normalized M htM q.2⟩ :
          ↥(CFSG.Open.pCoreOf 2 M)) * q⁻¹ := rfl
      rw [h2, map_mul, map_inv, mul_inv_eq_one] at h
      exact h
    apply hne
    have h3 := congrArg Multiplicative.toAdd h1
    rw [hq', hqk] at h3
    exact h3
  · exact h

include hR hij hπ in
theorem card_Q_le_two_mul (hS : H2.ConjLen D) (hKM : ¬ CGOf x ≤ M) {t : G} (ht : t ∈ TOf M x)
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) {t' : G} (ht'P : t' ∈ CFSG.Open.pCoreOf 2 (CGOf x))
    (ht'Q : t' ∉ CFSG.Open.pCoreOf 2 M)
    (ht'c : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * t' = t' * p) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≤
      2 * Nat.card ↥(CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M) := by
  classical
  have hQab := C.Q_comm hR
  have hsup := H2.sup_eq_TOf D hR hx hij hπ hS hKM ht htQ
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := le_sup_left.trans hsup.le
  have ht'T : t' ∈ TOf M x := hPT ht'P
  have ht'M : t' ∈ M := TOf_le_M M x ht'T
  have hθ' := H2.theta_eq_swap D hR hx hij hπ ht'T ht'M ht'Q
  have hQnorm : ∀ a ∈ CFSG.Open.pCoreOf 2 M, t' * a * t'⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    fun a ha => pCoreOf_normalized M ht'M ha
  have hCP : CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({t'} : Set G) ≤
      CFSG.Open.pCoreOf 2 (CGOf x) := by
    intro q hq
    have hqt : q * t' = t' * q := Subgroup.mem_centralizer_singleton_iff.1 hq.2
    refine H2.cons_P D hx hij hπ (H2.Q_le_CGOf D hR hx hq.1) fun p hp => ?_
    rcases H2.mem_Q_or_mul_inv_mem_Q D hR hx hij hπ ht'T ht'Q (hPT hp) with h | h
    · exact hQab p h q hq.1
    · have h1 : (p * t'⁻¹) * q = q * (p * t'⁻¹) := hQab _ h q hq.1
      calc p * q = (p * t'⁻¹) * (t' * q) := by group
        _ = (p * t'⁻¹) * (q * t') := by rw [hqt]
        _ = ((p * t'⁻¹) * q) * t' := by group
        _ = (q * (p * t'⁻¹)) * t' := by rw [h1]
        _ = q * p := by group
  have hPC : CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M ≤
      CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({t'} : Set G) := fun q hq =>
    ⟨hq.2, Subgroup.mem_centralizer_singleton_iff.2 (ht'c q hq.1)⟩
  have hEq : CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({t'} : Set G) =
      CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M :=
    le_antisymm (fun q hq => ⟨hCP hq, hq.1⟩) hPC
  have hxc : (⟨x, hx⟩ : ↥(CFSG.Open.pCoreOf 2 M)) ∉ (H2.commQ C hR ht'M).range := by
    rintro ⟨y, hy⟩
    have hyx : t' * (y : G) * t'⁻¹ * (y : G)⁻¹ = x := congrArg Subtype.val hy
    have hyK : (y : G) ∈ CGOf x := H2.Q_le_CGOf D hR hx y.2
    have hyP : (y : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
      refine H2.stab_mem_P D hx hij hπ hyK fun p hp => ?_
      rcases H2.mem_Q_or_mul_inv_mem_Q D hR hx hij hπ ht'T ht'Q (hPT hp) with h | h
      · have e : (y : G) * p * (y : G)⁻¹ * p⁻¹ = 1 := by rw [hQab y y.2 p h]; group
        rw [e]
        exact Subgroup.one_mem _
      · have e : p = (p * t'⁻¹) * t' := by group
        rw [e, H2.comm_mul_comm hQab hQnorm y.2 h]
        have e2 : (y : G) * t' * (y : G)⁻¹ * t'⁻¹ = (t' * (y : G) * t'⁻¹ * (y : G)⁻¹)⁻¹ := by
          group
        rw [e2, hyx]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
    have hyC : (y : G) * t' = t' * (y : G) := by
      have : (y : G) ∈ CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({t'} : Set G) :=
        hEq.symm ▸ (⟨hyP, y.2⟩ : (y : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M)
      exact Subgroup.mem_centralizer_singleton_iff.1 this.2
    have h1 : t' * (y : G) * t'⁻¹ * (y : G)⁻¹ = 1 := by rw [← hyC]; group
    exact H2.x_ne_one D hx hij hπ (hyx.symm.trans h1)
  have hy := H2.exists_piQ_commQ_eq D hR hx hij hπ ht'M hθ'
  have key := H2.card_le_two_mul_ker D.piQ (H2.commQ C hR ht'M) (D.piQ ⟨x, hx⟩)
    (H2.piQ_commQ_cases D hR hx hij hπ ht'M hθ') ⟨x, hx⟩ rfl hxc hy
    ((H2.card_ker_piQ D).le.trans hR)
  rw [H2.card_ker_commQ C hR ht'M, hEq] at key
  exact key

include hR hij hπ in
theorem centralizer_le_M_aux (hS : H2.ConjLen D) : CGOf x ≤ M := by
  classical
  by_contra hKM
  have hQab := C.Q_comm hR
  by_cases hTQ : TOf M x ≤ CFSG.Open.pCoreOf 2 M
  · apply hKM
    have hx1 := H2.x_ne_one D hx hij hπ
    have hB : Subgroup.zpowers x ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
    have h2 := (C.centralizer_le_M hR (Subgroup.zpowers_le.2 hx) hB hTQ).2
    exact (Subgroup.centralizer_le_normalizer _).trans h2
  obtain ⟨t, ht, htQ⟩ := SetLike.not_le_iff_exists.1 hTQ
  obtain ⟨g, hgK, hgM⟩ := SetLike.not_le_iff_exists.1 hKM
  obtain ⟨t', ht'P, ht'Q, ht'c⟩ := H2.exists_central_not_Q D hR hx hij hπ hS hKM ht htQ
  have hsup := H2.sup_eq_TOf D hR hx hij hπ hS hKM ht htQ
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := le_sup_left.trans hsup.le
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT.trans (TOf_le_M M x)
  have ht'T : t' ∈ TOf M x := hPT ht'P
  have ht'M : t' ∈ M := TOf_le_M M x ht'T
  have hθ' := H2.theta_eq_swap D hR hx hij hπ ht'T ht'M ht'Q
  have hQB := H2.card_Q_le_two_mul D hR hx hij hπ hS hKM ht htQ ht'P ht'Q ht'c
  have hQge := H2.card_Q_ge D hR
  set P : Subgroup G := CFSG.Open.pCoreOf 2 (CGOf x) with hP
  set Qs : Subgroup G := CFSG.Open.pCoreOf 2 M with hQs
  set B : Subgroup G := P ⊓ Qs with hB
  have hBP : B ≤ P := inf_le_left
  have hBQ : B ≤ Qs := inf_le_right
  have hθP : Nat.card ↥((P.subgroupOf M).map C.θ) = 2 := by
    have hswapmem : swap i j ∈ (P.subgroupOf M).map C.θ :=
      Subgroup.mem_map.2 ⟨⟨t', ht'M⟩, Subgroup.mem_subgroupOf.2 ht'P, hθ'⟩
    rw [Nat.card_eq_two_iff' (1 : ↥((P.subgroupOf M).map C.θ))]
    refine ⟨⟨swap i j, hswapmem⟩, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun f : Perm (Fin 10) => f i) (congrArg Subtype.val h)
      simp at h1
      exact hij h1.symm
    · intro y hy
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 y.2
      have hmP : (m : G) ∈ P := Subgroup.mem_subgroupOf.1 hm
      rcases H2.theta_TOf_cases D hx hij hπ (hPT hmP) m.2 with h | h
      · exact absurd (Subtype.ext (hmy.symm.trans (by rw [h]; rfl))) hy
      · exact Subtype.ext (hmy.symm.trans h)
  have hPcard : Nat.card ↥P = 2 * Nat.card ↥B := by
    have h1 := C.card_eq_card_inf_mul hR hPM
    rw [h1, hθP, mul_comm]
  have hBgP : conjSubgroup g B ≤ P := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ B := mem_conjSubgroup.1 hy
    have := pCoreOf_normalized (CGOf x) hgK (hBP hy')
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at this
  have hcardg : Nat.card ↥(conjSubgroup g B) = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hidx : ∀ A : Subgroup G, A ≤ P → Nat.card ↥A = Nat.card ↥B →
      (A.subgroupOf P).index = 2 := by
    intro A hAP hAB
    have h1 := Subgroup.card_mul_index (A.subgroupOf P)
    have h2 : Nat.card ↥(A.subgroupOf P) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
    rw [h2, hAB, hPcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hBpos (h1.trans (mul_comm _ _))
  set Dd : Subgroup G := B ⊓ conjSubgroup g B with hDd
  have hDP : Dd ≤ P := inf_le_left.trans hBP
  have hDidx : (Dd.subgroupOf P).index ≤ 4 := by
    have h1 : Dd.subgroupOf P = B.subgroupOf P ⊓ (conjSubgroup g B).subgroupOf P := by
      ext y
      simp only [hDd, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [h1]
    refine Subgroup.index_inf_le.trans ?_
    rw [hidx B hBP rfl, hidx _ hBgP hcardg]
  have hDcard : Nat.card ↥Dd * (Dd.subgroupOf P).index = Nat.card ↥P := by
    have h1 := Subgroup.card_mul_index (Dd.subgroupOf P)
    have h2 : Nat.card ↥(Dd.subgroupOf P) = Nat.card ↥Dd :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv
    rwa [h2] at h1
  have hP4 : Nat.card ↥P ≤ 4 * Nat.card ↥Dd := by
    rw [← hDcard]
    exact (Nat.mul_le_mul_left _ hDidx).trans (by rw [mul_comm])
  have hBC : B ≤ Qs ⊓ Subgroup.centralizer ({t'} : Set G) := fun q hq =>
    ⟨hq.2, Subgroup.mem_centralizer_singleton_iff.2 (ht'c q hq.1)⟩
  have hfixQ : ∀ z : ↥Qs, (z : G) * t' = t' * (z : G) →
      barAct (swap i j) (Multiplicative.toAdd (D.piQ z)) = Multiplicative.toAdd (D.piQ z) := by
    intro z hzt
    have h := D.piQ_conj ⟨t', ht'M⟩ z z (by
      show (z : G) = t' * (z : G) * t'⁻¹
      rw [← hzt]
      group)
    rw [hθ'] at h
    exact h.symm
  have hDgB : ∀ z ∈ Dd, g⁻¹ * z * g ∈ B := fun z hz => mem_conjSubgroup.1 hz.2
  have hDQ : Dd ≤ Qs := inf_le_left.trans hBQ
  have hcount := H2.card_le_of_conj D hij (D' := Dd) hDQ (g := g⁻¹)
    (fun z hz => by simpa using hBQ (hDgB z hz))
    (fun z hz => hfixQ z (Subgroup.mem_centralizer_singleton_iff.1 (hBC hz.1).2))
    (fun z z' hz hz' => hfixQ z' (by
      have hz'B : (z' : G) ∈ B := by
        rw [hz']
        simpa using hDgB _ hz
      exact Subgroup.mem_centralizer_singleton_iff.1 (hBC hz'B).2))
    (fun z z' hz hz1 hz' => hS z z' hz1 g⁻¹ hz' (fun h => hgM (by simpa using M.inv_mem h)))
  have hRpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
  norm_num at hQge
  omega

end Len2

end Cent

end H2

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10}
  (D : C.PiData)

theorem centralizer_le_M_of_len_two_of (hR : Nat.card ↥(Rc X) ≤ 2)
    (hlen4 : ∀ x : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ x)) = 4 →
      ∀ g : G, g * (x : G) * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M → g ∈ M)
    (x : ↥(CFSG.Open.pCoreOf 2 M)) (hl : barLen (Multiplicative.toAdd (D.piQ x)) = 2) :
    Subgroup.centralizer ({(x : G)} : Set G) ≤ M := by
  obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ x))
  rw [hl] at hIc
  obtain ⟨i, j, hij, hIij⟩ := Finset.card_eq_two.1 hIc
  have hπ : Multiplicative.toAdd (D.piQ ⟨(x : G), x.2⟩) = barInd ({i, j} : Finset (Fin 10)) := by
    rw [← hIij]
    exact hI
  rw [centralizer_singleton_eq_zpowers]
  exact H2.centralizer_le_M_aux D hR x.2 hij hπ (H2.conjLen_of D hR hlen4)

theorem centralizer_le_M_of_len_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (x : ↥(CFSG.Open.pCoreOf 2 M)) (hl : barLen (Multiplicative.toAdd (D.piQ x)) = 2) :
    Subgroup.centralizer ({(x : G)} : Set G) ≤ M :=
  D.centralizer_le_M_of_len_two_of hR
    (fun y hy g hg => D.mem_M_of_conj_len_four hR y hy hg) x hl

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
