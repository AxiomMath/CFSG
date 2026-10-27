module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res9A10

open Equiv Subgroup

@[expose] def cFive : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def cSeven : Perm (Fin 7) :=
  swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6

theorem cFive_mem : cFive ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem cSeven_mem : cSeven ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem orderOf_cFive : orderOf cFive = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem orderOf_cSeven : orderOf cSeven = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem eq_one_of_commute_orderOf_seven {x t : Perm (Fin 10)} (hx : orderOf x = 7)
    (ht : t ∈ alternatingGroup (Fin 10)) (htx : t * x = x * t) {k : ℕ} (ht2 : t ^ (2 ^ k) = 1) :
    t = 1 := by
  classical
  have hcyc : x.IsCycle := Perm.isCycle_of_prime_order' (by rw [hx]; decide)
    (by rw [hx, Fintype.card_fin]; norm_num)
  have hsupp : x.support.card = 7 := by rw [← hcyc.orderOf, hx]
  have hct : x.cycleType = {7} := by rw [hcyc.cycleType, hsupp]
  set C := Subgroup.centralizer ({x} : Set (Perm (Fin 10))) with hC
  have hC42 : Nat.card C = 42 := by
    rw [hC, Perm.nat_card_centralizer, hct]
    simp [Fintype.card_fin, Nat.factorial]
  have hcompl : 2 < (x.supportᶜ).card := by
    rw [Finset.card_compl, hsupp, Fintype.card_fin]
    norm_num
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (x.supportᶜ).card)
  have hdisj : Perm.Disjoint (swap p q) x := by
    rw [Perm.disjoint_iff_disjoint_support, Perm.support_swap hpq]
    rw [Finset.mem_compl] at hp hq
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    exacts [hp, hq]
  have hsC : swap p q ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hdisj.commute.eq
  set f : ↥C →* ℤˣ := Perm.sign.comp C.subtype with hf
  have hfsurj : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨swap p q, hsC⟩, by simp [hf, Perm.sign_swap hpq]⟩
  have hker : Nat.card f.ker = 21 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, hC42]
      at h1
    have h2 : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [h2] at h1
    omega
  have htC : t ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact htx
  have htk : (⟨t, htC⟩ : ↥C) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact Perm.mem_alternatingGroup.mp ht
  have h21 : orderOf (⟨⟨t, htC⟩, htk⟩ : ↥f.ker) ∣ 21 := hker ▸ orderOf_dvd_natCard _
  have h2 : orderOf (⟨⟨t, htC⟩, htk⟩ : ↥f.ker) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (Subtype.ext (by simpa using ht2))
  have h1 : orderOf (⟨⟨t, htC⟩, htk⟩ : ↥f.ker) = 1 := by
    have h3 := Nat.dvd_gcd h21 h2
    have h4 : Nat.Coprime 21 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    rw [h4.gcd_eq_one] at h3
    exact Nat.dvd_one.mp h3
  have h4 := congrArg (fun z : ↥f.ker => ((z : ↥C) : Perm (Fin 10))) (orderOf_eq_one_iff.mp h1)
  simpa using h4

theorem inf_centralizer_eq_bot {V : Subgroup (Perm (Fin 10))}
    (hV : V ≤ alternatingGroup (Fin 10)) (hV2 : IsPGroup 2 V) {x : Perm (Fin 10)}
    (hx : orderOf x = 7) : V ⊓ centralizer ({x} : Set (Perm (Fin 10))) = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨htV, htc⟩ := Subgroup.mem_inf.mp ht
  obtain ⟨k, hk⟩ := hV2 ⟨t, htV⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact Subgroup.mem_bot.mpr (eq_one_of_commute_orderOf_seven hx (hV htV)
    (Subgroup.mem_centralizer_singleton_iff.mp htc) hk')

theorem card_modEq_card_inf_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {D V : Subgroup G} (hD : IsPGroup p D)
    (hDV : D ≤ normalizer (V : Set G)) :
    Nat.card V ≡ Nat.card (V ⊓ centralizer (D : Set G) : Subgroup G) [MOD p] := by
  classical
  let _ : MulDistribMulAction D V :=
    { smul := fun t k => ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hDV t.2) k).mp k.2⟩
      one_smul := fun k => Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
      mul_smul := fun s t k => Subtype.ext (by
        change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
        group)
      smul_mul := fun t k l => Subtype.ext (by
        change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
        group)
      smul_one := fun t => Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group) }
  have key := hD.card_modEq_card_fixedPoints V
  have hfix : ∀ a : MulAction.fixedPoints D V, ∀ g : D, (g : G) * (a.1 : G) * (g : G)⁻¹ = a.1 :=
    fun a g => congrArg Subtype.val (a.2 g)
  have h1 : ∀ a : MulAction.fixedPoints D V, (a.1 : G) ∈ V ⊓ centralizer (D : Set G) := by
    intro a
    refine mem_inf.mpr ⟨a.1.2, mem_centralizer_iff.mpr fun g hg => ?_⟩
    have h2 := hfix a ⟨g, hg⟩
    calc g * (a.1 : G) = g * a.1 * g⁻¹ * g := by group
      _ = (a.1 : G) * g := by rw [show g * (a.1 : G) * g⁻¹ = a.1 from h2]
  have h3 : ∀ a : ↥(V ⊓ centralizer (D : Set G)),
      (⟨(a : G), (mem_inf.mp a.2).1⟩ : V) ∈ MulAction.fixedPoints D V := by
    intro a g
    have hac : (a : G) ∈ centralizer (D : Set G) := (mem_inf.mp a.2).2
    have hga := mem_centralizer_iff.mp hac g g.2
    apply Subtype.ext
    change (g : G) * (a : G) * (g : G)⁻¹ = a
    calc (g : G) * (a : G) * (g : G)⁻¹ = (a : G) * g * (g : G)⁻¹ := by rw [← hga]
      _ = a := by group
  have heq : Nat.card (MulAction.fixedPoints D V) =
      Nat.card (V ⊓ centralizer (D : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : G), h1 a⟩
        invFun := fun a => ⟨⟨(a : G), (mem_inf.mp a.2).1⟩, h3 a⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [heq] at key
  exact key

theorem card_sup_mul_card_inf_of_normal {G : Type*} [Group G] (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem eq_bot_of_normalized {V K : Subgroup (Perm (Fin 10))}
    (hV : V ≤ alternatingGroup (Fin 10)) (hK : K ≤ alternatingGroup (Fin 10))
    (hV2 : IsPGroup 2 V) (hKV : K ≤ normalizer (V : Set (Perm (Fin 10)))) (hVK : V ⊓ K = ⊥)
    (h2520 : 2520 ∣ Nat.card K) {y : Perm (Fin 10)} (hyK : y ∈ K)
    (hy5 : IsPGroup 5 (zpowers y))
    (hC : ∀ N : Subgroup (Perm (Fin 10)), N ≤ K → K ≤ normalizer (N : Set (Perm (Fin 10))) →
      y ∈ N → ∃ x ∈ N, orderOf x = 7) : V = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hsup := card_sup_mul_card_inf_of_le_normalizer hKV
  rw [hVK, Subgroup.card_bot, mul_one] at hsup
  have hdvdA : Nat.card (V ⊔ K : Subgroup (Perm (Fin 10))) ∣ 1814400 := by
    have h1 := Subgroup.card_dvd_of_le (sup_le hV hK)
    have h10 : Nat.card (Fin 10) = 10 := by simp
    rwa [nat_card_alternatingGroup, h10, show Nat.factorial 10 / 2 = 1814400 by decide] at h1
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hn4 : n ≤ 4 := by
    obtain ⟨m, hm⟩ := h2520
    have h1 : 2 ^ n * 2520 ∣ 720 * 2520 := by
      have h2 : 2 ^ n * 2520 ∣ Nat.card V * Nat.card K := by
        rw [hn, hm, ← mul_assoc]
        exact Dvd.intro m rfl
      rw [← hsup] at h2
      exact h2.trans (by norm_num at hdvdA ⊢; exact hdvdA)
    have h2 : 2 ^ n ∣ 720 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
    by_contra hn5
    push Not at hn5
    have h3 : 2 ^ 5 ∣ 720 := (pow_dvd_pow 2 hn5).trans h2
    norm_num at h3
  obtain ⟨x₀, hx₀K, hx₀⟩ := hC K le_rfl Subgroup.le_normalizer hyK
  have hfix : ∀ x : Perm (Fin 10), orderOf x = 7 → x ∈ K →
      Nat.card V ≡ 1 [MOD 7] := by
    intro x hx hxK
    have hD : IsPGroup 7 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    have hDV : zpowers x ≤ normalizer (V : Set (Perm (Fin 10))) := zpowers_le.mpr (hKV hxK)
    have h1 := card_modEq_card_inf_centralizer hD hDV
    have h2 : V ⊓ centralizer ((zpowers x : Subgroup (Perm (Fin 10))) : Set (Perm (Fin 10))) =
        ⊥ := by
      rw [eq_bot_iff, ← inf_centralizer_eq_bot hV hV2 hx]
      exact inf_le_inf_left _ (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (mem_zpowers x)))
    rwa [h2, Subgroup.card_bot] at h1
  have h7 := hfix x₀ hx₀ hx₀K
  rw [hn] at h7
  interval_cases n
  ·
    exact Subgroup.eq_bot_of_card_eq V (by rw [hn, pow_zero])
  · exact absurd h7 (by decide)
  · exact absurd h7 (by decide)
  ·
    exfalso
    have hDV : zpowers y ≤ normalizer (V : Set (Perm (Fin 10))) := zpowers_le.mpr (hKV hyK)
    have h5 := card_modEq_card_inf_centralizer hy5 hDV
    set W := V ⊓ centralizer ((zpowers y : Subgroup (Perm (Fin 10))) : Set (Perm (Fin 10)))
      with hW
    have hWV : W ≤ V := inf_le_left
    have hWdvd : Nat.card W ∣ 8 := by
      have := Subgroup.card_dvd_of_le hWV
      rwa [hn] at this
    rw [hn] at h5
    have hW8 : Nat.card W = 8 := by
      have hle : Nat.card W ≤ 8 := Nat.le_of_dvd (by norm_num) hWdvd
      interval_cases h : Nat.card W <;> simp_all [Nat.ModEq]
    have hWeq : W = V := Subgroup.eq_of_le_of_card_ge hWV (by rw [hW8, hn]; norm_num)
    have hyC : y ∈ centralizer (V : Set (Perm (Fin 10))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : v ∈ W := hWeq ▸ hv
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv').2 y (mem_zpowers y)).symm
    set N := K ⊓ centralizer (V : Set (Perm (Fin 10))) with hN
    have hKC : K ≤ normalizer ((centralizer (V : Set (Perm (Fin 10))) :
        Subgroup (Perm (Fin 10))) : Set (Perm (Fin 10))) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro hz v hv
        have hv' : k⁻¹ * v * k⁻¹⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hKV hk)) v).mp hv
        have := hz _ hv'
        calc v * (k * z * k⁻¹) = k * ((k⁻¹ * v * k⁻¹⁻¹) * z) * k⁻¹ := by group
          _ = k * (z * (k⁻¹ * v * k⁻¹⁻¹)) * k⁻¹ := by rw [this]
          _ = k * z * k⁻¹ * v := by group
      · intro hz v hv
        have hv' : k * v * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hKV hk) v).mp hv
        have := hz _ hv'
        calc v * z = k⁻¹ * ((k * v * k⁻¹) * (k * z * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * z * k⁻¹) * (k * v * k⁻¹)) * k := by rw [this]
          _ = z * v := by group
    have hKN : K ≤ normalizer (N : Set (Perm (Fin 10))) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [hN, Subgroup.mem_inf, Subgroup.mem_inf,
        Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) z,
        Subgroup.mem_normalizer_iff.mp (hKC hk) z]
    obtain ⟨x₁, hx₁N, hx₁⟩ := hC N inf_le_left hKN ⟨hyK, hyC⟩
    have hbot := inf_centralizer_eq_bot hV hV2 hx₁
    have hVle : V ≤ V ⊓ centralizer ({x₁} : Set (Perm (Fin 10))) := by
      refine le_inf le_rfl ?_
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx₁N).2) v hv
    rw [hbot, le_bot_iff] at hVle
    rw [hVle, Subgroup.card_bot] at hn
    norm_num at hn
  · exact absurd h7 (by decide)

end CFSG.RankThree.PartTwo.Sec16.Res9A10
