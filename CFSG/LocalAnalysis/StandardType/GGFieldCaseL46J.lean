module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL46
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type*} [Group G]

theorem card_inf_centralizer_mul_le [Finite G] {p : ℕ} [Fact p.Prime] {U₁ : Subgroup G}
    (hab : IsMulCommutative U₁) (hU₁p : IsPGroup p U₁) {a : G}
    (ha : a ∈ Subgroup.normalizer (U₁ : Set G)) {k : ℕ}
    (hak : a ^ p ^ k ∈ Subgroup.centralizer (U₁ : Set G))
    (hna : a ∉ Subgroup.centralizer (U₁ : Set G)) :
    Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p ≤
      Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p} : Set G) : Subgroup G) := by
  have hp := (Fact.out : p.Prime)
  have hcomm : ∀ u ∈ U₁, ∀ v ∈ U₁, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hconjU : ∀ u ∈ U₁, a * u * a⁻¹ ∈ U₁ := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp ha u).mp hu
  have memC : ∀ (b v : G), v ∈ Subgroup.centralizer ({b} : Set G) ↔ b * v = v * b := by
    intro b v
    rw [Subgroup.mem_centralizer_iff]
    simp
  have hFF' : U₁ ⊓ Subgroup.centralizer ({a} : Set G) ≤
      U₁ ⊓ Subgroup.centralizer ({a ^ p} : Set G) := by
    intro v hv
    refine ⟨hv.1, (memC _ v).mpr ?_⟩
    exact (Commute.pow_left ((memC a v).mp hv.2) p).eq
  have hne : U₁ ⊓ Subgroup.centralizer ({a} : Set G) ≠
      U₁ ⊓ Subgroup.centralizer ({a ^ p} : Set G) := by
    intro heq
    let ν : U₁ →* G := MonoidHom.mk' (fun u => (u : G)⁻¹ * (a * u * a⁻¹)) (by
      intro u v
      have h1 : (v : G)⁻¹ * ((u : G)⁻¹ * (a * u * a⁻¹)) =
          ((u : G)⁻¹ * (a * u * a⁻¹)) * (v : G)⁻¹ :=
        hcomm _ (U₁.inv_mem v.2) _ (U₁.mul_mem (U₁.inv_mem u.2) (hconjU _ u.2))
      simp only [Subgroup.coe_mul]
      calc ((u : G) * v)⁻¹ * (a * (u * v) * a⁻¹)
          = (v : G)⁻¹ * ((u : G)⁻¹ * (a * u * a⁻¹)) * (a * v * a⁻¹) := by group
        _ = ((u : G)⁻¹ * (a * u * a⁻¹)) * (v : G)⁻¹ * (a * v * a⁻¹) := by rw [h1]
        _ = (u : G)⁻¹ * (a * u * a⁻¹) * ((v : G)⁻¹ * (a * v * a⁻¹)) := by group)
    have hν : ∀ u : U₁, ν u = (u : G)⁻¹ * (a * u * a⁻¹) := fun _ => rfl
    have hWU₁ : ν.range ≤ U₁ := by
      rintro _ ⟨u, rfl⟩
      rw [hν]
      exact U₁.mul_mem (U₁.inv_mem u.2) (hconjU _ u.2)
    have hWne : ∃ w ∈ ν.range, w ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hna
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 := hcon _ ⟨⟨u, hu⟩, rfl⟩
      rw [hν] at h1
      have h2 : a * u * a⁻¹ = u := by
        calc a * u * a⁻¹ = u * (u⁻¹ * (a * u * a⁻¹)) := by group
          _ = u := by rw [h1, mul_one]
      calc u * a = a * u * a⁻¹ * a := by rw [h2]
        _ = a * u := by group
    have hWp : IsPGroup p ν.range := hU₁p.to_le hWU₁
    have hpW : p ∣ Nat.card ν.range := by
      rcases hWp.card_eq_or_dvd with h | h
      · exfalso
        obtain ⟨w, hw, hw1⟩ := hWne
        rw [Subgroup.card_eq_one] at h
        rw [h] at hw
        exact hw1 hw
      · exact h
    have hWN : Subgroup.zpowers a ≤ Subgroup.normalizer (ν.range : Set G) := by
      rw [Subgroup.zpowers_le]
      have hinv : a⁻¹ ∈ Subgroup.normalizer (ν.range : Set G) := by
        apply mem_normalizer_of_forall_conj_mem
        rintro _ ⟨u, rfl⟩
        refine ⟨⟨a * u * a⁻¹, hconjU _ u.2⟩, ?_⟩
        rw [hν, hν]
        group
      simpa using Subgroup.inv_mem _ hinv
    have hWa : ∀ g ∈ Subgroup.zpowers a, ∃ k' : ℕ,
        g ^ p ^ k' ∈ Subgroup.centralizer (ν.range : Set G) := by
      intro g hg
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨k, ?_⟩
      have e : (a ^ i) ^ p ^ k = (a ^ p ^ k) ^ i := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      rw [e]
      exact Subgroup.zpow_mem _ (Subgroup.centralizer_le hWU₁ hak) i
    obtain ⟨w, hwW, hw1, hwa⟩ := exists_ne_one_mem_centralizer hpW hWN hWa
    have haw : a * w = w * a := Subgroup.mem_centralizer_iff.mp hwa a (Subgroup.mem_zpowers a)
    obtain ⟨u, hu⟩ := hwW
    have hwU₁ : w ∈ U₁ := hWU₁ ⟨u, hu⟩
    obtain ⟨n₀, hn₀⟩ := hU₁p ⟨w, hwU₁⟩
    have hwn₀ : w ^ p ^ n₀ = 1 := by
      have := congrArg Subtype.val hn₀
      simpa using this
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hwn₀)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hw1 (orderOf_eq_one_iff.mp (by simpa using hn))
    have hw'p : (w ^ p ^ (n - 1)) ^ p = 1 := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), ← hn,
        pow_orderOf_eq_one]
    have hw'1 : w ^ p ^ (n - 1) ≠ 1 := by
      refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.ne_zero) ?_
      rw [hn]
      exact Nat.pow_lt_pow_right hp.one_lt (Nat.sub_lt (Nat.pos_of_ne_zero hn0) one_pos)
    set w' := w ^ p ^ (n - 1) with hw'def
    have hu' : ν (u ^ p ^ (n - 1)) = w' := by rw [map_pow, hu]
    have haw' : a * w' = w' * a := (Commute.pow_right haw _).eq
    set u' : G := ((u ^ p ^ (n - 1) : U₁) : G) with hu'def
    have hu'U₁ : u' ∈ U₁ := (u ^ p ^ (n - 1)).2
    have hau' : a * u' * a⁻¹ = u' * w' := by
      rw [← hu', hν, ← hu'def]
      group
    have hiter : ∀ m : ℕ, a ^ m * u' * (a ^ m)⁻¹ = u' * w' ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hc : a * w' ^ m * a⁻¹ = w' ^ m := by
          rw [(Commute.pow_right haw' m).eq, mul_inv_cancel_right]
        calc a ^ (m + 1) * u' * (a ^ (m + 1))⁻¹ = a * (a ^ m * u' * (a ^ m)⁻¹) * a⁻¹ := by
              rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
          _ = (a * u' * a⁻¹) * (a * w' ^ m * a⁻¹) := by rw [ih]; group
          _ = u' * w' ^ (m + 1) := by rw [hau', hc, pow_succ', mul_assoc]
    have hu'F' : u' ∈ U₁ ⊓ Subgroup.centralizer ({a ^ p} : Set G) := by
      refine ⟨hu'U₁, (memC _ u').mpr ?_⟩
      have h1 := hiter p
      rw [hw'p, mul_one] at h1
      calc a ^ p * u' = a ^ p * u' * (a ^ p)⁻¹ * a ^ p := by group
        _ = u' * a ^ p := by rw [h1]
    rw [← heq] at hu'F'
    have hau : a * u' = u' * a := (memC a u').mp hu'F'.2
    apply hw'1
    have h2 : u' * w' = u' := by rw [← hau', hau, mul_inv_cancel_right]
    calc w' = u'⁻¹ * (u' * w') := by group
      _ = 1 := by rw [h2, inv_mul_cancel]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hU₁p.to_le (inf_le_left :
    U₁ ⊓ Subgroup.centralizer ({a} : Set G) ≤ U₁))
  obtain ⟨m', hm'⟩ := IsPGroup.iff_card.mp (hU₁p.to_le (inf_le_left :
    U₁ ⊓ Subgroup.centralizer ({a ^ p} : Set G) ≤ U₁))
  have hdvd := Subgroup.card_dvd_of_le hFF'
  have hcne : Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≠
      Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p} : Set G) : Subgroup G) := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hFF' h.ge)
  rw [hm, hm'] at hdvd hcne ⊢
  have hle : m ≤ m' := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hlt : m < m' := lt_of_le_of_ne hle fun h => hcne (by rw [h])
  rw [← pow_succ]
  exact Nat.pow_le_pow_right hp.pos hlt

theorem card_inf_centralizer_mul_pow_le [Finite G] {p : ℕ} [Fact p.Prime] {U₁ : Subgroup G}
    (hab : IsMulCommutative U₁) (hU₁p : IsPGroup p U₁) {a : G}
    (ha : a ∈ Subgroup.normalizer (U₁ : Set G)) {k : ℕ}
    (hak : a ^ p ^ k ∈ Subgroup.centralizer (U₁ : Set G)) :
    ∀ j : ℕ, a ^ p ^ j ∉ Subgroup.centralizer (U₁ : Set G) →
      Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p ^ j ≤
        Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G) : Subgroup G) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hpow : a ^ p ^ (j + 1) = (a ^ p ^ j) ^ p := by rw [pow_succ, pow_mul]
    have hj' : a ^ p ^ j ∉ Subgroup.centralizer (U₁ : Set G) := fun h =>
      hj (hpow ▸ Subgroup.pow_mem _ h p)
    have hbk : (a ^ p ^ j) ^ p ^ k ∈ Subgroup.centralizer (U₁ : Set G) := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact Subgroup.pow_mem _ hak _
    have hstep := card_inf_centralizer_mul_le hab hU₁p (Subgroup.pow_mem _ ha _) hbk hj'
    rw [← hpow] at hstep
    calc Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p ^ (j + 1)
        = Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p ^ j * p := by
          rw [pow_succ, mul_assoc]
      _ ≤ Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G) : Subgroup G) * p :=
          Nat.mul_le_mul_right p (ih hj')
      _ ≤ _ := hstep

theorem card_le_card_inf_mul_of_le_sup [Finite G] {A U₁ : Subgroup G} {a : G} (haA : a ∈ A)
    (ha : a ∈ Subgroup.normalizer (U₁ : Set G)) (hA : A ≤ Subgroup.zpowers a ⊔ U₁) {n : ℕ}
    (hn : 0 < n) (han : a ^ n ∈ U₁) :
    Nat.card A ≤ Nat.card (A ⊓ U₁ : Subgroup G) * n := by
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (U₁ : Set G) := Subgroup.zpowers_le.mpr ha
  let f : Fin n × (A ⊓ U₁ : Subgroup G) → A := fun iu =>
    ⟨a ^ (iu.1 : ℕ) * iu.2, A.mul_mem (A.pow_mem haA _) iu.2.2.1⟩
  have hf : Function.Surjective f := by
    rintro ⟨b, hb⟩
    have hb' : b ∈ ((Subgroup.zpowers a ⊔ U₁ : Subgroup G) : Set G) := hA hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ haN] at hb'
    obtain ⟨z, hz, u, hu, rfl⟩ := hb'
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
    have e : a ^ i = a ^ (i % n) * (a ^ n) ^ (i / n) := by
      rw [← pow_mul, ← pow_add, add_comm, Nat.div_add_mod]
    set u₂ := (a ^ n) ^ (i / n) * u with hu₂
    have hu₂U : u₂ ∈ U₁ := U₁.mul_mem (U₁.pow_mem han _) hu
    have hu₂A : u₂ ∈ A := by
      have h1 : u₂ = (a ^ (i % n))⁻¹ * (a ^ i * u) := by rw [hu₂, e]; group
      rw [h1]
      exact A.mul_mem (A.inv_mem (A.pow_mem haA _)) hb
    refine ⟨(⟨i % n, Nat.mod_lt _ hn⟩, ⟨u₂, hu₂A, hu₂U⟩), ?_⟩
    apply Subtype.ext
    change a ^ (i % n) * u₂ = a ^ i * u
    rw [hu₂, e, mul_assoc]
  have h := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_fin, mul_comm] at h
  exact h

theorem exists_gen_mod_of_cyclic [Finite G] {p : ℕ} [Fact p.Prime] {U U₁ A : Subgroup G}
    {g : G} (hU₁U : U₁ ≤ U) (hUN : U ≤ Subgroup.normalizer (U₁ : Set G)) (hUp : IsPGroup p U)
    (hgU : g ∈ U) (hcyc : U ≤ Subgroup.zpowers g ⊔ U₁) (hAU : A ≤ U) (hAU₁ : ¬ A ≤ U₁) :
    ∃ a ∈ A, ∃ j : ℕ, A ≤ Subgroup.zpowers a ⊔ U₁ ∧ a ^ p ^ (j + 1) ∈ U₁ ∧
      a ^ p ^ j ∉ U₁ := by
  have hp := (Fact.out : p.Prime)
  have hNn : (U₁.subgroupOf U).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hUN g.2) n).mp hn⟩
  let π : U →* U ⧸ U₁.subgroupOf U := QuotientGroup.mk' _
  have hπ : ∀ w : U, π w = 1 ↔ (w : G) ∈ U₁ := fun w => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ w w' : U, π w = π w' → (w : G) = w' * ((w' : G)⁻¹ * w) ∧
      (w' : G)⁻¹ * w ∈ U₁ := fun w w' h => by
    refine ⟨by group, ?_⟩
    have h1 : π (w'⁻¹ * w) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    simpa using (hπ _).mp h1
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (U₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hUN hgU)
  have hQcyc : IsCyclic (U ⧸ U₁.subgroupOf U) := by
    refine ⟨⟨π ⟨g, hgU⟩, fun q => ?_⟩⟩
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (U₁.subgroupOf U) q
    have hw : (w : G) ∈ ((Subgroup.zpowers g ⊔ U₁ : Subgroup G) : Set G) := hcyc w.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hgN] at hw
    obtain ⟨z, hz, u, hu, hzu⟩ := hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨i, ?_⟩
    have hw' : w = (⟨g, hgU⟩ : U) ^ i * ⟨u, (hU₁U hu)⟩ := by
      apply Subtype.ext
      simp [hzu]
    change π ⟨g, hgU⟩ ^ i = π w
    rw [hw', map_mul, map_zpow, (hπ ⟨u, _⟩).mpr hu, mul_one]
  set Abar : Subgroup (U ⧸ U₁.subgroupOf U) := (A.subgroupOf U).map π with hAbar
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Abar)
  obtain ⟨a', ha'A, ha'γ⟩ := Subgroup.mem_map.mp γ.2
  have haA : (a' : G) ∈ A := Subgroup.mem_subgroupOf.mp ha'A
  have himg : ∀ (b : G) (hb : b ∈ A), ∃ i : ℤ, π (a' ^ i) = π ⟨b, hAU hb⟩ := by
    intro b hb
    have hbbar : π ⟨b, hAU hb⟩ ∈ Abar :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨_, hbbar⟩)
    refine ⟨i, ?_⟩
    rw [map_zpow, ha'γ]
    have := congrArg Subtype.val hi
    simpa using this
  have hAle : A ≤ Subgroup.zpowers (a' : G) ⊔ U₁ := by
    intro b hb
    obtain ⟨i, hi⟩ := himg b hb
    obtain ⟨e, hmem⟩ := hπeq _ _ hi.symm
    change ((⟨b, hAU hb⟩ : U) : G) ∈ _
    rw [e]
    refine Subgroup.mul_mem_sup ?_ hmem
    rw [Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers _ i
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp (hUp.to_quotient (U₁.subgroupOf U)) (π a')
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hAU₁
    intro b hb
    have h1 : π a' = 1 := orderOf_eq_one_iff.mp (by simpa using hn)
    obtain ⟨i, hi⟩ := himg b hb
    rw [map_zpow, h1, one_zpow] at hi
    exact (hπ _).mp hi.symm
  have hy1 : π a' ^ p ^ (n - 1) ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.ne_zero) ?_
    rw [hn]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  refine ⟨a', haA, n - 1, hAle, ?_, ?_⟩
  · have h1 : π (a' ^ p ^ (n - 1 + 1)) = 1 := by
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), map_pow, ← hn,
        pow_orderOf_eq_one]
    simpa using (hπ _).mp h1
  · intro h
    apply hy1
    rw [← map_pow]
    exact (hπ _).mpr (by simpa using h)

end General

section Main

variable {G : Type} [Group G]

theorem pow_pow_sub_one_eq_one_of_commute {p s i : ℕ} [Fact p.Prime] (hs : 2 ≤ s)
    {U₁ : Subgroup G} {x' : G} (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1)
    (hact : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) (hi : ¬ p ∣ i) {v : G}
    (hv : v ∈ U₁) (hvx : x' ^ i * v = v * x' ^ i) : v ^ p ^ (s - 1) = 1 := by
  have hp := (Fact.out : p.Prime)
  have h1 := conj_pow_eq_mul_pow_pow hs hexp hact i v hv
  rw [mul_assoc, ← hvx, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  have h2 : (v ^ p ^ (s - 1)) ^ i = 1 := by
    have := congrArg (v⁻¹ * ·) h1
    simpa using this.symm
  have h3 : (v ^ p ^ (s - 1)) ^ p = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s), hexp v hv]
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ orderOf_dvd_of_pow_eq_one h2) hi

theorem card_eq_card_omega_mul_card_ggPowSubgroup [Finite G] {U₁ : Subgroup G}
    (hab : IsMulCommutative U₁) (n : ℕ) :
    Nat.card U₁ = Nat.card ({u : G | u ∈ U₁ ∧ u ^ n = 1} : Set G) *
      Nat.card (ggPowSubgroup U₁ hab n) := by
  let φ : U₁ →* G := MonoidHom.mk' (fun u => (u : G) ^ n) (by
    intro u v
    have hc : Commute (u : G) v := congrArg Subtype.val (hab.is_comm.comm u v)
    simp only [Subgroup.coe_mul]
    exact hc.mul_pow n)
  have hrange : φ.range = ggPowSubgroup U₁ hab n := by
    ext w
    rw [MonoidHom.mem_range, mem_ggPowSubgroup]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have hker : Nat.card φ.ker = Nat.card ({u : G | u ∈ U₁ ∧ u ^ n = 1} : Set G) := by
    refine Nat.card_congr
      { toFun := fun u => ⟨(u : U₁), (u : U₁).2, (MonoidHom.mem_ker).mp u.2⟩
        invFun := fun u => ⟨⟨u, u.2.1⟩, (MonoidHom.mem_ker).mpr u.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← hker, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem thompsonAbelianSubgroups_eq_of_cyclic [Finite G] {p : ℕ} [Fact p.Prime]
    {U U₁ : Subgroup G} {x' g : G} {s : ℕ} (hs : 2 ≤ s) (hU₁U : U₁ ≤ U)
    (hUN : U ≤ Subgroup.normalizer (U₁ : Set G)) (hUp : IsPGroup p U)
    (hab : IsMulCommutative U₁) (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1)
    (hord : ∃ u ∈ U₁, orderOf u = p ^ s) (hx'U : x' ∈ U) (hx'p : x' ^ p = 1)
    (hact : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1)))
    (hgU : g ∈ U) (hcyc : U ≤ Subgroup.zpowers g ⊔ U₁)
    (hbig : p ^ 2 ≤ Nat.card (ggPowSubgroup U₁ hab (p ^ (s - 1)))) :
    ∀ A ∈ thompsonAbelianSubgroups U, A = U₁ := by
  have hp := (Fact.out : p.Prime)
  have hcomm : ∀ u ∈ U₁, ∀ v ∈ U₁, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have memC : ∀ (b v : G), v ∈ Subgroup.centralizer ({b} : Set G) ↔ b * v = v * b := by
    intro b v
    rw [Subgroup.mem_centralizer_iff]
    simp
  intro A hA
  obtain ⟨hAU, hAab, hAmax⟩ := hA
  have hU₁A : Nat.card U₁ ≤ Nat.card A := hAmax U₁ hU₁U hab
  by_contra hne
  have hAU₁ : ¬ A ≤ U₁ := fun h => hne (Subgroup.eq_of_le_of_card_ge h hU₁A)
  obtain ⟨u₀, hu₀, hou₀⟩ := hord
  have hnotfix : ∀ c : ℕ, u₀ ^ p ^ (s - 1) = 1 → False := by
    intro _ h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hou₀] at h1
    have h2 := Nat.le_of_dvd (pow_pos hp.pos _) h1
    have h3 : p ^ (s - 1) < p ^ s := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  have hx'U₁ : x' ∉ U₁ := by
    intro hx
    have hc : x'⁻¹ * u₀ * x' = u₀ := by
      rw [mul_assoc, hcomm u₀ hu₀ x' hx, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hact u₀ hu₀, pow_add, pow_one] at hc
    exact hnotfix 0 (by simpa using congrArg (u₀⁻¹ * ·) hc)
  obtain ⟨a, haA, j, hAle, haj1, hajU₁⟩ :=
    exists_gen_mod_of_cyclic hU₁U hUN hUp hgU hcyc hAU hAU₁
  have hajx : a ^ p ^ j ∈ Subgroup.zpowers x' ⊔ U₁ :=
    mem_zpowers_sup_of_cyclic hUN hgU hcyc hx'U hx'U₁ hx'p (U.pow_mem (hAU haA) _)
      (by rw [← pow_mul, ← pow_succ]; exact haj1)
  have hx'N : Subgroup.zpowers x' ≤ Subgroup.normalizer (U₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hUN hx'U)
  have hajx' : a ^ p ^ j ∈ ((Subgroup.zpowers x' ⊔ U₁ : Subgroup G) : Set G) := hajx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hx'N] at hajx'
  obtain ⟨z, hz, u, hu, hzu⟩ := hajx'
  beta_reduce at hzu
  obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  have hpi : ¬ p ∣ i := by
    rintro ⟨c, rfl⟩
    apply hajU₁
    rw [← hzu, pow_mul, hx'p, one_pow, one_mul]
    exact hu
  have hCsub : ∀ v ∈ U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G),
      v ∈ U₁ ∧ v ^ p ^ (s - 1) = 1 := by
    intro v hv
    refine ⟨hv.1, ?_⟩
    have hcv : a ^ p ^ j * v = v * a ^ p ^ j := (memC _ v).mp hv.2
    have huv : u * v = v * u := hcomm u hu v hv.1
    have hx'v : x' ^ i * v = v * x' ^ i := by
      have h1 : x' ^ i * v * u = v * x' ^ i * u := by
        calc x' ^ i * v * u = x' ^ i * (u * v) := by rw [huv]; group
          _ = a ^ p ^ j * v := by rw [← hzu]; group
          _ = v * a ^ p ^ j := hcv
          _ = v * x' ^ i * u := by rw [← hzu]; group
      exact mul_right_cancel h1
    exact pow_pow_sub_one_eq_one_of_commute hs hexp hact hpi hv.1 hx'v
  have hajC : a ^ p ^ j ∉ Subgroup.centralizer (U₁ : Set G) := by
    intro h
    have hv : u₀ ∈ U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G) :=
      ⟨hu₀, (memC _ u₀).mpr (Subgroup.mem_centralizer_iff.mp h u₀ hu₀).symm⟩
    exact hnotfix 0 (hCsub u₀ hv).2
  have hU₁C : U₁ ≤ Subgroup.centralizer (U₁ : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => hcomm w hw v hv
  have haN : a ∈ Subgroup.normalizer (U₁ : Set G) := hUN (hAU haA)
  have hchain := card_inf_centralizer_mul_pow_le hab (hUp.to_le hU₁U) haN (hU₁C haj1) j hajC
  have hCΩ : Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G) : Subgroup G) ≤
      Nat.card ({u : G | u ∈ U₁ ∧ u ^ p ^ (s - 1) = 1} : Set G) :=
    Nat.card_mono (Set.toFinite _) (fun v hv => hCsub v hv)
  have hAC : A ⊓ U₁ ≤ U₁ ⊓ Subgroup.centralizer ({a} : Set G) := fun v hv =>
    ⟨hv.2, (memC a v).mpr (congrArg Subtype.val (hAab.is_comm.comm ⟨a, haA⟩ ⟨v, hv.1⟩))⟩
  have hcount := card_le_card_inf_mul_of_le_sup haA haN hAle (pow_pos hp.pos _) haj1
  have hAC' := Subgroup.card_le_of_le hAC
  have hΩpos : 0 < Nat.card ({u : G | u ∈ U₁ ∧ u ^ p ^ (s - 1) = 1} : Set G) := by
    have : Nonempty ({u : G | u ∈ U₁ ∧ u ^ p ^ (s - 1) = 1} : Set G) :=
      ⟨⟨1, U₁.one_mem, one_pow _⟩⟩
    exact Nat.card_pos
  have key : Nat.card A ≤ Nat.card ({u : G | u ∈ U₁ ∧ u ^ p ^ (s - 1) = 1} : Set G) * p := by
    calc Nat.card A ≤ Nat.card (A ⊓ U₁ : Subgroup G) * p ^ (j + 1) := hcount
      _ ≤ Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p ^ (j + 1) :=
          Nat.mul_le_mul_right _ hAC'
      _ = Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p ^ j * p := by
          rw [pow_succ, mul_assoc]
      _ ≤ Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G) : Subgroup G) * p :=
          Nat.mul_le_mul_right _ hchain
      _ ≤ _ := Nat.mul_le_mul_right _ hCΩ
  have hdec := card_eq_card_omega_mul_card_ggPowSubgroup hab (p ^ (s - 1))
  have h2 := hp.two_le
  have hbig' : Nat.card ({u : G | u ∈ U₁ ∧ u ^ p ^ (s - 1) = 1} : Set G) * p ^ 2 ≤
      Nat.card U₁ := by
    rw [hdec]
    exact Nat.mul_le_mul_left _ hbig
  nlinarith

end Main

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGL46Core (p : ℕ) (Bs : Subgroup G) (x : G) (X U U₁ : Subgroup G) : Prop :=
  IsMulCommutative U₁ ∧
    (∃ s : ℕ, 2 ≤ s ∧ (∀ u ∈ U₁, u ^ p ^ s = 1) ∧ (∃ u ∈ U₁, orderOf u = p ^ s) ∧
      (∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
        ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) ∧
      ∃ (H : Subgroup G) (r : ℕ), H ≤ U₁ ∧ (∀ h ∈ H, h ^ p ^ s = 1) ∧
        Nat.card H = p ^ (s * r) ∧
        Nat.card (H ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) = p ^ r ∧
        Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤ p ^ (r + 1)) ∧
    (∀ u : G, u ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ u ∈ U₁ ∧ u ^ p = 1) ∧
    (∀ u ∈ U, u ^ p = 1 → u ∈ Bs)

end Defs

@[expose] def GGL46CoreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46Core p Bs x X U U₁

@[expose] def GGL46CyclicInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁

theorem ggUModUOneCyclicInput_of_l46 (hcyc : GGL46CyclicInput) : GGUModUOneCyclicInput :=
  fun G _ _ p B Bs x L D J X B₂ d y K U U₁ hS _ => hcyc G p B Bs x L D J X B₂ d y K U U₁ hS

theorem ggL46StructInput_of_core (hcore : GGL46CoreInput) (hcyc : GGL46CyclicInput) :
    GGL46StructInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS
  obtain ⟨hab, hii, hΩ₁, hΩU⟩ := hcore G p B Bs x L D J X B₂ d y K U U₁ hS
  obtain ⟨g, hgU, hcycU⟩ := hcyc G p B Bs x L D J X B₂ d y K U U₁ hS
  refine ⟨hab, hii, ?_, hΩ₁, hΩU⟩
  obtain ⟨s, hs, hexp, hord, ⟨x', hx'x, hx'⟩, H, r, hHU₁, -, hHcard, hHB₁, hB₁card⟩ := hii
  have hcfg := hS.1.1
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hp := (Fact.out : p.Prime)
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  obtain ⟨hUC, hUp, -, hBsU⟩ := hS.2.2.2.2.2.2.1
  have hU₁U : U₁ ≤ U := hS.2.2.2.2.2.2.2.1.2.1
  have hUN : U ≤ Subgroup.normalizer (U₁ : Set G) := fun u hu =>
    hS.2.2.2.2.2.2.2.2 ⟨Subgroup.le_normalizer hu,
      Subgroup.centralizer_le_normalizer _ (hUC hu)⟩
  have hx'zx : x' ∈ Subgroup.zpowers x := hx'x ▸ Subgroup.mem_zpowers x'
  have hx'U : x' ∈ U := Subgroup.zpowers_le.mpr (hBsU hxBs) hx'zx
  have hx'p : x' ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'zx
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard := card_le_mul_card_ggPowSubgroup hp (by omega) hab hΩ₁ hHU₁ hHcard hHB₁ hB₁card
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hL43 : GGL43 Bs x X := hS.2.2.1
  have hBsB₁ : Nat.card Bs ≤ Nat.card B₁ * p := by
    have hxN : x ∈ Subgroup.normalizer (B₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
        mul_comm_of_isElemAbelian hBs hb.1 hxBs)
    have h := card_le_card_inf_mul_of_le_sup hxBs hxN
      (by rw [hL43.2, sup_comm]) hp.pos (by rw [hxp]; exact B₁.one_mem)
    rwa [inf_eq_right.mpr (inf_le_left : B₁ ≤ Bs)] at h
  have hB4 : p ^ 4 ≤ Nat.card Bs := by
    have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
    have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
      _ = Nat.card B := hBc.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  have hbig : p ^ 2 ≤ Nat.card (ggPowSubgroup U₁ hab (p ^ (s - 1))) := by
    have h1 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card (ggPowSubgroup U₁ hab (p ^ (s - 1))) := by
      have e1 : p ^ 2 * p ^ 2 = p ^ 4 := by ring
      have e2 : Nat.card Bs ≤ p * Nat.card (ggPowSubgroup U₁ hab (p ^ (s - 1))) * p :=
        hBsB₁.trans (Nat.mul_le_mul_right p hcard)
      nlinarith
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos 2)
  exact thompsonAbelianSubgroups_eq_of_cyclic hs hU₁U hUN hUp hab hexp hord hx'U hx'p hx' hgU
    hcycU hbig

theorem ggL46Input_of_core (h43 : GGL43Input) (hcore : GGL46CoreInput)
    (hcyc : GGL46CyclicInput) : GGL46Input :=
  ggL46Input_of_struct h43 (ggL46StructInput_of_core hcore hcyc)

theorem ggL46Input_of_core_tableB (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hcore : GGL46CoreInput)
    (hcyc : GGL46CyclicInput) : GGL46Input :=
  ggL46Input_of_tableB hTB hNN hTBM hTBA (ggL46StructInput_of_core hcore hcyc)

end CFSG.StandardType

end
