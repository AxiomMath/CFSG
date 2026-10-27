module

public import CFSG.Monster.Existence.StdOdd.Cert.Base

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open Subgroup

section PtStab

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def baseStab (β : ℕ → X) (n : ℕ) : Subgroup G where
  carrier := {g | ∀ i < n, g • β i = β i}
  mul_mem' := by
    intro g h hg hh i hi
    rw [mul_smul, hh i hi, hg i hi]
  one_mem' := fun i _ => one_smul G _
  inv_mem' := by
    intro g hg i hi
    calc g⁻¹ • β i = g⁻¹ • (g • β i) := by rw [hg i hi]
      _ = β i := inv_smul_smul g _

theorem mem_baseStab {β : ℕ → X} {n : ℕ} {g : G} : g ∈ baseStab β n ↔ ∀ i < n, g • β i = β i :=
  Iff.rfl

theorem baseStab_zero (β : ℕ → X) : baseStab (G := G) β 0 = ⊤ := by
  ext g
  simp [mem_baseStab]

theorem baseStab_succ (β : ℕ → X) (n : ℕ) :
    baseStab (G := G) β (n + 1) = baseStab β n ⊓ MulAction.stabilizer G (β n) := by
  ext g
  simp only [mem_baseStab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h n (by omega)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · exact h1 i h
    · exact h2

theorem card_eq_prod_ncard_orbit_mul (β : ℕ → X) (n : ℕ) :
    Nat.card G = (∏ i ∈ Finset.range n, (MulAction.orbit (baseStab (G := G) β i) (β i)).ncard) *
      Nat.card (baseStab (G := G) β n) := by
  induction n with
  | zero => simp [baseStab_zero]
  | succ n ih =>
    have h := card_eq_ncard_orbit_mul (baseStab (G := G) β n) (β n)
    rw [← baseStab_succ] at h
    rw [ih, Finset.prod_range_succ, mul_assoc, ← h]

end PtStab

section Exact

variable {G X : Type*} [Group G] [MulAction G X]

theorem eq_of_mul_eq_of_le {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) (hc : 0 < c) (hd : 0 < d)
    (h : a * b = c * d) : a = c ∧ b = d := by
  have hab : a * b ≤ a * d := Nat.mul_le_mul_left a hbd
  have hcd : a * d ≤ c * d := Nat.mul_le_mul_right d hac
  have hac' : a = c := by
    by_contra hne
    have hlt : a < c := lt_of_le_of_ne hac hne
    have : a * d < c * d := Nat.mul_lt_mul_of_pos_right hlt hd
    omega
  subst hac'
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hc h⟩

theorem eq_of_prod_mul_eq (n : ℕ) (a A : ℕ → ℕ) (l L : ℕ) (ha : ∀ i < n, a i ≤ A i)
    (hA : ∀ i < n, 0 < A i) (hl : l ≤ L) (hL : 0 < L)
    (h : (∏ i ∈ Finset.range n, a i) * l = (∏ i ∈ Finset.range n, A i) * L) :
    (∀ i < n, a i = A i) ∧ l = L := by
  induction n generalizing l L with
  | zero => simpa using h
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc, mul_assoc] at h
    have hP : ∏ i ∈ Finset.range n, a i ≤ ∏ i ∈ Finset.range n, A i :=
      Finset.prod_le_prod (fun i hi => ha i (by simp at hi; omega))
    have hP' : 0 < ∏ i ∈ Finset.range n, A i :=
      Finset.prod_pos fun i hi => hA i (by simp at hi; omega)
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_le hP (Nat.mul_le_mul (ha n (by omega)) hl) hP'
      (Nat.mul_pos (hA n (by omega)) hL) h
    obtain ⟨h3, h4⟩ := eq_of_mul_eq_of_le (ha n (by omega)) hl (hA n (by omega)) hL h2
    have h5 := ih 1 1 (fun i hi => ha i (by omega)) (fun i hi => hA i (by omega)) le_rfl one_pos
      (by simpa using h1)
    exact ⟨fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h5.1 i hi
      · exact h3, h4⟩

theorem chain_exact_card [Finite G] (β : ℕ → X) (n : ℕ) (B : ℕ → Finset X) (l : ℕ)
    (hB : ∀ i < n, ∀ y ∈ B i, ∃ k ∈ baseStab (G := G) β i, k • β i = y)
    (hl : l ≤ Nat.card (baseStab (G := G) β n))
    (hprod : (∏ i ∈ Finset.range n, (B i).card) * l = Nat.card G) :
    (∀ i < n, ∀ y, y ∈ MulAction.orbit (baseStab (G := G) β i) (β i) → y ∈ B i) ∧
      l = Nat.card (baseStab (G := G) β n) := by
  have hsub : ∀ i < n, (B i : Set X) ⊆ MulAction.orbit (baseStab (G := G) β i) (β i) := by
    intro i hi y hy
    obtain ⟨k, hk, rfl⟩ := hB i hi y hy
    exact ⟨⟨k, hk⟩, rfl⟩
  have hle : ∀ i < n, (B i).card ≤ (MulAction.orbit (baseStab (G := G) β i) (β i)).ncard := by
    intro i hi
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (hsub i hi) (Set.finite_range _)
  have hpos : ∀ i < n, 0 < (MulAction.orbit (baseStab (G := G) β i) (β i)).ncard := fun i _ =>
    Set.ncard_pos (Set.finite_range _) |>.2 ⟨β i, MulAction.mem_orbit_self _⟩
  obtain ⟨h1, h2⟩ := eq_of_prod_mul_eq n (fun i => (B i).card)
    (fun i => (MulAction.orbit (baseStab (G := G) β i) (β i)).ncard) l
    (Nat.card (baseStab (G := G) β n)) hle hpos hl Nat.card_pos
    (hprod.trans (card_eq_prod_ncard_orbit_mul β n))
  refine ⟨fun i hi y hy => ?_, h2⟩
  have heq : (B i : Set X) = MulAction.orbit (baseStab (G := G) β i) (β i) := by
    refine Set.eq_of_subset_of_ncard_le (hsub i hi) ?_ (Set.finite_range _)
    rw [Set.ncard_coe_finset]
    exact (h1 i hi).ge
  rw [← Finset.mem_coe, heq]
  exact hy

theorem chain_exact [Finite G] (β : ℕ → X) (n : ℕ) (B : ℕ → Finset X) (L : Finset G)
    (hB : ∀ i < n, ∀ y ∈ B i, ∃ k ∈ baseStab (G := G) β i, k • β i = y)
    (hL : ∀ k ∈ L, k ∈ baseStab (G := G) β n)
    (hprod : (∏ i ∈ Finset.range n, (B i).card) * L.card = Nat.card G) :
    (∀ i < n, ∀ y, y ∈ MulAction.orbit (baseStab (G := G) β i) (β i) → y ∈ B i) ∧
      ∀ k, k ∈ baseStab (G := G) β n → k ∈ L := by
  have hcard : L.card ≤ Nat.card (baseStab (G := G) β n) := by
    rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (fun k => ⟨k.1, hL k.1 k.2⟩) fun k k' h =>
      Subtype.ext (by simpa using h)
  obtain ⟨h1, h2⟩ := chain_exact_card β n B L.card hB hcard hprod
  refine ⟨h1, fun k hk => ?_⟩
  have heq : (L : Set G) = baseStab (G := G) β n := by
    refine Set.eq_of_subset_of_ncard_le hL ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact h2.ge
  rw [← Finset.mem_coe, heq]
  exact hk

end Exact

section Sift

variable {G X : Type*} [Group G] [MulAction G X]

structure IsTransversal (β : ℕ → X) (n : ℕ) (B : ℕ → Finset X) (T : ℕ → X → G) : Prop where
  mem : ∀ i < n, ∀ y ∈ B i, T i y ∈ baseStab β i
  smul : ∀ i < n, ∀ y ∈ B i, T i y • β i = y

theorem IsTransversal.exists_mem {β : ℕ → X} {n : ℕ} {B : ℕ → Finset X} {T : ℕ → X → G}
    (hT : IsTransversal β n B T) {i : ℕ} (hi : i < n) {y : X} (hy : y ∈ B i) :
    ∃ k ∈ baseStab (G := G) β i, k • β i = y :=
  ⟨T i y, hT.mem i hi y hy, hT.smul i hi y hy⟩

@[expose] def siftElt (T : ℕ → X → G) (t : ℕ → X) : ℕ → G
  | 0 => 1
  | i + 1 => siftElt T t i * T i ((siftElt T t i)⁻¹ • t i)

@[expose] def SiftPasses (B : ℕ → Finset X) (T : ℕ → X → G) (t : ℕ → X) (n : ℕ) : Prop :=
  ∀ i < n, (siftElt T t i)⁻¹ • t i ∈ B i

section
variable {β : ℕ → X} {n : ℕ} {B : ℕ → Finset X} {T : ℕ → X → G}

theorem siftElt_inv_smul (hT : IsTransversal β n B T) {t : ℕ → X} :
    ∀ m, m ≤ n → (∀ i < m, (siftElt T t i)⁻¹ • t i ∈ B i) →
      ∀ j < m, (siftElt T t m)⁻¹ • t j = β j := by
  intro m
  induction m with
  | zero => intro _ _ j hj; omega
  | succ m ih =>
    intro hm hp j hj
    have ih' := ih (by omega) fun i hi => hp i (by omega)
    have hy := hp m (by omega)
    have hTm := hT.mem m (by omega) _ hy
    have hTs := hT.smul m (by omega) _ hy
    have hsucc : siftElt T t (m + 1) = siftElt T t m * T m ((siftElt T t m)⁻¹ • t m) := rfl
    rw [hsucc, mul_inv_rev, mul_smul]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjm | rfl
    · rw [ih' j hjm]
      exact mem_baseStab.1 ((baseStab β m).inv_mem hTm) j hjm
    · exact inv_smul_eq_iff.2 hTs.symm

theorem smul_base_of_siftPasses (hT : IsTransversal β n B T) {t : ℕ → X}
    (hp : SiftPasses B T t n) : ∀ j < n, siftElt T t n • β j = t j := fun j hj => by
  have := siftElt_inv_smul hT n le_rfl hp j hj
  rw [inv_smul_eq_iff] at this
  exact this.symm

theorem siftPasses_aux (hT : IsTransversal β n B T)
    (hex : ∀ i < n, ∀ y ∈ MulAction.orbit (baseStab (G := G) β i) (β i), y ∈ B i) {t : ℕ → X}
    {g : G} (hg : ∀ j < n, g • β j = t j) :
    ∀ m, m ≤ n → (∀ i < m, (siftElt T t i)⁻¹ • t i ∈ B i) ∧
      (siftElt T t m)⁻¹ * g ∈ baseStab β m := by
  intro m
  induction m with
  | zero => intro _; exact ⟨fun i hi => by omega, by simp [baseStab_zero]⟩
  | succ m ih =>
    intro hm
    obtain ⟨hpass, hk⟩ := ih (by omega)
    have hyk : (siftElt T t m)⁻¹ • t m = ((siftElt T t m)⁻¹ * g) • β m := by
      rw [mul_smul, hg m (by omega)]
    have hy : (siftElt T t m)⁻¹ • t m ∈ B m :=
      hex m (by omega) _ (by rw [hyk]; exact ⟨⟨_, hk⟩, rfl⟩)
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with him | rfl
      · exact hpass i him
      · exact hy
    · have hTm := hT.mem m (by omega) _ hy
      have hTs := hT.smul m (by omega) _ hy
      have hsucc : (siftElt T t (m + 1))⁻¹ * g =
          (T m ((siftElt T t m)⁻¹ • t m))⁻¹ * ((siftElt T t m)⁻¹ * g) := by
        show (siftElt T t m * T m ((siftElt T t m)⁻¹ • t m))⁻¹ * g = _
        rw [mul_inv_rev, mul_assoc]
      rw [hsucc, baseStab_succ]
      refine Subgroup.mem_inf.2 ⟨(baseStab β m).mul_mem ((baseStab β m).inv_mem hTm) hk, ?_⟩
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hyk]
      exact inv_smul_eq_iff.2 hTs.symm

theorem siftPasses_of_smul_base (hT : IsTransversal β n B T)
    (hex : ∀ i < n, ∀ y ∈ MulAction.orbit (baseStab (G := G) β i) (β i), y ∈ B i) {t : ℕ → X}
    {g : G} (hg : ∀ j < n, g • β j = t j) :
    SiftPasses B T t n ∧ (siftElt T t n)⁻¹ * g ∈ baseStab β n :=
  siftPasses_aux hT hex hg n le_rfl

end

structure IsStabChain (β : ℕ → X) (n : ℕ) (B : ℕ → Finset X) (T : ℕ → X → G) (L : Finset G) :
    Prop where
  trans : IsTransversal β n B T
  fix : ∀ k ∈ L, k ∈ baseStab β n
  card : (∏ i ∈ Finset.range n, (B i).card) * L.card = Nat.card G

section
variable {β : ℕ → X} {n : ℕ} {B : ℕ → Finset X} {T : ℕ → X → G} {L : Finset G}

theorem IsStabChain.exact [Finite G] (hc : IsStabChain β n B T L) :
    ∀ i < n, ∀ y, y ∈ MulAction.orbit (baseStab (G := G) β i) (β i) → y ∈ B i :=
  (chain_exact β n B L (fun _ hi _ hy => hc.trans.exists_mem hi hy) hc.fix hc.card).1

theorem IsStabChain.mem_iff [Finite G] (hc : IsStabChain β n B T L) (k : G) :
    k ∈ baseStab β n ↔ k ∈ L :=
  ⟨(chain_exact β n B L (fun _ hi _ hy => hc.trans.exists_mem hi hy) hc.fix hc.card).2 k,
    hc.fix k⟩

theorem IsStabChain.card_baseStab [Finite G] (hc : IsStabChain β n B T L) :
    Nat.card (baseStab (G := G) β n) = L.card := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun k => hc.mem_iff k)

end

end Sift

section OrbitBase

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def orbitBase (x : G) (b : X) (e : ℕ → ℕ) : ℕ → X := fun i => x ^ e i • b

theorem orbitBase_apply (x : G) (b : X) (e : ℕ → ℕ) (i : ℕ) :
    orbitBase x b e i = x ^ e i • b := rfl

theorem mem_baseStab_orbitBase [Finite G] {x : G} {b : X} {e : ℕ → ℕ} {n : ℕ} {g : G}
    (hg : ∀ j < orderOf x, g • (x ^ j • b) = x ^ j • b) : g ∈ baseStab (orbitBase x b e) n := by
  intro i _
  show g • (x ^ e i • b) = x ^ e i • b
  rw [← pow_mod_orderOf x (e i)]
  exact hg _ (Nat.mod_lt _ (orderOf_pos x))

theorem commutator_smul_pow {x g : G} {b u : X} (hω : ∀ j : ℕ, g • (x ^ j • b) = x ^ j • u)
    (j : ℕ) : (x⁻¹ * g⁻¹ * x * g) • (x ^ j • b) = x ^ j • b := by
  have h2 : g • x • x ^ j • b = x • x ^ j • u := by
    have := hω (j + 1)
    rwa [pow_succ', mul_smul, mul_smul] at this
  have h3 : g⁻¹ • x • x ^ j • u = x • x ^ j • b := inv_smul_eq_iff.2 h2.symm
  simp only [mul_smul]
  rw [hω j, h3, inv_smul_smul]

section
variable {x : G} {b u : X} {e : ℕ → ℕ} {n : ℕ} {B : ℕ → Finset X} {T : ℕ → X → G}
  {L : Finset G}

theorem baseStab_orbitBase_le_stabilizer_of_cover [Finite G]
    (hcover : ∀ j < orderOf x, ∃ i < n, x ^ e i = x ^ j) :
    baseStab (orbitBase x b e) n ≤ MulAction.stabilizer G b := fun g hg => by
  obtain ⟨i, hi, hxi⟩ := hcover 0 (orderOf_pos x)
  rw [MulAction.mem_stabilizer_iff]
  have := mem_baseStab.1 hg i hi
  rwa [orbitBase_apply, hxi, pow_zero, one_smul] at this

theorem smul_pow_eq_of_cover [Finite G] (hcover : ∀ j < orderOf x, ∃ i < n, x ^ e i = x ^ j)
    {g : G} (hg : ∀ i < n, g • orbitBase x b e i = orbitBase x u e i) (j : ℕ) :
    g • (x ^ j • b) = x ^ j • u := by
  obtain ⟨i, hi, hxi⟩ := hcover (j % orderOf x) (Nat.mod_lt _ (orderOf_pos x))
  rw [← pow_mod_orderOf x j, ← hxi]
  exact hg i hi

theorem exists_centralizer_smul_eq_iff_of_cover [Finite G]
    (hc : IsStabChain (orbitBase x b e) n B T L)
    (hcover : ∀ j < orderOf x, ∃ i < n, x ^ e i = x ^ j)
    (hH : ∀ κ ∈ L, (x * κ) ^ orderOf x = 1 → ∃ k ∈ L, k * x * k⁻¹ = x * κ) :
    (∃ c ∈ centralizer ({x} : Set G), c • b = u) ↔ SiftPasses B T (orbitBase x u e) n := by
  constructor
  · rintro ⟨c, hcC, rfl⟩
    exact (siftPasses_of_smul_base hc.trans hc.exact (t := orbitBase x (c • b) e) (g := c)
      fun j _ => smul_pow_smul_of_mem_centralizer hcC (e j) b).1
  · intro hp
    set g := siftElt T (orbitBase x u e) n with hg
    have hω : ∀ j : ℕ, g • (x ^ j • b) = x ^ j • u :=
      smul_pow_eq_of_cover hcover (smul_base_of_siftPasses hc.trans hp)
    have hκ : x⁻¹ * g⁻¹ * x * g ∈ L :=
      (hc.mem_iff _).1 (mem_baseStab_orbitBase fun j _ => commutator_smul_pow hω j)
    have hord : (x * (x⁻¹ * g⁻¹ * x * g)) ^ orderOf x = 1 := by
      have e1 : x * (x⁻¹ * g⁻¹ * x * g) = g⁻¹ * x * g := by group
      have e2 := conj_pow (a := g⁻¹) (b := x) (i := orderOf x)
      simp only [inv_inv] at e2
      rw [e1, e2, pow_orderOf_eq_one, mul_one, inv_mul_cancel]
    obtain ⟨k, hkL, hk⟩ := hH _ hκ hord
    have hk' : k * x * k⁻¹ = g⁻¹ * x * g := by rw [hk]; group
    refine ⟨g * k, mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · calc g * k * x = g * (k * x * k⁻¹) * k := by group
        _ = x * (g * k) := by rw [hk']; group
    · have hkb : k • b = b := MulAction.mem_stabilizer_iff.1
        (baseStab_orbitBase_le_stabilizer_of_cover hcover ((hc.mem_iff k).2 hkL))
      have := hω 0
      rw [pow_zero, one_smul, one_smul] at this
      rw [mul_smul, hkb, this]

theorem exists_centralizer_smul_eq_iff_of_coprime [Finite G]
    (hc : IsStabChain (orbitBase x b e) n B T L)
    (hcover : ∀ j < orderOf x, ∃ i < n, x ^ e i = x ^ j)
    (hcomm : ∀ κ ∈ L, κ * x = x * κ) (hcop : Nat.Coprime L.card (orderOf x)) :
    (∃ c ∈ centralizer ({x} : Set G), c • b = u) ↔ SiftPasses B T (orbitBase x u e) n := by
  refine exists_centralizer_smul_eq_iff_of_cover hc hcover fun κ hκ hord => ?_
  have hxκ : Commute x κ := (hcomm κ hκ).symm
  have h1 : κ ^ orderOf x = 1 := by
    have := hxκ.mul_pow (orderOf x)
    rwa [hord, pow_orderOf_eq_one, one_mul, eq_comm] at this
  have hκ1 : κ = 1 := by
    have hd1 : orderOf κ ∣ orderOf x := orderOf_dvd_of_pow_eq_one h1
    have hd2 : orderOf κ ∣ L.card := by
      rw [← hc.card_baseStab]
      exact Subgroup.orderOf_dvd_natCard _ ((hc.mem_iff κ).2 hκ)
    have := Nat.dvd_gcd hd2 hd1
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  subst hκ1
  exact ⟨1, (hc.mem_iff 1).1 (one_mem _), by simp⟩

theorem card_centralizer_eq_of_chain_coprime [Finite G]
    (hc : IsStabChain (orbitBase x b e) n B T L)
    (hcover : ∀ j < orderOf x, ∃ i < n, x ^ e i = x ^ j)
    (hcomm : ∀ κ ∈ L, κ * x = x * κ) (hcop : Nat.Coprime L.card (orderOf x)) (S : Finset X)
    (hS : ∀ c ∈ centralizer ({x} : Set G), c • b ∈ S) (P : X → Prop) [DecidablePred P]
    (hP : ∀ u ∈ S, P u ↔ SiftPasses B T (orbitBase x u e) n) :
    Nat.card (centralizer ({x} : Set G)) = (S.filter P).card * L.card := by
  have hle : baseStab (G := G) (orbitBase x b e) n ≤ centralizer ({x} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.2 (hcomm g ((hc.mem_iff g).1 hg))
  rw [card_centralizer_eq_of_sifting x b S (baseStab (orbitBase x b e) n) hS
    (baseStab_orbitBase_le_stabilizer_of_cover hcover) (fun g hg => mem_baseStab_orbitBase hg) P
    (fun u hu => (hP u hu).trans
      (exists_centralizer_smul_eq_iff_of_coprime hc hcover hcomm hcop).symm),
    inf_eq_left.2 hle, hc.card_baseStab]

end

end OrbitBase

end CFSG.Monster.Existence.StdOdd.Cert
