module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreSec45
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreAct
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreBSylow

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem isElemAb_E (h : FF84Sec4 b L B K b₁ b₂) :
    IsElementaryAbelian 3 (Subgroup.closure ({b, b₁} : Set G)) :=
  { toIsMulCommutative := ⟨⟨fun x y =>
      Subtype.ext (comm_of_mem h (closure_pair_le h x.2) (closure_pair_le h y.2)).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
      Subtype.ext (pow3_of_mem h (closure_pair_le h x.2)) }

theorem card_E_ge (h : FF84Sec4 b L B K b₁ b₂) :
    9 ≤ Nat.card (Subgroup.closure ({b, b₁} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({b, b₁} : Set G) with hE
  have hE3 : IsPGroup 3 E := (isPGroup_B h).to_le (closure_pair_le h)
  obtain ⟨k, hk⟩ := hE3.exists_card_eq
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hb₁E : b₁ ∈ E := Subgroup.subset_closure (by simp)
  have hzb : Subgroup.zpowers b ≤ E := Subgroup.zpowers_le.2 hbE
  have hcb : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, h.hyp.ord]
  rw [hk]
  rcases k with _ | _ | k
  · exfalso
    have h1 : Nat.card E = 1 := by rw [hk]; rfl
    have : b ∈ (⊥ : Subgroup G) := by
      have := Subgroup.card_eq_one.1 h1
      rwa [this] at hbE
    exact b_ne_one h (Subgroup.mem_bot.1 this)
  · exfalso
    have h3 : Nat.card E = 3 := by rw [hk]; norm_num
    have heq : Subgroup.zpowers b = E := Subgroup.eq_of_le_of_card_ge hzb (by rw [h3, hcb])
    exact b₁_notin_zpowers_b h (heq ▸ hb₁E)
  · calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem E_rep (h : FF84Sec4 b L B K b₁ b₂) {a : G}
    (ha : a ∈ Subgroup.closure ({b, b₁} : Set G)) : ∃ i j : ℤ, a = b ^ i * b₁ ^ j := by
  obtain ⟨i, j, k, rfl⟩ := coord_of_mem_B h (closure_pair_le h ha)
  have hb₂3 : b₂ ^ 3 = 1 := pow3_of_mem h (mem_b₂ h)
  have hk : (3 : ℤ) ∣ k := by
    by_contra hk
    apply b₂_notin_E h
    refine mem_of_zpow_mem hb₂3 hk ?_
    have hE : b ^ i * b₁ ^ j ∈ Subgroup.closure ({b, b₁} : Set G) :=
      mul_mem (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
    have e : b₂ ^ k = (b ^ i * b₁ ^ j)⁻¹ * (b ^ i * b₁ ^ j * b₂ ^ k) := by group
    rw [e]
    exact mul_mem (inv_mem hE) ha
  obtain ⟨t, rfl⟩ := hk
  refine ⟨i, j, ?_⟩
  rw [zpow_mul]
  have : b₂ ^ (3 : ℤ) = 1 := by exact_mod_cast hb₂3
  rw [this, one_zpow, mul_one]

theorem E_four (h : FF84Sec4 b L B K b₁ b₂) {a : G}
    (ha : a ∈ Subgroup.closure ({b, b₁} : Set G)) (ha1 : a ≠ 1) :
    b ∈ Subgroup.zpowers a ∨ b₁ ∈ Subgroup.zpowers a ∨ b * b₁ ∈ Subgroup.zpowers a ∨
      b * b₁ ^ 2 ∈ Subgroup.zpowers a := by
  obtain ⟨i, j, rfl⟩ := E_rep h ha
  have hb3 := pow3_of_mem h (mem_b h)
  have hb₁3 := pow3_of_mem h (mem_b₁ h)
  have hc : Commute b b₁ := comm_of_mem h (mem_b h) (mem_b₁ h)
  have hk : ∀ k : ℤ, (b ^ i * b₁ ^ j) ^ k = b ^ ((i * k) % 3) * b₁ ^ ((j * k) % 3) := by
    intro k
    rw [(hc.zpow_zpow i j).mul_zpow k, ← zpow_mul, ← zpow_mul, ← zpow_emod_three hb3,
      ← zpow_emod_three hb₁3]
  have hp : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hq : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq
  · exfalso
    have e := hk 1
    rw [show (i * 1) % 3 = 0 by omega, show (j * 1) % 3 = 0 by omega] at e
    simp at e
    exact ha1 e
  · right; left
    refine Subgroup.mem_zpowers_iff.2 ⟨1, ?_⟩
    have e := hk 1
    rw [show (i * 1) % 3 = 0 by omega, show (j * 1) % 3 = 1 by omega] at e
    simpa using e
  · right; left
    refine Subgroup.mem_zpowers_iff.2 ⟨2, ?_⟩
    have e := hk 2
    rw [show (i * 2) % 3 = 0 by omega, show (j * 2) % 3 = 1 by omega] at e
    simpa using e
  · left
    refine Subgroup.mem_zpowers_iff.2 ⟨1, ?_⟩
    have e := hk 1
    rw [show (i * 1) % 3 = 1 by omega, show (j * 1) % 3 = 0 by omega] at e
    simpa using e
  · right; right; left
    refine Subgroup.mem_zpowers_iff.2 ⟨1, ?_⟩
    have e := hk 1
    rw [show (i * 1) % 3 = 1 by omega, show (j * 1) % 3 = 1 by omega] at e
    simpa using e
  · right; right; right
    refine Subgroup.mem_zpowers_iff.2 ⟨1, ?_⟩
    have e := hk 1
    rw [show (i * 1) % 3 = 1 by omega, show (j * 1) % 3 = 2 by omega] at e
    simpa using e
  · left
    refine Subgroup.mem_zpowers_iff.2 ⟨2, ?_⟩
    have e := hk 2
    rw [show (i * 2) % 3 = 1 by omega, show (j * 2) % 3 = 0 by omega] at e
    simpa using e
  · right; right; right
    refine Subgroup.mem_zpowers_iff.2 ⟨2, ?_⟩
    have e := hk 2
    rw [show (i * 2) % 3 = 1 by omega, show (j * 2) % 3 = 2 by omega] at e
    simpa using e
  · right; right; left
    refine Subgroup.mem_zpowers_iff.2 ⟨2, ?_⟩
    have e := hk 2
    rw [show (i * 2) % 3 = 1 by omega, show (j * 2) % 3 = 1 by omega] at e
    simpa using e

theorem cen_le_of_mem_zpowers {a x : G} (hx : x ∈ Subgroup.zpowers a) : Cen a ≤ Cen x := by
  intro c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have : Commute c a := Subgroup.mem_centralizer_singleton_iff.1 hc
  exact Subgroup.mem_centralizer_singleton_iff.2 (this.zpow_right k).eq

theorem nor_Op {p : ℕ} [Fact p.Prime] {H : Subgroup G} {g : G} (hg : g ∈ H) :
    g ∈ Nor (Op p H) := by
  rw [Nor, Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => FF79.L41.Op_conj_mem hg hz, fun hz => ?_⟩
  have := FF79.L41.Op_conj_mem (inv_mem hg) hz
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at this

theorem comm_of_odd_normal {β : G} {N V X : Subgroup G} (hXN : X ≤ N)
    (hN : ∀ c ∈ Cen β, ∀ y ∈ N, c * y * c⁻¹ ∈ N) (hNodd : Odd (Nat.card N))
    (hV : IsPGroup 2 V) (hXV : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) :
    ∀ v ∈ V ⊓ Cen β, ∀ x ∈ X, v * x = x * v := by
  intro v hv x hx
  obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.1 hv
  have huN : v * x * v⁻¹ * x⁻¹ ∈ N := mul_mem (hN v hvC x (hXN hx)) (inv_mem (hXN hx))
  have huV : v * x * v⁻¹ * x⁻¹ ∈ V := by
    have := mul_mem hvV (hXV x hx v⁻¹ (inv_mem hvV))
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hV ⟨_, huV⟩
  have hk' : (v * x * v⁻¹ * x⁻¹) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf (v * x * v⁻¹ * x⁻¹) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf (v * x * v⁻¹ * x⁻¹) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N huN
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun hd => by
      have := Nat.odd_iff.1 hNodd
      omega
  have h3 : orderOf (v * x * v⁻¹ * x⁻¹) ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  have e : v * x * v⁻¹ * x⁻¹ = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have e' : v * x * v⁻¹ = x := mul_inv_eq_one.1 e
  calc v * x = (v * x * v⁻¹) * v := by group
    _ = x * v := by rw [e']

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
