module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simp only [conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩

theorem card_conjugate (H : Subgroup G) (g : G) : Nat.card (conjugate H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem mem_normalizer_of_forward {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (h' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    g ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  simpa [mul_assoc] using h' _ hx

theorem mem_normalizer_inf {V W : Subgroup G} {g : G} (hV : g ∈ normalizer (V : Set G))
    (hW : g ∈ normalizer (W : Set G)) : g ∈ normalizer ((V ⊓ W : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hV hW ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hV x, hW x]

theorem mem_normalizer_centralizer {Y : Subgroup G} {g : G} (hg : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer ((centralizer (Y : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (Y : Set G) →
      ∀ x ∈ centralizer (Y : Set G), g * x * g⁻¹ ∈ centralizer (Y : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have h1 : g⁻¹ * y * g ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
      simpa using this
    have h2 := hx _ h1
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h2]
      _ = g * x * g⁻¹ * y := by group
  exact mem_normalizer_of_forward (key g hg) (fun x hx => by
    simpa using key g⁻¹ (Subgroup.inv_mem _ hg) x hx)

theorem mem_normalizer_commutator {V W : Subgroup G} {g : G} (hV : g ∈ normalizer (V : Set G))
    (hW : g ∈ normalizer (W : Set G)) : g ∈ normalizer ((⁅V, W⁆ : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (V : Set G) → g ∈ normalizer (W : Set G) →
      ∀ x ∈ ⁅V, W⁆, g * x * g⁻¹ ∈ ⁅V, W⁆ := by
    intro g hV hW x hx
    have hle : ⁅V, W⁆ ≤ (⁅V, W⁆).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro v hv w hw
      show g * ⁅v, w⁆ * g⁻¹ ∈ ⁅V, W⁆
      rw [conjugate_commutatorElement]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hV v).mp hv)
        ((Subgroup.mem_normalizer_iff.mp hW w).mp hw)
    exact hle hx
  exact mem_normalizer_of_forward (key g hV hW) (fun x hx => by
    simpa using key g⁻¹ (Subgroup.inv_mem _ hV) (Subgroup.inv_mem _ hW) x hx)

theorem mem_normalizer_sup {U E : Subgroup G} {g : G} (hU : g ∈ normalizer (U : Set G))
    (hE : g ∈ normalizer (E : Set G)) : g ∈ normalizer ((U ⊔ E : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (U : Set G) → g ∈ normalizer (E : Set G) →
      ∀ x ∈ U ⊔ E, g * x * g⁻¹ ∈ U ⊔ E := by
    intro g hU hE x hx
    have hle : U ⊔ E ≤ (U ⊔ E).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun u hu => ?_) (fun e he => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hU u).mp hu)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hE e).mp he)
    exact hle hx
  exact mem_normalizer_of_forward (key g hU hE) (fun x hx => by
    simpa using key g⁻¹ (Subgroup.inv_mem _ hU) (Subgroup.inv_mem _ hE) x hx)

theorem commutator_inv_mem_centralizer_zpowers {x₀ g h : G}
    (hg : g ∈ normalizer ((zpowers x₀ : Subgroup G) : Set G))
    (hh : h ∈ normalizer ((zpowers x₀ : Subgroup G) : Set G)) :
    ⁅g⁻¹, h⁻¹⁆ ∈ centralizer ((zpowers x₀ : Subgroup G) : Set G) := by
  have hconj : ∀ k : G, k ∈ normalizer ((zpowers x₀ : Subgroup G) : Set G) →
      ∃ i : ℤ, k * x₀ * k⁻¹ = x₀ ^ i := by
    intro k hk
    have := (Subgroup.mem_normalizer_iff.mp hk x₀).mp (Subgroup.mem_zpowers x₀)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp this
    exact ⟨i, hi.symm⟩
  obtain ⟨i, hi⟩ := hconj g hg
  obtain ⟨j, hj⟩ := hconj h hh
  have e1 : (g * h) * x₀ * (g * h)⁻¹ = x₀ ^ (i * j) := by
    have : (g * h) * x₀ * (g * h)⁻¹ = g * (h * x₀ * h⁻¹) * g⁻¹ := by group
    rw [this, hj, ← conj_zpow, hi, ← zpow_mul]
  have e2 : (h * g) * x₀ * (h * g)⁻¹ = x₀ ^ (j * i) := by
    have : (h * g) * x₀ * (h * g)⁻¹ = h * (g * x₀ * g⁻¹) * h⁻¹ := by group
    rw [this, hi, ← conj_zpow, hj, ← zpow_mul]
  have key : (h * g)⁻¹ * (g * h) * x₀ = x₀ * ((h * g)⁻¹ * (g * h)) := by
    calc (h * g)⁻¹ * (g * h) * x₀ = (h * g)⁻¹ * ((g * h) * x₀ * (g * h)⁻¹) * (g * h) := by group
      _ = (h * g)⁻¹ * ((h * g) * x₀ * (h * g)⁻¹) * (g * h) := by rw [e1, e2, mul_comm i j]
      _ = x₀ * ((h * g)⁻¹ * (g * h)) := by group
  have hcomm : Commute x₀ ((h * g)⁻¹ * (g * h)) := key.symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have : ⁅g⁻¹, h⁻¹⁆ = (h * g)⁻¹ * (g * h) := by
    rw [commutatorElement_def]
    group
  rw [this]
  exact ((hcomm.zpow_left k).eq)

theorem commutator_mem_centralizer_zpowers {x₀ g h : G}
    (hg : g ∈ normalizer ((zpowers x₀ : Subgroup G) : Set G))
    (hh : h ∈ normalizer ((zpowers x₀ : Subgroup G) : Set G)) :
    ⁅g, h⁆ ∈ centralizer ((zpowers x₀ : Subgroup G) : Set G) := by
  have := commutator_inv_mem_centralizer_zpowers (Subgroup.inv_mem _ hg) (Subgroup.inv_mem _ hh)
  simpa using this

theorem commutator_le_centralizer_of_isCyclic {Φ R A : Subgroup G} (hΦ : IsCyclic Φ)
    (hR : R ≤ normalizer (Φ : Set G)) (hA : A ≤ normalizer (Φ : Set G)) :
    ⁅R, A⁆ ≤ centralizer (Φ : Set G) := by
  obtain ⟨x₀, rfl⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Φ).mp hΦ
  rw [Subgroup.commutator_le]
  intro r hr a ha
  exact commutator_mem_centralizer_zpowers (hR hr) (hA ha)

theorem mul_comm_of_inf_eq_bot {N₁ N₂ : Subgroup G} (h : N₁ ⊓ N₂ = ⊥) {x y : G} (hx : x ∈ N₁)
    (hy : y ∈ N₂) (hxN : x ∈ normalizer (N₂ : Set G)) (hyN : y ∈ normalizer (N₁ : Set G)) :
    x * y = y * x := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ N₂ :=
    N₂.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy) (N₂.inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ N₁ := by
    have h3 : x * y * x⁻¹ * y⁻¹ = x * (y * x * y⁻¹)⁻¹ := by group
    rw [h3]
    exact N₁.mul_mem hx (N₁.inv_mem ((Subgroup.mem_normalizer_iff.mp hyN x).mp hx))
  have h4 : x * y * x⁻¹ * y⁻¹ ∈ N₁ ⊓ N₂ := ⟨h2, h1⟩
  rw [h, Subgroup.mem_bot] at h4
  exact commutatorElement_eq_one_iff_mul_comm.mp h4

theorem inf_eq_bot_of_isPGroup {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {N₁ N₂ : Subgroup G} (h₁ : IsPGroup p N₁) (h₂ : IsPGroup r N₂) : N₁ ⊓ N₂ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  exact (IsPGroup.disjoint_of_ne p r hpr N₁ N₂ h₁ h₂).eq_bot

theorem mem_normalizer_zpowers_of_commute {c e : G} (h : e * c = c * e) :
    e ∈ normalizer ((zpowers c : Subgroup G) : Set G) := by
  refine centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_left (show Commute c e from h.symm) k).eq

theorem commutator_mem_of_mem_normalizer {T : Subgroup G} {x w : G}
    (hx : x ∈ normalizer (T : Set G)) (hw : w ∈ T) : ⁅x, w⁆ ∈ T :=
  T.mul_mem ((Subgroup.mem_normalizer_iff.mp hx w).mp hw) (T.inv_mem hw)

theorem commutator_le_of_le_normalizer {T X W : Subgroup G} (hX : X ≤ normalizer (T : Set G))
    (hW : W ≤ T) : ⁅X, W⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro x hx w hw
  exact commutator_mem_of_mem_normalizer (hX hx) (hW hw)

theorem center_eq_bot_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have : a ∈ center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem normalizer_ne_top_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {q : ℕ} (hq : q.Prime) {Y : Subgroup G}
    (hY : Nat.card Y = q) : normalizer (Y : Set G) ≠ ⊤ := by
  intro h
  have hn : Y.Normal := normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with hb | ht
  · rw [hb, Subgroup.card_bot] at hY
    exact hq.one_lt.ne hY
  · rw [ht, Subgroup.card_top] at hY
    have : Fact q.Prime := ⟨hq⟩
    have hcyc : IsCyclic G := isCyclic_of_prime_card hY
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)

end CFSG.RankThree.PartOne.Sec9Excl
