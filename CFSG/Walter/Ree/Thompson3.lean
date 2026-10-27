module

public import CFSG.Walter.Ree.Thompson3.Unique
public import CFSG.Walter.W67.RouteReeNative
import CFSG.Walter.Ree.Thompson3.ThompsonAut
import CFSG.Walter.Ree.Thompson3.FromBase
import CFSG.Walter.Ree.Hopkins.Thm26
import CFSG.Walter.Ree.Bombieri
import CFSG.Walter.Ree.Thompson1
import CFSG.Walter.Ree.Model.JTHyp

public section

namespace CFSG.Walter.Ree

open CFSG.Walter.Ward T2

namespace T2.RType

variable {k : Type} [Field k] [CharP k 3] [Fintype k] {σ : k ≃+* k} {d : k}
variable {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]

theorem nonempty_mulEquiv_of_isS
    (R₁ : RType G₁ k σ d) (R₂ : RType G₂ k σ d)
    {S : k → k × k × k} (hS₁ : IsS R₁ S) (hS₂ : IsS R₂ S) : Nonempty (G₁ ≃* G₂) := by
  obtain ⟨a, ha, haσ⟩ := R₁.exists_a'
  exact nonempty_mulEquiv R₁ R₂ hS₁ hS₂ ha haσ R₁.eq69 R₂.eq69

theorem nonempty_mulEquiv_of_eq211
    (h211 : ∀ a : ℕ, Even a → (∀ x : k, (σ x * x) ^ a = x ^ 2) → a < Fintype.card k - 1 →
      ∃ c : k → k → k → k, ∀ (d : k) (G : Type) [Group G] [Finite G] (R : RType G k σ d),
        Eq211 R a c)
    (hS : ∀ d : k, ∃ S : k → k × k × k,
      ∀ (G : Type) [Group G] [Finite G] (R : RType G k σ d), IsS R S)
    {d₁ d₂ : k} (R₁ : RType G₁ k σ d₁) (R₂ : RType G₂ k σ d₂) : Nonempty (G₁ ≃* G₂) := by
  obtain rfl : d₂ = d₁ := (Hopkins.d_unique_of_eq211 h211 R₁ R₂).symm
  obtain ⟨S, hS'⟩ := hS d₂
  exact nonempty_mulEquiv_of_isS R₁ R₂ (hS' G₁ R₁) (hS' G₂ R₂)

theorem nonempty_mulEquiv_of_rType
    {d₁ d₂ : k} (R₁ : RType G₁ k σ d₁) (R₂ : RType G₂ k σ d₂) :
    Nonempty (G₁ ≃* G₂) :=
  nonempty_mulEquiv_of_eq211
    (fun a ha haσ _ => ⟨Alg.c211 σ a, fun _ _ _ _ R => R.eq211_holds ha haσ⟩)
    (fun d => sExplicit_holds σ d) R₁ R₂

end T2.RType

theorem exists_rType
    (hbase : BaseExists) {k : Type} [Field k] [Fintype k] [CharP k 3] {n : ℕ}
    (hn : 1 ≤ n) (hk : Fintype.card k = 3 ^ (2 * n + 1)) {G : Type} [Group G] [Finite G]
    (h : ReeTypeHyp G) (hq : h.q = 3 ^ (2 * n + 1)) :
    ∃ σ : k ≃+* k, (∀ x, σ (σ x) = x ^ 3) ∧ ∃ d : k, Nonempty (RType G k σ d) := by
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hT := ward_thompsonIHyp h P
  rw [hq] at hT
  obtain ⟨σ, hgen, ⟨e⟩⟩ := thompson_I k n hn hk hT
  obtain ⟨d, ⟨R⟩⟩ := hbase k G h σ ⟨P, ⟨e⟩⟩
  exact ⟨σ, bombieri k n hn hk σ (R.isThompsonAut hk (odd_two_mul_add_one n) (by omega) hgen
    R.thompsonIdentity_holds), d, ⟨R⟩⟩

theorem reeType_unique
    (hbase : BaseExists) {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂]
    [Finite G₂] (h₁ : ReeTypeHyp G₁) (h₂ : ReeTypeHyp G₂) (hq : h₁.q = h₂.q) :
    Nonempty (G₁ ≃* G₂) := by
  obtain ⟨n, hn, hqn⟩ := (ward_order h₁).1
  let k := GaloisField 3 (2 * n + 1)
  let _ : Fintype k := Fintype.ofFinite k
  have hk : Fintype.card k = 3 ^ (2 * n + 1) := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card 3 _ (by omega)
  obtain ⟨σ₁, hσ₁, d₁, ⟨R₁⟩⟩ := exists_rType hbase hn hk h₁ hqn
  obtain ⟨σ₂, hσ₂, d₂, ⟨R₂⟩⟩ := exists_rType hbase hn hk h₂ (hq.symm.trans hqn)
  obtain rfl : σ₂ = σ₁ := RingEquiv.ext fun x => by
    rw [Hopkins.apply_eq_of_sq hn hk hσ₁, Hopkins.apply_eq_of_sq hn hk hσ₂]
  exact RType.nonempty_mulEquiv_of_rType R₁ R₂

theorem reeType_unique_of_thompson2
    (T2 : Thompson2) {G₁ G₂ : Type} [Group G₁] [Finite G₁]
    [Group G₂] [Finite G₂] (h₁ : ReeTypeHyp G₁) (h₂ : ReeTypeHyp G₂) (hq : h₁.q = h₂.q) :
    Nonempty (G₁ ≃* G₂) :=
  reeType_unique T2.base h₁ h₂ hq

theorem ree_order_lt {x y : ℕ} (hx : 2 ≤ x) (hxy : x < y) :
    x ^ 3 * (x ^ 3 + 1) * (x - 1) < y ^ 3 * (y ^ 3 + 1) * (y - 1) := by
  have h1 : x ^ 3 ≤ y ^ 3 := Nat.pow_le_pow_left hxy.le 3
  have h2 : x ^ 3 * (x ^ 3 + 1) ≤ y ^ 3 * (y ^ 3 + 1) := Nat.mul_le_mul h1 (by omega)
  have h3 : 0 < y ^ 3 * (y ^ 3 + 1) := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  calc x ^ 3 * (x ^ 3 + 1) * (x - 1) ≤ y ^ 3 * (y ^ 3 + 1) * (x - 1) :=
        Nat.mul_le_mul_right _ h2
    _ < y ^ 3 * (y ^ 3 + 1) * (y - 1) := (Nat.mul_lt_mul_left h3).2 (by omega)

theorem q_eq_of_card
    {G : Type} [Group G] [Finite G] (h : ReeTypeHyp G) {q : ℕ}
    (hq : 2 ≤ q) (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1)) : h.q = q := by
  have hG' := (ward_order h).2
  rw [hG] at hG'
  have h3 := h.three_le_q
  rcases lt_trichotomy h.q q with hlt | heq | hgt
  · exact absurd hG' (ree_order_lt (by omega) hlt).ne'
  · exact heq
  · exact absurd hG' (ree_order_lt hq hgt).ne

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree in
theorem reeIdentNative
    (hbase : BaseExists) : W67.ReeIdentNative := by
  intro G _ _ h
  obtain ⟨n, hn, hqn⟩ := (ward_order h).1
  let K := GaloisField 3 (2 * n + 1)
  have hK : Nat.card K = 3 ^ (2 * n + 1) := GaloisField.card 3 _ (by omega)
  have : CharP K ReeTag.G2.prime := (inferInstance : CharP K 3)
  obtain ⟨hΓ⟩ := Model.small_Ree_reeTypeHyp n hn K hK
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.G2.tag).length
  have hcard := (small_Ree_Borel_coset_Sylow_action n K hK w₀ hw₀).2.2.2.2.2.2.2.2.2.1
  have h2 : 2 ≤ 3 ^ (2 * n + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqΓ : hΓ.q = 3 ^ (2 * n + 1) := by
    refine q_eq_of_card hΓ h2 ?_
    rw [hcard, Nat.mul_right_comm]
  obtain ⟨e⟩ := reeType_unique hbase h hΓ (hqn.trans hqΓ.symm)
  exact ⟨n, K, inferInstance, inferInstance, inferInstance, hn, hK, hqn.trans hK.symm, ⟨e⟩⟩

theorem reeIdentNative_of_thompson2
    (T2 : Thompson2) : W67.ReeIdentNative :=
  reeIdentNative T2.base

end CFSG.Walter.Ree
