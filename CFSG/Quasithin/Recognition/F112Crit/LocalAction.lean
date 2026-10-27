module

public import CFSG.Quasithin.Recognition.F112Crit.NormalPrimeAction
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ : Subgroup G}

structure IsLocalReg (δ : CosetGeom G₀ G₁ G₂) (p : ℕ) (X : Subgroup G) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  ker_le : ballStab 1 δ ≤ X
  le_stab : X ≤ stab δ
  normal : stab δ ≤ Subgroup.normalizer (X : Set G)
  relIndex_eq : (ballStab 1 δ).relIndex X = p
  inf_le : ∀ γ ∈ nbrs δ, X ⊓ stab γ ≤ ballStab 1 δ
  trans : ∀ γ ∈ nbrs δ, ∀ γ' ∈ nbrs δ, ∃ g : ↥G₀, (g : G) ∈ X ∧ g • γ = γ'
  exists_mem : ∀ γ ∈ nbrs δ, ∃ s ∈ stab δ ⊓ stab γ, s ∉ ballStab 1 δ

abbrev LocalQuot (δ : CosetGeom G₀ G₁ G₂) : Type _ :=
  ↥(stab δ) ⧸ (ballStab 1 δ).subgroupOf (stab δ)

instance instNormalKerSubgroupOf (δ : CosetGeom G₀ G₁ G₂) :
    ((ballStab 1 δ).subgroupOf (stab δ)).Normal :=
  (CosetGeom.ballStab_normal 1 δ).2

@[expose] noncomputable def localMk (δ : CosetGeom G₀ G₁ G₂) : ↥(stab δ) →* LocalQuot δ := QuotientGroup.mk' _

theorem localMk_eq_one_iff {δ : CosetGeom G₀ G₁ G₂} {g : ↥(stab δ)} :
    localMk δ g = 1 ↔ (g : G) ∈ ballStab 1 δ := by
  unfold localMk
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

namespace IsLocalReg

variable {δ : CosetGeom G₀ G₁ G₂} {p : ℕ} {X : Subgroup G}

theorem ker_le_stab_of_mem_nbrs {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ) :
    ballStab 1 δ ≤ stab γ :=
  CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hγ).le

theorem exists_not_mem (h : IsLocalReg δ p X) : ∃ x ∈ X, x ∉ ballStab 1 δ := by
  by_contra hcon
  push Not at hcon
  have h1 : (ballStab 1 δ).relIndex X = 1 := Subgroup.relIndex_eq_one.mpr hcon
  rw [h.relIndex_eq] at h1
  exact h.prime.one_lt.ne' h1

theorem X_le_sup_zpowers (h : IsLocalReg δ p X) {x : G} (hx : x ∈ X) (hxN : x ∉ ballStab 1 δ) :
    X ≤ ballStab 1 δ ⊔ Subgroup.zpowers x := by
  have hK : ballStab 1 δ ⊔ Subgroup.zpowers x ≤ X :=
    sup_le h.ker_le ((Subgroup.zpowers_le).mpr hx)
  have h1 := Subgroup.relIndex_mul_relIndex (ballStab 1 δ) (ballStab 1 δ ⊔ Subgroup.zpowers x) X
    le_sup_left hK
  rw [h.relIndex_eq] at h1
  rcases (Nat.dvd_prime h.prime).mp (Dvd.intro _ h1) with h2 | h2
  · exfalso
    exact hxN (Subgroup.relIndex_eq_one.mp h2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  · rw [h2] at h1
    have h3 : (ballStab 1 δ ⊔ Subgroup.zpowers x).relIndex X = 1 :=
      Nat.eq_of_mul_eq_mul_left h.prime.pos (by rw [h1, mul_one])
    exact Subgroup.relIndex_eq_one.mp h3

theorem pow_mem_ker (h : IsLocalReg δ p X) {x : G} (hx : x ∈ X) : x ^ p ∈ ballStab 1 δ := by
  haveI : ((ballStab 1 δ).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.ker_le).mpr
      (h.le_stab.trans (CosetGeom.le_normalizer_ballStab 1 δ))
  have hcard : Nat.card (↥X ⧸ (ballStab 1 δ).subgroupOf X) = p := h.relIndex_eq
  have h1 := pow_card_eq_one' (G := ↥X ⧸ (ballStab 1 δ).subgroupOf X)
    (x := QuotientGroup.mk ⟨x, hx⟩)
  rw [hcard, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem normalizes_ker (h : IsLocalReg δ p X) {g : G} (hg : g ∈ stab δ) {n : G}
    (hn : n ∈ ballStab 1 δ) : g * n * g⁻¹ ∈ ballStab 1 δ :=
  (Subgroup.mem_normalizer_iff.mp (CosetGeom.le_normalizer_ballStab 1 δ hg) n).mp hn

theorem normalizes_X (h : IsLocalReg δ p X) {g : G} (hg : g ∈ stab δ) {x : G} (hx : x ∈ X) :
    g * x * g⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.mp (h.normal hg) x).mp hx

variable (hG : G₀ = G₁ ⊔ G₂)

include hG in
theorem exists_mul (h : IsLocalReg δ p X) {g : G} (hg : g ∈ stab δ) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : γ ∈ nbrs δ) : ∃ x ∈ X, ∃ m ∈ stab δ ⊓ stab γ, g = x * m := by
  have hg0 : g ∈ G₀ := CosetGeom.stab_le δ hg
  set g' : ↥G₀ := ⟨g, hg0⟩ with hg'
  have hδ : g' • δ = δ := CosetGeom.smul_eq_of_mem_stab (g := g') hg
  have hγ' : g' • γ ∈ nbrs δ := by
    have := (CosetGeom.smul_adj g').mpr (show (graph G₀ G₁ G₂).Adj δ γ from hγ)
    rwa [hδ] at this
  obtain ⟨a, haX, ha⟩ := h.trans γ hγ (g' • γ) hγ'
  have hm : (a⁻¹ * g' : ↥G₀) • γ = γ := by
    rw [mul_smul, ← ha, inv_smul_smul]
  have hmstab : ((a⁻¹ * g' : ↥G₀) : G) ∈ stab γ := CosetGeom.mem_stab_of_smul_eq hm
  have hmδ : ((a⁻¹ * g' : ↥G₀) : G) ∈ stab δ := by
    have : ((a⁻¹ * g' : ↥G₀) : G) = (a : G)⁻¹ * g := rfl
    rw [this]
    exact (stab δ).mul_mem ((stab δ).inv_mem (h.le_stab haX)) hg
  refine ⟨a, haX, ((a⁻¹ * g' : ↥G₀) : G), ⟨hmδ, hmstab⟩, ?_⟩
  show g = (a : G) * ((a : G)⁻¹ * g)
  group

include hG in
theorem mem_ker_of_commutes (h : IsLocalReg δ p X) {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ)
    {s : G} (hs : s ∈ stab δ ⊓ stab γ)
    (hc : ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ ballStab 1 δ) : s ∈ ballStab 1 δ := by
  rw [CosetGeom.mem_ballStab]
  intro δ' hδ'
  rcases (CosetGeom.dist_le_one_iff hG).mp hδ' with rfl | hadj
  · exact hs.1
  · obtain ⟨g, hgX, hg⟩ := h.trans γ hγ δ' hadj
    rw [← hg, CosetGeom.stab_smul, mem_conjSub]
    have hn := hc (g : G) hgX
    have hgH : (g : G) ∈ stab δ := h.le_stab hgX
    have hn' : (g : G)⁻¹ * (s * (g : G) * s⁻¹ * (g : G)⁻¹) * (g : G) ∈ ballStab 1 δ := by
      have := h.normalizes_ker ((stab δ).inv_mem hgH) hn
      simpa using this
    have e : (g : G)⁻¹ * s * (g : G) =
        ((g : G)⁻¹ * (s * (g : G) * s⁻¹ * (g : G)⁻¹) * (g : G)) * s := by group
    rw [e]
    exact (stab γ).mul_mem (ker_le_stab_of_mem_nbrs hγ hn') hs.2

theorem exists_gen (h : IsLocalReg δ p X) :
    ∃ x₀ : G, ∃ hx₀ : x₀ ∈ stab δ, x₀ ∈ X ∧ x₀ ∉ ballStab 1 δ ∧
      orderOf (localMk δ ⟨x₀, hx₀⟩) = p ∧
      ∀ x ∈ X, ∃ j : ℤ, ∃ hx : x ∈ stab δ, localMk δ ⟨x, hx⟩ = localMk δ ⟨x₀, hx₀⟩ ^ j := by
  obtain ⟨x₀, hx₀X, hx₀N⟩ := h.exists_not_mem
  have hx₀H : x₀ ∈ stab δ := h.le_stab hx₀X
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hpow : localMk δ ⟨x₀, hx₀H⟩ ^ p = 1 := by
    rw [← map_pow, localMk_eq_one_iff]
    exact h.pow_mem_ker hx₀X
  have hne : localMk δ ⟨x₀, hx₀H⟩ ≠ 1 := by
    rw [Ne, localMk_eq_one_iff]; exact hx₀N
  refine ⟨x₀, hx₀H, hx₀X, hx₀N, orderOf_eq_prime hpow hne, fun x hx => ?_⟩
  have hnorm : Subgroup.zpowers x₀ ≤ Subgroup.normalizer (ballStab 1 δ : Set G) :=
    (Subgroup.zpowers_le).mpr (CosetGeom.le_normalizer_ballStab 1 δ hx₀H)
  have hmem := h.X_le_sup_zpowers hx₀X hx₀N hx
  obtain ⟨n, hn, y, hy, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hmem
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hyH : x₀ ^ j ∈ stab δ := (stab δ).zpow_mem hx₀H j
  have hnH : n ∈ stab δ := CosetGeom.ballStab_le_stab 1 δ hn
  refine ⟨j, (stab δ).mul_mem hnH hyH, ?_⟩
  have e : (⟨n * x₀ ^ j, (stab δ).mul_mem hnH hyH⟩ : ↥(stab δ)) =
      ⟨n, hnH⟩ * ⟨x₀, hx₀H⟩ ^ j := by
    apply Subtype.ext; simp
  rw [e, map_mul, map_zpow]
  have : localMk δ ⟨n, hnH⟩ = 1 := localMk_eq_one_iff.mpr hn
  rw [this, one_mul]

theorem cent_or_inv_quot (h : IsLocalReg δ p X) {s : G} (hs : s ∈ stab δ)
    (hss : s * s ∈ ballStab 1 δ) :
    (∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ ballStab 1 δ) ∨ (∀ x ∈ X, s * x * s⁻¹ * x ∈ ballStab 1 δ) := by
  obtain ⟨x₀, hx₀H, hx₀X, hx₀N, hord, hgen⟩ := h.exists_gen
  set c₀ := localMk δ ⟨x₀, hx₀H⟩ with hc₀
  set ŝ := localMk δ ⟨s, hs⟩ with hŝ
  have hŝ2 : ŝ * ŝ = 1 := by
    rw [← map_mul, localMk_eq_one_iff]; exact hss
  obtain ⟨j₀, hsx, hj₀⟩ := hgen (s * x₀ * s⁻¹) (h.normalizes_X hs hx₀X)
  have hconj : ŝ * c₀ * ŝ⁻¹ = c₀ ^ j₀ := by
    rw [← hj₀, hŝ, hc₀, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  rcases NormalPrimeAction.cent_or_inv h.prime hord hconj hŝ2 with hc | hc
  · left
    intro x hx
    obtain ⟨j, hxH, hj⟩ := hgen x hx
    have hsxH : s * x * s⁻¹ * x⁻¹ ∈ stab δ :=
      (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).mul_mem hs hxH) ((stab δ).inv_mem hs))
        ((stab δ).inv_mem hxH)
    have : localMk δ ⟨s * x * s⁻¹ * x⁻¹, hsxH⟩ = 1 := by
      have e : (⟨s * x * s⁻¹ * x⁻¹, hsxH⟩ : ↥(stab δ)) =
          ⟨s, hs⟩ * ⟨x, hxH⟩ * ⟨s, hs⟩⁻¹ * ⟨x, hxH⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hj, ← hŝ, ← conj_zpow, hc]
      group
    exact localMk_eq_one_iff.mp this
  · right
    intro x hx
    obtain ⟨j, hxH, hj⟩ := hgen x hx
    have hsxH : s * x * s⁻¹ * x ∈ stab δ :=
      (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).mul_mem hs hxH) ((stab δ).inv_mem hs)) hxH
    have : localMk δ ⟨s * x * s⁻¹ * x, hsxH⟩ = 1 := by
      have e : (⟨s * x * s⁻¹ * x, hsxH⟩ : ↥(stab δ)) =
          ⟨s, hs⟩ * ⟨x, hxH⟩ * ⟨s, hs⟩⁻¹ * ⟨x, hxH⟩ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, hj, ← hŝ, ← conj_zpow, hc, inv_zpow]
      group
    exact localMk_eq_one_iff.mp this

theorem pow_pred_trivial (h : IsLocalReg δ p X) {s : G} (hs : s ∈ stab δ) :
    ∀ x ∈ X, s ^ (p - 1) * x * (s ^ (p - 1))⁻¹ * x⁻¹ ∈ ballStab 1 δ := by
  obtain ⟨x₀, hx₀H, hx₀X, hx₀N, hord, hgen⟩ := h.exists_gen
  set c₀ := localMk δ ⟨x₀, hx₀H⟩ with hc₀
  set ŝ := localMk δ ⟨s, hs⟩ with hŝ
  obtain ⟨j₀, hsx, hj₀⟩ := hgen (s * x₀ * s⁻¹) (h.normalizes_X hs hx₀X)
  have hconj : ŝ * c₀ * ŝ⁻¹ = c₀ ^ j₀ := by
    rw [← hj₀, hŝ, hc₀, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hc := NormalPrimeAction.pow_pred_cent h.prime hord hconj
  intro x hx
  obtain ⟨j, hxH, hj⟩ := hgen x hx
  have hsH : s ^ (p - 1) ∈ stab δ := (stab δ).pow_mem hs _
  have hsxH : s ^ (p - 1) * x * (s ^ (p - 1))⁻¹ * x⁻¹ ∈ stab δ :=
    (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).mul_mem hsH hxH) ((stab δ).inv_mem hsH))
      ((stab δ).inv_mem hxH)
  have : localMk δ ⟨s ^ (p - 1) * x * (s ^ (p - 1))⁻¹ * x⁻¹, hsxH⟩ = 1 := by
    have e : (⟨s ^ (p - 1) * x * (s ^ (p - 1))⁻¹ * x⁻¹, hsxH⟩ : ↥(stab δ)) =
        ⟨s, hs⟩ ^ (p - 1) * ⟨x, hxH⟩ * (⟨s, hs⟩ ^ (p - 1))⁻¹ * ⟨x, hxH⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hj, ← hŝ, ← conj_zpow, hc]
    group
  exact localMk_eq_one_iff.mp this

theorem ker_le_stab_inf (h : IsLocalReg δ p X) {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ) :
    ballStab 1 δ ≤ stab δ ⊓ stab γ :=
  le_inf (CosetGeom.ballStab_le_stab 1 δ) (ker_le_stab_of_mem_nbrs hγ)

include hG in
theorem mem_ker_or_inv (h : IsLocalReg δ p X) {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ)
    {s : G} (hs : s ∈ stab δ ⊓ stab γ) (hss : s * s ∈ ballStab 1 δ) :
    s ∈ ballStab 1 δ ∨ ∀ x ∈ X, s * x * s⁻¹ * x ∈ ballStab 1 δ := by
  rcases h.cent_or_inv_quot hs.1 hss with hc | hi
  · exact Or.inl (h.mem_ker_of_commutes hG hγ hs hc)
  · exact Or.inr hi

include hG in
theorem pow_pred_mem (h : IsLocalReg δ p X) {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ) {s : G}
    (hs : s ∈ stab δ ⊓ stab γ) : s ^ (p - 1) ∈ ballStab 1 δ :=
  h.mem_ker_of_commutes hG hγ ⟨(stab δ).pow_mem hs.1 _, (stab γ).pow_mem hs.2 _⟩
    (h.pow_pred_trivial hs.1)

theorem mul_centralizes_of_inv (h : IsLocalReg δ p X) {e e' : G} (he : e ∈ stab δ)
    (he' : e' ∈ stab δ) (h1 : ∀ x ∈ X, e * x * e⁻¹ * x ∈ ballStab 1 δ)
    (h2 : ∀ x ∈ X, e' * x * e'⁻¹ * x ∈ ballStab 1 δ) :
    ∀ x ∈ X, (e * e') * x * (e * e')⁻¹ * x⁻¹ ∈ ballStab 1 δ := by
  intro x hx
  have e1 : (e * e') * x * (e * e')⁻¹ * x⁻¹ =
      (e * (e' * x * e'⁻¹ * x) * e⁻¹) * (x * (e * x * e⁻¹ * x)⁻¹ * x⁻¹) := by group
  rw [e1]
  refine Subgroup.mul_mem _ (h.normalizes_ker he (h2 x hx)) ?_
  have hxs : x ∈ stab δ := h.le_stab hx
  have := h.normalizes_ker hxs ((ballStab 1 δ).inv_mem (h1 x hx))
  simpa [mul_assoc] using this

include hG in
theorem mul_mem_ker (h : IsLocalReg δ p X) {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ) {e e' : G}
    (he : e ∈ stab δ ⊓ stab γ) (he' : e' ∈ stab δ ⊓ stab γ) (hee : e * e ∈ ballStab 1 δ)
    (hee' : e' * e' ∈ ballStab 1 δ) (hne : e ∉ ballStab 1 δ) (hne' : e' ∉ ballStab 1 δ) :
    e * e' ∈ ballStab 1 δ := by
  have h1 := (h.mem_ker_or_inv hG hγ he hee).resolve_left hne
  have h2 := (h.mem_ker_or_inv hG hγ he' hee').resolve_left hne'
  exact h.mem_ker_of_commutes hG hγ ⟨(stab δ).mul_mem he.1 he'.1, (stab γ).mul_mem he.2 he'.2⟩
    (h.mul_centralizes_of_inv he.1 he'.1 h1 h2)

include hG in
theorem le_sup_zpowers (h : IsLocalReg δ p X) {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ) {x : G}
    (hx : x ∈ X) (hxN : x ∉ ballStab 1 δ) :
    stab δ ≤ (stab δ ⊓ stab γ) ⊔ Subgroup.zpowers x := by
  intro g hg
  obtain ⟨a, haX, m, hm, rfl⟩ := h.exists_mul hG hg hγ
  have ha : a ∈ (stab δ ⊓ stab γ) ⊔ Subgroup.zpowers x :=
    sup_le_sup_right (h.ker_le_stab_inf hγ) _ (h.X_le_sup_zpowers hx hxN haX)
  exact Subgroup.mul_mem _ ha (Subgroup.mem_sup_left hm)

theorem exists_pow_mul (h : IsLocalReg δ p X) {x : G} (hx : x ∈ X) (hxN : x ∉ ballStab 1 δ) {a : G}
    (ha : a ∈ X) : ∃ r < p, ∃ n ∈ ballStab 1 δ, a = x ^ r * n := by
  have hxH : x ∈ stab δ := h.le_stab hx
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (ballStab 1 δ : Set G) :=
    (Subgroup.zpowers_le).mpr (CosetGeom.le_normalizer_ballStab 1 δ hxH)
  obtain ⟨n, hn, y, hy, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp (h.X_le_sup_zpowers hx hxN ha)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hp0 : (0 : ℤ) < p := by exact_mod_cast h.prime.pos
  obtain ⟨q, r, hr, hkqr⟩ : ∃ q : ℤ, ∃ r : ℕ, r < p ∧ k = r + p * q := by
    refine ⟨k / p, (k % p).toNat, ?_, ?_⟩
    · have h1 := Int.emod_lt_of_pos k hp0
      have h2 := Int.emod_nonneg k hp0.ne'
      omega
    · have h1 := Int.emod_add_mul_ediv k p
      have h2 := Int.emod_nonneg k hp0.ne'
      omega
  subst hkqr
  have hk : x ^ ((r : ℤ) + p * q) = x ^ r * (x ^ p) ^ q := by
    rw [zpow_add, zpow_natCast, zpow_mul, zpow_natCast]
  refine ⟨r, hr, (x ^ r)⁻¹ * n * x ^ r * (x ^ p) ^ q, ?_, ?_⟩
  · refine Subgroup.mul_mem _ ?_ (Subgroup.zpow_mem _ (h.pow_mem_ker hx) _)
    have := h.normalizes_ker (g := (x ^ r)⁻¹) ((stab δ).inv_mem ((stab δ).pow_mem hxH _)) hn
    simpa using this
  · rw [hk]; group

theorem exists_pow_smul_eq (h : IsLocalReg δ p X) {γ μ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ)
    (hμ : μ ∈ nbrs δ) {x : G} (hx : x ∈ X) (hxN : x ∉ ballStab 1 δ) :
    ∃ r < p, ∃ g : ↥G₀, (g : G) = x ^ r ∧ g • γ = μ := by
  obtain ⟨a, haX, ha⟩ := h.trans γ hγ μ hμ
  obtain ⟨r, hr, n, hn, han⟩ := h.exists_pow_mul hx hxN haX
  have hxr : x ^ r ∈ G₀ := G₀.pow_mem (CosetGeom.stab_le δ (h.le_stab hx)) r
  have hnG : n ∈ G₀ := CosetGeom.stab_le δ (CosetGeom.ballStab_le_stab 1 δ hn)
  refine ⟨r, hr, ⟨x ^ r, hxr⟩, rfl, ?_⟩
  rw [← ha]
  have h1 : a = (⟨x ^ r, hxr⟩ : ↥G₀) * ⟨n, hnG⟩ := Subtype.ext han
  rw [h1, mul_smul, CosetGeom.smul_eq_of_mem_stab (g := ⟨n, hnG⟩) (ker_le_stab_of_mem_nbrs hγ hn)]

theorem smul_mem_nbrs {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ) {g : ↥G₀}
    (hg : (g : G) ∈ stab δ) : g • γ ∈ nbrs δ := by
  have hδ : g • δ = δ := CosetGeom.smul_eq_of_mem_stab hg
  have := (CosetGeom.smul_adj g).mpr (show (graph G₀ G₁ G₂).Adj δ γ from hγ)
  rwa [hδ] at this

theorem card_conjSub_eq (g : G) (H : Subgroup G) : Nat.card (conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem relIndex_conjSub_eq (g : G) (H K : Subgroup G) :
    (conjSub g H).relIndex (conjSub g K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective H K (MulAut.conj g).injective

theorem smul (g : ↥G₀) (h : IsLocalReg δ p X) : IsLocalReg (g • δ) p (conjSub (g : G) X) where
  prime := h.prime
  ne_two := h.ne_two
  ker_le := by
    rw [CosetGeom.ballStab_smul]
    exact conjSub_mono _ h.ker_le
  le_stab := by
    rw [CosetGeom.stab_smul]
    exact conjSub_mono _ h.le_stab
  normal := by
    rw [CosetGeom.stab_smul]
    exact conjSub_le_normalizer h.normal
  relIndex_eq := by
    rw [CosetGeom.ballStab_smul, relIndex_conjSub_eq]
    exact h.relIndex_eq
  inf_le := by
    intro γ hγ
    obtain ⟨γ', rfl⟩ : ∃ γ', γ = g • γ' := ⟨g⁻¹ • γ, by simp⟩
    have hγ' : γ' ∈ nbrs δ := (CosetGeom.smul_adj g).mp hγ
    rw [CosetGeom.stab_smul, CosetGeom.ballStab_smul, ← conjSub_inf]
    exact conjSub_mono _ (h.inf_le γ' hγ')
  trans := by
    intro γ hγ γ'' hγ''
    obtain ⟨a, rfl⟩ : ∃ a, γ = g • a := ⟨g⁻¹ • γ, by simp⟩
    obtain ⟨b, rfl⟩ : ∃ b, γ'' = g • b := ⟨g⁻¹ • γ'', by simp⟩
    have ha : a ∈ nbrs δ := (CosetGeom.smul_adj g).mp hγ
    have hb : b ∈ nbrs δ := (CosetGeom.smul_adj g).mp hγ''
    obtain ⟨x, hxX, hx⟩ := h.trans a ha b hb
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · show (g : G) * (x : G) * (g : G)⁻¹ ∈ conjSub (g : G) X
      rw [mem_conjSub]
      have e : (g : G)⁻¹ * ((g : G) * (x : G) * (g : G)⁻¹) * (g : G) = (x : G) := by group
      rw [e]
      exact hxX
    · rw [mul_smul, mul_smul, inv_smul_smul, hx]
  exists_mem := by
    intro γ hγ
    obtain ⟨γ', rfl⟩ : ∃ γ', γ = g • γ' := ⟨g⁻¹ • γ, by simp⟩
    have hγ' : γ' ∈ nbrs δ := (CosetGeom.smul_adj g).mp hγ
    obtain ⟨s, hs, hsN⟩ := h.exists_mem γ' hγ'
    have e : (g : G)⁻¹ * ((g : G) * s * (g : G)⁻¹) * (g : G) = s := by group
    refine ⟨(g : G) * s * (g : G)⁻¹, ?_, ?_⟩
    · rw [CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf, mem_conjSub, e]
      exact hs
    · rw [CosetGeom.ballStab_smul, mem_conjSub, e]
      exact hsN

end IsLocalReg

theorem exists_isLocalReg_of_vtype {p : ℕ} {X₁ : Subgroup G}
    (h : IsLocalReg (γ₁ G₀ G₁ G₂) p X₁) {δ : CosetGeom G₀ G₁ G₂} (hδ : vtype δ = true) :
    ∃ X, IsLocalReg δ p X := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hδ
  exact ⟨_, h.smul g⟩

end CFSG.Quasithin.F112Crit
