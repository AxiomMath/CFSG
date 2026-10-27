module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartOne.K1327.Trick
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.LocalCores
open scoped commutatorElement

variable {G : Type} [Group G]

theorem normalizes_of_component [Finite G] {Y X R : Subgroup G} (hXY : X ≤ Y)
    (hX : IsComponent (X.subgroupOf Y)) (hRX : R ≤ X) (hR1 : R ≠ ⊥)
    (hZ : Subgroup.center ↥X = ⊥) {v : G} (hv : v ∈ Y) (hvR : ∀ x ∈ R, v * x = x * v) :
    ∀ x ∈ X, v * x * v⁻¹ ∈ X := by
  set vY : ↥Y := ⟨v, hv⟩ with hvY
  set φ : ↥Y ≃* ↥Y := MulAut.conj vY with hφ
  have hX'' : IsComponent ((X.subgroupOf Y).map φ.toMonoidHom) :=
    isComponent_map_mulEquiv φ hX
  rcases distinct_components_commute hX hX'' with h | h
  · intro x hx
    have hx' : (⟨x, hXY hx⟩ : ↥Y) ∈ X.subgroupOf Y := hx
    have h2 : φ ⟨x, hXY hx⟩ ∈ (X.subgroupOf Y).map φ.toMonoidHom := ⟨_, hx', rfl⟩
    rw [← h] at h2
    exact h2
  · exfalso
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have hrX : r ∈ X := hRX hr
    have hr' : (⟨r, hXY hrX⟩ : ↥Y) ∈ X.subgroupOf Y := hrX
    have hr'' : (⟨r, hXY hrX⟩ : ↥Y) ∈ (X.subgroupOf Y).map φ.toMonoidHom := by
      refine ⟨⟨r, hXY hrX⟩, hr', ?_⟩
      apply Subtype.ext
      show v * r * v⁻¹ = r
      rw [hvR r hr]
      group
    have hcen : (⟨r, hrX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy' : (⟨(y : G), hXY y.2⟩ : ↥Y) ∈ X.subgroupOf Y := y.2
      have hc : ⁅(⟨(y : G), hXY y.2⟩ : ↥Y), (⟨r, hXY hrX⟩ : ↥Y)⁆ ∈
          ⁅X.subgroupOf Y, (X.subgroupOf Y).map φ.toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator hy' hr''
      rw [h, Subgroup.mem_bot] at hc
      have h5 : (⟨(y : G), hXY y.2⟩ : ↥Y) * ⟨r, hXY hrX⟩ = ⟨r, hXY hrX⟩ * ⟨(y : G), hXY y.2⟩ :=
        commutatorElement_eq_one_iff_mul_comm.1 hc
      have h6 : (y : G) * r = r * (y : G) := congrArg Subtype.val h5
      exact Subtype.ext h6
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen

theorem inf_eq_bot_of_solvable {J V K₀ : Subgroup G} (hK₀J : K₀ ≤ J)
    (hVJ : ∀ j ∈ J, ∀ v ∈ V, j * v * j⁻¹ ∈ V) (hVs : Group.IsSolvable ↥V)
    (hq : IsQuasisimple ↥K₀) (hz : Subgroup.center ↥K₀ = ⊥) : V ⊓ K₀ = ⊥ := by
  set N : Subgroup ↥K₀ := (V ⊓ K₀).subgroupOf K₀ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ V ⊓ K₀ := hn
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · have := hVJ (g : G) (hK₀J g.2) (n : G) hn'.1
      exact this
    · exact K₀.mul_mem (K₀.mul_mem g.2 hn'.2) (K₀.inv_mem g.2)
  rcases quasisimple_normal_subgroups hq hNn with htop | hcen
  · exfalso
    have hK₀V : K₀ ≤ V := fun x hx => by
      have : (⟨x, hx⟩ : ↥K₀) ∈ N := by rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 this).1
    have hsolK : Group.IsSolvable ↥K₀ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK₀V)
        (Subgroup.inclusion_injective hK₀V)
    have : Nontrivial ↥K₀ := isQuasisimple_nontrivial hq
    have : Group.IsPerfect ↥K₀ := hq.1
    exact Group.IsPerfect.not_isSolvable ↥K₀ hsolK
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥K₀) ∈ N := Subgroup.mem_subgroupOf.2 hx
    have := hcen hx'
    rw [hz, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this

theorem commute_of_component {p : ℕ} (hp : p.Prime) {K R V : Subgroup G}
    (hT : ∀ a ∈ K, ∀ a' ∈ K, (∀ x ∈ R, a * x = x * a) → (∀ x ∈ R, a' * x = x * a') →
      a * a' = a' * a)
    {c : G} (hcK : c ∈ K) (hcR : ∀ x ∈ R, c * x = x * c) (hcp : c ^ p = 1)
    (hVc : ∀ v ∈ V, c * v * c⁻¹ ∈ V) (hcop : ¬ p ∣ Nat.card V)
    {u : G} (huV : u ∈ V) (huK : ∀ x ∈ K, u * x * u⁻¹ ∈ K) (huR : ∀ x ∈ R, u * x = x * u) :
    Commute u c := by
  have h1 : u * c * u⁻¹ ∈ K := huK c hcK
  have h2 : ∀ x ∈ R, (u * c * u⁻¹) * x = x * (u * c * u⁻¹) := by
    intro x hx
    have hu := huR x hx
    have hc := hcR x hx
    calc u * c * u⁻¹ * x = u * c * (u⁻¹ * x) := by group
      _ = u * c * (x * u⁻¹) := by
          rw [(Commute.inv_left (show Commute u x from hu)).eq]
      _ = u * (c * x) * u⁻¹ := by group
      _ = u * (x * c) * u⁻¹ := by rw [hc]
      _ = (u * x) * c * u⁻¹ := by group
      _ = (x * u) * c * u⁻¹ := by rw [hu]
      _ = x * (u * c * u⁻¹) := by group
  have h3 : (u * c * u⁻¹) * c = c * (u * c * u⁻¹) := hT _ h1 c hcK h2 hcR
  have h4 : Commute ⁅u, c⁆ c := by
    have hcomm : Commute (u * c * u⁻¹) c := h3
    have hdef : ⁅u, c⁆ = (u * c * u⁻¹) * c⁻¹ := by
      rw [commutatorElement_def]
    rw [hdef]
    exact hcomm.mul_left (Commute.refl c).inv_left
  have h5 : ⁅u, c⁆ = 1 := eq_one_of_commute_pow hp huV hcp hVc hcop h4
  exact commutatorElement_eq_one_iff_mul_comm.1 h5


theorem commute_of_block_data [Finite G] {p : ℕ} (hp : p.Prime) {Y L R J V K₀ K₀' : Subgroup G}
    (hLY : L ≤ Y) (hL : IsComponent (L.subgroupOf Y)) (hRL : R ≤ L) (hR1 : R ≠ ⊥)
    (hZL : Subgroup.center ↥L = ⊥)
    (hVJ : ∀ j ∈ J, ∀ v ∈ V, j * v * j⁻¹ ∈ V) (hVs : Group.IsSolvable ↥V)
    (hcop : ¬ p ∣ Nat.card V) (hK₀J : K₀ ≤ J) (hK₀'J : K₀' ≤ J)
    (hq₀ : IsQuasisimple ↥K₀) (hq₀' : IsQuasisimple ↥K₀')
    (hz₀ : Subgroup.center ↥K₀ = ⊥) (hz₀' : Subgroup.center ↥K₀' = ⊥)
    (hn₀ : ∀ n ∈ L, (∀ x ∈ R, n * x = x * n) → ∀ k ∈ K₀, n * k * n⁻¹ ∈ K₀)
    (hn₀' : ∀ n ∈ L, (∀ x ∈ R, n * x = x * n) → ∀ k ∈ K₀', n * k * n⁻¹ ∈ K₀')
    {e : G} (heJ : e ∈ J) (heL : e ∈ L) (hep : e ^ p = 1) (heR : ∀ x ∈ R, e * x = x * e)
    (hcentral : ∀ n ∈ L, (∀ k ∈ K₀, n * k = k * n) → (∀ k ∈ K₀', n * k = k * n) →
      n * e = e * n)
    {u : G} (huV : u ∈ V) (huY : u ∈ Y) (huR : ∀ x ∈ R, u * x = x * u) : Commute u e := by
  have hLu : ∀ x ∈ L, u * x * u⁻¹ ∈ L := normalizes_of_component hLY hL hRL hR1 hZL huY huR
  set n : G := u * e * u⁻¹ * e⁻¹ with hn
  have hnL : n ∈ L := L.mul_mem (hLu e heL) (L.inv_mem heL)
  have hnV : n ∈ V := by
    have : n = u * (e * u⁻¹ * e⁻¹) := by rw [hn]; group
    rw [this]
    exact V.mul_mem huV (hVJ e heJ u⁻¹ (V.inv_mem huV))
  have hnR : ∀ x ∈ R, n * x = x * n := by
    intro x hx
    have h1 := huR x hx
    have h2 := heR x hx
    have h3 : u⁻¹ * x = x * u⁻¹ := (Commute.inv_left (show Commute u x from h1)).eq
    have h4 : e⁻¹ * x = x * e⁻¹ := (Commute.inv_left (show Commute e x from h2)).eq
    calc u * e * u⁻¹ * e⁻¹ * x = u * e * u⁻¹ * (e⁻¹ * x) := by group
      _ = u * e * u⁻¹ * (x * e⁻¹) := by rw [h4]
      _ = u * e * (u⁻¹ * x) * e⁻¹ := by group
      _ = u * e * (x * u⁻¹) * e⁻¹ := by rw [h3]
      _ = u * (e * x) * u⁻¹ * e⁻¹ := by group
      _ = u * (x * e) * u⁻¹ * e⁻¹ := by rw [h2]
      _ = (u * x) * e * u⁻¹ * e⁻¹ := by group
      _ = (x * u) * e * u⁻¹ * e⁻¹ := by rw [h1]
      _ = x * (u * e * u⁻¹ * e⁻¹) := by group
  have hcentr : ∀ (K' : Subgroup G), K' ≤ J → IsQuasisimple ↥K' → Subgroup.center ↥K' = ⊥ →
      (∀ k ∈ K', n * k * n⁻¹ ∈ K') → ∀ k ∈ K', n * k = k * n := by
    intro K' hK'J hq hz hnk k hk
    have hbot := inf_eq_bot_of_solvable hK'J hVJ hVs hq hz
    have hmem : n * k * n⁻¹ * k⁻¹ ∈ V ⊓ K' := by
      refine ⟨?_, K'.mul_mem (hnk k hk) (K'.inv_mem hk)⟩
      have : n * k * n⁻¹ * k⁻¹ = n * (k * n⁻¹ * k⁻¹) := by group
      rw [this]
      exact V.mul_mem hnV (hVJ k (hK'J hk) n⁻¹ (V.inv_mem hnV))
    rw [hbot, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hmem)
  have hK₀c := hcentr K₀ hK₀J hq₀ hz₀ (hn₀ n hnL hnR)
  have hK₀'c := hcentr K₀' hK₀'J hq₀' hz₀' (hn₀' n hnL hnR)
  have hne : n * e = e * n := hcentral n hnL hK₀c hK₀'c
  have hcomm : Commute ⁅u, e⁆ e := by
    have : ⁅u, e⁆ = n := by rw [hn, commutatorElement_def]
    rw [this]
    exact hne
  have h5 : ⁅u, e⁆ = 1 := eq_one_of_commute_pow hp huV hep (hVJ e heJ) hcop hcomm
  exact commutatorElement_eq_one_iff_mul_comm.1 h5

end CFSG.RankThree.PartOne.K1327
