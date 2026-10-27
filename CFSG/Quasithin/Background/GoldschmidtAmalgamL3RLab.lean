module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace CosetGeom

variable {G : Type*} [Group G] {G₀ G₁ G₂ : Subgroup G} {z : G}

@[expose] noncomputable def Zv1 (z : G) (y : G₀ ⧸ G₂.subgroupOf G₀) : Subgroup G :=
  ⨆ (g : G₀) (_ : (g : G₀ ⧸ G₂.subgroupOf G₀) = y), conjSub (g : G) (Subgroup.zpowers z)

@[expose] noncomputable def Zv (z : G) : CosetGeom G₀ G₁ G₂ → Subgroup G
  | Sum.inl _ => ⊥
  | Sum.inr y => Zv1 z y

theorem Zv_inl (z : G) (x : G₀ ⧸ G₁.subgroupOf G₀) :
    Zv z (Sum.inl x : CosetGeom G₀ G₁ G₂) = ⊥ := rfl

theorem Zv_inr (z : G) (y : G₀ ⧸ G₂.subgroupOf G₀) :
    Zv z (Sum.inr y : CosetGeom G₀ G₁ G₂) = Zv1 z y := rfl

theorem Zv1_mk (hN : G₂ ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G))
    (g : G₀) : Zv1 z (g : G₀ ⧸ G₂.subgroupOf G₀) = conjSub (g : G) (Subgroup.zpowers z) := by
  refine le_antisymm (iSup₂_le fun g' hg' => ?_) (le_iSup₂_of_le g rfl le_rfl)
  have h1 : (g' : G₀)⁻¹ * g ∈ G₂.subgroupOf G₀ := QuotientGroup.eq.mp hg'
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (g : G)⁻¹ * g' ∈ G₂ := by simpa [mul_assoc] using G₂.inv_mem h1
  have e : (g' : G) = g * ((g : G)⁻¹ * g') := by group
  rw [e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hN h2)]

theorem Zv1_smul (hN : G₂ ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G))
    (g : G₀) (y : G₀ ⧸ G₂.subgroupOf G₀) :
    Zv1 z (g • y) = conjSub (g : G) (Zv1 z y) := by
  induction y using QuotientGroup.induction_on with
  | H h =>
    rw [smul_coe_quot, Zv1_mk hN, Zv1_mk hN, Subgroup.coe_mul, conjSub_mul]

theorem Zv_smul (hN : G₂ ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G))
    (g : G₀) (γ : CosetGeom G₀ G₁ G₂) : Zv z (g • γ) = conjSub (g : G) (Zv z γ) := by
  cases γ with
  | inl x => rw [smul_inl, Zv_inl, Zv_inl, conjSub_bot]
  | inr y => rw [smul_inr, Zv_inr, Zv_inr]; exact Zv1_smul hN g y

theorem Zv_smul_γ₁ (hN : G₂ ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G))
    (g : G₀) : Zv z (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) (Subgroup.zpowers z) := by
  rw [smul_γ₁, Zv_inr]
  exact Zv1_mk hN g

theorem Zv_γ₁ (hN : G₂ ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :
    Zv z (γ₁ G₀ G₁ G₂) = Subgroup.zpowers z := by
  have := Zv_smul_γ₁ (G₁ := G₁) hN (1 : G₀)
  rwa [one_smul, Subgroup.coe_one, conjSub_one] at this

theorem exists_smul_edge_AB {u v : CosetGeom G₀ G₁ G₂} (huv : (graph G₀ G₁ G₂).Adj u v)
    (hu : vtype u = false) :
    ∃ g : ↥G₀, g • γ₀ G₀ G₁ G₂ = u ∧ g • γ₁ G₀ G₁ G₂ = v := by
  obtain ⟨g, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := exists_smul_edge huv
  · exact ⟨g, h1, h2⟩
  · exfalso
    rw [← h2, vtype_smul, vtype_γ₁] at hu
    exact absurd hu (by decide)

theorem vtype_eq_true_of_adj {u v : CosetGeom G₀ G₁ G₂} (huv : (graph G₀ G₁ G₂).Adj u v)
    (hu : vtype u = false) : vtype v = true := by
  have h1 := vtype_ne_of_adj huv
  rw [hu] at h1
  cases hv : vtype v
  · exact absurd hv.symm h1
  · rfl

theorem Vv_le_Vv_of_adj {V : Subgroup G} {u v : CosetGeom G₀ G₁ G₂}
    (huv : (graph G₀ G₁ G₂).Adj u v) (hu : vtype u = false) : Vv V u ≤ Vv V v := by
  cases u with
  | inr y => simp [vtype] at hu
  | inl x =>
    cases v with
    | inl x' => exact (not_adj_inl_inl huv).elim
    | inr y =>
      rw [Vv_inr]
      exact le_iSup₂_of_le x huv.symm le_rfl

theorem Vv_B_le_iff {V X : Subgroup G} {v : CosetGeom G₀ G₁ G₂} (hv : vtype v = true) :
    Vv V v ≤ X ↔ ∀ u, (graph G₀ G₁ G₂).Adj v u → Vv V u ≤ X := by
  cases v with
  | inl x => simp [vtype] at hv
  | inr y =>
    rw [Vv_inr, iSup₂_le_iff]
    constructor
    · intro hle u hu
      cases u with
      | inl x => exact hle x hu
      | inr y' => exact (not_adj_inr_inr hu).elim
    · intro hall x hx
      exact hall (Sum.inl x) hx

theorem Zv_le_Vv_of_adj {V : Subgroup G} {z : G} (hz : z ∈ V)
    (hN₁ : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hN₂ : G₂ ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G))
    {u v : CosetGeom G₀ G₁ G₂} (huv : (graph G₀ G₁ G₂).Adj u v) (hu : vtype u = false) :
    Zv z v ≤ Vv V u := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [Zv_smul_γ₁ hN₂, Vv_smul_γ₀ hN₁]
  exact conjSub_mono _ (Subgroup.zpowers_le.mpr hz)

theorem vtype_eq_false_of_adj {u v : CosetGeom G₀ G₁ G₂} (huv : (graph G₀ G₁ G₂).Adj u v)
    (hu : vtype u = true) : vtype v = false := by
  have h1 := vtype_ne_of_adj huv
  rw [hu] at h1
  cases hv : vtype v
  · rfl
  · exact absurd hv.symm h1

theorem ballStab_le_ballStab_of_dist (hG : G₀ = G₁ ⊔ G₂) {u v : CosetGeom G₀ G₁ G₂} {n m : ℕ}
    (hd : dist u v + m ≤ n) : ballStab n u ≤ ballStab m v := fun _ hx =>
  mem_ballStab.mpr fun δ hδ => mem_ballStab.mp hx δ (by have := dist_triangle hG u v δ; omega)

@[expose] def IsGeo (p : ℕ → CosetGeom G₀ G₁ G₂) (n : ℕ) : Prop :=
  ∀ i j, i ≤ j → j ≤ n → dist (p i) (p j) = j - i

theorem IsGeo.adj {p : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ} (hp : IsGeo p n) {i : ℕ} (hi : i < n) :
    (graph G₀ G₁ G₂).Adj (p i) (p (i + 1)) := by
  have := hp i (i + 1) (by omega) (by omega)
  exact dist_eq_one_iff_adj.mp (by omega)

theorem IsGeo.ne {p : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ} (hp : IsGeo p n) {i j : ℕ} (hij : i < j)
    (hj : j ≤ n) : p i ≠ p j := fun e => by
  have := hp i j hij.le hj
  rw [e, dist_self] at this
  omega

theorem exists_geodesic (hG : G₀ = G₁ ⊔ G₂) (n : ℕ) :
    ∀ u v : CosetGeom G₀ G₁ G₂, dist u v = n →
      ∃ p : ℕ → CosetGeom G₀ G₁ G₂, p 0 = u ∧ p n = v ∧ IsGeo p n := by
  induction n with
  | zero =>
    intro u v huv
    obtain rfl : u = v := (dist_eq_zero_iff hG).mp huv
    refine ⟨fun _ => u, rfl, rfl, fun i j hij hj => ?_⟩
    obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    exact dist_self u
  | succ n ih =>
    intro u v huv
    obtain ⟨β, hβ, hβd⟩ := exists_adj_dist_eq hG (α := u) (δ := v) (d := n) huv
    obtain ⟨p, hp0, hpn, hgeo⟩ := ih u β hβd
    have hβv : dist β v = 1 := by rw [dist_comm]; exact dist_eq_one_iff_adj.mpr hβ
    refine ⟨fun i => if i ≤ n then p i else v, by simp [hp0], by simp, fun i j hij hj => ?_⟩
    by_cases hjn : j ≤ n
    · have hin : i ≤ n := hij.trans hjn
      simp only [hin, hjn, ↓reduceIte]
      exact hgeo i j hij hjn
    · obtain rfl : j = n + 1 := by omega
      simp only [hjn, ↓reduceIte]
      by_cases hin : i ≤ n
      · simp only [hin, ↓reduceIte]
        have h1 : dist (p i) v ≤ dist (p i) β + dist β v := dist_triangle hG _ _ _
        have h2 : dist u v ≤ dist u (p i) + dist (p i) v := dist_triangle hG _ _ _
        have h3 := hgeo i n hin le_rfl
        have h4 := hgeo 0 i (Nat.zero_le _) hin
        rw [hpn] at h3
        rw [hp0] at h4
        omega
      · obtain rfl : i = n + 1 := by omega
        simp [dist_self]

end CosetGeom

end CFSG.Quasithin
