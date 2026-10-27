module

public import CFSG.Quasithin.H13.A5W1622a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_comm_mem_of_fixed' (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (h1317 : ∀ g : G, (∀ t ∈ S.Tv,
        (g * S.z * g⁻¹) * t * (g * S.z * g⁻¹)⁻¹ * t⁻¹ ∈ Subgroup.zpowers S.v12) →
      ¬ K₀ ≤ Subgroup.centralizer ({g * S.z * g⁻¹} : Set G)) {A : Subgroup G}
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hK₀A : K₀ ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ A) {Y : Subgroup G}
    (hYK : Y ≤ Subgroup.normalizer (K₀ : Set G)) (hYA : Y ≤ Subgroup.normalizer (A : Set G))
    (hYa : ∀ y ∈ Y, y * S.a * y⁻¹ = S.a)
    (hfix : ∀ m ∈ A, (∀ y ∈ Y, ∀ k ∈ K₀,
        k * (y * m * y⁻¹ * m⁻¹) * k⁻¹ = y * m * y⁻¹ * m⁻¹) → ∀ k ∈ K₀, k * m * k⁻¹ = m) :
    False := by
  classical
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hsylH : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv h1222 h517) le_sup_right
      (sup_le hK₀G S.Tv_le_Gv)
  have hS₀ : IsSylowTwoOf (S.Tv ⊓ K₀) K₀ :=
    A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hTK₀)
  let ρ : ↥K₀ →* MulAut ↥A := (conjAct A).comp (Subgroup.inclusion hK₀A)
  have hρ : ∀ (g : ↥K₀) (u : ↥A), ((ρ g u : ↥A) : G) = g * u * (g : G)⁻¹ := fun g u =>
    InternalSec.coe_conjAct_apply _ u
  let δ : ↥K₀ → ↥A := fun k => ⟨(k : G)⁻¹ * S.a * k * S.a⁻¹, hcomm k k.2⟩
  have hδ : ∀ g h, δ (g * h) = ρ h⁻¹ (δ g) * δ h := by
    intro g h
    apply Subtype.ext
    rw [Subgroup.coe_mul, hρ]
    simp only [δ, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hA2' : ∀ u : ↥A, u ^ 2 = 1 := fun u =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA2 u u.2)
  have : IsMulCommutative ↥A := ⟨⟨fun u w => Subtype.ext (hAc u u.2 w w.2)⟩⟩
  set Z₀ : Subgroup ↥A := (Subgroup.zpowers S.v12).subgroupOf A with hZ₀def
  have hZ₀ : ∀ g, ∀ z ∈ Z₀, ρ g z = z := by
    intro g z hz
    apply Subtype.ext
    rw [hρ]
    have hzv : (z : G) ∈ Subgroup.zpowers S.v12 := hz
    rw [← S.zpowers_v12_comm hK₀G _ hzv _ g.2, mul_inv_cancel_right]
  set D : Subgroup ↥K₀ := (S.Tv ⊓ K₀).subgroupOf K₀ with hDdef
  have hD : ∀ d ∈ D, δ d ∈ Z₀ := by
    intro d hd
    have hdT : (d : G) ∈ S.Tv := (Subgroup.mem_subgroupOf.mp hd).1
    show (d : G)⁻¹ * S.a * d * S.a⁻¹ ∈ Subgroup.zpowers S.v12
    have h1 := S.comm_a_Tv (S.Tv.inv_mem hdT)
    have e : (d : G)⁻¹ * S.a * d * S.a⁻¹ = (S.a * (d : G)⁻¹ * S.a⁻¹ * (d : G)⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hodd : ¬ 2 ∣ D.index := hS₀.2.2
  have hperf : commutator ↥K₀ = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hK₀p)
  obtain ⟨m, hm⟩ := exists_coboundary_of_odd_index hA2' ρ δ hδ Z₀ hZ₀ D hD hodd hperf
  have hmk : ∀ k : ↥K₀, (k : G)⁻¹ * S.a * k * S.a⁻¹ = (k : G)⁻¹ * m * k * (m : G)⁻¹ := by
    intro k
    have h1 := congrArg Subtype.val (hm k)
    rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv] at h1
    simp only [δ, Subgroup.coe_inv, inv_inv] at h1
    rw [h1]
  have hconj : ∀ k ∈ K₀, S.a * k * S.a⁻¹ = (m : G) * k * (m : G)⁻¹ := by
    intro k hk
    have h1 := hmk ⟨k, hk⟩
    calc S.a * k * S.a⁻¹ = k * (k⁻¹ * S.a * k * S.a⁻¹) := by group
      _ = k * (k⁻¹ * (m : G) * k * (m : G)⁻¹) := by rw [h1]
      _ = (m : G) * k * (m : G)⁻¹ := by group
  have hmY : ∀ y ∈ Y, ∀ k ∈ K₀,
      k * (y * (m : G) * y⁻¹ * (m : G)⁻¹) * k⁻¹ = y * (m : G) * y⁻¹ * (m : G)⁻¹ := by
    intro y hy k hk
    have hk' : y⁻¹ * k * y ∈ K₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hYK hy)) k).mp hk
      simpa using this
    have h1 := hconj _ hk'
    have h2 : S.a * k * S.a⁻¹ = (y * m * y⁻¹) * k * (y * m * y⁻¹)⁻¹ := by
      have e1 : S.a * k * S.a⁻¹ = y * (S.a * (y⁻¹ * k * y) * S.a⁻¹) * y⁻¹ := by
        have hya := hYa y hy
        calc S.a * k * S.a⁻¹ = (y * S.a * y⁻¹) * k * (y * S.a * y⁻¹)⁻¹ := by rw [hya]
          _ = y * (S.a * (y⁻¹ * k * y) * S.a⁻¹) * y⁻¹ := by group
      rw [e1, h1]
      group
    have h3 : (m : G) * k * (m : G)⁻¹ = (y * m * y⁻¹) * k * (y * m * y⁻¹)⁻¹ :=
      (hconj k hk).symm.trans h2
    have hmA : y * (m : G) * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hYA hy) _).mp m.2
    have hc : (m : G)⁻¹ * (y * m * y⁻¹) = y * m * y⁻¹ * (m : G)⁻¹ := by
      have := hAc _ (A.inv_mem m.2) _ hmA
      rw [this]
    have h4 : k * ((m : G)⁻¹ * (y * m * y⁻¹)) = ((m : G)⁻¹ * (y * m * y⁻¹)) * k := by
      calc k * ((m : G)⁻¹ * (y * m * y⁻¹)) =
          (m : G)⁻¹ * ((m : G) * k * (m : G)⁻¹) * (y * m * y⁻¹) := by group
        _ = (m : G)⁻¹ * ((y * m * y⁻¹) * k * (y * m * y⁻¹)⁻¹) * (y * m * y⁻¹) := by rw [h3]
        _ = ((m : G)⁻¹ * (y * m * y⁻¹)) * k := by group
    rw [← hc]
    calc k * ((m : G)⁻¹ * (y * m * y⁻¹)) * k⁻¹ =
        ((m : G)⁻¹ * (y * m * y⁻¹)) * k * k⁻¹ := by rw [h4]
      _ = (m : G)⁻¹ * (y * m * y⁻¹) := by group
  have hmK := hfix m m.2 hmY
  have hK₀a : K₀ ≤ Subgroup.centralizer ({S.a} : Set G) := by
    intro k hk
    have h1 := hmk ⟨k, hk⟩
    have h3 : k⁻¹ * (m : G) * k * (m : G)⁻¹ = 1 := by
      have h5 : (m : G) * k = k * m := by
        calc (m : G) * k = (k * m * k⁻¹) * k := by rw [hmK k hk]
          _ = k * m := by group
      calc k⁻¹ * (m : G) * k * (m : G)⁻¹ = k⁻¹ * ((m : G) * k) * (m : G)⁻¹ := by group
        _ = 1 := by rw [h5]; group
    have h4 : k⁻¹ * S.a * k * S.a⁻¹ = 1 := h1.trans h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h5 : S.a * k = k * S.a := by
      calc S.a * k = k * (k⁻¹ * S.a * k * S.a⁻¹) * S.a := by group
        _ = k * S.a := by rw [h4]; group
    exact h5.symm
  obtain ⟨g, -, hga⟩ := S.exists_conj_a
  refine h1317 g (fun t ht => by rw [hga]; exact S.comm_a_Tv ht) ?_
  rw [hga]
  exact hK₀a

end Setting

end CFSG.Quasithin.H13.A5
