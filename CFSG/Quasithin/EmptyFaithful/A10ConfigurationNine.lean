module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationEightGz
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationNineModel

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

theorem oTwoUpper_top_eq_top (hG : IsSimpleGroup G) {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    oTwoUpper (⊤ : Subgroup G) = ⊤ := by
  have hN : (oTwoUpper (⊤ : Subgroup G)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_oTwoUpper ⊤ (Subgroup.mem_top g)) n).1 hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oTwoUpper (⊤ : Subgroup G)) with h | h
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have ho : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have hc : c ∈ oTwoUpper (⊤ : Subgroup G) :=
      mem_oTwoUpper_of_odd (Subgroup.mem_top c) (by rw [ho]; decide)
    rw [h, Subgroup.mem_bot] at hc
    exact hc1 hc
  · exact h

theorem zpow_involution {g : G} (hg : g * g = 1) (m : ℤ) : g ^ m = 1 ∨ g ^ m = g := by
  have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  have hm : m = 2 * (m / 2) + m % 2 := by omega
  have hr : m % 2 = 0 ∨ m % 2 = 1 := Int.emod_two_eq_zero_or_one m
  rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases hr with h | h
  · left
    rw [h]
    simp
  · right
    rw [h]
    simp

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def T₀ : Subgroup G := T0h.map E.ι

theorem T₀_le_T : E.T₀ ≤ T := by
  have := Subgroup.map_mono (f := E.ι) T0h_le_Th
  rwa [E.map_Th] at this

theorem T_conj_T₀ : ∀ h ∈ T, ∀ k ∈ E.T₀, h * k * h⁻¹ ∈ E.T₀ := by
  intro h hh k hk
  obtain ⟨w, hw, rfl⟩ := E.mem_T_iff.1 hh
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨w * k' * w⁻¹, Th_conj_T0h w hw k' hk', by simp⟩

theorem comm_T_le_T₀ : ⁅T, T⁆ ≤ E.T₀ := by
  have h1 : ⁅T, T⁆ = (⁅Th, Th⁆).map E.ι := by
    have := (Subgroup.map_commutator Th Th E.ι).symm
    rwa [E.map_Th] at this
  rw [h1]
  exact Subgroup.map_mono commutator_Th_le_T0h

theorem mul_mem_T₀_of_not_mem {x y : G} (hx : x ∈ T) (hy : y ∈ T) (hxn : x ∉ E.T₀)
    (hyn : y ∉ E.T₀) : x * y ∈ E.T₀ := by
  obtain ⟨u, hu, rfl⟩ := E.mem_T_iff.1 hx
  obtain ⟨v, hv, rfl⟩ := E.mem_T_iff.1 hy
  have hun : u ∉ T0h := fun h => hxn ⟨u, h, rfl⟩
  have hvn : v ∉ T0h := fun h => hyn ⟨v, h, rfl⟩
  exact ⟨u * v, mul_mem_T0h_of_not_mem u hu v hv hun hvn, map_mul _ _ _⟩

theorem mem_Δ₅_iff {w : Wc} : E.ι w ∈ E.Δ₅ ↔ D5 w = true := by
  rw [E.Δ₅_eq_image]
  constructor
  · rintro ⟨w', hw', h⟩
    have := E.injective h
    subst this
    exact hw'
  · intro h
    exact ⟨w, h, rfl⟩

theorem involution_mem_Δ_of_mem_T₀ {x : G} (hx : x ∈ E.T₀) (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    x ∈ E.Δ₁ ∨ x ∈ E.Δ₂ ∨ x ∈ E.Δ₄ := by
  obtain ⟨w, hw, rfl⟩ := hx
  have hw1 : w ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hw2 : w * w = 1 := E.ι_sq_eq_one.1 hx2
  rcases T0h_involution w hw hw1 hw2 with h | h | h
  · exact Or.inl (E.mem_Δ₁_iff.2 h)
  · exact Or.inr (Or.inl (E.mem_Δ₂_iff.2 h))
  · exact Or.inr (Or.inr (E.mem_Δ₄_iff.2 h))

include E in
theorem exists_order_three : ∃ c : G, c ^ 3 = 1 ∧ c ≠ 1 := by
  obtain ⟨w, hw3, hw1⟩ := exists_order_three_model
  refine ⟨E.ι w, by rw [← map_pow, hw3, map_one], fun h => hw1 (E.ι_eq_one.1 h)⟩

theorem exists_conj_mem_T₀ [Finite G] (hOT : oTwoUpper (⊤ : Subgroup G) = ⊤)
    (hT : quasithinIsSylowTwo T) {g : G} (hg : g ∈ T) (hgn : g ∉ E.T₀) (hg2 : g * g = 1) :
    ∃ a : G, a⁻¹ * g * a ∈ E.T₀ := by
  by_contra hcon
  push Not at hcon
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hnot := not_mem_oTwoUpper_of_transfer (X := ⊤) (H := T) (K := E.T₀) le_top hT.1
    (by rw [Subgroup.relIndex_top_right]; exact hT.2) E.T₀_le_T E.T_conj_T₀ E.comm_T_le_T₀ hg hgn
    (fun m a _ ha => by
      rcases zpow_involution hg2 m with h | h
      · rw [h] at ha ⊢
        simp only [inv_one, mul_one, inv_mul_cancel]
        exact one_mem _
      · rw [h] at ha ⊢
        rw [hinv]
        exact E.mul_mem_T₀_of_not_mem hg ha hgn (hcon a))
  have hgO : g ∈ oTwoUpper (⊤ : Subgroup G) := by
    rw [hOT]
    exact Subgroup.mem_top g
  exact hnot hgO

theorem Δ₄_conj_t [Finite G] {y : G} (hLam : E.Lam = (E.B : Set G) ∩ (E.Δ₂ ∪ E.Δ₄))
    (hy : y ∈ E.Δ₄) : ∃ g : G, g⁻¹ * E.t * g = y := by
  have hu4 : E.ι u4 ∈ E.Lam := by
    rw [hLam]
    exact ⟨Subgroup.mem_map_of_mem _ u4_mem_A2, Or.inr (E.mem_Δ₄_iff.2 D4_u4)⟩
  obtain ⟨g, -, hg⟩ := hu4
  obtain ⟨u, -, hu⟩ := E.Δ₄_isClass
  have hu4' : E.ι u4 ∈ E.Δ₄ := E.mem_Δ₄_iff.2 D4_u4
  rw [hu] at hy hu4'
  obtain ⟨m, -, hm⟩ := hy
  obtain ⟨m', -, hm'⟩ := hu4'
  refine ⟨g * m'⁻¹ * m, ?_⟩
  calc (g * m'⁻¹ * m)⁻¹ * E.t * (g * m'⁻¹ * m) = m⁻¹ * m' * (g⁻¹ * E.t * g) * m'⁻¹ * m := by group
    _ = m⁻¹ * m' * (m'⁻¹ * u * m') * m'⁻¹ * m := by rw [hg, hm']
    _ = m⁻¹ * u * m := by group
    _ = y := hm

theorem involution_fusion [Finite G] (hOT : oTwoUpper (⊤ : Subgroup G) = ⊤)
    (hT : quasithinIsSylowTwo T) (hLam : E.Lam = (E.B : Set G) ∩ (E.Δ₂ ∪ E.Δ₄)) {x : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    (∃ g : G, g⁻¹ * E.z * g = x) ∨ ∃ g : G, g⁻¹ * E.t * g = x := by
  obtain ⟨c, hc⟩ := exists_conj_mem_of_odd_index hT.2 hx2
  have hy2 : (c⁻¹ * x * c) * (c⁻¹ * x * c) = 1 := by
    calc (c⁻¹ * x * c) * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c := by group
      _ = 1 := by rw [hx2]; group
  have hy1 : c⁻¹ * x * c ≠ 1 := by
    intro h
    apply hx1
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨d, hd⟩ : ∃ d : G, d⁻¹ * x * d ∈ E.T₀ := by
    by_cases hyT0 : c⁻¹ * x * c ∈ E.T₀
    · exact ⟨c, hyT0⟩
    · obtain ⟨a, ha⟩ := E.exists_conj_mem_T₀ hOT hT hc hyT0 hy2
      refine ⟨c * a, ?_⟩
      have e : (c * a)⁻¹ * x * (c * a) = a⁻¹ * (c⁻¹ * x * c) * a := by group
      rw [e]
      exact ha
  have hd2 : (d⁻¹ * x * d) * (d⁻¹ * x * d) = 1 := by
    calc (d⁻¹ * x * d) * (d⁻¹ * x * d) = d⁻¹ * (x * x) * d := by group
      _ = 1 := by rw [hx2]; group
  have hd1 : d⁻¹ * x * d ≠ 1 := by
    intro h
    apply hx1
    calc x = d * (d⁻¹ * x * d) * d⁻¹ := by group
      _ = 1 := by rw [h]; group
  rcases E.involution_mem_Δ_of_mem_T₀ hd hd1 hd2 with h | h | h
  · obtain ⟨m, -, hm⟩ := h
    left
    refine ⟨m * d⁻¹, ?_⟩
    calc (m * d⁻¹)⁻¹ * E.z * (m * d⁻¹) = d * (m⁻¹ * E.z * m) * d⁻¹ := by group
      _ = d * (d⁻¹ * x * d) * d⁻¹ := by rw [hm]
      _ = x := by group
  · obtain ⟨m, -, hm⟩ := h
    right
    refine ⟨m * d⁻¹, ?_⟩
    calc (m * d⁻¹)⁻¹ * E.t * (m * d⁻¹) = d * (m⁻¹ * E.t * m) * d⁻¹ := by group
      _ = d * (d⁻¹ * x * d) * d⁻¹ := by rw [hm]
      _ = x := by group
  · obtain ⟨g, hg⟩ := E.Δ₄_conj_t hLam h
    right
    refine ⟨g * d⁻¹, ?_⟩
    calc (g * d⁻¹)⁻¹ * E.t * (g * d⁻¹) = d * (g⁻¹ * E.t * g) * d⁻¹ := by group
      _ = d * (d⁻¹ * x * d) * d⁻¹ := by rw [hg]
      _ = x := by group

theorem centralizer_B [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.centralizer (E.B : Set G) = E.B := by
  apply le_antisymm
  · intro x hx
    have hpair : x ∈ Subgroup.centralizer ({E.z, E.t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro h (rfl | rfl)
      · exact Subgroup.mem_centralizer_iff.1 hx _ E.z_mem_B
      · exact Subgroup.mem_centralizer_iff.1 hx _ E.t_mem_B
    rw [E.lemma_13_9_7 hEven hT hM] at hpair
    obtain ⟨w, hw, rfl⟩ := E.mem_T_iff.1 (E.J_le_T hpair)
    have hwB : w ∈ A2 := by
      refine centralizer_B_Th w hw fun y hy => ?_
      have := Subgroup.mem_centralizer_iff.1 hx (E.ι y) (Subgroup.mem_map_of_mem _ hy)
      exact E.injective (by rw [map_mul, map_mul]; exact this.symm)
    exact Subgroup.mem_map_of_mem _ hwB
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact E.B_commute h hh b hb

theorem Gz_le_K (hBn : ∀ g ∈ E.Gz, ∀ b ∈ E.B, g * b * g⁻¹ ∈ E.B) : E.Gz ≤ E.K := by
  intro g hg
  rw [K, Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact hBn g hg b hb
  · intro hb
    have := hBn g⁻¹ (E.Gz.inv_mem hg) _ hb
    have e : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
    rwa [e] at this

end Emb

end CFSG.Quasithin.A10
