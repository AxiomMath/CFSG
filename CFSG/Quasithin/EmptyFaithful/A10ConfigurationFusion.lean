module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationLocal
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationParity

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem pResidual_two_eq_top (hG : IsSimpleGroup G) {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    pResidual 2 G = ⊤ := by
  refine eq_top_iff.2 (le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    obtain ⟨k, hk⟩ := hp c
    rw [h, Subgroup.mem_bot] at hk
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have ho : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have h3 := orderOf_dvd_of_pow_eq_one hk
    rw [ho] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · rw [h]

theorem not_mem_isPGroup_of_order_three {P : Subgroup G} (hP : IsPGroup 2 P) {c : G}
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) : c ∉ P := by
  intro hc
  obtain ⟨k, hk⟩ := hP ⟨c, hc⟩
  have hk' : c ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have h3 := orderOf_dvd_of_pow_eq_one hk'
  rw [ho] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem z_sq : E.z * E.z = 1 := by
  rw [z, ← map_mul, z0_sq, map_one]

theorem s_sq : E.s * E.s = 1 := by
  rw [s, ← map_mul, s0_sq, map_one]

theorem z_ne_one : E.z ≠ 1 := by
  intro h
  exact z0_ne_one (E.injective (by rw [map_one]; exact h))

theorem z_mem_M : E.z ∈ M := E.mem_M.2 ⟨z0, rfl⟩
theorem mem_T_iff {x : G} : x ∈ T ↔ ∃ w ∈ Th, E.ι w = x := by
  constructor
  · intro hx
    rw [← E.map_Th] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have := Subgroup.mem_map_of_mem E.ι hw
    rwa [E.map_Th] at this

theorem s_mem_T : E.s ∈ T := E.mem_T_iff.2 ⟨s0, s0_mem_Th, rfl⟩
theorem z_central {y : G} (hy : y ∈ T) : y * E.z = E.z * y := by
  obtain ⟨w, hw, rfl⟩ := E.mem_T_iff.1 hy
  rw [z, ← map_mul, ← map_mul, z0_central w hw]

theorem s_comm_z : E.s * E.z = E.z * E.s := E.z_central E.s_mem_T

include E in
theorem not_dvd_index_T_M [Finite G] (hT : quasithinIsSylowTwo T) :
    ¬ 2 ∣ (T.subgroupOf M).index := by
  intro h
  apply hT.2
  refine h.trans ?_
  have := Subgroup.relIndex_dvd_index_of_le E.T_le_M
  simpa [Subgroup.relIndex] using this

theorem not_mem_zG_of_D236 (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hT : quasithinIsSylowTwo T) {w : Wc}
    (hw : D2 w = true ∨ D3 w = true ∨ D6 w = true) :
    ¬ ∃ g : G, g⁻¹ * E.z * g = E.ι w := by
  have hc : ∃ c : Wc, c * c * c = 1 ∧ c ≠ 1 ∧ c * w = w * c := by
    rcases hw with h | h | h
    · exact exists_three_central_of_conj exists_three_central_t0 ((cls_t0 w).2 h)
    · exact exists_three_central_of_conj exists_three_central_u3 ((cls_u3 w).2 h)
    · exact exists_three_central_of_conj exists_three_central_s0 ((cls_s0 w).2 h)
  obtain ⟨c, hc3, hc1, hcw⟩ := hc
  rintro ⟨g, hg⟩
  have hcen : g * E.ι c * g⁻¹ ∈ Subgroup.centralizer ({E.z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hz : E.z = g * E.ι w * g⁻¹ := by rw [← hg]; group
    have hcw' : E.ι c * E.ι w = E.ι w * E.ι c := by rw [← map_mul, ← map_mul, hcw]
    rw [hz]
    calc g * E.ι w * g⁻¹ * (g * E.ι c * g⁻¹) = g * (E.ι w * E.ι c) * g⁻¹ := by group
      _ = g * (E.ι c * E.ι w) * g⁻¹ := by rw [hcw']
      _ = g * E.ι c * g⁻¹ * (g * E.ι w * g⁻¹) := by group
  rw [hGz] at hcen
  have hc3' : (g * E.ι c * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow]
    have : E.ι c ^ 3 = 1 := by
      rw [pow_succ, pow_two, ← map_mul, ← map_mul, hc3, map_one]
    rw [this]
    group
  have hc1' : g * E.ι c * g⁻¹ ≠ 1 := by
    intro h
    apply hc1
    apply E.injective
    rw [map_one]
    have : E.ι c = g⁻¹ * (g * E.ι c * g⁻¹) * g := by group
    rw [this, h]
    group
  exact not_mem_isPGroup_of_order_three hT.1 hc3' hc1' hcen

theorem zG_cap_M [Finite G] (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hT : quasithinIsSylowTwo T)
    (hwc : ∀ g : G, g⁻¹ * E.z * g ∈ E.B → g⁻¹ * E.z * g = E.z) :
    ∀ g : G, g⁻¹ * E.z * g ∈ M → ∃ m ∈ M, m⁻¹ * E.z * m = g⁻¹ * E.z * g := by
  intro g hgM
  obtain ⟨w, hw⟩ := E.mem_M.1 hgM
  have hsq : w * w = 1 := by
    apply E.injective
    rw [map_mul, map_one, hw]
    calc g⁻¹ * E.z * g * (g⁻¹ * E.z * g) = g⁻¹ * (E.z * E.z) * g := by group
      _ = 1 := by rw [E.z_sq]; group
  have hne : w ≠ 1 := by
    intro h1
    rw [h1, map_one] at hw
    apply E.z_ne_one
    calc E.z = g * (g⁻¹ * E.z * g) * g⁻¹ := by group
      _ = 1 := by rw [← hw]; group
  have hconj : ∀ v : Wc, (g * E.ι v)⁻¹ * E.z * (g * E.ι v) = E.ι (v⁻¹ * w * v) := by
    intro v
    rw [map_mul, map_mul, map_inv, hw]
    group
  rcases involution_partition w hsq hne with h | h | h | h | h | h
  · obtain ⟨v, hv⟩ := (cls_z0 w).2 h
    refine ⟨E.ι v, E.mem_M.2 ⟨v, rfl⟩, ?_⟩
    rw [← hw, ← hv, map_mul, map_mul, map_inv]
    rfl
  · exact absurd ⟨g, hw.symm⟩ (E.not_mem_zG_of_D236 hGz hT (Or.inl h))
  · exact absurd ⟨g, hw.symm⟩ (E.not_mem_zG_of_D236 hGz hT (Or.inr (Or.inl h)))
  · exfalso
    obtain ⟨v, hv⟩ := D4_into_B w h
    have h1 : (g * E.ι v)⁻¹ * E.z * (g * E.ι v) ∈ E.B := by
      rw [hconj]
      exact ⟨_, hv, rfl⟩
    have h2 := hwc _ h1
    rw [hconj] at h2
    have h3 : v⁻¹ * w * v = z0 := E.injective h2
    have h4 := D4_conj h v
    rw [h3] at h4
    have := (D_exclusive z0).1 D1_z0
    rw [this.2.2.1] at h4
    exact Bool.noConfusion h4
  · exfalso
    obtain ⟨v, hv⟩ := D5_into_B w h
    have h1 : (g * E.ι v)⁻¹ * E.z * (g * E.ι v) ∈ E.B := by
      rw [hconj]
      exact ⟨_, hv, rfl⟩
    have h2 := hwc _ h1
    rw [hconj] at h2
    have h3 : v⁻¹ * w * v = z0 := E.injective h2
    have h4 := D5_conj h v
    rw [h3] at h4
    have := (D_exclusive z0).1 D1_z0
    rw [this.2.2.2.1] at h4
    exact Bool.noConfusion h4
  · exact absurd ⟨g, hw.symm⟩ (E.not_mem_zG_of_D236 hGz hT (Or.inr (Or.inr h)))

theorem hfix_of_zG_cap_M (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hA1 : ∀ g : G, g⁻¹ * E.z * g ∈ M → ∃ m ∈ M, m⁻¹ * E.z * m = g⁻¹ * E.z * g) :
    ∀ g : G, g⁻¹ * E.z * g ∈ M → g ∈ M := by
  intro g hg
  obtain ⟨m, hm, hmeq⟩ := hA1 g hg
  have hcen : g * m⁻¹ ∈ Subgroup.centralizer ({E.z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc E.z * (g * m⁻¹) = g * (g⁻¹ * E.z * g) * m⁻¹ := by group
      _ = g * (m⁻¹ * E.z * m) * m⁻¹ := by rw [← hmeq]
      _ = g * m⁻¹ * E.z := by group
  rw [hGz] at hcen
  have h1 : g * m⁻¹ ∈ M := E.T_le_M hcen
  have := M.mul_mem h1 hm
  simpa using this

theorem fusion_s_of_mem_T [Finite G] (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hfix : ∀ g : G, g⁻¹ * E.z * g ∈ M → g ∈ M)
    (hA1 : ∀ g : G, g⁻¹ * E.z * g ∈ M → ∃ m ∈ M, m⁻¹ * E.z * m = g⁻¹ * E.z * g)
    {y g : G} (hy : g⁻¹ * E.s * g = y) (hyT : y ∈ T) : ∃ m ∈ M, m⁻¹ * E.s * m = y := by
  have hyz : y * E.z = E.z * y := E.z_central hyT
  have hodd := odd_index_centralizer_of_unique_fixed E.z_sq E.z_mem_M hyz hfix
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC
  have hz₂C : g⁻¹ * E.z * g ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc h * (g⁻¹ * E.z * g) = g⁻¹ * E.s * g * (g⁻¹ * E.z * g) := by rw [hy]
      _ = g⁻¹ * (E.s * E.z) * g := by group
      _ = g⁻¹ * (E.z * E.s) * g := by rw [E.s_comm_z]
      _ = g⁻¹ * E.z * g * h := by rw [← hy]; group
  have hu2 : (⟨g⁻¹ * E.z * g, hz₂C⟩ : C) * ⟨g⁻¹ * E.z * g, hz₂C⟩ = 1 := by
    apply Subtype.ext
    calc g⁻¹ * E.z * g * (g⁻¹ * E.z * g) = g⁻¹ * (E.z * E.z) * g := by group
      _ = 1 := by rw [E.z_sq]; group
  obtain ⟨c, hc⟩ := exists_conj_mem_of_odd_index hodd hu2
  have hz₃ : (c : G)⁻¹ * (g⁻¹ * E.z * g) * (c : G) ∈ M := (Subgroup.mem_subgroupOf.1 hc).1
  have hz₃' : (g * c)⁻¹ * E.z * (g * c) ∈ M := by
    have : (g * (c : G))⁻¹ * E.z * (g * (c : G)) = (c : G)⁻¹ * (g⁻¹ * E.z * g) * (c : G) := by
      group
    rw [this]
    exact hz₃
  obtain ⟨m, hm, hmeq⟩ := hA1 (g * c) hz₃'
  have hinner : (g * c * m⁻¹)⁻¹ * E.z * (g * c * m⁻¹) = E.z := by
    calc (g * c * m⁻¹)⁻¹ * E.z * (g * c * m⁻¹)
        = m * ((g * c)⁻¹ * E.z * (g * c)) * m⁻¹ := by group
      _ = m * (m⁻¹ * E.z * m) * m⁻¹ := by rw [hmeq]
      _ = E.z := by group
  have hcen : g * c * m⁻¹ ∈ Subgroup.centralizer ({E.z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc E.z * (g * c * m⁻¹)
        = (g * c * m⁻¹) * ((g * c * m⁻¹)⁻¹ * E.z * (g * c * m⁻¹)) := by group
      _ = (g * c * m⁻¹) * E.z := by rw [hinner]
  rw [hGz] at hcen
  have hhM : g * c * m⁻¹ ∈ M := E.T_le_M hcen
  have hcy : (c : G)⁻¹ * y * (c : G) = y := by
    have : y * (c : G) = (c : G) * y := Subgroup.mem_centralizer_iff.mp c.2 y rfl
    calc (c : G)⁻¹ * y * (c : G) = (c : G)⁻¹ * ((c : G) * y) := by rw [← this]; group
      _ = y := by group
  refine ⟨g * c * m⁻¹ * m, M.mul_mem hhM hm, ?_⟩
  calc (g * c * m⁻¹ * m)⁻¹ * E.s * (g * c * m⁻¹ * m) = (c : G)⁻¹ * (g⁻¹ * E.s * g) * (c : G) := by
        group
    _ = y := by rw [hy, hcy]

theorem fusion_s_of_zG_cap_M [Finite G] (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hT : quasithinIsSylowTwo T)
    (hA1 : ∀ g : G, g⁻¹ * E.z * g ∈ M → ∃ m ∈ M, m⁻¹ * E.z * m = g⁻¹ * E.z * g)
    {y g : G} (hy : g⁻¹ * E.s * g = y) (hyM : y ∈ M) : ∃ m ∈ M, m⁻¹ * E.s * m = y := by
  have hfix := E.hfix_of_zG_cap_M hGz hA1
  have hy2 : (⟨y, hyM⟩ : M) * ⟨y, hyM⟩ = 1 := by
    apply Subtype.ext
    calc y * y = g⁻¹ * (E.s * E.s) * g := by rw [← hy]; group
      _ = 1 := by rw [E.s_sq]; group
  obtain ⟨c, hc⟩ := exists_conj_mem_of_odd_index (E.not_dvd_index_T_M hT) hy2
  have hyT : (c : G)⁻¹ * y * (c : G) ∈ T := Subgroup.mem_subgroupOf.1 hc
  obtain ⟨m, hm, hmeq⟩ := E.fusion_s_of_mem_T hGz hfix hA1 (y := (c : G)⁻¹ * y * (c : G))
    (g := g * c) (by rw [← hy]; group) hyT
  refine ⟨m * (c : G)⁻¹, M.mul_mem hm (M.inv_mem c.2), ?_⟩
  have e1 : (m * (c : G)⁻¹)⁻¹ * E.s * (m * (c : G)⁻¹) =
      (c : G) * (m⁻¹ * E.s * m) * (c : G)⁻¹ := by group
  rw [e1, hmeq]
  group

include E in
theorem card_T : Nat.card T = 128 := by
  rw [← E.map_Th, card_map_of_inj E.injective, card_Th]

theorem card_J : Nat.card E.J = 64 := by
  unfold J
  rw [card_map_of_inj E.injective, card_Jh]

theorem relIndex_J_T [Finite G] : E.J.relIndex T = 2 := by
  have h := Subgroup.card_mul_index (E.J.subgroupOf T)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe E.J_le_T).toEquiv, E.card_J, E.card_T] at h
  rw [Subgroup.relIndex]
  omega

theorem orderOf_s : orderOf E.s = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [pow_two]; exact E.s_sq) ?_
  intro h
  exact s0_ne_one (E.injective (by rw [map_one]; exact h))

theorem not_weakly_closed [Finite G] (hG : IsSimpleGroup G) (hT : quasithinIsSylowTwo T)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T) :
    ¬ ∀ g : G, g⁻¹ * E.z * g ∈ E.B → g⁻¹ * E.z * g = E.z := by
  intro hwc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA1 := E.zG_cap_M hGz hT hwc
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hQP : E.J ≤ (S : Subgroup G) := hS ▸ E.J_le_T
  have hidx : E.J.relIndex (S : Subgroup G) = 2 := hS ▸ E.relIndex_J_T
  have hQs : ∀ x : G, x⁻¹ * E.s * x ∉ E.J := by
    intro x hx
    have hxM : x⁻¹ * E.s * x ∈ M := E.T_le_M (E.J_le_T hx)
    obtain ⟨m, hm, hmeq⟩ := E.fusion_s_of_zG_cap_M hGz hT hA1 rfl hxM
    obtain ⟨w, rfl⟩ := E.mem_M.1 hm
    rw [← hmeq] at hx
    obtain ⟨v, hv, hvx⟩ := hx
    have : v = w⁻¹ * s0 * w := E.injective (by rw [hvx, s]; simp)
    rw [this] at hv
    exact D6_not_mem_Jh ((cls_s0 _).1 ⟨w, rfl⟩) hv
  have hnot := thompson_transfer_lemma S hQP hidx E.orderOf_s hQs
  have htop : pResidual 2 G = ⊤ :=
    pResidual_two_eq_top hG (c := E.ι x3) (by rw [← map_pow, x3_cube, map_one])
      (fun h => x3_ne_one (E.injective (by rw [map_one]; exact h)))
  rw [htop] at hnot
  exact hnot (Subgroup.mem_top _)

end Emb

end CFSG.Quasithin.A10
