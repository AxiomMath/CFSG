module

public import CFSG.Quasithin.EmptyFaithful.S143QB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

@[expose] def wOfX {G : Type*} [Group G] (d x : G) : G :=
  d * (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)

section Elements

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c hxL hx3 in
theorem goodElt_of_order_three : GoodElt128 T (yOfL22 T M) x := by
  refine ⟨hxL, fun hxN => ?_⟩
  have hxV : x ∈ Subgroup.normalizer (VZ T M : Set G) :=
    c.h1281.LT_le_normalizer_VZ (Subgroup.mem_sup_left hxL)
  have hxodd : Odd (orderOf x) := by rw [hx3]; decide
  have hxC : x ∈ Subgroup.centralizer (VZ T M : Set G) :=
    c.h1281.mem_centralizer_of_odd hxV hxN hxodd
  have hx2 : x ∈ pCoreOf 2 (yOfL22 T M ⊔ T) := by
    rw [← c.h1281.centralizer]
    exact ⟨Subgroup.mem_sup_left hxL, hxC⟩
  have hp : IsPGroup 2 ↥(pCoreOf 2 (yOfL22 T M ⊔ T)) :=
    c.hyp.sylow.1.to_le (pCoreOf_LT_le_T c)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨x, hx2⟩
  have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_mk _ _).symm.trans hk
  rw [hx3] at hk'
  have : (3 : ℕ) ∣ 2 ^ k := hk' ▸ dvd_refl 3
  have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

include c hD hd4 hxL hx3 in
theorem three_cycle_x : ∃ a : G, a = x * (d * d) * x⁻¹ ∧ a ∈ VZ T M ∧ a ∉ quasithinOmegaOneCenter T ∧
    (d * d) * a = a * (d * d) ∧ a * a = 1 ∧ x * a * x⁻¹ = (d * d) * a ∧
    ∀ w ∈ VZ T M, w = 1 ∨ w = d * d ∨ w = a ∨ w = (d * d) * a := by
  obtain ⟨z, a, hzZ, hz1, ha, haV, haZ, hzz, haa, hza, hxa, hxza, hall⟩ :=
    exists_three_cycle c.h1281 (goodElt_of_order_three c hxL hx3)
  have hzd : z = d * d := by
    rcases c.mem_Z_cases (sq_mem_omegaOneCenter c hD hd4) (dd_facts hd4).2 hzZ with h | h
    · exact absurd h hz1
    · exact h
  subst hzd
  exact ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩

end Elements

section WFacts

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c hxL in
theorem d1_mem_Xgen {d : G} (hd : d ∈ dOf T M) : x * d * x⁻¹ ∈ Xgen T M := by
  have hx' : x⁻¹ ∈ yOfL22 T M := (yOfL22 T M).inv_mem hxL
  refine le_Wgen (conjSubgroup_dOf_mem_delta c hx') ?_
  rw [mem_conjSubgroup_iff]
  have : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
  rw [this]; exact hd

include c hxL in
theorem d2_mem_Xgen {d : G} (hd : d ∈ dOf T M) : x * (x * d * x⁻¹) * x⁻¹ ∈ Xgen T M := by
  have hx' : x⁻¹ * x⁻¹ ∈ yOfL22 T M := (yOfL22 T M).mul_mem ((yOfL22 T M).inv_mem hxL) ((yOfL22 T M).inv_mem hxL)
  refine le_Wgen (conjSubgroup_dOf_mem_delta c hx') ?_
  rw [mem_conjSubgroup_iff]
  have : (x⁻¹ * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) * (x⁻¹ * x⁻¹)⁻¹ = d := by group
  rw [this]; exact hd

include c hD hd4 hxL hx3 in
theorem wOfX_sq : wOfX d x * wOfX d x = 1 := by
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd
  have h1 := d1_mem_Xgen c hxL hd
  have h2 := d2_mem_Xgen c hxL hd
  have hc := Xgen_comm c hD hd4
  have c01 : Commute d (x * d * x⁻¹) := hc _ h0 _ h1
  have c02 : Commute d (x * (x * d * x⁻¹) * x⁻¹) := hc _ h0 _ h2
  have c12 : Commute (x * d * x⁻¹) (x * (x * d * x⁻¹) * x⁻¹) := hc _ h1 _ h2
  have e1 : (x * d * x⁻¹) * (x * d * x⁻¹) = a := by
    rw [ha]; group
  have e2 : (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) = (d * d) * a := by
    rw [← hxa, ← e1]; group
  have hw : (wOfX d x) * (wOfX d x) = (d * d) * ((x * d * x⁻¹) * (x * d * x⁻¹)) *
      ((x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) := by
    have hcm : Commute (d * (x * d * x⁻¹)) (x * (x * d * x⁻¹) * x⁻¹) := c02.mul_left c12
    unfold wOfX
    have := (hcm.mul_pow 2)
    rw [pow_two, pow_two] at this
    have h3 := (c01.mul_pow 2)
    rw [pow_two, pow_two] at h3
    rw [this, h3]
    simp only [pow_two]
  rw [hw, e1, e2]
  have hdd : (d * d) * (d * d) = 1 := (dd_facts hd4).1
  calc (d * d) * a * ((d * d) * a) = (d * d) * (a * (d * d)) * a := by group
    _ = (d * d) * ((d * d) * a) * a := by rw [← hza]
    _ = ((d * d) * (d * d)) * (a * a) := by group
    _ = 1 := by rw [hdd, haa, one_mul]

include c hD hxL in
theorem wOfX_mem_Xgen : wOfX d x ∈ Xgen T M := by
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd
  exact (Xgen T M).mul_mem ((Xgen T M).mul_mem h0 (d1_mem_Xgen c hxL hd)) (d2_mem_Xgen c hxL hd)

include c hD hxL in
theorem wOfX_mem_T : wOfX d x ∈ T := Xgen_le_T (wOfX_mem_Xgen c hD hxL)

include c hD hd4 hxL hx3 in
theorem x_comm_wOfX : x * wOfX d x * x⁻¹ = wOfX d x := by
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd
  have h1 := d1_mem_Xgen c hxL hd
  have h2 := d2_mem_Xgen c hxL hd
  have hc := Xgen_comm c hD hd4
  have hx3' : x * x * x = 1 := by rw [← pow_three', ← hx3]; exact pow_orderOf_eq_one x
  have e3 : x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹ = d := by
    have : x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * d * (x * x * x)⁻¹ := by group
    rw [this, hx3']; group
  have hcomm12 := hc _ h1 _ h2
  have hcomm02 := hc _ h0 _ h2
  have hcomm01 := hc _ h0 _ h1
  unfold wOfX
  calc x * (d * (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) * x⁻¹
      = (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹) := by
        group
    _ = (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) * d := by rw [e3]
    _ = d * (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) := by
        rw [mul_assoc, ← hcomm02, ← mul_assoc, ← hcomm01]

end WFacts

end S143

end CFSG.Quasithin
