module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubLong
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubPartner

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem zpowers_transitive (F : FanTree Γ G) (v : V) {x : G} (hx : x ∈ MulAction.stabilizer G v)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (ho : orderOf x = q) :
    ∀ u w, Γ.Adj v u → Γ.Adj v w → ∃ k ∈ Subgroup.zpowers x, k • v = v ∧ k • u = w := by
  intro u w hu hw
  have hZ : Subgroup.zpowers x ≤ MulAction.stabilizer G v := Subgroup.zpowers_le.2 hx
  rcases F.fixes_or_trans v hZ with ⟨w₀, hw₀, hfix⟩ | htr
  · exfalso
    have hxw : x • w₀ = w₀ := hfix x (Subgroup.mem_zpowers x)
    obtain ⟨j, hj⟩ := F.edge_two v w₀ hw₀ ⟨x, hx, MulAction.mem_stabilizer_iff.2 hxw⟩
    have h1 : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
  · obtain ⟨k, hk, hkx⟩ := htr u w hu hw
    exact ⟨k, hk, MulAction.mem_stabilizer_iff.1 (hZ hk), hkx⟩

theorem fixSet_orbit_conj {v : V} {H : Subgroup G} {h : G} (hh : h ∈ H) {z : G}
    (hz : z ∈ fixSet G (MulAction.orbit ↥H v)) : h * z * h⁻¹ ∈ fixSet G (MulAction.orbit ↥H v) := by
  intro u hu
  have hu' : h⁻¹ • u ∈ MulAction.orbit ↥H v := by
    obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup.1 hu
    exact mem_orbit_subgroup.2 ⟨h⁻¹ * k, H.mul_mem (H.inv_mem hh) hk, by rw [mul_smul]⟩
  rw [mul_smul, mul_smul, hz _ hu', smul_inv_smul]

namespace SubgraphProp

variable {T : Track Γ G} {a b : ℤ} {H : Subgroup G}

theorem fixSet_le_H (hS : SubgraphProp T a b H) (F : FanTree Γ G) :
    fixSet G (MulAction.orbit ↥H (T.line.vert a)) ≤ H := fun _ hg =>
  hS.sub (T.fixer_le_subFixer a b (hS.fixSet_orbit_le_fixer F hg))

theorem fixSet_le_nbrStab (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ}
    (hm : b - a = 2 * m) {u : V} (hu : u ∈ MulAction.orbit ↥H (T.line.vert a)) :
    fixSet G (MulAction.orbit ↥H (T.line.vert a)) ≤ nbrStab Γ G u := by
  intro z hz w hw
  obtain ⟨u', ⟨hu'A, hne, hadj⟩, -⟩ := fan46_partner hS F hm hu hw
  have hu'A' : u' ∈ MulAction.orbit ↥H (T.line.vert a) := by
    rwa [MulAction.orbit_eq_iff.2 hu] at hu'A
  have e1 : z • u = u := hz u hu
  have e2 : z • u' = u' := hz u' hu'A'
  have h1 : Γ.Adj u (z • w) := by
    have := (F.adj_smul z u w).2 hw
    rwa [e1] at this
  have h2 : Γ.Adj (z • w) u' := by
    have := (F.adj_smul z u' w).2 hadj
    rw [e2] at this
    exact this.symm
  exact F.eq_of_adj_adj h1 h2 hw hadj.symm hne.symm

end SubgraphProp

end CFSG.Quasithin.Fan86
