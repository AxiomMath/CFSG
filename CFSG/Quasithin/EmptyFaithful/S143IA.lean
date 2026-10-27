module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2414a
public import CFSG.Quasithin.EmptyFaithful.S143HC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Lin2

namespace S143

section Util

variable {G : Type*} [Group G]

theorem mul_mem_mul_of_relIndex_two_not_mem {T N : Subgroup G} {t s : G} (htT : t ∈ T)
    (hsT : s ∈ T) (hidx : N.relIndex T = 2) (htN : t ∉ N) (hsN : s ∉ N) :
    s * t⁻¹ ∈ N ∧ t * s ∈ N := by
  constructor
  · rcases coset_of_relIndex_two hidx hsT htT htN with h | h
    · exact absurd h hsN
    · exact h
  · have hs' : s⁻¹ ∈ T := T.inv_mem hsT
    have hs'N : s⁻¹ ∉ N := fun h' => hsN (by simpa using N.inv_mem h')
    rcases coset_of_relIndex_two hidx htT hs' hs'N with h | h
    · exact absurd h htN
    · simpa using h

end Util

section Swap

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.swapData_of_involution {t s : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T)
    (hsT : s ∈ T) (hsRQ : s ∉ rOf T M ⊔ qOf T) (hs2 : s * s = 1)
    (hidx : (rOf T M ⊔ qOf T).relIndex T = 2) :
    SwapData (rOf T M) (c.Ac hrW hrV hr2) (conjSubgroup (c.Ac hrW hrV hr2) t) (VZ T M) s := by
  obtain ⟨hst, hts⟩ := mul_mem_mul_of_relIndex_two_not_mem htT hsT hidx htRQ hsRQ
  have hRQN : rOf T M ⊔ qOf T ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (sup_le_sup_right (pCoreOf_le 2 (iTwo T M)) _).trans (c.normal_Ac hrW hrV hr2)
  have hRN : rOf T M ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    le_sup_left.trans hRQN
  have hAN : ∀ x ∈ rOf T M, ∀ a ∈ c.Ac hrW hrV hr2, x * a * x⁻¹ ∈ c.Ac hrW hrV hr2 :=
    fun x hx a ha => (Subgroup.mem_normalizer_iff.mp (hRN hx) a).mp ha
  have hq : ∀ x, x ∈ (conjSubgroup (c.Ac hrW hrV hr2) t) ↔ t * x * t⁻¹ ∈ c.Ac hrW hrV hr2 :=
    fun x => mem_conjSubgroup_iff
  refine
    { tt := hs2
      R_eq := (c.Ac_sup_conj hrW hrV hr2 htT htRQ).symm
      U_norm := hRN
      V_norm := fun x hx => ?_
      inf_eq := c.Ac_inf_conj hrW hrV hr2 htT htRQ
      U_ab := fun a ha b hb =>
        mul_comm_of_sq_eq_one (fun z hz => c.sq_Ac hrW hrV hr2 hz) ha hb
      V_ab := fun a ha b hb =>
        mul_comm_of_sq_eq_one (fun z hz => c.sq_conjAc hrW hrV hr2 hz) ha hb
      U_sq := fun a ha => c.sq_Ac hrW hrV hr2 ha
      V_sq := fun a ha => c.sq_conjAc hrW hrV hr2 ha
      tU := fun u hu => ?_
      tV := fun v hv => ?_
      N_cen := fun n hn x hx => c.rOf_comm_VZ hx hn
      inv_mem_UV := fun x hx hx2 => ?_ }
  ·
    have htR : ∀ y ∈ rOf T M, t * y * t⁻¹ ∈ rOf T M := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp (c.T_le_normalizer_rOf' htT) y).mp hy
    refine mem_normalizer_of_conj_mem (fun a ha => ?_) (fun a ha => ?_)
    · rw [hq] at ha ⊢
      have := hAN _ (htR x hx) _ ha
      have e : t * (x * a * x⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * a * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
      rw [e]; exact this
    · rw [hq] at ha ⊢
      have := hAN _ (htR x⁻¹ ((rOf T M).inv_mem hx)) _ ha
      have e : t * (x⁻¹ * a * x) * t⁻¹ =
          (t * x⁻¹ * t⁻¹) * (t * a * t⁻¹) * (t * x⁻¹ * t⁻¹)⁻¹ := by group
      rw [e]; exact this
  ·
    rw [hq]
    have e : t * (s * u * s⁻¹) * t⁻¹ = (t * s) * u * (t * s)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hRQN hts) u).mp hu
  ·
    rw [hq] at hv
    have e : s * v * s⁻¹ = (s * t⁻¹) * (t * v * t⁻¹) * (s * t⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hRQN hst) (t * v * t⁻¹)).mp hv
  ·
    have hcl : ∀ y ∈ Subgroup.zpowers x, y = 1 ∨ y = x := fun y hy =>
      mem_zpowers_of_mul_self_eq_one hx2 hy
    have hBe : IsElemAbelian 2 (Subgroup.zpowers x) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
      · rcases hcl a a.2 with ha | ha <;> rcases hcl b b.2 with hb | hb <;> simp [ha, hb]
      · rcases hcl y hy with h1 | h1 <;> simp [h1, sq, hx2]
    have hB : Subgroup.zpowers x ≤ rOf T M := (Subgroup.zpowers_le).2 hx
    rcases c.maximal_Ac hrW hrV hr2 htT htRQ hB hBe with h1 | h1
    · exact Or.inl (h1 (Subgroup.mem_zpowers x))
    · exact Or.inr (h1 (Subgroup.mem_zpowers x))

end Swap

end S143

end CFSG.Quasithin
