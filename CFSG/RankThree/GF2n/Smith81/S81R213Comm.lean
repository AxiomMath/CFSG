module

public import CFSG.RankThree.GF2n.Smith81.S81R213Odd
public import CFSG.RankThree.GF2n.Smith81.S81RRangePure
public import CFSG.RankThree.GF2n.Smith81.S81LV0

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

section Comm

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} {z : G}

theorem comm_sq_mem_range (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) {x y : G} (hxc : IsConj z x)
    (hxM : x ∈ M) (hxQ : x ∉ Q) (hyc : IsConj z y) (hyM : y ∈ M)
    {gx gy : GL (Fin 6) K} (hgx : IsTransvec K gx)
    (hx : ActsAs φ x gx) (hy : ActsAs φ y gy) (hcomm : gx * gy = gy * gx) :
    (x * y) ^ 2 ∈ Q ∧ ψ (M₀.π ((x * y) ^ 2)) ∈ LinearMap.range (rho K gx - 1) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  have hxx : x * x = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hxc
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hyc
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hx'A : ActsAs φ (y * x * y⁻¹) gx := by
    have h := hx.conj hy
    have e : gy * gx * gy⁻¹ = gx := by rw [← hcomm]; group
    rwa [e] at h
  have hx'M : y * x * y⁻¹ ∈ M := M.mul_mem (M.mul_mem hyM hxM) (M.inv_mem hyM)
  have hx'Q : y * x * y⁻¹ ∉ Q := hx'A.not_mem_Q Dt (hx.rho_ne_one_of_not_mem_Q Dt hxQ)
  have hx'c : IsConj z (y * x * y⁻¹) := hxc.trans (isConj_iff.mpr ⟨y, rfl⟩)
  obtain ⟨q, hqQ, hq⟩ := conj_of_phi_eq Dt hxc hxM hxQ hx'c hx'M hx'Q hgx hx hx'A
  obtain ⟨X, hs, Tx, hII, hCs, hRs⟩ := Dt.xdata hxc hxM hxQ hgx hx
  have hsq : (x * y) ^ 2 = (x * q * x⁻¹) * q⁻¹ := by
    have h1 : (x * y) ^ 2 = x * (y * x * y⁻¹) := by rw [pow_two, hyinv]; group
    rw [h1, hq, hxinv]; group
  have hxqQ : x * q * x⁻¹ ∈ Q := conj_mem_Q H hxM hqQ
  have hcQ : (x * y) ^ 2 ∈ Q := by rw [hsq]; exact Q.mul_mem hxqQ (Q.inv_mem hqQ)
  refine ⟨hcQ, ?_⟩
  have hπ : M₀.π ((x * y) ^ 2) = Tx.T (M₀.π q) - M₀.π q := by
    rw [hsq, M₀.π_mul _ hxqQ _ (Q.inv_mem hqQ), Tim79.QuadModel.pi_inv M₀ hqQ, Tx.hπ q hqQ,
      sub_eq_add_neg]
  rw [← (hRs _)]
  rw [hπ]
  exact mem_Rs.mpr ⟨M₀.π q, rfl⟩

theorem two_close_of_comm (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) {x y : G} (hxc : IsConj z x)
    (hxM : x ∈ M) (hxQ : x ∉ Q) (hyc : IsConj z y) (hyM : y ∈ M) (hyQ : y ∉ Q)
    {gx gy : GL (Fin 6) K} (hgx : IsTransvec K gx) (hgy : IsTransvec K gy)
    (hx : ActsAs φ x gx) (hy : ActsAs φ y gy) (hcomm : gx * gy = gy * gx)
    (hnot : ¬ ∃ s : K, (gy : Matrix (Fin 6) (Fin 6) K) - 1 = s • ((gx : Matrix (Fin 6) (Fin 6) K) - 1)) :
    (x * y) ^ 2 = 1 ∨ InZClass Z ((x * y) ^ 2) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  have hxx : x * x = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hxc
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hyc
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  obtain ⟨hcQ, hR⟩ := comm_sq_mem_range Dt hxc hxM hxQ hyc hyM hgx hx hy hcomm
  obtain ⟨hcQ', hR'⟩ := comm_sq_mem_range Dt hyc hyM hyQ hxc hxM hgy hy hx hcomm.symm
  have hyx : (y * x) ^ 2 = ((x * y) ^ 2)⁻¹ := by
    have : y * x = (x * y)⁻¹ := by rw [mul_inv_rev, hxinv, hyinv]
    rw [this, inv_pow]
  have hψ : ψ (M₀.π ((x * y) ^ 2)) ∈ LinearMap.range (rho K gy - 1) := by
    have h := hR'
    rw [hyx, Tim79.QuadModel.pi_inv M₀ hcQ, map_neg] at h
    exact (Submodule.neg_mem_iff _).mp h
  have hpure := pure_of_range_inf_range hgx hgy hnot _ ⟨hR, hψ⟩
  by_cases h0 : M₀.π ((x * y) ^ 2) = 0
  · have hcZ : (x * y) ^ 2 ∈ Z := (M₀.π_ker _ hcQ).mp h0
    by_cases hc1 : (x * y) ^ 2 = 1
    · exact Or.inl hc1
    · exact Or.inr ⟨1, _, hcZ, hc1, by group⟩
  · have hcZ : (x * y) ^ 2 ∉ Z := fun h => h0 ((M₀.π_ker _ hcQ).mpr h)
    exact Or.inr (inZClass_of_isConj Dt.hz Dt.hz1
      (Dt.d.isConj_of_isPure H Dt.hD Dt.hz Dt.hz1 hcQ hcZ hpure))

end Comm

end CFSG.RankThree.GF2n.Smith81.E3LRoot
